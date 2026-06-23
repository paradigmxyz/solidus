#!/usr/bin/env python3
"""Compare full-solc and solc->Lean bytecode with a Forge call harness."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence


SUPPORTED_EVM_VERSIONS = ("london", "paris", "shanghai", "cancun")
DEFAULT_EVM_VERSION = "cancun"


def load_bridge(script_dir: Path) -> Any:
    bridge_path = script_dir / "solidity_to_yul_lean.py"
    spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {bridge_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def resolve_executable(path: str) -> str:
    if "/" in path:
        return path
    resolved = shutil.which(path)
    return resolved or path


def concrete_hex(value: str, what: str, prefixed: bool = True) -> str:
    value = value.strip()
    if value.startswith(("0x", "0X")):
        value = value[2:]
    if not re.fullmatch(r"[0-9a-fA-F]*", value) or len(value) % 2:
        raise ValueError(f"{what} must be even-length hex bytes")
    normalized = value.lower()
    return "0x" + normalized if prefixed else normalized


def ensure_output_selection_fields(
    compiler_input: dict[str, Any],
    fields: Sequence[str],
) -> None:
    settings = compiler_input.setdefault("settings", {})
    output_selection = settings.setdefault("outputSelection", {})
    source_selection = output_selection.setdefault("*", {})
    contract_selection = source_selection.setdefault("*", [])
    for field in fields:
        if field not in contract_selection:
            contract_selection.append(field)


def link_solc_bytecode(
    bytecode: str,
    link_references: Any,
    linker_symbols: Sequence[Any],
    what: str,
) -> str:
    value = bytecode[2:] if bytecode.startswith(("0x", "0X")) else bytecode
    if re.fullmatch(r"[0-9a-fA-F]*", value):
        return concrete_hex(value, what)
    symbol_values = {entry.name: entry.value for entry in linker_symbols}
    if not isinstance(link_references, dict):
        raise ValueError(f"{what} has non-hex link placeholders but no linkReferences")
    if not symbol_values:
        for source_name, contracts in link_references.items():
            if isinstance(source_name, str) and isinstance(contracts, dict):
                for contract_name in contracts:
                    if isinstance(contract_name, str):
                        symbol_name = f"{source_name}:{contract_name}"
                        raise ValueError(
                            f"{what} needs linker symbol {symbol_name!r}; "
                            "pass --linker-symbol"
                        )
        return concrete_hex(value, what)
    linked = value
    for source_name, contracts in link_references.items():
        if not isinstance(source_name, str) or not isinstance(contracts, dict):
            raise ValueError(f"{what} has malformed linkReferences")
        for contract_name, references in contracts.items():
            if not isinstance(contract_name, str) or not isinstance(references, list):
                raise ValueError(f"{what} has malformed linkReferences")
            symbol_name = f"{source_name}:{contract_name}"
            if symbol_name not in symbol_values:
                raise ValueError(
                    f"{what} needs linker symbol {symbol_name!r}; "
                    "pass --linker-symbol"
                )
            for reference in references:
                if not isinstance(reference, dict):
                    raise ValueError(f"{what} has malformed link reference")
                start = reference.get("start")
                length = reference.get("length")
                if not isinstance(start, int) or not isinstance(length, int):
                    raise ValueError(f"{what} has malformed link reference")
                if length <= 0:
                    raise ValueError(f"{what} has non-positive link length")
                symbol_value = symbol_values[symbol_name]
                if symbol_value < 0 or symbol_value >= 1 << (8 * length):
                    raise ValueError(
                        f"{what} linker symbol {symbol_name!r} does not fit "
                        f"in {length} bytes"
                    )
                replacement = symbol_value.to_bytes(length, "big").hex()
                start_index = start * 2
                end_index = start_index + length * 2
                linked = linked[:start_index] + replacement + linked[end_index:]
    return concrete_hex(linked, what)


def link_compared_full_solc_bytecode(
    creation: str,
    runtime: str,
    creation_link_references: Any,
    runtime_link_references: Any,
    linker_symbols: Sequence[Any],
    compare_creation: bool = True,
    compare_runtime: bool = True,
) -> tuple[str, str]:
    linked_creation = (
        link_solc_bytecode(
            creation,
            creation_link_references,
            linker_symbols,
            "solc creation bytecode",
        )
        if compare_creation
        else "0x"
    )
    linked_runtime = (
        link_solc_bytecode(
            runtime,
            runtime_link_references,
            linker_symbols,
            "solc runtime bytecode",
        )
        if compare_runtime
        else "0x"
    )
    return linked_creation, linked_runtime


def prefixed_hex_size(value: str) -> int:
    if not re.fullmatch(r"0x[0-9a-f]*", value):
        raise ValueError(f"expected prefixed lowercase hex, got {value!r}")
    return (len(value) - 2) // 2


def parse_uint256(value: str, what: str) -> int:
    try:
        parsed = int(value, 16) if value.startswith(("0x", "0X")) else int(value, 10)
    except ValueError as exc:
        raise ValueError(f"{what} must be a decimal or hex uint256") from exc
    if parsed < 0 or parsed >= 2**256:
        raise ValueError(f"{what} is outside uint256 range")
    return parsed


def build_full_solc_input(bridge: Any, args: argparse.Namespace) -> dict[str, Any]:
    source_name, content = bridge.read_source_input(args.input, args.source_name)
    explicit_include_sources = bridge.read_include_source_files(
        args.include_source,
        source_name,
    )
    import_remappings = bridge.read_import_remappings(
        args.remapping,
        args.remappings_file,
    )
    if args.auto_include_imports:
        include_source_files = bridge.collect_local_import_sources(
            source_name,
            content,
            args.input,
            explicit_include_sources,
            import_remappings,
        )
    else:
        include_source_files = explicit_include_sources
    include_sources = {
        include_name: include_source.content
        for include_name, include_source in include_source_files.items()
    }
    compiler_input = bridge.standard_json_input(
        source_name,
        content,
        via_ir=args.via_ir,
        optimized=args.optimized,
        experimental=args.experimental,
        include_sources=include_sources,
        optimizer_runs=getattr(args, "optimizer_runs", None),
        evm_version=getattr(args, "evm_version", DEFAULT_EVM_VERSION),
    )
    ensure_output_selection_fields(
        compiler_input,
        [
            "evm.bytecode.linkReferences",
            "evm.deployedBytecode.linkReferences",
        ],
    )
    return compiler_input


def load_full_solc_bytecode(
    bridge: Any,
    args: argparse.Namespace,
) -> tuple[str, str, str, str, Any, Any]:
    compiler_input = build_full_solc_input(bridge, args)
    output = bridge.run_solc(args.solc, compiler_input, args.solc_arg)
    source_name, contract_name, contract_output = bridge.choose_contract(
        output,
        args.source_name,
        args.contract,
    )
    evm = contract_output.get("evm", {})
    if not isinstance(evm, dict):
        raise ValueError(f"solc output for {source_name}:{contract_name} has no evm object")
    bytecode = evm.get("bytecode", {})
    deployed = evm.get("deployedBytecode", {})
    if not isinstance(bytecode, dict) or not isinstance(deployed, dict):
        raise ValueError(f"solc output for {source_name}:{contract_name} has no bytecode")
    creation = bytecode.get("object")
    runtime = deployed.get("object")
    if not isinstance(creation, str) or not isinstance(runtime, str):
        raise ValueError(f"solc output for {source_name}:{contract_name} has no object hex")
    return (
        source_name,
        contract_name,
        creation,
        runtime,
        bytecode.get("linkReferences"),
        deployed.get("linkReferences"),
    )


def append_bridge_compile_options(
    command: list[str],
    args: argparse.Namespace,
) -> None:
    if args.source_name:
        command.extend(["--source-name", args.source_name])
    if args.optimized:
        command.append("--optimized")
    evm_version = getattr(args, "evm_version", None)
    if evm_version is not None:
        command.extend(["--evm-version", evm_version])
    optimizer_runs = getattr(args, "optimizer_runs", None)
    if optimizer_runs is not None:
        command.extend(["--optimizer-runs", str(optimizer_runs)])
    yul_ast_solc = getattr(args, "yul_ast_solc", None)
    if yul_ast_solc:
        command.extend(["--yul-ast-solc", yul_ast_solc])
    for solc_arg in getattr(args, "yul_ast_solc_arg", []):
        command.append(f"--yul-ast-solc-arg={solc_arg}")
    if not args.via_ir:
        command.append("--no-via-ir")
    if not args.experimental:
        command.append("--no-experimental")
    if not args.auto_include_imports:
        command.append("--no-auto-include-imports")
    for include in args.include_source:
        command.extend(["--include-source", include])
    for remapping in args.remapping:
        command.extend(["--remapping", remapping])
    for remappings_file in args.remappings_file:
        command.extend(["--remappings-file", str(remappings_file)])
    for linker_symbol in args.linker_symbol:
        command.extend(["--linker-symbol", linker_symbol])
    for solc_arg in args.solc_arg:
        command.append(f"--solc-arg={solc_arg}")


def run_bridge_artifact(
    root: Path,
    args: argparse.Namespace,
    output_path: Path,
) -> dict[str, Any]:
    bridge_json_dir = output_path.parent / "bridge-json"
    bridge_summary_path = output_path.parent / "bridge-json-summary.json"
    command = [
        sys.executable,
        str(root / "scripts" / "solidity_to_yul_lean.py"),
        str(args.input),
        "--solc",
        args.solc,
        "--lake",
        args.lake,
        "--lake-cwd",
        str(args.lake_cwd),
        "--contract",
        args.contract,
        "--format",
        "bytecode-artifact",
        "--namespace",
        args.namespace,
        "--bridge-json-dir",
        str(bridge_json_dir),
        "--output",
        str(output_path),
    ]
    append_bridge_compile_options(command, args)
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        output = "\n".join(
            part for part in [completed.stdout.strip(), completed.stderr.strip()] if part
        )
        summary_suffix = ""
        if (bridge_json_dir / "manifest.json").exists():
            try:
                write_bridge_summary(root, bridge_json_dir, bridge_summary_path)
                summary_suffix = f"\nbridge_summary={bridge_summary_path}"
            except RuntimeError as exc:
                summary_suffix = f"\nbridge_summary_error={exc}"
        raise RuntimeError(
            "Lean bytecode artifact generation failed:\n"
            + output
            + f"\nbridge_json_dir={bridge_json_dir}"
            + summary_suffix
        )
    if (bridge_json_dir / "manifest.json").exists():
        write_bridge_summary(root, bridge_json_dir, bridge_summary_path)
    return json.loads(output_path.read_text())


def run_bridge_bytecode(
    root: Path,
    args: argparse.Namespace,
    output_path: Path,
    object_selector: str,
) -> str:
    bridge_json_dir = output_path.parent / f"bridge-json-{object_selector}"
    bridge_summary_path = (
        output_path.parent / f"bridge-json-{object_selector}-summary.json"
    )
    command = [
        sys.executable,
        str(root / "scripts" / "solidity_to_yul_lean.py"),
        str(args.input),
        "--solc",
        args.solc,
        "--lake",
        args.lake,
        "--lake-cwd",
        str(args.lake_cwd),
        "--contract",
        args.contract,
        "--format",
        "bytecode",
        "--object",
        object_selector,
        "--namespace",
        args.namespace,
        "--bridge-json-dir",
        str(bridge_json_dir),
        "--output",
        str(output_path),
    ]
    append_bridge_compile_options(command, args)
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        output = "\n".join(
            part for part in [completed.stdout.strip(), completed.stderr.strip()] if part
        )
        summary_suffix = ""
        if (bridge_json_dir / "manifest.json").exists():
            try:
                write_bridge_summary(root, bridge_json_dir, bridge_summary_path)
                summary_suffix = f"\nbridge_summary={bridge_summary_path}"
            except RuntimeError as exc:
                summary_suffix = f"\nbridge_summary_error={exc}"
        raise RuntimeError(
            "Lean bytecode generation failed:\n"
            + output
            + f"\nbridge_json_dir={bridge_json_dir}"
            + summary_suffix
        )
    if (bridge_json_dir / "manifest.json").exists():
        write_bridge_summary(root, bridge_json_dir, bridge_summary_path)
    return concrete_hex(output_path.read_text(), f"Lean {object_selector} bytecode")


def write_bridge_summary(
    root: Path,
    bridge_json_dir: Path,
    output_path: Path,
) -> None:
    manifest_path = bridge_json_dir / "manifest.json"
    if not manifest_path.exists():
        return
    command = [
        sys.executable,
        str(root / "scripts" / "solidity_to_yul_lean.py"),
        str(manifest_path),
        "--input-format",
        "bridge-json-manifest",
        "--format",
        "bridge-json-summary",
        "--output",
        str(output_path),
    ]
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        output = "\n".join(
            part for part in [completed.stdout.strip(), completed.stderr.strip()] if part
        )
        raise RuntimeError(
            "Bridge JSON summary generation failed:\n"
            + output
            + f"\nbridge_json_manifest={manifest_path}"
        )
    validate_command = [
        sys.executable,
        str(root / "scripts" / "validate_bridge_json.py"),
        "--quiet",
        str(output_path),
    ]
    completed = subprocess.run(
        validate_command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        output = "\n".join(
            part for part in [completed.stdout.strip(), completed.stderr.strip()] if part
        )
        raise RuntimeError(
            "Bridge JSON summary validation failed:\n"
            + output
            + f"\nbridge_summary={output_path}"
        )


def csv(names: Any) -> str:
    if not isinstance(names, list):
        return "none"
    strings = [name for name in names if isinstance(name, str)]
    return ",".join(strings) if strings else "none"


def bridge_object_labels(objects: Any) -> list[str]:
    if not isinstance(objects, list):
        return []
    labels: list[str] = []
    for item in objects:
        if not isinstance(item, dict):
            continue
        contract = item.get("contract")
        selector = item.get("selector")
        object_name = item.get("object")
        if isinstance(contract, str) and isinstance(selector, str):
            labels.append(f"{contract}:{selector}")
        elif isinstance(object_name, str):
            labels.append(object_name)
    return labels


def bridge_frontend_labels(objects: Any) -> list[str]:
    if not isinstance(objects, list):
        return []
    labels: set[str] = set()
    for item in objects:
        if not isinstance(item, dict):
            continue
        frontend = item.get("frontend")
        if not isinstance(frontend, dict):
            continue
        producer = frontend.get("producer")
        ast = frontend.get("ast")
        if isinstance(producer, str) and isinstance(ast, str):
            labels.add(f"{producer}:{ast}")
    return sorted(labels)


def bridge_summary_report_lines(summary_path: Path, index: int) -> list[str]:
    summary = json.loads(summary_path.read_text())
    counts = summary.get("counts", {})
    compatibility = summary.get("backendCompatibility", {})
    objects = summary.get("objects")
    prefix = f"bridge_summary_{index}"
    return [
        f"{prefix}_backend_compatibility={compatibility.get('status', 'unknown')}",
        f"{prefix}_objects={counts.get('objects', 'unknown')}",
        f"{prefix}_object_selectors={csv(bridge_object_labels(objects))}",
        f"{prefix}_frontends={csv(bridge_frontend_labels(objects))}",
        f"{prefix}_skipped_contracts={counts.get('skippedContracts', 'unknown')}",
        (
            f"{prefix}_unsupported_primitives="
            f"{csv(compatibility.get('unsupportedPrimitiveNames'))}"
        ),
        (
            f"{prefix}_object_builtins="
            f"{csv(compatibility.get('objectBuiltinNames'))}"
        ),
        (
            f"{prefix}_dialect_builtins="
            f"{csv(compatibility.get('dialectBuiltinNames'))}"
        ),
    ]


def require_bridge_summary_paths(outdir: Path) -> list[Path]:
    summary_paths = sorted(outdir.glob("bridge-json*summary.json"))
    if not summary_paths:
        raise RuntimeError(
            "Lean bytecode comparison produced no bridge summaries; "
            "the structured Yul bridge handoff was not validated"
        )
    return summary_paths


def render_harness(
    full_creation: str,
    full_runtime: str,
    lean_creation: str,
    lean_runtime: str,
    constructor_args: str,
    calldatas: Sequence[str],
    call_values: Sequence[int],
    constructor_value: int,
    compare_creation: bool = True,
    compare_runtime: bool = True,
) -> str:
    call_pushes = "\n".join(f"        calls.push(hex\"{data[2:]}\");" for data in calldatas)
    value_pushes = "\n".join(f"        values.push({value});" for value in call_values)
    creation_test = ""
    if compare_creation:
        creation_test = f"""
    function testCreationBytecodeCallResultsMatch() public {{
        _fundFor(constructorValue * 2);
        address full = _deploy(
            hex"{full_creation[2:]}",
            hex"{constructor_args[2:]}",
            constructorValue
        );
        address lean = _deploy(
            hex"{lean_creation[2:]}",
            hex"{constructor_args[2:]}",
            constructorValue
        );
        _compareSequence(full, lean);
    }}
"""
    runtime_test = ""
    if compare_runtime:
        runtime_test = f"""
    function testRuntimeBytecodeCallResultsMatch() public {{
        address full = address(0x5100);
        address lean = address(0x5101);
        vm.etch(full, hex\"{full_runtime[2:]}\");
        vm.etch(lean, hex\"{lean_runtime[2:]}\");
        _compareSequence(full, lean);
    }}
"""
    return f"""// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

interface Vm {{
    struct Log {{
        bytes32[] topics;
        bytes data;
        address emitter;
    }}

    function etch(address target, bytes calldata newRuntimeBytecode) external;
    function deal(address who, uint256 newBalance) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}}

contract BytecodeCompareTest {{
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    bytes[] private calls;
    uint256[] private values;
    uint256 private constant constructorValue = {constructor_value};

    constructor() {{
{call_pushes}
{value_pushes}
    }}

{creation_test}
{runtime_test}

    function _deploy(bytes memory initcode, bytes memory constructorArgs)
        private
        returns (address deployed)
    {{
        return _deploy(initcode, constructorArgs, 0);
    }}

    function _deploy(
        bytes memory initcode,
        bytes memory constructorArgs,
        uint256 value
    ) private returns (address deployed) {{
        bytes memory payload = bytes.concat(initcode, constructorArgs);
        assembly {{
            deployed := create(value, add(payload, 0x20), mload(payload))
        }}
        require(deployed != address(0), "create failed");
    }}

    function _fundFor(uint256 amount) private {{
        if (amount != 0) {{
            vm.deal(address(this), address(this).balance + amount);
        }}
    }}

    function _compareSequence(address full, address lean) private {{
        require(calls.length == values.length, "call/value length mismatch");
        for (uint256 i = 0; i < calls.length; i++) {{
            _fundFor(values[i] * 2);

            vm.recordLogs();
            (bool fullOk, bytes memory fullRet) =
                full.call{{value: values[i]}}(calls[i]);
            Vm.Log[] memory fullLogs = vm.getRecordedLogs();

            vm.recordLogs();
            (bool leanOk, bytes memory leanRet) =
                lean.call{{value: values[i]}}(calls[i]);
            Vm.Log[] memory leanLogs = vm.getRecordedLogs();

            require(fullOk == leanOk, "success mismatch");
            require(keccak256(fullRet) == keccak256(leanRet), "return mismatch");
            _compareLogs(fullLogs, leanLogs);
        }}
    }}

    function _compareLogs(Vm.Log[] memory fullLogs, Vm.Log[] memory leanLogs)
        private
        pure
    {{
        require(fullLogs.length == leanLogs.length, "log count mismatch");
        for (uint256 i = 0; i < fullLogs.length; i++) {{
            require(
                fullLogs[i].topics.length == leanLogs[i].topics.length,
                "log topic count mismatch"
            );
            for (uint256 j = 0; j < fullLogs[i].topics.length; j++) {{
                require(
                    fullLogs[i].topics[j] == leanLogs[i].topics[j],
                    "log topic mismatch"
                );
            }}
            require(
                keccak256(fullLogs[i].data) == keccak256(leanLogs[i].data),
                "log data mismatch"
            );
        }}
    }}
}}
"""


def run_forge_harness(
    forge: str,
    solc: str,
    outdir: Path,
    harness: str,
    evm_version: str,
) -> None:
    project = outdir / "forge"
    (project / "test").mkdir(parents=True)
    (project / "src").mkdir()
    (project / "foundry.toml").write_text(
        "\n".join(
            [
                "[profile.default]",
                'src = "src"',
                'test = "test"',
                'out = "out"',
                'cache_path = "cache"',
                f'evm_version = "{evm_version}"',
                "",
            ]
        )
    )
    (project / "test" / "BytecodeCompare.t.sol").write_text(harness)
    completed = subprocess.run(
        [
            forge,
            "test",
            "--root",
            str(project),
            "--use",
            solc,
            "--offline",
            "--match-contract",
            "BytecodeCompareTest",
            "--match-test",
            "test*BytecodeCallResultsMatch",
            "-q",
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "Forge bytecode comparison failed:\n"
            + "\n".join(
                part for part in [completed.stdout.strip(), completed.stderr.strip()] if part
            )
        )


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="Solidity source file")
    parser.add_argument("--contract", required=True, help="Contract name to compare")
    parser.add_argument(
        "--calldata",
        action="append",
        required=True,
        help="Hex calldata to replay against both deployments; repeat for sequences",
    )
    parser.add_argument(
        "--value",
        action="append",
        default=[],
        help=(
            "Wei value for the corresponding --calldata; repeat to match the "
            "calldata sequence. Defaults to zero for every call."
        ),
    )
    parser.add_argument("--constructor-args", default="0x", help="Hex constructor args")
    parser.add_argument(
        "--constructor-value",
        default="0",
        help="Wei value to send when deploying creation bytecode",
    )
    parser.add_argument(
        "--creation-only",
        action="store_true",
        help=(
            "Only compare deployments produced from creation bytecode. Use this "
            "for constructor-state tests where etching runtime bytecode would "
            "intentionally skip constructor initialization."
        ),
    )
    parser.add_argument(
        "--runtime-only",
        action="store_true",
        help=(
            "Only compare deployed runtime bytecode by etching both runtimes. "
            "Use this for pure/runtime library wrappers whose creation object "
            "needs unsupported linker or object-layout resolution."
        ),
    )
    parser.add_argument("--source-name")
    parser.add_argument("--include-source", action="append", default=[])
    parser.add_argument("--remapping", action="append", default=[])
    parser.add_argument("--remappings-file", action="append", default=[], type=Path)
    parser.add_argument("--no-auto-include-imports", dest="auto_include_imports", action="store_false")
    parser.add_argument("--linker-symbol", action="append", default=[])
    parser.add_argument("--solc", default=os.environ.get("SOLC", "/Users/dan/.local/bin/solc"))
    parser.add_argument("--solc-arg", action="append", default=[])
    parser.add_argument("--yul-ast-solc")
    parser.add_argument("--yul-ast-solc-arg", action="append", default=[])
    parser.add_argument("--lake", default=os.environ.get("LAKE", "/Users/dan/.elan/bin/lake"))
    parser.add_argument("--lake-cwd", type=Path, default=Path.cwd())
    parser.add_argument("--forge", default=os.environ.get("FORGE", "forge"))
    parser.add_argument(
        "--forge-evm-version",
        default="cancun",
        help=(
            "EVM version used to compile the generated Forge comparison harness. "
            "Older pinned solc versions may need values such as london."
        ),
    )
    parser.add_argument("--optimized", action="store_true")
    parser.add_argument(
        "--evm-version",
        choices=SUPPORTED_EVM_VERSIONS,
        default=DEFAULT_EVM_VERSION,
    )
    parser.add_argument("--optimizer-runs", type=int, metavar="N")
    parser.add_argument("--no-via-ir", dest="via_ir", action="store_false")
    parser.add_argument("--no-experimental", dest="experimental", action="store_false")
    parser.add_argument("--namespace", default="Generated.ContractCallCompare")
    parser.add_argument("--keep-tmp", action="store_true")
    parser.set_defaults(via_ir=True, experimental=True, auto_include_imports=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    root = Path(__file__).resolve().parent.parent
    script_dir = root / "scripts"
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    if args.creation_only and args.runtime_only:
        parser.error("--creation-only and --runtime-only are mutually exclusive")
    if args.optimizer_runs is not None:
        if not args.optimized:
            parser.error("--optimizer-runs requires --optimized")
        if args.optimizer_runs <= 0:
            parser.error("--optimizer-runs must be positive")
    args.solc = resolve_executable(args.solc)
    if args.yul_ast_solc:
        args.yul_ast_solc = resolve_executable(args.yul_ast_solc)
    args.forge = resolve_executable(args.forge)
    args.lake = resolve_executable(args.lake)
    calldatas = [concrete_hex(item, "calldata") for item in args.calldata]
    if args.value:
        if len(args.value) != len(calldatas):
            parser.error("--value must be repeated exactly once per --calldata")
        call_values = [
            parse_uint256(value, f"value #{index + 1}")
            for index, value in enumerate(args.value)
        ]
    else:
        call_values = [0 for _ in calldatas]
    constructor_args = concrete_hex(args.constructor_args, "constructor args")
    constructor_value = parse_uint256(args.constructor_value, "constructor value")
    outdir = Path(tempfile.mkdtemp(prefix="evm-compiler-call-compare."))
    try:
        bridge = load_bridge(script_dir)
        (
            source_name,
            contract_name,
            full_creation_raw,
            full_runtime_raw,
            full_creation_links,
            full_runtime_links,
        ) = load_full_solc_bytecode(
            bridge,
            args,
        )
        linker_symbols = [
            bridge.parse_linker_symbol_entry(entry) for entry in args.linker_symbol
        ]
        full_creation, full_runtime = link_compared_full_solc_bytecode(
            full_creation_raw,
            full_runtime_raw,
            full_creation_links,
            full_runtime_links,
            linker_symbols,
            compare_creation=not args.runtime_only,
            compare_runtime=not args.creation_only,
        )
        if args.runtime_only:
            lean_creation = "0x"
            lean_runtime = run_bridge_bytecode(
                root,
                args,
                outdir / "lean-runtime.hex",
                "runtime",
            )
        else:
            lean_artifact = run_bridge_artifact(root, args, outdir / "lean-artifact.json")
            lean_creation = concrete_hex(
                lean_artifact["bytecode"]["creation"],
                "Lean creation bytecode",
            )
            lean_runtime = concrete_hex(
                lean_artifact["bytecode"]["runtime"],
                "Lean runtime bytecode",
            )
            if args.creation_only:
                lean_runtime = "0x"
        harness = render_harness(
            full_creation,
            full_runtime,
            lean_creation,
            lean_runtime,
            constructor_args,
            calldatas,
            call_values,
            constructor_value,
            compare_creation=not args.runtime_only,
            compare_runtime=not args.creation_only,
        )
        run_forge_harness(
            args.forge,
            args.solc,
            outdir,
            harness,
            args.forge_evm_version,
        )
        summary_paths = require_bridge_summary_paths(outdir)
        print("contract_call_compare=pass")
        print(f"source={source_name}")
        print(f"contract={contract_name}")
        print(f"calls={len(calldatas)}")
        print(f"full_creation_bytes={prefixed_hex_size(full_creation)}")
        print(f"lean_creation_bytes={prefixed_hex_size(lean_creation)}")
        print(f"full_runtime_bytes={prefixed_hex_size(full_runtime)}")
        print(f"lean_runtime_bytes={prefixed_hex_size(lean_runtime)}")
        print(f"bridge_summary_count={len(summary_paths)}")
        for index, summary_path in enumerate(summary_paths, start=1):
            for line in bridge_summary_report_lines(summary_path, index):
                print(line)
        if args.keep_tmp:
            for summary_path in summary_paths:
                print(f"bridge_summary={summary_path}")
            print(f"tmp={outdir}")
        return 0
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        if args.keep_tmp:
            print(f"tmp={outdir}", file=sys.stderr)
        else:
            shutil.rmtree(outdir, ignore_errors=True)
        return 1
    finally:
        if not args.keep_tmp:
            shutil.rmtree(outdir, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
