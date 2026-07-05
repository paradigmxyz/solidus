#!/usr/bin/env python3
"""solc-compatible Standard JSON wrapper backed by the verified Lean raw path.

This wrapper is intentionally narrow: it behaves like solc for `--standard-json`
calls by reading Standard JSON from stdin and returning solc-shaped JSON with
Lean-produced bytecode.  Non-Standard-JSON invocations are delegated to the real
solc so tools can still probe `--version`, `--help`, and similar metadata.

Bytecode is produced by the supported verified route: the real solc emits
Standard JSON output including `irOptimizedAst`, and the in-Lean raw decoder
(`evm-compiler-backend raw-image`, backed by
`Solidity.RawAst.compileArtifactFromRawSolcIr?`) compiles each contract
directly from that output.  No Python-side Yul translation is involved.
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

REQUIRED_CONTRACT_OUTPUTS = [
    "irOptimizedAst",
    "metadata",
    "evm.bytecode.object",
    "evm.deployedBytecode.object",
]


def default_real_solc() -> str:
    local_solc = Path.home() / ".local" / "bin" / "solc"
    if local_solc.exists():
        return str(local_solc)
    return "solc"


def default_lake() -> str:
    local_lake = Path.home() / ".elan" / "bin" / "lake"
    if local_lake.exists():
        return str(local_lake)
    return "lake"


def env_flag_default(name: str, default: bool) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return value.strip().lower() not in {"", "0", "false", "no", "off"}


def validate_standard_json_output(output: str) -> int:
    import validate_bridge_json

    with tempfile.NamedTemporaryFile(
        "w",
        encoding="utf-8",
        suffix=".json",
        delete=False,
    ) as handle:
        handle.write(output)
        path = Path(handle.name)
    try:
        return validate_bridge_json.main(["--quiet", str(path)])
    finally:
        try:
            path.unlink()
        except FileNotFoundError:
            pass


def requested_output_names(compiler_input: Any) -> set:
    names: set = set()
    if not isinstance(compiler_input, dict):
        return names
    settings = compiler_input.get("settings")
    if not isinstance(settings, dict):
        return names
    selection = settings.get("outputSelection")
    if not isinstance(selection, dict):
        return names
    for contracts in selection.values():
        if not isinstance(contracts, dict):
            continue
        for outputs in contracts.values():
            if not isinstance(outputs, list):
                continue
            for name in outputs:
                if isinstance(name, str):
                    names.add(name)
    return names


def augment_standard_json_input(compiler_input: Any) -> Any:
    """Force viaIR and add the outputs the Lean raw decoder consumes."""
    augmented = copy.deepcopy(compiler_input)
    if not isinstance(augmented, dict):
        return augmented
    settings = augmented.setdefault("settings", {})
    if not isinstance(settings, dict):
        return augmented
    settings["viaIR"] = True
    selection = settings.setdefault("outputSelection", {})
    if not isinstance(selection, dict):
        return augmented
    star_source = selection.setdefault("*", {})
    if not isinstance(star_source, dict):
        return augmented
    star_contract = star_source.setdefault("*", [])
    if not isinstance(star_contract, list):
        return augmented
    for name in REQUIRED_CONTRACT_OUTPUTS:
        if name not in star_contract:
            star_contract.append(name)
    return augmented


def has_error(output: Any) -> bool:
    if not isinstance(output, dict):
        return True
    errors = output.get("errors")
    if not isinstance(errors, list):
        return False
    return any(
        isinstance(entry, dict) and entry.get("severity") == "error"
        for entry in errors
    )


def yul_object_names(ir_ast: Any) -> Tuple[str, str]:
    creation = ""
    runtime = ""
    if isinstance(ir_ast, dict) and ir_ast.get("nodeType") == "YulObject":
        name = ir_ast.get("name")
        if isinstance(name, str):
            creation = name
        for sub in ir_ast.get("subObjects") or []:
            if isinstance(sub, dict) and sub.get("nodeType") == "YulObject":
                sub_name = sub.get("name")
                if isinstance(sub_name, str):
                    runtime = sub_name
                    break
    return creation, runtime


class BackendError(RuntimeError):
    pass


def run_raw_backend(
    lake: str,
    lake_cwd: Path,
    raw_output_path: Path,
    source_name: str,
    contract_name: str,
    selector: str,
) -> Tuple[str, Dict[str, List[Dict[str, int]]]]:
    """Run `evm-compiler-backend raw-image` and parse bytecode + immutables."""
    command = [
        lake,
        "exe",
        "evm-compiler-backend",
        "raw-image",
        str(raw_output_path),
        source_name,
        contract_name,
        selector,
    ]
    try:
        completed = subprocess.run(
            command,
            cwd=str(lake_cwd),
            text=True,
            capture_output=True,
        )
    except FileNotFoundError as exc:
        raise BackendError(f"could not run {exc.filename!r}") from exc
    if completed.returncode != 0:
        raise BackendError(
            f"verified raw backend failed for {source_name}:{contract_name} "
            f"({selector}): "
            + (completed.stderr or completed.stdout or "").strip()
        )
    bytecode: Optional[str] = None
    immutable_references: Dict[str, List[Dict[str, int]]] = {}
    for line in (completed.stdout or "").splitlines():
        if line.startswith("bytecode=0x"):
            bytecode = line[len("bytecode=0x"):]
            continue
        if line.startswith("immutable\t"):
            parts = line.split("\t")
            if len(parts) != 4:
                raise BackendError(
                    f"malformed immutable reference line: {line!r}"
                )
            immutable_references.setdefault(parts[1], []).append(
                {"start": int(parts[2]), "length": int(parts[3])}
            )
    if bytecode is None:
        raise BackendError(
            f"verified raw backend printed no bytecode for "
            f"{source_name}:{contract_name} ({selector})"
        )
    return bytecode, immutable_references


def replace_contract_bytecode(
    contract_output: Dict[str, Any],
    source_name: str,
    contract_name: str,
    creation_bytecode: str,
    runtime_bytecode: str,
    runtime_immutable_references: Dict[str, List[Dict[str, int]]],
) -> None:
    evm = contract_output.setdefault("evm", {})
    bytecode = evm.setdefault("bytecode", {})
    deployed = evm.setdefault("deployedBytecode", {})
    bytecode["object"] = creation_bytecode
    bytecode["sourceMap"] = ""
    bytecode["linkReferences"] = {}
    bytecode["generatedSources"] = []
    deployed["object"] = runtime_bytecode
    deployed["sourceMap"] = ""
    deployed["linkReferences"] = {}
    deployed["generatedSources"] = []
    deployed["immutableReferences"] = runtime_immutable_references
    creation_object, runtime_object = yul_object_names(
        contract_output.get("irOptimizedAst")
    )
    contract_output["evmCompiler"] = {
        "schema": "evm-compiler.solc-standard-json-output.v1",
        "source": source_name,
        "contract": contract_name,
        "yul": {
            "creationObject": creation_object or contract_name,
            "runtimeObject": runtime_object or (contract_name + "_deployed"),
        },
        "sizes": {
            "creationBytes": len(creation_bytecode) // 2,
            "runtimeBytes": len(runtime_bytecode) // 2,
        },
        "bytecodeSource": "lean-unchecked-bytecode-image",
    }


def deployable_contract(contract_output: Any) -> bool:
    if not isinstance(contract_output, dict):
        return False
    if not isinstance(contract_output.get("irOptimizedAst"), dict):
        return False
    evm = contract_output.get("evm")
    if not isinstance(evm, dict):
        return False
    bytecode = evm.get("bytecode")
    if not isinstance(bytecode, dict):
        return False
    solc_object = bytecode.get("object")
    return isinstance(solc_object, str) and solc_object != ""


def strip_unrequested_outputs(output: Any, requested: set) -> None:
    """Drop outputs this wrapper added but the caller did not request."""
    if not isinstance(output, dict):
        return
    contracts_by_source = output.get("contracts")
    if not isinstance(contracts_by_source, dict):
        return
    for contracts in contracts_by_source.values():
        if not isinstance(contracts, dict):
            continue
        for contract_output in contracts.values():
            if not isinstance(contract_output, dict):
                continue
            if "irOptimizedAst" not in requested:
                contract_output.pop("irOptimizedAst", None)
            if "metadata" not in requested:
                contract_output.pop("metadata", None)


def compile_standard_json(argv: List[str]) -> int:
    script_dir = Path(__file__).resolve().parent
    root = script_dir.parent
    real_solc = os.environ.get("SOLC_LEAN_REAL_SOLC", default_real_solc())
    lake = os.environ.get("SOLC_LEAN_LAKE", os.environ.get("LAKE", default_lake()))
    lake_cwd = Path(os.environ.get("SOLC_LEAN_LAKE_CWD", root))
    if os.environ.get("SOLC_LEAN_BRIDGE_JSON_DIR"):
        print(
            "note: SOLC_LEAN_BRIDGE_JSON_DIR is ignored; the unverified "
            "Python bridge route was retired in favor of the in-Lean raw "
            "solc Standard JSON path",
            file=sys.stderr,
        )
    extra_solc_args = [arg for arg in argv if arg != "--standard-json"]
    input_text = sys.stdin.read()
    try:
        compiler_input = json.loads(input_text)
    except json.JSONDecodeError as exc:
        print(f"error: could not parse Standard JSON input: {exc}", file=sys.stderr)
        return 1
    requested = requested_output_names(compiler_input)
    augmented = augment_standard_json_input(compiler_input)
    try:
        completed = subprocess.run(
            [real_solc, *extra_solc_args, "--standard-json"],
            input=json.dumps(augmented, separators=(",", ":")),
            text=True,
            capture_output=True,
        )
    except FileNotFoundError:
        print(
            f"error: could not find real solc executable {real_solc!r}; "
            "set SOLC_LEAN_REAL_SOLC",
            file=sys.stderr,
        )
        return 1
    if completed.stderr:
        sys.stderr.write(completed.stderr)
    if completed.returncode != 0:
        if completed.stdout:
            sys.stdout.write(completed.stdout)
        return completed.returncode
    try:
        output = json.loads(completed.stdout or "")
    except json.JSONDecodeError as exc:
        print(f"error: could not parse solc output: {exc}", file=sys.stderr)
        return 1
    if has_error(output) or not isinstance(output.get("contracts"), dict):
        # Let the caller see solc's own diagnostics unchanged.
        sys.stdout.write(completed.stdout)
        return 0
    raw_output_path: Optional[Path] = None
    try:
        with tempfile.NamedTemporaryFile(
            "w",
            encoding="utf-8",
            suffix=".standard-output.json",
            delete=False,
        ) as handle:
            handle.write(completed.stdout)
            raw_output_path = Path(handle.name)
        for source_name, contracts in output["contracts"].items():
            if not isinstance(contracts, dict):
                continue
            for contract_name, contract_output in contracts.items():
                if not deployable_contract(contract_output):
                    continue
                try:
                    creation, _ = run_raw_backend(
                        lake,
                        lake_cwd,
                        raw_output_path,
                        source_name,
                        contract_name,
                        "creation",
                    )
                    runtime, runtime_immutables = run_raw_backend(
                        lake,
                        lake_cwd,
                        raw_output_path,
                        source_name,
                        contract_name,
                        "runtime",
                    )
                except BackendError as exc:
                    print(f"error: {exc}", file=sys.stderr)
                    return 1
                replace_contract_bytecode(
                    contract_output,
                    source_name,
                    contract_name,
                    creation,
                    runtime,
                    runtime_immutables,
                )
    finally:
        if raw_output_path is not None:
            try:
                raw_output_path.unlink()
            except FileNotFoundError:
                pass
    strip_unrequested_outputs(output, requested)
    rendered = json.dumps(output, indent=2) + "\n"
    if env_flag_default("SOLC_LEAN_VALIDATE_OUTPUT", True):
        validation_result = validate_standard_json_output(rendered)
        if validation_result != 0:
            print(
                "error: solc-lean produced invalid Standard JSON output",
                file=sys.stderr,
            )
            return validation_result
    sys.stdout.write(rendered)
    return 0


def main(argv: list[str]) -> int:
    real_solc = os.environ.get("SOLC_LEAN_REAL_SOLC", default_real_solc())
    if "--standard-json" not in argv:
        try:
            return subprocess.run([real_solc, *argv]).returncode
        except FileNotFoundError:
            print(
                f"error: could not find real solc executable {real_solc!r}; "
                "set SOLC_LEAN_REAL_SOLC",
                file=sys.stderr,
            )
            return 1
    return compile_standard_json(argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
