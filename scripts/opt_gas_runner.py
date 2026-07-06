#!/usr/bin/env python3
"""Deterministic gas runner + vector tooling for the optimization harness.

The contest metric is *total gas*: for every corpus contract,

    total_gas = deploy_gas + exec_gas

where

  * ``deploy_gas`` is the **deployment transaction** cost, priced arithmetically
    from the yellow paper (``deploy_gas_model = "computed"``) so it is defined
    even for contracts that violate EIP-170 and could never actually deploy:

        deploy_gas = 21000                       (G_transaction)
                   + 32000                       (G_txcreate)
                   + calldata_cost(creation)     (4/zero byte, 16/non-zero byte)
                   + 2 * ceil(len(creation)/32)  (EIP-3860 initcode word cost)
                   + 200 * runtime_bytes         (code-deposit, 200/byte)

  * ``exec_gas`` is the summed cost of a fixed, ordered set of execution
    vectors (``exec_gas_model = "measured-callgas+intrinsic"``): each vector is
    replayed against the deployed image inside a pinned Foundry EVM; the raw
    ``CALL`` opcode gas is measured with ``gasleft()`` deltas and the per-
    transaction intrinsic (21000 + calldata cost of the vector) is added so the
    number is a faithful EOA->contract transaction cost.

Deployability caps (hard validity constraints, reported but never excluded):

  * EIP-170  : runtime image  <= 24576 bytes
  * EIP-3860 : creation image <= 49152 bytes

The executor is Foundry ``forge test`` (same engine the repo's differential
execution-compare gates use: ``scripts/compare_contract_call_bytecode.py``).
The runtime image is injected with ``vm.etch`` (or a real ``CREATE`` when the
creation image both fits the caps and deploys cleanly, so constructor state and
immutables are honoured); ``etch`` also lets us execute — and therefore price —
contracts whose runtime exceeds EIP-170.

This module is imported by ``scripts/opt_harness.py`` and also exposes two CLI
subcommands:

    opt_gas_runner.py gen-vectors [--force]   bootstrap benchmarks/vectors/*.json
    opt_gas_runner.py run <Source.sol:Contract>   measure one contract (debug)
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = REPO_ROOT / "scripts"
BENCH_DIR = REPO_ROOT / "benchmarks"
VECTORS_DIR = BENCH_DIR / "vectors"

# Deployability caps.
EIP170_RUNTIME_CAP = 24576
EIP3860_CREATION_CAP = 49152

# Yellow-paper gas constants.
G_TRANSACTION = 21000
G_TXCREATE = 32000
G_CODEDEPOSIT_PER_BYTE = 200
G_INITCODE_WORD = 2  # EIP-3860
G_CALLDATA_ZERO = 4
G_CALLDATA_NONZERO = 16

DEPLOY_GAS_FORMULA = (
    "21000 + 32000 + calldata_cost(creation,4/16) "
    "+ 2*ceil(len(creation)/32) + 200*runtime_bytes"
)
DEPLOY_GAS_MODEL = "computed"
EXEC_GAS_MODEL = "measured-callgas+intrinsic (30M block-budget per call)"

# Fixed test EVM parameters (recorded in output for reproducibility).
FORGE_EVM_VERSION = "cancun"
DEFAULT_SENDER = "0x00000000000000000000000000000000000010a0"
ETCH_ADDR = "0x0000000000000000000000000000000000005100"

# Each vector forwards at most a realistic mainnet block budget of gas.  A real
# deployment/execution transaction cannot exceed the block gas limit, so
# forwarding Foundry's ~1e9 test budget would let a single gas-consume-all path
# (e.g. an invalid-input precompile that burns all forwarded gas) dwarf the
# whole suite.  A vector that would exceed this budget OOG-reverts and is priced
# at the budget.
GAS_BUDGET_PER_CALL = 30_000_000


# --------------------------------------------------------------------------
# gas arithmetic
# --------------------------------------------------------------------------

def _bytes_of_hex(hexstr: str) -> bytes:
    h = hexstr[2:] if hexstr.startswith(("0x", "0X")) else hexstr
    if h == "":
        return b""
    return bytes.fromhex(h)


def calldata_cost(data: bytes) -> int:
    zeros = data.count(0)
    nonzeros = len(data) - zeros
    return zeros * G_CALLDATA_ZERO + nonzeros * G_CALLDATA_NONZERO


def compute_deploy_gas(creation_hex: str, runtime_bytes: int) -> int:
    creation = _bytes_of_hex(creation_hex)
    words = math.ceil(len(creation) / 32) if creation else 0
    return (
        G_TRANSACTION
        + G_TXCREATE
        + calldata_cost(creation)
        + G_INITCODE_WORD * words
        + G_CODEDEPOSIT_PER_BYTE * runtime_bytes
    )


def vector_intrinsic(calldata_hex: str) -> int:
    return G_TRANSACTION + calldata_cost(_bytes_of_hex(calldata_hex))


def cap_ok(runtime_bytes: int, creation_bytes: int) -> bool:
    return (runtime_bytes <= EIP170_RUNTIME_CAP
            and creation_bytes <= EIP3860_CREATION_CAP)


# --------------------------------------------------------------------------
# forge executor
# --------------------------------------------------------------------------

def _hex_body(hexstr: str) -> str:
    h = hexstr[2:] if hexstr.startswith(("0x", "0X")) else hexstr
    return h.lower()


def render_gas_harness(runtime_hex: str, creation_hex: str,
                       deploy: Dict[str, Any],
                       vectors: List[Dict[str, Any]],
                       result_name: str) -> str:
    """Render a Forge test that deploys/etches the image, replays every vector
    measuring raw CALL gas, and writes ``used,ok`` lines to ``result_path``."""
    ctor_args = _hex_body(deploy.get("constructor_args", "0x") or "0x")
    ctor_value = int(deploy.get("value", 0) or 0)

    push_lines = []
    for v in vectors:
        data = _hex_body(v.get("calldata", "0x") or "0x")
        value = int(v.get("value", 0) or 0)
        sender = v.get("sender") or DEFAULT_SENDER
        push_lines.append(f'        _add(hex"{data}", {value}, {sender});')
    pushes = "\n".join(push_lines)

    return f"""// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

interface Vm {{
    function etch(address target, bytes calldata code) external;
    function deal(address who, uint256 balance) external;
    function prank(address who) external;
    function toString(uint256 v) external pure returns (string memory);
    function writeFile(string calldata path, string calldata data) external;
}}

contract GasRunner {{
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    bytes[] private calls;
    uint256[] private values;
    address[] private senders;

    function _add(bytes memory data, uint256 value, address sender) private {{
        calls.push(data);
        values.push(value);
        senders.push(sender);
    }}

    function _register() private {{
{pushes}
    }}

    function _target() private returns (address target) {{
        bytes memory payload =
            bytes.concat(hex"{_hex_body(creation_hex)}", hex"{ctor_args}");
        uint256 cval = {ctor_value};
        if (cval != 0) {{ vm.deal(address(this), cval); }}
        address created;
        assembly {{
            created := create(cval, add(payload, 0x20), mload(payload))
        }}
        if (created != address(0)) {{
            return created;
        }}
        target = address(0x5100);
        vm.etch(target, hex"{_hex_body(runtime_hex)}");
    }}

    function test_gas() public {{
        _register();
        address target = _target();
        string memory out = "";
        for (uint256 i = 0; i < calls.length; i++) {{
            bytes memory data = calls[i];
            uint256 v = values[i];
            vm.deal(address(this), v);
            uint256 ok;
            uint256 g0;
            uint256 g1;
            address sender = senders[i];
            vm.prank(sender);
            assembly {{
                g0 := gas()
                ok := call({GAS_BUDGET_PER_CALL}, target, v, add(data, 0x20), mload(data), 0, 0)
                g1 := gas()
            }}
            uint256 used = g0 - g1;
            out = string.concat(
                out, vm.toString(used), ",", vm.toString(ok), "\\n"
            );
        }}
        vm.writeFile("{result_name}", out);
    }}
}}
"""


def run_forge_gas(forge: str, solc: str, runtime_hex: str, creation_hex: str,
                  deploy: Dict[str, Any], vectors: List[Dict[str, Any]],
                  workdir: Path) -> List[Tuple[int, bool]]:
    """Run the gas harness; return per-vector ``(call_gas, ok)`` in order."""
    if not vectors:
        return []
    project = workdir / "forge"
    (project / "test").mkdir(parents=True, exist_ok=True)
    (project / "src").mkdir(parents=True, exist_ok=True)
    result_name = "gas.out"
    result_path = project / result_name
    (project / "foundry.toml").write_text("\n".join([
        "[profile.default]",
        'src = "src"',
        'test = "test"',
        'out = "out"',
        'cache_path = "cache"',
        f'evm_version = "{FORGE_EVM_VERSION}"',
        'fs_permissions = [{ access = "read-write", path = "./" }]',
        "",
    ]))
    harness = render_gas_harness(runtime_hex, creation_hex, deploy, vectors,
                                 result_name)
    (project / "test" / "GasRunner.t.sol").write_text(harness)
    proc = subprocess.run(
        [forge, "test", "--root", str(project), "--use", solc, "--offline",
         "--match-contract", "GasRunner", "--match-test", "test_gas", "-q"],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if proc.returncode != 0 or not result_path.exists():
        raise RuntimeError(
            "forge gas harness failed:\n"
            + "\n".join(p for p in [proc.stdout.strip(), proc.stderr.strip()]
                        if p)[:4000])
    out: List[Tuple[int, bool]] = []
    for line in result_path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        used_s, ok_s = line.split(",")
        out.append((int(used_s), ok_s.strip() == "1"))
    if len(out) != len(vectors):
        raise RuntimeError(
            f"gas harness produced {len(out)} results for {len(vectors)} "
            "vectors")
    return out


def measure_contract(forge: str, solc: str, name: str,
                     creation_hex: str, runtime_hex: str,
                     runtime_bytes: int, creation_bytes: int,
                     vspec: Dict[str, Any]) -> Dict[str, Any]:
    """Measure deploy + exec gas for one contract.  Pure arithmetic for the
    deploy leg; Foundry for the exec leg."""
    deploy = vspec.get("deploy") or {}
    vectors = vspec.get("vectors") or []
    deploy_gas = compute_deploy_gas(creation_hex, runtime_bytes)

    per_vector: List[Dict[str, Any]] = []
    exec_gas = 0
    if vectors:
        with tempfile.TemporaryDirectory(prefix="opt-gas.") as td:
            results = run_forge_gas(forge, solc, runtime_hex, creation_hex,
                                    deploy, vectors, Path(td))
        for v, (call_gas, ok) in zip(vectors, results):
            intrinsic = vector_intrinsic(v.get("calldata", "0x") or "0x")
            tx_gas = call_gas + intrinsic
            exec_gas += tx_gas
            per_vector.append({
                "calldata": v.get("calldata", "0x"),
                "value": int(v.get("value", 0) or 0),
                "gas": tx_gas,
                "call_gas": call_gas,
                "intrinsic": intrinsic,
                "ok": ok,
            })
    return {
        "name": name,
        "runtime_bytes": runtime_bytes,
        "creation_bytes": creation_bytes,
        "deploy_gas": deploy_gas,
        "deploy_gas_model": DEPLOY_GAS_MODEL,
        "exec_gas": exec_gas,
        "exec_gas_model": EXEC_GAS_MODEL,
        "total_gas": deploy_gas + exec_gas,
        "cap_ok": cap_ok(runtime_bytes, creation_bytes),
        "eip170_ok": runtime_bytes <= EIP170_RUNTIME_CAP,
        "eip3860_ok": creation_bytes <= EIP3860_CREATION_CAP,
        "vectors": len(vectors),
        "vector_source": vspec.get("source", "none"),
        "per_vector": per_vector,
    }


# --------------------------------------------------------------------------
# vector files
# --------------------------------------------------------------------------

def vector_path(name: str) -> Path:
    """benchmarks/vectors/<Contract>.vectors.json (short contract name)."""
    short = name.split(":")[-1]
    return VECTORS_DIR / f"{short}.vectors.json"


def load_vectors(name: str) -> Dict[str, Any]:
    path = vector_path(name)
    if not path.exists():
        return {"contract": name, "source": "missing", "deploy": {},
                "vectors": [], "empty_reason": "no vector file"}
    spec = json.loads(path.read_text())
    spec.setdefault("deploy", {})
    spec.setdefault("vectors", [])
    return spec


# --------------------------------------------------------------------------
# ABI zero-encoding (for auto-generated vectors)
# --------------------------------------------------------------------------

def _split_top(types: str) -> List[str]:
    out, depth, cur = [], 0, ""
    for ch in types:
        if ch in "([":
            depth += 1
            cur += ch
        elif ch in ")]":
            depth -= 1
            cur += ch
        elif ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def _is_dynamic(t: str) -> bool:
    if t in ("bytes", "string"):
        return True
    m = re.fullmatch(r"(.+)\[(\d*)\]", t)
    if m:
        base, count = m.group(1), m.group(2)
        if count == "":
            return True
        return _is_dynamic(base)
    if t.startswith("(") and t.endswith(")"):
        return any(_is_dynamic(x) for x in _split_top(t[1:-1]))
    return False


def _static_words(t: str) -> int:
    m = re.fullmatch(r"(.+)\[(\d+)\]", t)
    if m:
        return int(m.group(2)) * _static_words(m.group(1))
    if t.startswith("(") and t.endswith(")"):
        return sum(_static_words(x) for x in _split_top(t[1:-1]))
    return 1  # elementary static


def zero_encode(sig: str) -> Optional[str]:
    """Return hex calldata (0x + selector-less body) of all-zero arguments for
    the signature's parameter list, or None if a param type is unsupported."""
    inner = sig[sig.index("(") + 1:sig.rindex(")")]
    if inner == "":
        return ""
    params = _split_top(inner)
    head_words: List[int] = []  # word count contributed to head per param
    dyn_flags: List[bool] = []
    try:
        for p in params:
            dyn = _is_dynamic(p)
            dyn_flags.append(dyn)
            head_words.append(1 if dyn else _static_words(p))
    except Exception:
        return None
    total_head_words = sum(head_words)
    head = bytearray()
    tail = bytearray()
    for p, dyn, hw in zip(params, dyn_flags, head_words):
        if dyn:
            offset = 32 * total_head_words + len(tail)
            head += offset.to_bytes(32, "big")
            tail += (0).to_bytes(32, "big")  # empty bytes/string/array
        else:
            head += bytes(32 * hw)
    return (bytes(head) + bytes(tail)).hex()


# --------------------------------------------------------------------------
# gen-vectors: bootstrap vector files
# --------------------------------------------------------------------------

def _solc_method_ids(source_path: Path, solc: str) -> Dict[str, Dict[str, str]]:
    content = source_path.read_text()
    std = {
        "language": "Solidity",
        "sources": {source_path.name: {"content": content}},
        "settings": {"outputSelection": {"*": {"*": ["evm.methodIdentifiers"]}}},
    }
    proc = subprocess.run([solc, "--standard-json"], input=json.dumps(std),
                          capture_output=True, text=True)
    out = json.loads(proc.stdout or "{}")
    result: Dict[str, Dict[str, str]] = {}
    for _src, contracts in (out.get("contracts") or {}).items():
        for cname, cdata in contracts.items():
            mids = (cdata.get("evm") or {}).get("methodIdentifiers") or {}
            result[cname] = mids
    return result


def auto_vectors_for(mids: Dict[str, str], limit: int = 8) -> List[Dict[str, Any]]:
    vectors: List[Dict[str, Any]] = []
    for sig, selector in mids.items():
        body = zero_encode(sig)
        if body is None:
            continue
        vectors.append({
            "calldata": "0x" + selector + body,
            "value": 0,
            "sender": DEFAULT_SENDER,
            "note": sig,
        })
        if len(vectors) >= limit:
            break
    return vectors


# --------------------------------------------------------------------------
# test-derived vectors: parse the execution-compare shell scripts
# --------------------------------------------------------------------------

TEST_SCRIPTS = [
    "scripts/test_solidity_contract_call_compare.sh",
    "scripts/test_solidity_execution_coverage_compare.sh",
]


def parse_test_scripts() -> Dict[str, Dict[str, Any]]:
    """Extract per-contract vector specs from the differential execution-compare
    scripts.  Returns {contract_short: {source, deploy, vectors}}."""
    out: Dict[str, Dict[str, Any]] = {}
    for rel in TEST_SCRIPTS:
        path = REPO_ROOT / rel
        if not path.exists():
            continue
        text = path.read_text().replace("\\\n", " ")
        for line in text.splitlines():
            if "--contract" not in line or "--calldata" not in line:
                continue
            toks = line.split()
            contract = None
            ctor_args = "0x"
            ctor_value = 0
            vectors: List[Dict[str, Any]] = []
            i = 0
            while i < len(toks):
                t = toks[i]
                if t == "--contract" and i + 1 < len(toks):
                    contract = toks[i + 1]
                    i += 2
                elif t == "--calldata" and i + 1 < len(toks):
                    vectors.append({"calldata": toks[i + 1], "value": 0,
                                    "sender": DEFAULT_SENDER})
                    i += 2
                elif t == "--value" and i + 1 < len(toks) and vectors:
                    vectors[-1]["value"] = int(toks[i + 1], 0)
                    i += 2
                elif t == "--constructor-args" and i + 1 < len(toks):
                    ctor_args = toks[i + 1]
                    i += 2
                elif t == "--constructor-value" and i + 1 < len(toks):
                    ctor_value = int(toks[i + 1], 0)
                    i += 2
                else:
                    i += 1
            if contract is None or not vectors:
                continue
            out[contract] = {
                "source_test": rel,
                "deploy": {"constructor_args": ctor_args, "value": ctor_value},
                "vectors": vectors,
            }
    return out


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def _default_solc() -> str:
    local = Path.home() / ".local" / "bin" / "solc"
    return str(local) if local.exists() else "solc"


def _deployable_universe() -> List[str]:
    """Deployable 'Source.sol:Contract' names, from the current baseline."""
    for candidate in (BENCH_DIR / "opt_baseline.json",
                      BENCH_DIR / "opt_baseline_size_only.json"):
        if candidate.exists():
            data = json.loads(candidate.read_text())
            return [c["name"] for c in data.get("contracts", [])]
    return []


def cmd_gen_vectors(args: argparse.Namespace) -> int:
    solc = args.solc
    VECTORS_DIR.mkdir(parents=True, exist_ok=True)
    derived = parse_test_scripts()

    universe = _deployable_universe()
    # Group deployable contracts by source basename.
    by_source: Dict[str, List[str]] = {}
    for full in universe:
        src = full.split(":")[0]
        by_source.setdefault(src, []).append(full)

    # Corpus sources (so we only generate for the measured set).
    corpus_sources = []
    manifest = BENCH_DIR / "corpus.txt"
    for raw in manifest.read_text().splitlines():
        s = raw.strip()
        if s and not s.startswith("#"):
            corpus_sources.append(s)
    corpus_basenames = {Path(s).name for s in corpus_sources}

    written, skipped = 0, 0
    for src_path in corpus_sources:
        basename = Path(src_path).name
        fulls = by_source.get(basename, [])
        if not fulls:
            continue
        mids_by_contract = _solc_method_ids(REPO_ROOT / src_path, solc)
        for full in fulls:
            short = full.split(":")[-1]
            path = vector_path(full)
            if path.exists() and not args.force:
                skipped += 1
                continue
            mids = mids_by_contract.get(short, {})
            if short in derived:
                d = derived[short]
                spec = {
                    "contract": full,
                    "source": f"derived-from-test:{d['source_test']}",
                    "deploy": d["deploy"],
                    "vectors": d["vectors"],
                    "empty_reason": None,
                }
            elif mids:
                spec = {
                    "contract": full,
                    "source": "auto-abi-zeroargs",
                    "deploy": {"constructor_args": "0x", "value": 0},
                    "vectors": auto_vectors_for(mids),
                    "empty_reason": None,
                }
            else:
                spec = {
                    "contract": full,
                    "source": "empty",
                    "deploy": {"constructor_args": "0x", "value": 0},
                    "vectors": [],
                    "empty_reason": ("no external/public functions "
                                     "(library with only internal linkage or "
                                     "interface); deployment gas only"),
                }
            path.write_text(json.dumps(spec, indent=2) + "\n")
            written += 1
    print(f"gen-vectors: wrote {written}, skipped {skipped} existing "
          f"(--force to overwrite) into {VECTORS_DIR.relative_to(REPO_ROOT)}")
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    """Debug: measure one contract by compiling it through the raw solc path."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "solc_lean_standard_json", SCRIPTS / "solc_lean_standard_json.py")
    # Reuse opt_harness's compile to fetch bytecode.
    oh = importlib.util.spec_from_file_location(
        "opt_harness", SCRIPTS / "opt_harness.py")
    mod = importlib.util.module_from_spec(oh)
    oh.loader.exec_module(mod)
    env = mod.tool_env()
    full = args.contract
    src = full.split(":")[0]
    rel = None
    for raw in (BENCH_DIR / "corpus.txt").read_text().splitlines():
        s = raw.strip()
        if s and not s.startswith("#") and Path(s).name == src:
            rel = s
            break
    if rel is None:
        print(f"error: source for {full} not found in corpus", file=sys.stderr)
        return 2
    result = mod.compile_source(rel, env)
    match = next((c for c in result["contracts"] if c["name"] == full), None)
    if match is None:
        print(f"error: {full} did not compile", file=sys.stderr)
        return 2
    vspec = load_vectors(full)
    forge = os.environ.get("FORGE", "forge")
    out = measure_contract(forge, env["SOLC"], full,
                           match["creation_hex"], match["runtime_hex"],
                           match["runtime_bytes"], match["creation_bytes"],
                           vspec)
    print(json.dumps(out, indent=2))
    return 0


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="opt_gas_runner")
    sub = parser.add_subparsers(dest="command", required=True)
    g = sub.add_parser("gen-vectors")
    g.add_argument("--force", action="store_true")
    g.add_argument("--solc", default=_default_solc())
    r = sub.add_parser("run")
    r.add_argument("contract")
    args = parser.parse_args(argv)
    if args.command == "gen-vectors":
        return cmd_gen_vectors(args)
    if args.command == "run":
        return cmd_run(args)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
