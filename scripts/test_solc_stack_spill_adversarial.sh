#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-stack-spill-adversarial.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

FIXTURE="$ROOT/examples/AdversarialStackPressure.sol"
CONVENTIONAL_OUT="$OUTDIR/conventional.txt"
if "$SOLC_BIN" --optimize --bin "$FIXTURE" >"$CONVENTIONAL_OUT" 2>&1; then
  printf 'error: conventional codegen unexpectedly accepted hostile pressure\n' >&2
  exit 1
fi
if ! grep -q 'Stack too deep' "$CONVENTIONAL_OUT"; then
  printf 'error: conventional codegen failed for an unexpected reason\n' >&2
  cat "$CONVENTIONAL_OUT" >&2
  exit 1
fi

CREATION_BRIDGE="$OUTDIR/adversarial.creation.bridge.json"
RUNTIME_BRIDGE="$OUTDIR/adversarial.runtime.bridge.json"
for selector in creation runtime; do
  output="$OUTDIR/adversarial.$selector.bridge.json"
  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$FIXTURE" \
    --solc "$SOLC_BIN" \
    --optimized \
    --contract AdversarialStackPressure \
    --object "$selector" \
    --format bridge-json \
    --output "$output"
  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$output"
done

"$PYTHON_BIN" - "$RUNTIME_BRIDGE" <<'PY'
import json
import sys
from collections import Counter
from pathlib import Path

root = json.loads(Path(sys.argv[1]).read_text())
if root.get("frontend") != {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"}:
    raise SystemExit(f"unexpected frontend boundary: {root.get('frontend')!r}")

calls = Counter()


def visit(value):
    if isinstance(value, dict):
        callee = value.get("callee")
        if isinstance(callee, str):
            calls[callee] += 1
        for child in value.values():
            visit(child)
    elif isinstance(value, list):
        for child in value:
            visit(child)


visit(root)
minimums = {"memoryguard": 1, "mstore": 8, "mload": 8}
missing = {
    name: (calls[name], minimum)
    for name, minimum in minimums.items()
    if calls[name] < minimum
}
if missing:
    raise SystemExit(f"optimized Yul did not expose expected solc spills: {missing!r}")

print(f"adversarial_memoryguard_calls={calls['memoryguard']}")
print(f"adversarial_mstore_calls={calls['mstore']}")
print(f"adversarial_mload_calls={calls['mload']}")
PY

for selector in creation runtime; do
  "$LAKE_BIN" exe evm-compiler-backend summary \
    "$OUTDIR/adversarial.$selector.bridge.json" \
    >"$OUTDIR/adversarial.$selector.backend.txt"
done

"$LAKE_BIN" exe evm-compiler-backend stack-diagnostics "$RUNTIME_BRIDGE" \
  >"$OUTDIR/adversarial.runtime.diagnostics.txt"

"$PYTHON_BIN" - \
  "$OUTDIR/adversarial.creation.backend.txt" \
  "$OUTDIR/adversarial.runtime.backend.txt" \
  "$OUTDIR/adversarial.runtime.diagnostics.txt" <<'PY'
import sys
from pathlib import Path


def lines(path):
    return Path(path).read_text().splitlines()


for selector, path in zip(("creation", "runtime"), sys.argv[1:3]):
    bytecode = [line for line in lines(path) if line.startswith("bytecode_bytes=")]
    if len(bytecode) != 1 or int(bytecode[0].split("=", 1)[1]) <= 0:
        raise SystemExit(f"{selector} did not produce checked raw bytecode")
    print(f"adversarial_{selector}_bytecode_bytes={bytecode[0].split('=', 1)[1]}")

diagnostics = set(lines(sys.argv[3]))
required = {
    "stack_frontend_object_artifact=true",
    "stack_program_artifact=true",
    "liveness_ok=1",
    "schedule_ok=1",
    "lowering_ok=1",
    "next_use_ok=1",
    "first_failure=none",
}
missing = sorted(required - diagnostics)
if missing:
    raise SystemExit(f"hostile runtime missed checked stack gates: {missing!r}")
PY

MATRIX_SOURCE="$OUTDIR/GeneratedPressureMatrix.sol"
"$PYTHON_BIN" - "$MATRIX_SOURCE" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
params = ", ".join(f"uint256 p{i}" for i in range(20))
param_sum = " + ".join(f"p{i}" for i in range(20))
returns = ", ".join("uint256" for _ in range(18))
tuple_values = ", ".join(f"seed + {i}" for i in range(18))
internal_params = ", ".join(f"uint256 p{i}" for i in range(14))
internal_args = ", ".join(f"seed + {i}" for i in range(14))
internal_sum = " + ".join(f"p{i}" for i in range(14))

path.write_text(f'''// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract GeneratedTuplePressure {{
    function pressure(uint256 seed) external pure returns ({returns}) {{
        return ({tuple_values});
    }}
}}

contract GeneratedParameterPressure {{
    function pressure({params}) external pure returns (uint256) {{
        unchecked {{ return {param_sum}; }}
    }}
}}

contract GeneratedNestedControlPressure {{
    function pressure(uint256 seed) external pure returns (uint256 result) {{
        result = seed;
        if (seed & 1 == 0) {{
            if (seed & 2 == 0) {{ result += 11; }}
            else {{ result += 17; }}
        }} else if (seed & 4 == 0) {{
            result += 23;
        }} else {{
            result += 29;
        }}
    }}
}}

contract GeneratedLoopPressure {{
    function pressure(uint256[] calldata values) external pure returns (uint256 result) {{
        for (uint256 i; i < values.length; ++i) {{
            if (values[i] & 1 == 0) result += values[i];
            else result ^= values[i];
        }}
    }}
}}

contract GeneratedInternalCallPressure {{
    function pressure(uint256 seed) external pure returns (uint256) {{
        return combine({internal_args});
    }}

    function combine({internal_params}) internal pure returns (uint256) {{
        unchecked {{ return {internal_sum}; }}
    }}
}}

contract GeneratedDynamicMemoryPressure {{
    function pressure(uint256 count) external pure returns (bytes memory result) {{
        result = new bytes(count);
        for (uint256 i; i < count; ++i) result[i] = bytes1(uint8(i));
    }}
}}

contract GeneratedChild {{
    uint256 public immutable value;
    constructor(uint256 initial) {{ value = initial; }}
}}

contract GeneratedCallCreatePressure {{
    function pressure(address target, uint256 value, bytes32 salt)
        external returns (bytes32 digest, address child, address child2)
    {{
        (bool ok, bytes memory data) = target.call(abi.encode(value));
        require(ok);
        child = address(new GeneratedChild(value));
        child2 = address(new GeneratedChild{{salt: salt}}(value + 1));
        digest = keccak256(data);
    }}
}}

contract GeneratedUnsafeAssemblyPressure {{
    function pressure(uint256 value) external pure returns (uint256 result) {{
        assembly {{
            mstore(0, value)
            result := mload(0)
        }}
    }}
}}
''')
PY

MATRIX_DIR="$OUTDIR/matrix-bridge"
MATRIX_MANIFEST="$MATRIX_DIR/manifest.json"
mkdir -p "$MATRIX_DIR"
"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$MATRIX_SOURCE" \
  --solc "$SOLC_BIN" \
  --optimized \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$MATRIX_DIR" \
  --output "$MATRIX_MANIFEST"
"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MATRIX_MANIFEST"

"$PYTHON_BIN" - \
  "$MATRIX_MANIFEST" "$MATRIX_DIR" "$LAKE_BIN" "$ROOT" <<'PY'
import json
import subprocess
import sys
from pathlib import Path

manifest_path = Path(sys.argv[1])
bridge_dir = Path(sys.argv[2])
lake = sys.argv[3]
root = sys.argv[4]
manifest = json.loads(manifest_path.read_text())

required_contracts = {
    "GeneratedTuplePressure",
    "GeneratedParameterPressure",
    "GeneratedNestedControlPressure",
    "GeneratedLoopPressure",
    "GeneratedInternalCallPressure",
    "GeneratedDynamicMemoryPressure",
    "GeneratedCallCreatePressure",
    "GeneratedUnsafeAssemblyPressure",
}
seen = {name: set() for name in required_contracts}
checked = 0

for entry in manifest.get("entries", []):
    contract = entry.get("contract")
    selector = entry.get("selector")
    path = bridge_dir / entry["path"]
    bridge = json.loads(path.read_text())
    if bridge.get("frontend") != {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"}:
        raise SystemExit(f"{contract}/{selector}: frontend provenance drift")
    completed = subprocess.run(
        [lake, "exe", "evm-compiler-backend", "summary", str(path)],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if completed.returncode != 0:
        raise SystemExit(
            f"{contract}/{selector}: stack backend rejected generated pressure:\n"
            f"{completed.stdout}"
        )
    bytecode = [
        line for line in completed.stdout.splitlines()
        if line.startswith("bytecode_bytes=")
    ]
    if len(bytecode) != 1 or int(bytecode[0].split("=", 1)[1]) <= 0:
        raise SystemExit(f"{contract}/{selector}: no checked raw bytecode")
    if contract in seen:
        seen[contract].add(selector)
    checked += 1

missing = {
    contract: sorted({"creation", "runtime"} - selectors)
    for contract, selectors in seen.items()
    if selectors != {"creation", "runtime"}
}
if missing:
    raise SystemExit(f"generated pressure selector coverage missing: {missing!r}")

print(f"generated_pressure_contracts={len(required_contracts)}")
print(f"generated_pressure_objects={checked}")
PY

REJECTED_SOURCE="$OUTDIR/RejectedUnsafePressure.sol"
"$PYTHON_BIN" - "$REJECTED_SOURCE" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
loads = "\n".join(
    f"        uint256 v{i:02d} = values[{i}];" for i in range(32)
)
total = " + ".join(f"v{i:02d}" for i in range(32))
path.write_text(f'''// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract RejectedUnsafePressure {{
    uint256[32] private values;

    function pressure(address target) external returns (uint256) {{
        assembly {{ mstore(0, 0) }}
{loads}
        (bool ok,) = target.call("");
        require(ok);
        unchecked {{ return {total}; }}
    }}
}}
''')
PY

REJECTED_OUT="$OUTDIR/rejected-unsafe.txt"
if "$SOLC_BIN" --via-ir --optimize --bin "$REJECTED_SOURCE" \
    >"$REJECTED_OUT" 2>&1; then
  printf 'error: memory-unsafe hostile source unexpectedly compiled\n' >&2
  exit 1
fi
if ! grep -Eqi 'stack too deep|YulException|too deep' "$REJECTED_OUT"; then
  printf 'error: memory-unsafe hostile source failed for an unexpected reason\n' >&2
  cat "$REJECTED_OUT" >&2
  exit 1
fi

printf 'conventional_stack_too_deep=confirmed\n'
printf 'optimized_solc_spills=confirmed\n'
printf 'memory_unsafe_pressure_rejection=confirmed\n'
printf 'solc_stack_spill_adversarial=pass\n'
