#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
BUNDLED_PYTHON="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1 && \
    [[ -x "$BUNDLED_PYTHON" ]]; then
  PYTHON_BIN="$BUNDLED_PYTHON"
fi
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_817="${SOLC_817:-$HOME/.solc-select/artifacts/solc-0.8.17/solc-0.8.17}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-full-contracts.XXXXXX")"

PERMIT2_URL="${PERMIT2_URL:-https://github.com/Uniswap/permit2.git}"
PERMIT2_REF="${PERMIT2_REF:-cc56ad0f3439c502c246fc5cfcc3db92bb8b7219}"
AAVE_URL="${AAVE_URL:-https://github.com/aave/aave-v3-core.git}"
AAVE_REF="${AAVE_REF:-b74526a7bc67a3a117a1963fc871b3eb8cea8435}"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_817" "$SOLC_826"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

checkout_repo() {
  local destination="$1"
  local url="$2"
  local ref="$3"
  git init -q "$destination"
  git -C "$destination" remote add origin "$url"
  git -C "$destination" fetch --depth 1 origin "$ref"
  git -C "$destination" -c advice.detachedHead=false checkout -q FETCH_HEAD
}

if [[ -n "${PERMIT2_DIR:-}" ]]; then
  PERMIT2_REPO="$PERMIT2_DIR"
else
  PERMIT2_REPO="$OUTDIR/permit2"
  checkout_repo "$PERMIT2_REPO" "$PERMIT2_URL" "$PERMIT2_REF"
  git -C "$PERMIT2_REPO" submodule update --init --depth 1 lib/solmate
fi

if [[ -n "${AAVE_V3_DIR:-}" ]]; then
  AAVE_REPO="$AAVE_V3_DIR"
else
  AAVE_REPO="$OUTDIR/aave-v3-core"
  checkout_repo "$AAVE_REPO" "$AAVE_URL" "$AAVE_REF"
fi

PERMIT2_BRIDGE="$OUTDIR/permit2-runtime.bridge.json"
PERMIT2_BACKEND="$OUTDIR/permit2-runtime.backend.txt"
AAVE_BRIDGE="$OUTDIR/aave-pool-runtime.bridge.json"
AAVE_BACKEND="$OUTDIR/aave-pool-runtime.backend.txt"

(
  cd "$PERMIT2_REPO"
  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" src/Permit2.sol \
    --input-format solidity \
    --source-name src/Permit2.sol \
    --solc "$SOLC_817" \
    --yul-ast-solc "$SOLC_826" \
    --contract Permit2 \
    --object runtime \
    --optimized \
    --remapping solmate/=lib/solmate/ \
    --format bridge-json \
    --output "$PERMIT2_BRIDGE"
)

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
  --quiet "$PERMIT2_BRIDGE"

"$LAKE_BIN" exe evm-compiler-backend stack-diagnostics \
  "$PERMIT2_BRIDGE" > "$PERMIT2_BACKEND"

(
  cd "$AAVE_REPO"
  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    contracts/protocol/pool/Pool.sol \
    --input-format solidity \
    --source-name contracts/protocol/pool/Pool.sol \
    --solc "$SOLC_826" \
    --no-via-ir \
    --contract Pool \
    --object runtime \
    --optimized \
    --format bridge-json \
    --output "$AAVE_BRIDGE"
)

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
  --quiet "$AAVE_BRIDGE"

"$LAKE_BIN" exe evm-compiler-backend stack-diagnostics "$AAVE_BRIDGE" \
  contracts/protocol/libraries/logic/BorrowLogic.sol:BorrowLogic=97433442488726861213578988847752201310395502865 \
  contracts/protocol/libraries/logic/BridgeLogic.sol:BridgeLogic=194866884977453722427157977695504402620791005730 \
  contracts/protocol/libraries/logic/EModeLogic.sol:EModeLogic=292300327466180583640736966543256603931186508595 \
  contracts/protocol/libraries/logic/FlashLoanLogic.sol:FlashLoanLogic=389733769954907444854315955391008805241582011460 \
  contracts/protocol/libraries/logic/LiquidationLogic.sol:LiquidationLogic=487167212443634306067894944238761006551977514325 \
  contracts/protocol/libraries/logic/PoolLogic.sol:PoolLogic=584600654932361167281473933086513207862373017190 \
  contracts/protocol/libraries/logic/SupplyLogic.sol:SupplyLogic=682034097421088028495052921934265409172768520055 \
  > "$AAVE_BACKEND"

"$PYTHON_BIN" - "$PERMIT2_BRIDGE" "$PERMIT2_BACKEND" \
  "$AAVE_BRIDGE" "$AAVE_BACKEND" "$PERMIT2_REF" "$AAVE_REF" <<'PY'
import json
import sys
from pathlib import Path

permit_bridge = json.loads(Path(sys.argv[1]).read_text())
permit_backend = Path(sys.argv[2]).read_text().splitlines()
aave_bridge = json.loads(Path(sys.argv[3]).read_text())
aave_backend = Path(sys.argv[4]).read_text().splitlines()


def require_backend(name, lines, expected_units):
    required = {
        "stack_frontend_object_artifact=true",
        "stack_frontend_code_artifact=true",
    }
    missing = sorted(required - set(lines))
    if missing:
        raise SystemExit(f"{name} verified stack artifact failed: {missing!r}")
    bytecode = [
        line for line in lines
        if line.startswith("stack_frontend_object_bytecode_bytes=")
    ]
    if len(bytecode) != 1 or int(bytecode[0].split("=", 1)[1]) <= 0:
        raise SystemExit(f"{name} verified stack artifact emitted no bytecode")
    units = [line for line in lines if line.startswith("unit\t")]
    if len(units) != expected_units:
        raise SystemExit(
            f"{name} expected {expected_units} checked units, got {len(units)}"
        )
    for line in units:
        fields = dict(
            field.split("=", 1)
            for field in line.split("\t")[2:]
            if "=" in field
        )
        expected = {
            "liveness": "true",
            "schedule": "true",
            "access_failures": "0",
            "lowering": "true",
            "next_use": "true",
        }
        bad = {key: fields.get(key) for key, value in expected.items()
               if fields.get(key) != value}
        if bad:
            raise SystemExit(f"{name} unchecked stack unit: {line!r}; bad={bad!r}")
    return int(bytecode[0].split("=", 1)[1])


permit_bytes = require_backend("Permit2", permit_backend, 39)
aave_bytes = require_backend("Aave Pool", aave_backend, 189)

if permit_bridge.get("frontend") != {"producer": "solc", "ast": "yulAst"}:
    raise SystemExit("Permit2 did not use the exact-text parser boundary")

print("full_contract_backend_smoke=pass")
print(f"permit2_ref={sys.argv[5]}")
print(f"permit2_bytecode_bytes={permit_bytes}")
print(f"aave_ref={sys.argv[6]}")
print(f"aave_bytecode_bytes={aave_bytes}")
print("aave_stack_only=true")
PY
