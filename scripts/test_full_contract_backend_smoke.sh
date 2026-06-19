#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_817="${SOLC_817:-$HOME/.solc-select/artifacts/solc-0.8.17/solc-0.8.17}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-full-contracts.XXXXXX")"

PERMIT2_URL="${PERMIT2_URL:-https://github.com/Uniswap/permit2.git}"
PERMIT2_REF="${PERMIT2_REF:-cc56ad0f3439c502c246fc5cfcc3db92bb8b7219}"
AAVE_URL="${AAVE_URL:-https://github.com/aave/aave-v3-core.git}"
AAVE_REF="${AAVE_REF:-b74526a7bc67a3a117a1963fc871b3eb8cea8435}"
AAVE_SCRATCH_BASE="${AAVE_SCRATCH_BASE:-0x100000}"
AAVE_SCRATCH_WORDS="${AAVE_SCRATCH_WORDS:-8193}"

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

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$PERMIT2_BRIDGE" \
  --input-format bridge-json \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$PERMIT2_BACKEND"

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
    --scratch-reservation-base "$AAVE_SCRATCH_BASE" \
    --scratch-reservation-words "$AAVE_SCRATCH_WORDS" \
    --output "$AAVE_BRIDGE"
)

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
  --quiet "$AAVE_BRIDGE"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$AAVE_BRIDGE" \
  --input-format bridge-json \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --linker-symbol contracts/protocol/libraries/logic/BorrowLogic.sol:BorrowLogic=0x1111111111111111111111111111111111111111 \
  --linker-symbol contracts/protocol/libraries/logic/BridgeLogic.sol:BridgeLogic=0x2222222222222222222222222222222222222222 \
  --linker-symbol contracts/protocol/libraries/logic/EModeLogic.sol:EModeLogic=0x3333333333333333333333333333333333333333 \
  --linker-symbol contracts/protocol/libraries/logic/FlashLoanLogic.sol:FlashLoanLogic=0x4444444444444444444444444444444444444444 \
  --linker-symbol contracts/protocol/libraries/logic/LiquidationLogic.sol:LiquidationLogic=0x5555555555555555555555555555555555555555 \
  --linker-symbol contracts/protocol/libraries/logic/PoolLogic.sol:PoolLogic=0x6666666666666666666666666666666666666666 \
  --linker-symbol contracts/protocol/libraries/logic/SupplyLogic.sol:SupplyLogic=0x7777777777777777777777777777777777777777 \
  --output "$AAVE_BACKEND"

"$PYTHON_BIN" - "$PERMIT2_BRIDGE" "$PERMIT2_BACKEND" \
  "$AAVE_BRIDGE" "$AAVE_BACKEND" "$PERMIT2_REF" "$AAVE_REF" <<'PY'
import json
import sys
from pathlib import Path

permit_bridge = json.loads(Path(sys.argv[1]).read_text())
permit_backend = Path(sys.argv[2]).read_text().splitlines()
aave_bridge = json.loads(Path(sys.argv[3]).read_text())
aave_backend = Path(sys.argv[4]).read_text().splitlines()


def require_backend(name, lines):
    required = {
        "lean_backend_check=pass",
        "stage\tsolc_validation\tsome",
        "stage\tobject_image\tsome",
        "first_none=none",
    }
    missing = sorted(required - set(lines))
    if missing:
        raise SystemExit(f"{name} checked backend failed: missing {missing!r}")
    bytecode = [line for line in lines if line.startswith("bytecode_bytes=")]
    if len(bytecode) != 1 or int(bytecode[0].split("=", 1)[1]) <= 0:
        raise SystemExit(f"{name} backend emitted no bytecode size")
    return int(bytecode[0].split("=", 1)[1])


permit_bytes = require_backend("Permit2", permit_backend)
aave_bytes = require_backend("Aave Pool", aave_backend)

if permit_bridge.get("frontend") != {"producer": "solc", "ast": "yulAst"}:
    raise SystemExit("Permit2 did not use the exact-text parser boundary")

reservation = (
    aave_bridge.get("selectedObject", {})
    .get("memoryContract", {})
    .get("scratch")
)
if not isinstance(reservation, dict):
    raise SystemExit("Aave Pool is missing its explicit source reservation")

print("full_contract_backend_smoke=pass")
print(f"permit2_ref={sys.argv[5]}")
print(f"permit2_bytecode_bytes={permit_bytes}")
print(f"aave_ref={sys.argv[6]}")
print(f"aave_bytecode_bytes={aave_bytes}")
print(f"aave_scratch_base={reservation['base']}")
print(f"aave_scratch_words={reservation['words']}")
PY
