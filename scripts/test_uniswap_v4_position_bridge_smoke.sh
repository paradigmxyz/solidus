#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
BUNDLED_PYTHON="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1 && \
    [[ -x "$BUNDLED_PYTHON" ]]; then
  PYTHON_BIN="$BUNDLED_PYTHON"
fi
SOLC_BIN="${SOLC:-solc}"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi
FORGE_BIN="${FORGE:-forge}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-uniswap-v4-position-smoke.XXXXXX")"
UNISWAP_V4_REPO_URL="${UNISWAP_V4_REPO_URL:-https://github.com/Uniswap/v4-core.git}"
UNISWAP_V4_REF="${UNISWAP_V4_REF:-46c6834698c48bc4a463a86d8420f4eb1d7f3b75}"
UNISWAP_V4_SOLC_VERSION="${UNISWAP_V4_SOLC_VERSION:-0.8.26}"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

ensure_solc_version() {
  local version="$1"
  local output
  output="$(SOLC_VERSION="$version" "$SOLC_BIN" --version 2>/dev/null || true)"
  if [[ "$output" == *"Version: $version"* ]]; then
    return
  fi
  if [[ "$INSTALL_SOLC" == "1" ]] && command -v solc-select >/dev/null 2>&1; then
    solc-select install "$version"
  fi
  output="$(SOLC_VERSION="$version" "$SOLC_BIN" --version 2>&1 || true)"
  if [[ "$output" != *"Version: $version"* ]]; then
    printf 'error: %s cannot provide solc %s\n%s\n' "$SOLC_BIN" "$version" "$output" >&2
    return 1
  fi
}

if [[ -n "${UNISWAP_V4_DIR:-}" ]]; then
  REPO="$UNISWAP_V4_DIR"
else
  REPO="$OUTDIR/v4-core"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$UNISWAP_V4_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$UNISWAP_V4_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$UNISWAP_V4_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
POSITION_FIXTURE="$OUTDIR/UniswapV4PositionFallback.sol"
POSITION_BRIDGE_DIR="$OUTDIR/position-bridge-json"
POSITION_MANIFEST="$POSITION_BRIDGE_DIR/manifest.json"
POSITION_CHECK="$OUTDIR/UniswapV4PositionFallback.lean-json-check.json"
POSITION_SUMMARY="$OUTDIR/UniswapV4PositionFallback.bridge-json-summary.json"
POSITION_BACKEND_CHECK="$OUTDIR/UniswapV4PositionFallback.lean-backend-check.json"
POSITION_COMPARE="$OUTDIR/UniswapV4PositionFallback.call-compare.txt"

cat > "$POSITION_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Position} from "v4-core/src/libraries/Position.sol";

contract UniswapV4PositionFallback {
    using Position for mapping(bytes32 => Position.State);
    using Position for Position.State;

    uint256 private constant Q128 = 1 << 128;

    mapping(bytes32 => Position.State) internal positions;

    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }

        address owner = address(0x000000000000000000000000000000000000bEEF);
        bytes32 salt = bytes32(uint256(mode) + 0x42);
        int24 tickLower = -120;
        int24 tickUpper = 120;
        bytes32 result;

        if (mode == 0) {
            result = Position.calculatePositionKey(owner, tickLower, tickUpper, salt);
        } else {
            Position.State storage position =
                positions.get(owner, tickLower, tickUpper, salt);
            uint256 feesOwed0;
            uint256 feesOwed1;

            if (mode == 1) {
                (feesOwed0, feesOwed1) =
                    position.update(1000, Q128, 2 * Q128);
            } else if (mode == 2) {
                position.update(1000, Q128, 2 * Q128);
                (feesOwed0, feesOwed1) =
                    position.update(0, 3 * Q128, 5 * Q128);
            } else if (mode == 3) {
                position.update(
                    1200,
                    type(uint256).max - Q128 + 1,
                    type(uint256).max - 2 * Q128 + 1
                );
                (feesOwed0, feesOwed1) = position.update(-400, 0, 0);
            } else if (mode == 4) {
                // Fresh salt for this mode hits Position.CannotUpdateEmptyPosition.
                position.update(0, Q128, Q128);
            }

            result = keccak256(
                abi.encode(
                    position.liquidity,
                    position.feeGrowthInside0LastX128,
                    position.feeGrowthInside1LastX128,
                    feesOwed0,
                    feesOwed1
                )
            );
        }

        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$POSITION_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UniswapV4PositionFallback \
  --remapping "v4-core/=$REPO/" \
  --object runtime \
  --format lean-json-check \
  --bridge-json-dir "$POSITION_BRIDGE_DIR" \
  --optimized \
  --output "$POSITION_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$POSITION_MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$POSITION_MANIFEST" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --contract UniswapV4PositionFallback \
  --object runtime \
  --output "$POSITION_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$POSITION_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$POSITION_MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UniswapV4PositionFallback \
  --object runtime \
  --format lean-backend-check \
  --output "$POSITION_BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$POSITION_BACKEND_CHECK"

RUNTIME_BACKEND_STATUS="$(
  "$PYTHON_BIN" - "$POSITION_BACKEND_CHECK" <<'PY'
import json
import sys

backend_check = json.load(open(sys.argv[1]))
runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "UniswapV4PositionFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(f"expected one Uniswap position runtime check: {runtime_checks!r}")
print(runtime_checks[0].get("status", "missing"))
PY
)"

if [[ "$RUNTIME_BACKEND_STATUS" == "pass" ]]; then
  SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" \
  "$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
    "$POSITION_FIXTURE" \
    --solc "$SOLC_BIN" \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --forge "$FORGE_BIN" \
    --contract UniswapV4PositionFallback \
    --remapping "v4-core/=$REPO/" \
    --runtime-only \
    --calldata 0x00 \
    --calldata 0x01 \
    --calldata 0x02 \
    --calldata 0x03 \
    --calldata 0x04 \
    --optimized > "$POSITION_COMPARE"
fi

"$PYTHON_BIN" - "$POSITION_MANIFEST" "$POSITION_CHECK" "$POSITION_SUMMARY" \
  "$POSITION_BACKEND_CHECK" "$POSITION_COMPARE" <<'PY'
import json
import sys
from pathlib import Path

manifest = json.load(open(sys.argv[1]))
lean_check = Path(sys.argv[2]).read_text()
summary = json.load(open(sys.argv[3]))
backend_check = json.load(open(sys.argv[4]))
compare_path = Path(sys.argv[5])
compare = {}
if compare_path.exists():
    for line in compare_path.read_text().splitlines():
        if "=" in line:
            key, value = line.strip().split("=", 1)
            compare[key] = value

if manifest.get("counts", {}).get("entries") != 1:
    raise SystemExit(f"expected one position runtime bridge object: {manifest!r}")
if manifest.get("counts", {}).get("skippedContracts", 0) != 0:
    raise SystemExit(f"unexpected skipped position contracts: {manifest!r}")
if "lean_bridge_json_decode=pass" not in lean_check:
    raise SystemExit("Uniswap position Lean JSON decode did not report pass")

entries = [
    item
    for item in manifest.get("entries", [])
    if item.get("contract") == "UniswapV4PositionFallback"
    and item.get("selector") == "runtime"
]
if len(entries) != 1:
    raise SystemExit(f"expected one position runtime manifest entry: {entries!r}")
frontend = entries[0].get("frontend")
if (
    not isinstance(frontend, dict)
    or frontend.get("producer") != "solc"
    or frontend.get("ast") not in {"irAst", "irOptimizedAst"}
):
    raise SystemExit(f"unexpected position frontend metadata: {frontend!r}")
frontend_label = f"{frontend['producer']}:{frontend['ast']}"

if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected position summary schema: {summary.get('schema')!r}")
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(f"unexpected position summary counts: {summary.get('counts')!r}")
runtime_summaries = [
    item
    for item in summary.get("objects", [])
    if item.get("contract") == "UniswapV4PositionFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(f"expected one position runtime summary: {runtime_summaries!r}")
runtime = runtime_summaries[0]
if runtime.get("frontend") != frontend:
    raise SystemExit(f"position summary frontend drift: {runtime!r}")

def collect_names(kind):
    names = set()
    for entry in runtime.get("calls", {}).get(kind, {}).get("names", []):
        if isinstance(entry, dict) and isinstance(entry.get("name"), str):
            names.add(entry["name"])
    return names

primitive_calls = collect_names("primitive")
missing_primitives = sorted(
    {"calldataload", "keccak256", "sload", "sstore", "revert", "return"}
    - primitive_calls
)
if missing_primitives:
    raise SystemExit(
        f"Uniswap position summary missing primitives: {missing_primitives!r}"
    )

user_calls = collect_names("user")
required_user_call_prefixes = [
    "fun_calculatePositionKey",
    "fun_update",
    "fun_mulDiv",
]
missing_user_calls = [
    prefix
    for prefix in required_user_call_prefixes
    if not any(name.startswith(prefix) for name in user_calls)
]
if missing_user_calls:
    raise SystemExit(
        f"Uniswap position summary missing user calls: {missing_user_calls!r}"
    )

compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(f"unexpected position backend compatibility: {compatibility!r}")

runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "UniswapV4PositionFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(f"expected one position runtime backend check: {runtime_checks!r}")
runtime_check = runtime_checks[0]
runtime_check_status = runtime_check.get("status")
runtime_first_none = runtime_check.get("firstNone")
if (runtime_check_status, runtime_first_none) != ("pass", "none"):
    raise SystemExit(f"position runtime backend failed: {runtime_check!r}")
if compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"position runtime compare did not pass: {compare!r}")
if compare.get("calls") != "5":
    raise SystemExit(f"position runtime compare call count mismatch: {compare!r}")
if compare.get("bridge_summary_1_frontends") != frontend_label:
    raise SystemExit(f"position compare frontend drift: {compare!r}")
if (
    compare.get("bridge_summary_1_object_selectors")
    != "UniswapV4PositionFallback:runtime"
):
    raise SystemExit(f"position compare selector mismatch: {compare!r}")
runtime_compare = "yes"
runtime_compare_calls = compare["calls"]

print("uniswap_v4_position_decode_objects=1")
print(f"uniswap_v4_position_summary_objects={summary['counts']['objects']}")
print(f"uniswap_v4_position_summary_calls={runtime['counts']['calls']}")
print(f"uniswap_v4_position_backend_compatibility={compatibility.get('status')}")
print(f"uniswap_v4_position_runtime_backend_check={runtime_check_status}")
print(f"uniswap_v4_position_runtime_backend_first_none={runtime_first_none}")
print("uniswap_v4_position_frontend_metadata=yes")
print("uniswap_v4_position_summary_primitives=yes")
print("uniswap_v4_position_summary_user_calls=yes")
print("uniswap_v4_position_storage_behavior=yes")
print(f"uniswap_v4_position_runtime_compare={runtime_compare}")
print(f"uniswap_v4_position_compare_calls={runtime_compare_calls}")
PY
printf 'uniswap_v4_position_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
