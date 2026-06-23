#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi
FORGE_BIN="${FORGE:-forge}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-universal-router-smoke.XXXXXX")"
UNISWAP_UNIVERSAL_ROUTER_REPO_URL="${UNISWAP_UNIVERSAL_ROUTER_REPO_URL:-https://github.com/Uniswap/universal-router.git}"
UNISWAP_UNIVERSAL_ROUTER_REF="${UNISWAP_UNIVERSAL_ROUTER_REF:-5a5336a2aa69faea5407ad610feabed6d5a1c4fa}"
UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION="${UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${UNISWAP_UNIVERSAL_ROUTER_DIR:-}" ]]; then
  REPO="$UNISWAP_UNIVERSAL_ROUTER_DIR"
else
  REPO="$OUTDIR/universal-router"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$UNISWAP_UNIVERSAL_ROUTER_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$UNISWAP_UNIVERSAL_ROUTER_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
SOURCE="$REPO/contracts/deploy/UnsupportedProtocol.sol"
BRIDGE_DIR="$OUTDIR/bridge-json"
BRIDGE="$OUTDIR/UnsupportedProtocol.runtime.bridge.json"
LEAN_CHECK="$OUTDIR/UnsupportedProtocol.runtime.lean-json-check.txt"
ARTIFACT="$OUTDIR/UnsupportedProtocol.artifact.json"
PACKAGE_DIR="$OUTDIR/package"
PACKAGE_MANIFEST="$PACKAGE_DIR/manifest.json"
PACKAGE_SUMMARY="$OUTDIR/package.bridge-json-summary.json"
MANIFEST_CHECK="$OUTDIR/manifest.lean-json-check.json"
CALL_COMPARE="$OUTDIR/UnsupportedProtocol.call-compare.txt"
COMMANDS_FIXTURE="$OUTDIR/UniswapUniversalRouterCommandsFallback.sol"
COMMANDS_BRIDGE_DIR="$OUTDIR/commands-bridge-json"
COMMANDS_BRIDGE="$OUTDIR/UniswapUniversalRouterCommandsFallback.runtime.bridge.json"
COMMANDS_LEAN_CHECK="$OUTDIR/UniswapUniversalRouterCommandsFallback.runtime.lean-json-check.txt"
COMMANDS_SUMMARY="$OUTDIR/UniswapUniversalRouterCommandsFallback.bridge-json-summary.json"
COMMANDS_BACKEND_CHECK="$OUTDIR/UniswapUniversalRouterCommandsFallback.lean-backend-check.json"
COMMANDS_COMPARE="$OUTDIR/UniswapUniversalRouterCommandsFallback.call-compare.txt"

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$SOURCE" \
  --solc "$SOLC_BIN" \
  --contract UnsupportedProtocol \
  --format bridge-json \
  --object runtime \
  --bridge-json-dir "$BRIDGE_DIR" \
  --output "$BRIDGE"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" "$BRIDGE"

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$BRIDGE" \
  --input-format bridge-json \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$LEAN_CHECK"

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UnsupportedProtocol \
  --format bytecode-artifact \
  --output "$ARTIFACT"

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$SOURCE" \
  --solc "$SOLC_BIN" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$PACKAGE_DIR" \
  --output "$PACKAGE_MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$PACKAGE_MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$PACKAGE_MANIFEST" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$PACKAGE_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$PACKAGE_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$PACKAGE_MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$MANIFEST_CHECK"

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" "$SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UnsupportedProtocol \
  --calldata 0x12345678 > "$CALL_COMPARE"

cat > "$COMMANDS_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Commands} from "universal-router/contracts/libraries/Commands.sol";

contract UniswapUniversalRouterCommandsFallback {
    fallback() external {
        uint256 allowFlag = uint8(Commands.FLAG_ALLOW_REVERT);
        uint256 typeMask = uint8(Commands.COMMAND_TYPE_MASK);
        uint256 firstMax = Commands.PAY_PORTION_FULL_PRECISION;
        uint256 secondMax = Commands.BALANCE_CHECK_ERC20;
        uint256 thirdMax = Commands.V4_POSITION_MANAGER_CALL;
        uint256 subPlan = Commands.EXECUTE_SUB_PLAN;
        uint256 across = Commands.ACROSS_V4_DEPOSIT_V3;

        assembly ("memory-safe") {
            let command := byte(0, calldataload(0))
            let commandType := and(command, typeMask)
            let allowRevert := iszero(iszero(and(command, allowFlag)))
            let firstBand := iszero(gt(commandType, firstMax))
            let secondBand := and(gt(commandType, firstMax), iszero(gt(commandType, secondMax)))
            let thirdBand := and(gt(commandType, secondMax), iszero(gt(commandType, thirdMax)))
            let subPlanBand := eq(commandType, subPlan)
            let acrossBand := eq(commandType, across)
            let selected := or(or(firstBand, secondBand), or(thirdBand, or(subPlanBand, acrossBand)))
            let base := or(
                or(mul(firstBand, 0x100), mul(secondBand, 0x200)),
                or(
                    or(mul(thirdBand, 0x300), mul(subPlanBand, 0x400)),
                    or(mul(acrossBand, 0x500), mul(iszero(selected), 0x500))
                )
            )
            let bucket := or(base, commandType)
            let result := or(or(shl(255, allowRevert), shl(16, commandType)), bucket)
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$COMMANDS_FIXTURE" \
  --solc "$SOLC_BIN" \
  --contract UniswapUniversalRouterCommandsFallback \
  --remapping "universal-router/=$REPO/" \
  --format bridge-json \
  --object runtime \
  --bridge-json-dir "$COMMANDS_BRIDGE_DIR" \
  --output "$COMMANDS_BRIDGE" \
  --optimized

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" "$COMMANDS_BRIDGE"
"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet \
  "$COMMANDS_BRIDGE_DIR/manifest.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$COMMANDS_BRIDGE" \
  --input-format bridge-json \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$COMMANDS_LEAN_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$COMMANDS_BRIDGE" \
  --input-format bridge-json \
  --format bridge-json-summary \
  --output "$COMMANDS_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$COMMANDS_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$COMMANDS_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UniswapUniversalRouterCommandsFallback \
  --object runtime \
  --format lean-backend-check \
  --output "$COMMANDS_BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$COMMANDS_BACKEND_CHECK"

SOLC_VERSION="$UNISWAP_UNIVERSAL_ROUTER_SOLC_VERSION" \
"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" "$COMMANDS_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapUniversalRouterCommandsFallback \
  --remapping "universal-router/=$REPO/" \
  --optimized \
  --runtime-only \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x21 \
  --calldata 0x40 \
  --calldata 0x80 \
  --calldata 0xff > "$COMMANDS_COMPARE"

BRIDGE_BYTES="$(wc -c < "$BRIDGE" | tr -d ' ')"
LEAN_DECODE="$(sed -n 's/^lean_bridge_json_decode=//p' "$LEAN_CHECK")"
ARTIFACT_RUNTIME_BYTES="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["sizes"]["runtimeBytes"])' \
    "$ARTIFACT"
)"
PACKAGE_ENTRIES="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["entries"])' \
    "$PACKAGE_MANIFEST"
)"
PACKAGE_SKIPPED="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["skippedContracts"])' \
    "$PACKAGE_MANIFEST"
)"
PACKAGE_SUMMARY_OBJECTS="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["objects"])' \
    "$PACKAGE_SUMMARY"
)"
MANIFEST_OBJECTS="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["checkedObjects"])' \
    "$MANIFEST_CHECK"
)"
CALLS="$(
  sed -n 's/^calls=//p' "$CALL_COMPARE"
)"
COMMANDS_CALLS="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["calls"])' \
    "$COMMANDS_SUMMARY"
)"
COMMANDS_LEAN_DECODE="$(
  sed -n 's/^lean_bridge_json_decode=//p' "$COMMANDS_LEAN_CHECK"
)"
COMMANDS_BACKEND_FIRST_NONE="$(
  "$PYTHON_BIN" -c 'import json, sys; print(json.load(open(sys.argv[1]))["firstNoneCounts"])' \
    "$COMMANDS_BACKEND_CHECK"
)"
COMMANDS_COMPARE_CALLS="$(
  sed -n 's/^calls=//p' "$COMMANDS_COMPARE"
)"

printf 'uniswap_universal_router_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'unsupported_runtime_bridge_json_bytes=%s\n' "$BRIDGE_BYTES"
printf 'unsupported_runtime_lean_decode=%s\n' "$LEAN_DECODE"
printf 'unsupported_artifact_runtime_bytes=%s\n' "$ARTIFACT_RUNTIME_BYTES"
printf 'unsupported_package_bridge_objects=%s\n' "$PACKAGE_ENTRIES"
printf 'unsupported_package_skipped_contracts=%s\n' "$PACKAGE_SKIPPED"
printf 'unsupported_package_summary_objects=%s\n' "$PACKAGE_SUMMARY_OBJECTS"
printf 'manifest_lean_decode_objects=%s\n' "$MANIFEST_OBJECTS"
printf 'fallback_compare_calls=%s\n' "$CALLS"
printf 'universal_router_commands_lean_decode=%s\n' "$COMMANDS_LEAN_DECODE"
printf 'universal_router_commands_summary_calls=%s\n' "$COMMANDS_CALLS"
printf 'universal_router_commands_backend_first_none=%s\n' "$COMMANDS_BACKEND_FIRST_NONE"
printf 'universal_router_commands_compare_calls=%s\n' "$COMMANDS_COMPARE_CALLS"
"$PYTHON_BIN" - "$PACKAGE_SUMMARY" "$COMMANDS_BRIDGE" "$COMMANDS_SUMMARY" "$COMMANDS_BACKEND_CHECK" "$MANIFEST_CHECK" <<'PY'
import json
import sys

summary = json.load(open(sys.argv[1]))
commands_bridge = json.load(open(sys.argv[2]))
commands_summary = json.load(open(sys.argv[3]))
commands_backend_check = json.load(open(sys.argv[4]))
manifest_check = json.load(open(sys.argv[5]))
compatibility = summary.get("backendCompatibility", {})
object_builtins = set(compatibility.get("objectBuiltinNames", []))
missing_builtins = sorted({"dataoffset", "datasize"} - object_builtins)
if compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected Universal Router package compatibility: {compatibility!r}"
    )
if missing_builtins:
    raise SystemExit(
        f"Universal Router summary missing object builtins: {missing_builtins!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
if "codecopy" in unsupported:
    raise SystemExit(
        f"Universal Router package summary still marks codecopy unsupported: "
        f"{compatibility!r}"
    )

runtime_summaries = [
    item
    for item in summary.get("objects", [])
    if item.get("contract") == "UnsupportedProtocol"
    and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(
        f"expected one UnsupportedProtocol runtime summary, got {runtime_summaries!r}"
    )
runtime = runtime_summaries[0]
runtime_compatibility = runtime.get("backendCompatibility", {})
if runtime_compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected UnsupportedProtocol runtime compatibility: "
        f"{runtime_compatibility!r}"
    )
primitives = {
    entry.get("name")
    for entry in runtime.get("calls", {}).get("primitive", {}).get("names", [])
    if isinstance(entry, dict)
}
required_primitives = {"callvalue", "mstore", "revert", "shr"}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(
        f"UnsupportedProtocol runtime missing primitives: {missing_primitives!r}"
    )
manifest_frontends = {
    tuple(item.get("frontend", {}).items())
    for item in manifest_check.get("checkedObjects", [])
}
expected_manifest_frontend = tuple(
    {"producer": "solc", "ast": "irAst"}.items()
)
if manifest_frontends != {expected_manifest_frontend}:
    raise SystemExit(
        "Universal Router manifest Lean check report has unexpected frontend "
        f"metadata: {manifest_frontends!r}"
    )

print(f"unsupported_package_backend_compatibility={compatibility['status']}")
print("unsupported_runtime_backend_compatibility=ready")
print("unsupported_runtime_summary_primitives=yes")
print("unsupported_manifest_report_frontend_metadata=yes")

frontend = commands_bridge.get("frontend", {})
if frontend != {"producer": "solc", "ast": "irOptimizedAst"}:
    raise SystemExit(f"unexpected Commands frontend metadata: {frontend!r}")
summary_frontend = commands_summary.get("frontend", {})
if summary_frontend != frontend:
    raise SystemExit(
        f"unexpected Commands summary frontend metadata: {summary_frontend!r}"
    )
commands_calls = commands_summary.get("calls", {}).get("primitive", {}).get("names", [])
commands_primitives = {
    item.get("name")
    for item in commands_calls
    if isinstance(item, dict)
}
required_commands_primitives = {
    "and",
    "byte",
    "calldataload",
    "eq",
    "gt",
    "iszero",
    "mul",
    "or",
    "shl",
}
missing_commands_primitives = sorted(
    required_commands_primitives - commands_primitives
)
if missing_commands_primitives:
    raise SystemExit(
        "Universal Router Commands summary missing primitives: "
        f"{missing_commands_primitives!r}"
    )
first_none_counts = commands_backend_check.get("firstNoneCounts", {})
if first_none_counts:
    raise SystemExit(
        "Universal Router Commands backend-check unexpectedly blocked: "
        f"{first_none_counts!r}"
    )
checked_objects = commands_backend_check.get("checkedObjects", [])
if len(checked_objects) != 1:
    raise SystemExit(
        f"expected one Commands backend-check object: {checked_objects!r}"
    )
backend_frontend = checked_objects[0].get("frontend", {})
if backend_frontend != frontend:
    raise SystemExit(
        f"unexpected Commands backend-check frontend metadata: {backend_frontend!r}"
    )
if checked_objects[0].get("status") != "pass":
    raise SystemExit(
        f"Commands backend-check did not pass: {checked_objects[0]!r}"
    )
if checked_objects[0].get("firstNone") != "none":
    raise SystemExit(
        f"Commands backend-check still has firstNone: {checked_objects[0]!r}"
    )
print("universal_router_commands_frontend_metadata=yes")
print("universal_router_commands_summary_frontend_metadata=yes")
print("universal_router_commands_backend_frontend_metadata=yes")
print("universal_router_commands_summary_primitives=yes")
print("universal_router_commands_backend_check=pass")
PY
