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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-solady-smoke.XXXXXX")"
SOLADY_REPO_URL="${SOLADY_REPO_URL:-https://github.com/Vectorized/solady.git}"
SOLADY_REF="${SOLADY_REF:-5dc5fc87374e6e9de15e8139c09d80fde5a22303}"
SOLADY_SOLC_VERSION="${SOLADY_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${SOLADY_DIR:-}" ]]; then
  REPO="$SOLADY_DIR"
else
  REPO="$OUTDIR/solady"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$SOLADY_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$SOLADY_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$SOLADY_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
FIXTURE="$OUTDIR/SoladyLibBitFallback.sol"
SOLADY_BRIDGE_DIR="$OUTDIR/bridge-json"
SOLADY_BATCH_CHECK="$OUTDIR/SoladyLibBitFallback.lean-json-check.json"
SOLADY_MANIFEST_CHECK="$OUTDIR/SoladyLibBitFallback.manifest.lean-json-check.json"
SOLADY_SUMMARY="$OUTDIR/SoladyLibBitFallback.bridge-json-summary.json"
SOLADY_BACKEND_CHECK="$OUTDIR/SoladyLibBitFallback.lean-backend-check.json"
SOLADY_PACKAGE_DIR="$OUTDIR/solady-package"
SOLADY_PACKAGE_MANIFEST="$SOLADY_PACKAGE_DIR/manifest.json"
LIBBIT_COMPARE="$OUTDIR/SoladyLibBitFallback.call-compare.txt"

cat > "$FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

import {LibBit} from "solady/utils/LibBit.sol";

contract SoladyLibBitFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        uint256 result;
        if (mode == 1) {
            result = LibBit.fls(0x0100);
        } else if (mode == 2) {
            result = LibBit.clz(0x0100);
        } else if (mode == 3) {
            result = LibBit.ffs(0x0100);
        } else if (mode == 4) {
            result = LibBit.popCount(type(uint256).max);
        } else if (mode == 5) {
            result = LibBit.countZeroBytes(
                0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
            );
        } else if (mode == 6) {
            result = LibBit.isPo2(1024) ? 1 : 0;
        } else {
            result = LibBit.reverseBytes(
                0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
            );
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$SOLADY_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "solady/=$REPO/src/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --bridge-json-dir "$SOLADY_BRIDGE_DIR" \
  --output "$SOLADY_BATCH_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLADY_BRIDGE_DIR/manifest.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOLADY_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$SOLADY_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLADY_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOLADY_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$SOLADY_MANIFEST_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOLADY_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --linker-symbol "solady/utils/LibBit.sol:LibBit=0x1111111111111111111111111111111111111111" \
  --format lean-backend-check \
  --output "$SOLADY_BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLADY_BACKEND_CHECK"

SOLC_VERSION="$SOLADY_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "solady/=$REPO/src/" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$SOLADY_PACKAGE_DIR" \
  --output "$SOLADY_PACKAGE_MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLADY_PACKAGE_MANIFEST"

SOLC_VERSION="$SOLADY_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract SoladyLibBitFallback \
  --remapping "solady/=$REPO/src/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --calldata 0x04 \
  --calldata 0x05 \
  --calldata 0x06 \
  --optimized > "$LIBBIT_COMPARE"

printf 'solady_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'libbit_fallback_compare_calls=%s\n' "$(
  sed -n 's/^calls=//p' "$LIBBIT_COMPARE"
)"
"$PYTHON_BIN" - "$SOLADY_BATCH_CHECK" \
  "$SOLADY_MANIFEST_CHECK" \
  "$SOLADY_BRIDGE_DIR/manifest.json" \
  "$SOLADY_PACKAGE_MANIFEST" \
  "$SOLADY_SUMMARY" \
  "$SOLADY_BACKEND_CHECK" <<'PY'
import json
import sys

batch = json.load(open(sys.argv[1]))
manifest_replay = json.load(open(sys.argv[2]))
manifest = json.load(open(sys.argv[3]))
package_manifest = json.load(open(sys.argv[4]))
bridge_summary = json.load(open(sys.argv[5]))
backend_check = json.load(open(sys.argv[6]))

batch_count = batch["counts"]["checkedObjects"]
replay_count = manifest_replay["counts"]["checkedObjects"]
manifest_count = manifest["counts"]["entries"]
package_count = package_manifest["counts"]["entries"]
package_skipped = package_manifest["counts"]["skippedContracts"]
summary_count = bridge_summary["counts"]["objects"]

if batch_count != 2:
    raise SystemExit(f"expected 2 batch decoded objects, got {batch_count}")
if replay_count != batch_count:
    raise SystemExit(
        f"manifest replay decoded {replay_count} objects, expected {batch_count}"
    )
if manifest_count != batch_count:
    raise SystemExit(
        f"manifest listed {manifest_count} bridge files, expected {batch_count}"
    )
if package_count != batch_count:
    raise SystemExit(
        f"Lean-free package listed {package_count} bridge files, expected "
        f"{batch_count}"
    )
if package_skipped != 0:
    raise SystemExit(
        f"Lean-free package skipped {package_skipped} contracts, expected 0"
    )
if summary_count != manifest_count:
    raise SystemExit(
        f"bridge summary listed {summary_count} objects, expected {manifest_count}"
    )

compatibility = bridge_summary.get("backendCompatibility", {})
object_builtins = set(compatibility.get("objectBuiltinNames", []))
missing_builtins = sorted({"dataoffset", "datasize", "linkersymbol"} - object_builtins)
if compatibility.get("status") != "needs-resolution":
    raise SystemExit(f"unexpected Solady backend compatibility: {compatibility!r}")
if missing_builtins:
    raise SystemExit(f"Solady summary missing object builtins: {missing_builtins!r}")
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
if "codecopy" in unsupported:
    raise SystemExit(
        f"Solady package summary still marks codecopy unsupported: {compatibility!r}"
    )

runtime_summaries = [
    item
    for item in bridge_summary.get("objects", [])
    if item.get("contract") == "SoladyLibBitFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(f"expected one Solady runtime summary, got {runtime_summaries!r}")
runtime_summary = runtime_summaries[0]
runtime_compatibility = runtime_summary.get("backendCompatibility", {})
if runtime_compatibility.get("status") != "needs-resolution":
    raise SystemExit(
        f"unexpected Solady runtime backend compatibility: {runtime_compatibility!r}"
    )
runtime_builtins = set(runtime_compatibility.get("objectBuiltinNames", []))
if "linkersymbol" not in runtime_builtins:
    raise SystemExit(
        f"Solady runtime summary missing linker symbol need: {runtime_compatibility!r}"
    )
runtime_primitives = {
    entry.get("name")
    for entry in runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
    if isinstance(entry, dict)
}
required_runtime_primitives = {"byte", "shl", "shr", "xor"}
missing_runtime_primitives = sorted(
    required_runtime_primitives - runtime_primitives
)
if missing_runtime_primitives:
    raise SystemExit(
        f"Solady runtime summary missing primitives: {missing_runtime_primitives!r}"
    )

objects = [
    (item["contract"], item["selector"], item["object"])
    for item in batch["checkedObjects"]
]
if [item[:2] for item in objects] != [
    ("SoladyLibBitFallback", "creation"),
    ("SoladyLibBitFallback", "runtime"),
]:
    raise SystemExit(f"unexpected decoded objects: {objects!r}")

backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != batch_count
    or backend_counts.get("checkedContracts") != 1
    or backend_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected Solady backend-check counts: {backend_counts!r}")
backend_status = {}
for item in backend_check.get("checkedObjects", []):
    key = (item.get("contract"), item.get("selector"))
    status = item.get("status")
    first_none = item.get("firstNone")
    backend_status[key] = (status, first_none)
    if status not in {"pass", "fail"}:
        raise SystemExit(f"unexpected Solady backend status: {item!r}")
    if status == "pass" and first_none != "none":
        raise SystemExit(f"Solady backend pass mismatch: {item!r}")
    if status == "fail" and first_none in {"", None, "none"}:
        raise SystemExit(f"Solady backend failure missing firstNone: {item!r}")
if set(backend_status) != {
    ("SoladyLibBitFallback", "creation"),
    ("SoladyLibBitFallback", "runtime"),
}:
    raise SystemExit(f"unexpected Solady backend labels: {backend_status!r}")
for key, (status, first_none) in backend_status.items():
    if status != "pass" or first_none != "none":
        raise SystemExit(f"linked Solady backend failed at {key}: {backend_status!r}")
runtime_backend_status, runtime_first_none = backend_status[
    ("SoladyLibBitFallback", "runtime")
]

print(f"solady_batch_decode_objects={batch_count}")
print(f"solady_manifest_decode_objects={replay_count}")
print(f"solady_package_bridge_objects={package_count}")
print(f"solady_package_skipped_contracts={package_skipped}")
print(f"solady_manifest_summary_objects={summary_count}")
print(f"solady_manifest_backend_compatibility={compatibility['status']}")
print(f"solady_backend_check_objects={backend_counts['checkedObjects']}")
print(f"solady_backend_check_passed={backend_counts['passedObjects']}")
print(f"solady_backend_check_failed={backend_counts['failedObjects']}")
print(f"solady_runtime_backend_check={runtime_backend_status}")
print(f"solady_runtime_backend_first_none={runtime_first_none}")
print("solady_runtime_summary_primitives=yes")
PY
