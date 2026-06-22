#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-openzeppelin-smoke.XXXXXX")"
OPENZEPPELIN_REPO_URL="${OPENZEPPELIN_REPO_URL:-https://github.com/OpenZeppelin/openzeppelin-contracts.git}"
OPENZEPPELIN_REF="${OPENZEPPELIN_REF:-dbb6104ce834628e473d2173bbc9d47f81a9eec3}"
OPENZEPPELIN_SOLC_VERSION="${OPENZEPPELIN_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${OPENZEPPELIN_DIR:-}" ]]; then
  REPO="$OPENZEPPELIN_DIR"
else
  REPO="$OUTDIR/openzeppelin-contracts"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$OPENZEPPELIN_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$OPENZEPPELIN_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$OPENZEPPELIN_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
FIXTURE="$OUTDIR/OzToken.sol"
SAFECAST_FIXTURE="$OUTDIR/OzSafeCastFallback.sol"
STRINGS_FIXTURE="$OUTDIR/OzStringsFallback.sol"
OZ_BRIDGE_DIR="$OUTDIR/bridge-json"
STRINGS_BRIDGE_DIR="$OUTDIR/strings-bridge-json"
OZ_BATCH_CHECK="$OUTDIR/OzToken.lean-json-check.json"
OZ_MANIFEST_CHECK="$OUTDIR/OzToken.manifest.lean-json-check.json"
OZ_SUMMARY="$OUTDIR/OzToken.bridge-json-summary.json"
OZ_BACKEND_CHECK="$OUTDIR/OzToken.lean-backend-check.json"
STRINGS_CHECK="$OUTDIR/OzStringsFallback.lean-json-check.txt"
STRINGS_MANIFEST_CHECK="$OUTDIR/OzStringsFallback.manifest.lean-json-check.json"
STRINGS_SUMMARY="$OUTDIR/OzStringsFallback.bridge-json-summary.json"
STRINGS_BACKEND_CHECK="$OUTDIR/OzStringsFallback.lean-backend-check.json"
SAFECAST_COMPARE="$OUTDIR/OzSafeCastFallback.call-compare.txt"

cat > "$FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/Pausable.sol";

contract OzToken is ERC20, Ownable, Pausable {
    constructor(address owner) ERC20("OzToken", "OZT") Ownable(owner) {
        _mint(owner, 1000 ether);
    }

    function pause() external onlyOwner {
        _pause();
    }

    function unpause() external onlyOwner {
        _unpause();
    }

    function mint(address to, uint256 amount) external onlyOwner whenNotPaused {
        _mint(to, amount);
    }

    function transfer(address to, uint256 value) public override whenNotPaused returns (bool) {
        return super.transfer(to, value);
    }
}
SOL

SOLC_VERSION="$OPENZEPPELIN_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "@openzeppelin/contracts/=$REPO/contracts/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --bridge-json-dir "$OZ_BRIDGE_DIR" \
  --output "$OZ_BATCH_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$OZ_BRIDGE_DIR/manifest.json"
bridge_json_files="$(find "$OZ_BRIDGE_DIR" -name '*.bridge.json' -type f | wc -l | tr -d ' ')"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$OZ_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$OZ_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$OZ_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$OZ_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$OZ_MANIFEST_CHECK"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$OZ_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$OZ_BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$OZ_BACKEND_CHECK"

cat > "$SAFECAST_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {SafeCast} from "@openzeppelin/contracts/utils/math/SafeCast.sol";

contract OzSafeCastFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        uint256 result;
        if (mode == 1) {
            result = SafeCast.toUint64(42);
        } else if (mode == 2) {
            result = SafeCast.toUint64(type(uint64).max + 1);
        } else if (mode == 3) {
            result = uint256(uint128(SafeCast.toInt128(-7)));
        } else {
            result = SafeCast.toUint160(0x1234);
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$OPENZEPPELIN_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SAFECAST_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract OzSafeCastFallback \
  --remapping "@openzeppelin/contracts/=$REPO/contracts/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --optimized > "$SAFECAST_COMPARE"

cat > "$STRINGS_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Strings} from "@openzeppelin/contracts/utils/Strings.sol";

contract OzStringsFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        uint256 result;
        if (mode == 1) {
            result = uint256(keccak256(bytes(Strings.toString(12345678901234567890))));
        } else if (mode == 2) {
            result = uint256(keccak256(bytes(Strings.toHexString(0x1234, 2))));
        } else if (mode == 3) {
            result = uint256(
                keccak256(
                    bytes(
                        Strings.toHexString(
                            address(0x1234567890123456789012345678901234567890)
                        )
                    )
                )
            );
        } else {
            result = Strings.equal(
                "front-half",
                string.concat("front", "-", "half")
            ) ? 1 : 0;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$OPENZEPPELIN_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$STRINGS_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract OzStringsFallback \
  --remapping "@openzeppelin/contracts/=$REPO/contracts/" \
  --format lean-json-check \
  --object runtime \
  --bridge-json-dir "$STRINGS_BRIDGE_DIR" \
  --output "$STRINGS_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$STRINGS_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$STRINGS_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$STRINGS_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$STRINGS_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$STRINGS_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$STRINGS_MANIFEST_CHECK"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$STRINGS_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --linker-symbol "@openzeppelin/contracts/utils/Strings.sol:Strings=0x1111111111111111111111111111111111111111" \
  --linker-symbol "@openzeppelin/contracts/utils/math/Math.sol:Math=0x2222222222222222222222222222222222222222" \
  --format lean-backend-check \
  --output "$STRINGS_BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$STRINGS_BACKEND_CHECK"

printf 'openzeppelin_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'bridge_json_files=%s\n' "$bridge_json_files"
printf 'safecast_fallback_compare_calls=%s\n' "$(sed -n 's/^calls=//p' "$SAFECAST_COMPARE")"
python3 - "$OZ_BATCH_CHECK" "$OZ_MANIFEST_CHECK" "$OZ_BRIDGE_DIR/manifest.json" \
  "$OZ_SUMMARY" "$OZ_BACKEND_CHECK" <<'PY'
import json
import sys

batch = json.load(open(sys.argv[1]))
manifest_replay = json.load(open(sys.argv[2]))
manifest = json.load(open(sys.argv[3]))
bridge_summary = json.load(open(sys.argv[4]))
backend_check = json.load(open(sys.argv[5]))

batch_count = batch["counts"]["checkedObjects"]
replay_count = manifest_replay["counts"]["checkedObjects"]
manifest_count = manifest["counts"]["entries"]
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
if summary_count != manifest_count:
    raise SystemExit(
        f"bridge summary listed {summary_count} objects, expected {manifest_count}"
    )

compatibility = bridge_summary.get("backendCompatibility", {})
object_builtins = set(compatibility.get("objectBuiltinNames", []))
required_builtins = {"dataoffset", "datasize"}
missing_builtins = sorted(required_builtins - object_builtins)
if compatibility.get("status") != "ready":
    raise SystemExit(f"unexpected OzToken backend compatibility: {compatibility!r}")
if missing_builtins:
    raise SystemExit(
        f"OzToken summary missing object builtins: {missing_builtins!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
unexpected_unsupported = sorted({"codecopy", "log3", "sstore"} & unsupported)
if unexpected_unsupported:
    raise SystemExit(
        f"OzToken summary still marks supported primitives unsupported: "
        f"{unexpected_unsupported!r}"
    )
runtime_summaries = [
    item
    for item in bridge_summary.get("objects", [])
    if item.get("contract") == "OzToken" and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(f"expected one OzToken runtime summary, got {runtime_summaries!r}")
runtime_summary = runtime_summaries[0]
runtime_compatibility = runtime_summary.get("backendCompatibility", {})
if runtime_compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected OzToken runtime backend compatibility: {runtime_compatibility!r}"
    )
runtime_unsupported = set(runtime_compatibility.get("unsupportedPrimitiveNames", []))
unexpected_runtime_unsupported = sorted({"log3", "sstore"} & runtime_unsupported)
if unexpected_runtime_unsupported:
    raise SystemExit(
        "OzToken runtime summary still marks supported primitives unsupported: "
        f"{unexpected_runtime_unsupported!r}"
    )
runtime_primitives = {
    entry.get("name")
    for entry in runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
    if isinstance(entry, dict)
}
required_runtime_primitives = {"sload", "sstore", "log3", "mcopy"}
missing_runtime_primitives = sorted(required_runtime_primitives - runtime_primitives)
if missing_runtime_primitives:
    raise SystemExit(
        f"OzToken runtime summary missing primitives: {missing_runtime_primitives!r}"
    )

objects = [
    (item["contract"], item["selector"], item["object"])
    for item in batch["checkedObjects"]
]
if [item[:2] for item in objects] != [
    ("OzToken", "creation"),
    ("OzToken", "runtime"),
]:
    raise SystemExit(f"unexpected decoded objects: {objects!r}")

backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != batch_count
    or backend_counts.get("checkedContracts") != 1
    or backend_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected OzToken backend-check counts: {backend_counts!r}")
backend_status = {}
for item in backend_check.get("checkedObjects", []):
    key = (item.get("contract"), item.get("selector"))
    status = item.get("status")
    first_none = item.get("firstNone")
    backend_status[key] = (status, first_none)
    if status not in {"pass", "fail"}:
        raise SystemExit(f"unexpected OzToken backend status: {item!r}")
    if status == "pass" and first_none != "none":
        raise SystemExit(f"OzToken backend pass mismatch: {item!r}")
    if status == "fail" and first_none in {"", None, "none"}:
        raise SystemExit(f"OzToken backend failure missing firstNone: {item!r}")
if set(backend_status) != {("OzToken", "creation"), ("OzToken", "runtime")}:
    raise SystemExit(f"unexpected OzToken backend labels: {backend_status!r}")
runtime_backend_status, runtime_first_none = backend_status[("OzToken", "runtime")]

print(f"openzeppelin_batch_decode_objects={batch_count}")
print(f"manifest_lean_decode_objects={replay_count}")
print(f"openzeppelin_manifest_summary_objects={summary_count}")
print(f"openzeppelin_manifest_backend_compatibility={compatibility['status']}")
print(f"openzeppelin_backend_check_objects={backend_counts['checkedObjects']}")
print(f"openzeppelin_backend_check_passed={backend_counts['passedObjects']}")
print(f"openzeppelin_backend_check_failed={backend_counts['failedObjects']}")
print(f"openzeppelin_runtime_backend_check={runtime_backend_status}")
print(f"openzeppelin_runtime_backend_first_none={runtime_first_none}")
PY
python3 - "$STRINGS_CHECK" "$STRINGS_MANIFEST_CHECK" "$STRINGS_SUMMARY" \
  "$STRINGS_BACKEND_CHECK" <<'PY'
import json
import sys

summary = {}
for line in open(sys.argv[1]):
    if "=" in line:
        key, value = line.strip().split("=", 1)
        summary[key] = value

manifest_replay = json.load(open(sys.argv[2]))
bridge_summary = json.load(open(sys.argv[3]))
backend_check = json.load(open(sys.argv[4]))
checked = manifest_replay["counts"]["checkedObjects"]
summary_count = bridge_summary["counts"]["objects"]
functions = int(summary["functions"])
data_sections = int(summary["data_sections"])

if summary.get("lean_bridge_json_decode") != "pass":
    raise SystemExit(f"unexpected Strings decode summary: {summary!r}")
if checked != 1:
    raise SystemExit(f"expected 1 Strings manifest object, got {checked}")
if summary_count != checked:
    raise SystemExit(
        f"Strings bridge summary listed {summary_count} objects, expected {checked}"
    )
if functions < 100:
    raise SystemExit(f"expected a rich Strings helper surface, got {functions} functions")
if data_sections < 1:
    raise SystemExit("expected Strings runtime to preserve at least one data section")
compatibility = bridge_summary.get("backendCompatibility", {})
object_builtins = set(compatibility.get("objectBuiltinNames", []))
required_builtins = {"linkersymbol"}
missing_builtins = sorted(required_builtins - object_builtins)
if compatibility.get("status") != "needs-resolution":
    raise SystemExit(f"unexpected Strings backend compatibility: {compatibility!r}")
if missing_builtins:
    raise SystemExit(
        f"Strings summary missing object builtins: {missing_builtins!r}"
    )
primitive_entries = bridge_summary["objects"][0].get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required_primitives = {"calldatacopy", "keccak256", "mstore8"}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(
        f"Strings summary missing primitives: {missing_primitives!r}"
    )

backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != 1
    or backend_counts.get("checkedContracts") != 1
    or backend_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected Strings backend-check counts: {backend_counts!r}")
runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "OzStringsFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(f"expected one Strings runtime backend check: {runtime_checks!r}")
runtime_check = runtime_checks[0]
runtime_backend_status = runtime_check.get("status")
runtime_first_none = runtime_check.get("firstNone")
if runtime_backend_status != "pass" or runtime_first_none != "none":
    raise SystemExit(f"linked Strings backend failed: {runtime_check!r}")

print(f"strings_runtime_lean_decode={summary['lean_bridge_json_decode']}")
print(f"strings_runtime_functions={functions}")
print(f"strings_runtime_data_sections={data_sections}")
print(f"strings_manifest_decode_objects={checked}")
print(f"strings_manifest_summary_objects={summary_count}")
print(f"strings_backend_compatibility={compatibility['status']}")
print(f"strings_runtime_backend_check={runtime_backend_status}")
print(f"strings_runtime_backend_first_none={runtime_first_none}")
print("strings_runtime_summary_primitives=yes")
PY
