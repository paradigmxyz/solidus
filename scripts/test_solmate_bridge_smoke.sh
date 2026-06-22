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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-solmate-smoke.XXXXXX")"
SOLMATE_REPO_URL="${SOLMATE_REPO_URL:-https://github.com/transmissions11/solmate.git}"
SOLMATE_REF="${SOLMATE_REF:-4b47a19038b798b4a33d9749d25e570443520647}"
SOLMATE_SOLC_VERSION="${SOLMATE_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${SOLMATE_DIR:-}" ]]; then
  REPO="$SOLMATE_DIR"
else
  REPO="$OUTDIR/solmate"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$SOLMATE_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$SOLMATE_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$SOLMATE_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
FIXTURE="$OUTDIR/SolmateHarness.sol"
FIXED_POINT_FIXTURE="$OUTDIR/SolmateFixedPointFallback.sol"
SOLMATE_BRIDGE_DIR="$OUTDIR/bridge-json"
SOLMATE_BATCH_CHECK="$OUTDIR/SolmateHarness.lean-json-check.json"
SOLMATE_MANIFEST_CHECK="$OUTDIR/SolmateHarness.manifest.lean-json-check.json"
SOLMATE_SUMMARY="$OUTDIR/SolmateHarness.bridge-json-summary.json"
SOLMATE_BACKEND_CHECK="$OUTDIR/SolmateHarness.lean-backend-check.json"
SOLMATE_PACKAGE_DIR="$OUTDIR/solmate-package"
SOLMATE_PACKAGE_MANIFEST="$SOLMATE_PACKAGE_DIR/manifest.json"
FIXED_POINT_COMPARE="$OUTDIR/SolmateFixedPointFallback.call-compare.txt"

cat > "$FIXTURE" <<'SOL'
// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity >=0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {SafeTransferLib} from "solmate/utils/SafeTransferLib.sol";
import {Owned} from "solmate/auth/Owned.sol";

contract SolmateHarness is ERC20, Owned {
    using SafeTransferLib for ERC20;

    constructor(address owner) ERC20("Harness", "HARN", 18) Owned(owner) {
        _mint(owner, 100 ether);
    }

    receive() external payable {}

    function mint(address to, uint256 amount) external onlyOwner {
        _mint(to, amount);
    }

    function burn(address from, uint256 amount) external onlyOwner {
        _burn(from, amount);
    }

    function rescueToken(ERC20 token, address to, uint256 amount) external onlyOwner {
        token.safeTransfer(to, amount);
    }

    function rescueEth(address payable to, uint256 amount) external onlyOwner {
        SafeTransferLib.safeTransferETH(to, amount);
    }
}
SOL

SOLC_VERSION="$SOLMATE_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "solmate/=$REPO/src/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --bridge-json-dir "$SOLMATE_BRIDGE_DIR" \
  --output "$SOLMATE_BATCH_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLMATE_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOLMATE_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$SOLMATE_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLMATE_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOLMATE_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$SOLMATE_MANIFEST_CHECK"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOLMATE_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --linker-symbol "solmate/utils/SafeTransferLib.sol:SafeTransferLib=0x1111111111111111111111111111111111111111" \
  --format lean-backend-check \
  --output "$SOLMATE_BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLMATE_BACKEND_CHECK"

SOLC_VERSION="$SOLMATE_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "solmate/=$REPO/src/" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$SOLMATE_PACKAGE_DIR" \
  --output "$SOLMATE_PACKAGE_MANIFEST"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SOLMATE_PACKAGE_MANIFEST"

cat > "$FIXED_POINT_FIXTURE" <<'SOL'
// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity >=0.8.0;

import {FixedPointMathLib} from "solmate/utils/FixedPointMathLib.sol";

contract SolmateFixedPointFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        uint256 result;
        if (mode == 1) {
            result = FixedPointMathLib.mulWadDown(2e18, 3e18);
        } else if (mode == 2) {
            result = FixedPointMathLib.mulWadUp(5, 1e18 + 1);
        } else if (mode == 3) {
            result = FixedPointMathLib.sqrt(10_000);
        } else if (mode == 4) {
            result = FixedPointMathLib.mulDivDown(type(uint256).max, 2, 1);
        } else {
            result = FixedPointMathLib.divWadDown(7e18, 2e18);
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$SOLMATE_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$FIXED_POINT_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract SolmateFixedPointFallback \
  --remapping "solmate/=$REPO/src/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --calldata 0x04 \
  --optimized > "$FIXED_POINT_COMPARE"

printf 'solmate_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'fixed_point_fallback_compare_calls=%s\n' "$(
  sed -n 's/^calls=//p' "$FIXED_POINT_COMPARE"
)"
python3 - "$SOLMATE_BATCH_CHECK" \
  "$SOLMATE_MANIFEST_CHECK" \
  "$SOLMATE_BRIDGE_DIR/manifest.json" \
  "$SOLMATE_PACKAGE_MANIFEST" \
  "$SOLMATE_SUMMARY" \
  "$SOLMATE_BACKEND_CHECK" <<'PY'
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
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
object_builtins = set(compatibility.get("objectBuiltinNames", []))
unexpected_unsupported = sorted(unsupported)
missing_builtins = sorted(
    {"dataoffset", "datasize", "linkersymbol", "loadimmutable", "setimmutable"}
    - object_builtins
)
if compatibility.get("status") != "needs-resolution":
    raise SystemExit(f"unexpected Solmate backend compatibility: {compatibility!r}")
if unexpected_unsupported:
    raise SystemExit(
        f"Solmate summary reported unexpected unsupported primitives: "
        f"{unexpected_unsupported!r}"
    )
if missing_builtins:
    raise SystemExit(f"Solmate summary missing object builtins: {missing_builtins!r}")

runtime_summaries = [
    item
    for item in bridge_summary.get("objects", [])
    if item.get("contract") == "SolmateHarness" and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(f"expected one Solmate runtime summary, got {runtime_summaries!r}")
runtime_summary = runtime_summaries[0]
runtime_compatibility = runtime_summary.get("backendCompatibility", {})
if runtime_compatibility.get("status") != "needs-resolution":
    raise SystemExit(
        f"unexpected Solmate runtime backend compatibility: {runtime_compatibility!r}"
    )
runtime_unsupported = set(runtime_compatibility.get("unsupportedPrimitiveNames", []))
if runtime_unsupported:
    raise SystemExit(
        f"Solmate runtime expected no backend blockers: "
        f"{sorted(runtime_unsupported)!r}"
    )
runtime_primitives = {
    entry.get("name")
    for entry in runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
    if isinstance(entry, dict)
}
required_runtime_primitives = {
    "call",
    "staticcall",
    "gas",
    "returndatacopy",
    "returndatasize",
    "mcopy",
}
missing_runtime_primitives = sorted(
    required_runtime_primitives - runtime_primitives
)
if missing_runtime_primitives:
    raise SystemExit(
        f"Solmate runtime summary missing primitives: {missing_runtime_primitives!r}"
    )

objects = [
    (item["contract"], item["selector"], item["object"])
    for item in batch["checkedObjects"]
]
if [item[:2] for item in objects] != [
    ("SolmateHarness", "creation"),
    ("SolmateHarness", "runtime"),
]:
    raise SystemExit(f"unexpected decoded objects: {objects!r}")

backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != batch_count
    or backend_counts.get("checkedContracts") != 1
    or backend_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected Solmate backend-check counts: {backend_counts!r}")
backend_status = {}
for item in backend_check.get("checkedObjects", []):
    key = (item.get("contract"), item.get("selector"))
    status = item.get("status")
    first_none = item.get("firstNone")
    backend_status[key] = (status, first_none)
    if status not in {"pass", "fail"}:
        raise SystemExit(f"unexpected Solmate backend status: {item!r}")
    if status == "pass" and first_none != "none":
        raise SystemExit(f"Solmate backend pass mismatch: {item!r}")
    if status == "fail" and first_none in {"", None, "none"}:
        raise SystemExit(f"Solmate backend failure missing firstNone: {item!r}")
if set(backend_status) != {("SolmateHarness", "creation"), ("SolmateHarness", "runtime")}:
    raise SystemExit(f"unexpected Solmate backend labels: {backend_status!r}")
for key, (status, first_none) in backend_status.items():
    if status != "pass" or first_none != "none":
        raise SystemExit(f"linked Solmate backend failed at {key}: {backend_status!r}")
runtime_backend_status, runtime_first_none = backend_status[("SolmateHarness", "runtime")]

print(f"solmate_batch_decode_objects={batch_count}")
print(f"solmate_manifest_decode_objects={replay_count}")
print(f"solmate_package_bridge_objects={package_count}")
print(f"solmate_package_skipped_contracts={package_skipped}")
print(f"solmate_manifest_summary_objects={summary_count}")
print(f"solmate_manifest_backend_compatibility={compatibility['status']}")
print(f"solmate_backend_check_objects={backend_counts['checkedObjects']}")
print(f"solmate_backend_check_passed={backend_counts['passedObjects']}")
print(f"solmate_backend_check_failed={backend_counts['failedObjects']}")
print(f"solmate_runtime_backend_check={runtime_backend_status}")
print(f"solmate_runtime_backend_first_none={runtime_first_none}")
print("solmate_runtime_summary_primitives=yes")
PY
