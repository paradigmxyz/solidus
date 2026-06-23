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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-aave-v3-smoke.XXXXXX")"
AAVE_V3_REPO_URL="${AAVE_V3_REPO_URL:-https://github.com/aave/aave-v3-core.git}"
AAVE_V3_REF="${AAVE_V3_REF:-b74526a7bc67a3a117a1963fc871b3eb8cea8435}"
AAVE_V3_SOLC_VERSION="${AAVE_V3_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${AAVE_V3_DIR:-}" ]]; then
  REPO="$AAVE_V3_DIR"
else
  REPO="$OUTDIR/aave-v3-core"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$AAVE_V3_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$AAVE_V3_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$AAVE_V3_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
MATH_FIXTURE="$OUTDIR/AaveV3MathFallback.sol"
MATH_BRIDGE_DIR="$OUTDIR/aave-v3-math-bridge-json"
MATH_CHECK="$OUTDIR/AaveV3MathFallback.lean-json-check.json"
MATH_SUMMARY="$OUTDIR/AaveV3MathFallback.bridge-json-summary.json"
MATH_BACKEND_CHECK="$OUTDIR/AaveV3MathFallback.lean-backend-check.json"
INTEREST_FIXTURE="$OUTDIR/AaveV3InterestFallback.sol"
INTEREST_BRIDGE_DIR="$OUTDIR/aave-v3-interest-bridge-json"
INTEREST_CHECK="$OUTDIR/AaveV3InterestFallback.lean-json-check.json"
INTEREST_SUMMARY="$OUTDIR/AaveV3InterestFallback.bridge-json-summary.json"
INTEREST_BACKEND_CHECK="$OUTDIR/AaveV3InterestFallback.lean-backend-check.json"

cat > "$MATH_FIXTURE" <<'SOL'
// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import {WadRayMath} from "aave-v3-core/protocol/libraries/math/WadRayMath.sol";
import {PercentageMath} from "aave-v3-core/protocol/libraries/math/PercentageMath.sol";

contract AaveV3MathFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        uint256 result;
        if (mode == 1) {
            result = WadRayMath.wadMul(2e18, 3e18);
        } else if (mode == 2) {
            result = WadRayMath.wadDiv(5e18, 2e18);
        } else if (mode == 3) {
            result = WadRayMath.rayMul(2e27, 3e27);
        } else if (mode == 4) {
            result = WadRayMath.rayDiv(5e27, 2e27);
        } else if (mode == 5) {
            result = WadRayMath.rayToWad(1234567890123456789500000000);
        } else if (mode == 6) {
            result = WadRayMath.wadToRay(7e18);
        } else if (mode == 7) {
            result = PercentageMath.percentMul(123456789, 1234);
        } else if (mode == 8) {
            result = PercentageMath.percentDiv(123456789, 1234);
        } else if (mode == 9) {
            WadRayMath.wadDiv(1, 0);
        } else if (mode == 10) {
            PercentageMath.percentDiv(1, 0);
        } else {
            result = PercentageMath.percentMul(0, type(uint256).max);
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$AAVE_V3_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$MATH_FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "aave-v3-core/=$REPO/contracts/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract AaveV3MathFallback \
  --object runtime \
  --format lean-json-check \
  --bridge-json-dir "$MATH_BRIDGE_DIR" \
  --optimized \
  --output "$MATH_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MATH_BRIDGE_DIR/manifest.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$MATH_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$MATH_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MATH_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$MATH_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract AaveV3MathFallback \
  --object runtime \
  --format lean-backend-check \
  --output "$MATH_BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MATH_BACKEND_CHECK"

cat > "$INTEREST_FIXTURE" <<'SOL'
// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import {MathUtils} from "aave-v3-core/protocol/libraries/math/MathUtils.sol";

contract AaveV3InterestFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        uint256 result;
        if (mode == 1) {
            result = MathUtils.calculateCompoundedInterest(5e25, uint40(1), 365 days + 1);
        } else {
            result = MathUtils.calculateCompoundedInterest(5e25, uint40(1));
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$AAVE_V3_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$INTEREST_FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "aave-v3-core/=$REPO/contracts/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract AaveV3InterestFallback \
  --object runtime \
  --format lean-json-check \
  --bridge-json-dir "$INTEREST_BRIDGE_DIR" \
  --optimized \
  --output "$INTEREST_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$INTEREST_BRIDGE_DIR/manifest.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$INTEREST_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$INTEREST_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$INTEREST_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$INTEREST_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract AaveV3InterestFallback \
  --object runtime \
  --format lean-backend-check \
  --output "$INTEREST_BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$INTEREST_BACKEND_CHECK"

"$PYTHON_BIN" - "$MATH_CHECK" "$MATH_SUMMARY" "$MATH_BACKEND_CHECK" \
  "$INTEREST_CHECK" "$INTEREST_SUMMARY" "$INTEREST_BACKEND_CHECK" <<'PY'
import json
import sys
from pathlib import Path

math_check = Path(sys.argv[1]).read_text()
math_summary = json.load(open(sys.argv[2]))
math_backend_check = json.load(open(sys.argv[3]))
interest_check = Path(sys.argv[4]).read_text()
interest_summary = json.load(open(sys.argv[5]))
interest_backend_check = json.load(open(sys.argv[6]))

def collect_names(summary, kind):
    names = set()
    for item in summary.get("objects", []):
        for entry in item.get("calls", {}).get(kind, {}).get("names", []):
            if isinstance(entry, dict) and isinstance(entry.get("name"), str):
                names.add(entry["name"])
    return names

def runtime_backend_status(report, contract):
    counts = report.get("counts", {})
    if (
        counts.get("checkedObjects") != 1
        or counts.get("checkedContracts") != 1
        or counts.get("skippedContracts") != 0
    ):
        raise SystemExit(
            f"unexpected {contract} backend-check counts: {counts!r}"
        )
    checks = [
        item
        for item in report.get("checkedObjects", [])
        if item.get("contract") == contract and item.get("selector") == "runtime"
    ]
    if len(checks) != 1:
        raise SystemExit(f"expected one {contract} runtime backend check: {checks!r}")
    check = checks[0]
    status = check.get("status")
    first_none = check.get("firstNone")
    object_image = check.get("stages", {}).get("object_image")
    if (
        status != "pass"
        or first_none != "none"
        or object_image != "some"
    ):
        raise SystemExit(
            f"{contract} runtime did not compile through verified stack allocation: "
            f"{check!r}"
        )
    return status, first_none

math_summary_count = math_summary["counts"]["objects"]
if "lean_bridge_json_decode=pass" not in math_check:
    raise SystemExit("Aave math Lean JSON decode did not report pass")
if math_summary_count != 1:
    raise SystemExit(f"expected 1 Aave math summary object, got {math_summary_count}")

math_primitives = collect_names(math_summary, "primitive")
math_user_calls = collect_names(math_summary, "user")
missing_math_primitives = sorted(
    {"calldataload", "callvalue", "return", "revert"} - math_primitives
)
if missing_math_primitives:
    raise SystemExit(
        f"Aave math summary missing primitives: {missing_math_primitives!r}"
    )
missing_math_user_calls = sorted({"fun_percentDiv", "fun_rayToWad"} - math_user_calls)
if missing_math_user_calls:
    raise SystemExit(
        f"Aave math summary missing user calls: {missing_math_user_calls!r}"
    )

math_compatibility = math_summary.get("backendCompatibility", {})
if math_compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(f"unexpected Aave math compatibility: {math_compatibility!r}")
math_backend_status, math_first_none = runtime_backend_status(
    math_backend_check,
    "AaveV3MathFallback",
)

interest_summary_count = interest_summary["counts"]["objects"]
if "lean_bridge_json_decode=pass" not in interest_check:
    raise SystemExit("Aave interest Lean JSON decode did not report pass")
if interest_summary_count != 1:
    raise SystemExit(
        f"expected 1 Aave interest summary object, got {interest_summary_count}"
    )

interest_primitives = collect_names(interest_summary, "primitive")
interest_user_calls = collect_names(interest_summary, "user")
missing_primitives = sorted(
    {"calldataload", "timestamp", "return"} - interest_primitives
)
if missing_primitives:
    raise SystemExit(f"Aave interest summary missing primitives: {missing_primitives!r}")
if "fun_calculateCompoundedInterest" not in interest_user_calls:
    raise SystemExit("Aave interest summary missing calculateCompoundedInterest call")

interest_compatibility = interest_summary.get("backendCompatibility", {})
if interest_compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(f"unexpected Aave interest compatibility: {interest_compatibility!r}")
interest_backend_status, interest_first_none = runtime_backend_status(
    interest_backend_check,
    "AaveV3InterestFallback",
)

print("aave_v3_math_decode_objects=1")
print(f"aave_v3_math_summary_objects={math_summary_count}")
print(f"aave_v3_math_backend_compatibility={math_compatibility.get('status')}")
print(f"aave_v3_math_runtime_backend_check={math_backend_status}")
print(f"aave_v3_math_runtime_backend_first_none={math_first_none}")
print("aave_v3_math_summary_primitives=yes")
print("aave_v3_interest_decode_objects=1")
print(f"aave_v3_interest_summary_objects={interest_summary_count}")
print(f"aave_v3_interest_backend_compatibility={interest_compatibility.get('status')}")
print(f"aave_v3_interest_runtime_backend_check={interest_backend_status}")
print(f"aave_v3_interest_runtime_backend_first_none={interest_first_none}")
print("aave_v3_interest_summary_primitives=yes")
PY

printf 'aave_v3_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
