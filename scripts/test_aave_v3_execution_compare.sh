#!/usr/bin/env bash
set -euo pipefail

# Differential execution test for the Aave v3 math corpus.
#
# Each fixture below wraps real aave-v3-core libraries (pinned to the same
# ref as scripts/test_aave_v3_bridge_smoke.sh) in a small contract exposing
# external functions that return uint256 values. compare_contract_call_bytecode.py
# compiles every fixture twice (full solc, and solc IR -> Lean backend),
# deploys both bytecodes in one Foundry VM, replays each --calldata against
# both instances, and requires identical success flags, keccak(returndata),
# and logs. Fixtures are pure/view math wrappers, so no output can embed a
# contract address, and MathUtils' block.timestamp-dependent helpers are safe
# because both instances execute in the same block.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"

AAVE_V3_SOLC_VERSION="${AAVE_V3_SOLC_VERSION:-0.8.26}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-$AAVE_V3_SOLC_VERSION/solc-$AAVE_V3_SOLC_VERSION}"
YUL_AST_SOLC_BIN="${YUL_AST_SOLC:-$SOLC_BIN}"
AAVE_V3_EVM_VERSION="${AAVE_V3_EVM_VERSION:-cancun}"
AAVE_V3_FORGE_EVM_VERSION="${AAVE_V3_FORGE_EVM_VERSION:-cancun}"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

# Same pinned corpus as scripts/test_aave_v3_bridge_smoke.sh.
AAVE_V3_REPO_URL="${AAVE_V3_REPO_URL:-https://github.com/aave/aave-v3-core.git}"
AAVE_V3_REF="${AAVE_V3_REF:-b74526a7bc67a3a117a1963fc871b3eb8cea8435}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-aave-v3-exec.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

if [[ ! -x "$SOLC_BIN" ]]; then
  if [[ "$INSTALL_SOLC" != "1" ]] || ! command -v solc-select >/dev/null 2>&1; then
    printf 'error: pinned solc %s is unavailable at %s\n' \
      "$AAVE_V3_SOLC_VERSION" "$SOLC_BIN" >&2
    exit 1
  fi
  solc-select install "$AAVE_V3_SOLC_VERSION"
fi
if [[ ! -x "$SOLC_BIN" ]]; then
  printf 'error: pinned solc %s is still unavailable at %s\n' \
    "$AAVE_V3_SOLC_VERSION" "$SOLC_BIN" >&2
  exit 1
fi

if [[ -n "${AAVE_V3_DIR:-}" ]]; then
  REPO="$AAVE_V3_DIR"
else
  REPO="$OUTDIR/aave-v3-core"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$AAVE_V3_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$AAVE_V3_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
REMAP="aave-v3-core/=$REPO/contracts/"
MAX_UINT="$("$CAST_BIN" max-uint)"

# --- Fixture 1: WadRayMath -------------------------------------------------

WADRAY_FIXTURE="$OUTDIR/AaveV3WadRayFixture.sol"
cat > "$WADRAY_FIXTURE" <<'SOL'
// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import {WadRayMath} from "aave-v3-core/protocol/libraries/math/WadRayMath.sol";

contract AaveV3WadRayFixture {
    function wadMulOf(uint256 a, uint256 b) external pure returns (uint256) {
        return WadRayMath.wadMul(a, b);
    }

    function wadDivOf(uint256 a, uint256 b) external pure returns (uint256) {
        return WadRayMath.wadDiv(a, b);
    }

    function rayMulOf(uint256 a, uint256 b) external pure returns (uint256) {
        return WadRayMath.rayMul(a, b);
    }

    function rayDivOf(uint256 a, uint256 b) external pure returns (uint256) {
        return WadRayMath.rayDiv(a, b);
    }

    function rayToWadOf(uint256 a) external pure returns (uint256) {
        return WadRayMath.rayToWad(a);
    }

    function wadToRayOf(uint256 a) external pure returns (uint256) {
        return WadRayMath.wadToRay(a);
    }
}
SOL

# --- Fixture 2: PercentageMath ---------------------------------------------

PERCENTAGE_FIXTURE="$OUTDIR/AaveV3PercentageFixture.sol"
cat > "$PERCENTAGE_FIXTURE" <<'SOL'
// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import {PercentageMath} from "aave-v3-core/protocol/libraries/math/PercentageMath.sol";

contract AaveV3PercentageFixture {
    function percentMulOf(uint256 value, uint256 percentage)
        external
        pure
        returns (uint256)
    {
        return PercentageMath.percentMul(value, percentage);
    }

    function percentDivOf(uint256 value, uint256 percentage)
        external
        pure
        returns (uint256)
    {
        return PercentageMath.percentDiv(value, percentage);
    }
}
SOL

# --- Fixture 3: MathUtils ---------------------------------------------------

MATHUTILS_FIXTURE="$OUTDIR/AaveV3MathUtilsFixture.sol"
cat > "$MATHUTILS_FIXTURE" <<'SOL'
// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import {MathUtils} from "aave-v3-core/protocol/libraries/math/MathUtils.sol";

contract AaveV3MathUtilsFixture {
    function compoundedInterest(
        uint256 rate,
        uint40 lastUpdateTimestamp,
        uint256 currentTimestamp
    ) external pure returns (uint256) {
        return
            MathUtils.calculateCompoundedInterest(
                rate,
                lastUpdateTimestamp,
                currentTimestamp
            );
    }

    function linearInterest(uint256 rate, uint40 lastUpdateTimestamp)
        external
        view
        returns (uint256)
    {
        return MathUtils.calculateLinearInterest(rate, lastUpdateTimestamp);
    }
}
SOL

# --- Differential execution -------------------------------------------------

run_compare() {
  local fixture="$1"
  local contract="$2"
  local report="$3"
  shift 3
  "$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
    "$fixture" \
    --solc "$SOLC_BIN" \
    --yul-ast-solc "$YUL_AST_SOLC_BIN" \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --forge "$FORGE_BIN" \
    --forge-evm-version "$AAVE_V3_FORGE_EVM_VERSION" \
    --remapping "$REMAP" \
    --contract "$contract" \
    --optimized \
    --optimizer-runs 200 \
    --evm-version "$AAVE_V3_EVM_VERSION" \
    "$@" > "$report"
  grep -qx 'contract_call_compare=pass' "$report"
  sed -n 's/^\(contract\|calls\|full_runtime_bytes\|lean_runtime_bytes\)=/\0/p' "$report" \
    | sed "s|^|$contract: |"
}

WADRAY_COMPARE="$OUTDIR/AaveV3WadRayFixture.compare.txt"
run_compare "$WADRAY_FIXTURE" AaveV3WadRayFixture "$WADRAY_COMPARE" \
  --calldata "$("$CAST_BIN" calldata 'wadMulOf(uint256,uint256)' 2000000000000000000 3000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata 'wadMulOf(uint256,uint256)' "$MAX_UINT" 2)" \
  --calldata "$("$CAST_BIN" calldata 'wadDivOf(uint256,uint256)' 5000000000000000000 2000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata 'wadDivOf(uint256,uint256)' 1 0)" \
  --calldata "$("$CAST_BIN" calldata 'rayMulOf(uint256,uint256)' 2000000000000000000000000000 3000000000000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata 'rayDivOf(uint256,uint256)' 5000000000000000000000000000 2000000000000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata 'rayDivOf(uint256,uint256)' 1 3)" \
  --calldata "$("$CAST_BIN" calldata 'rayToWadOf(uint256)' 1234567890123456789500000000)" \
  --calldata "$("$CAST_BIN" calldata 'wadToRayOf(uint256)' 7000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata 'wadToRayOf(uint256)' "$MAX_UINT")"
grep -qx 'calls=10' "$WADRAY_COMPARE"

PERCENTAGE_COMPARE="$OUTDIR/AaveV3PercentageFixture.compare.txt"
run_compare "$PERCENTAGE_FIXTURE" AaveV3PercentageFixture "$PERCENTAGE_COMPARE" \
  --calldata "$("$CAST_BIN" calldata 'percentMulOf(uint256,uint256)' 123456789 1234)" \
  --calldata "$("$CAST_BIN" calldata 'percentMulOf(uint256,uint256)' 1000000000000000000000000000 5000)" \
  --calldata "$("$CAST_BIN" calldata 'percentMulOf(uint256,uint256)' "$MAX_UINT" 10001)" \
  --calldata "$("$CAST_BIN" calldata 'percentDivOf(uint256,uint256)' 123456789 1234)" \
  --calldata "$("$CAST_BIN" calldata 'percentDivOf(uint256,uint256)' 1 0)" \
  --calldata "$("$CAST_BIN" calldata 'percentDivOf(uint256,uint256)' "$MAX_UINT" 1)"
grep -qx 'calls=6' "$PERCENTAGE_COMPARE"

MATHUTILS_COMPARE="$OUTDIR/AaveV3MathUtilsFixture.compare.txt"
run_compare "$MATHUTILS_FIXTURE" AaveV3MathUtilsFixture "$MATHUTILS_COMPARE" \
  --calldata "$("$CAST_BIN" calldata 'compoundedInterest(uint256,uint40,uint256)' 50000000000000000000000000 1 31536001)" \
  --calldata "$("$CAST_BIN" calldata 'compoundedInterest(uint256,uint40,uint256)' 50000000000000000000000000 1000 1000)" \
  --calldata "$("$CAST_BIN" calldata 'compoundedInterest(uint256,uint40,uint256)' 50000000000000000000000000 1 2)" \
  --calldata "$("$CAST_BIN" calldata 'compoundedInterest(uint256,uint40,uint256)' 1000000000000000000000000000 1 63072001)" \
  --calldata "$("$CAST_BIN" calldata 'compoundedInterest(uint256,uint40,uint256)' "$MAX_UINT" 1 31536001)" \
  --calldata "$("$CAST_BIN" calldata 'linearInterest(uint256,uint40)' 50000000000000000000000000 0)" \
  --calldata "$("$CAST_BIN" calldata 'linearInterest(uint256,uint40)' 300000000000000000000000000 1)"
grep -qx 'calls=7' "$MATHUTILS_COMPARE"

printf 'aave_v3_execution_compare=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'solc_version=%s\n' "$AAVE_V3_SOLC_VERSION"
printf 'evm_version=%s\n' "$AAVE_V3_EVM_VERSION"
printf 'forge_evm_version=%s\n' "$AAVE_V3_FORGE_EVM_VERSION"
printf 'wadray_calls=%s\n' "$(sed -n 's/^calls=//p' "$WADRAY_COMPARE")"
printf 'percentage_calls=%s\n' "$(sed -n 's/^calls=//p' "$PERCENTAGE_COMPARE")"
printf 'mathutils_calls=%s\n' "$(sed -n 's/^calls=//p' "$MATHUTILS_COMPARE")"

