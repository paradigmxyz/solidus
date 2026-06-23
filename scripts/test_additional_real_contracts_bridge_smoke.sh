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
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-additional-real-contracts.XXXXXX")"
REAL_CONTRACTS_SOLC_VERSION="${REAL_CONTRACTS_SOLC_VERSION:-0.8.26}"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

PRB_MATH_REPO_URL="${PRB_MATH_REPO_URL:-https://github.com/PaulRBerg/prb-math.git}"
PRB_MATH_REF="${PRB_MATH_REF:-982c369fe95e1d2c93d2bb1fd8650becbbfb92f1}"
SOLBASE_REPO_URL="${SOLBASE_REPO_URL:-https://github.com/Sol-DAO/solbase.git}"
SOLBASE_REF="${SOLBASE_REF:-e12d00b9ff196667e3199d61971907510948583b}"
BALANCER_V3_REPO_URL="${BALANCER_V3_REPO_URL:-https://github.com/balancer/balancer-v3-monorepo.git}"
BALANCER_V3_REF="${BALANCER_V3_REF:-80fd29ce4eb627139694db7fef5aba355759d303}"
SEAPORT_REPO_URL="${SEAPORT_REPO_URL:-https://github.com/ProjectOpenSea/seaport.git}"
SEAPORT_REF="${SEAPORT_REF:-080133906585660f6a76b82984f3fb690ff4b2a9}"

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
    printf 'error: %s cannot provide solc %s\n%s\n' \
      "$SOLC_BIN" "$version" "$output" >&2
    return 1
  fi
}

checkout_repo() {
  local directory="$1"
  local url="$2"
  local ref="$3"

  git init -q "$directory"
  git -C "$directory" remote add origin "$url"
  git -C "$directory" fetch --depth 1 origin "$ref"
  git -C "$directory" -c advice.detachedHead=false checkout -q FETCH_HEAD
}

ensure_solc_version "$REAL_CONTRACTS_SOLC_VERSION"

if [[ -n "${PRB_MATH_DIR:-}" ]]; then
  PRB_MATH_REPO="$PRB_MATH_DIR"
else
  PRB_MATH_REPO="$OUTDIR/prb-math"
  checkout_repo "$PRB_MATH_REPO" "$PRB_MATH_REPO_URL" "$PRB_MATH_REF"
fi

if [[ -n "${SOLBASE_DIR:-}" ]]; then
  SOLBASE_REPO="$SOLBASE_DIR"
else
  SOLBASE_REPO="$OUTDIR/solbase"
  checkout_repo "$SOLBASE_REPO" "$SOLBASE_REPO_URL" "$SOLBASE_REF"
fi

if [[ -n "${BALANCER_V3_DIR:-}" ]]; then
  BALANCER_V3_REPO="$BALANCER_V3_DIR"
else
  BALANCER_V3_REPO="$OUTDIR/balancer-v3"
  checkout_repo "$BALANCER_V3_REPO" "$BALANCER_V3_REPO_URL" "$BALANCER_V3_REF"
fi

if [[ -n "${SEAPORT_DIR:-}" ]]; then
  SEAPORT_REPO="$SEAPORT_DIR"
else
  SEAPORT_REPO="$OUTDIR/seaport"
  checkout_repo "$SEAPORT_REPO" "$SEAPORT_REPO_URL" "$SEAPORT_REF"
fi

PRB_MATH_ACTUAL_REF="$(git -C "$PRB_MATH_REPO" rev-parse HEAD)"
SOLBASE_ACTUAL_REF="$(git -C "$SOLBASE_REPO" rev-parse HEAD)"
BALANCER_V3_ACTUAL_REF="$(git -C "$BALANCER_V3_REPO" rev-parse HEAD)"
SEAPORT_ACTUAL_REF="$(git -C "$SEAPORT_REPO" rev-parse HEAD)"

PRB_MATH_FIXTURE="$OUTDIR/PRBMathRealWorldFallback.sol"
SOLBASE_FIXTURE="$OUTDIR/SolbaseRealWorldFallback.sol"
BALANCER_FIXTURE="$OUTDIR/BalancerV3RealWorldFallback.sol"
SEAPORT_FIXTURE="$OUTDIR/SeaportMerkleRealWorldFallback.sol"

cat > "$PRB_MATH_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity >=0.8.19;

import { UD60x18 } from "prb/ud60x18/ValueType.sol";
import { wrap } from "prb/ud60x18/Casting.sol";
import {
    avg,
    ceil,
    div,
    floor,
    frac,
    gm,
    inv,
    log2,
    mul,
    powu,
    sqrt
} from "prb/ud60x18/Math.sol";

contract PRBMathRealWorldFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }

        UD60x18 result;
        if (mode == 1) {
            result = avg(wrap(2e18), wrap(4e18));
        } else if (mode == 2) {
            result = ceil(wrap(1.25e18));
        } else if (mode == 3) {
            result = div(wrap(5e18), wrap(2e18));
        } else if (mode == 4) {
            result = floor(wrap(1.75e18));
        } else if (mode == 5) {
            result = frac(wrap(1.75e18));
        } else if (mode == 6) {
            result = gm(wrap(4e18), wrap(9e18));
        } else if (mode == 7) {
            result = inv(wrap(2e18));
        } else if (mode == 8) {
            result = log2(wrap(8e18));
        } else if (mode == 9) {
            result = mul(wrap(2e18), wrap(3e18));
        } else if (mode == 10) {
            result = powu(wrap(2e18), 10);
        } else if (mode == 11) {
            result = sqrt(wrap(9e18));
        } else {
            result = inv(wrap(0));
        }

        uint256 raw = UD60x18.unwrap(result);
        assembly ("memory-safe") {
            mstore(0, raw)
            return(0, 32)
        }
    }
}
SOL

cat > "$SOLBASE_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

import { FixedPointMathLib } from "solbase/utils/FixedPointMathLib.sol";

contract SolbaseRealWorldFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }

        int256 result;
        if (mode == 1) {
            result = int256(FixedPointMathLib.mulWadDown(2e18, 3e18));
        } else if (mode == 2) {
            result = int256(FixedPointMathLib.mulWadUp(1e18 + 1, 1e18 + 1));
        } else if (mode == 3) {
            result = int256(FixedPointMathLib.divWadDown(5e18, 2e18));
        } else if (mode == 4) {
            result = int256(FixedPointMathLib.divWadUp(5e18 + 1, 2e18));
        } else if (mode == 5) {
            result = FixedPointMathLib.expWad(1e18);
        } else if (mode == 6) {
            result = FixedPointMathLib.lnWad(2e18);
        } else if (mode == 7) {
            result = FixedPointMathLib.powWad(2e18, 3e18);
        } else if (mode == 8) {
            result = int256(FixedPointMathLib.sqrt(81));
        } else if (mode == 9) {
            result = int256(FixedPointMathLib.log2(1024));
        } else if (mode == 10) {
            result = int256(FixedPointMathLib.mulDivUp(17, 19, 5));
        } else if (mode == 11) {
            result = FixedPointMathLib.lnWad(0.5e18);
        } else {
            result = FixedPointMathLib.lnWad(0);
        }

        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

cat > "$BALANCER_FIXTURE" <<'SOL'
// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.24;

import { FixedPoint } from "balancer/math/FixedPoint.sol";

contract BalancerV3RealWorldFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }

        uint256 result;
        if (mode == 1) {
            result = FixedPoint.mulDown(2e18, 3e18);
        } else if (mode == 2) {
            result = FixedPoint.mulUp(1e18 + 1, 1e18 + 1);
        } else if (mode == 3) {
            result = FixedPoint.divDown(5e18, 2e18);
        } else if (mode == 4) {
            result = FixedPoint.divUp(5e18 + 1, 2e18);
        } else if (mode == 5) {
            result = FixedPoint.mulDivUp(17, 19, 5);
        } else if (mode == 6) {
            result = FixedPoint.divUpRaw(17, 5);
        } else if (mode == 7) {
            result = FixedPoint.powDown(2e18, 2e18);
        } else if (mode == 8) {
            result = FixedPoint.powUp(2e18, 1.5e18);
        } else if (mode == 9) {
            result = FixedPoint.complement(0.25e18);
        } else if (mode == 10) {
            result = FixedPoint.powDown(0.5e18, 3e18);
        } else if (mode == 11) {
            result = FixedPoint.complement(2e18);
        } else {
            result = FixedPoint.divUp(1, 0);
        }

        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

cat > "$SEAPORT_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import { MerkleLib } from "seaport/helpers/navigator/lib/MerkleLib.sol";

contract SeaportMerkleRealWorldFallback {
    function _leaves(uint256 length)
        private
        pure
        returns (bytes32[] memory leaves)
    {
        leaves = new bytes32[](length);
        for (uint256 i = 0; i < length; ++i) {
            leaves[i] = keccak256(abi.encodePacked(i + 1));
        }
    }

    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }

        bytes32 result;
        if (mode == 1) {
            result = MerkleLib.merkleHash(bytes32(uint256(1)), bytes32(uint256(2)));
        } else if (mode == 2) {
            result = bytes32(MerkleLib.log2ceil(0));
        } else if (mode == 3) {
            result = bytes32(MerkleLib.log2ceil(17));
        } else if (mode == 4) {
            result = bytes32(MerkleLib.log2ceilBitMagic(16));
        } else if (mode == 5) {
            result = bytes32(MerkleLib.log2ceilBitMagic(17));
        } else if (mode == 6) {
            bytes32[] memory leaves = _leaves(4);
            result = MerkleLib.getRoot(leaves, MerkleLib.merkleHash);
        } else if (mode == 7) {
            bytes32[] memory leaves = _leaves(5);
            result = MerkleLib.getRoot(leaves, MerkleLib.merkleHash);
        } else if (mode == 8) {
            bytes32[] memory leaves = _leaves(5);
            bytes32[] memory proof = MerkleLib.getProof(
                leaves,
                3,
                MerkleLib.merkleHash
            );
            result = keccak256(abi.encode(proof));
        } else if (mode == 9) {
            bytes32[] memory leaves = _leaves(5);
            bytes32 root = MerkleLib.getRoot(leaves, MerkleLib.merkleHash);
            bytes32[] memory proof = MerkleLib.getProof(
                leaves,
                3,
                MerkleLib.merkleHash
            );
            result = bytes32(
                MerkleLib.verifyProof(
                    root,
                    proof,
                    leaves[3],
                    MerkleLib.merkleHash
                )
                    ? uint256(1)
                    : uint256(0)
            );
        } else if (mode == 10) {
            bytes32[] memory leaves = _leaves(5);
            bytes32 root = MerkleLib.getRoot(leaves, MerkleLib.merkleHash);
            bytes32[] memory proof = MerkleLib.getProof(
                leaves,
                3,
                MerkleLib.merkleHash
            );
            proof[0] = bytes32(uint256(proof[0]) ^ 1);
            result = bytes32(
                MerkleLib.verifyProof(
                    root,
                    proof,
                    leaves[3],
                    MerkleLib.merkleHash
                )
                    ? uint256(1)
                    : uint256(0)
            );
        } else if (mode == 11) {
            bytes32[] memory leaves = _leaves(6);
            bytes32[] memory proof = MerkleLib.getProof(
                leaves,
                5,
                MerkleLib.merkleHash
            );
            result = bytes32(proof.length);
        } else {
            bytes32[] memory leaves = _leaves(1);
            result = MerkleLib.getRoot(leaves, MerkleLib.merkleHash);
        }

        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

run_real_contract_case() {
  local label="$1"
  local fixture="$2"
  local contract="$3"
  local remapping="$4"
  local expected_calls="$5"
  local compare_mode="$6"
  shift 6

  local case_dir="$OUTDIR/$label"
  local bridge_dir="$case_dir/bridge-json"
  local decode_check="$case_dir/lean-json-check.txt"
  local summary="$case_dir/bridge-json-summary.json"
  local backend_check="$case_dir/lean-backend-check.json"
  local compare="$case_dir/call-compare.txt"
  local calldata_args=()
  local calldata

  mkdir -p "$case_dir"
  if [[ "$compare_mode" != "both" && "$compare_mode" != "runtime-only" ]]; then
    printf 'error: unknown comparison mode %s\n' "$compare_mode" >&2
    return 1
  fi
  for calldata in "$@"; do
    calldata_args+=(--calldata "$calldata")
  done

  SOLC_VERSION="$REAL_CONTRACTS_SOLC_VERSION" "$PYTHON_BIN" \
    "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$fixture" \
    --solc "$SOLC_BIN" \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --remapping "$remapping" \
    --contract "$contract" \
    --optimized \
    --format lean-json-check \
    --bridge-json-dir "$bridge_dir" \
    --output "$decode_check"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
    --quiet "$bridge_dir/manifest.json"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$bridge_dir/manifest.json" \
    --input-format bridge-json-manifest \
    --format bridge-json-summary \
    --output "$summary"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$summary"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$bridge_dir/manifest.json" \
    --input-format bridge-json-manifest \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --format lean-backend-check \
    --output "$backend_check"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$backend_check"

  if [[ "$compare_mode" == "runtime-only" ]]; then
    SOLC_VERSION="$REAL_CONTRACTS_SOLC_VERSION" "$PYTHON_BIN" \
      "$ROOT/scripts/compare_contract_call_bytecode.py" \
      "$fixture" \
      --solc "$SOLC_BIN" \
      --lake "$LAKE_BIN" \
      --lake-cwd "$ROOT" \
      --forge "$FORGE_BIN" \
      --remapping "$remapping" \
      --contract "$contract" \
      --optimized \
      --runtime-only \
      "${calldata_args[@]}" > "$compare"
  else
    SOLC_VERSION="$REAL_CONTRACTS_SOLC_VERSION" "$PYTHON_BIN" \
      "$ROOT/scripts/compare_contract_call_bytecode.py" \
      "$fixture" \
      --solc "$SOLC_BIN" \
      --lake "$LAKE_BIN" \
      --lake-cwd "$ROOT" \
      --forge "$FORGE_BIN" \
      --remapping "$remapping" \
      --contract "$contract" \
      --optimized \
      "${calldata_args[@]}" > "$compare"
  fi

  "$PYTHON_BIN" - \
    "$label" \
    "$expected_calls" \
    "$decode_check" \
    "$summary" \
    "$backend_check" \
    "$compare" <<'PY'
import json
import sys

label = sys.argv[1]
expected_calls = int(sys.argv[2])
decode = open(sys.argv[3]).read()
summary = json.load(open(sys.argv[4]))
backend = json.load(open(sys.argv[5]))
compare_lines = open(sys.argv[6]).read().splitlines()

if "lean_bridge_json_decode=pass" not in decode:
    raise SystemExit(f"{label}: Lean bridge decode did not report pass")
if summary.get("counts", {}).get("objects", 0) < 1:
    raise SystemExit(f"{label}: bridge summary did not contain an object")
if backend.get("counts", {}).get("checkedObjects", 0) < 1:
    raise SystemExit(f"{label}: backend check did not inspect an object")
if backend.get("counts", {}).get("failedObjects") != 0:
    raise SystemExit(f"{label}: backend check failed: {backend!r}")
if "contract_call_compare=pass" not in compare_lines:
    raise SystemExit(f"{label}: Forge bytecode comparison did not pass")
if f"calls={expected_calls}" not in compare_lines:
    raise SystemExit(
        f"{label}: Forge comparison did not run {expected_calls} calls"
    )
PY

  printf '%s_compare_calls=%s\n' "$label" "$(
    sed -n 's/^calls=//p' "$compare"
  )"
  printf '%s_backend_objects=%s\n' "$label" "$(
    "$PYTHON_BIN" - "$backend_check" <<'PY'
import json
import sys

print(json.load(open(sys.argv[1]))["counts"]["checkedObjects"])
PY
  )"
}

run_real_contract_case \
  prb_math \
  "$PRB_MATH_FIXTURE" \
  PRBMathRealWorldFallback \
  "prb/=$PRB_MATH_REPO/src/" \
  12 \
  both \
  0x01 0x02 0x03 0x04 0x05 0x06 \
  0x07 0x08 0x09 0x0a 0x0b 0x0c

run_real_contract_case \
  solbase \
  "$SOLBASE_FIXTURE" \
  SolbaseRealWorldFallback \
  "solbase/=$SOLBASE_REPO/src/" \
  12 \
  both \
  0x01 0x02 0x03 0x04 0x05 0x06 \
  0x07 0x08 0x09 0x0a 0x0b 0x0c

run_real_contract_case \
  balancer_v3 \
  "$BALANCER_FIXTURE" \
  BalancerV3RealWorldFallback \
  "balancer/=$BALANCER_V3_REPO/pkg/solidity-utils/contracts/" \
  12 \
  runtime-only \
  0x01 0x02 0x03 0x04 0x05 0x06 \
  0x07 0x08 0x09 0x0a 0x0b 0x0c

run_real_contract_case \
  seaport \
  "$SEAPORT_FIXTURE" \
  SeaportMerkleRealWorldFallback \
  "seaport/=$SEAPORT_REPO/contracts/" \
  12 \
  both \
  0x01 0x02 0x03 0x04 0x05 0x06 \
  0x07 0x08 0x09 0x0a 0x0b 0x0c

printf 'additional_real_contracts_bridge_smoke=pass\n'
printf 'solc_version=%s\n' "$REAL_CONTRACTS_SOLC_VERSION"
printf 'prb_math_repo_ref=%s\n' "$PRB_MATH_ACTUAL_REF"
printf 'solbase_repo_ref=%s\n' "$SOLBASE_ACTUAL_REF"
printf 'balancer_v3_repo_ref=%s\n' "$BALANCER_V3_ACTUAL_REF"
printf 'seaport_repo_ref=%s\n' "$SEAPORT_ACTUAL_REF"
printf 'real_contract_repositories=4\n'
printf 'real_contract_compare_calls=48\n'
