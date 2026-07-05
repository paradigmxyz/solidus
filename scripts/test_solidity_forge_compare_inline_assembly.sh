#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-compare-inline-assembly.XXXXXX")"

cleanup() {
  status=$?
  if [[ "$status" -ne 0 && -f "$OUTDIR/compare.log" ]]; then
    echo "--- inline assembly forge compare log ---" >&2
    cat "$OUTDIR/compare.log" >&2
  fi
  rm -rf "$OUTDIR"
}
trap cleanup EXIT

mkdir -p "$OUTDIR/src" "$OUTDIR/test"

cat > "$OUTDIR/foundry.toml" <<'TOML'
[profile.default]
src = "src"
test = "test"
out = "out"
cache_path = "cache"
evm_version = "cancun"
TOML

cat > "$OUTDIR/src/InlineAssemblyHarness.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

contract InlineAssemblyHarness {
    event Stored(uint256 indexed oldValue, uint256 newValue);

    uint256 internal stored;

    function asmMath(uint256 left, uint256 right)
        public
        pure
        returns (uint256 sum, uint256 product, uint256 mixed)
    {
        assembly ("memory-safe") {
            sum := add(left, right)
            product := mul(left, right)
            mixed := xor(shl(4, left), shr(1, right))
        }
    }

    function writeSlot(uint256 next) public returns (uint256 oldValue) {
        assembly {
            oldValue := sload(stored.slot)
            sstore(stored.slot, next)
        }
        emit Stored(oldValue, next);
    }

    function readSlot() public view returns (uint256 current) {
        assembly {
            current := sload(stored.slot)
        }
    }

    function digest(bytes memory input)
        public
        pure
        returns (bytes32 hashValue, uint256 length)
    {
        assembly ("memory-safe") {
            length := mload(input)
            hashValue := keccak256(add(input, 0x20), length)
        }
    }

    function checkedDiv(uint256 denominator) public pure returns (uint256 result) {
        assembly ("memory-safe") {
            if iszero(denominator) {
                mstore(0x00, shl(224, 0x4e487b71))
                mstore(0x04, 0x12)
                revert(0x00, 0x24)
            }
        }
        result = 100 / denominator;
    }
}
SOL

cat > "$OUTDIR/test/InlineAssemblyCompare.t.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {InlineAssemblyHarness} from "../src/InlineAssemblyHarness.sol";

contract InlineAssemblyCompareTest is InlineAssemblyHarness {
    function testInlineAssemblyArithmetic() public pure {
        (uint256 sum, uint256 product, uint256 mixed) = asmMath(7, 9);
        if (sum != 16 || product != 63 || mixed != 116) {
            revert();
        }
        if (checkedDiv(4) != 25) {
            revert();
        }
    }

    function testInlineAssemblyStorageAndHash() public {
        if (readSlot() != 0) {
            revert();
        }
        if (writeSlot(42) != 0) {
            revert();
        }
        if (readSlot() != 42) {
            revert();
        }
        if (writeSlot(99) != 42) {
            revert();
        }
        if (readSlot() != 99) {
            revert();
        }

        (bytes32 hashValue, uint256 length) = digest(hex"112233445566");
        if (
            length != 6 ||
            hashValue != 0x67b2e3dafd05b82d7f58cb68f8bb7b735faec6b9258c143f8e10509016a61fb8
        ) {
            revert();
        }
    }
}
SOL

(
  cd "$OUTDIR"
  SOLC="$SOLC_BIN" LAKE="$LAKE_BIN" FORGE="$FORGE_BIN" \
    "$ROOT/scripts/compare_forge_solc_lean.sh" --match-test testInlineAssembly \
    > "$OUTDIR/compare.log"
)

grep -q '^forge_compare=pass$' "$OUTDIR/compare.log"
grep -q '^results_match=yes$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_count=2$' "$OUTDIR/compare.log"
grep -Eq '^forge_compare_result_[0-9]+=PASS testInlineAssemblyArithmetic\(\)$' \
  "$OUTDIR/compare.log"
grep -Eq '^forge_compare_result_[0-9]+=PASS testInlineAssemblyStorageAndHash\(\)$' \
  "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_passed=2$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_failed=0$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_skipped=0$' "$OUTDIR/compare.log"
cat "$OUTDIR/compare.log"
