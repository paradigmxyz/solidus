#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-compare-libraries.XXXXXX")"

cleanup() {
  exit_code=$?
  if [[ "$exit_code" -ne 0 && -f "$OUTDIR/compare.log" ]]; then
    echo "--- library forge compare log ---" >&2
    cat "$OUTDIR/compare.log" >&2
  fi
  rm -rf "$OUTDIR"
}
trap cleanup EXIT

mkdir -p "$OUTDIR/src/lib" "$OUTDIR/test"

cat > "$OUTDIR/foundry.toml" <<'TOML'
[profile.default]
src = "src"
test = "test"
out = "out"
cache_path = "cache"
evm_version = "cancun"
libraries = ["src/lib/ScaleLib.sol:ScaleLib:0x000000000000000000000000000000000000002a"]
TOML

cat > "$OUTDIR/src/lib/ScaleLib.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

library ScaleLib {
    function scale(uint256 value) internal pure returns (uint256) {
        return value * 7 + 3;
    }

    function folded(uint256 first, uint256 second, uint256 third)
        internal
        pure
        returns (uint256)
    {
        return scale(first) + scale(second) + scale(third);
    }
}
SOL

cat > "$OUTDIR/src/LibraryHarness.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ScaleLib} from "./lib/ScaleLib.sol";

contract LibraryHarness {
    using ScaleLib for uint256;

    function score(uint256 value) public pure returns (uint256) {
        return value.scale() + (value ^ 0x55);
    }

    function folded(uint256 first, uint256 second, uint256 third)
        public
        pure
        returns (uint256)
    {
        return ScaleLib.folded(first, second, third);
    }
}
SOL

cat > "$OUTDIR/test/LibraryCompare.t.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {LibraryHarness} from "../src/LibraryHarness.sol";

contract LibraryCompareTest is LibraryHarness {
    function testLibraryScore() public pure {
        if (score(5) != 118) revert();
    }

    function testLibraryFolded() public pure {
        if (folded(1, 2, 3) != 51) revert();
    }
}
SOL

(
  cd "$OUTDIR"
  SOLC="$SOLC_BIN" LAKE="$LAKE_BIN" FORGE="$FORGE_BIN" \
    "$ROOT/scripts/compare_forge_solc_lean.sh" --match-test testLibrary \
    > "$OUTDIR/compare.log"
)

grep -q '^forge_compare=pass$' "$OUTDIR/compare.log"
grep -q '^results_match=yes$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_count=2$' "$OUTDIR/compare.log"
grep -Eq '^forge_compare_result_[0-9]+=PASS testLibraryFolded\(\)$' \
  "$OUTDIR/compare.log"
grep -Eq '^forge_compare_result_[0-9]+=PASS testLibraryScore\(\)$' \
  "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_passed=2$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_failed=0$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_skipped=0$' "$OUTDIR/compare.log"
  "$OUTDIR/compare.log"
  "$OUTDIR/compare.log"

cat "$OUTDIR/compare.log"
