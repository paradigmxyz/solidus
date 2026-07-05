#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-compare-imports.XXXXXX")"

cleanup() {
  status=$?
  if [[ "$status" -ne 0 && -f "$OUTDIR/compare.log" ]]; then
    echo "--- imported forge compare log ---" >&2
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
TOML

cat > "$OUTDIR/src/lib/ScaleBase.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

contract ScaleBase {
    function scale(uint256 value) internal pure returns (uint256) {
        return value * 7 + 3;
    }

    function foldedScale(uint256 first, uint256 second, uint256 third)
        internal
        pure
        returns (uint256)
    {
        return scale(first) + scale(second) + scale(third);
    }
}
SOL

cat > "$OUTDIR/src/ImportedHarness.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ScaleBase} from "./lib/ScaleBase.sol";

contract ImportedHarness is ScaleBase {
    function score(uint256 value) public pure returns (uint256) {
        return scale(value) + (value ^ 0x55);
    }

    function folded(uint256 first, uint256 second, uint256 third)
        public
        pure
        returns (uint256)
    {
        return foldedScale(first, second, third);
    }
}
SOL

cat > "$OUTDIR/test/ImportCompare.t.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ImportedHarness} from "../src/ImportedHarness.sol";

contract ImportCompareTest is ImportedHarness {
    function testImportedScore() public pure {
        if (score(5) != 118) {
            revert();
        }
    }

    function testImportedFolded() public pure {
        if (folded(1, 2, 3) != 51) {
            revert();
        }
    }
}
SOL

(
  cd "$OUTDIR"
  SOLC="$SOLC_BIN" LAKE="$LAKE_BIN" FORGE="$FORGE_BIN" \
    "$ROOT/scripts/compare_forge_solc_lean.sh" --match-test testImported \
    > "$OUTDIR/compare.log"
)

grep -q '^forge_compare=pass$' "$OUTDIR/compare.log"
grep -q '^results_match=yes$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_count=2$' "$OUTDIR/compare.log"
grep -Eq '^forge_compare_result_[0-9]+=PASS testImportedFolded\(\)$' \
  "$OUTDIR/compare.log"
grep -Eq '^forge_compare_result_[0-9]+=PASS testImportedScore\(\)$' \
  "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_passed=2$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_failed=0$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_skipped=0$' "$OUTDIR/compare.log"
cat "$OUTDIR/compare.log"
