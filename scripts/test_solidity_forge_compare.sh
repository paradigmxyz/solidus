#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-compare-smoke.XXXXXX")"

cleanup() {
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

cat > "$OUTDIR/test/SimpleCompare.t.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract SimpleCompareTest {
    function addOne(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    function testAddOne() public pure {
        if (addOne(41) != 42) {
            revert();
        }
    }
}
SOL

(
  cd "$OUTDIR"
  SOLC="$SOLC_BIN" LAKE="$LAKE_BIN" FORGE="$FORGE_BIN" \
    "$ROOT/scripts/compare_forge_solc_lean.sh" --match-test testAddOne \
    > "$OUTDIR/compare.log"
)

grep -q '^forge_compare=pass$' "$OUTDIR/compare.log"
grep -q '^results_match=yes$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_count=1$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_1=PASS testAddOne()$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_passed=1$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_failed=0$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_skipped=0$' "$OUTDIR/compare.log"

cat "$OUTDIR/compare.log"
