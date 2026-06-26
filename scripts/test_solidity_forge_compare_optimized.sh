#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-compare-optimized.XXXXXX")"

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
via_ir = true
optimizer = true
optimizer_runs = 200
TOML

cat > "$OUTDIR/test/OptimizedCompare.t.sol" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

contract OptimizedCompareTest {
    function fold(uint256 x) internal pure returns (uint256) {
        uint256 total = 3;
        for (uint256 i = 0; i < 4; i++) {
            total = total * 7 + x + i;
        }
        return total;
    }

    function testFold() public pure {
        if (fold(5) != 9269) {
            revert();
        }
    }
}
SOL

(
  cd "$OUTDIR"
  SOLC="$SOLC_BIN" \
  LAKE="$LAKE_BIN" \
  FORGE="$FORGE_BIN" \
  SOLC_LEAN_OPTIMIZED=1 \
    "$ROOT/scripts/compare_forge_solc_lean.sh" --match-test testFold \
    > "$OUTDIR/compare.log"
)

grep -q '^forge_compare=pass$' "$OUTDIR/compare.log"
grep -q '^results_match=yes$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_count=1$' "$OUTDIR/compare.log"
grep -q '^forge_compare_result_1=PASS testFold()$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_passed=1$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_failed=0$' "$OUTDIR/compare.log"
grep -q '^forge_compare_tests_skipped=0$' "$OUTDIR/compare.log"
grep -q '^bridge_json_manifest_validated=yes$' "$OUTDIR/compare.log"
grep -q '^bridge_json_summary_validated=yes$' "$OUTDIR/compare.log"
grep -q '^bridge_json_backend_compatibility=ready$' "$OUTDIR/compare.log"
grep -q '^bridge_json_summary_objects=2$' "$OUTDIR/compare.log"
grep -q '^bridge_json_summary_skipped_contracts=0$' "$OUTDIR/compare.log"

cat "$OUTDIR/compare.log"
