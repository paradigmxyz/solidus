#!/usr/bin/env bash
set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REAL_SOLC="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
PYTHON_BIN="${PYTHON:-python3}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-compare.XXXXXX")"
KEEP_TMP="${KEEP_TMP:-0}"

cleanup() {
  status=$?
  if [[ "$KEEP_TMP" == "1" || "$status" -ne 0 ]]; then
    echo "kept_tmp=$OUTDIR" >&2
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

usage() {
  cat <<USAGE
Usage: $(basename "$0") [forge test args...]

Runs the same Forge test selection twice:
  1. full solc via --use \$SOLC
  2. solc-lean via scripts/solc_lean_standard_json.py

The solc-lean run produces bytecode through the verified in-Lean raw path
(solc Standard JSON output decoded by \`evm-compiler-backend raw-image\`).

Environment:
  SOLC      Real solc executable. Default: solc
  LAKE      Lake executable. Default: lake
  FORGE     Forge executable. Default: forge
  PYTHON    Python executable used for result normalization.
            Default: python3
  KEEP_TMP  Set to 1 to keep logs/artifacts under the temp directory.

Example:
  $(basename "$0") --match-test testAddOne -vv
USAGE
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

if [[ "$REAL_SOLC" != */* ]]; then
  resolved_solc="$(command -v "$REAL_SOLC" || true)"
  if [[ -n "$resolved_solc" ]]; then
    REAL_SOLC="$resolved_solc"
  fi
fi

if [[ "$FORGE_BIN" != */* ]]; then
  resolved_forge="$(command -v "$FORGE_BIN" || true)"
  if [[ -n "$resolved_forge" ]]; then
    FORGE_BIN="$resolved_forge"
  fi
fi

if [[ "$PYTHON_BIN" != */* ]]; then
  resolved_python="$(command -v "$PYTHON_BIN" || true)"
  if [[ -n "$resolved_python" ]]; then
    PYTHON_BIN="$resolved_python"
  fi
fi

if [[ ! -x "$REAL_SOLC" ]]; then
  echo "error: real solc is not executable: $REAL_SOLC" >&2
  exit 2
fi

if [[ ! -x "$FORGE_BIN" ]]; then
  echo "error: forge is not executable: $FORGE_BIN" >&2
  exit 2
fi

if [[ ! -x "$PYTHON_BIN" ]]; then
  echo "error: python is not executable: $PYTHON_BIN" >&2
  exit 2
fi

wrapper="$ROOT/scripts/solc_lean_standard_json.py"
full_log="$OUTDIR/full-solc.log"
lean_log="$OUTDIR/solc-lean.log"
full_results="$OUTDIR/full-solc.results"
lean_results="$OUTDIR/solc-lean.results"
gas_report="$OUTDIR/gas-report.txt"

full_args=(
  test
  --use "$REAL_SOLC"
  --no-auto-detect
  --force
  --out "$OUTDIR/full-out"
  --cache-path "$OUTDIR/full-cache"
  "$@"
)

lean_args=(
  test
  --use "$wrapper"
  --no-auto-detect
  --force
  --out "$OUTDIR/lean-out"
  --cache-path "$OUTDIR/lean-cache"
  "$@"
)

set +e
"$FORGE_BIN" "${full_args[@]}" >"$full_log" 2>&1
full_status=$?

SOLC_LEAN_REAL_SOLC="$REAL_SOLC" \
SOLC_LEAN_LAKE="$LAKE_BIN" \
SOLC_LEAN_LAKE_CWD="$ROOT" \
  "$FORGE_BIN" "${lean_args[@]}" >"$lean_log" 2>&1
lean_status=$?
set -e

"$PYTHON_BIN" - "$full_log" "$lean_log" "$full_results" "$lean_results" "$gas_report" <<'PY'
import re
import sys
from pathlib import Path

ansi = re.compile(r"\x1b\[[0-9;]*m")
test_line = re.compile(r"^\[(PASS|FAIL|SKIP)\]\s+(.+)$")
gas_suffix = re.compile(r"\s+\(gas:\s*(\d+)\)$")
summary = re.compile(
    r"^Ran\s+\d+\s+test suites?.*:\s+(\d+)\s+tests?\s+passed,\s+"
    r"(\d+)\s+failed,\s+(\d+)\s+skipped"
)


def normalize(path: Path) -> tuple[list[str], dict[str, int]]:
    """Return (parity lines, per-test gas).

    The parity lines are gas-STRIPPED on purpose: pass/fail parity between the
    two backends is what gates the build, and the two backends legitimately
    emit different gas. The gas map is captured separately so gas can be
    reported side by side without ever affecting the parity diff or exit code.
    """
    result_lines: list[str] = []
    summary_lines: list[str] = []
    gas: dict[str, int] = {}
    for raw in path.read_text(errors="replace").splitlines():
        line = ansi.sub("", raw).strip()
        match = test_line.match(line)
        if match:
            name_with_gas = match.group(2)
            gas_match = gas_suffix.search(name_with_gas)
            test_name = gas_suffix.sub("", name_with_gas)
            result_lines.append(f"{match.group(1)} {test_name}")
            if gas_match:
                gas[test_name] = int(gas_match.group(1))
            continue
        match = summary.match(line)
        if match:
            summary_lines.append(
                "SUMMARY passed="
                + match.group(1)
                + " failed="
                + match.group(2)
                + " skipped="
                + match.group(3)
            )
    normalized = sorted(result_lines)
    if summary_lines:
        normalized.append(summary_lines[-1])
    if not normalized:
        normalized.append("NO_FORGE_TEST_RESULTS_FOUND")
    return normalized, gas


full_log, lean_log, full_results, lean_results, gas_report = map(
    Path, sys.argv[1:]
)
full_norm, full_gas = normalize(full_log)
lean_norm, lean_gas = normalize(lean_log)
full_results.write_text("\n".join(full_norm) + "\n")
lean_results.write_text("\n".join(lean_norm) + "\n")

# Gas-visibility channel: record solc vs Lean execution gas per test, side by
# side. This is INFORMATIONAL only — divergent gas never fails the build (the
# two backends differ by design); the parity diff above is the gate.
report: list[str] = []
for name in sorted(set(full_gas) | set(lean_gas)):
    s = full_gas.get(name)
    l = lean_gas.get(name)
    if s is not None and l is not None:
        delta = l - s
        pct = (delta / s * 100.0) if s else 0.0
        report.append(
            f"forge_compare_gas={name} solc={s} lean={l} "
            f"delta={delta:+d} ({pct:+.2f}%)"
        )
    else:
        report.append(
            f"forge_compare_gas={name} "
            f"solc={'NA' if s is None else s} "
            f"lean={'NA' if l is None else l}"
        )
gas_report.write_text(("\n".join(report) + "\n") if report else "")
PY

if [[ "$full_status" -ne "$lean_status" ]]; then
  echo "forge_compare=fail"
  echo "full_solc_status=$full_status"
  echo "solc_lean_status=$lean_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "--- full solc tail ---"
  tail -n 40 "$full_log"
  echo "--- solc-lean tail ---"
  tail -n 80 "$lean_log"
  exit 1
fi

if grep -qx 'NO_FORGE_TEST_RESULTS_FOUND' "$full_results" \
  && grep -qx 'NO_FORGE_TEST_RESULTS_FOUND' "$lean_results"; then
  echo "forge_compare=fail"
  echo "reason=no_forge_test_results"
  echo "status=$full_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "full_solc_results=$full_results"
  echo "solc_lean_results=$lean_results"
  echo "--- full solc tail ---"
  tail -n 40 "$full_log"
  echo "--- solc-lean tail ---"
  tail -n 80 "$lean_log"
  exit 1
fi

if ! diff -u "$full_results" "$lean_results" >"$OUTDIR/result-diff.txt"; then
  echo "forge_compare=fail"
  echo "reason=result_mismatch"
  echo "status=$full_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "result_diff=$OUTDIR/result-diff.txt"
  cat "$OUTDIR/result-diff.txt"
  exit 1
fi

# Parity holds (same PASS/FAIL/SKIP set). Surface the gas both backends spent,
# side by side. This is observability only: gas divergence is expected and does
# NOT change the exit status below.
if [[ -s "$gas_report" ]]; then
  echo "--- gas comparison (solc vs lean; informational, non-failing) ---"
  cat "$gas_report"
  echo "gas_report=$gas_report"
fi

if [[ "$full_status" -ne 0 ]]; then
  echo "forge_compare=same_failure"
  echo "status=$full_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  exit "$full_status"
fi

result_count="$(grep -Ec '^(PASS|FAIL|SKIP) ' "$full_results" || true)"
summary_line="$(grep -E '^SUMMARY passed=[0-9]+ failed=[0-9]+ skipped=[0-9]+$' "$full_results" | tail -n 1 || true)"
if [[ ! "$summary_line" =~ ^SUMMARY\ passed=([0-9]+)\ failed=([0-9]+)\ skipped=([0-9]+)$ ]]; then
  echo "forge_compare=fail"
  echo "reason=forge_summary_missing"
  echo "status=$full_status"
  echo "forge_compare_result_count=$result_count"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "full_solc_results=$full_results"
  echo "solc_lean_results=$lean_results"
  echo "--- full solc tail ---"
  tail -n 40 "$full_log"
  echo "--- solc-lean tail ---"
  tail -n 80 "$lean_log"
  exit 1
fi
summary_passed="${BASH_REMATCH[1]}"
summary_failed="${BASH_REMATCH[2]}"
summary_skipped="${BASH_REMATCH[3]}"
summary_total=$((summary_passed + summary_failed + summary_skipped))
if [[ "$result_count" -ne "$summary_total" ]]; then
  echo "forge_compare=fail"
  echo "reason=forge_result_count_mismatch"
  echo "status=$full_status"
  echo "forge_compare_result_count=$result_count"
  echo "forge_compare_summary_count=$summary_total"
  echo "forge_compare_tests_passed=$summary_passed"
  echo "forge_compare_tests_failed=$summary_failed"
  echo "forge_compare_tests_skipped=$summary_skipped"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "full_solc_results=$full_results"
  echo "solc_lean_results=$lean_results"
  echo "--- full solc tail ---"
  tail -n 40 "$full_log"
  echo "--- solc-lean tail ---"
  tail -n 80 "$lean_log"
  exit 1
fi

echo "forge_compare=pass"
echo "status=0"
echo "results_match=yes"
echo "forge_compare_result_count=$result_count"
result_index=0
while IFS= read -r result_line; do
  case "$result_line" in
    PASS\ *|FAIL\ *|SKIP\ *)
      result_index=$((result_index + 1))
      echo "forge_compare_result_${result_index}=$result_line"
      ;;
  esac
done <"$full_results"
echo "forge_compare_tests_passed=$summary_passed"
echo "forge_compare_tests_failed=$summary_failed"
echo "forge_compare_tests_skipped=$summary_skipped"
if [[ "$KEEP_TMP" == "1" ]]; then
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "full_solc_results=$full_results"
  echo "solc_lean_results=$lean_results"
else
  echo "logs_kept=no"
fi
