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
BRIDGE_JSON_DIR="${SOLC_LEAN_BRIDGE_JSON_DIR:-$OUTDIR/bridge-json}"

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

On successful solc-lean compilation, validates the generated
bridge-json/manifest.json handoff package before reporting pass.

Environment:
  SOLC      Real solc executable. Default: solc
  LAKE      Lake executable. Default: lake
  FORGE     Forge executable. Default: forge
  PYTHON    Python executable used for bridge JSON validation and reports.
            Default: python3
  KEEP_TMP  Set to 1 to keep logs/artifacts under the temp directory.
  SOLC_LEAN_BRIDGE_JSON_DIR
            Directory for normalized bridge JSON files from the solc-lean run.
            Default: <temp>/bridge-json

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
bridge_json_validate_log="$OUTDIR/bridge-json-validate.log"
bridge_json_manifest="$BRIDGE_JSON_DIR/manifest.json"
bridge_json_summary="$OUTDIR/bridge-json-summary.json"
bridge_json_summary_log="$OUTDIR/bridge-json-summary.log"
bridge_json_summary_validate_log="$OUTDIR/bridge-json-summary-validate.log"
bridge_json_summary_report="$OUTDIR/bridge-json-summary.report"
mkdir -p "$BRIDGE_JSON_DIR"

build_bridge_summary_report() {
  if [[ ! -f "$bridge_json_manifest" ]]; then
    return 20
  fi
  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
    --quiet "$bridge_json_manifest" >"$bridge_json_validate_log" 2>&1 || return 21
  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$bridge_json_manifest" \
    --input-format bridge-json-manifest \
    --format bridge-json-summary \
    --output "$bridge_json_summary" \
    >"$bridge_json_summary_log" 2>&1 || return 22
  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
    --quiet "$bridge_json_summary" \
    >"$bridge_json_summary_validate_log" 2>&1 || return 23
  "$PYTHON_BIN" - "$bridge_json_summary" "$bridge_json_manifest" >"$bridge_json_summary_report" <<'PY' || return 24
import json
import sys

summary = json.load(open(sys.argv[1]))
manifest = json.load(open(sys.argv[2]))
counts = summary.get("counts", {})
compatibility = summary.get("backendCompatibility", {})

def csv(names):
    if not isinstance(names, list):
        return "none"
    strings = [name for name in names if isinstance(name, str)]
    return ",".join(strings) if strings else "none"

print(f"bridge_json_backend_compatibility={compatibility.get('status', 'unknown')}")
print(
    "bridge_json_summary_unsupported_primitives="
    f"{csv(compatibility.get('unsupportedPrimitiveNames'))}"
)
print(
    "bridge_json_summary_object_builtins="
    f"{csv(compatibility.get('objectBuiltinNames'))}"
)
print(
    "bridge_json_summary_dialect_builtins="
    f"{csv(compatibility.get('dialectBuiltinNames'))}"
)
print(f"bridge_json_summary_objects={counts.get('objects', 'unknown')}")
print(
    "bridge_json_summary_skipped_contracts="
    f"{counts.get('skippedContracts', 'unknown')}"
)
linker_symbols = manifest.get("linkerSymbols", [])
linker_names = [
    item.get("name")
    for item in linker_symbols
    if isinstance(item, dict) and isinstance(item.get("name"), str)
]
print(f"bridge_json_linker_symbol_count={len(linker_names)}")
print(f"bridge_json_linker_symbols={csv(linker_names)}")
PY
}

emit_bridge_summary_diagnostic() {
  local summary_status=0
  if build_bridge_summary_report; then
    summary_status=0
  else
    summary_status=$?
  fi
  case "$summary_status" in
    0)
      echo "bridge_json_manifest=$bridge_json_manifest"
      echo "bridge_json_manifest_validated=yes"
      echo "bridge_json_summary=$bridge_json_summary"
      echo "bridge_json_summary_validated=yes"
      cat "$bridge_json_summary_report"
      ;;
    20)
      echo "bridge_json_manifest=missing"
      ;;
    21)
      echo "bridge_json_manifest=$bridge_json_manifest"
      echo "bridge_json_manifest_validated=no"
      echo "bridge_json_validate_log=$bridge_json_validate_log"
      cat "$bridge_json_validate_log"
      ;;
    22)
      echo "bridge_json_manifest=$bridge_json_manifest"
      echo "bridge_json_manifest_validated=yes"
      echo "bridge_json_summary_status=failed"
      echo "bridge_json_summary_log=$bridge_json_summary_log"
      cat "$bridge_json_summary_log"
      ;;
    23)
      echo "bridge_json_manifest=$bridge_json_manifest"
      echo "bridge_json_manifest_validated=yes"
      echo "bridge_json_summary=$bridge_json_summary"
      echo "bridge_json_summary_validated=no"
      echo "bridge_json_summary_validate_log=$bridge_json_summary_validate_log"
      cat "$bridge_json_summary_validate_log"
      ;;
    *)
      echo "bridge_json_manifest=$bridge_json_manifest"
      echo "bridge_json_summary=$bridge_json_summary"
      echo "bridge_json_summary_report_status=failed"
      ;;
  esac
}

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
SOLC_LEAN_BRIDGE_JSON_DIR="$BRIDGE_JSON_DIR" \
  "$FORGE_BIN" "${lean_args[@]}" >"$lean_log" 2>&1
lean_status=$?
set -e

"$PYTHON_BIN" - "$full_log" "$lean_log" "$full_results" "$lean_results" <<'PY'
import re
import sys
from pathlib import Path

ansi = re.compile(r"\x1b\[[0-9;]*m")
test_line = re.compile(r"^\[(PASS|FAIL|SKIP)\]\s+(.+)$")
summary = re.compile(
    r"^Ran\s+\d+\s+test suites?.*:\s+(\d+)\s+tests?\s+passed,\s+"
    r"(\d+)\s+failed,\s+(\d+)\s+skipped"
)


def normalize(path: Path) -> list[str]:
    result_lines: list[str] = []
    summary_lines: list[str] = []
    for raw in path.read_text(errors="replace").splitlines():
        line = ansi.sub("", raw).strip()
        match = test_line.match(line)
        if match:
            test_name = re.sub(r"\s+\(gas:\s*\d+\)$", "", match.group(2))
            result_lines.append(f"{match.group(1)} {test_name}")
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
    return normalized


full_log, lean_log, full_results, lean_results = map(Path, sys.argv[1:])
full_results.write_text("\n".join(normalize(full_log)) + "\n")
lean_results.write_text("\n".join(normalize(lean_log)) + "\n")
PY

if [[ "$full_status" -ne "$lean_status" ]]; then
  echo "forge_compare=fail"
  echo "full_solc_status=$full_status"
  echo "solc_lean_status=$lean_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  emit_bridge_summary_diagnostic
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
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  emit_bridge_summary_diagnostic
  echo "--- full solc tail ---"
  tail -n 40 "$full_log"
  echo "--- solc-lean tail ---"
  tail -n 80 "$lean_log"
  exit 1
fi

if [[ "$lean_status" -eq 0 ]]; then
  summary_status=0
  if build_bridge_summary_report; then
    summary_status=0
  else
    summary_status=$?
  fi
  if [[ "$summary_status" -eq 20 ]]; then
    echo "forge_compare=fail"
    echo "reason=bridge_json_manifest_missing"
    echo "status=$lean_status"
    echo "full_solc_log=$full_log"
    echo "solc_lean_log=$lean_log"
    echo "bridge_json_dir=$BRIDGE_JSON_DIR"
    echo "bridge_json_manifest=$bridge_json_manifest"
    exit 1
  elif [[ "$summary_status" -eq 21 ]]; then
    echo "forge_compare=fail"
    echo "reason=bridge_json_manifest_invalid"
    echo "status=$lean_status"
    echo "full_solc_log=$full_log"
    echo "solc_lean_log=$lean_log"
    echo "bridge_json_dir=$BRIDGE_JSON_DIR"
    echo "bridge_json_manifest=$bridge_json_manifest"
    echo "bridge_json_validate_log=$bridge_json_validate_log"
    cat "$bridge_json_validate_log"
    exit 1
  elif [[ "$summary_status" -eq 22 ]]; then
    echo "forge_compare=fail"
    echo "reason=bridge_json_summary_failed"
    echo "status=$lean_status"
    echo "full_solc_log=$full_log"
    echo "solc_lean_log=$lean_log"
    echo "bridge_json_dir=$BRIDGE_JSON_DIR"
    echo "bridge_json_manifest=$bridge_json_manifest"
    echo "bridge_json_summary_log=$bridge_json_summary_log"
    cat "$bridge_json_summary_log"
    exit 1
  elif [[ "$summary_status" -eq 23 ]]; then
    echo "forge_compare=fail"
    echo "reason=bridge_json_summary_invalid"
    echo "status=$lean_status"
    echo "full_solc_log=$full_log"
    echo "solc_lean_log=$lean_log"
    echo "bridge_json_dir=$BRIDGE_JSON_DIR"
    echo "bridge_json_manifest=$bridge_json_manifest"
    echo "bridge_json_summary=$bridge_json_summary"
    echo "bridge_json_summary_validate_log=$bridge_json_summary_validate_log"
    cat "$bridge_json_summary_validate_log"
    exit 1
  elif [[ "$summary_status" -ne 0 ]]; then
    echo "forge_compare=fail"
    echo "reason=bridge_json_summary_report_failed"
    echo "status=$lean_status"
    echo "full_solc_log=$full_log"
    echo "solc_lean_log=$lean_log"
    echo "bridge_json_dir=$BRIDGE_JSON_DIR"
    echo "bridge_json_manifest=$bridge_json_manifest"
    echo "bridge_json_summary=$bridge_json_summary"
    exit 1
  fi
fi

if ! diff -u "$full_results" "$lean_results" >"$OUTDIR/result-diff.txt"; then
  echo "forge_compare=fail"
  echo "reason=result_mismatch"
  echo "status=$full_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  emit_bridge_summary_diagnostic
  echo "result_diff=$OUTDIR/result-diff.txt"
  cat "$OUTDIR/result-diff.txt"
  exit 1
fi

if [[ "$full_status" -ne 0 ]]; then
  echo "forge_compare=same_failure"
  echo "status=$full_status"
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  emit_bridge_summary_diagnostic
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
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  emit_bridge_summary_diagnostic
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
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  emit_bridge_summary_diagnostic
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
echo "bridge_json_manifest_validated=yes"
echo "bridge_json_summary_validated=yes"
if [[ -f "$bridge_json_summary_report" ]]; then
  cat "$bridge_json_summary_report"
fi
if [[ "$KEEP_TMP" == "1" ]]; then
  echo "full_solc_log=$full_log"
  echo "solc_lean_log=$lean_log"
  echo "full_solc_results=$full_results"
  echo "solc_lean_results=$lean_results"
  echo "bridge_json_dir=$BRIDGE_JSON_DIR"
  echo "bridge_json_summary=$bridge_json_summary"
else
  echo "logs_kept=no"
fi
