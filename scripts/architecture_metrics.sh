#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

output="proof_artifacts/architecture_baseline.json"
cache_label="unspecified"
build_modules=()

usage() {
  cat <<'EOF'
Usage: scripts/architecture_metrics.sh [options]

Options:
  --output PATH        Write metrics to PATH.
  --build MODULE       Measure `lake build MODULE`; may be repeated.
  --cache-label LABEL  Describe the build-cache state recorded in measurements.
  --help               Show this help.
EOF
}

while (($# > 0)); do
  case "$1" in
    --output)
      output="$2"
      shift 2
      ;;
    --build)
      build_modules+=("$2")
      shift 2
      ;;
    --cache-label)
      cache_label="$2"
      shift 2
      ;;
    --help)
      usage
      exit 0
      ;;
    *)
      printf 'unknown option: %s\n' "$1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

command -v jq >/dev/null || {
  printf 'architecture metrics require jq\n' >&2
  exit 1
}

count_matches() {
  local pattern="$1"
  shift
  local count
  count="$(rg -n "$pattern" "$@" 2>/dev/null | wc -l | tr -d ' ')"
  printf '%s' "$count"
}

modules_json='[]'
while IFS= read -r -d '' file; do
  lines="$(wc -l < "$file" | tr -d ' ')"
  imports="$(rg -c '^import ' "$file" 2>/dev/null || true)"
  declarations="$(
    rg -c \
      '^(noncomputable )?(def|abbrev|structure|inductive|theorem|lemma|class|instance) ' \
      "$file" 2>/dev/null || true
  )"
  imports="${imports:-0}"
  declarations="${declarations:-0}"
  module="${file%.lean}"
  module="${module//\//.}"
  modules_json="$(
    jq -c \
      --arg path "$file" \
      --arg module "$module" \
      --argjson lines "$lines" \
      --argjson imports "$imports" \
      --argjson declarations "$declarations" \
      '. + [{
        path: $path,
        module: $module,
        source_lines: $lines,
        direct_imports: $imports,
        declarations: $declarations
      }]' <<<"$modules_json"
  )"
done < <(find EvmCompiler -type f -name '*.lean' -print0 | sort -z)

measurements_json='[]'
if ((${#build_modules[@]} > 0)); then
  for module in "${build_modules[@]}"; do
    time_file="$(mktemp)"
    log_file="$(mktemp)"
    started_at="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    set +e
    /usr/bin/time -l -o "$time_file" lake build "$module" >"$log_file" 2>&1
    status=$?
    set -e
    real_seconds="$(awk '$2 == "real" { print $1; exit }' "$time_file")"
    peak_rss_bytes="$(
      awk '/maximum resident set size/ { print $1; exit }' "$time_file"
    )"
    real_seconds="${real_seconds:-null}"
    peak_rss_bytes="${peak_rss_bytes:-null}"
    measurements_json="$(
      jq -c \
        --arg module "$module" \
        --arg started_at "$started_at" \
        --arg cache_label "$cache_label" \
        --argjson exit_status "$status" \
        --argjson real_seconds "$real_seconds" \
        --argjson peak_rss_bytes "$peak_rss_bytes" \
        '. + [{
          module: $module,
          started_at: $started_at,
          cache_state: $cache_label,
          exit_status: $exit_status,
          real_seconds: $real_seconds,
          peak_rss_bytes: $peak_rss_bytes
        }]' <<<"$measurements_json"
    )"
    if ((status != 0)); then
      printf 'build failed for %s; output follows\n' "$module" >&2
      sed -n '1,200p' "$log_file" >&2
      rm -f "$time_file" "$log_file"
      exit "$status"
    fi
    rm -f "$time_file" "$log_file"
  done
fi

compiler_variant_count="$(
  count_matches \
    '^(noncomputable )?def [A-Za-z0-9_]*(compile|Compile)[A-Za-z0-9_?]* ' \
    EvmCompiler -g '*.lean'
)"
outcome_relation_count="$(
  count_matches \
    '^(def|abbrev|structure|inductive) [A-Za-z0-9_]*OutcomeRel' \
    EvmCompiler -g '*.lean'
)"
layer_audit_abbrev_count="$(
  count_matches '^abbrev ' EvmCompiler/LayerAudit.lean
)"
layer_audit_example_count="$(
  count_matches '^example ' EvmCompiler/LayerAudit.lean
)"

mkdir -p "$(dirname "$output")"
tmp_output="$(mktemp)"
jq -n \
  --arg generated_at "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" \
  --arg git_commit "$(git rev-parse HEAD)" \
  --arg git_branch "$(git branch --show-current)" \
  --argjson modules "$modules_json" \
  --argjson measurements "$measurements_json" \
  --argjson compiler_variant_count "$compiler_variant_count" \
  --argjson outcome_relation_count "$outcome_relation_count" \
  --argjson layer_audit_abbrev_count "$layer_audit_abbrev_count" \
  --argjson layer_audit_example_count "$layer_audit_example_count" \
  '{
    schema_version: 1,
    generated_at: $generated_at,
    git: {
      commit: $git_commit,
      branch: $git_branch
    },
    totals: {
      module_count: ($modules | length),
      source_lines: ($modules | map(.source_lines) | add),
      direct_imports: ($modules | map(.direct_imports) | add),
      declarations: ($modules | map(.declarations) | add),
      compiler_variant_declarations: $compiler_variant_count,
      outcome_relation_declarations: $outcome_relation_count,
      layer_audit_abbrevs: $layer_audit_abbrev_count,
      layer_audit_examples: $layer_audit_example_count
    },
    modules: $modules,
    build_measurements: $measurements
  }' >"$tmp_output"
mv "$tmp_output" "$output"

printf 'wrote %s\n' "$output"
