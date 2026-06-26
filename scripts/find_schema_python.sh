#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
candidates=()
if [[ -n "${PYTHON:-}" ]]; then
  candidates+=("$PYTHON")
fi
candidates+=("$ROOT/.venv/bin/python" python3)

for candidate in "${candidates[@]}"; do
  if "$candidate" -c 'import jsonschema' >/dev/null 2>&1; then
    if [[ "$candidate" == */* ]]; then
      printf '%s\n' "$candidate"
    else
      command -v "$candidate"
    fi
    exit 0
  fi
done

printf 'error: no Python interpreter with jsonschema is available\n' >&2
printf 'run "uv sync --locked" from %s\n' "$ROOT" >&2
exit 1
