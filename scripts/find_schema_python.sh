#!/usr/bin/env bash
set -euo pipefail

candidate="${PYTHON:-python3}"
bundled="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"

if "$candidate" -c 'import jsonschema' >/dev/null 2>&1; then
  if [[ "$candidate" == */* ]]; then
    printf '%s\n' "$candidate"
  else
    command -v "$candidate"
  fi
elif [[ -x "$bundled" ]] && "$bundled" -c 'import jsonschema' >/dev/null 2>&1; then
  printf '%s\n' "$bundled"
else
  printf 'error: no Python interpreter with jsonschema is available\n' >&2
  exit 1
fi
