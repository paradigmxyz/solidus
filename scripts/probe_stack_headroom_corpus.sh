#!/usr/bin/env bash
# Probe Assembly.StackHeadroom.mkCert? (VerifiedStackObjectArtifact
# .stackHeadroomCert?) on the large real-world raw-solc corpora.
# See scripts/probe_stack_headroom_corpus.py for corpus definitions and
# options; all arguments are forwarded.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# The probe needs only the Python standard library (no jsonschema), so a
# plain python3 suffices; override with PYTHON=... if desired.
PYTHON_BIN="${PYTHON:-python3}"

exec "$PYTHON_BIN" "$ROOT/scripts/probe_stack_headroom_corpus.py" "$@"
