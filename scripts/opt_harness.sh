#!/usr/bin/env bash
# Optimization harness dispatcher for the verified EVM compiler.
#
# Thin wrapper around scripts/opt_harness.py: pins the solc/lake tools the way
# the repo's other scripts do and forwards the subcommand.
#
#   scripts/opt_harness.sh baseline                 record corpus sizes
#   scripts/opt_harness.sh bench [--fail-on-regression]
#   scripts/opt_harness.sh check                     correctness + axiom gate
#   scripts/opt_harness.sh full  [--fail-on-regression]   check then bench
#
# Exit codes: 0 pass; 2 usage; 10 build-fail; 11 axiom-fail;
#             20 compile-fail; 30 gas-regression;
#             40 EIP-170/EIP-3860 cap (only with --enforce-caps; report-only by default).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Match the tool discovery used by scripts/test_all.sh and the solc drivers.
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$HOME/.foundry/bin:$PATH"
export SOLC="${SOLC:-$HOME/.local/bin/solc}"
export LAKE="${LAKE:-$(command -v lake || echo lake)}"
export FORGE="${FORGE:-$HOME/.foundry/bin/forge}"

# Prefer a real CPython over any hanging sandbox venv shim.
PYTHON_BIN="${PYTHON:-python3}"

exec "$PYTHON_BIN" "$ROOT/scripts/opt_harness.py" "$@"
