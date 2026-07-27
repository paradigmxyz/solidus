#!/usr/bin/env bash
# Bridge CLI must apply the same deployability guards as raw-image:
# a creation bridge whose setimmutable/loadimmutable names diverge must be
# rejected (previously only the raw path enforced this).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-bridge-deployability.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

SOURCE="$ROOT/examples/ImmutableBox.sol"
CREATION_BRIDGE="$OUTDIR/ImmutableBox.creation.bridge.json"
RUNTIME_BRIDGE="$OUTDIR/ImmutableBox.runtime.bridge.json"
CREATION_IMAGE="$OUTDIR/ImmutableBox.creation.image.txt"
RUNTIME_IMAGE="$OUTDIR/ImmutableBox.runtime.image.txt"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --contract ImmutableBox \
  --object creation \
  --optimized \
  --format bridge-json \
  --output "$CREATION_BRIDGE"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --contract ImmutableBox \
  --object runtime \
  --optimized \
  --format bridge-json \
  --output "$RUNTIME_BRIDGE"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$CREATION_BRIDGE"
"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$RUNTIME_BRIDGE"

# Happy path: bridge image emits for both selectors.
"$LAKE_BIN" exe solidus-backend image "$CREATION_BRIDGE" > "$CREATION_IMAGE"
"$LAKE_BIN" exe solidus-backend image "$RUNTIME_BRIDGE" > "$RUNTIME_IMAGE"
grep -q '^bytecode=0x' "$CREATION_IMAGE"
grep -q '^bytecode=0x' "$RUNTIME_IMAGE"
printf 'bridge_deployability_happy=pass\n'

# Fail-closed: mangle setimmutable name on the creation bridge JSON.
# Bridge v3 encodes calls as {"node":"call","calleeKind":"objectBuiltin",
# "callee":"setimmutable","args":[offset, {"node":"stringLiteral","value":…}, …]}.
"$PYTHON_BIN" - "$CREATION_BRIDGE" "$OUTDIR/ImmutableBox.typo.bridge.json" <<'PY'
import json
import sys
from pathlib import Path

src = Path(sys.argv[1])
dst = Path(sys.argv[2])
data = json.loads(src.read_text())
count = 0

def mangle(node):
    global count
    if isinstance(node, dict):
        if (
            node.get("node") == "call"
            and node.get("calleeKind") == "objectBuiltin"
            and node.get("callee") == "setimmutable"
        ):
            args = node.get("args") or []
            if len(args) >= 2 and args[1].get("node") == "stringLiteral":
                args[1]["value"] = str(args[1]["value"]) + "_typo"
                count += 1
        for value in node.values():
            mangle(value)
    elif isinstance(node, list):
        for value in node:
            mangle(value)

mangle(data)
if count == 0:
    raise SystemExit("FAIL: found no setimmutable site to mangle in bridge JSON")
dst.write_text(json.dumps(data))
print(f"mangled_setimmutable_sites={count}")
PY

if "$LAKE_BIN" exe solidus-backend image \
    "$OUTDIR/ImmutableBox.typo.bridge.json" \
    >"$OUTDIR/typo.stdout" 2>"$OUTDIR/typo.stderr"; then
  printf 'error: mangled creation bridge was ACCEPTED by bridge image\n' >&2
  cat "$OUTDIR/typo.stdout" "$OUTDIR/typo.stderr" >&2
  exit 1
fi

message="$(cat "$OUTDIR/typo.stderr" "$OUTDIR/typo.stdout" 2>/dev/null || true)"
if ! grep -q 'no setimmutable site ever writes' <<<"$message"; then
  printf 'error: mangled bridge rejected, but not by immutable-coverage guard:\n%s\n' \
    "$message" >&2
  exit 1
fi

printf 'bridge_deployability_immutable_guard=pass\n'
printf 'bridge_deployability_guards=pass\n'
