#!/usr/bin/env bash
# Regression for the previously untested EIP-170 / EIP-3860 refuse-to-emit
# path. Caps are lowered via EVM_COMPILER_EIP170_CAP / EVM_COMPILER_EIP3860_CAP
# so a tiny library exercises the real CLI guard without needing a >24KB
# corpus object.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-eip-size-cap.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

RAW_JSON="$OUTDIR/MathLib.raw.json"

"$PYTHON_BIN" - "$ROOT" "$SOLC_BIN" "$RAW_JSON" <<'PY'
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
solc = sys.argv[2]
out = pathlib.Path(sys.argv[3])
source_name = "MathLib.sol"
content = (root / "examples" / source_name).read_text()
standard_input = {
    "language": "Solidity",
    "sources": {source_name: {"content": content}},
    "settings": {
        "viaIR": True,
        "optimizer": {"enabled": True, "details": {"yul": True}},
        "outputSelection": {
            "*": {
                "*": [
                    "irOptimizedAst",
                    "metadata",
                    "evm.bytecode.object",
                    "evm.deployedBytecode.object",
                ]
            }
        },
    },
}
proc = subprocess.run(
    [solc, "--standard-json"],
    input=json.dumps(standard_input),
    capture_output=True,
    text=True,
    check=True,
)
payload = json.loads(proc.stdout)
errors = [e for e in payload.get("errors", []) if e.get("severity") == "error"]
if errors:
    raise SystemExit(errors)
out.write_text(json.dumps(payload))
print(f"wrote {out}")
PY

run_raw_image() {
  local selector="$1"
  shift
  env "$@" "$LAKE_BIN" exe solidus-backend raw-image \
    "$RAW_JSON" MathLib.sol MathLib "$selector"
}

# 1) Refuse runtime emit when EIP-170 cap is below the compiled size.
set +e
run_raw_image runtime EVM_COMPILER_EIP170_CAP=1 \
  >"$OUTDIR/runtime.refuse.stdout" 2>"$OUTDIR/runtime.refuse.stderr"
refuse_rc=$?
set -e
if [[ "$refuse_rc" == "0" ]]; then
  printf 'error: expected EIP-170 refusal, but raw-image succeeded\n' >&2
  cat "$OUTDIR/runtime.refuse.stdout" "$OUTDIR/runtime.refuse.stderr" >&2
  exit 1
fi
refuse_msg="$(cat "$OUTDIR/runtime.refuse.stderr" "$OUTDIR/runtime.refuse.stdout")"
if ! grep -q 'exceeding the EIP-170 cap' <<<"$refuse_msg"; then
  printf 'error: refusal did not cite EIP-170:\n%s\n' "$refuse_msg" >&2
  exit 1
fi
printf 'eip170_refusal=pass\n'

# 2) ALLOW_OVERSIZE=1 must warn and still emit.
set +e
run_raw_image runtime EVM_COMPILER_EIP170_CAP=1 EVM_COMPILER_ALLOW_OVERSIZE=1 \
  >"$OUTDIR/runtime.allow.stdout" 2>"$OUTDIR/runtime.allow.stderr"
allow_rc=$?
set -e
if [[ "$allow_rc" != "0" ]]; then
  printf 'error: ALLOW_OVERSIZE=1 should emit despite lowered EIP-170 cap\n' >&2
  cat "$OUTDIR/runtime.allow.stdout" "$OUTDIR/runtime.allow.stderr" >&2
  exit 1
fi
allow_err="$(cat "$OUTDIR/runtime.allow.stderr")"
if ! grep -q 'warning:.*EIP-170' <<<"$allow_err"; then
  printf 'error: expected EIP-170 oversize warning on stderr:\n%s\n' "$allow_err" >&2
  exit 1
fi
if ! grep -q '^bytecode=0x' "$OUTDIR/runtime.allow.stdout"; then
  printf 'error: ALLOW_OVERSIZE path did not emit bytecode\n' >&2
  cat "$OUTDIR/runtime.allow.stdout" >&2
  exit 1
fi
printf 'eip170_allow_oversize=pass\n'

# 3) Creation / EIP-3860 refusal with lowered initcode cap.
set +e
run_raw_image creation EVM_COMPILER_EIP3860_CAP=1 \
  >"$OUTDIR/creation.refuse.stdout" 2>"$OUTDIR/creation.refuse.stderr"
create_rc=$?
set -e
if [[ "$create_rc" == "0" ]]; then
  printf 'error: expected EIP-3860 refusal, but raw-image succeeded\n' >&2
  cat "$OUTDIR/creation.refuse.stdout" "$OUTDIR/creation.refuse.stderr" >&2
  exit 1
fi
create_msg="$(cat "$OUTDIR/creation.refuse.stderr" "$OUTDIR/creation.refuse.stdout")"
if ! grep -q 'exceeding the EIP-3860 cap' <<<"$create_msg"; then
  printf 'error: refusal did not cite EIP-3860:\n%s\n' "$create_msg" >&2
  exit 1
fi
printf 'eip3860_refusal=pass\n'

printf 'eip_size_cap_refusal=pass\n'
