#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
BUNDLED_PYTHON="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1 && \
    [[ -x "$BUNDLED_PYTHON" ]]; then
  PYTHON_BIN="$BUNDLED_PYTHON"
fi
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_817="${SOLC_817:-$HOME/.solc-select/artifacts/solc-0.8.17/solc-0.8.17}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
SOLC_835="${SOLC_835:-$HOME/.solc-select/artifacts/solc-0.8.35/solc-0.8.35}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-permit2-boundary.XXXXXX")"

PERMIT2_URL="${PERMIT2_URL:-https://github.com/Uniswap/permit2.git}"
PERMIT2_REF="${PERMIT2_REF:-cc56ad0f3439c502c246fc5cfcc3db92bb8b7219}"
PERMIT2_SOURCE="src/Permit2.sol"
PERMIT2_CONTRACT="Permit2"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_817" "$SOLC_826" "$SOLC_835"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

checkout_repo() {
  local destination="$1"
  local url="$2"
  local ref="$3"
  git init -q "$destination"
  git -C "$destination" remote add origin "$url"
  git -C "$destination" fetch --depth 1 origin "$ref"
  git -C "$destination" -c advice.detachedHead=false checkout -q FETCH_HEAD
}

if [[ -n "${PERMIT2_DIR:-}" ]]; then
  PERMIT2_REPO="$PERMIT2_DIR"
else
  PERMIT2_REPO="$OUTDIR/permit2"
  checkout_repo "$PERMIT2_REPO" "$PERMIT2_URL" "$PERMIT2_REF"
fi
git -C "$PERMIT2_REPO" submodule update --init --depth 1 lib/solmate

"$PYTHON_BIN" - \
  "$ROOT" "$PERMIT2_REPO" "$OUTDIR" "$SOLC_817" "$SOLC_826" "$SOLC_835" \
  "$PERMIT2_SOURCE" "$PERMIT2_CONTRACT" <<'PY'
import importlib.util
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
permit2_repo = pathlib.Path(sys.argv[2])
outdir = pathlib.Path(sys.argv[3])
solc_817 = pathlib.Path(sys.argv[4])
solcs = {
    "0.8.26": pathlib.Path(sys.argv[5]),
    "0.8.35": pathlib.Path(sys.argv[6]),
}
source_name = sys.argv[7]
contract_name = sys.argv[8]

bridge_path = root / "scripts" / "solidity_to_yul_lean.py"
spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
bridge = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = bridge
spec.loader.exec_module(bridge)

source_path = permit2_repo / source_name
source_content = source_path.read_text()
pragma_lines = [
    line.strip()
    for line in source_content.splitlines()
    if "pragma solidity" in line
]
if "pragma solidity 0.8.17;" not in pragma_lines:
    raise SystemExit(f"Permit2 pragma changed: {pragma_lines!r}")

remappings = bridge.read_import_remappings(
    [f"solmate/={permit2_repo / 'lib' / 'solmate'}/"],
    [],
)
included = bridge.collect_local_import_sources(
    source_name,
    source_content,
    source_path,
    {},
    remappings,
)
include_sources = {
    name: source.content
    for name, source in included.items()
}
if len(include_sources) != 13:
    raise SystemExit(
        f"Permit2 import closure changed: expected 13 includes, "
        f"got {len(include_sources)}"
    )

request_817 = bridge.standard_json_input(
    source_name,
    source_content,
    via_ir=True,
    optimized=True,
    experimental=False,
    include_sources=include_sources,
    require_bytecode=True,
    evm_version="london",
)
completed_817 = subprocess.run(
    [str(solc_817), "--standard-json"],
    input=json.dumps(request_817),
    text=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    check=False,
)
try:
    output_817 = json.loads(completed_817.stdout)
except json.JSONDecodeError as exc:
    raise SystemExit(f"solc 0.8.17 returned non-JSON output: {exc}") from exc
errors_817 = [
    err for err in output_817.get("errors", [])
    if err.get("severity") == "error"
]
if errors_817:
    raise SystemExit(f"solc 0.8.17 unexpectedly rejected Permit2: {errors_817!r}")
contract_output_817 = (
    output_817.get("contracts", {})
    .get(source_name, {})
    .get(contract_name, {})
)
if not contract_output_817:
    raise SystemExit("solc 0.8.17 did not emit Permit2 contract output")
if contract_output_817.get("irOptimizedAst") is not None:
    raise SystemExit("solc 0.8.17 unexpectedly emitted irOptimizedAst")
if not contract_output_817.get("irOptimized"):
    raise SystemExit("solc 0.8.17 did not emit optimized Yul text")
metadata = contract_output_817.get("metadata")
if not metadata:
    raise SystemExit("solc 0.8.17 did not emit metadata")
metadata_json = json.loads(metadata)
if metadata_json.get("settings", {}).get("evmVersion") != "london":
    raise SystemExit("solc 0.8.17 metadata did not preserve evmVersion=london")
evm = contract_output_817.get("evm") or {}
bytecode = ((evm.get("bytecode") or {}).get("object") or "")
deployed = ((evm.get("deployedBytecode") or {}).get("object") or "")
if len(bytecode) == 0 or len(bytecode) % 2 != 0:
    raise SystemExit("solc 0.8.17 emitted invalid creation bytecode")
if len(deployed) == 0 or len(deployed) % 2 != 0:
    raise SystemExit("solc 0.8.17 emitted invalid runtime bytecode")
(outdir / "permit2-0.8.17.standard-output.json").write_text(
    json.dumps(output_817, separators=(",", ":"))
)
print(f"permit2_raw_solc_0_8_17_included_sources={len(include_sources)}")
print(f"permit2_raw_solc_0_8_17_creation_bytecode_bytes={len(bytecode) // 2}")
print(f"permit2_raw_solc_0_8_17_runtime_bytecode_bytes={len(deployed) // 2}")
print("permit2_raw_solc_0_8_17_ir_optimized_ast=absent")
print("permit2_raw_solc_0_8_17_evm_version=london")

for version, solc in solcs.items():
    # solc 0.8.26 rejects unknown `settings.experimental`; solc 0.8.35
    # requires it before accepting irOptimizedAst in outputSelection. Both
    # requests then prove the same source-level boundary: exact pragma 0.8.17
    # does not produce a raw AST for the supported production pins.
    request = bridge.standard_json_input(
        source_name,
        source_content,
        via_ir=True,
        optimized=True,
        experimental=(version == "0.8.35"),
        include_sources=include_sources,
        require_bytecode=True,
        evm_version="cancun",
    )
    completed = subprocess.run(
        [str(solc), "--standard-json"],
        input=json.dumps(request),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    try:
        output = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"solc {version} returned non-JSON output: {exc}") from exc
    errors = output.get("errors", [])
    if output.get("contracts"):
        raise SystemExit(f"solc {version} unexpectedly emitted Permit2 contracts")
    messages = "\n".join(
        err.get("message") or ""
        for err in errors
        if err.get("severity") == "error"
    )
    if "requires different compiler version" not in messages:
        raise SystemExit(
            f"solc {version} did not reject Permit2 by exact pragma: {errors!r}"
        )
    raw_path = outdir / f"permit2-{version}.standard-output.json"
    raw_path.write_text(json.dumps(output, separators=(",", ":")))
    version_key = version.replace(".", "_")
    print(f"permit2_raw_solc_{version_key}_included_sources={len(include_sources)}")
    print(f"permit2_raw_solc_{version_key}_exact_pragma_rejection=pass")
PY

for version in 0.8.17 0.8.26 0.8.35; do
  version_key="${version//./_}"
  report="$OUTDIR/permit2-$version.raw-check.txt"
  if "$LAKE_BIN" exe evm-compiler-backend raw-check \
      "$OUTDIR/permit2-$version.standard-output.json" \
      "$PERMIT2_SOURCE" "$PERMIT2_CONTRACT" runtime > "$report" 2>&1; then
    printf 'Permit2 solc %s rejection JSON unexpectedly decoded\n' "$version" >&2
    cat "$report" >&2
    exit 1
  fi
  grep -qx 'raw Standard JSON decode failed' "$report"
  grep -Eq '^timing	object_image	[0-9]+	bytes=0$' "$report"
  printf 'permit2_raw_solc_%s_raw_check_fail_closed=pass\n' "$version_key"
done

printf 'permit2_ref=%s\n' "$PERMIT2_REF"
printf 'raw_solc_permit2_version_boundary=pass\n'
