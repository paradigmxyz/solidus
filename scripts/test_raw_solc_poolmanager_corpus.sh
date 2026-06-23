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
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
SOLC_835="${SOLC_835:-$HOME/.solc-select/artifacts/solc-0.8.35/solc-0.8.35}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-poolmanager.XXXXXX")"

UNISWAP_V4_URL="${UNISWAP_V4_URL:-https://github.com/Uniswap/v4-core.git}"
UNISWAP_V4_REF="${UNISWAP_V4_REF:-46c6834698c48bc4a463a86d8420f4eb1d7f3b75}"
POOLMANAGER_SOURCE="src/PoolManager.sol"
POOLMANAGER_CONTRACT="PoolManager"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_826" "$SOLC_835"; do
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

if [[ -n "${UNISWAP_V4_DIR:-}" ]]; then
  UNISWAP_V4_REPO="$UNISWAP_V4_DIR"
else
  UNISWAP_V4_REPO="$OUTDIR/v4-core"
  checkout_repo "$UNISWAP_V4_REPO" "$UNISWAP_V4_URL" "$UNISWAP_V4_REF"
fi
git -C "$UNISWAP_V4_REPO" submodule update --init --depth 1 lib/solmate

"$PYTHON_BIN" - \
  "$ROOT" "$UNISWAP_V4_REPO" "$OUTDIR" "$SOLC_826" "$SOLC_835" \
  "$POOLMANAGER_SOURCE" "$POOLMANAGER_CONTRACT" <<'PY'
import copy
import importlib.util
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
repo = pathlib.Path(sys.argv[2])
outdir = pathlib.Path(sys.argv[3])
solc_826 = pathlib.Path(sys.argv[4])
solc_835 = pathlib.Path(sys.argv[5])
source_name = sys.argv[6]
contract_name = sys.argv[7]

bridge_path = root / "scripts" / "solidity_to_yul_lean.py"
spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
bridge = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = bridge
spec.loader.exec_module(bridge)

source_path = repo / source_name
source_content = source_path.read_text()
remappings = bridge.read_import_remappings([], [repo / "remappings.txt"])
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
if len(include_sources) != 44:
    raise SystemExit(
        f"PoolManager import closure changed: expected 44 includes, "
        f"got {len(include_sources)}"
    )

def standard_request():
    return bridge.standard_json_input(
        source_name,
        source_content,
        via_ir=True,
        optimized=True,
        experimental=True,
        include_sources=include_sources,
        require_bytecode=True,
        evm_version="cancun",
    )

raw_output = bridge.run_solc(str(solc_826), standard_request(), ())
contract_output = raw_output["contracts"][source_name][contract_name]
ast = contract_output.get("irOptimizedAst")
if not isinstance(ast, dict) or ast.get("nodeType") != "YulObject":
    raise SystemExit("solc 0.8.26 did not emit a YulObject irOptimizedAst")
metadata = json.loads(contract_output["metadata"])
metadata_libraries = metadata.get("settings", {}).get("libraries", {})
if metadata_libraries:
    raise SystemExit(
        f"PoolManager unexpectedly emitted linker metadata: {metadata_libraries!r}"
    )
runtime_hex = contract_output["evm"]["deployedBytecode"]["object"]
creation_hex = contract_output["evm"]["bytecode"]["object"]
if len(runtime_hex) // 2 != 17151 or len(creation_hex) // 2 != 17336:
    raise SystemExit("PoolManager solc byte sizes changed")
(outdir / "poolmanager-0.8.26.standard-output.json").write_text(
    json.dumps(raw_output, separators=(",", ":"))
)

try:
    bridge.run_solc(str(solc_835), copy.deepcopy(standard_request()), ())
except bridge.ConversionError as exc:
    if "requires different compiler version" not in str(exc):
        raise
else:
    raise SystemExit("solc 0.8.35 unexpectedly accepted exact pragma 0.8.26")

print(f"poolmanager_raw_solc_0_8_26_included_sources={len(include_sources)}")
print("poolmanager_raw_solc_0_8_26_metadata_linker_count=0")
print(f"poolmanager_raw_solc_0_8_26_solc_runtime_bytes={len(runtime_hex) // 2}")
print(f"poolmanager_raw_solc_0_8_26_solc_creation_bytes={len(creation_hex) // 2}")
print("poolmanager_raw_solc_0_8_35_exact_pragma_rejection=pass")
PY

run_raw_summary() {
  local selector="$1"
  local expected_bytes="$2"
  local raw_json="$OUTDIR/poolmanager-0.8.26.standard-output.json"
  local report="$OUTDIR/poolmanager-0.8.26-$selector.raw-summary.txt"

  "$LAKE_BIN" exe evm-compiler-backend raw-summary \
    "$raw_json" "$POOLMANAGER_SOURCE" "$POOLMANAGER_CONTRACT" "$selector" \
    > "$report"

  local bytes
  bytes="$(sed -n 's/^bytecode_bytes=//p' "$report")"
  if [[ "$bytes" != "$expected_bytes" ]]; then
    printf 'PoolManager %s raw byte length mismatch: expected %s, got %s\n' \
      "$selector" "$expected_bytes" "${bytes:-<missing>}" >&2
    tail -20 "$report" >&2
    exit 1
  fi

  local immutables
  immutables="$(grep -c $'^immutable\t' "$report" || true)"
  if [[ "$immutables" != "1" ]]; then
    printf 'PoolManager %s immutable reference count mismatch: expected 1, got %s\n' \
      "$selector" "$immutables" >&2
    tail -20 "$report" >&2
    exit 1
  fi

  printf 'poolmanager_raw_solc_0_8_26_%s_bytecode_bytes=%s\n' \
    "$selector" "$bytes"
  printf 'poolmanager_raw_solc_0_8_26_%s_immutable_references=%s\n' \
    "$selector" "$immutables"
}

run_raw_summary "runtime" "114118"
run_raw_summary "creation" "114434"

printf 'uniswap_v4_ref=%s\n' "$UNISWAP_V4_REF"
printf 'raw_solc_poolmanager_corpus=pass\n'
