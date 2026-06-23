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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-aave.XXXXXX")"

AAVE_URL="${AAVE_URL:-https://github.com/aave/aave-v3-core.git}"
AAVE_REF="${AAVE_REF:-b74526a7bc67a3a117a1963fc871b3eb8cea8435}"
AAVE_SOURCE="contracts/protocol/pool/Pool.sol"
AAVE_CONTRACT="Pool"

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

if [[ -n "${AAVE_V3_DIR:-}" ]]; then
  AAVE_REPO="$AAVE_V3_DIR"
else
  AAVE_REPO="$OUTDIR/aave-v3-core"
  checkout_repo "$AAVE_REPO" "$AAVE_URL" "$AAVE_REF"
fi

"$PYTHON_BIN" - \
  "$ROOT" "$AAVE_REPO" "$OUTDIR" "$PYTHON_BIN" "$LAKE_BIN" \
  "$SOLC_826" "$SOLC_835" \
  "$AAVE_SOURCE" "$AAVE_CONTRACT" <<'PY'
import copy
import importlib.util
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
aave_repo = pathlib.Path(sys.argv[2])
outdir = pathlib.Path(sys.argv[3])
python_bin = pathlib.Path(sys.argv[4])
lake_bin = pathlib.Path(sys.argv[5])
solcs = {
    "0.8.26": pathlib.Path(sys.argv[6]),
    "0.8.35": pathlib.Path(sys.argv[7]),
}
source_name = sys.argv[8]
contract_name = sys.argv[9]

bridge_path = root / "scripts" / "solidity_to_yul_lean.py"
spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
bridge = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = bridge
spec.loader.exec_module(bridge)

sys.path.insert(0, str(root / "scripts"))
import raw_bridge_differential

library_addresses = {
    "contracts/protocol/libraries/logic/BorrowLogic.sol:BorrowLogic":
        "0x1111111111111111111111111111111111111111",
    "contracts/protocol/libraries/logic/BridgeLogic.sol:BridgeLogic":
        "0x2222222222222222222222222222222222222222",
    "contracts/protocol/libraries/logic/EModeLogic.sol:EModeLogic":
        "0x3333333333333333333333333333333333333333",
    "contracts/protocol/libraries/logic/FlashLoanLogic.sol:FlashLoanLogic":
        "0x4444444444444444444444444444444444444444",
    "contracts/protocol/libraries/logic/LiquidationLogic.sol:LiquidationLogic":
        "0x5555555555555555555555555555555555555555",
    "contracts/protocol/libraries/logic/PoolLogic.sol:PoolLogic":
        "0x6666666666666666666666666666666666666666",
    "contracts/protocol/libraries/logic/SupplyLogic.sol:SupplyLogic":
        "0x7777777777777777777777777777777777777777",
}

source_path = aave_repo / source_name
source_content = source_path.read_text()
included = bridge.collect_local_import_sources(
    source_name,
    source_content,
    source_path,
    {},
)
include_sources = {
    name: source.content
    for name, source in included.items()
}
if len(include_sources) != 45:
    raise SystemExit(
        f"Aave Pool import closure changed: expected 45 includes, "
        f"got {len(include_sources)}"
    )

libraries = {}
for qualified_name, address in library_addresses.items():
    source, contract = qualified_name.rsplit(":", 1)
    libraries.setdefault(source, {})[contract] = address
linker_symbols = [
    (qualified_name, int(address, 16))
    for qualified_name, address in library_addresses.items()
]

differential_cases = []
for version, solc in solcs.items():
    request = bridge.standard_json_input(
        source_name,
        source_content,
        via_ir=False,
        optimized=True,
        experimental=True,
        include_sources=include_sources,
        require_bytecode=True,
        evm_version="cancun",
    )
    request["settings"]["libraries"] = copy.deepcopy(libraries)
    request_path = outdir / f"aave-pool-{version}.standard-input.json"
    request_path.write_text(json.dumps(request, separators=(",", ":")))
    raw_output = bridge.run_solc(str(solc), request, ())
    contract_output = raw_output["contracts"][source_name][contract_name]
    ast = contract_output.get("irOptimizedAst")
    if not isinstance(ast, dict) or ast.get("nodeType") != "YulObject":
        raise SystemExit(f"solc {version} did not emit a YulObject irOptimizedAst")
    metadata = json.loads(contract_output["metadata"])
    metadata_libraries = metadata.get("settings", {}).get("libraries", {})
    if len(metadata_libraries) != len(library_addresses):
        raise SystemExit(
            f"solc {version} metadata linker count mismatch: "
            f"{len(metadata_libraries)} != {len(library_addresses)}"
        )
    runtime_hex = contract_output["evm"]["deployedBytecode"]["object"]
    creation_hex = contract_output["evm"]["bytecode"]["object"]
    if not runtime_hex or not creation_hex:
        raise SystemExit(f"solc {version} emitted empty Aave bytecode")
    raw_path = outdir / f"aave-pool-{version}.standard-output.json"
    raw_path.write_text(json.dumps(raw_output, separators=(",", ":")))
    for selector in ("runtime", "creation"):
        bridge_json_path = outdir / f"aave-pool-{version}-{selector}.bridge.json"
        subprocess.run(
            [
                str(python_bin),
                str(bridge_path),
                str(request_path),
                "--input-format",
                "standard-json",
                "--solc",
                str(solc),
                "--lake",
                str(lake_bin),
                "--lake-cwd",
                str(root),
                "--source-name",
                source_name,
                "--contract",
                contract_name,
                "--object",
                selector,
                "--optimized",
                "--format",
                "bridge-json",
                "-o",
                str(bridge_json_path),
            ],
            check=True,
        )
        differential_cases.append(
            {
                "label": f"aave-pool-{version}-{selector}",
                "raw": str(raw_path),
                "bridge": str(bridge_json_path),
                "source": source_name,
                "contract": contract_name,
                "selector": selector,
                "compare_artifacts": False,
                "linker_symbols": linker_symbols,
            }
        )
    version_key = version.replace(".", "_")
    print(f"aave_raw_solc_{version_key}_included_sources={len(include_sources)}")
    print(
        f"aave_raw_solc_{version_key}_metadata_linker_count="
        f"{len(metadata_libraries)}"
    )
    print(f"aave_raw_solc_{version_key}_solc_runtime_bytes={len(runtime_hex) // 2}")
    print(f"aave_raw_solc_{version_key}_solc_creation_bytes={len(creation_hex) // 2}")

raw_bridge_differential.write_runner(
    outdir / "aave_raw_bridge_differential_runner.lean",
    differential_cases,
    lean_string=bridge.lean_string,
)
PY

AAVE_DIFFERENTIAL_REPORT="$OUTDIR/aave-raw-bridge-differential.txt"
"$LAKE_BIN" env lean --run "$OUTDIR/aave_raw_bridge_differential_runner.lean" \
  > "$AAVE_DIFFERENTIAL_REPORT"
grep -qx 'raw_solc_frontend_differential_count=4' "$AAVE_DIFFERENTIAL_REPORT"
grep -qx 'raw_solc_frontend_differential=pass' "$AAVE_DIFFERENTIAL_REPORT"
grep -E '^raw_solc_frontend_differential(_count|=)' "$AAVE_DIFFERENTIAL_REPORT"

run_raw_summary() {
  local version="$1"
  local selector="$2"
  local expected_bytes="$3"
  local version_key="${version//./_}"
  local raw_json="$OUTDIR/aave-pool-$version.standard-output.json"
  local report="$OUTDIR/aave-pool-$version-$selector.raw-summary.txt"

  "$LAKE_BIN" exe evm-compiler-backend raw-summary \
    "$raw_json" "$AAVE_SOURCE" "$AAVE_CONTRACT" "$selector" > "$report"

  local bytes
  bytes="$(sed -n 's/^bytecode_bytes=//p' "$report")"
  if [[ "$bytes" != "$expected_bytes" ]]; then
    printf 'Aave %s %s raw byte length mismatch: expected %s, got %s\n' \
      "$version" "$selector" "$expected_bytes" "${bytes:-<missing>}" >&2
    tail -20 "$report" >&2
    exit 1
  fi

  local immutables
  immutables="$(grep -c $'^immutable\t' "$report" || true)"
  if [[ "$immutables" != "14" ]]; then
    printf 'Aave %s %s immutable reference count mismatch: expected 14, got %s\n' \
      "$version" "$selector" "$immutables" >&2
    tail -20 "$report" >&2
    exit 1
  fi

  printf 'aave_raw_solc_%s_%s_bytecode_bytes=%s\n' \
    "$version_key" "$selector" "$bytes"
  printf 'aave_raw_solc_%s_%s_immutable_references=%s\n' \
    "$version_key" "$selector" "$immutables"
}

run_raw_summary "0.8.26" "runtime" "92785"
run_raw_summary "0.8.26" "creation" "93242"
run_raw_summary "0.8.35" "runtime" "92838"
run_raw_summary "0.8.35" "creation" "93295"

printf 'aave_ref=%s\n' "$AAVE_REF"
printf 'raw_solc_aave_corpus=pass\n'
