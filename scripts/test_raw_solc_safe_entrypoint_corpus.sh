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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-safe-entrypoint.XXXXXX")"

SAFE_SMART_ACCOUNT_URL="${SAFE_SMART_ACCOUNT_URL:-https://github.com/safe-global/safe-smart-account.git}"
SAFE_SMART_ACCOUNT_REF="${SAFE_SMART_ACCOUNT_REF:-bf943f80fec5ac647159d26161446ac5d716a294}"
ACCOUNT_ABSTRACTION_URL="${ACCOUNT_ABSTRACTION_URL:-https://github.com/eth-infinitism/account-abstraction.git}"
ACCOUNT_ABSTRACTION_REF="${ACCOUNT_ABSTRACTION_REF:-7af70c8993a6f42973f520ae0752386a5032abe7}"
OPENZEPPELIN_URL="${OPENZEPPELIN_URL:-https://github.com/OpenZeppelin/openzeppelin-contracts.git}"
OPENZEPPELIN_REF="${OPENZEPPELIN_REF:-932fddf69a699a9a80fd2396fd1a2ab91cdda123}"

SAFE_SOURCE="contracts/Safe.sol"
SAFE_CONTRACT="Safe"
ENTRYPOINT_SOURCE="contracts/core/EntryPoint.sol"
ENTRYPOINT_CONTRACT="EntryPoint"

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

if [[ -n "${SAFE_SMART_ACCOUNT_DIR:-}" ]]; then
  SAFE_SMART_ACCOUNT_REPO="$SAFE_SMART_ACCOUNT_DIR"
else
  SAFE_SMART_ACCOUNT_REPO="$OUTDIR/safe-smart-account"
  checkout_repo "$SAFE_SMART_ACCOUNT_REPO" \
    "$SAFE_SMART_ACCOUNT_URL" "$SAFE_SMART_ACCOUNT_REF"
fi

if [[ -n "${ACCOUNT_ABSTRACTION_DIR:-}" ]]; then
  ACCOUNT_ABSTRACTION_REPO="$ACCOUNT_ABSTRACTION_DIR"
else
  ACCOUNT_ABSTRACTION_REPO="$OUTDIR/account-abstraction"
  checkout_repo "$ACCOUNT_ABSTRACTION_REPO" \
    "$ACCOUNT_ABSTRACTION_URL" "$ACCOUNT_ABSTRACTION_REF"
fi

if [[ -n "${OPENZEPPELIN_DIR:-}" ]]; then
  OPENZEPPELIN_REPO="$OPENZEPPELIN_DIR"
else
  OPENZEPPELIN_REPO="$OUTDIR/openzeppelin-contracts"
  checkout_repo "$OPENZEPPELIN_REPO" "$OPENZEPPELIN_URL" "$OPENZEPPELIN_REF"
fi

"$PYTHON_BIN" - \
  "$ROOT" "$SAFE_SMART_ACCOUNT_REPO" "$ACCOUNT_ABSTRACTION_REPO" \
  "$OPENZEPPELIN_REPO" "$OUTDIR" "$PYTHON_BIN" "$LAKE_BIN" \
  "$SOLC_826" "$SOLC_835" \
  "$SAFE_SOURCE" "$SAFE_CONTRACT" "$ENTRYPOINT_SOURCE" "$ENTRYPOINT_CONTRACT" \
  <<'PY'
import copy
import importlib.util
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
safe_repo = pathlib.Path(sys.argv[2])
entrypoint_repo = pathlib.Path(sys.argv[3])
openzeppelin_repo = pathlib.Path(sys.argv[4])
outdir = pathlib.Path(sys.argv[5])
python_bin = pathlib.Path(sys.argv[6])
lake_bin = pathlib.Path(sys.argv[7])
solcs = {
    "0.8.26": pathlib.Path(sys.argv[8]),
    "0.8.35": pathlib.Path(sys.argv[9]),
}
safe_source = sys.argv[10]
safe_contract = sys.argv[11]
entrypoint_source = sys.argv[12]
entrypoint_contract = sys.argv[13]

bridge_path = root / "scripts" / "solidity_to_yul_lean.py"
spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
bridge = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = bridge
spec.loader.exec_module(bridge)

sys.path.insert(0, str(root / "scripts"))
import raw_bridge_differential

def source_closure(repo, source_name, remapping_values=()):
    source_path = repo / source_name
    source_content = source_path.read_text()
    remappings = bridge.read_import_remappings(remapping_values, [])
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
    return source_content, include_sources

safe_content, safe_includes = source_closure(safe_repo, safe_source)
if len(safe_includes) != 15:
    raise SystemExit(
        f"Safe import closure changed: expected 15 includes, got {len(safe_includes)}"
    )

openzeppelin_remapping = (
    f"@openzeppelin/contracts/={openzeppelin_repo / 'contracts'}/",
)
entrypoint_content, entrypoint_includes = source_closure(
    entrypoint_repo,
    entrypoint_source,
    openzeppelin_remapping,
)
if len(entrypoint_includes) != 17:
    raise SystemExit(
        "EntryPoint import closure changed: expected 17 includes, "
        f"got {len(entrypoint_includes)}"
    )

def ensure_metadata_output(request):
    outputs = request["settings"]["outputSelection"]["*"]["*"]
    if "metadata" not in outputs:
        outputs.append("metadata")

def metadata_linker_count(contract_output):
    metadata = json.loads(contract_output["metadata"])
    settings = metadata.get("settings", {})
    if settings.get("evmVersion") != "cancun":
        raise SystemExit(f"unexpected evmVersion metadata: {settings!r}")
    return len(settings.get("libraries", {}))

def assert_yul_object(contract_output, label):
    ast = contract_output.get("irOptimizedAst")
    if not isinstance(ast, dict) or ast.get("nodeType") != "YulObject":
        raise SystemExit(f"{label} did not emit a YulObject irOptimizedAst")

def safe_request(require_bytecode):
    request = bridge.standard_json_input(
        safe_source,
        safe_content,
        via_ir=True,
        optimized=True,
        experimental=True,
        include_sources=safe_includes,
        require_bytecode=require_bytecode,
        evm_version="cancun",
    )
    ensure_metadata_output(request)
    return request

def entrypoint_request():
    return bridge.standard_json_input(
        entrypoint_source,
        entrypoint_content,
        via_ir=True,
        optimized=True,
        experimental=True,
        include_sources=entrypoint_includes,
        require_bytecode=True,
        evm_version="cancun",
    )

entrypoint_solc_sizes = {
    "0.8.26": (11962, 12444),
    "0.8.35": (11976, 12472),
}

differential_cases = []
for version, solc in solcs.items():
    try:
        bridge.run_solc(str(solc), copy.deepcopy(safe_request(True)), ())
    except bridge.ConversionError as exc:
        message = str(exc)
        if "too deep in the stack" not in message and "YulException" not in message:
            raise
    else:
        raise SystemExit(f"Safe solc {version} unexpectedly emitted bytecode")

    safe_raw_request = safe_request(False)
    safe_request_path = outdir / f"safe-{version}.standard-input.json"
    safe_request_path.write_text(json.dumps(safe_raw_request, separators=(",", ":")))
    raw_safe = bridge.run_solc(str(solc), copy.deepcopy(safe_raw_request), ())
    safe_output = raw_safe["contracts"][safe_source][safe_contract]
    assert_yul_object(safe_output, f"Safe solc {version}")
    safe_linkers = metadata_linker_count(safe_output)
    if safe_linkers != 0:
        raise SystemExit(f"Safe linker metadata changed: {safe_linkers}")
    (outdir / f"safe-{version}.standard-output.json").write_text(
        json.dumps(raw_safe, separators=(",", ":"))
    )
    for selector in ("runtime", "creation"):
        bridge_json_path = outdir / f"safe-{version}-{selector}.bridge.json"
        subprocess.run(
            [
                str(python_bin),
                str(bridge_path),
                str(safe_request_path),
                "--input-format",
                "standard-json",
                "--solc",
                str(solc),
                "--lake",
                str(lake_bin),
                "--lake-cwd",
                str(root),
                "--source-name",
                safe_source,
                "--contract",
                safe_contract,
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
                "label": f"safe-{version}-{selector}",
                "raw": str(outdir / f"safe-{version}.standard-output.json"),
                "bridge": str(bridge_json_path),
                "source": safe_source,
                "contract": safe_contract,
                "selector": selector,
                "compare_artifacts": False,
                "linker_symbols": [],
            }
        )
    version_key = version.replace(".", "_")
    print(f"safe_raw_solc_{version_key}_included_sources={len(safe_includes)}")
    print(f"safe_raw_solc_{version_key}_metadata_linker_count={safe_linkers}")
    print(f"safe_raw_solc_{version_key}_solc_bytecode_rejection=stack_too_deep")

    entrypoint_raw_request = entrypoint_request()
    entrypoint_request_path = outdir / f"entrypoint-{version}.standard-input.json"
    entrypoint_request_path.write_text(
        json.dumps(entrypoint_raw_request, separators=(",", ":"))
    )
    raw_entrypoint = bridge.run_solc(
        str(solc),
        copy.deepcopy(entrypoint_raw_request),
        (),
    )
    entrypoint_output = raw_entrypoint["contracts"][entrypoint_source][
        entrypoint_contract
    ]
    assert_yul_object(entrypoint_output, f"EntryPoint solc {version}")
    entrypoint_linkers = metadata_linker_count(entrypoint_output)
    if entrypoint_linkers != 0:
        raise SystemExit(f"EntryPoint linker metadata changed: {entrypoint_linkers}")
    runtime_hex = entrypoint_output["evm"]["deployedBytecode"]["object"]
    creation_hex = entrypoint_output["evm"]["bytecode"]["object"]
    expected_runtime, expected_creation = entrypoint_solc_sizes[version]
    if len(runtime_hex) // 2 != expected_runtime:
        raise SystemExit(f"EntryPoint solc {version} runtime byte size changed")
    if len(creation_hex) // 2 != expected_creation:
        raise SystemExit(f"EntryPoint solc {version} creation byte size changed")
    (outdir / f"entrypoint-{version}.standard-output.json").write_text(
        json.dumps(raw_entrypoint, separators=(",", ":"))
    )
    for selector in ("runtime", "creation"):
        bridge_json_path = outdir / f"entrypoint-{version}-{selector}.bridge.json"
        subprocess.run(
            [
                str(python_bin),
                str(bridge_path),
                str(entrypoint_request_path),
                "--input-format",
                "standard-json",
                "--solc",
                str(solc),
                "--lake",
                str(lake_bin),
                "--lake-cwd",
                str(root),
                "--source-name",
                entrypoint_source,
                "--contract",
                entrypoint_contract,
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
                "label": f"entrypoint-{version}-{selector}",
                "raw": str(outdir / f"entrypoint-{version}.standard-output.json"),
                "bridge": str(bridge_json_path),
                "source": entrypoint_source,
                "contract": entrypoint_contract,
                "selector": selector,
                "compare_artifacts": False,
                "linker_symbols": [],
            }
        )
    print(
        f"entrypoint_raw_solc_{version_key}_included_sources="
        f"{len(entrypoint_includes)}"
    )
    print(
        f"entrypoint_raw_solc_{version_key}_metadata_linker_count="
        f"{entrypoint_linkers}"
    )
    print(
        f"entrypoint_raw_solc_{version_key}_solc_runtime_bytes="
        f"{len(runtime_hex) // 2}"
    )
    print(
        f"entrypoint_raw_solc_{version_key}_solc_creation_bytes="
        f"{len(creation_hex) // 2}"
    )

raw_bridge_differential.write_runner(
    outdir / "safe_entrypoint_raw_bridge_differential_runner.lean",
    differential_cases,
    lean_string=bridge.lean_string,
)
PY

SAFE_ENTRYPOINT_DIFFERENTIAL_REPORT="$OUTDIR/safe-entrypoint-raw-bridge-differential.txt"
"$LAKE_BIN" env lean --run "$OUTDIR/safe_entrypoint_raw_bridge_differential_runner.lean" \
  > "$SAFE_ENTRYPOINT_DIFFERENTIAL_REPORT"
grep -qx 'raw_solc_frontend_differential_count=8' "$SAFE_ENTRYPOINT_DIFFERENTIAL_REPORT"
grep -qx 'raw_solc_frontend_differential=pass' "$SAFE_ENTRYPOINT_DIFFERENTIAL_REPORT"
grep -E '^raw_solc_frontend_differential(_count|=)' "$SAFE_ENTRYPOINT_DIFFERENTIAL_REPORT"

run_raw_summary() {
  local label="$1"
  local version="$2"
  local selector="$3"
  local expected_bytes="$4"
  local expected_immutables="$5"
  local source="$6"
  local contract="$7"
  local version_key="${version//./_}"
  local raw_json="$OUTDIR/$label-$version.standard-output.json"
  local report="$OUTDIR/$label-$version-$selector.raw-summary.txt"

  "$LAKE_BIN" exe evm-compiler-backend raw-summary \
    "$raw_json" "$source" "$contract" "$selector" > "$report"

  local bytes
  bytes="$(sed -n 's/^bytecode_bytes=//p' "$report")"
  if [[ "$bytes" != "$expected_bytes" ]]; then
    printf '%s %s %s raw byte length mismatch: expected %s, got %s\n' \
      "$label" "$version" "$selector" "$expected_bytes" "${bytes:-<missing>}" >&2
    tail -20 "$report" >&2
    exit 1
  fi

  local immutables
  immutables="$(grep -c $'^immutable\t' "$report" || true)"
  if [[ "$immutables" != "$expected_immutables" ]]; then
    printf '%s %s %s immutable reference count mismatch: expected %s, got %s\n' \
      "$label" "$version" "$selector" "$expected_immutables" "$immutables" >&2
    tail -20 "$report" >&2
    exit 1
  fi

  printf '%s_raw_solc_%s_%s_bytecode_bytes=%s\n' \
    "$label" "$version_key" "$selector" "$bytes"
  printf '%s_raw_solc_%s_%s_immutable_references=%s\n' \
    "$label" "$version_key" "$selector" "$immutables"
}

run_raw_summary safe 0.8.26 runtime 64843 0 "$SAFE_SOURCE" "$SAFE_CONTRACT"
run_raw_summary safe 0.8.26 creation 64882 0 "$SAFE_SOURCE" "$SAFE_CONTRACT"
run_raw_summary safe 0.8.35 runtime 64857 0 "$SAFE_SOURCE" "$SAFE_CONTRACT"
run_raw_summary safe 0.8.35 creation 64896 0 "$SAFE_SOURCE" "$SAFE_CONTRACT"

run_raw_summary entrypoint 0.8.26 runtime 76897 2 \
  "$ENTRYPOINT_SOURCE" "$ENTRYPOINT_CONTRACT"
run_raw_summary entrypoint 0.8.26 creation 78182 2 \
  "$ENTRYPOINT_SOURCE" "$ENTRYPOINT_CONTRACT"
run_raw_summary entrypoint 0.8.35 runtime 76911 2 \
  "$ENTRYPOINT_SOURCE" "$ENTRYPOINT_CONTRACT"
run_raw_summary entrypoint 0.8.35 creation 78210 2 \
  "$ENTRYPOINT_SOURCE" "$ENTRYPOINT_CONTRACT"

printf 'safe_smart_account_ref=%s\n' "$SAFE_SMART_ACCOUNT_REF"
printf 'account_abstraction_ref=%s\n' "$ACCOUNT_ABSTRACTION_REF"
printf 'openzeppelin_ref=%s\n' "$OPENZEPPELIN_REF"
printf 'raw_solc_safe_entrypoint_corpus=pass\n'
