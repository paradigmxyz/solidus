#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-uniswap-v4-extload-summary.XXXXXX")"
UNISWAP_V4_REPO_URL="${UNISWAP_V4_REPO_URL:-https://github.com/Uniswap/v4-core.git}"
UNISWAP_V4_REF="${UNISWAP_V4_REF:-46c6834698c48bc4a463a86d8420f4eb1d7f3b75}"
UNISWAP_V4_SOLC_VERSION="${UNISWAP_V4_SOLC_VERSION:-0.8.26}"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

ensure_solc_version() {
  local version="$1"
  local output
  output="$(SOLC_VERSION="$version" "$SOLC_BIN" --version 2>/dev/null || true)"
  if [[ "$output" == *"Version: $version"* ]]; then
    return
  fi
  if [[ "$INSTALL_SOLC" == "1" ]] && command -v solc-select >/dev/null 2>&1; then
    solc-select install "$version"
  fi
  output="$(SOLC_VERSION="$version" "$SOLC_BIN" --version 2>&1 || true)"
  if [[ "$output" != *"Version: $version"* ]]; then
    printf 'error: %s cannot provide solc %s\n%s\n' "$SOLC_BIN" "$version" "$output" >&2
    return 1
  fi
}

if [[ -n "${UNISWAP_V4_DIR:-}" ]]; then
  REPO="$UNISWAP_V4_DIR"
else
  REPO="$OUTDIR/v4-core"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$UNISWAP_V4_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$UNISWAP_V4_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$UNISWAP_V4_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
EXTLOAD_FIXTURE="$OUTDIR/UniswapV4ExtloadWrapper.sol"
EXTLOAD_BRIDGE_DIR="$OUTDIR/extload-bridge-json"
EXTLOAD_MANIFEST="$EXTLOAD_BRIDGE_DIR/manifest.json"
EXTLOAD_SUMMARY="$OUTDIR/UniswapV4ExtloadWrapper.bridge-json-summary.json"
EXTLOAD_BACKEND="$OUTDIR/UniswapV4ExtloadWrapper.lean-backend-check.json"

cat > "$EXTLOAD_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Extsload} from "v4-core/src/Extsload.sol";
import {Exttload} from "v4-core/src/Exttload.sol";

contract UniswapV4ExtloadWrapper is Extsload, Exttload {
    event Seeded(bytes32 indexed slot, bytes32 value);

    function seed(bytes32 slot, bytes32 value) external {
        assembly ("memory-safe") {
            sstore(slot, value)
            tstore(slot, value)
        }
        emit Seeded(slot, value);
    }
}
SOL

mkdir -p "$EXTLOAD_BRIDGE_DIR"
SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$EXTLOAD_FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "v4-core/=$REPO/" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$EXTLOAD_BRIDGE_DIR" \
  --output "$EXTLOAD_MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$EXTLOAD_MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$EXTLOAD_MANIFEST" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --contract UniswapV4ExtloadWrapper \
  --object runtime \
  --output "$EXTLOAD_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$EXTLOAD_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$EXTLOAD_MANIFEST" \
  --input-format bridge-json-manifest \
  --contract UniswapV4ExtloadWrapper \
  --object runtime \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$EXTLOAD_BACKEND"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$EXTLOAD_BACKEND"

printf 'uniswap_v4_extload_summary_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
"$PYTHON_BIN" - "$EXTLOAD_MANIFEST" "$EXTLOAD_BRIDGE_DIR" "$EXTLOAD_SUMMARY" \
  "$EXTLOAD_BACKEND" <<'PY'
import json
import sys
from pathlib import Path

manifest_path = Path(sys.argv[1])
bridge_dir = Path(sys.argv[2])
summary_path = Path(sys.argv[3])
backend_path = Path(sys.argv[4])

manifest = json.loads(manifest_path.read_text())
counts = manifest.get("counts", {})
if counts.get("entries") != 2 or counts.get("skippedContracts") != 0:
    raise SystemExit(f"unexpected extload manifest counts: {counts!r}")

runtime_entries = [
    entry
    for entry in manifest.get("entries", [])
    if entry.get("contract") == "UniswapV4ExtloadWrapper"
    and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit(f"expected one extload runtime entry, got {runtime_entries!r}")

frontend = runtime_entries[0].get("frontend")
if frontend != {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"}:
    raise SystemExit(f"unexpected extload frontend metadata: {frontend!r}")

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
if runtime_bridge.get("frontend") != frontend:
    raise SystemExit(
        f"extload bridge frontend drift: {runtime_bridge.get('frontend')!r}"
    )
if not runtime_bridge.get("selectedObject", {}).get("name"):
    raise SystemExit("extload runtime bridge is missing selected object name")

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected extload summary schema: {summary.get('schema')!r}")
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(f"unexpected extload summary counts: {summary.get('counts')!r}")

runtime_summary = summary.get("objects", [])[0]
if runtime_summary.get("frontend") != frontend:
    raise SystemExit(
        f"extload summary frontend drift: {runtime_summary.get('frontend')!r}"
    )
if runtime_summary.get("counts", {}).get("functions", 0) < 40:
    raise SystemExit(
        f"expected rich Extsload/Exttload helper surface, got {runtime_summary!r}"
    )

primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required_primitives = {
    "calldataload",
    "log2",
    "return",
    "sload",
    "sstore",
    "tload",
    "tstore",
}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(f"extload summary missing primitives: {missing_primitives!r}")

compatibility = runtime_summary.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(f"unexpected extload backend compatibility: {compatibility!r}")
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
unexpected_blockers = sorted({"log2", "sstore", "tstore"} & unsupported)
if unexpected_blockers:
    raise SystemExit(
        f"extload summary still marks supported primitives unsupported: "
        f"{unexpected_blockers!r}"
    )

backend = json.loads(backend_path.read_text())
backend_counts = backend.get("counts", {})
if backend_counts.get("checkedObjects") != 1:
    raise SystemExit(f"unexpected extload backend counts: {backend_counts!r}")
if backend_counts.get("failedObjects") != 0:
    raise SystemExit(f"extload strict backend failed: {backend!r}")
checked = backend.get("checkedObjects", [])
if len(checked) != 1 or checked[0].get("status") != "pass":
    raise SystemExit(f"extload checked artifact did not pass: {checked!r}")
if checked[0].get("firstNone") != "none":
    raise SystemExit(f"extload checked artifact is incomplete: {checked[0]!r}")

print(f"uniswap_v4_extload_manifest_entries={counts['entries']}")
print(f"uniswap_v4_extload_summary_calls={runtime_summary['counts']['calls']}")
print("uniswap_v4_extload_frontend_metadata=yes")
print("uniswap_v4_extload_summary_primitives=yes")
print(f"uniswap_v4_extload_backend_compatibility={compatibility['status']}")
print("uniswap_v4_extload_strict_backend=pass")
PY
