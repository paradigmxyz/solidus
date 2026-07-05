#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-manifest-replay-smoke.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

BRIDGE_DIR="$OUTDIR/bridge-json"
MANIFEST="$BRIDGE_DIR/manifest.json"
ORIGINAL_ARTIFACT="$OUTDIR/Simple.original-artifact.json"
REPLAYED_ARTIFACT="$OUTDIR/Simple.replayed-artifact.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Simple.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --auto-object-layout \
  --data-base 461 \
  --bridge-json-dir "$BRIDGE_DIR" \
  --namespace Generated.SimpleManifestReplayOriginalSmoke \
  --output "$ORIGINAL_ARTIFACT"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST"
python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$ORIGINAL_ARTIFACT"

python3 - "$MANIFEST" <<'PY'
import json
import sys

manifest = json.load(open(sys.argv[1]))
creation_entries = [
    entry
    for entry in manifest.get("entries", [])
    if entry.get("contract") == "Simple" and entry.get("selector") == "creation"
]
if len(creation_entries) != 1:
    raise SystemExit(f"expected one Simple creation entry, got {creation_entries!r}")

creation_entry = creation_entries[0]
layout = creation_entry.get("objectLayout")
if not isinstance(layout, list) or len(layout) != 1:
    raise SystemExit(f"manifest creation entry missing objectLayout: {creation_entry!r}")
if layout[0].get("name") != "Simple_14_deployed":
    raise SystemExit(f"unexpected objectLayout entry: {layout!r}")
if "localDataBase" not in creation_entry:
    raise SystemExit(f"manifest creation entry missing localDataBase: {creation_entry!r}")

print("manifest_replay_manifest_hints=yes")
print(f"manifest_replay_manifest_object_layout_entries={len(layout)}")
print("manifest_replay_manifest_local_data_base=yes")
PY

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --contract Simple \
  --namespace Generated.SimpleManifestReplaySmoke \
  --output "$REPLAYED_ARTIFACT"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$REPLAYED_ARTIFACT"

python3 - "$MANIFEST" "$ORIGINAL_ARTIFACT" "$REPLAYED_ARTIFACT" <<'PY'
import json
import sys

manifest_path, original_path, replayed_path = sys.argv[1:4]
manifest = json.load(open(manifest_path))
original = json.load(open(original_path))
replayed = json.load(open(replayed_path))

creation_entries = [
    entry
    for entry in manifest.get("entries", [])
    if entry.get("contract") == "Simple" and entry.get("selector") == "creation"
]
if len(creation_entries) != 1:
    raise SystemExit(f"expected one Simple creation entry, got {creation_entries!r}")

creation_entry = creation_entries[0]
layout = creation_entry.get("objectLayout")

if original["bytecode"] != replayed["bytecode"]:
    raise SystemExit("manifest replay bytecode differs from original artifact")
if original["sizes"] != replayed["sizes"]:
    raise SystemExit("manifest replay sizes differ from original artifact")

bridge_json = replayed.get("bridgeJson", {})
provenance_creation = bridge_json.get("entries", {}).get("creation", {})
if provenance_creation.get("objectLayout") != layout:
    raise SystemExit("replayed artifact provenance did not preserve objectLayout")
if provenance_creation.get("localDataBase") != creation_entry.get("localDataBase"):
    raise SystemExit("replayed artifact provenance did not preserve localDataBase")

print("manifest_replay_smoke=pass")
print("manifest_replay_without_layout_flags=pass")
print(f"manifest_replay_creation_bytes={replayed['sizes']['creationBytes']}")
print(f"manifest_replay_runtime_bytes={replayed['sizes']['runtimeBytes']}")
print(f"manifest_replay_object_layout_entries={len(layout)}")
print("manifest_replay_local_data_base=yes")
PY
