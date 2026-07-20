#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-solidity-smoke.XXXXXX")"

cleanup() {
  rm -rf "$OUTDIR"
}
trap cleanup EXIT

simple_artifact="$OUTDIR/Simple.artifact.json"
simple_standard_json="$OUTDIR/Simple.standard.json"
simple_standard_json_artifact="$OUTDIR/Simple.standard-json.artifact.json"
simple_forge_artifact="$OUTDIR/Simple.forge-artifact.json"
simple_standard_json_output="$OUTDIR/Simple.standard-json-output.json"
multi_standard_json="$OUTDIR/Multi.standard.json"
multi_standard_json_output="$OUTDIR/Multi.standard-json-output.json"
multi_standard_json_bridge_dir="$OUTDIR/Multi.standard-json-output.bridge-json"
multi_lean_json_check="$OUTDIR/Multi.lean-json-check.json"
wrapper_standard_json_output="$OUTDIR/Simple.wrapper-standard-json-output.json"
uses_library_artifact="$OUTDIR/UsesLibrary.artifact.json"
uses_remapping_artifact="$OUTDIR/UsesRemapping.artifact.json"
immutable_artifact="$OUTDIR/ImmutableBox.artifact.json"
constructor_abi_artifact="$OUTDIR/ConstructorAbiBox.artifact.json"
mapping_artifact="$OUTDIR/MappingCounter.artifact.json"
revert_artifact="$OUTDIR/RevertReason.artifact.json"
bytes_artifact="$OUTDIR/BytesBox.artifact.json"
abi_artifact="$OUTDIR/AbiBox.artifact.json"
array_artifact="$OUTDIR/ArrayBox.artifact.json"
env_artifact="$OUTDIR/EnvBox.artifact.json"
string_artifact="$OUTDIR/StringBox.artifact.json"
loop_artifact="$OUTDIR/LoopBox.artifact.json"
struct_artifact="$OUTDIR/StructBox.artifact.json"
bitwise_artifact="$OUTDIR/BitwiseBox.artifact.json"
modifier_artifact="$OUTDIR/ModifierBox.artifact.json"
inline_assembly_artifact="$OUTDIR/InlineAssemblyBox.artifact.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Simple.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.SimpleArtifactSmoke \
  --output "$simple_artifact"

python3 - "$ROOT/examples/Simple.sol" "$simple_standard_json" <<'PY'
import json
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text()
with open(sys.argv[2], "w") as handle:
    json.dump(
        {
            "language": "Solidity",
            "sources": {"Simple.sol": {"content": source}},
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        },
        handle,
    )
PY

python3 - "$ROOT/examples/Simple.sol" "$ROOT/examples/Counter.sol" "$ROOT/examples/ConstructorCounter.sol" "$ROOT/examples/ConstructorAbiBox.sol" "$ROOT/examples/InterfaceCase.sol" "$ROOT/examples/ImmutableBox.sol" "$ROOT/examples/EventCounter.sol" "$ROOT/examples/PayableVault.sol" "$ROOT/examples/MappingCounter.sol" "$ROOT/examples/RevertReason.sol" "$ROOT/examples/BytesBox.sol" "$ROOT/examples/AbiBox.sol" "$ROOT/examples/ArrayBox.sol" "$ROOT/examples/EnvBox.sol" "$ROOT/examples/StringBox.sol" "$ROOT/examples/LoopBox.sol" "$ROOT/examples/StructBox.sol" "$ROOT/examples/BitwiseBox.sol" "$ROOT/examples/ModifierBox.sol" "$ROOT/examples/InlineAssemblyBox.sol" "$multi_standard_json" <<'PY'
import json
import sys
from pathlib import Path

sources = {
    "Simple.sol": {"content": Path(sys.argv[1]).read_text()},
    "Counter.sol": {"content": Path(sys.argv[2]).read_text()},
    "ConstructorCounter.sol": {"content": Path(sys.argv[3]).read_text()},
    "ConstructorAbiBox.sol": {"content": Path(sys.argv[4]).read_text()},
    "InterfaceCase.sol": {"content": Path(sys.argv[5]).read_text()},
    "ImmutableBox.sol": {"content": Path(sys.argv[6]).read_text()},
    "EventCounter.sol": {"content": Path(sys.argv[7]).read_text()},
    "PayableVault.sol": {"content": Path(sys.argv[8]).read_text()},
    "MappingCounter.sol": {"content": Path(sys.argv[9]).read_text()},
    "RevertReason.sol": {"content": Path(sys.argv[10]).read_text()},
    "BytesBox.sol": {"content": Path(sys.argv[11]).read_text()},
    "AbiBox.sol": {"content": Path(sys.argv[12]).read_text()},
    "ArrayBox.sol": {"content": Path(sys.argv[13]).read_text()},
    "EnvBox.sol": {"content": Path(sys.argv[14]).read_text()},
    "StringBox.sol": {"content": Path(sys.argv[15]).read_text()},
    "LoopBox.sol": {"content": Path(sys.argv[16]).read_text()},
    "StructBox.sol": {"content": Path(sys.argv[17]).read_text()},
    "BitwiseBox.sol": {"content": Path(sys.argv[18]).read_text()},
    "ModifierBox.sol": {"content": Path(sys.argv[19]).read_text()},
    "InlineAssemblyBox.sol": {"content": Path(sys.argv[20]).read_text()},
}
with open(sys.argv[21], "w") as handle:
    json.dump(
        {
            "language": "Solidity",
            "sources": sources,
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        },
        handle,
    )
PY

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$simple_standard_json" \
  --input-format standard-json \
  --source-name Simple.sol \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.SimpleStandardJsonArtifactSmoke \
  --output "$simple_standard_json_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Simple.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format forge-artifact \
  --unverified-diagnostic \
  --namespace Generated.SimpleForgeArtifactSmoke \
  --output "$simple_forge_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$simple_standard_json" \
  --input-format standard-json \
  --source-name Simple.sol \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format standard-json-output \
  --unverified-diagnostic \
  --namespace Generated.SimpleStandardJsonOutputSmoke \
  --output "$simple_standard_json_output"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$multi_standard_json" \
  --input-format standard-json \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format standard-json-output \
  --unverified-diagnostic \
  --all-contracts \
  --bridge-json-dir "$multi_standard_json_bridge_dir" \
  --namespace Generated.MultiStandardJsonOutputSmoke \
  --output "$multi_standard_json_output"

python3 "$ROOT/scripts/validate_bridge_json.py" \
  --quiet "$multi_standard_json_bridge_dir/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$multi_standard_json" \
  --input-format standard-json \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --namespace Generated.MultiLeanJsonCheckSmoke \
  --output "$multi_lean_json_check"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/UsesLibrary.sol" \
  --linker-symbol 'MathLib.sol:MathLib=0' \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UsesLibrary \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.UsesLibraryArtifactSmoke \
  --output "$uses_library_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/UsesRemapping.sol" \
  --remapping "sample-lib/=$ROOT/examples/vendor/" \
  --linker-symbol 'sample-lib/ScaleLib.sol:ScaleLib=0' \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UsesRemapping \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.UsesRemappingArtifactSmoke \
  --output "$uses_remapping_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/ImmutableBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract ImmutableBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.ImmutableBoxArtifactSmoke \
  --output "$immutable_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/ConstructorAbiBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract ConstructorAbiBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.ConstructorAbiBoxArtifactSmoke \
  --output "$constructor_abi_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/MappingCounter.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract MappingCounter \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.MappingCounterArtifactSmoke \
  --output "$mapping_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/RevertReason.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract RevertReason \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.RevertReasonArtifactSmoke \
  --output "$revert_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/BytesBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract BytesBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.BytesBoxArtifactSmoke \
  --output "$bytes_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/AbiBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract AbiBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.AbiBoxArtifactSmoke \
  --output "$abi_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/ArrayBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract ArrayBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.ArrayBoxArtifactSmoke \
  --output "$array_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/EnvBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract EnvBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.EnvBoxArtifactSmoke \
  --output "$env_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/StringBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract StringBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.StringBoxArtifactSmoke \
  --output "$string_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/LoopBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract LoopBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.LoopBoxArtifactSmoke \
  --output "$loop_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/StructBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract StructBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.StructBoxArtifactSmoke \
  --output "$struct_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/BitwiseBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract BitwiseBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.BitwiseBoxArtifactSmoke \
  --output "$bitwise_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/ModifierBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract ModifierBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.ModifierBoxArtifactSmoke \
  --output "$modifier_artifact"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/InlineAssemblyBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract InlineAssemblyBox \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.InlineAssemblyBoxArtifactSmoke \
  --output "$inline_assembly_artifact"

SOLC_LEAN_REAL_SOLC="$SOLC_BIN" \
SOLC_LEAN_LAKE="$LAKE_BIN" \
SOLC_LEAN_LAKE_CWD="$ROOT" \
  "$ROOT/scripts/solc_lean_standard_json.py" --version >/dev/null

SOLC_LEAN_REAL_SOLC="$SOLC_BIN" \
SOLC_LEAN_LAKE="$LAKE_BIN" \
SOLC_LEAN_LAKE_CWD="$ROOT" \
  "$ROOT/scripts/solc_lean_standard_json.py" --standard-json \
  < "$simple_standard_json" > "$wrapper_standard_json_output"

python3 - "$simple_artifact" "$simple_standard_json_artifact" "$simple_forge_artifact" "$simple_standard_json_output" "$multi_standard_json_output" "$multi_standard_json_bridge_dir/manifest.json" "$multi_lean_json_check" "$wrapper_standard_json_output" "$uses_library_artifact" "$uses_remapping_artifact" "$immutable_artifact" "$constructor_abi_artifact" "$mapping_artifact" "$revert_artifact" "$bytes_artifact" "$abi_artifact" "$array_artifact" "$env_artifact" "$string_artifact" "$loop_artifact" "$struct_artifact" "$bitwise_artifact" "$modifier_artifact" "$inline_assembly_artifact" <<'PY'
import json
import re
import sys

def immutable_reference_list(refs):
    if not isinstance(refs, dict):
        return []
    result = []
    for entries in refs.values():
        if isinstance(entries, list):
            result.extend(entries)
    return result

def validate_artifact(label, artifact_path):
    with open(artifact_path) as handle:
        artifact = json.load(handle)

    if artifact.get("schema") != "evm-compiler.solidity-bytecode-artifact.v1":
        raise SystemExit(f"unexpected artifact schema: {artifact.get('schema')!r}")

    creation_hex = artifact["bytecode"]["creation"]
    runtime_hex = artifact["bytecode"]["runtime"]
    creation_payload = creation_hex.removeprefix("0x")
    runtime_payload = runtime_hex.removeprefix("0x")

    if not re.fullmatch(r"0x[0-9a-f]+", creation_hex):
        raise SystemExit(
            f"{label} creation bytecode is not nonempty lowercase hex"
        )

    if not re.fullmatch(r"0x[0-9a-f]+", runtime_hex):
        raise SystemExit(f"{label} runtime bytecode is not nonempty lowercase hex")

    if not creation_payload.endswith(runtime_payload):
        raise SystemExit(f"{label} runtime bytecode is not a suffix of creation bytecode")

    creation_bytes = len(creation_payload) // 2
    runtime_bytes = len(runtime_payload) // 2
    if artifact["sizes"]["creationBytes"] != creation_bytes:
        raise SystemExit(f"{label} artifact creationBytes does not match bytecode")
    if artifact["sizes"]["runtimeBytes"] != runtime_bytes:
        raise SystemExit(f"{label} artifact runtimeBytes does not match bytecode")

    prefix = "" if label == "simple" else f"{label}_"
    print(f"{prefix}creation_bytes={creation_bytes}")
    print(f"{prefix}runtime_bytes={runtime_bytes}")
    print(f"{prefix}runtime_is_creation_suffix=yes")
    return artifact


validate_artifact("simple", sys.argv[1])
validate_artifact("simple_standard_json", sys.argv[2])
with open(sys.argv[3]) as handle:
    forge_artifact = json.load(handle)

if forge_artifact.get("evmCompiler", {}).get("schema") != "evm-compiler.forge-artifact.v1":
    raise SystemExit("unexpected forge artifact compiler schema")
if not isinstance(forge_artifact.get("abi"), list):
    raise SystemExit("forge artifact did not preserve ABI as a list")
if "addOne(uint256)" not in forge_artifact.get("methodIdentifiers", {}):
    raise SystemExit("forge artifact did not preserve method identifiers")
if not re.fullmatch(r"0x[0-9a-f]+", forge_artifact["bytecode"]["object"]):
    raise SystemExit("forge artifact creation bytecode is not nonempty lowercase hex")
if not re.fullmatch(r"0x[0-9a-f]+", forge_artifact["deployedBytecode"]["object"]):
    raise SystemExit("forge artifact runtime bytecode is not nonempty lowercase hex")
print(
    "forge_artifact_creation_bytes="
    f"{forge_artifact['evmCompiler']['sizes']['creationBytes']}"
)
print(
    "forge_artifact_runtime_bytes="
    f"{forge_artifact['evmCompiler']['sizes']['runtimeBytes']}"
)

with open(sys.argv[4]) as handle:
    standard_json_output = json.load(handle)

selected = standard_json_output["contracts"]["Simple.sol"]["Simple"]
evm_compiler = selected.get("evmCompiler", {})
if evm_compiler.get("schema") != "evm-compiler.solc-standard-json-output.v1":
    raise SystemExit("unexpected standard JSON compiler schema")
standard_json_creation = selected["evm"]["bytecode"]["object"]
standard_json_runtime = selected["evm"]["deployedBytecode"]["object"]
if not re.fullmatch(r"[0-9a-f]+", standard_json_creation):
    raise SystemExit("standard JSON creation bytecode is not nonempty hex")
if not re.fullmatch(r"[0-9a-f]+", standard_json_runtime):
    raise SystemExit("standard JSON runtime bytecode is not nonempty hex")
if not standard_json_creation.endswith(standard_json_runtime):
    raise SystemExit("standard JSON runtime bytecode is not a suffix")
print(
    "standard_json_output_creation_bytes="
    f"{evm_compiler['sizes']['creationBytes']}"
)
print(
    "standard_json_output_runtime_bytes="
    f"{evm_compiler['sizes']['runtimeBytes']}"
)

with open(sys.argv[5]) as handle:
    multi_standard_json_output = json.load(handle)

for source_name, contract_name in [
    ("Simple.sol", "Simple"),
    ("Counter.sol", "Counter"),
    ("ConstructorCounter.sol", "ConstructorCounter"),
    ("ConstructorAbiBox.sol", "ConstructorAbiBox"),
    ("InterfaceCase.sol", "Impl"),
    ("ImmutableBox.sol", "ImmutableBox"),
    ("EventCounter.sol", "EventCounter"),
    ("PayableVault.sol", "PayableVault"),
    ("MappingCounter.sol", "MappingCounter"),
    ("RevertReason.sol", "RevertReason"),
    ("BytesBox.sol", "BytesBox"),
    ("AbiBox.sol", "AbiBox"),
    ("ArrayBox.sol", "ArrayBox"),
    ("EnvBox.sol", "EnvBox"),
    ("StringBox.sol", "StringBox"),
    ("LoopBox.sol", "LoopBox"),
    ("StructBox.sol", "StructBox"),
    ("BitwiseBox.sol", "BitwiseBox"),
    ("ModifierBox.sol", "ModifierBase"),
    ("ModifierBox.sol", "ModifierBox"),
    ("InlineAssemblyBox.sol", "InlineAssemblyBox"),
]:
    selected = multi_standard_json_output["contracts"][source_name][contract_name]
    evm_compiler = selected.get("evmCompiler", {})
    if evm_compiler.get("schema") != "evm-compiler.solc-standard-json-output.v1":
        raise SystemExit(f"{source_name}:{contract_name} missing compiler schema")
    creation = selected["evm"]["bytecode"]["object"]
    runtime = selected["evm"]["deployedBytecode"]["object"]
    if not re.fullmatch(r"[0-9a-f]+", creation):
        raise SystemExit(f"{source_name}:{contract_name} creation bytecode invalid")
    if not re.fullmatch(r"[0-9a-f]+", runtime):
        raise SystemExit(f"{source_name}:{contract_name} runtime bytecode invalid")
    if not creation.endswith(runtime):
        raise SystemExit(f"{source_name}:{contract_name} runtime is not a suffix")
    if source_name in {"ImmutableBox.sol", "ConstructorAbiBox.sol"}:
        refs = selected["evm"]["deployedBytecode"].get("immutableReferences")
        flattened_refs = immutable_reference_list(refs)
        if not flattened_refs:
            raise SystemExit(
                f"{source_name}:{contract_name} standard JSON missing "
                "immutable references"
            )
        runtime_bytes = len(runtime) // 2
        for ref in flattened_refs:
            if ref.get("length") != 32:
                raise SystemExit(
                    f"{source_name}:{contract_name} immutable reference "
                    "is not 32 bytes"
                )
            start = ref.get("start")
            if not isinstance(start, int) or start < 0 or start + 32 > runtime_bytes:
                raise SystemExit(
                    f"{source_name}:{contract_name} immutable reference "
                    "offset invalid"
                )
        print(
            f"multi_standard_json_{contract_name}_immutable_refs="
            f"{len(flattened_refs)}"
        )
for contract_name in ["IFace", "Base"]:
    selected = multi_standard_json_output["contracts"]["InterfaceCase.sol"][contract_name]
    if "evmCompiler" in selected:
        raise SystemExit(f"non-deployable {contract_name} unexpectedly rewritten")
print("multi_standard_json_output_contracts=21")
print("multi_standard_json_non_deployable_preserved=2")

with open(sys.argv[6]) as handle:
    multi_bridge_manifest = json.load(handle)

manifest_counts = multi_bridge_manifest.get("counts", {})
if manifest_counts.get("entries") != 42:
    raise SystemExit(f"unexpected multi bridge manifest entries: {manifest_counts!r}")
if manifest_counts.get("skippedContracts") != 2:
    raise SystemExit(f"unexpected multi bridge manifest skips: {manifest_counts!r}")
if multi_bridge_manifest.get("skippedContracts") != [
    "InterfaceCase.sol:Base",
    "InterfaceCase.sol:IFace",
]:
    raise SystemExit(
        "unexpected multi bridge manifest skipped contracts: "
        f"{multi_bridge_manifest.get('skippedContracts')!r}"
    )
expected_structured_skips = [
    {
        "source": "InterfaceCase.sol",
        "contract": "Base",
        "reason": "no-lean-bytecode-inputs",
    },
    {
        "source": "InterfaceCase.sol",
        "contract": "IFace",
        "reason": "no-lean-bytecode-inputs",
    },
]
if multi_bridge_manifest.get("skippedContractEntries") != expected_structured_skips:
    raise SystemExit(
        "unexpected multi bridge manifest structured skips: "
        f"{multi_bridge_manifest.get('skippedContractEntries')!r}"
    )
print(f"multi_standard_json_bridge_manifest_entries={manifest_counts['entries']}")
print(
    "multi_standard_json_bridge_manifest_skipped="
    f"{manifest_counts['skippedContracts']}"
)
print(
    "multi_standard_json_bridge_manifest_structured_skips="
    f"{len(expected_structured_skips)}"
)

with open(sys.argv[7]) as handle:
    multi_lean_json_check = json.load(handle)

if multi_lean_json_check.get("schema") != "evm-compiler.lean-json-check.v2":
    raise SystemExit("unexpected lean-json-check schema")
counts = multi_lean_json_check.get("counts", {})
total_contracts = (
    counts.get("checkedContracts", 0) + counts.get("skippedContracts", 0)
)
if counts.get("checkedContracts", 0) < 21 or total_contracts != 23:
    raise SystemExit(f"unexpected lean-json-check counts: {counts!r}")
if counts.get("checkedObjects", 0) < counts.get("checkedContracts", 0):
    raise SystemExit(f"lean-json-check object count too small: {counts!r}")
checked_contracts = set(multi_lean_json_check.get("checkedContracts", []))
checked_objects = {
    f"{entry.get('source')}:{entry.get('contract')}"
    for entry in multi_lean_json_check.get("checkedObjects", [])
}
for label in [
    "Simple.sol:Simple",
    "Counter.sol:Counter",
    "ConstructorAbiBox.sol:ConstructorAbiBox",
    "InterfaceCase.sol:Impl",
    "AbiBox.sol:AbiBox",
    "StructBox.sol:StructBox",
    "BitwiseBox.sol:BitwiseBox",
    "ModifierBox.sol:ModifierBase",
    "ModifierBox.sol:ModifierBox",
    "InlineAssemblyBox.sol:InlineAssemblyBox",
]:
    if label not in checked_contracts or label not in checked_objects:
        raise SystemExit(f"lean-json-check did not decode {label}")
runtime_objects = [
    entry for entry in multi_lean_json_check.get("checkedObjects", [])
    if entry.get("selector") == "runtime"
]
if len(runtime_objects) < 21:
    raise SystemExit("lean-json-check did not decode deployable runtime objects")
print(f"multi_lean_json_check_objects={counts['checkedObjects']}")
print(f"multi_lean_json_check_contracts={counts['checkedContracts']}")
print(f"multi_lean_json_check_skipped={counts['skippedContracts']}")

with open(sys.argv[8]) as handle:
    wrapper_standard_json_output = json.load(handle)
wrapper_selected = wrapper_standard_json_output["contracts"]["Simple.sol"]["Simple"]
if (
    wrapper_selected.get("evmCompiler", {}).get("schema")
    != "evm-compiler.solc-standard-json-output.v1"
):
    raise SystemExit("wrapper standard JSON output missing compiler schema")
wrapper_creation = wrapper_selected["evm"]["bytecode"]["object"]
wrapper_runtime = wrapper_selected["evm"]["deployedBytecode"]["object"]
if not wrapper_creation or not wrapper_creation.endswith(wrapper_runtime):
    raise SystemExit("wrapper standard JSON bytecode shape is invalid")
print("wrapper_standard_json_output=yes")

validate_artifact("uses_library", sys.argv[9])
validate_artifact("uses_remapping", sys.argv[10])
immutable_artifact = validate_artifact("immutable_box", sys.argv[11])
immutable_refs = immutable_artifact.get("immutableReferences", {}).get("runtime", {})
flattened_immutable_refs = immutable_reference_list(immutable_refs)
if not flattened_immutable_refs:
    raise SystemExit("ImmutableBox bytecode artifact missing immutable references")
for ref in flattened_immutable_refs:
    if ref.get("length") != 32:
        raise SystemExit("ImmutableBox bytecode artifact reference is not 32 bytes")
print(f"immutable_box_runtime_immutable_references={len(flattened_immutable_refs)}")
constructor_abi_artifact = validate_artifact("constructor_abi_box", sys.argv[12])
constructor_abi_refs = constructor_abi_artifact.get("immutableReferences", {}).get("runtime", {})
flattened_constructor_abi_refs = immutable_reference_list(constructor_abi_refs)
if not flattened_constructor_abi_refs:
    raise SystemExit(
        "ConstructorAbiBox bytecode artifact missing immutable references"
    )
for ref in flattened_constructor_abi_refs:
    if ref.get("length") != 32:
        raise SystemExit(
            "ConstructorAbiBox bytecode artifact reference is not 32 bytes"
        )
print(
    "constructor_abi_box_runtime_immutable_references="
    f"{len(flattened_constructor_abi_refs)}"
)
validate_artifact("mapping_counter", sys.argv[13])
validate_artifact("revert_reason", sys.argv[14])
validate_artifact("bytes_box", sys.argv[15])
validate_artifact("abi_box", sys.argv[16])
validate_artifact("array_box", sys.argv[17])
validate_artifact("env_box", sys.argv[18])
validate_artifact("string_box", sys.argv[19])
validate_artifact("loop_box", sys.argv[20])
validate_artifact("struct_box", sys.argv[21])
validate_artifact("bitwise_box", sys.argv[22])
validate_artifact("modifier_box", sys.argv[23])
validate_artifact("inline_assembly_box", sys.argv[24])
PY
