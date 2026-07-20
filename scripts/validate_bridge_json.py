#!/usr/bin/env python3
"""Validate normalized bridge JSON before handing it to Lean.

This checks the public JSON Schema contract and then runs the same Python
decoder used by `solidity_to_yul_lean.py --input-format bridge-json`.
It also accepts a bridge `manifest.json` and validates every listed bridge
file as one handoff package.  Summary artifacts from `--format
bridge-json-summary` are schema-checked and checked for internal count
consistency.  Lean backend check reports from `--format lean-backend-check`
are also schema-checked and checked for internal count consistency.  Bridge
provenance blocks are checked against their manifest and referenced files.
Lean-produced bytecode artifacts, Forge artifacts, and solc Standard JSON
outputs are schema-checked and have their `evmCompiler` provenance checked
against any referenced bridge package.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from collections import Counter
from typing import Any, Sequence, Tuple

import solidity_to_yul_lean as bridge

try:
    import jsonschema
except ImportError:  # pragma: no cover - exercised only in stripped envs
    jsonschema = None


def read_json(path: Path) -> Any:
    text = sys.stdin.read() if str(path) == "-" else path.read_text()
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        bridge.fail(f"Could not parse bridge JSON input: {exc}")


def load_schema(schema_path: Path) -> Any:
    try:
        schema = json.loads(schema_path.read_text())
    except json.JSONDecodeError as exc:
        bridge.fail(f"Could not parse bridge JSON schema: {exc}")
    if jsonschema is None:
        bridge.fail(
            "The jsonschema Python package is required for schema validation"
        )
    jsonschema.Draft202012Validator.check_schema(schema)
    return schema


def schema_error_path(error: Any) -> str:
    parts = list(error.absolute_path)
    if not parts:
        return "$"
    return "$" + "".join(
        f"[{part}]" if isinstance(part, int) else f".{part}"
        for part in parts
    )


def validate_bridge_data(
    label: str,
    data: Any,
    schema: Any,
    quiet: bool,
) -> Tuple[str, str, str]:
    validator = jsonschema.Draft202012Validator(schema)
    # Stringify the path elements: a raw deque mixes int array indices with
    # str keys, and comparing those raises TypeError, turning a clean
    # "schema validation failed" message into a traceback.
    errors = sorted(
        validator.iter_errors(data),
        key=lambda error: [str(part) for part in error.path],
    )
    if errors:
        first = errors[0]
        bridge.fail(
            f"schema validation failed at {schema_error_path(first)}: "
            f"{first.message}"
        )
    source_name, contract_name, obj = bridge.decode_bridge_program(data)
    if not quiet:
        print(
            f"{label}: ok source={source_name} "
            f"contract={contract_name} object={obj.name}"
        )
    return source_name, contract_name, obj.name


def validate_schema_data(data: Any, schema: Any, label: str) -> None:
    validator = jsonschema.Draft202012Validator(schema)
    # Stringify the path elements: a raw deque mixes int array indices with
    # str keys, and comparing those raises TypeError, turning a clean
    # "schema validation failed" message into a traceback.
    errors = sorted(
        validator.iter_errors(data),
        key=lambda error: [str(part) for part in error.path],
    )
    if errors:
        first = errors[0]
        bridge.fail(
            f"{label} schema validation failed at {schema_error_path(first)}: "
            f"{first.message}"
        )


def validate_bridge_frontend_metadata(
    bridge_path: Path,
    bridge_data: Any,
    manifest_entry: Any,
    owner_label: str,
) -> None:
    if not isinstance(bridge_data, dict) or not isinstance(manifest_entry, dict):
        return
    bridge_frontend = bridge_data.get("frontend")
    entry_frontend = manifest_entry.get("frontend")
    if bridge_frontend != entry_frontend:
        bridge.fail(
            f"Bridge JSON file {bridge_path} frontend metadata does not match "
            f"{owner_label}"
        )


def require_mapping(value: Any, label: str) -> Any:
    if not isinstance(value, dict):
        bridge.fail(f"{label} is not an object")
    return value


def prefixed_bytecode_size(value: Any, label: str) -> int:
    if not isinstance(value, str):
        bridge.fail(f"{label} is not bytecode hex")
    try:
        return bridge.bytecode_size(value)
    except bridge.ConversionError as exc:
        bridge.fail(f"{label} is invalid: {exc}")


def unprefixed_bytecode_size(value: Any, label: str) -> int:
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]*", value):
        bridge.fail(f"{label} is not lowercase unprefixed bytecode hex")
    return len(value) // 2


def validate_recorded_sizes(
    sizes: Any,
    creation_bytes: int,
    runtime_bytes: int,
    label: str,
) -> None:
    sizes_obj = require_mapping(sizes, f"{label}.sizes")
    if sizes_obj.get("creationBytes") != creation_bytes:
        bridge.fail(f"{label} has inconsistent sizes.creationBytes")
    if sizes_obj.get("runtimeBytes") != runtime_bytes:
        bridge.fail(f"{label} has inconsistent sizes.runtimeBytes")


def validate_manifest(
    path: Path,
    manifest: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    quiet: bool,
) -> None:
    if str(path) == "-":
        bridge.fail("Bridge JSON manifest validation requires a file path")
    validate_schema_data(manifest, manifest_schema, "manifest")
    bridge.validate_bridge_json_manifest_index(manifest, path)
    entries = manifest["entries"]
    parsed_entries: list[tuple[str, str, str, str | None, Any]] = []
    for entry in entries:
        source_name = bridge.manifest_entry_string(entry, "source", path)
        contract_name = bridge.manifest_entry_string(entry, "contract", path)
        object_name = bridge.manifest_entry_string(entry, "object", path)
        expected_sha256 = bridge.manifest_entry_sha256(entry, path)
        parsed_entries.append(
            (source_name, contract_name, object_name, expected_sha256, entry)
        )
    for (
        source_name,
        contract_name,
        object_name,
        expected_sha256,
        entry,
    ) in parsed_entries:
        bridge_path = bridge.manifest_entry_bridge_json_path(path, entry)
        bridge.check_manifest_entry_sha256(path, bridge_path, entry)
        data = read_json(bridge_path)
        decoded_source, decoded_contract, decoded_object = validate_bridge_data(
            str(bridge_path),
            data,
            bridge_schema,
            quiet,
        )
        if decoded_source != source_name:
            bridge.fail(
                f"Bridge JSON file {bridge_path} source is {decoded_source!r}, "
                f"but manifest says {source_name!r}"
            )
        if decoded_contract != contract_name:
            bridge.fail(
                f"Bridge JSON file {bridge_path} contract is "
                f"{decoded_contract!r}, but manifest says {contract_name!r}"
            )
        if decoded_object != object_name:
            bridge.fail(
                f"Bridge JSON file {bridge_path} object is {decoded_object!r}, "
                f"but manifest says {object_name!r}"
            )
        validate_bridge_frontend_metadata(
            bridge_path,
            data,
            entry,
            "manifest entry",
        )
    if not quiet:
        print(f"{path}: ok manifest entries={len(entries)}")


def provenance_manifest_path(path: Path, provenance: Any) -> Path:
    manifest_value = provenance.get("manifest")
    if not isinstance(manifest_value, str) or not manifest_value:
        bridge.fail("bridge provenance has invalid manifest path")
    manifest_path = Path(manifest_value)
    if not manifest_path.is_absolute():
        if str(path) == "-":
            bridge.fail(
                "relative bridge provenance manifest path requires a file input"
            )
        manifest_path = path.parent / manifest_path
    return manifest_path


def validate_provenance_entry(
    manifest: Any,
    manifest_path: Path,
    provenance_entry: Any,
    expected_selector: str,
    bridge_schema: Any,
    quiet: bool,
) -> None:
    if not isinstance(provenance_entry, dict):
        bridge.fail(f"bridge provenance {expected_selector} entry is not an object")
    if provenance_entry.get("selector") != expected_selector:
        bridge.fail(
            f"bridge provenance {expected_selector} entry has selector "
            f"{provenance_entry.get('selector')!r}"
        )
    source_name = bridge.manifest_entry_string(
        provenance_entry,
        "source",
        manifest_path,
    )
    contract_name = bridge.manifest_entry_string(
        provenance_entry,
        "contract",
        manifest_path,
    )
    object_name = bridge.manifest_entry_string(
        provenance_entry,
        "object",
        manifest_path,
    )
    manifest_entry = bridge.bridge_json_manifest_entry_for_object(
        manifest,
        source_name,
        contract_name,
        expected_selector,
        object_name,
        manifest_path,
    )
    if provenance_entry != manifest_entry:
        bridge.fail(
            f"bridge provenance {expected_selector} entry does not match "
            "manifest entry"
        )
    bridge_path = bridge.manifest_entry_bridge_json_path(
        manifest_path,
        provenance_entry,
    )
    bridge.check_manifest_entry_sha256(manifest_path, bridge_path, provenance_entry)
    data = read_json(bridge_path)
    decoded_source, decoded_contract, decoded_object = validate_bridge_data(
        str(bridge_path),
        data,
        bridge_schema,
        quiet=True,
    )
    if decoded_source != source_name:
        bridge.fail(
            f"Bridge JSON file {bridge_path} source is {decoded_source!r}, "
            f"but provenance says {source_name!r}"
        )
    if decoded_contract != contract_name:
        bridge.fail(
            f"Bridge JSON file {bridge_path} contract is "
            f"{decoded_contract!r}, but provenance says {contract_name!r}"
        )
    if decoded_object != object_name:
        bridge.fail(
            f"Bridge JSON file {bridge_path} object is {decoded_object!r}, "
            f"but provenance says {object_name!r}"
        )
    validate_bridge_frontend_metadata(
        bridge_path,
        data,
        provenance_entry,
        "bridge provenance entry",
    )


def validate_provenance(
    path: Path,
    provenance: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    provenance_schema: Any,
    quiet: bool,
) -> None:
    if not isinstance(provenance, dict):
        bridge.fail("bridge provenance is not an object")
    validate_schema_data(provenance, provenance_schema, "bridge provenance")
    manifest_path = provenance_manifest_path(path, provenance)
    manifest = read_json(manifest_path)
    validate_schema_data(manifest, manifest_schema, "manifest")
    bridge.validate_bridge_json_manifest_index(manifest, manifest_path)
    entries = provenance.get("entries")
    if not isinstance(entries, dict):
        bridge.fail("bridge provenance has invalid entries")
    validate_provenance_entry(
        manifest,
        manifest_path,
        entries.get("creation"),
        "creation",
        bridge_schema,
        quiet,
    )
    validate_provenance_entry(
        manifest,
        manifest_path,
        entries.get("runtime"),
        "runtime",
        bridge_schema,
        quiet,
    )
    if not quiet:
        print(f"{path}: ok provenance manifest={manifest_path} entries=2")


def validate_optional_bridge_provenance(
    path: Path,
    owner: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    provenance_schema: Any,
) -> None:
    if not isinstance(owner, dict):
        return
    provenance = owner.get("bridgeJson")
    if provenance is None:
        return
    validate_provenance(
        path,
        provenance,
        bridge_schema,
        manifest_schema,
        provenance_schema,
        quiet=True,
    )


def validate_bytecode_artifact(
    path: Path,
    artifact: Any,
    artifact_schema: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    provenance_schema: Any,
    quiet: bool,
) -> None:
    label = "<stdin>" if str(path) == "-" else str(path)
    validate_schema_data(artifact, artifact_schema, "bytecode-artifact")
    artifact_obj = require_mapping(artifact, "bytecode-artifact")
    bytecode = require_mapping(
        artifact_obj.get("bytecode"),
        "bytecode-artifact.bytecode",
    )
    creation_bytes = prefixed_bytecode_size(
        bytecode.get("creation"),
        "bytecode-artifact.bytecode.creation",
    )
    runtime_bytes = prefixed_bytecode_size(
        bytecode.get("runtime"),
        "bytecode-artifact.bytecode.runtime",
    )
    validate_recorded_sizes(
        artifact_obj.get("sizes"),
        creation_bytes,
        runtime_bytes,
        "bytecode-artifact",
    )
    validate_optional_bridge_provenance(
        path,
        artifact_obj,
        bridge_schema,
        manifest_schema,
        provenance_schema,
    )
    if not quiet:
        print(
            f"{label}: ok bytecode-artifact source={artifact_obj['source']} "
            f"contract={artifact_obj['contract']} "
            f"creationBytes={creation_bytes} runtimeBytes={runtime_bytes}"
        )


def validate_evm_compiler_metadata(
    path: Path,
    metadata: Any,
    metadata_schema: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    provenance_schema: Any,
) -> None:
    validate_schema_data(metadata, metadata_schema, "evmCompiler")
    validate_optional_bridge_provenance(
        path,
        metadata,
        bridge_schema,
        manifest_schema,
        provenance_schema,
    )


def validate_forge_artifact(
    path: Path,
    artifact: Any,
    metadata_schema: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    provenance_schema: Any,
    quiet: bool,
) -> None:
    label = "<stdin>" if str(path) == "-" else str(path)
    artifact_obj = require_mapping(artifact, "forge artifact")
    metadata = require_mapping(
        artifact_obj.get("evmCompiler"),
        "forge artifact.evmCompiler",
    )
    validate_evm_compiler_metadata(
        path,
        metadata,
        metadata_schema,
        bridge_schema,
        manifest_schema,
        provenance_schema,
    )
    if metadata.get("schema") != "evm-compiler.forge-artifact.v1":
        bridge.fail("forge artifact evmCompiler schema is not forge-artifact.v1")
    creation_section = require_mapping(
        artifact_obj.get("bytecode"),
        "forge artifact.bytecode",
    )
    runtime_section = require_mapping(
        artifact_obj.get("deployedBytecode"),
        "forge artifact.deployedBytecode",
    )
    creation_bytes = prefixed_bytecode_size(
        creation_section.get("object"),
        "forge artifact.bytecode.object",
    )
    runtime_bytes = prefixed_bytecode_size(
        runtime_section.get("object"),
        "forge artifact.deployedBytecode.object",
    )
    validate_recorded_sizes(
        metadata.get("sizes"),
        creation_bytes,
        runtime_bytes,
        "forge artifact.evmCompiler",
    )
    if not quiet:
        print(
            f"{label}: ok forge-artifact source={metadata['source']} "
            f"contract={metadata['contract']} "
            f"creationBytes={creation_bytes} runtimeBytes={runtime_bytes}"
        )


def standard_json_metadata_entries(data: Any) -> list[tuple[str, str, Any, Any]]:
    if not isinstance(data, dict):
        return []
    contracts_by_source = data.get("contracts")
    if not isinstance(contracts_by_source, dict):
        return []
    entries: list[tuple[str, str, Any, Any]] = []
    for source_name, contracts in contracts_by_source.items():
        if not isinstance(source_name, str) or not isinstance(contracts, dict):
            continue
        for contract_name, contract_output in contracts.items():
            if (
                not isinstance(contract_name, str)
                or not isinstance(contract_output, dict)
            ):
                continue
            metadata = contract_output.get("evmCompiler")
            if metadata is not None:
                entries.append((source_name, contract_name, contract_output, metadata))
    return entries


def looks_like_standard_json_output(data: Any) -> bool:
    return isinstance(data, dict) and isinstance(data.get("contracts"), dict)


def validate_standard_json_contract_map(data: Any, label: str) -> int:
    data_obj = require_mapping(data, label)
    contracts_by_source = require_mapping(
        data_obj.get("contracts"),
        f"{label}.contracts",
    )
    contract_count = 0
    for source_name, contracts in contracts_by_source.items():
        if not isinstance(source_name, str) or not source_name:
            bridge.fail(f"{label}.contracts has invalid source name")
        contracts_obj = require_mapping(
            contracts,
            f"{label}.contracts[{source_name!r}]",
        )
        for contract_name, contract_output in contracts_obj.items():
            if not isinstance(contract_name, str) or not contract_name:
                bridge.fail(
                    f"{label}.contracts[{source_name!r}] has invalid contract name"
                )
            require_mapping(
                contract_output,
                f"{source_name}:{contract_name}",
            )
            contract_count += 1
    return contract_count


def validate_standard_json_output_metadata(
    path: Path,
    data: Any,
    metadata_schema: Any,
    bridge_schema: Any,
    manifest_schema: Any,
    provenance_schema: Any,
    quiet: bool,
) -> None:
    label = "<stdin>" if str(path) == "-" else str(path)
    validate_standard_json_contract_map(data, label)
    entries = standard_json_metadata_entries(data)
    for source_name, contract_name, contract_output, metadata in entries:
        entry_label = f"{source_name}:{contract_name}.evmCompiler"
        metadata_obj = require_mapping(metadata, entry_label)
        validate_evm_compiler_metadata(
            path,
            metadata_obj,
            metadata_schema,
            bridge_schema,
            manifest_schema,
            provenance_schema,
        )
        if metadata_obj.get("schema") != "evm-compiler.solc-standard-json-output.v1":
            bridge.fail(f"{entry_label} schema is not solc-standard-json-output.v1")
        if metadata_obj.get("source") != source_name:
            bridge.fail(f"{entry_label} source does not match contract map")
        if metadata_obj.get("contract") != contract_name:
            bridge.fail(f"{entry_label} contract does not match contract map")
        evm = require_mapping(
            contract_output.get("evm"),
            f"{source_name}:{contract_name}.evm",
        )
        bytecode = require_mapping(
            evm.get("bytecode"),
            f"{source_name}:{contract_name}.evm.bytecode",
        )
        runtime = require_mapping(
            evm.get("deployedBytecode"),
            f"{source_name}:{contract_name}.evm.deployedBytecode",
        )
        creation_bytes = unprefixed_bytecode_size(
            bytecode.get("object"),
            f"{source_name}:{contract_name}.evm.bytecode.object",
        )
        runtime_bytes = unprefixed_bytecode_size(
            runtime.get("object"),
            f"{source_name}:{contract_name}.evm.deployedBytecode.object",
        )
        validate_recorded_sizes(
            metadata_obj.get("sizes"),
            creation_bytes,
            runtime_bytes,
            entry_label,
        )
    if not quiet:
        print(f"{label}: ok standard-json-output contracts={len(entries)}")


def validate_count_entries(entries: Any, label: str) -> int:
    if not isinstance(entries, list):
        bridge.fail(f"{label} is not a count-entry list")
    seen: set[str] = set()
    total = 0
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            bridge.fail(f"{label}[{index}] is not an object")
        name = entry.get("name")
        count = entry.get("count")
        if not isinstance(name, str) or not name:
            bridge.fail(f"{label}[{index}] has invalid name")
        if name in seen:
            bridge.fail(f"{label} has duplicate count entry name: {name!r}")
        seen.add(name)
        if not isinstance(count, int) or count <= 0:
            bridge.fail(f"{label}[{index}] has invalid count")
        total += count
    return total


def count_entry_names(entries: Any) -> set[str]:
    if not isinstance(entries, list):
        return set()
    return {
        entry["name"]
        for entry in entries
        if isinstance(entry, dict) and isinstance(entry.get("name"), str)
    }


def validate_string_list(value: Any, label: str) -> list[str]:
    if not isinstance(value, list):
        bridge.fail(f"{label} is not a list")
    names = []
    seen: set[str] = set()
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            bridge.fail(f"{label}[{index}] is not a nonempty string")
        if item in seen:
            bridge.fail(f"{label} has duplicate name: {item!r}")
        seen.add(item)
        names.append(item)
    return names


def validate_backend_compatibility(summary: Any, label: str) -> None:
    compatibility = summary.get("backendCompatibility")
    if not isinstance(compatibility, dict):
        bridge.fail(f"{label} summary has invalid backendCompatibility")
    calls = summary.get("calls")
    if not isinstance(calls, dict):
        bridge.fail(f"{label} summary has invalid calls")
    primitive_names = count_entry_names(calls.get("primitive", {}).get("names"))
    object_builtin_names = count_entry_names(
        calls.get("objectBuiltin", {}).get("names")
    )
    dialect_builtin_names = count_entry_names(
        calls.get("dialectBuiltin", {}).get("names")
    )
    expected_unsupported = sorted(
        primitive_names & bridge.BACKEND_BLOCKING_PRIMITIVES
    )
    expected_object_builtins = sorted(object_builtin_names)
    expected_dialect_builtins = sorted(dialect_builtin_names)
    actual_unsupported = validate_string_list(
        compatibility.get("unsupportedPrimitiveNames"),
        f"{label} summary.backendCompatibility.unsupportedPrimitiveNames",
    )
    actual_object_builtins = validate_string_list(
        compatibility.get("objectBuiltinNames"),
        f"{label} summary.backendCompatibility.objectBuiltinNames",
    )
    actual_dialect_builtins = validate_string_list(
        compatibility.get("dialectBuiltinNames"),
        f"{label} summary.backendCompatibility.dialectBuiltinNames",
    )
    validate_string_list(
        compatibility.get("notes"),
        f"{label} summary.backendCompatibility.notes",
    )
    if actual_unsupported != expected_unsupported:
        bridge.fail(
            f"{label} summary has inconsistent "
            "backendCompatibility.unsupportedPrimitiveNames"
        )
    if actual_object_builtins != expected_object_builtins:
        bridge.fail(
            f"{label} summary has inconsistent "
            "backendCompatibility.objectBuiltinNames"
        )
    if actual_dialect_builtins != expected_dialect_builtins:
        bridge.fail(
            f"{label} summary has inconsistent "
            "backendCompatibility.dialectBuiltinNames"
        )
    expected_linker_object_builtins = (
        set(expected_object_builtins)
        & bridge.BACKEND_OBJECT_BUILTINS_REQUIRING_LINKER
    )
    if expected_unsupported or expected_dialect_builtins:
        expected_status = "blocked"
    elif expected_linker_object_builtins:
        expected_status = "needs-resolution"
    else:
        expected_status = "ready"
    if compatibility.get("status") != expected_status:
        bridge.fail(
            f"{label} summary has inconsistent backendCompatibility.status"
        )


def validate_manifest_backend_compatibility(
    data: Any,
    label: str,
) -> None:
    compatibility = data.get("backendCompatibility")
    if not isinstance(compatibility, dict):
        bridge.fail(f"{label} summary has invalid backendCompatibility")
    objects = data.get("objects")
    if not isinstance(objects, list):
        bridge.fail(f"{label} summary has invalid objects")
    unsupported: set[str] = set()
    object_builtins: set[str] = set()
    dialect_builtins: set[str] = set()
    for object_summary in objects:
        if not isinstance(object_summary, dict):
            continue
        object_compatibility = object_summary.get("backendCompatibility")
        if not isinstance(object_compatibility, dict):
            continue
        unsupported.update(
            name
            for name in object_compatibility.get("unsupportedPrimitiveNames", [])
            if isinstance(name, str)
        )
        object_builtins.update(
            name
            for name in object_compatibility.get("objectBuiltinNames", [])
            if isinstance(name, str)
        )
        dialect_builtins.update(
            name
            for name in object_compatibility.get("dialectBuiltinNames", [])
            if isinstance(name, str)
        )
    expected_unsupported = sorted(unsupported)
    expected_object_builtins = sorted(object_builtins)
    expected_dialect_builtins = sorted(dialect_builtins)
    actual_unsupported = validate_string_list(
        compatibility.get("unsupportedPrimitiveNames"),
        f"{label} summary.backendCompatibility.unsupportedPrimitiveNames",
    )
    actual_object_builtins = validate_string_list(
        compatibility.get("objectBuiltinNames"),
        f"{label} summary.backendCompatibility.objectBuiltinNames",
    )
    actual_dialect_builtins = validate_string_list(
        compatibility.get("dialectBuiltinNames"),
        f"{label} summary.backendCompatibility.dialectBuiltinNames",
    )
    validate_string_list(
        compatibility.get("notes"),
        f"{label} summary.backendCompatibility.notes",
    )
    if actual_unsupported != expected_unsupported:
        bridge.fail(
            f"{label} summary has inconsistent aggregate "
            "backendCompatibility.unsupportedPrimitiveNames"
        )
    if actual_object_builtins != expected_object_builtins:
        bridge.fail(
            f"{label} summary has inconsistent aggregate "
            "backendCompatibility.objectBuiltinNames"
        )
    if actual_dialect_builtins != expected_dialect_builtins:
        bridge.fail(
            f"{label} summary has inconsistent aggregate "
            "backendCompatibility.dialectBuiltinNames"
        )
    expected_linker_object_builtins = (
        set(expected_object_builtins)
        & bridge.BACKEND_OBJECT_BUILTINS_REQUIRING_LINKER
    )
    if expected_unsupported or expected_dialect_builtins:
        expected_status = "blocked"
    elif expected_linker_object_builtins:
        expected_status = "needs-resolution"
    else:
        expected_status = "ready"
    if compatibility.get("status") != expected_status:
        bridge.fail(
            f"{label} summary has inconsistent aggregate "
            "backendCompatibility.status"
        )


def validate_object_summary_counts(summary: Any, label: str) -> None:
    if not isinstance(summary, dict):
        bridge.fail(f"{label} summary is not an object")
    counts = summary.get("counts")
    if not isinstance(counts, dict):
        bridge.fail(f"{label} summary has invalid counts")
    objects = summary.get("objects")
    if not isinstance(objects, list):
        bridge.fail(f"{label} summary has invalid objects")
    if counts.get("objects") != len(objects):
        bridge.fail(f"{label} summary has inconsistent counts.objects")
    for count_name, object_field in [
        ("functions", "functions"),
        ("dataSections", "dataSections"),
        ("dataBytes", "dataBytes"),
    ]:
        total = sum(
            item.get(object_field, 0)
            for item in objects
            if isinstance(item, dict) and isinstance(item.get(object_field), int)
        )
        if counts.get(count_name) != total:
            bridge.fail(f"{label} summary has inconsistent counts.{count_name}")
    statements_total = validate_count_entries(
        summary.get("statements"),
        f"{label} summary.statements",
    )
    if counts.get("statements") != statements_total:
        bridge.fail(f"{label} summary has inconsistent counts.statements")
    expressions_total = validate_count_entries(
        summary.get("expressions"),
        f"{label} summary.expressions",
    )
    if counts.get("expressions") != expressions_total:
        bridge.fail(f"{label} summary has inconsistent counts.expressions")
    calls = summary.get("calls")
    if not isinstance(calls, dict):
        bridge.fail(f"{label} summary has invalid calls")
    call_total = 0
    for kind in ["primitive", "user", "objectBuiltin", "dialectBuiltin"]:
        kind_summary = calls.get(kind)
        if not isinstance(kind_summary, dict):
            bridge.fail(f"{label} summary has invalid calls.{kind}")
        name_total = validate_count_entries(
            kind_summary.get("names"),
            f"{label} summary.calls.{kind}.names",
        )
        if kind_summary.get("total") != name_total:
            bridge.fail(f"{label} summary has inconsistent calls.{kind}.total")
        call_total += name_total
    if counts.get("calls") != call_total:
        bridge.fail(f"{label} summary has inconsistent counts.calls")
    if "frontend" in summary:
        bridge.normalize_bridge_json_frontend_metadata(
            summary.get("frontend"),
            f"{label} summary.frontend",
        )
    validate_backend_compatibility(summary, label)


def validate_summary(
    label: str,
    data: Any,
    summary_schema: Any,
    quiet: bool,
) -> None:
    validate_schema_data(data, summary_schema, "summary")
    schema = data.get("schema") if isinstance(data, dict) else None
    if schema == bridge.BRIDGE_JSON_SUMMARY_SCHEMA:
        validate_object_summary_counts(data, label)
        if not quiet:
            counts = data["counts"]
            print(
                f"{label}: ok summary source={data['source']} "
                f"contract={data['contract']} object={data['object']} "
                f"calls={counts['calls']}"
            )
        return
    if schema == bridge.BRIDGE_JSON_MANIFEST_SUMMARY_SCHEMA:
        counts = data.get("counts")
        objects = data.get("objects")
        skipped_contracts = data.get("skippedContracts")
        skipped_entries = data.get("skippedContractEntries")
        if not isinstance(counts, dict):
            bridge.fail(f"{label} summary has invalid counts")
        if not isinstance(objects, list):
            bridge.fail(f"{label} summary has invalid objects")
        if not isinstance(skipped_contracts, list):
            bridge.fail(f"{label} summary has invalid skippedContracts")
        if skipped_entries is not None:
            if not isinstance(skipped_entries, list):
                bridge.fail(f"{label} summary has invalid skippedContractEntries")
            skipped_entry_labels = [
                bridge.skipped_contract_label_from_entry(entry, Path(label))
                for entry in skipped_entries
            ]
            if sorted(skipped_entry_labels) != sorted(skipped_contracts):
                bridge.fail(
                    f"{label} summary has inconsistent skippedContracts "
                    "and skippedContractEntries"
                )
        if counts.get("objects") != len(objects):
            bridge.fail(f"{label} summary has inconsistent counts.objects")
        if counts.get("skippedContracts") != len(skipped_contracts):
            bridge.fail(
                f"{label} summary has inconsistent counts.skippedContracts"
            )
        object_call_total = 0
        for index, object_summary in enumerate(objects):
            validate_object_summary_counts(
                object_summary,
                f"{label} summary.objects[{index}]",
            )
            object_counts = object_summary.get("counts")
            if isinstance(object_counts, dict) and isinstance(
                object_counts.get("calls"),
                int,
            ):
                object_call_total += object_counts["calls"]
        if counts.get("calls") != object_call_total:
            bridge.fail(f"{label} summary has inconsistent counts.calls")
        validate_manifest_backend_compatibility(data, label)
        if not quiet:
            print(
                f"{label}: ok manifest-summary objects={len(objects)} "
                f"skippedContracts={len(skipped_contracts)} "
                f"calls={counts['calls']}"
            )
        return
    bridge.fail(f"{label} has unsupported summary schema: {schema!r}")


def validate_lean_backend_check(
    label: str,
    data: Any,
    backend_check_schema: Any,
    quiet: bool,
) -> None:
    validate_schema_data(data, backend_check_schema, "lean-backend-check")
    if not isinstance(data, dict):
        bridge.fail(f"{label} backend check is not an object")
    checked_objects = data.get("checkedObjects")
    checked_contracts = data.get("checkedContracts")
    skipped_contracts = data.get("skippedContracts")
    counts = data.get("counts")
    first_none_counts = data.get("firstNoneCounts")
    if not isinstance(checked_objects, list):
        bridge.fail(f"{label} backend check has invalid checkedObjects")
    if not isinstance(checked_contracts, list):
        bridge.fail(f"{label} backend check has invalid checkedContracts")
    if not isinstance(skipped_contracts, list):
        bridge.fail(f"{label} backend check has invalid skippedContracts")
    if not isinstance(counts, dict):
        bridge.fail(f"{label} backend check has invalid counts")
    if not isinstance(first_none_counts, dict):
        bridge.fail(f"{label} backend check has invalid firstNoneCounts")

    expected_contracts = sorted(
        {
            f"{item.get('source')}:{item.get('contract')}"
            for item in checked_objects
            if isinstance(item, dict)
        }
    )
    if checked_contracts != expected_contracts:
        bridge.fail(
            f"{label} backend check has inconsistent checkedContracts"
        )
    if counts.get("checkedObjects") != len(checked_objects):
        bridge.fail(
            f"{label} backend check has inconsistent counts.checkedObjects"
        )
    if counts.get("checkedContracts") != len(checked_contracts):
        bridge.fail(
            f"{label} backend check has inconsistent counts.checkedContracts"
        )
    if counts.get("skippedContracts") != len(skipped_contracts):
        bridge.fail(
            f"{label} backend check has inconsistent counts.skippedContracts"
        )

    status_counts = Counter()
    expected_first_none_counts: Counter[str] = Counter()
    seen_keys: set[tuple[str, str, str, str]] = set()
    for index, item in enumerate(checked_objects):
        if not isinstance(item, dict):
            bridge.fail(f"{label} backend check checkedObjects[{index}] is invalid")
        key = (
            str(item.get("source")),
            str(item.get("contract")),
            str(item.get("selector")),
            str(item.get("object")),
        )
        if key in seen_keys:
            bridge.fail(
                f"{label} backend check has duplicate checked object: {key!r}"
            )
        seen_keys.add(key)
        status = item.get("status")
        first_none = item.get("firstNone")
        stages = item.get("stages")
        if status not in {"pass", "fail"}:
            bridge.fail(f"{label} backend check checkedObjects[{index}] status")
        if not isinstance(first_none, str) or not first_none:
            bridge.fail(
                f"{label} backend check checkedObjects[{index}] firstNone"
            )
        if not isinstance(stages, dict):
            bridge.fail(f"{label} backend check checkedObjects[{index}] stages")
        if "frontend" in item:
            frontend = bridge.normalize_bridge_json_frontend_metadata(
                item.get("frontend"),
                f"{label} backend check checkedObjects[{index}].frontend",
            )
            if frontend is None:
                bridge.fail(
                    f"{label} backend check checkedObjects[{index}] frontend"
                )
        object_image = stages.get("object_image")
        status_counts[status] += 1
        if status == "pass":
            if first_none != "none":
                bridge.fail(
                    f"{label} backend check pass object has firstNone={first_none!r}"
                )
            if object_image != "some":
                bridge.fail(
                    f"{label} backend check pass object lacks object_image=some"
                )
        else:
            if first_none == "none":
                bridge.fail(
                    f"{label} backend check fail object has firstNone=none"
                )
            expected_first_none_counts[first_none] += 1
            if stages.get(first_none) != "none":
                bridge.fail(
                    f"{label} backend check firstNone stage is not none: "
                    f"{first_none!r}"
                )
        bytecode_bytes = item.get("bytecodeBytes")
        if bytecode_bytes is not None and object_image != "some":
            bridge.fail(
                f"{label} backend check object has bytecodeBytes without "
                "object_image=some"
            )
    if counts.get("passedObjects") != status_counts.get("pass", 0):
        bridge.fail(
            f"{label} backend check has inconsistent counts.passedObjects"
        )
    if counts.get("failedObjects") != status_counts.get("fail", 0):
        bridge.fail(
            f"{label} backend check has inconsistent counts.failedObjects"
        )
    if dict(sorted(expected_first_none_counts.items())) != first_none_counts:
        bridge.fail(
            f"{label} backend check has inconsistent firstNoneCounts"
        )
    if not quiet:
        print(
            f"{label}: ok backend-check objects={len(checked_objects)} "
            f"passed={status_counts.get('pass', 0)} "
            f"failed={status_counts.get('fail', 0)}"
        )


def validate_one(
    path: Path,
    bridge_schema: Any,
    manifest_schema: Any,
    summary_schema: Any,
    backend_check_schema: Any,
    provenance_schema: Any,
    bytecode_artifact_schema: Any,
    metadata_schema: Any,
    quiet: bool,
) -> bool:
    label = "<stdin>" if str(path) == "-" else str(path)
    try:
        data = read_json(path)
        if (
            isinstance(data, dict)
            and data.get("schema") == bridge.BRIDGE_JSON_MANIFEST_SCHEMA
        ):
            validate_manifest(path, data, bridge_schema, manifest_schema, quiet)
        elif (
            isinstance(data, dict)
            and data.get("schema")
            in {
                bridge.BRIDGE_JSON_SUMMARY_SCHEMA,
                bridge.BRIDGE_JSON_MANIFEST_SUMMARY_SCHEMA,
            }
        ):
            validate_summary(label, data, summary_schema, quiet)
        elif (
            isinstance(data, dict)
            and data.get("schema") == bridge.LEAN_BACKEND_CHECK_SCHEMA
        ):
            validate_lean_backend_check(
                label,
                data,
                backend_check_schema,
                quiet,
            )
        elif (
            isinstance(data, dict)
            and data.get("schema") == bridge.BRIDGE_JSON_PROVENANCE_SCHEMA
        ):
            validate_provenance(
                path,
                data,
                bridge_schema,
                manifest_schema,
                provenance_schema,
                quiet,
            )
        elif (
            isinstance(data, dict)
            and data.get("schema")
            == "evm-compiler.solidity-bytecode-artifact.v1"
        ):
            validate_bytecode_artifact(
                path,
                data,
                bytecode_artifact_schema,
                bridge_schema,
                manifest_schema,
                provenance_schema,
                quiet,
            )
        elif isinstance(data, dict) and isinstance(data.get("evmCompiler"), dict):
            validate_forge_artifact(
                path,
                data,
                metadata_schema,
                bridge_schema,
                manifest_schema,
                provenance_schema,
                quiet,
            )
        elif looks_like_standard_json_output(data):
            validate_standard_json_output_metadata(
                path,
                data,
                metadata_schema,
                bridge_schema,
                manifest_schema,
                provenance_schema,
                quiet,
            )
        else:
            validate_bridge_data(label, data, bridge_schema, quiet)
    except bridge.ConversionError as exc:
        print(f"{label}: error: {exc}", file=sys.stderr)
        return False
    return True


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "inputs",
        nargs="+",
        type=Path,
        help=(
            "Bridge JSON files, manifests, summaries, provenance blocks, "
            "bytecode artifacts, Forge artifacts, or Standard JSON outputs "
            "to validate, or '-' for stdin"
        ),
    )
    parser.add_argument(
        "--schema",
        type=Path,
        default=Path(__file__).with_name("bridge-json-v3.schema.json"),
        help="JSON Schema file to validate against",
    )
    parser.add_argument(
        "--manifest-schema",
        type=Path,
        default=Path(__file__).with_name("bridge-json-manifest-v1.schema.json"),
        help="JSON Schema file to validate bridge manifests against",
    )
    parser.add_argument(
        "--summary-schema",
        type=Path,
        default=Path(__file__).with_name("bridge-json-summary-v1.schema.json"),
        help="JSON Schema file to validate bridge summaries against",
    )
    parser.add_argument(
        "--backend-check-schema",
        type=Path,
        default=Path(__file__).with_name("lean-backend-check-v1.schema.json"),
        help="JSON Schema file to validate Lean backend check reports against",
    )
    parser.add_argument(
        "--provenance-schema",
        type=Path,
        default=Path(__file__).with_name("bridge-json-provenance-v1.schema.json"),
        help="JSON Schema file to validate bridge provenance blocks against",
    )
    parser.add_argument(
        "--bytecode-artifact-schema",
        type=Path,
        default=Path(__file__).with_name("bytecode-artifact-v1.schema.json"),
        help="JSON Schema file to validate bytecode artifacts against",
    )
    parser.add_argument(
        "--metadata-schema",
        type=Path,
        default=Path(__file__).with_name("evm-compiler-metadata-v1.schema.json"),
        help="JSON Schema file to validate evmCompiler metadata against",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Only print validation errors",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    try:
        bridge_schema = load_schema(args.schema)
        manifest_schema = load_schema(args.manifest_schema)
        summary_schema = load_schema(args.summary_schema)
        backend_check_schema = load_schema(args.backend_check_schema)
        provenance_schema = load_schema(args.provenance_schema)
        bytecode_artifact_schema = load_schema(args.bytecode_artifact_schema)
        metadata_schema = load_schema(args.metadata_schema)
    except bridge.ConversionError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    ok = True
    for path in args.inputs:
        ok = (
            validate_one(
                path,
                bridge_schema,
                manifest_schema,
                summary_schema,
                backend_check_schema,
                provenance_schema,
                bytecode_artifact_schema,
                metadata_schema,
                args.quiet,
            )
            and ok
        )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
