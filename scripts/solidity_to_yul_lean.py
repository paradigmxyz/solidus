#!/usr/bin/env python3
"""Compile Solidity through solc's Yul AST into Lean-facing artifacts.

The Solidity-facing Lean frontend accepts a typed selected Yul object tree:
dispatcher code, functions, data sections, child objects, and solc's mixed
object/data item order.  This tool keeps that front half structural: it asks
solc for `irAst`, `irOptimizedAst`, or standalone Yul source `ast`,
normalizes the JSON Yul AST into bridge JSON or
`EvmCompiler.Solidity.Frontend.Program`, and never reparses pretty-printed Yul
text.  Bytecode/artifact paths use the computed object-image entrypoints; lower
`EvmCompiler.Yul.Program` conversions remain available for proof and debugging
boundaries.
"""

from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field, replace
from pathlib import Path, PurePosixPath
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple, Union


Json = Dict[str, Any]
BRIDGE_JSON_MANIFEST_SCHEMA = "evm-compiler.bridge-json-manifest.v1"
BRIDGE_JSON_SUMMARY_SCHEMA = "evm-compiler.solc-yul-bridge-summary.v1"
BRIDGE_JSON_MANIFEST_SUMMARY_SCHEMA = "evm-compiler.solc-yul-bridge-manifest-summary.v1"
LEAN_BACKEND_CHECK_SCHEMA = "evm-compiler.lean-backend-check.v1"


class ConversionError(Exception):
    """A user-facing error while importing solc's Yul AST."""


def fail(message: str) -> None:
    raise ConversionError(message)


def default_lake() -> str:
    local_lake = Path.home() / ".elan" / "bin" / "lake"
    if local_lake.exists():
        return str(local_lake)
    return "lake"


def lean_string(value: str) -> str:
    try:
        value.encode("ascii")
    except UnicodeEncodeError:
        fail(f"Lean string emission currently expects ASCII Yul names, got {value!r}")
    return json.dumps(value)


def indent(text: str, prefix: str) -> str:
    return "\n".join(prefix + line if line else line for line in text.splitlines())


def lean_list(items: Sequence[str], level: int = 0) -> str:
    if not items:
        return "[]"
    pad = "  " * level
    item_pad = "  " * (level + 1)
    rendered = []
    for item in items:
        rendered.append(indent(item, item_pad))
    return "[\n" + ",\n".join(rendered) + "\n" + pad + "]"


def parse_uint256(value: str) -> int:
    value = value.strip()
    if value.startswith(("0x", "0X")):
        parsed = int(value, 16)
    else:
        parsed = int(value, 10)
    if parsed < 0 or parsed >= 2**256:
        fail(f"Yul literal is outside UInt256 range: {value}")
    return parsed


def parse_uint256_arg(value: str) -> int:
    try:
        return parse_uint256(value)
    except (ConversionError, ValueError) as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def parse_object_layout_entry(value: str) -> "ObjectLayoutEntry":
    name, sep, rest = value.partition("=")
    if not sep or not name:
        fail(
            "Expected object layout entry in the form NAME=OFFSET:SIZE, "
            f"got {value!r}"
        )
    offset_text, sep, size_text = rest.partition(":")
    if not sep or not offset_text or not size_text:
        fail(
            "Expected object layout entry in the form NAME=OFFSET:SIZE, "
            f"got {value!r}"
        )
    return ObjectLayoutEntry(
        name=name,
        offset=parse_uint256(offset_text),
        size=parse_uint256(size_text),
    )


def parse_linker_symbol_entry(value: str) -> "LinkerSymbolEntry":
    name, sep, value_text = value.partition("=")
    if not sep or not name or not value_text:
        fail(f"Expected linker symbol in the form NAME=VALUE, got {value!r}")
    return LinkerSymbolEntry(name=name, value=parse_uint256(value_text))


def parse_standard_json_library_address(
    value: Any,
    source_name: str,
    library_name: str,
) -> int:
    if not isinstance(value, str):
        fail(
            "Malformed solc Standard JSON settings.libraries entry for "
            f"{source_name}:{library_name}: address must be a hex string"
        )
    address = value.strip()
    if address.startswith(("0x", "0X")):
        address = address[2:]
    if not address:
        fail(
            "Malformed solc Standard JSON settings.libraries entry for "
            f"{source_name}:{library_name}: address is empty"
        )
    if not re.fullmatch(r"[0-9a-fA-F]+", address):
        fail(
            "Malformed solc Standard JSON settings.libraries entry for "
            f"{source_name}:{library_name}: address must be hex"
        )
    if len(address) > 40:
        fail(
            "Malformed solc Standard JSON settings.libraries entry for "
            f"{source_name}:{library_name}: address is wider than 20 bytes"
        )
    return int(address, 16)


def standard_json_linker_symbol_entries(
    compiler_input: Json,
) -> List["LinkerSymbolEntry"]:
    settings = compiler_input.get("settings", {})
    if settings is None:
        return []
    if not isinstance(settings, dict):
        fail("Malformed solc Standard JSON input: settings must be an object")
    libraries = settings.get("libraries", {})
    if libraries is None:
        return []
    if not isinstance(libraries, dict):
        fail("Malformed solc Standard JSON input: settings.libraries must be an object")
    entries: List[LinkerSymbolEntry] = []
    for source_name, contracts in libraries.items():
        if not isinstance(source_name, str) or not isinstance(contracts, dict):
            fail(
                "Malformed solc Standard JSON input: settings.libraries maps "
                "source names to contract-address objects"
            )
        for library_name, address in contracts.items():
            if not isinstance(library_name, str):
                fail(
                    "Malformed solc Standard JSON input: settings.libraries "
                    "contract names must be strings"
                )
            entries.append(
                LinkerSymbolEntry(
                    f"{source_name}:{library_name}",
                    parse_standard_json_library_address(
                        address,
                        source_name,
                        library_name,
                    ),
                )
            )
    return entries


def merged_linker_symbol_entries(
    explicit_entries: Sequence[str],
    compiler_input: Optional[Json] = None,
    extra_entries: Sequence["LinkerSymbolEntry"] = (),
) -> List["LinkerSymbolEntry"]:
    merged: Dict[str, LinkerSymbolEntry] = {}
    if compiler_input is not None:
        for entry in standard_json_linker_symbol_entries(compiler_input):
            merged[entry.name] = entry
    for entry in extra_entries:
        merged[entry.name] = entry
    for entry_text in explicit_entries:
        entry = parse_linker_symbol_entry(entry_text)
        merged[entry.name] = entry
    return list(merged.values())


def parse_import_remapping_arg(
    value: str,
    base: Optional[Path] = None,
) -> "ImportRemapping":
    prefix, sep, target_text = value.partition("=")
    if not sep or not prefix or not target_text:
        fail(f"Expected import remapping in the form PREFIX=PATH, got {value!r}")
    target = Path(target_text)
    if base is not None and not target.is_absolute():
        target = base / target
    return ImportRemapping(prefix=prefix, target=target)


def read_import_remappings(
    values: Sequence[str],
    files: Sequence[Path],
) -> List["ImportRemapping"]:
    remappings: List[ImportRemapping] = []
    for path in files:
        try:
            lines = path.read_text().splitlines()
        except FileNotFoundError:
            fail(f"Import remappings file {path} does not exist")
        for line_number, raw_line in enumerate(lines, start=1):
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                remappings.append(
                    parse_import_remapping_arg(line, base=path.parent)
                )
            except ConversionError as exc:
                fail(f"{path}:{line_number}: {exc}")
    remappings.extend(parse_import_remapping_arg(value) for value in values)
    return remappings


def strip_solidity_comments(source: str) -> str:
    result: List[str] = []
    i = 0
    in_string: Optional[str] = None
    while i < len(source):
        ch = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""
        if in_string is not None:
            result.append(ch)
            if ch == "\\" and i + 1 < len(source):
                result.append(source[i + 1])
                i += 2
                continue
            if ch == in_string:
                in_string = None
            i += 1
            continue
        if ch in {"'", '"'}:
            in_string = ch
            result.append(ch)
            i += 1
            continue
        if ch == "/" and nxt == "/":
            while i < len(source) and source[i] not in "\r\n":
                result.append(" ")
                i += 1
            continue
        if ch == "/" and nxt == "*":
            result.extend("  ")
            i += 2
            while i < len(source):
                if source[i] == "*" and i + 1 < len(source) and source[i + 1] == "/":
                    result.extend("  ")
                    i += 2
                    break
                result.append("\n" if source[i] in "\r\n" else " ")
                i += 1
            continue
        result.append(ch)
        i += 1
    return "".join(result)


IMPORT_DIRECTIVE_RE = re.compile(r"\bimport\b(?P<body>[^;]*);", re.S)
SOLIDITY_STRING_RE = re.compile(r"""(?P<literal>'(?:\\.|[^'\\])*'|"(?:\\.|[^"\\])*")""")


def parse_solidity_string_literal(literal: str) -> str:
    try:
        value = ast.literal_eval(literal)
    except (SyntaxError, ValueError) as exc:
        fail(f"Could not parse Solidity import string literal {literal!r}: {exc}")
    if not isinstance(value, str):
        fail(f"Expected Solidity import string literal, got {literal!r}")
    return value


def iter_solidity_import_paths(source: str) -> List[str]:
    stripped = strip_solidity_comments(source)
    paths: List[str] = []
    for match in IMPORT_DIRECTIVE_RE.finditer(stripped):
        literals = [
            parse_solidity_string_literal(literal_match.group("literal"))
            for literal_match in SOLIDITY_STRING_RE.finditer(match.group("body"))
        ]
        if literals:
            paths.append(literals[-1])
    return paths


def normalize_source_name(path: PurePosixPath) -> str:
    parts: List[str] = []
    for part in path.parts:
        if part in {"", "."}:
            continue
        if part == "..":
            if parts and parts[-1] != "..":
                parts.pop()
            else:
                parts.append(part)
            continue
        parts.append(part)
    return "/".join(parts)


def resolve_relative_import_source_name(source_name: str, import_path: str) -> str:
    if not import_path.startswith(("./", "../")):
        return import_path
    base = PurePosixPath(source_name).parent
    if str(base) == ".":
        base = PurePosixPath("")
    return normalize_source_name(base / PurePosixPath(import_path))


def resolve_remapped_import_path(
    import_path: str,
    remappings: Sequence["ImportRemapping"],
) -> Optional[Path]:
    matches = [
        (index, remapping)
        for index, remapping in enumerate(remappings)
        if import_path.startswith(remapping.prefix)
    ]
    if not matches:
        return None
    _index, remapping = max(
        matches,
        key=lambda item: (len(item[1].prefix), item[0]),
    )
    suffix = import_path[len(remapping.prefix) :].lstrip("/")
    if not suffix:
        return remapping.target
    return remapping.target / PurePosixPath(suffix)


def concrete_hex_bytes(value: str, what: str) -> str:
    value = value.strip()
    if value.startswith(("0x", "0X")):
        value = value[2:]
    if len(value) % 2 != 0 or not re.fullmatch(r"[0-9a-fA-F]*", value):
        fail(f"{what} must be concrete even-length hex bytes")
    return value.lower()


def parse_hex_bytes(value: str, what: str) -> List[int]:
    concrete = concrete_hex_bytes(value, what)
    return [int(concrete[i : i + 2], 16) for i in range(0, len(concrete), 2)]


def yul_string_literal_word(value: str) -> int:
    return yul_bytes_literal_word(value.encode("utf-8"))


def yul_bytes_literal_word(data: Sequence[int]) -> int:
    data_bytes = bytes(data)
    if len(data_bytes) > 32:
        fail(
            "Yul string/hex literals used as values must fit in one word; "
            f"got {len(data_bytes)} bytes"
        )
    return int.from_bytes(data_bytes.ljust(32, b"\x00"), "big")


PRIMITIVE_OPS: Dict[str, str] = {
    "stop": "STOP",
    "add": "ADD",
    "mul": "MUL",
    "sub": "SUB",
    "div": "DIV",
    "sdiv": "SDIV",
    "mod": "MOD",
    "smod": "SMOD",
    "addmod": "ADDMOD",
    "mulmod": "MULMOD",
    "exp": "EXP",
    "signextend": "SIGNEXTEND",
    "lt": "LT",
    "gt": "GT",
    "slt": "SLT",
    "sgt": "SGT",
    "eq": "EQ",
    "iszero": "ISZERO",
    "and": "AND",
    "or": "OR",
    "xor": "XOR",
    "not": "NOT",
    "byte": "BYTE",
    "shl": "SHL",
    "shr": "SHR",
    "sar": "SAR",
    "keccak256": "KECCAK256",
    "sha3": "KECCAK256",
    "address": "ADDRESS",
    "balance": "BALANCE",
    "origin": "ORIGIN",
    "caller": "CALLER",
    "callvalue": "CALLVALUE",
    "calldataload": "CALLDATALOAD",
    "calldatasize": "CALLDATASIZE",
    "calldatacopy": "CALLDATACOPY",
    "codesize": "CODESIZE",
    "codecopy": "CODECOPY",
    "gasprice": "GASPRICE",
    "extcodesize": "EXTCODESIZE",
    "extcodecopy": "EXTCODECOPY",
    "returndatasize": "RETURNDATASIZE",
    "returndatacopy": "RETURNDATACOPY",
    "extcodehash": "EXTCODEHASH",
    "blockhash": "BLOCKHASH",
    "coinbase": "COINBASE",
    "timestamp": "TIMESTAMP",
    "number": "NUMBER",
    "prevrandao": "PREVRANDAO",
    "difficulty": "PREVRANDAO",
    "gaslimit": "GASLIMIT",
    "chainid": "CHAINID",
    "selfbalance": "SELFBALANCE",
    "basefee": "BASEFEE",
    "blobhash": "BLOBHASH",
    "blobbasefee": "BLOBBASEFEE",
    "pop": "POP",
    "mload": "MLOAD",
    "mstore": "MSTORE",
    "sload": "SLOAD",
    "sstore": "SSTORE",
    "mstore8": "MSTORE8",
    "msize": "MSIZE",
    "gas": "GAS",
    "tload": "TLOAD",
    "tstore": "TSTORE",
    "mcopy": "MCOPY",
    "log0": "LOG0",
    "log1": "LOG1",
    "log2": "LOG2",
    "log3": "LOG3",
    "log4": "LOG4",
    "create": "CREATE",
    "call": "CALL",
    "callcode": "CALLCODE",
    "return": "RETURN",
    "delegatecall": "DELEGATECALL",
    "create2": "CREATE2",
    "staticcall": "STATICCALL",
    "revert": "REVERT",
    "invalid": "INVALID",
    "selfdestruct": "SELFDESTRUCT",
}

OBJECT_BUILTINS = {
    "datasize",
    "dataoffset",
    "datacopy",
    "setimmutable",
    "loadimmutable",
    "linkersymbol",
    "memoryguard",
}

UNSUPPORTED_DIALECT_BUILTINS = (
    {
        "pc",
        "jump",
        "jumpi",
        "jumpdest",
        "dataloadn",
        "auxdataloadn",
        "eofcreate",
        "returncontract",
        "rjump",
        "rjumpi",
        "callf",
        "retf",
        "jumpf",
    }
    | {f"push{i}" for i in range(33)}
    | {f"dup{i}" for i in range(1, 17)}
    | {f"swap{i}" for i in range(1, 17)}
)

RESERVED_BINDING_NAMES = (
    set(PRIMITIVE_OPS)
    | OBJECT_BUILTINS
    | UNSUPPORTED_DIALECT_BUILTINS
    | {
        "memoryguard",
        "clz",
    }
)

LEAN_EXPR = "EvmYul.Yul.Ast.Expr"
LEAN_STMT = "EvmYul.Yul.Ast.Stmt"
LEAN_FUNCTION = "EvmYul.Yul.Ast.FunctionDefinition"
LEAN_FRONTEND = "EvmCompiler.Solidity.Frontend"

CALL_PRIMITIVE = "primitive"
CALL_USER = "user"
CALL_OBJECT_BUILTIN = "objectBuiltin"
CALL_DIALECT_BUILTIN = "dialectBuiltin"

LEAN_CALL_KIND = {
    CALL_PRIMITIVE: f"{LEAN_FRONTEND}.CallKind.primitive",
    CALL_USER: f"{LEAN_FRONTEND}.CallKind.user",
    CALL_OBJECT_BUILTIN: f"{LEAN_FRONTEND}.CallKind.objectBuiltin",
    CALL_DIALECT_BUILTIN: f"{LEAN_FRONTEND}.CallKind.dialectBuiltin",
}

BACKEND_COMPATIBILITY_PROFILE = "current-yul-compiler"
BACKEND_EXTERNAL_EFFECT_PRIMITIVES = {
    "call",
    "callcode",
    "delegatecall",
    "staticcall",
    "create",
    "create2",
}
BACKEND_EXTERNAL_ACCOUNT_QUERY_PRIMITIVES = {
    "balance",
    "extcodesize",
    "extcodecopy",
    "extcodehash",
}
BACKEND_OBJECT_BUILTINS_REQUIRING_LINKER = {
    "linkersymbol",
}
BACKEND_OBJECT_BUILTINS_COMPUTED = {
    "datasize",
    "dataoffset",
    "datacopy",
    "loadimmutable",
    "setimmutable",
    "memoryguard",
}
BACKEND_EXECUTABLE_OBSERVER_PRIMITIVES: Set[str] = {
    "gas",
    "msize",
}
BACKEND_BLOCKING_PRIMITIVES: Set[str] = set()

BRIDGE_JSON_SCHEMA = "evm-compiler.solc-yul-bridge.v3"
BRIDGE_JSON_PROVENANCE_SCHEMA = "evm-compiler.bridge-json-provenance.v1"
BRIDGE_JSON_FRONTEND_PRODUCER = "solc"
RECOVERED_YUL_AST_OUTPUTS: Dict[Tuple[str, str], str] = {}


def solc_yul_ast_output(optimized: bool) -> str:
    return "irOptimizedAst" if optimized else "irAst"


def solc_yul_text_output(optimized: bool) -> str:
    return "irOptimized" if optimized else "ir"


def solc_standalone_yul_ast_output() -> str:
    return "yulAst"


def contract_frontend_ast_output(
    source_name: str,
    contract_name: str,
    optimized: bool,
) -> str:
    return RECOVERED_YUL_AST_OUTPUTS.get(
        (source_name, contract_name),
        solc_yul_ast_output(optimized),
    )


def bridge_json_frontend_metadata(ast_output: Optional[str]) -> Optional[Json]:
    if ast_output is None:
        return None
    if ast_output not in {"irAst", "irOptimizedAst", "yulAst"}:
        fail(f"Unsupported solc Yul AST output kind: {ast_output!r}")
    return {
        "producer": BRIDGE_JSON_FRONTEND_PRODUCER,
        "ast": ast_output,
    }


def normalize_bridge_json_frontend_metadata(
    frontend: Any,
    label: str,
) -> Optional[Json]:
    if frontend is None:
        return None
    frontend_obj = bridge_object(frontend, label)
    producer = bridge_string(frontend_obj.get("producer"), f"{label}.producer")
    ast_output = bridge_string(frontend_obj.get("ast"), f"{label}.ast")
    if producer != BRIDGE_JSON_FRONTEND_PRODUCER:
        fail(f"Unsupported bridge JSON frontend producer: {producer!r}")
    return bridge_json_frontend_metadata(ast_output)


@dataclass(frozen=True)
class ObjectLayoutEntry:
    name: str
    offset: int
    size: int

    def lean_ir(self) -> str:
        return (
            f"{LEAN_FRONTEND}.ObjectLayout.Entry.mk {lean_string(self.name)} "
            f"(EvmYul.UInt256.ofNat {self.offset}) "
            f"(EvmYul.UInt256.ofNat {self.size})"
        )


@dataclass(frozen=True)
class LinkerSymbolEntry:
    name: str
    value: int

    def lean_ir(self) -> str:
        return (
            "("
            + lean_string(self.name)
            + f", EvmYul.UInt256.ofNat {self.value})"
        )


@dataclass(frozen=True)
class ImportRemapping:
    prefix: str
    target: Path


@dataclass(frozen=True)
class ContractBytecodeArtifact:
    source_name: str
    contract_name: str
    creation_object_name: str
    runtime_object_name: str
    creation_bytecode: str
    runtime_bytecode: str
    runtime_immutable_references: Dict[str, List[Dict[str, int]]] = field(
        default_factory=dict
    )
    backend_compatibility: Optional[Json] = None
    bridge_json: Optional[Json] = None


@dataclass(frozen=True)
class LeanJsonCheckArtifact:
    source_name: str
    contract_name: str
    object_selector: str
    object_name: str
    summary: Json
    frontend: Optional[Json] = None


@dataclass(frozen=True)
class LeanBackendCheckArtifact:
    source_name: str
    contract_name: str
    object_selector: str
    object_name: str
    summary: Json
    frontend: Optional[Json] = None


@dataclass(frozen=True)
class CompiledObjectImage:
    bytecode: str
    immutable_references: Dict[str, List[Dict[str, int]]] = field(
        default_factory=dict
    )


@dataclass(frozen=True)
class Expr:
    def lean(self) -> str:
        raise NotImplementedError

    def lean_ir(self) -> str:
        raise NotImplementedError

    def bridge_json(self) -> Json:
        raise NotImplementedError


@dataclass(frozen=True)
class Lit(Expr):
    value: int

    def lean(self) -> str:
        return f"{LEAN_EXPR}.Lit (EvmYul.UInt256.ofNat {self.value})"

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.Expr.lit (EvmYul.UInt256.ofNat {self.value})"

    def bridge_json(self) -> Json:
        return {"node": "literal", "value": self.value}


@dataclass(frozen=True)
class StringLit(Expr):
    value: str

    def lean(self) -> str:
        return (
            f"{LEAN_EXPR}.Lit "
            f"(EvmYul.UInt256.ofNat {yul_string_literal_word(self.value)})"
        )

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.Expr.stringLit {lean_string(self.value)}"

    def bridge_json(self) -> Json:
        return {"node": "stringLiteral", "value": self.value}


@dataclass(frozen=True)
class BytesLit(Expr):
    bytes: List[int]

    def lean(self) -> str:
        return (
            f"{LEAN_EXPR}.Lit "
            f"(EvmYul.UInt256.ofNat {yul_bytes_literal_word(self.bytes)})"
        )

    def lean_ir(self) -> str:
        bytes_ = lean_list([f"UInt8.ofNat {byte}" for byte in self.bytes], 1)
        return f"{LEAN_FRONTEND}.Expr.bytesLit {bytes_}"

    def bridge_json(self) -> Json:
        return {"node": "bytesLiteral", "bytes": list(self.bytes)}


@dataclass(frozen=True)
class Var(Expr):
    name: str

    def lean(self) -> str:
        return f"{LEAN_EXPR}.Var {lean_string(self.name)}"

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.Expr.var {lean_string(self.name)}"

    def bridge_json(self) -> Json:
        return {"node": "var", "name": self.name}


@dataclass(frozen=True)
class Call(Expr):
    callee: str
    args: List[Expr]
    callee_kind: str

    @property
    def primitive(self) -> bool:
        return self.callee_kind == CALL_PRIMITIVE

    def lean(self) -> str:
        if self.callee_kind == CALL_OBJECT_BUILTIN:
            fail(
                f"Yul object builtin {self.callee!r} is preserved in the bridge AST "
                "but is not representable in the current Lean YulContract entrypoint"
            )
        if self.callee_kind == CALL_DIALECT_BUILTIN:
            fail(
                f"Yul dialect builtin {self.callee!r} is preserved in the bridge AST "
                "but is not representable in the current Lean YulContract entrypoint"
            )
        args = lean_list([arg.lean() for arg in self.args], 1)
        if self.primitive:
            op = PRIMITIVE_OPS[self.callee]
            callee = (
                f"Sum.inl (EvmYul.Operation.{op} : "
                "EvmYul.Operation EvmYul.OperationType.Yul)"
            )
        else:
            callee = f"Sum.inr {lean_string(self.callee)}"
        return f"{LEAN_EXPR}.Call ({callee}) {args}"

    def lean_ir(self) -> str:
        args = lean_list([arg.lean_ir() for arg in self.args], 1)
        return (
            f"{LEAN_FRONTEND}.Expr.call {LEAN_CALL_KIND[self.callee_kind]} "
            f"{lean_string(self.callee)} {args}"
        )

    def bridge_json(self) -> Json:
        return {
            "node": "call",
            "callee": self.callee,
            "calleeKind": self.callee_kind,
            "args": [arg.bridge_json() for arg in self.args],
        }


@dataclass(frozen=True)
class Stmt:
    def lean(self) -> str:
        raise NotImplementedError

    def lean_ir(self) -> str:
        raise NotImplementedError

    def bridge_json(self) -> Json:
        raise NotImplementedError


@dataclass(frozen=True)
class Block(Stmt):
    stmts: List[Stmt]

    def lean(self) -> str:
        return f"{LEAN_STMT}.Block " + lean_stmt_list(self.stmts, 1)

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.Stmt.block " + lean_ir_stmt_list(self.stmts, 1)

    def bridge_json(self) -> Json:
        return {"node": "block", "stmts": [stmt.bridge_json() for stmt in self.stmts]}


@dataclass(frozen=True)
class Let(Stmt):
    names: List[str]
    value: Optional[Expr]

    def lean(self) -> str:
        names = lean_list([lean_string(name) for name in self.names], 1)
        if self.value is None:
            return f"{LEAN_STMT}.Let {names} none"
        return f"{LEAN_STMT}.Let {names} (some ({self.value.lean()}))"

    def lean_ir(self) -> str:
        names = lean_list([lean_string(name) for name in self.names], 1)
        if self.value is None:
            return f"{LEAN_FRONTEND}.Stmt.letDecl {names} none"
        return f"{LEAN_FRONTEND}.Stmt.letDecl {names} (some ({self.value.lean_ir()}))"

    def bridge_json(self) -> Json:
        return {
            "node": "let",
            "names": self.names,
            "value": self.value.bridge_json() if self.value is not None else None,
        }


@dataclass(frozen=True)
class Assign(Stmt):
    names: List[str]
    value: Expr

    def lean(self) -> str:
        names = lean_list([lean_string(name) for name in self.names], 1)
        return f"{LEAN_STMT}.Assign {names} ({self.value.lean()})"

    def lean_ir(self) -> str:
        names = lean_list([lean_string(name) for name in self.names], 1)
        return f"{LEAN_FRONTEND}.Stmt.assign {names} ({self.value.lean_ir()})"

    def bridge_json(self) -> Json:
        return {
            "node": "assign",
            "names": self.names,
            "value": self.value.bridge_json(),
        }


@dataclass(frozen=True)
class ExprStmt(Stmt):
    expr: Expr

    def lean(self) -> str:
        return f"{LEAN_STMT}.ExprStmtCall ({self.expr.lean()})"

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.Stmt.exprStmt ({self.expr.lean_ir()})"

    def bridge_json(self) -> Json:
        return {"node": "exprStmt", "expr": self.expr.bridge_json()}


SWITCH_CASE_WORD = "word"
SWITCH_CASE_STRING = "string"
SWITCH_CASE_BYTES = "bytes"
SWITCH_CASE_BOOL = "bool"


@dataclass(frozen=True)
class SwitchCaseValue:
    kind: str
    value: Union[int, str, Tuple[int, ...], bool]

    def word(self) -> int:
        if self.kind == SWITCH_CASE_WORD:
            if not isinstance(self.value, int) or isinstance(self.value, bool):
                fail(f"Invalid switch word case value: {self.value!r}")
            return self.value
        if self.kind == SWITCH_CASE_STRING:
            if not isinstance(self.value, str):
                fail(f"Invalid switch string case value: {self.value!r}")
            return yul_string_literal_word(self.value)
        if self.kind == SWITCH_CASE_BYTES:
            if not isinstance(self.value, tuple):
                fail(f"Invalid switch bytes case value: {self.value!r}")
            return yul_bytes_literal_word(list(self.value))
        if self.kind == SWITCH_CASE_BOOL:
            if not isinstance(self.value, bool):
                fail(f"Invalid switch bool case value: {self.value!r}")
            return 1 if self.value else 0
        fail(f"Unknown switch case value kind: {self.kind!r}")

    def lean(self) -> str:
        return f"EvmYul.UInt256.ofNat {self.word()}"

    def lean_ir(self) -> str:
        if self.kind == SWITCH_CASE_WORD:
            return (
                f"{LEAN_FRONTEND}.SwitchCaseValue.word "
                f"(EvmYul.UInt256.ofNat {self.word()})"
            )
        if self.kind == SWITCH_CASE_STRING:
            return (
                f"{LEAN_FRONTEND}.SwitchCaseValue.stringLit "
                f"{lean_string(str(self.value))}"
            )
        if self.kind == SWITCH_CASE_BYTES:
            if not isinstance(self.value, tuple):
                fail(f"Invalid switch bytes case value: {self.value!r}")
            bytes_ = lean_list([f"UInt8.ofNat {byte}" for byte in self.value], 1)
            return f"{LEAN_FRONTEND}.SwitchCaseValue.bytesLit {bytes_}"
        if self.kind == SWITCH_CASE_BOOL:
            return (
                f"{LEAN_FRONTEND}.SwitchCaseValue.boolLit "
                f"{str(bool(self.value)).lower()}"
            )
        fail(f"Unknown switch case value kind: {self.kind!r}")

    def bridge_json(self) -> Json:
        if self.kind == SWITCH_CASE_WORD:
            return {"node": "literal", "value": self.word()}
        if self.kind == SWITCH_CASE_STRING:
            return {"node": "stringLiteral", "value": str(self.value)}
        if self.kind == SWITCH_CASE_BYTES:
            if not isinstance(self.value, tuple):
                fail(f"Invalid switch bytes case value: {self.value!r}")
            return {"node": "bytesLiteral", "bytes": list(self.value)}
        if self.kind == SWITCH_CASE_BOOL:
            return {"node": "boolLiteral", "value": bool(self.value)}
        fail(f"Unknown switch case value kind: {self.kind!r}")


@dataclass(frozen=True)
class Switch(Stmt):
    scrutinee: Expr
    cases: List[Tuple[SwitchCaseValue, List[Stmt]]]
    default: List[Stmt]

    def lean(self) -> str:
        cases = lean_list(
            [
                "("
                + value.lean()
                + ", "
                + lean_stmt_list(body, 2)
                + ")"
                for value, body in self.cases
            ],
            1,
        )
        default = lean_stmt_list(self.default, 1)
        return f"{LEAN_STMT}.Switch ({self.scrutinee.lean()}) {cases} {default}"

    def lean_ir(self) -> str:
        cases = lean_list(
            [
                "("
                + value.lean_ir()
                + ", "
                + lean_ir_stmt_list(body, 2)
                + ")"
                for value, body in self.cases
            ],
            1,
        )
        default = lean_ir_stmt_list(self.default, 1)
        return (
            f"{LEAN_FRONTEND}.Stmt.switch ({self.scrutinee.lean_ir()}) "
            f"{cases} {default}"
        )

    def bridge_json(self) -> Json:
        return {
            "node": "switch",
            "scrutinee": self.scrutinee.bridge_json(),
            "cases": [
                {"value": value.bridge_json(), "body": [stmt.bridge_json() for stmt in body]}
                for value, body in self.cases
            ],
            "default": [stmt.bridge_json() for stmt in self.default],
        }


@dataclass(frozen=True)
class For(Stmt):
    pre: List[Stmt]
    cond: Expr
    post: List[Stmt]
    body: List[Stmt]

    def lean(self) -> str:
        loop = (
            f"{LEAN_STMT}.For ({self.cond.lean()}) "
            f"{lean_stmt_list(self.post, 1)} {lean_stmt_list(self.body, 1)}"
        )
        if not self.pre:
            return loop
        stmts = [stmt.lean() for stmt in self.pre] + [loop]
        return f"{LEAN_STMT}.Block {lean_list(stmts, 1)}"

    def lean_ir(self) -> str:
        return (
            f"{LEAN_FRONTEND}.Stmt.forLoop {lean_ir_stmt_list(self.pre, 1)} "
            f"({self.cond.lean_ir()}) "
            f"{lean_ir_stmt_list(self.post, 1)} {lean_ir_stmt_list(self.body, 1)}"
        )

    def bridge_json(self) -> Json:
        return {
            "node": "for",
            "pre": [stmt.bridge_json() for stmt in self.pre],
            "condition": self.cond.bridge_json(),
            "post": [stmt.bridge_json() for stmt in self.post],
            "body": [stmt.bridge_json() for stmt in self.body],
        }


@dataclass(frozen=True)
class If(Stmt):
    cond: Expr
    body: List[Stmt]

    def lean(self) -> str:
        return f"{LEAN_STMT}.If ({self.cond.lean()}) {lean_stmt_list(self.body, 1)}"

    def lean_ir(self) -> str:
        return (
            f"{LEAN_FRONTEND}.Stmt.ifThen ({self.cond.lean_ir()}) "
            f"{lean_ir_stmt_list(self.body, 1)}"
        )

    def bridge_json(self) -> Json:
        return {
            "node": "if",
            "condition": self.cond.bridge_json(),
            "body": [stmt.bridge_json() for stmt in self.body],
        }


@dataclass(frozen=True)
class Control(Stmt):
    name: str

    def lean(self) -> str:
        return f"{LEAN_STMT}.{self.name}"

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.Stmt.{self.name[0].lower() + self.name[1:]}"

    def bridge_json(self) -> Json:
        return {"node": self.name[0].lower() + self.name[1:]}


def lean_stmt_list(stmts: Sequence[Stmt], level: int = 0) -> str:
    return lean_list([stmt.lean() for stmt in stmts], level)


def lean_ir_stmt_list(stmts: Sequence[Stmt], level: int = 0) -> str:
    return lean_list([stmt.lean_ir() for stmt in stmts], level)


@dataclass(frozen=True)
class FunctionDef:
    params: List[str]
    returns: List[str]
    body: List[Stmt]

    def lean(self) -> str:
        params = lean_list([lean_string(name) for name in self.params], 1)
        returns = lean_list([lean_string(name) for name in self.returns], 1)
        body = lean_stmt_list(self.body, 1)
        return f"{LEAN_FUNCTION}.Def {params} {returns} {body}"

    def lean_ir(self) -> str:
        params = lean_list([lean_string(name) for name in self.params], 1)
        returns = lean_list([lean_string(name) for name in self.returns], 1)
        body = lean_ir_stmt_list(self.body, 1)
        return (
            f"{LEAN_FRONTEND}.FunctionDef.mk {params} {returns} {body}"
        )

    def bridge_json(self) -> Json:
        return {
            "params": self.params,
            "returns": self.returns,
            "body": [stmt.bridge_json() for stmt in self.body],
        }


@dataclass(frozen=True)
class FunctionStmt(Stmt):
    name: str
    function: FunctionDef

    def lean(self) -> str:
        return f"{LEAN_STMT}.Block []"

    def lean_ir(self) -> str:
        params = lean_list([lean_string(name) for name in self.function.params], 1)
        returns = lean_list([lean_string(name) for name in self.function.returns], 1)
        body = lean_ir_stmt_list(self.function.body, 1)
        return (
            f"{LEAN_FRONTEND}.Stmt.functionDef {lean_string(self.name)} "
            f"{params} {returns} {body}"
        )

    def bridge_json(self) -> Json:
        return {
            "node": "function",
            "name": self.name,
            "params": self.function.params,
            "returns": self.function.returns,
            "body": [stmt.bridge_json() for stmt in self.function.body],
        }


@dataclass(frozen=True)
class DataSection:
    name: Optional[str]
    bytes: List[int]

    def lean_ir(self) -> str:
        name = "none" if self.name is None else f"(some {lean_string(self.name)})"
        bytes_ = lean_list([f"UInt8.ofNat {byte}" for byte in self.bytes], 1)
        return (
            f"{LEAN_FRONTEND}.DataSection.mk {name} "
            f"{bytes_}"
        )

    def bridge_json(self) -> Json:
        return {"name": self.name, "bytes": self.bytes}


@dataclass(frozen=True)
class ObjectItemRef:
    kind: str
    index: int

    def __post_init__(self) -> None:
        if self.kind not in {"data", "object"}:
            fail(f"Unknown object item ref kind: {self.kind!r}")
        if self.index < 0:
            fail(f"Object item ref index must be nonnegative, got {self.index}")

    def lean_ir(self) -> str:
        return f"{LEAN_FRONTEND}.ObjectItemRef.{self.kind} {self.index}"

    def bridge_json(self) -> Json:
        return {"kind": self.kind, "index": self.index}


@dataclass(frozen=True)
class YulObject:
    name: str
    dispatcher: List[Stmt]
    functions: List[Tuple[str, FunctionDef]]
    data: List[DataSection]
    subobjects: List["YulObject"]
    items: List[ObjectItemRef] = field(default_factory=list)
    scratch_reservation: Optional[Tuple[int, int]] = None

    def lean_ir(self) -> str:
        functions = lean_list(
            [
                "(" + lean_string(name) + ", " + fn.lean_ir() + ")"
                for name, fn in self.functions
            ],
            1,
        )
        data = lean_list([section.lean_ir() for section in self.data], 1)
        objects = lean_list([subobject.lean_ir() for subobject in self.subobjects], 1)
        items = lean_list([item.lean_ir() for item in self.items], 1)
        dispatcher = lean_ir_stmt_list(self.dispatcher, 1)
        memory_contract = self.memory_contract_lean()
        return (
            f"{LEAN_FRONTEND}.Object.mk {lean_string(self.name)} {dispatcher} "
            f"{functions} {data} {objects} {items} {memory_contract}"
        )

    def memory_contract_lean(self) -> str:
        if self.scratch_reservation is None:
            return "EvmCompiler.MemoryContract.unrestricted"
        base, words = self.scratch_reservation
        return (
            "{ scratch? := some "
            f"{{ base := {base}, words := {words} }} }}"
        )

    def bridge_json(self) -> Json:
        artifact: Json = {
            "node": "object",
            "name": self.name,
            "dispatcher": [stmt.bridge_json() for stmt in self.dispatcher],
            "functions": [
                {"name": name, **fn.bridge_json()} for name, fn in self.functions
            ],
            "data": [section.bridge_json() for section in self.data],
            "subobjects": [subobject.bridge_json() for subobject in self.subobjects],
            "items": [item.bridge_json() for item in self.items],
        }
        if self.scratch_reservation is not None:
            base, words = self.scratch_reservation
            artifact["memoryContract"] = {
                "scratch": {"base": base, "words": words}
            }
        return artifact


def requested_scratch_reservation(
    args: argparse.Namespace,
) -> Optional[Tuple[int, int]]:
    base = getattr(args, "scratch_reservation_base", None)
    words = getattr(args, "scratch_reservation_words", None)
    if (base is None) != (words is None):
        fail(
            "--scratch-reservation-base and --scratch-reservation-words "
            "must be provided together"
        )
    if base is None:
        return None
    if words <= 0:
        fail("--scratch-reservation-words must be positive")
    end_exclusive = base + 32 * words
    if base % 32 != 0 or end_exclusive >= 2**256:
        fail(
            "The source scratch reservation must be word-aligned and end "
            "below 2^256"
        )
    return base, words


def with_requested_scratch_reservation(
    obj: YulObject, args: argparse.Namespace
) -> YulObject:
    reservation = requested_scratch_reservation(args)
    if reservation is None:
        return obj
    if obj.scratch_reservation is not None and obj.scratch_reservation != reservation:
        fail(
            "The requested source scratch reservation conflicts with the "
            "reservation already carried by bridge JSON"
        )
    return replace(obj, scratch_reservation=reservation)


def expr_linker_symbol_names(expr: Expr) -> List[str]:
    if isinstance(expr, Call):
        names: List[str] = []
        if (
            expr.callee_kind == CALL_OBJECT_BUILTIN
            and expr.callee == "linkersymbol"
            and len(expr.args) == 1
            and isinstance(expr.args[0], StringLit)
        ):
            names.append(expr.args[0].value)
        for arg in expr.args:
            names.extend(expr_linker_symbol_names(arg))
        return names
    return []


def stmt_linker_symbol_names(stmt: Stmt) -> List[str]:
    if isinstance(stmt, Block):
        names: List[str] = []
        for child in stmt.stmts:
            names.extend(stmt_linker_symbol_names(child))
        return names
    if isinstance(stmt, Let):
        return [] if stmt.value is None else expr_linker_symbol_names(stmt.value)
    if isinstance(stmt, Assign):
        return expr_linker_symbol_names(stmt.value)
    if isinstance(stmt, ExprStmt):
        return expr_linker_symbol_names(stmt.expr)
    if isinstance(stmt, Switch):
        names = expr_linker_symbol_names(stmt.scrutinee)
        for _value, body in stmt.cases:
            for child in body:
                names.extend(stmt_linker_symbol_names(child))
        for child in stmt.default:
            names.extend(stmt_linker_symbol_names(child))
        return names
    if isinstance(stmt, For):
        names = []
        for child in stmt.pre:
            names.extend(stmt_linker_symbol_names(child))
        names.extend(expr_linker_symbol_names(stmt.cond))
        for child in stmt.post:
            names.extend(stmt_linker_symbol_names(child))
        for child in stmt.body:
            names.extend(stmt_linker_symbol_names(child))
        return names
    if isinstance(stmt, If):
        names = expr_linker_symbol_names(stmt.cond)
        for child in stmt.body:
            names.extend(stmt_linker_symbol_names(child))
        return names
    if isinstance(stmt, FunctionStmt):
        return function_linker_symbol_names(stmt.function)
    if isinstance(stmt, Control):
        return []
    fail(f"Unsupported statement while collecting linker symbols: {stmt!r}")


def function_linker_symbol_names(fn: FunctionDef) -> List[str]:
    names: List[str] = []
    for stmt in fn.body:
        names.extend(stmt_linker_symbol_names(stmt))
    return names


def object_linker_symbol_names(obj: YulObject) -> List[str]:
    names: List[str] = []
    for stmt in obj.dispatcher:
        names.extend(stmt_linker_symbol_names(stmt))
    for _name, fn in obj.functions:
        names.extend(function_linker_symbol_names(fn))
    for subobject in obj.subobjects:
        names.extend(object_linker_symbol_names(subobject))
    return names


def unresolved_linker_symbol_names(
    obj: YulObject,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> List[str]:
    explicit = {entry.name for entry in linker_symbols}
    return sorted(set(object_linker_symbol_names(obj)) - explicit)


def linker_symbols_with_zero_defaults(
    obj: YulObject,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> List[LinkerSymbolEntry]:
    merged = {entry.name: entry for entry in linker_symbols}
    for name in unresolved_linker_symbol_names(obj, linker_symbols):
        merged[name] = LinkerSymbolEntry(name, 0)
    return list(merged.values())


@dataclass(frozen=True)
class StandaloneYulDataNameTree:
    name: str
    data_names: List[str]
    subobjects: List["StandaloneYulDataNameTree"]


@dataclass(frozen=True)
class YulSourceToken:
    kind: str
    value: str


def node_src(node: Json) -> str:
    return str(node.get("nativeSrc") or node.get("src") or "<unknown source>")


def decode_yul_string_token(token: str) -> str:
    try:
        decoded = ast.literal_eval(token)
    except (SyntaxError, ValueError) as exc:
        fail(f"Could not decode Yul string token {token!r}: {exc}")
    if not isinstance(decoded, str):
        fail(f"Expected Yul string token, got {token!r}")
    return decoded


def yul_source_tokens(source: str) -> List[YulSourceToken]:
    tokens: List[YulSourceToken] = []
    i = 0
    while i < len(source):
        ch = source[i]
        if ch.isspace():
            i += 1
            continue
        if source.startswith("//", i):
            newline = source.find("\n", i + 2)
            if newline == -1:
                break
            i = newline + 1
            continue
        if source.startswith("/*", i):
            end = source.find("*/", i + 2)
            if end == -1:
                fail("Unterminated block comment while scanning Yul object names")
            i = end + 2
            continue
        if ch == "{":
            tokens.append(YulSourceToken("lbrace", ch))
            i += 1
            continue
        if ch == "}":
            tokens.append(YulSourceToken("rbrace", ch))
            i += 1
            continue
        if source.startswith('hex"', i):
            start = i
            i += 4
            while i < len(source) and source[i] != '"':
                i += 1
            if i >= len(source):
                fail("Unterminated Yul hex string while scanning object names")
            i += 1
            tokens.append(YulSourceToken("hexstring", source[start:i]))
            continue
        if ch == '"':
            start = i
            i += 1
            escaped = False
            while i < len(source):
                current = source[i]
                if escaped:
                    escaped = False
                elif current == "\\":
                    escaped = True
                elif current == '"':
                    i += 1
                    break
                i += 1
            else:
                fail("Unterminated Yul string while scanning object names")
            tokens.append(
                YulSourceToken("string", decode_yul_string_token(source[start:i]))
            )
            continue
        if ch.isascii() and (ch.isalpha() or ch in {"_", "$"}):
            start = i
            i += 1
            while i < len(source):
                current = source[i]
                if current == "." or (
                    current.isascii() and (current.isalnum() or current in {"_", "$"})
                ):
                    i += 1
                else:
                    break
            tokens.append(YulSourceToken("ident", source[start:i]))
            continue
        i += 1
    return tokens


class StandaloneYulObjectNameParser:
    def __init__(self, tokens: Sequence[YulSourceToken]) -> None:
        self.tokens = list(tokens)
        self.index = 0

    def peek(self) -> Optional[YulSourceToken]:
        if self.index >= len(self.tokens):
            return None
        return self.tokens[self.index]

    def pop(self) -> Optional[YulSourceToken]:
        token = self.peek()
        if token is not None:
            self.index += 1
        return token

    def expect(self, kind: str, value: Optional[str] = None) -> YulSourceToken:
        token = self.pop()
        if token is None or token.kind != kind or (
            value is not None and token.value != value
        ):
            expected = kind if value is None else f"{kind} {value!r}"
            got = "<eof>" if token is None else f"{token.kind} {token.value!r}"
            fail(f"Expected {expected} while scanning Yul object names, got {got}")
        return token

    def skip_braced_block(self) -> None:
        self.expect("lbrace")
        depth = 1
        while depth > 0:
            token = self.pop()
            if token is None:
                fail("Unterminated Yul block while scanning object names")
            if token.kind == "lbrace":
                depth += 1
            elif token.kind == "rbrace":
                depth -= 1

    def parse_object(self) -> StandaloneYulDataNameTree:
        self.expect("ident", "object")
        name = self.expect("string").value
        self.expect("lbrace")
        data_names: List[str] = []
        subobjects: List[StandaloneYulDataNameTree] = []
        while True:
            token = self.peek()
            if token is None:
                fail("Unterminated Yul object while scanning data names")
            if token.kind == "rbrace":
                self.pop()
                break
            if token.kind == "ident" and token.value == "code":
                self.pop()
                self.skip_braced_block()
                continue
            if token.kind == "ident" and token.value == "data":
                self.pop()
                data_names.append(self.expect("string").value)
                payload = self.pop()
                if payload is None or payload.kind not in {"string", "hexstring"}:
                    got = (
                        "<eof>"
                        if payload is None
                        else f"{payload.kind} {payload.value!r}"
                    )
                    fail(
                        "Expected Yul data payload while scanning data names, "
                        f"got {got}"
                    )
                continue
            if token.kind == "ident" and token.value == "object":
                subobjects.append(self.parse_object())
                continue
            self.pop()
        return StandaloneYulDataNameTree(name, data_names, subobjects)


def parse_standalone_yul_data_name_tree(source: str) -> StandaloneYulDataNameTree:
    parser = StandaloneYulObjectNameParser(yul_source_tokens(source))
    return parser.parse_object()


def apply_standalone_yul_data_names(
    node: Json,
    tree: StandaloneYulDataNameTree,
) -> None:
    if node.get("nodeType") != "YulObject":
        fail(
            "Expected YulObject while applying data names, "
            f"got {node.get('nodeType')!r}"
        )
    name = raw_object_name(node)
    if name != tree.name:
        fail(
            f"Standalone Yul object-name scan found {tree.name!r}, "
            f"but solc AST has {name!r}"
        )
    data_index = 0
    object_index = 0
    for subobject in node.get("subObjects", []):
        if not isinstance(subobject, dict):
            continue
        node_type = subobject.get("nodeType")
        if node_type == "YulData":
            if subobject.get("name") is None and data_index < len(tree.data_names):
                subobject["name"] = tree.data_names[data_index]
            data_index += 1
        elif node_type == "YulObject":
            if object_index >= len(tree.subobjects):
                fail(
                    f"Standalone Yul object-name scan found too few child objects "
                    f"under {name!r}"
                )
            apply_standalone_yul_data_names(
                subobject,
                tree.subobjects[object_index],
            )
            object_index += 1


def recover_standalone_yul_data_names(root_ast: Json, source: Optional[str]) -> None:
    if source is None:
        return
    tree = parse_standalone_yul_data_name_tree(source)
    apply_standalone_yul_data_names(root_ast, tree)


def typed_names(nodes: Sequence[Json], field: str) -> List[str]:
    names = []
    for entry in nodes:
        name = entry.get("name")
        if not isinstance(name, str):
            fail(f"Expected a name in {field} at {node_src(entry)}")
        names.append(name)
    return names


def generated_identifier_part(name: str) -> str:
    chars = []
    for ch in name:
        if ch.isascii() and (ch.isalnum() or ch in {"_", "$"}):
            chars.append(ch)
        elif ch == ".":
            chars.append("_")
    result = "".join(chars).strip("_")
    return result or "fn"


def valid_yul_identifier(name: str) -> bool:
    if not name:
        return False
    first = name[0]
    if not (first.isascii() and (first.isalpha() or first in {"_", "$"})):
        return False
    previous_dot = False
    for ch in name[1:]:
        if ch == ".":
            if previous_dot:
                return False
            previous_dot = True
            continue
        previous_dot = False
        if not (ch.isascii() and (ch.isalnum() or ch in {"_", "$"})):
            return False
    return not name.endswith(".")


def binding_name_ok(name: str) -> bool:
    return (
        valid_yul_identifier(name)
        and name not in RESERVED_BINDING_NAMES
        and not name.startswith("verbatim")
    )


@dataclass
class ParseContext:
    function_scopes: List[Dict[str, str]] = field(default_factory=list)
    identifier_scopes: List[Set[str]] = field(default_factory=list)
    hoisted_functions: List[Tuple[str, FunctionDef]] = field(default_factory=list)
    used_function_names: Set[str] = field(default_factory=set)
    next_generated_function_id: int = 0
    clz_helper_name: Optional[str] = None
    clz_arg_name: Optional[str] = None
    clz_return_name: Optional[str] = None

    def push_function_scope(self, names: Dict[str, str]) -> None:
        self.function_scopes.append(names)

    def pop_function_scope(self) -> None:
        self.function_scopes.pop()

    def push_identifier_scope(self) -> None:
        self.identifier_scopes.append(set())

    def pop_identifier_scope(self) -> None:
        self.identifier_scopes.pop()

    def identifier_visible(self, name: str) -> bool:
        return any(name in scope for scope in self.identifier_scopes)

    def declare_identifiers(
        self, names: Sequence[str], description: str, node: Json
    ) -> None:
        if not self.identifier_scopes:
            self.push_identifier_scope()
        seen: Set[str] = set()
        for name in names:
            if not binding_name_ok(name):
                fail(
                    f"Invalid Yul {description} name {name!r} at "
                    f"{node_src(node)}"
                )
            if name in seen:
                fail(
                    f"Duplicate Yul {description} name {name!r} at "
                    f"{node_src(node)}"
                )
            if self.identifier_visible(name):
                fail(
                    f"Yul {description} name {name!r} already taken in this "
                    f"scope at {node_src(node)}"
                )
            seen.add(name)
        self.identifier_scopes[-1].update(seen)

    def resolve_function(self, name: str) -> str:
        for scope in reversed(self.function_scopes):
            resolved = scope.get(name)
            if resolved is not None:
                return resolved
        return name

    def fresh_generated_function_name(self, base: str) -> str:
        stem = generated_identifier_part(base)
        while True:
            candidate = f"__yul_gen_{self.next_generated_function_id}_{stem}"
            self.next_generated_function_id += 1
            if candidate not in self.used_function_names:
                self.used_function_names.add(candidate)
                return candidate

    def fresh_non_function_binding_name(self, base: str) -> str:
        stem = generated_identifier_part(base)
        index = 0
        while True:
            candidate = f"__yul_{stem}" if index == 0 else f"__yul_{stem}_{index}"
            index += 1
            if candidate not in self.used_function_names:
                self.used_function_names.add(candidate)
                return candidate

    def ensure_clz_helper(self) -> str:
        if self.clz_helper_name is None:
            self.clz_helper_name = self.fresh_generated_function_name("clz")
            self.clz_arg_name = self.fresh_non_function_binding_name("clz_arg")
            self.clz_return_name = self.fresh_non_function_binding_name("clz_ret")
        return self.clz_helper_name


def clz_helper_function_def(arg_name: str, return_name: str) -> FunctionDef:
    def prim(name: str, args: List[Expr]) -> Call:
        return Call(name, args, CALL_PRIMITIVE)

    def value(name: str) -> Var:
        return Var(name)

    def word(value: int) -> Lit:
        return Lit(value)

    nonzero_body: List[Stmt] = [Assign([return_name], word(0))]
    for check_shift, addend in [
        (128, 128),
        (192, 64),
        (224, 32),
        (240, 16),
        (248, 8),
        (252, 4),
        (254, 2),
        (255, 1),
    ]:
        step: List[Stmt] = [
            Assign(
                [return_name],
                prim("add", [value(return_name), word(addend)]),
            )
        ]
        if addend != 1:
            step.append(
                Assign([arg_name], prim("shl", [word(addend), value(arg_name)]))
            )
        nonzero_body.append(
            If(
                prim("iszero", [prim("shr", [word(check_shift), value(arg_name)])]),
                step,
            )
        )

    return FunctionDef(
        [arg_name],
        [return_name],
        [
            Assign([return_name], word(256)),
            If(value(arg_name), nonzero_body),
        ],
    )


def yul_function_name(node: Json) -> str:
    name = node.get("name")
    if not isinstance(name, str):
        fail(f"Expected Yul function name at {node_src(node)}")
    return name


def classify_call(name: str) -> str:
    if name in PRIMITIVE_OPS:
        return CALL_PRIMITIVE
    if name in OBJECT_BUILTINS:
        return CALL_OBJECT_BUILTIN
    if name in UNSUPPORTED_DIALECT_BUILTINS or name.startswith("verbatim"):
        return CALL_DIALECT_BUILTIN
    return CALL_USER


def yul_literal_word(expr: Expr, what: str) -> int:
    if isinstance(expr, Lit):
        return expr.value
    if isinstance(expr, StringLit):
        return yul_string_literal_word(expr.value)
    if isinstance(expr, BytesLit):
        return yul_bytes_literal_word(expr.bytes)
    fail(f"{what} must be a literal")


def parse_switch_case_value(node: Any, what: str) -> SwitchCaseValue:
    if isinstance(node, dict) and node.get("nodeType") == "YulLiteral":
        kind = node.get("kind")
        value = node.get("value")
        if kind == "bool":
            if isinstance(value, bool):
                return SwitchCaseValue(SWITCH_CASE_BOOL, value)
            if value == "true":
                return SwitchCaseValue(SWITCH_CASE_BOOL, True)
            if value == "false":
                return SwitchCaseValue(SWITCH_CASE_BOOL, False)
        if kind == "string" and isinstance(value, str):
            return SwitchCaseValue(SWITCH_CASE_STRING, value)
        hex_value = node.get("hexValue")
        if kind == "string" and isinstance(hex_value, str):
            return SwitchCaseValue(
                SWITCH_CASE_BYTES,
                tuple(parse_hex_bytes(hex_value, f"{what} hex string literal")),
            )
    literal = parse_expr(node)
    return SwitchCaseValue(SWITCH_CASE_WORD, yul_literal_word(literal, what))


def parse_expr(node: Any, ctx: Optional[ParseContext] = None) -> Expr:
    if not isinstance(node, dict):
        fail(f"Expected Yul expression object, got {node!r}")
    node_type = node.get("nodeType")
    if node_type == "YulLiteral":
        kind = node.get("kind")
        value = node.get("value")
        if kind == "number":
            if isinstance(value, str):
                return Lit(parse_uint256(value))
            if isinstance(value, int) and not isinstance(value, bool):
                return Lit(parse_uint256(str(value)))
        if kind == "bool":
            if isinstance(value, bool):
                return Lit(1 if value else 0)
            if isinstance(value, str):
                if value == "true":
                    return Lit(1)
                if value == "false":
                    return Lit(0)
        if kind == "string" and isinstance(value, str):
            return StringLit(value)
        hex_value = node.get("hexValue")
        if kind == "string" and isinstance(hex_value, str):
            return BytesLit(
                parse_hex_bytes(hex_value, f"Yul hex string literal at {node_src(node)}")
            )
        fail(
            "Unsupported Yul literal kind in solc IR AST; "
            f"got {kind!r} at {node_src(node)}"
        )
    if node_type == "YulIdentifier":
        name = node.get("name")
        if not isinstance(name, str):
            fail(f"Expected Yul identifier name at {node_src(node)}")
        return Var(name)
    if node_type == "YulFunctionCall":
        function_name = node.get("functionName", {}).get("name")
        if not isinstance(function_name, str):
            fail(f"Expected Yul function call name at {node_src(node)}")
        raw_args = node.get("arguments", [])
        if not isinstance(raw_args, list):
            fail(f"Expected Yul function call arguments at {node_src(node)}")
        if function_name == "memoryguard":
            if len(raw_args) != 1:
                fail(f"memoryguard expects one argument at {node_src(node)}")
            return Call(
                "memoryguard",
                [parse_expr(raw_args[0], ctx)],
                CALL_OBJECT_BUILTIN,
            )
        args = [parse_expr(arg, ctx) for arg in raw_args]
        if function_name == "clz":
            if len(args) != 1:
                fail(f"clz expects one argument at {node_src(node)}")
            if ctx is None:
                fail("clz lowering requires a Yul object parse context")
            return Call(ctx.ensure_clz_helper(), args, CALL_USER)
        callee_kind = classify_call(function_name)
        callee = (
            ctx.resolve_function(function_name)
            if ctx is not None and callee_kind == CALL_USER
            else function_name
        )
        return Call(callee, args, callee_kind)
    fail(f"Unsupported Yul expression nodeType {node_type!r} at {node_src(node)}")


def parse_block(
    node: Json,
    ctx: Optional[ParseContext] = None,
    *,
    creates_scope: bool = True,
) -> List[Stmt]:
    if node.get("nodeType") != "YulBlock":
        fail(f"Expected YulBlock, got {node.get('nodeType')!r} at {node_src(node)}")
    statements = node.get("statements", [])
    if not isinstance(statements, list):
        fail(f"Expected statements list in YulBlock at {node_src(node)}")
    if ctx is None:
        return [parse_stmt(stmt) for stmt in statements]

    if creates_scope:
        ctx.push_identifier_scope()
    try:
        local_functions: Dict[str, str] = {}
        for stmt in statements:
            if isinstance(stmt, dict) and stmt.get("nodeType") == "YulFunctionDefinition":
                source_name = yul_function_name(stmt)
                if source_name in local_functions:
                    fail(
                        f"Duplicate Yul function {source_name!r} in block at "
                        f"{node_src(stmt)}"
                    )
                ctx.declare_identifiers([source_name], "function", stmt)
                local_functions[source_name] = ctx.fresh_generated_function_name(
                    source_name
                )

        ctx.push_function_scope(local_functions)
        try:
            for stmt in statements:
                if (
                    isinstance(stmt, dict)
                    and stmt.get("nodeType") == "YulFunctionDefinition"
                ):
                    source_name = yul_function_name(stmt)
                    ctx.hoisted_functions.append(
                        (local_functions[source_name], parse_function_def(stmt, ctx))
                    )
            return [parse_stmt(stmt, ctx) for stmt in statements]
        finally:
            ctx.pop_function_scope()
    finally:
        if creates_scope:
            ctx.pop_identifier_scope()


def block_has_immediate_function_definition(node: Json) -> bool:
    if node.get("nodeType") != "YulBlock":
        return False
    statements = node.get("statements", [])
    return isinstance(statements, list) and any(
        isinstance(stmt, dict) and stmt.get("nodeType") == "YulFunctionDefinition"
        for stmt in statements
    )


def parse_for_init_block_with_scope(pre_node: Json, ctx: ParseContext) -> List[Stmt]:
    if pre_node.get("nodeType") != "YulBlock":
        fail(
            f"Expected YulForLoop pre block, got {pre_node.get('nodeType')!r} "
            f"at {node_src(pre_node)}"
        )
    statements = pre_node.get("statements", [])
    if not isinstance(statements, list):
        fail(f"Expected statements list in YulForLoop pre block at {node_src(pre_node)}")

    local_functions: Dict[str, str] = {}
    for stmt in statements:
        if isinstance(stmt, dict) and stmt.get("nodeType") == "YulFunctionDefinition":
            source_name = yul_function_name(stmt)
            if source_name in local_functions:
                fail(
                    f"Duplicate Yul function {source_name!r} in for-loop init "
                    f"block at {node_src(stmt)}"
                )
            ctx.declare_identifiers([source_name], "function", stmt)
            local_functions[source_name] = ctx.fresh_generated_function_name(
                source_name
            )

    ctx.push_function_scope(local_functions)
    try:
        for stmt in statements:
            if isinstance(stmt, dict) and stmt.get("nodeType") == "YulFunctionDefinition":
                source_name = yul_function_name(stmt)
                ctx.hoisted_functions.append(
                    (local_functions[source_name], parse_function_def(stmt, ctx))
                )
        return [parse_stmt(stmt, ctx) for stmt in statements]
    except BaseException:
        ctx.pop_function_scope()
        raise


def pop_for_init_function_scope_if_present(pre_node: Json, ctx: ParseContext) -> None:
    if block_has_immediate_function_definition(pre_node):
        ctx.pop_function_scope()


def parse_stmt(node: Any, ctx: Optional[ParseContext] = None) -> Stmt:
    if not isinstance(node, dict):
        fail(f"Expected Yul statement object, got {node!r}")
    node_type = node.get("nodeType")
    if node_type == "YulBlock":
        return Block(parse_block(node, ctx))
    if node_type == "YulVariableDeclaration":
        variables = node.get("variables", [])
        if not isinstance(variables, list):
            fail(f"Expected variables list at {node_src(node)}")
        names = typed_names(variables, "variables")
        value = node.get("value")
        parsed_value = parse_expr(value, ctx) if value else None
        if ctx is not None:
            ctx.declare_identifiers(names, "variable", node)
        return Let(names, parsed_value)
    if node_type == "YulAssignment":
        variable_names = node.get("variableNames", [])
        if not isinstance(variable_names, list):
            fail(f"Expected variableNames list at {node_src(node)}")
        return Assign(
            typed_names(variable_names, "variableNames"),
            parse_expr(node["value"], ctx),
        )
    if node_type == "YulExpressionStatement":
        return ExprStmt(parse_expr(node["expression"], ctx))
    if node_type == "YulIf":
        body = node.get("body")
        if not isinstance(body, dict):
            fail(f"Expected YulIf body at {node_src(node)}")
        return If(parse_expr(node["condition"], ctx), parse_block(body, ctx))
    if node_type == "YulSwitch":
        cases: List[Tuple[SwitchCaseValue, List[Stmt]]] = []
        default: List[Stmt] = []
        for case in node.get("cases", []):
            value = case.get("value")
            body_node = case.get("body")
            if not isinstance(body_node, dict):
                fail(f"Expected YulCase body at {node_src(case)}")
            body = parse_block(body_node, ctx)
            if value == "default":
                default = body
            else:
                cases.append(
                    (
                        parse_switch_case_value(
                            value,
                            f"Yul switch case at {node_src(case)}",
                        ),
                        body,
                    )
                )
        return Switch(parse_expr(node["expression"], ctx), cases, default)
    if node_type == "YulForLoop":
        pre_node = node.get("pre")
        post_node = node.get("post")
        body_node = node.get("body")
        if not all(isinstance(part, dict) for part in [pre_node, post_node, body_node]):
            fail(f"Expected YulForLoop pre/post/body blocks at {node_src(node)}")
        if ctx is None:
            pre = parse_block(pre_node)
            return For(
                pre,
                parse_expr(node["condition"]),
                parse_block(post_node),
                parse_block(body_node),
            )

        ctx.push_identifier_scope()
        try:
            if block_has_immediate_function_definition(pre_node):
                pre = parse_for_init_block_with_scope(pre_node, ctx)
                try:
                    loop = For(
                        pre,
                        parse_expr(node["condition"], ctx),
                        parse_block(post_node, ctx),
                        parse_block(body_node, ctx),
                    )
                finally:
                    pop_for_init_function_scope_if_present(pre_node, ctx)
            else:
                pre = parse_block(pre_node, ctx, creates_scope=False)
                loop = For(
                    pre,
                    parse_expr(node["condition"], ctx),
                    parse_block(post_node, ctx),
                    parse_block(body_node, ctx),
                )
        finally:
            ctx.pop_identifier_scope()
        return loop
    if node_type == "YulBreak":
        return Control("Break")
    if node_type == "YulContinue":
        return Control("Continue")
    if node_type == "YulLeave":
        return Control("Leave")
    if node_type == "YulFunctionDefinition":
        return FunctionStmt(yul_function_name(node), parse_function_def(node, ctx))
    fail(f"Unsupported Yul statement nodeType {node_type!r} at {node_src(node)}")


def parse_function_def(node: Json, ctx: Optional[ParseContext] = None) -> FunctionDef:
    body = node.get("body")
    if not isinstance(body, dict):
        fail(f"Expected function body for {node.get('name')!r} at {node_src(node)}")
    params = typed_names(node.get("parameters", []), "parameters")
    returns = typed_names(node.get("returnVariables", []), "returnVariables")
    if ctx is None:
        return FunctionDef(params, returns, parse_block(body))
    ctx.push_identifier_scope()
    try:
        ctx.declare_identifiers(params + returns, "function parameter/result", node)
        return FunctionDef(params, returns, parse_block(body, ctx))
    finally:
        ctx.pop_identifier_scope()


def parse_yul_object(node: Json) -> YulObject:
    if node.get("nodeType") != "YulObject":
        fail(f"Expected YulObject, got {node.get('nodeType')!r}")
    name = node.get("name")
    if not isinstance(name, str):
        fail("Expected YulObject.name")
    code = node.get("code")
    dispatcher: List[Stmt] = []
    functions: List[Tuple[str, FunctionDef]] = []
    if code is not None:
        block = code.get("block") if isinstance(code, dict) else None
        if not isinstance(block, dict):
            fail(f"Expected code.block for YulObject {name!r}")
        statements = block.get("statements", [])
        if not isinstance(statements, list):
            fail(f"Expected statements list in YulObject {name!r} code block")
        ctx = ParseContext()
        top_level_functions: Dict[str, str] = {}
        ctx.push_identifier_scope()
        for stmt in statements:
            if isinstance(stmt, dict) and stmt.get("nodeType") == "YulFunctionDefinition":
                fn_name = yul_function_name(stmt)
                if fn_name in top_level_functions:
                    fail(
                        f"Duplicate top-level Yul function {fn_name!r} in "
                        f"object {name!r} at {node_src(stmt)}"
                    )
                ctx.declare_identifiers([fn_name], "function", stmt)
                top_level_functions[fn_name] = fn_name
                ctx.used_function_names.add(fn_name)

        ctx.push_function_scope(top_level_functions)
        try:
            for stmt in statements:
                if isinstance(stmt, dict) and stmt.get("nodeType") == "YulFunctionDefinition":
                    fn_name = yul_function_name(stmt)
                    functions.append((fn_name, parse_function_def(stmt, ctx)))
                else:
                    dispatcher.append(parse_stmt(stmt, ctx))
        finally:
            ctx.pop_function_scope()
            ctx.pop_identifier_scope()

        functions.extend(ctx.hoisted_functions)
        if ctx.clz_helper_name is not None:
            if ctx.clz_arg_name is None or ctx.clz_return_name is None:
                fail("Internal error: incomplete clz helper context")
            functions.append(
                (
                    ctx.clz_helper_name,
                    clz_helper_function_def(ctx.clz_arg_name, ctx.clz_return_name),
                )
            )

    data = []
    subobjects = []
    items: List[ObjectItemRef] = []
    for subobject in node.get("subObjects", []):
        if not isinstance(subobject, dict):
            fail(f"Expected Yul subobject in object {name!r}")
        node_type = subobject.get("nodeType")
        if node_type == "YulObject":
            index = len(subobjects)
            subobjects.append(parse_yul_object(subobject))
            items.append(ObjectItemRef("object", index))
        elif node_type == "YulData":
            value = subobject.get("value")
            if not isinstance(value, str):
                fail(f"Expected hex value in YulData under object {name!r}")
            data_name = subobject.get("name")
            if data_name is not None and not isinstance(data_name, str):
                fail(f"Expected string name in YulData under object {name!r}")
            index = len(data)
            data.append(
                DataSection(
                    data_name,
                    parse_hex_bytes(value, f"YulData under object {name!r}"),
                )
            )
            items.append(ObjectItemRef("data", index))
        else:
            fail(f"Unsupported Yul subobject nodeType {node_type!r} in object {name!r}")
    return YulObject(name, dispatcher, functions, data, subobjects, items)


def raw_object_name(node: Json) -> str:
    name = node.get("name")
    if not isinstance(name, str):
        fail("Expected YulObject.name")
    return name


def walk_raw_objects(root: Json) -> Iterable[Json]:
    if root.get("nodeType") != "YulObject":
        fail(f"Expected YulObject, got {root.get('nodeType')!r}")
    yield root
    for subobject in root.get("subObjects", []):
        if isinstance(subobject, dict) and subobject.get("nodeType") == "YulObject":
            yield from walk_raw_objects(subobject)


def raw_object_tree_lines(node: Json, level: int = 0) -> List[str]:
    node_type = node.get("nodeType")
    pad = "  " * level
    if node_type == "YulObject":
        name = raw_object_name(node)
        lines = [f"{pad}object {name}"]
        for subobject in node.get("subObjects", []):
            if isinstance(subobject, dict):
                lines.extend(raw_object_tree_lines(subobject, level + 1))
        return lines
    if node_type == "YulData":
        value = node.get("value")
        name = node.get("name")
        byte_count = (
            len(parse_hex_bytes(value, "YulData"))
            if isinstance(value, str)
            else "unknown"
        )
        label = name if isinstance(name, str) else "<anonymous>"
        return [f"{pad}data {label} {byte_count} bytes"]
    return [f"{pad}{node_type or '<unknown>'}"]


def select_raw_object(root: Json, selector: str) -> Json:
    objects = list(walk_raw_objects(root))
    if selector == "creation":
        return root
    if selector == "runtime":
        for obj in objects:
            if obj is not root and raw_object_name(obj).endswith("_deployed"):
                return obj
        return root
    for obj in objects:
        if raw_object_name(obj) == selector:
            return obj
    available = ", ".join(raw_object_name(obj) for obj in objects)
    fail(f"No Yul object named {selector!r}; available objects: {available}")


def walk_objects(root: YulObject) -> Iterable[YulObject]:
    yield root
    for subobject in root.subobjects:
        yield from walk_objects(subobject)


def select_object(root: YulObject, selector: str) -> YulObject:
    objects = list(walk_objects(root))
    if selector == "creation":
        return root
    if selector == "runtime":
        for obj in objects:
            if obj is not root and obj.name.endswith("_deployed"):
                return obj
        return root
    for obj in objects:
        if obj.name == selector:
            return obj
    available = ", ".join(obj.name for obj in objects)
    fail(f"No Yul object named {selector!r}; available objects: {available}")


def bytecode_object(contract_output: Json, deployed: bool) -> Optional[str]:
    evm = contract_output.get("evm")
    if not isinstance(evm, dict):
        return None
    section_name = "deployedBytecode" if deployed else "bytecode"
    section = evm.get(section_name)
    if not isinstance(section, dict):
        return None
    value = section.get("object")
    return value if isinstance(value, str) and value else None


def unique_byte_offset(haystack_hex: str, needle_hex: str, what: str) -> int:
    haystack = concrete_hex_bytes(haystack_hex, "creation bytecode")
    needle = concrete_hex_bytes(needle_hex, what)
    if not needle:
        fail(f"{what} is empty, so no object layout entry can be inferred")
    first = haystack.find(needle)
    if first < 0:
        fail(f"Could not find {what} inside creation bytecode")
    second = haystack.find(needle, first + 2)
    if second >= 0:
        fail(f"Found {what} more than once inside creation bytecode")
    if first % 2 != 0:
        fail(f"Found {what} at a non-byte-aligned offset")
    return first // 2


def infer_object_layout(
    root: YulObject, contract_output: Json
) -> List[ObjectLayoutEntry]:
    runtime_objects = [
        obj for obj in root.subobjects if obj.name.endswith("_deployed")
    ]
    if not runtime_objects:
        return []
    if len(runtime_objects) > 1:
        names = ", ".join(obj.name for obj in runtime_objects)
        fail(f"Cannot auto-infer object layout with multiple runtime objects: {names}")

    creation = bytecode_object(contract_output, deployed=False)
    deployed = bytecode_object(contract_output, deployed=True)
    if creation is None or deployed is None:
        fail("solc output did not include creation and deployed bytecode")

    runtime = runtime_objects[0]
    offset = unique_byte_offset(
        creation,
        deployed,
        f"deployed bytecode for Yul object {runtime.name!r}",
    )
    size = len(concrete_hex_bytes(deployed, "deployed bytecode")) // 2
    return [ObjectLayoutEntry(runtime.name, offset, size)]


def merge_layout_entries(
    explicit: Sequence[ObjectLayoutEntry],
    inferred: Sequence[ObjectLayoutEntry],
) -> List[ObjectLayoutEntry]:
    explicit_names = {entry.name for entry in explicit}
    merged = list(explicit)
    merged.extend(entry for entry in inferred if entry.name not in explicit_names)
    return merged


def contract_to_lean(obj: YulObject, definition: str) -> str:
    function_map_type = (
        "Finmap (fun (_ : EvmYul.Yul.Ast.YulFunctionName) => "
        "AstFunctionDefinition)"
    )
    function_map = f"(\u2205 : {function_map_type})"
    for name, fn in obj.functions:
        function_map += f"\n    |>.insert {lean_string(name)} ({fn.lean()})"

    return f"""def {definition} : EvmCompiler.Yul.Program :=
  {{ contract :=
    {{ dispatcher := {LEAN_STMT}.Block {lean_stmt_list(obj.dispatcher, 3)}
      functions :=
        {function_map}
    }}
  }}
"""


def render_concrete_yul_backend_defs(yul_definition: str) -> str:
    artifact = yul_definition + "CompileArtifact"
    target = yul_definition + "Target"
    bytecode = yul_definition + "Bytecode"
    validate_lean_name(artifact, "compile artifact definition name")
    validate_lean_name(target, "target definition name")
    validate_lean_name(bytecode, "bytecode definition name")
    return f"""
noncomputable def {artifact} :
    Option EvmCompiler.Yul.Program.CompileArtifact :=
  EvmCompiler.Yul.Program.compileArtifact? {yul_definition}

noncomputable def {target} : Option EvmCompiler.Assembly.TargetProgram := do
  let compiled ← {artifact}
  some compiled.target

noncomputable def {bytecode} : Option ByteArray := do
  let target ← {target}
  some (EvmCompiler.Assembly.Bytecode.encodeTarget target)
"""


def render_optional_yul_backend_defs(optional_yul_definition: str) -> str:
    artifact = optional_yul_definition + "CompileArtifact"
    target = optional_yul_definition + "Target"
    bytecode = optional_yul_definition + "Bytecode"
    validate_lean_name(artifact, "compile artifact definition name")
    validate_lean_name(target, "target definition name")
    validate_lean_name(bytecode, "bytecode definition name")
    return f"""
noncomputable def {artifact} :
    Option EvmCompiler.Yul.Program.CompileArtifact := do
  let yul ← {optional_yul_definition}
  EvmCompiler.Yul.Program.compileArtifact? yul

noncomputable def {target} : Option EvmCompiler.Assembly.TargetProgram := do
  let compiled ← {artifact}
  some compiled.target

noncomputable def {bytecode} : Option ByteArray := do
  let target ← {target}
  some (EvmCompiler.Assembly.Bytecode.encodeTarget target)
"""


def render_frontend_unchecked_backend_defs(
    target_definition: str,
    bytecode_definition: str,
    target_expr: str,
    bytecode_expr: str,
) -> str:
    validate_lean_name(target_definition, "unchecked target definition name")
    validate_lean_name(bytecode_definition, "unchecked bytecode definition name")
    return f"""
def {target_definition} : Option EvmCompiler.Assembly.TargetProgram :=
  {target_expr}

def {bytecode_definition} : Option ByteArray :=
  {bytecode_expr}
"""


def validate_lean_name(name: str, what: str) -> None:
    if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", name):
        fail(f"Invalid Lean {what}: {name!r}")


def render_module(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    definition: str,
    namespace: Optional[str],
) -> str:
    validate_lean_name(definition, "definition name")
    namespace_parts = []
    if namespace:
        namespace_parts = namespace.split(".")
        for part in namespace_parts:
            validate_lean_name(part, "namespace component")

    header = f"""import EvmCompiler

/-!
Generated by `scripts/solidity_to_yul_lean.py`.

Source: {source_name}
Contract: {contract_name}
Selected Yul object: {obj.name}
-/

abbrev AstExpr := EvmYul.Yul.Ast.Expr
abbrev AstStmt := EvmYul.Yul.Ast.Stmt
abbrev AstFunctionDefinition := EvmYul.Yul.Ast.FunctionDefinition

"""
    opens = "".join(f"namespace {part}\n" for part in namespace_parts)
    closes = "".join(f"end {part}\n" for part in reversed(namespace_parts))
    return (
        header
        + opens
        + "\n"
        + contract_to_lean(obj, definition)
        + render_concrete_yul_backend_defs(definition)
        + "\n"
        + closes
    )


def render_frontend_module(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    definition: str,
    namespace: Optional[str],
    object_layout: Optional[Sequence[ObjectLayoutEntry]] = None,
    local_data_base: Optional[int] = None,
    linker_symbols: Optional[Sequence[LinkerSymbolEntry]] = None,
) -> str:
    validate_lean_name(definition, "definition name")
    to_yul_definition = definition + "ToYul"
    validate_lean_name(to_yul_definition, "to-Yul definition name")
    to_yul_with_layout_definition = definition + "ToYulWithLayout"
    validate_lean_name(to_yul_with_layout_definition, "to-Yul-with-layout definition name")
    to_yul_with_local_data_base_definition = definition + "ToYulWithLocalDataBase"
    validate_lean_name(
        to_yul_with_local_data_base_definition,
        "to-Yul-with-local-data-base definition name",
    )
    to_objects_definition = definition + "ToObjects"
    validate_lean_name(to_objects_definition, "to-Objects definition name")
    to_objects_with_layout_definition = definition + "ToObjectsWithLayout"
    validate_lean_name(
        to_objects_with_layout_definition,
        "to-Objects-with-layout definition name",
    )
    to_objects_with_local_data_base_definition = (
        definition + "ToObjectsWithLocalDataBase"
    )
    validate_lean_name(
        to_objects_with_local_data_base_definition,
        "to-Objects-with-local-data-base definition name",
    )
    resolved_object_data_definition = definition + "ResolvedObjectData"
    validate_lean_name(
        resolved_object_data_definition,
        "resolved-object-data definition name",
    )
    to_yul_with_computed_object_data_definition = (
        definition + "ToYulWithComputedObjectData"
    )
    validate_lean_name(
        to_yul_with_computed_object_data_definition,
        "to-Yul-with-computed-object-data definition name",
    )
    to_objects_with_computed_object_data_definition = (
        definition + "ToObjectsWithComputedObjectData"
    )
    validate_lean_name(
        to_objects_with_computed_object_data_definition,
        "to-Objects-with-computed-object-data definition name",
    )
    compile_artifact_with_computed_object_data_definition = (
        definition + "CompileArtifactWithComputedObjectData"
    )
    validate_lean_name(
        compile_artifact_with_computed_object_data_definition,
        "compile-artifact-with-computed-object-data definition name",
    )
    namespace_parts = []
    if namespace:
        namespace_parts = namespace.split(".")
        for part in namespace_parts:
            validate_lean_name(part, "namespace component")

    program = (
        f"{LEAN_FRONTEND}.Program.mk {lean_string(source_name)} "
        f"{lean_string(contract_name)} ({obj.lean_ir()})"
    )
    header = f"""import EvmCompiler.Solidity.Frontend
import EvmCompiler.Assembly.Bytecode

/-!
Generated by `scripts/solidity_to_yul_lean.py --format lean-ir`.

Source: {source_name}
Contract: {contract_name}
Selected Yul object: {obj.name}
-/

"""
    opens = "".join(f"namespace {part}\n" for part in namespace_parts)
    closes = "".join(f"end {part}\n" for part in reversed(namespace_parts))
    body = f"""def {definition} : {LEAN_FRONTEND}.Program :=
  {program}

def {to_yul_definition} : Option EvmCompiler.Yul.Program :=
  {definition}.toYulProgram?

noncomputable def {to_objects_definition} : Option EvmCompiler.Objects.Program :=
  {definition}.toObjects?
"""
    body += render_frontend_unchecked_backend_defs(
        definition + "UncheckedTarget",
        definition + "UncheckedBytecode",
        f"{definition}.compileUnchecked?",
        f"{definition}.bytecodeUnchecked?",
    )
    bytecode_image_definition = definition + "UncheckedBytecodeImage"
    object_image_definition = definition + "UncheckedObjectImage"
    checked_bytecode_image_definition = definition + "CheckedBytecodeImage"
    checked_object_image_definition = definition + "CheckedObjectImage"
    validate_lean_name(bytecode_image_definition, "unchecked bytecode image definition name")
    validate_lean_name(object_image_definition, "unchecked object image definition name")
    validate_lean_name(
        checked_bytecode_image_definition,
        "checked bytecode image definition name",
    )
    validate_lean_name(
        checked_object_image_definition,
        "checked object image definition name",
    )
    body += f"""
def {object_image_definition} : Option {LEAN_FRONTEND}.ObjectImage :=
  {definition}.object.bytecodeImageUnchecked?

def {bytecode_image_definition} : Option ByteArray :=
  Option.map
    (fun image => EvmCompiler.Assembly.Bytecode.ofList image.bytes)
    {object_image_definition}

noncomputable def {checked_object_image_definition} :
    Option {LEAN_FRONTEND}.ObjectImage :=
  {definition}.object.bytecodeImageChecked?

noncomputable def {checked_bytecode_image_definition} : Option ByteArray :=
  Option.map
    (fun image => EvmCompiler.Assembly.Bytecode.ofList image.bytes)
    {checked_object_image_definition}
"""
    linker_entries = list(linker_symbols or [])
    linker_symbols_definition = definition + "LinkerSymbols"
    object_image_with_linkers_definition = (
        definition + "UncheckedObjectImageWithLinkerSymbols"
    )
    bytecode_image_with_linkers_definition = (
        definition + "UncheckedBytecodeImageWithLinkerSymbols"
    )
    checked_object_image_with_linkers_definition = (
        definition + "CheckedObjectImageWithLinkerSymbols"
    )
    checked_bytecode_image_with_linkers_definition = (
        definition + "CheckedBytecodeImageWithLinkerSymbols"
    )
    validate_lean_name(linker_symbols_definition, "linker-symbols definition name")
    validate_lean_name(
        object_image_with_linkers_definition,
        "unchecked object image with linker symbols definition name",
    )
    validate_lean_name(
        bytecode_image_with_linkers_definition,
        "unchecked bytecode image with linker symbols definition name",
    )
    validate_lean_name(
        checked_object_image_with_linkers_definition,
        "checked object image with linker symbols definition name",
    )
    validate_lean_name(
        checked_bytecode_image_with_linkers_definition,
        "checked bytecode image with linker symbols definition name",
    )
    linker_symbols_rendered = lean_list(
        [entry.lean_ir() for entry in linker_entries],
        1,
    )
    body += f"""
def {linker_symbols_definition} :
    List ({LEAN_FRONTEND}.Name × {LEAN_FRONTEND}.Word) :=
  {linker_symbols_rendered}

def {object_image_with_linkers_definition} :
    Option {LEAN_FRONTEND}.ObjectImage :=
  {definition}.object.bytecodeImageUncheckedWithLinkerSymbols?
    {linker_symbols_definition}

def {bytecode_image_with_linkers_definition} : Option ByteArray :=
  Option.map
    (fun image => EvmCompiler.Assembly.Bytecode.ofList image.bytes)
    {object_image_with_linkers_definition}

noncomputable def {checked_object_image_with_linkers_definition} :
    Option {LEAN_FRONTEND}.ObjectImage :=
  {definition}.object.bytecodeImageCheckedWithLinkerSymbols?
    {linker_symbols_definition}

noncomputable def {checked_bytecode_image_with_linkers_definition} :
    Option ByteArray :=
  Option.map
    (fun image => EvmCompiler.Assembly.Bytecode.ofList image.bytes)
    {checked_object_image_with_linkers_definition}

def {resolved_object_data_definition} :
    Option {LEAN_FRONTEND}.Program :=
  {definition}.resolveObjectBuiltinsWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}

def {to_yul_with_computed_object_data_definition} :
    Option EvmCompiler.Yul.Program :=
  {definition}.toYulProgramWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}

noncomputable def {to_objects_with_computed_object_data_definition} :
    Option EvmCompiler.Objects.Program :=
  {definition}.toObjectsWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}

noncomputable def {compile_artifact_with_computed_object_data_definition} :
    Option EvmCompiler.Objects.Program.CompileArtifact :=
  {definition}.compileArtifactWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}
"""
    body += render_optional_yul_backend_defs(
        to_yul_with_computed_object_data_definition
    )
    body += render_optional_yul_backend_defs(to_yul_definition)
    layout_entries = list(object_layout or [])
    layout = (
        f"{LEAN_FRONTEND}.ObjectLayout.mk "
        + lean_list([entry.lean_ir() for entry in layout_entries], 1)
    )
    body += f"""
def objectLayout : {LEAN_FRONTEND}.ObjectLayout :=
  {layout}

def {to_yul_with_layout_definition} : Option EvmCompiler.Yul.Program :=
  {definition}.toYulProgramWithLayout? objectLayout

noncomputable def {to_objects_with_layout_definition} :
    Option EvmCompiler.Objects.Program :=
  {definition}.toObjectsWithLayout? objectLayout
"""
    body += render_frontend_unchecked_backend_defs(
        definition + "UncheckedTargetWithLayout",
        definition + "UncheckedBytecodeWithLayout",
        f"{definition}.compileUncheckedWithLayout? objectLayout",
        f"{definition}.bytecodeUncheckedWithLayout? objectLayout",
    )
    body += render_optional_yul_backend_defs(to_yul_with_layout_definition)
    if local_data_base is not None:
        body += f"""
def localDataBase : Nat :=
  {local_data_base}

def {to_yul_with_local_data_base_definition} : Option EvmCompiler.Yul.Program :=
  {definition}.toYulProgramWithLocalDataBase? objectLayout localDataBase

noncomputable def {to_objects_with_local_data_base_definition} :
    Option EvmCompiler.Objects.Program :=
  {definition}.toObjectsWithLocalDataBase? objectLayout localDataBase
"""
        body += render_frontend_unchecked_backend_defs(
            definition + "UncheckedTargetWithLocalDataBase",
            definition + "UncheckedBytecodeWithLocalDataBase",
            f"{definition}.compileUncheckedWithLocalDataBase? "
            "objectLayout localDataBase",
            f"{definition}.bytecodeUncheckedWithLocalDataBase? "
            "objectLayout localDataBase",
        )
        body += render_optional_yul_backend_defs(
            to_yul_with_local_data_base_definition
        )
    return header + opens + "\n" + body + "\n" + closes


def render_frontend_json_module(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    definition: str,
    namespace: Optional[str],
    object_layout: Optional[Sequence[ObjectLayoutEntry]] = None,
    local_data_base: Optional[int] = None,
    linker_symbols: Optional[Sequence[LinkerSymbolEntry]] = None,
) -> str:
    validate_lean_name(definition, "definition name")
    json_definition = definition + "Json"
    decode_definition = definition + "Decode"
    to_yul_definition = definition + "ToYul"
    to_yul_with_layout_definition = definition + "ToYulWithLayout"
    to_yul_with_local_data_base_definition = definition + "ToYulWithLocalDataBase"
    to_objects_definition = definition + "ToObjects"
    to_objects_with_layout_definition = definition + "ToObjectsWithLayout"
    to_objects_with_local_data_base_definition = (
        definition + "ToObjectsWithLocalDataBase"
    )
    checked_object_image_definition = definition + "CheckedObjectImage"
    checked_bytecode_image_definition = definition + "CheckedBytecodeImage"
    resolved_object_data_definition = definition + "ResolvedObjectData"
    to_yul_with_computed_object_data_definition = (
        definition + "ToYulWithComputedObjectData"
    )
    to_objects_with_computed_object_data_definition = (
        definition + "ToObjectsWithComputedObjectData"
    )
    compile_artifact_with_computed_object_data_definition = (
        definition + "CompileArtifactWithComputedObjectData"
    )
    for generated_name, what in [
        (json_definition, "JSON definition name"),
        (decode_definition, "JSON decode definition name"),
        (to_yul_definition, "to-Yul definition name"),
        (to_yul_with_layout_definition, "to-Yul-with-layout definition name"),
        (
            to_yul_with_local_data_base_definition,
            "to-Yul-with-local-data-base definition name",
        ),
        (to_objects_definition, "to-Objects definition name"),
        (to_objects_with_layout_definition, "to-Objects-with-layout definition name"),
        (
            to_objects_with_local_data_base_definition,
            "to-Objects-with-local-data-base definition name",
        ),
        (checked_object_image_definition, "checked object image definition name"),
        (
            checked_bytecode_image_definition,
            "checked bytecode image definition name",
        ),
        (resolved_object_data_definition, "resolved-object-data definition name"),
        (
            to_yul_with_computed_object_data_definition,
            "to-Yul-with-computed-object-data definition name",
        ),
        (
            to_objects_with_computed_object_data_definition,
            "to-Objects-with-computed-object-data definition name",
        ),
        (
            compile_artifact_with_computed_object_data_definition,
            "compile-artifact-with-computed-object-data definition name",
        ),
    ]:
        validate_lean_name(generated_name, what)

    namespace_parts = []
    if namespace:
        namespace_parts = namespace.split(".")
        for part in namespace_parts:
            validate_lean_name(part, "namespace component")

    bridge_json = render_bridge_json(obj, source_name, contract_name)
    header = f"""import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.Assembly.Bytecode

/-!
Generated by `scripts/solidity_to_yul_lean.py --format lean-json-ir`.

Source: {source_name}
Contract: {contract_name}
Selected Yul object: {obj.name}
-/

"""
    opens = "".join(f"namespace {part}\n" for part in namespace_parts)
    closes = "".join(f"end {part}\n" for part in reversed(namespace_parts))
    body = f"""def {json_definition} : String :=
  {lean_string(bridge_json)}

def {decode_definition} :
    Except String EvmCompiler.Solidity.Frontend.Program :=
  EvmCompiler.Solidity.Frontend.BridgeJson.parseProgram? {json_definition}

def {definition} : Option EvmCompiler.Solidity.Frontend.Program :=
  match {decode_definition} with
  | .ok program => some program
  | .error _ => none

def {to_yul_definition} : Option EvmCompiler.Yul.Program := do
  let program ← {definition}
  program.toYulProgram?

noncomputable def {to_objects_definition} : Option EvmCompiler.Objects.Program := do
  let program ← {definition}
  program.toObjects?

def {definition}UncheckedTarget : Option EvmCompiler.Assembly.TargetProgram := do
  let program ← {definition}
  program.compileUnchecked?

def {definition}UncheckedBytecode : Option ByteArray := do
  let program ← {definition}
  program.bytecodeUnchecked?

def {definition}UncheckedObjectImage :
    Option EvmCompiler.Solidity.Frontend.ObjectImage := do
  let program ← {definition}
  program.object.bytecodeImageUnchecked?

def {definition}UncheckedBytecodeImage : Option ByteArray := do
  let image ← {definition}UncheckedObjectImage
  some (EvmCompiler.Assembly.Bytecode.ofList image.bytes)

noncomputable def {checked_object_image_definition} :
    Option EvmCompiler.Solidity.Frontend.ObjectImage := do
  let program ← {definition}
  program.object.bytecodeImageChecked?

noncomputable def {checked_bytecode_image_definition} : Option ByteArray := do
  let image ← {checked_object_image_definition}
  some (EvmCompiler.Assembly.Bytecode.ofList image.bytes)
"""
    linker_entries = list(linker_symbols or [])
    linker_symbols_definition = definition + "LinkerSymbols"
    object_image_with_linkers_definition = (
        definition + "UncheckedObjectImageWithLinkerSymbols"
    )
    bytecode_image_with_linkers_definition = (
        definition + "UncheckedBytecodeImageWithLinkerSymbols"
    )
    checked_object_image_with_linkers_definition = (
        definition + "CheckedObjectImageWithLinkerSymbols"
    )
    checked_bytecode_image_with_linkers_definition = (
        definition + "CheckedBytecodeImageWithLinkerSymbols"
    )
    validate_lean_name(linker_symbols_definition, "linker-symbols definition name")
    validate_lean_name(
        object_image_with_linkers_definition,
        "unchecked object image with linker symbols definition name",
    )
    validate_lean_name(
        bytecode_image_with_linkers_definition,
        "unchecked bytecode image with linker symbols definition name",
    )
    validate_lean_name(
        checked_object_image_with_linkers_definition,
        "checked object image with linker symbols definition name",
    )
    validate_lean_name(
        checked_bytecode_image_with_linkers_definition,
        "checked bytecode image with linker symbols definition name",
    )
    linker_symbols_rendered = lean_list(
        [entry.lean_ir() for entry in linker_entries],
        1,
    )
    body += f"""
def {linker_symbols_definition} :
    List (EvmCompiler.Solidity.Frontend.Name × EvmCompiler.Solidity.Frontend.Word) :=
  {linker_symbols_rendered}

def {object_image_with_linkers_definition} :
    Option EvmCompiler.Solidity.Frontend.ObjectImage := do
  let program ← {definition}
  program.object.bytecodeImageUncheckedWithLinkerSymbols?
    {linker_symbols_definition}

def {bytecode_image_with_linkers_definition} : Option ByteArray := do
  let image ← {object_image_with_linkers_definition}
  some (EvmCompiler.Assembly.Bytecode.ofList image.bytes)

noncomputable def {checked_object_image_with_linkers_definition} :
    Option EvmCompiler.Solidity.Frontend.ObjectImage := do
  let program ← {definition}
  program.object.bytecodeImageCheckedWithLinkerSymbols?
    {linker_symbols_definition}

noncomputable def {checked_bytecode_image_with_linkers_definition} :
    Option ByteArray := do
  let image ← {checked_object_image_with_linkers_definition}
  some (EvmCompiler.Assembly.Bytecode.ofList image.bytes)

def {resolved_object_data_definition} :
    Option EvmCompiler.Solidity.Frontend.Program := do
  let program ← {definition}
  program.resolveObjectBuiltinsWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}

def {to_yul_with_computed_object_data_definition} :
    Option EvmCompiler.Yul.Program := do
  let program ← {definition}
  program.toYulProgramWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}

noncomputable def {to_objects_with_computed_object_data_definition} :
    Option EvmCompiler.Objects.Program := do
  let program ← {definition}
  program.toObjectsWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}

noncomputable def {compile_artifact_with_computed_object_data_definition} :
    Option EvmCompiler.Objects.Program.CompileArtifact := do
  let program ← {definition}
  program.compileArtifactWithComputedObjectDataAndLinkerSymbols?
    {linker_symbols_definition}
"""
    body += render_optional_yul_backend_defs(
        to_yul_with_computed_object_data_definition
    )
    body += render_optional_yul_backend_defs(to_yul_definition)
    layout_entries = list(object_layout or [])
    layout = (
        f"EvmCompiler.Solidity.Frontend.ObjectLayout.mk "
        + lean_list([entry.lean_ir() for entry in layout_entries], 1)
    )
    body += f"""
def objectLayout : EvmCompiler.Solidity.Frontend.ObjectLayout :=
  {layout}

def {to_yul_with_layout_definition} : Option EvmCompiler.Yul.Program := do
  let program ← {definition}
  program.toYulProgramWithLayout? objectLayout

noncomputable def {to_objects_with_layout_definition} :
    Option EvmCompiler.Objects.Program := do
  let program ← {definition}
  program.toObjectsWithLayout? objectLayout

def {definition}UncheckedTargetWithLayout :
    Option EvmCompiler.Assembly.TargetProgram := do
  let program ← {definition}
  program.compileUncheckedWithLayout? objectLayout

def {definition}UncheckedBytecodeWithLayout : Option ByteArray := do
  let program ← {definition}
  program.bytecodeUncheckedWithLayout? objectLayout
"""
    body += render_optional_yul_backend_defs(to_yul_with_layout_definition)
    if local_data_base is not None:
        body += f"""
def localDataBase : Nat :=
  {local_data_base}

def {to_yul_with_local_data_base_definition} : Option EvmCompiler.Yul.Program := do
  let program ← {definition}
  program.toYulProgramWithLocalDataBase? objectLayout localDataBase

noncomputable def {to_objects_with_local_data_base_definition} :
    Option EvmCompiler.Objects.Program := do
  let program ← {definition}
  program.toObjectsWithLocalDataBase? objectLayout localDataBase

def {definition}UncheckedTargetWithLocalDataBase :
    Option EvmCompiler.Assembly.TargetProgram := do
  let program ← {definition}
  program.compileUncheckedWithLocalDataBase? objectLayout localDataBase

def {definition}UncheckedBytecodeWithLocalDataBase : Option ByteArray := do
  let program ← {definition}
  program.bytecodeUncheckedWithLocalDataBase? objectLayout localDataBase
"""
        body += render_optional_yul_backend_defs(
            to_yul_with_local_data_base_definition
        )
    return header + opens + "\n" + body + "\n" + closes


def render_bridge_json(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    ast_output: Optional[str] = None,
) -> str:
    artifact: Json = {
        "schema": BRIDGE_JSON_SCHEMA,
        "source": source_name,
        "contract": contract_name,
        "selectedObject": obj.bridge_json(),
    }
    frontend = bridge_json_frontend_metadata(ast_output)
    if frontend is not None:
        artifact["frontend"] = frontend
    return (
        json.dumps(
            artifact,
            indent=2,
        )
        + "\n"
    )


def sorted_counter_entries(counter: Counter[str]) -> List[Json]:
    return [
        {"name": name, "count": count}
        for name, count in sorted(counter.items())
    ]


def increment_nested(counter: Counter[str], key: str, amount: int = 1) -> None:
    counter[key] += amount


def collect_expr_summary(
    expr: Expr,
    expr_counts: Counter[str],
    call_kind_counts: Counter[str],
    call_name_counts: Dict[str, Counter[str]],
) -> None:
    if isinstance(expr, Lit):
        increment_nested(expr_counts, "literal")
        return
    if isinstance(expr, StringLit):
        increment_nested(expr_counts, "stringLiteral")
        return
    if isinstance(expr, BytesLit):
        increment_nested(expr_counts, "bytesLiteral")
        return
    if isinstance(expr, Var):
        increment_nested(expr_counts, "var")
        return
    if isinstance(expr, Call):
        increment_nested(expr_counts, "call")
        increment_nested(call_kind_counts, expr.callee_kind)
        call_name_counts.setdefault(expr.callee_kind, Counter())[expr.callee] += 1
        for arg in expr.args:
            collect_expr_summary(
                arg,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        return
    fail(f"Unsupported expression in bridge summary: {expr!r}")


def collect_stmt_summary(
    stmt: Stmt,
    stmt_counts: Counter[str],
    expr_counts: Counter[str],
    call_kind_counts: Counter[str],
    call_name_counts: Dict[str, Counter[str]],
) -> None:
    if isinstance(stmt, Block):
        increment_nested(stmt_counts, "block")
        for child in stmt.stmts:
            collect_stmt_summary(
                child,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        return
    if isinstance(stmt, Let):
        increment_nested(stmt_counts, "let")
        if stmt.value is not None:
            collect_expr_summary(
                stmt.value,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        return
    if isinstance(stmt, Assign):
        increment_nested(stmt_counts, "assign")
        collect_expr_summary(
            stmt.value,
            expr_counts,
            call_kind_counts,
            call_name_counts,
        )
        return
    if isinstance(stmt, ExprStmt):
        increment_nested(stmt_counts, "exprStmt")
        collect_expr_summary(
            stmt.expr,
            expr_counts,
            call_kind_counts,
            call_name_counts,
        )
        return
    if isinstance(stmt, FunctionStmt):
        increment_nested(stmt_counts, "function")
        return
    if isinstance(stmt, Switch):
        increment_nested(stmt_counts, "switch")
        collect_expr_summary(
            stmt.scrutinee,
            expr_counts,
            call_kind_counts,
            call_name_counts,
        )
        for _case_value, body in stmt.cases:
            for child in body:
                collect_stmt_summary(
                    child,
                    stmt_counts,
                    expr_counts,
                    call_kind_counts,
                    call_name_counts,
                )
        for child in stmt.default:
            collect_stmt_summary(
                child,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        return
    if isinstance(stmt, For):
        increment_nested(stmt_counts, "for")
        for child in stmt.pre:
            collect_stmt_summary(
                child,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        collect_expr_summary(
            stmt.cond,
            expr_counts,
            call_kind_counts,
            call_name_counts,
        )
        for child in stmt.post:
            collect_stmt_summary(
                child,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        for child in stmt.body:
            collect_stmt_summary(
                child,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        return
    if isinstance(stmt, If):
        increment_nested(stmt_counts, "if")
        collect_expr_summary(
            stmt.cond,
            expr_counts,
            call_kind_counts,
            call_name_counts,
        )
        for child in stmt.body:
            collect_stmt_summary(
                child,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        return
    if isinstance(stmt, Control):
        increment_nested(stmt_counts, stmt.name[0].lower() + stmt.name[1:])
        return
    fail(f"Unsupported statement in bridge summary: {stmt!r}")


def bridge_summary_hint_strings(
    obj: YulObject,
    call_kind_counts: Counter[str],
    call_name_counts: Dict[str, Counter[str]],
) -> List[str]:
    hints = []
    if call_kind_counts.get(CALL_DIALECT_BUILTIN, 0) > 0:
        hints.append(
            "unsupported-dialect-builtins-present: bridge JSON preserves "
            "pc/raw-EVM/verbatim/EOF dialect calls, but checked executable lowering "
            "rejects them"
        )
    object_builtin_names = set(call_name_counts.get(CALL_OBJECT_BUILTIN, Counter()))
    unresolved_object_builtins = sorted(
        object_builtin_names & BACKEND_OBJECT_BUILTINS_REQUIRING_LINKER
    )
    computed_object_builtins = sorted(
        object_builtin_names & BACKEND_OBJECT_BUILTINS_COMPUTED
    )
    if unresolved_object_builtins:
        hints.append(
            "linker-symbols-present: executable lowering needs an explicit "
            "linker-symbol map"
        )
    if computed_object_builtins:
        hints.append(
            "object-builtins-computed: datasize/dataoffset/datacopy/immutable/"
            "memoryguard builtins are resolved by the computed object-image path"
        )
    primitive_calls = call_name_counts.get(CALL_PRIMITIVE, Counter())
    external_primitives = sorted(
        name
        for name in primitive_calls
        if name in {"call", "callcode", "delegatecall", "staticcall", "create", "create2"}
    )
    if external_primitives:
        hints.append(
            "external-effect-primitives-present: "
            + ", ".join(external_primitives)
        )
    account_query_primitives = sorted(
        name
        for name in primitive_calls
        if name in BACKEND_EXTERNAL_ACCOUNT_QUERY_PRIMITIVES
    )
    if account_query_primitives:
        hints.append(
            "external-account-query-primitives-present: "
            + ", ".join(account_query_primitives)
        )
    if obj.subobjects:
        hints.append(
            "subobjects-present: bridge JSON preserves the object tree; "
            "executable bytecode support depends on the current object-image path"
        )
    if obj.data:
        hints.append(
            "data-sections-present: bridge JSON preserves typed data bytes and "
            "object/data item order"
        )
    return hints


def bridge_summary_backend_compatibility(
    call_name_counts: Dict[str, Counter[str]],
) -> Json:
    primitive_calls = call_name_counts.get(CALL_PRIMITIVE, Counter())
    object_builtin_calls = call_name_counts.get(CALL_OBJECT_BUILTIN, Counter())
    dialect_builtin_calls = call_name_counts.get(CALL_DIALECT_BUILTIN, Counter())
    unsupported_primitives = sorted(
        name for name in primitive_calls if name in BACKEND_BLOCKING_PRIMITIVES
    )
    object_builtin_names = sorted(object_builtin_calls)
    dialect_builtin_names = sorted(dialect_builtin_calls)
    linker_object_builtins = sorted(
        name for name in object_builtin_names
        if name in BACKEND_OBJECT_BUILTINS_REQUIRING_LINKER
    )
    computed_object_builtins = sorted(
        name for name in object_builtin_names
        if name in BACKEND_OBJECT_BUILTINS_COMPUTED
    )
    notes = []
    external_primitives = sorted(
        name for name in primitive_calls
        if name in BACKEND_EXTERNAL_EFFECT_PRIMITIVES
    )
    account_query_primitives = sorted(
        name for name in primitive_calls
        if name in BACKEND_EXTERNAL_ACCOUNT_QUERY_PRIMITIVES
    )
    executable_observer_primitives = sorted(
        name for name in primitive_calls
        if name in BACKEND_EXECUTABLE_OBSERVER_PRIMITIVES
    )
    if external_primitives:
        notes.append(
            "CALL/CALLCODE/DELEGATECALL/STATICCALL and CREATE/CREATE2 are "
            "covered by the open external-boundary proof surface"
        )
    if account_query_primitives:
        notes.append(
            "BALANCE and external account-code inspection are covered by "
            "state/query and code-image preservation"
        )
    if executable_observer_primitives:
        notes.append(
            "gas() and msize() are covered by the shared ordered-interaction "
            "semantics and the open-world end-to-end theorem"
        )
    if dialect_builtin_names:
        notes.append(
            "pc/raw-EVM and verbatim/EOF dialect builtins are intentionally "
            "rejected before executable core Yul lowering"
        )
    if linker_object_builtins:
        notes.append(
            "linkersymbol object builtin needs an explicit linker-symbol map"
        )
    if computed_object_builtins:
        notes.append(
            "computed object/data and memoryguard builtins are resolved by the "
            "object-image path"
        )
    if unsupported_primitives or dialect_builtin_names:
        status = "blocked"
    elif linker_object_builtins:
        status = "needs-resolution"
    else:
        status = "ready"
    return {
        "profile": BACKEND_COMPATIBILITY_PROFILE,
        "status": status,
        "unsupportedPrimitiveNames": unsupported_primitives,
        "objectBuiltinNames": object_builtin_names,
        "dialectBuiltinNames": dialect_builtin_names,
        "notes": notes,
    }


def bridge_summary_aggregate_backend_compatibility(
    summaries: Sequence[Json],
) -> Json:
    unsupported: set[str] = set()
    object_builtins: set[str] = set()
    dialect_builtins: set[str] = set()
    for summary in summaries:
        compatibility = summary.get("backendCompatibility")
        if not isinstance(compatibility, dict):
            continue
        unsupported.update(
            name for name in compatibility.get("unsupportedPrimitiveNames", [])
            if isinstance(name, str)
        )
        object_builtins.update(
            name for name in compatibility.get("objectBuiltinNames", [])
            if isinstance(name, str)
        )
        dialect_builtins.update(
            name for name in compatibility.get("dialectBuiltinNames", [])
            if isinstance(name, str)
        )
    call_name_counts: Dict[str, Counter[str]] = {
        CALL_PRIMITIVE: Counter({name: 1 for name in unsupported}),
        CALL_OBJECT_BUILTIN: Counter({name: 1 for name in object_builtins}),
        CALL_DIALECT_BUILTIN: Counter({name: 1 for name in dialect_builtins}),
    }
    return bridge_summary_backend_compatibility(call_name_counts)


def bridge_json_summary_artifact(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    object_selector: str,
    frontend: Optional[Json] = None,
) -> Json:
    stmt_counts: Counter[str] = Counter()
    expr_counts: Counter[str] = Counter()
    call_kind_counts: Counter[str] = Counter()
    call_name_counts: Dict[str, Counter[str]] = {
        CALL_PRIMITIVE: Counter(),
        CALL_USER: Counter(),
        CALL_OBJECT_BUILTIN: Counter(),
        CALL_DIALECT_BUILTIN: Counter(),
    }
    object_summaries: List[Json] = []

    def visit_object(current: YulObject, depth: int) -> None:
        data_bytes = sum(len(section.bytes) for section in current.data)
        object_summaries.append(
            {
                "name": current.name,
                "depth": depth,
                "dispatcherStatements": len(current.dispatcher),
                "functions": len(current.functions),
                "dataSections": len(current.data),
                "dataBytes": data_bytes,
                "subobjects": len(current.subobjects),
                "items": len(current.items),
            }
        )
        for stmt in current.dispatcher:
            collect_stmt_summary(
                stmt,
                stmt_counts,
                expr_counts,
                call_kind_counts,
                call_name_counts,
            )
        for _name, function in current.functions:
            for stmt in function.body:
                collect_stmt_summary(
                    stmt,
                    stmt_counts,
                    expr_counts,
                    call_kind_counts,
                    call_name_counts,
                )
        for child in current.subobjects:
            visit_object(child, depth + 1)

    visit_object(obj, 0)
    total_data_sections = sum(item["dataSections"] for item in object_summaries)
    total_data_bytes = sum(item["dataBytes"] for item in object_summaries)
    total_functions = sum(item["functions"] for item in object_summaries)
    total_calls = sum(call_kind_counts.values())
    calls_by_kind: Json = {}
    for kind in [CALL_PRIMITIVE, CALL_USER, CALL_OBJECT_BUILTIN, CALL_DIALECT_BUILTIN]:
        calls_by_kind[kind] = {
            "total": call_kind_counts.get(kind, 0),
            "names": sorted_counter_entries(call_name_counts.get(kind, Counter())),
        }
    artifact: Json = {
        "schema": BRIDGE_JSON_SUMMARY_SCHEMA,
        "source": source_name,
        "contract": contract_name,
        "selector": object_selector,
        "object": obj.name,
        "counts": {
            "objects": len(object_summaries),
            "functions": total_functions,
            "dataSections": total_data_sections,
            "dataBytes": total_data_bytes,
            "statements": sum(stmt_counts.values()),
            "expressions": sum(expr_counts.values()),
            "calls": total_calls,
        },
        "objects": object_summaries,
        "statements": sorted_counter_entries(stmt_counts),
        "expressions": sorted_counter_entries(expr_counts),
        "calls": calls_by_kind,
        "backendCompatibility": bridge_summary_backend_compatibility(
            call_name_counts
        ),
        "backendHints": bridge_summary_hint_strings(
            obj,
            call_kind_counts,
            call_name_counts,
        ),
    }
    normalized_frontend = normalize_bridge_json_frontend_metadata(
        frontend,
        "summary.frontend",
    )
    if normalized_frontend is not None:
        artifact["frontend"] = normalized_frontend
    return artifact


def render_bridge_json_summary(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    object_selector: str,
    frontend: Optional[Json] = None,
) -> str:
    return (
        json.dumps(
            bridge_json_summary_artifact(
                obj,
                source_name,
                contract_name,
                object_selector,
                frontend,
            ),
            indent=2,
        )
        + "\n"
    )


def render_bridge_json_summary_outputs(
    summaries: Sequence[Json],
    skipped_contracts: Sequence[str],
    skipped_contract_entries: Optional[Sequence[Json]] = None,
) -> str:
    skipped_entries = (
        list(skipped_contract_entries)
        if skipped_contract_entries is not None
        else skipped_contract_entries_from_labels(
            skipped_contracts,
            Path("<bridge-json-summary>"),
            "skipped",
        )
    )
    counts: Json = {
        "objects": len(summaries),
        "skippedContracts": len(skipped_contracts),
        "calls": sum(
            summary.get("counts", {}).get("calls", 0)
            for summary in summaries
            if isinstance(summary.get("counts"), dict)
        ),
    }
    return (
        json.dumps(
            {
                "schema": BRIDGE_JSON_MANIFEST_SUMMARY_SCHEMA,
                "counts": counts,
                "objects": list(summaries),
                "skippedContracts": list(skipped_contracts),
                "skippedContractEntries": skipped_entries,
                "backendCompatibility": (
                    bridge_summary_aggregate_backend_compatibility(summaries)
                ),
            },
            indent=2,
        )
        + "\n"
    )


def safe_bridge_json_path_part(value: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._-")
    return safe or "unnamed"


def bridge_json_output_identity_digest(
    source_name: str,
    contract_name: str,
    role: str,
    object_name: str,
) -> str:
    identity = "\0".join((source_name, contract_name, role, object_name))
    return hashlib.sha256(identity.encode("utf-8")).hexdigest()[:12]


def bridge_json_output_stem(
    source_name: str,
    contract_name: str,
    role: str,
    object_name: str,
) -> str:
    readable = "__".join(
        safe_bridge_json_path_part(part)
        for part in (source_name, contract_name, role, object_name)
    )
    digest = bridge_json_output_identity_digest(
        source_name,
        contract_name,
        role,
        object_name,
    )
    return f"{readable}__{digest}"


def bridge_json_output_path(
    directory: Path,
    source_name: str,
    contract_name: str,
    role: str,
    object_name: str,
) -> Path:
    return directory / (
        bridge_json_output_stem(source_name, contract_name, role, object_name)
        + ".bridge.json"
    )


def bridge_json_manifest_path(directory: Path) -> Path:
    return directory / "manifest.json"


def read_bridge_json_manifest_file(path: Path) -> Json:
    if not path.exists():
        fail(f"Bridge JSON manifest {path} does not exist")
    try:
        manifest = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        fail(f"Could not parse bridge JSON manifest {path}: {exc}")
    if not isinstance(manifest, dict):
        fail(f"Bridge JSON manifest {path} is not a JSON object")
    if manifest.get("schema") != BRIDGE_JSON_MANIFEST_SCHEMA:
        fail(
            f"Unsupported bridge JSON manifest schema in {path}: "
            f"{manifest.get('schema')!r}"
        )
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        fail(f"Bridge JSON manifest {path} has no entries array")
    return manifest


def read_bridge_json_manifest(directory: Path) -> Json:
    path = bridge_json_manifest_path(directory)
    if not path.exists():
        return {"schema": BRIDGE_JSON_MANIFEST_SCHEMA, "entries": []}
    return read_bridge_json_manifest_file(path)


def uint256_manifest_value(value: int, what: str) -> str:
    if value < 0 or value >= 2**256:
        fail(f"{what} is outside UInt256 range: {value}")
    return "0x" + value.to_bytes(32, "big").hex()


def uint256_from_manifest_value(value: Any, manifest_path: Path, what: str) -> int:
    if not isinstance(value, str):
        fail(f"Bridge JSON manifest {manifest_path} {what} must be a hex string")
    try:
        return parse_uint256(value)
    except (ConversionError, ValueError) as exc:
        fail(f"Bridge JSON manifest {manifest_path} has invalid {what}: {exc}")


def linker_symbol_manifest_value(value: int) -> str:
    return uint256_manifest_value(value, "Linker symbol value")


def linker_symbol_manifest_entry(entry: LinkerSymbolEntry) -> Json:
    return {
        "name": entry.name,
        "value": linker_symbol_manifest_value(entry.value),
    }


def linker_symbol_from_manifest_entry(item: Any, manifest_path: Path) -> LinkerSymbolEntry:
    if not isinstance(item, dict):
        fail(f"Bridge JSON manifest {manifest_path} has malformed linkerSymbols entry")
    name = item.get("name")
    value = item.get("value")
    if not isinstance(name, str) or not name:
        fail(
            f"Bridge JSON manifest {manifest_path} has linkerSymbols entry "
            "without a nonempty name"
        )
    if not isinstance(value, str):
        fail(
            f"Bridge JSON manifest {manifest_path} linkerSymbols[{name!r}] "
            "value must be a hex string"
        )
    parsed_value = uint256_from_manifest_value(
        value,
        manifest_path,
        f"linkerSymbols[{name!r}].value",
    )
    return LinkerSymbolEntry(name, parsed_value)


def object_layout_manifest_entry(entry: ObjectLayoutEntry) -> Json:
    return {
        "name": entry.name,
        "offset": uint256_manifest_value(entry.offset, "Object layout offset"),
        "size": uint256_manifest_value(entry.size, "Object layout size"),
    }


def object_layout_from_manifest_entry(
    item: Any,
    manifest_path: Path,
) -> ObjectLayoutEntry:
    if not isinstance(item, dict):
        fail(f"Bridge JSON manifest {manifest_path} has malformed objectLayout entry")
    name = item.get("name")
    if not isinstance(name, str) or not name:
        fail(
            f"Bridge JSON manifest {manifest_path} has objectLayout entry "
            "without a nonempty name"
        )
    return ObjectLayoutEntry(
        name=name,
        offset=uint256_from_manifest_value(
            item.get("offset"),
            manifest_path,
            f"objectLayout[{name!r}].offset",
        ),
        size=uint256_from_manifest_value(
            item.get("size"),
            manifest_path,
            f"objectLayout[{name!r}].size",
        ),
    )


def bridge_json_manifest_linker_symbols(
    manifest: Json,
    manifest_path: Path,
) -> List[LinkerSymbolEntry]:
    raw_entries = manifest.get("linkerSymbols", [])
    if raw_entries is None:
        return []
    if not isinstance(raw_entries, list):
        fail(f"Bridge JSON manifest {manifest_path} linkerSymbols must be an array")
    entries = [
        linker_symbol_from_manifest_entry(item, manifest_path)
        for item in raw_entries
    ]
    seen: set[str] = set()
    for entry in entries:
        if entry.name in seen:
            fail(
                f"Bridge JSON manifest {manifest_path} has duplicate linker "
                f"symbol {entry.name!r}"
            )
        seen.add(entry.name)
    return entries


def bridge_json_manifest_entry_object_layout(
    entry: Any,
    manifest_path: Path,
) -> List[ObjectLayoutEntry]:
    if not isinstance(entry, dict):
        fail(f"Bridge JSON manifest {manifest_path} has a non-object entry")
    raw_entries = entry.get("objectLayout", [])
    if raw_entries is None:
        return []
    if not isinstance(raw_entries, list):
        fail(
            f"Bridge JSON manifest {manifest_path} entry objectLayout must "
            "be an array"
        )
    entries = [
        object_layout_from_manifest_entry(item, manifest_path)
        for item in raw_entries
    ]
    seen: set[str] = set()
    for layout_entry in entries:
        if layout_entry.name in seen:
            fail(
                f"Bridge JSON manifest {manifest_path} has duplicate object "
                f"layout entry {layout_entry.name!r}"
            )
        seen.add(layout_entry.name)
    return entries


def bridge_json_manifest_entry_local_data_base(
    entry: Any,
    manifest_path: Path,
) -> Optional[int]:
    if not isinstance(entry, dict):
        fail(f"Bridge JSON manifest {manifest_path} has a non-object entry")
    if "localDataBase" not in entry:
        return None
    return uint256_from_manifest_value(
        entry.get("localDataBase"),
        manifest_path,
        "entry localDataBase",
    )


def bridge_json_manifest_entry_frontend(
    entry: Any,
    manifest_path: Path,
) -> Optional[Json]:
    if not isinstance(entry, dict):
        fail(f"Bridge JSON manifest {manifest_path} has a non-object entry")
    return normalize_bridge_json_frontend_metadata(
        entry.get("frontend"),
        f"Bridge JSON manifest {manifest_path} entry frontend",
    )


def set_bridge_json_manifest_linker_symbols(
    manifest: Json,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> None:
    if linker_symbols:
        merged = {entry.name: entry for entry in linker_symbols}
        manifest["linkerSymbols"] = [
            linker_symbol_manifest_entry(entry)
            for entry in sorted(merged.values(), key=lambda item: item.name)
        ]
    else:
        manifest.pop("linkerSymbols", None)


def write_bridge_json_manifest_entry(
    directory: Path,
    source_name: str,
    contract_name: str,
    role: str,
    object_name: str,
    path: Path,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
    object_layout: Sequence[ObjectLayoutEntry] = (),
    local_data_base: Optional[int] = None,
    ast_output: Optional[str] = None,
) -> None:
    manifest = read_bridge_json_manifest(directory)
    entries = manifest["entries"]
    entry: Json = {
        "source": source_name,
        "contract": contract_name,
        "selector": role,
        "object": object_name,
        "path": path.name,
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }
    frontend = bridge_json_frontend_metadata(ast_output)
    if frontend is not None:
        entry["frontend"] = frontend
    if object_layout:
        entry["objectLayout"] = [
            object_layout_manifest_entry(layout_entry)
            for layout_entry in object_layout
        ]
    if local_data_base is not None:
        entry["localDataBase"] = uint256_manifest_value(
            local_data_base,
            "localDataBase",
        )
    key = (source_name, contract_name, role, object_name)
    filtered = [
        item for item in entries
        if not (
            isinstance(item, dict)
            and (
                item.get("source"),
                item.get("contract"),
                item.get("selector"),
                item.get("object"),
            ) == key
        )
    ]
    filtered.append(entry)
    filtered.sort(
        key=lambda item: (
            str(item.get("source", "")) if isinstance(item, dict) else "",
            str(item.get("contract", "")) if isinstance(item, dict) else "",
            str(item.get("selector", "")) if isinstance(item, dict) else "",
            str(item.get("object", "")) if isinstance(item, dict) else "",
        )
    )
    manifest["entries"] = filtered
    counts: Json = {"entries": len(filtered)}
    skipped_contracts = manifest.get("skippedContracts")
    if isinstance(skipped_contracts, list):
        counts["skippedContracts"] = len(skipped_contracts)
    manifest["counts"] = counts
    if linker_symbols:
        set_bridge_json_manifest_linker_symbols(manifest, linker_symbols)
    bridge_json_manifest_path(directory).write_text(
        json.dumps(manifest, indent=2) + "\n"
    )


def skipped_contract_parts_from_label(label: Any, manifest_path: Path) -> Tuple[str, str]:
    if not isinstance(label, str) or ":" not in label:
        fail(
            f"Bridge JSON manifest {manifest_path} has invalid skipped contract "
            f"label: {label!r}"
        )
    skipped_source, skipped_contract = label.rsplit(":", 1)
    if not skipped_source or not skipped_contract:
        fail(
            f"Bridge JSON manifest {manifest_path} has invalid skipped contract "
            f"label: {label!r}"
        )
    return skipped_source, skipped_contract


def skipped_contract_entry_from_label(
    label: Any,
    manifest_path: Path,
    reason: str,
) -> Json:
    if not reason:
        fail(f"Bridge JSON manifest {manifest_path} skipped reason is empty")
    source, contract = skipped_contract_parts_from_label(label, manifest_path)
    return {"source": source, "contract": contract, "reason": reason}


def skipped_contract_entries_from_labels(
    labels: Sequence[str],
    manifest_path: Path,
    reason: str,
) -> List[Json]:
    return [
        skipped_contract_entry_from_label(label, manifest_path, reason)
        for label in labels
    ]


def write_bridge_json_manifest_skipped_contracts(
    directory: Path,
    skipped_contracts: Sequence[str],
    reason: str = "skipped",
) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    manifest = read_bridge_json_manifest(directory)
    entries = manifest["entries"]
    skipped = sorted(skipped_contracts)
    manifest["entries"] = entries
    manifest["skippedContracts"] = skipped
    manifest["skippedContractEntries"] = [
        skipped_contract_entry_from_label(
            label,
            bridge_json_manifest_path(directory),
            reason,
        )
        for label in skipped
    ]
    manifest["counts"] = {
        "entries": len(entries),
        "skippedContracts": len(skipped),
    }
    bridge_json_manifest_path(directory).write_text(
        json.dumps(manifest, indent=2) + "\n"
    )


def write_bridge_json_output(
    directory: Path,
    obj: YulObject,
    source_name: str,
    contract_name: str,
    role: str,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
    object_layout: Sequence[ObjectLayoutEntry] = (),
    local_data_base: Optional[int] = None,
    ast_output: Optional[str] = None,
) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    path = bridge_json_output_path(
        directory,
        source_name,
        contract_name,
        role,
        obj.name,
    )
    path.write_text(render_bridge_json(obj, source_name, contract_name, ast_output))
    write_bridge_json_manifest_entry(
        directory,
        source_name,
        contract_name,
        role,
        obj.name,
        path,
        linker_symbols,
        object_layout,
        local_data_base,
        ast_output,
    )
    return path


def write_artifact_bridge_json_outputs(
    directory: Optional[Path],
    root: YulObject,
    source_name: str,
    contract_name: str,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
    object_layout: Sequence[ObjectLayoutEntry] = (),
    local_data_base: Optional[int] = None,
    ast_output: Optional[str] = None,
) -> None:
    if directory is None:
        return
    write_bridge_json_output(
        directory,
        root,
        source_name,
        contract_name,
        "creation",
        linker_symbols,
        object_layout,
        local_data_base,
        ast_output,
    )
    write_bridge_json_output(
        directory,
        select_object(root, "runtime"),
        source_name,
        contract_name,
        "runtime",
        linker_symbols,
        ast_output=ast_output,
    )


def bridge_json_manifest_entry_for_object(
    manifest: Json,
    source_name: str,
    contract_name: str,
    selector: str,
    object_name: str,
    manifest_path: Path,
) -> Json:
    for entry in manifest.get("entries", []):
        if not isinstance(entry, dict):
            continue
        if (
            entry.get("source") == source_name
            and entry.get("contract") == contract_name
            and entry.get("selector") == selector
            and entry.get("object") == object_name
        ):
            return copy.deepcopy(entry)
    fail(
        f"Bridge JSON manifest {manifest_path} has no {selector} entry for "
        f"{source_name}:{contract_name} object {object_name!r}"
    )


def bridge_json_provenance_for_artifact(
    directory: Path,
    artifact: ContractBytecodeArtifact,
) -> Json:
    manifest_path = bridge_json_manifest_path(directory)
    manifest = read_bridge_json_manifest_file(manifest_path)
    provenance: Json = {
        "schema": BRIDGE_JSON_PROVENANCE_SCHEMA,
        "manifestSchema": BRIDGE_JSON_MANIFEST_SCHEMA,
        "manifest": str(manifest_path),
        "entries": {
            "creation": bridge_json_manifest_entry_for_object(
                manifest,
                artifact.source_name,
                artifact.contract_name,
                "creation",
                artifact.creation_object_name,
                manifest_path,
            ),
            "runtime": bridge_json_manifest_entry_for_object(
                manifest,
                artifact.source_name,
                artifact.contract_name,
                "runtime",
                artifact.runtime_object_name,
                manifest_path,
            ),
        },
    }
    linker_symbols = bridge_json_manifest_linker_symbols(manifest, manifest_path)
    if linker_symbols:
        provenance["linkerSymbols"] = [
            linker_symbol_manifest_entry(entry) for entry in linker_symbols
        ]
    return provenance


def attach_bridge_json_provenance(
    artifact: ContractBytecodeArtifact,
    directory: Optional[Path],
) -> ContractBytecodeArtifact:
    if directory is None:
        return artifact
    return ContractBytecodeArtifact(
        source_name=artifact.source_name,
        contract_name=artifact.contract_name,
        creation_object_name=artifact.creation_object_name,
        runtime_object_name=artifact.runtime_object_name,
        creation_bytecode=artifact.creation_bytecode,
        runtime_bytecode=artifact.runtime_bytecode,
        runtime_immutable_references=copy.deepcopy(
            artifact.runtime_immutable_references
        ),
        backend_compatibility=copy.deepcopy(artifact.backend_compatibility),
        bridge_json=bridge_json_provenance_for_artifact(directory, artifact),
    )


def bridge_object(value: Any, what: str) -> Json:
    if not isinstance(value, dict):
        fail(f"Expected bridge JSON {what} to be an object")
    return value


def bridge_array(value: Any, what: str) -> List[Any]:
    if not isinstance(value, list):
        fail(f"Expected bridge JSON {what} to be an array")
    return value


def bridge_string(value: Any, what: str) -> str:
    if not isinstance(value, str):
        fail(f"Expected bridge JSON {what} to be a string")
    return value


def bridge_bool(value: Any, what: str) -> bool:
    if not isinstance(value, bool):
        fail(f"Expected bridge JSON {what} to be a boolean")
    return value


def bridge_optional_string(value: Any, what: str) -> Optional[str]:
    if value is None:
        return None
    return bridge_string(value, what)


def bridge_uint(value: Any, what: str, bound: Optional[int] = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        fail(f"Expected bridge JSON {what} to be a nonnegative integer")
    if value < 0:
        fail(f"Expected bridge JSON {what} to be nonnegative, got {value}")
    if bound is not None and value >= bound:
        fail(f"Bridge JSON {what} is out of range: {value}")
    return value


def bridge_uint256(value: Any, what: str) -> int:
    return bridge_uint(value, what, 2**256)


def decode_bridge_switch_case_value(value: Any, what: str) -> SwitchCaseValue:
    if isinstance(value, int) and not isinstance(value, bool):
        return SwitchCaseValue(SWITCH_CASE_WORD, bridge_uint256(value, what))
    case_value = bridge_object(value, what)
    node = bridge_string(case_value.get("node"), f"{what}.node")
    if node == "literal":
        return SwitchCaseValue(
            SWITCH_CASE_WORD,
            bridge_uint256(case_value.get("value"), f"{what}.value"),
        )
    if node == "stringLiteral":
        return SwitchCaseValue(
            SWITCH_CASE_STRING,
            bridge_string(case_value.get("value"), f"{what}.value"),
        )
    if node == "bytesLiteral":
        return SwitchCaseValue(
            SWITCH_CASE_BYTES,
            tuple(bridge_byte_array(case_value.get("bytes"), f"{what}.bytes")),
        )
    if node == "boolLiteral":
        return SwitchCaseValue(
            SWITCH_CASE_BOOL,
            bridge_bool(case_value.get("value"), f"{what}.value"),
        )
    fail(f"Unsupported bridge JSON switch case value node: {node!r}")


def bridge_byte_array(value: Any, what: str) -> List[int]:
    return [
        bridge_uint(item, f"{what}[{index}]", 256)
        for index, item in enumerate(bridge_array(value, what))
    ]


def bridge_string_array(value: Any, what: str) -> List[str]:
    return [
        bridge_string(item, f"{what}[{index}]")
        for index, item in enumerate(bridge_array(value, what))
    ]


def expect_bridge_node(data: Any, expected: str, what: str) -> Json:
    node = bridge_object(data, what)
    actual = bridge_string(node.get("node"), f"{what}.node")
    if actual != expected:
        fail(f"Expected bridge JSON {what} node {expected!r}, got {actual!r}")
    return node


def decode_bridge_expr(data: Any) -> Expr:
    expr = bridge_object(data, "expression")
    node = bridge_string(expr.get("node"), "expression.node")
    if node == "literal":
        return Lit(bridge_uint256(expr.get("value"), "literal.value"))
    if node == "stringLiteral":
        return StringLit(bridge_string(expr.get("value"), "stringLiteral.value"))
    if node == "bytesLiteral":
        return BytesLit(bridge_byte_array(expr.get("bytes"), "bytesLiteral.bytes"))
    if node == "var":
        return Var(bridge_string(expr.get("name"), "var.name"))
    if node == "call":
        callee = bridge_string(expr.get("callee"), "call.callee")
        callee_kind = bridge_string(expr.get("calleeKind"), "call.calleeKind")
        if callee_kind not in LEAN_CALL_KIND:
            fail(f"Unknown bridge JSON call kind: {callee_kind!r}")
        if callee_kind == CALL_PRIMITIVE and callee not in PRIMITIVE_OPS:
            fail(f"Unknown primitive Yul call in bridge JSON: {callee!r}")
        if callee_kind == CALL_OBJECT_BUILTIN and callee not in OBJECT_BUILTINS:
            fail(f"Unknown object builtin Yul call in bridge JSON: {callee!r}")
        args = [
            decode_bridge_expr(arg)
            for arg in bridge_array(expr.get("args"), "call.args")
        ]
        return Call(callee, args, callee_kind)
    fail(f"Unsupported bridge JSON expression node: {node!r}")


def decode_bridge_stmt(data: Any) -> Stmt:
    stmt = bridge_object(data, "statement")
    node = bridge_string(stmt.get("node"), "statement.node")
    if node == "block":
        return Block(
            [
                decode_bridge_stmt(child)
                for child in bridge_array(stmt.get("stmts"), "block.stmts")
            ]
        )
    if node == "let":
        value = stmt.get("value")
        return Let(
            bridge_string_array(stmt.get("names"), "let.names"),
            decode_bridge_expr(value) if value is not None else None,
        )
    if node == "assign":
        return Assign(
            bridge_string_array(stmt.get("names"), "assign.names"),
            decode_bridge_expr(stmt.get("value")),
        )
    if node == "exprStmt":
        return ExprStmt(decode_bridge_expr(stmt.get("expr")))
    if node == "function":
        return FunctionStmt(
            bridge_string(stmt.get("name"), "function.name"),
            FunctionDef(
                bridge_string_array(stmt.get("params"), "function.params"),
                bridge_string_array(stmt.get("returns"), "function.returns"),
                [
                    decode_bridge_stmt(child)
                    for child in bridge_array(stmt.get("body"), "function.body")
                ],
            ),
        )
    if node == "switch":
        cases = []
        for index, raw_case in enumerate(
            bridge_array(stmt.get("cases"), "switch.cases")
        ):
            case = bridge_object(raw_case, f"switch.cases[{index}]")
            value = decode_bridge_switch_case_value(
                case.get("value"),
                f"switch.cases[{index}].value",
            )
            body = [
                decode_bridge_stmt(child)
                for child in bridge_array(
                    case.get("body"),
                    f"switch.cases[{index}].body",
                )
            ]
            cases.append((value, body))
        default = [
            decode_bridge_stmt(child)
            for child in bridge_array(stmt.get("default"), "switch.default")
        ]
        return Switch(decode_bridge_expr(stmt.get("scrutinee")), cases, default)
    if node == "for":
        return For(
            [
                decode_bridge_stmt(child)
                for child in bridge_array(stmt.get("pre", []), "for.pre")
            ],
            decode_bridge_expr(stmt.get("condition")),
            [
                decode_bridge_stmt(child)
                for child in bridge_array(stmt.get("post"), "for.post")
            ],
            [
                decode_bridge_stmt(child)
                for child in bridge_array(stmt.get("body"), "for.body")
            ],
        )
    if node == "if":
        return If(
            decode_bridge_expr(stmt.get("condition")),
            [
                decode_bridge_stmt(child)
                for child in bridge_array(stmt.get("body"), "if.body")
            ],
        )
    if node in {"break", "continue", "leave"}:
        return Control(node[0].upper() + node[1:])
    fail(f"Unsupported bridge JSON statement node: {node!r}")


def decode_bridge_function(data: Any) -> FunctionDef:
    fn = bridge_object(data, "function")
    return FunctionDef(
        bridge_string_array(fn.get("params"), "function.params"),
        bridge_string_array(fn.get("returns"), "function.returns"),
        [
            decode_bridge_stmt(stmt)
            for stmt in bridge_array(fn.get("body"), "function.body")
        ],
    )


def decode_bridge_data_section(data: Any) -> DataSection:
    section = bridge_object(data, "data section")
    bytes_ = [
        bridge_uint(byte, f"data.bytes[{index}]", 256)
        for index, byte in enumerate(bridge_array(section.get("bytes"), "data.bytes"))
    ]
    return DataSection(
        bridge_optional_string(section.get("name"), "data.name"),
        bytes_,
    )


def decode_bridge_item_ref(data: Any) -> ObjectItemRef:
    item = bridge_object(data, "object item")
    return ObjectItemRef(
        bridge_string(item.get("kind"), "object item.kind"),
        bridge_uint(item.get("index"), "object item.index"),
    )


def decode_bridge_object(data: Any) -> YulObject:
    obj = expect_bridge_node(data, "object", "object")
    name = bridge_string(obj.get("name"), "object.name")
    dispatcher = [
        decode_bridge_stmt(stmt)
        for stmt in bridge_array(obj.get("dispatcher"), f"object {name}.dispatcher")
    ]
    functions = []
    for index, raw_fn in enumerate(
        bridge_array(obj.get("functions"), f"object {name}.functions")
    ):
        fn_obj = bridge_object(raw_fn, f"object {name}.functions[{index}]")
        fn_name = bridge_string(
            fn_obj.get("name"),
            f"object {name}.functions[{index}].name",
        )
        functions.append((fn_name, decode_bridge_function(fn_obj)))
    data_sections = [
        decode_bridge_data_section(section)
        for section in bridge_array(obj.get("data"), f"object {name}.data")
    ]
    subobjects = [
        decode_bridge_object(child)
        for child in bridge_array(obj.get("subobjects"), f"object {name}.subobjects")
    ]
    items = [
        decode_bridge_item_ref(item)
        for item in bridge_array(obj.get("items"), f"object {name}.items")
    ]
    for item in items:
        if item.kind == "data" and item.index >= len(data_sections):
            fail(
                f"Bridge JSON object {name!r} has data item index {item.index} "
                f"but only {len(data_sections)} data sections"
            )
        if item.kind == "object" and item.index >= len(subobjects):
            fail(
                f"Bridge JSON object {name!r} has object item index {item.index} "
                f"but only {len(subobjects)} subobjects"
            )
    scratch_reservation = None
    raw_contract = obj.get("memoryContract")
    if raw_contract is not None:
        contract = bridge_object(raw_contract, f"object {name}.memoryContract")
        raw_scratch = contract.get("scratch")
        if raw_scratch is not None:
            scratch = bridge_object(raw_scratch, f"object {name}.memoryContract.scratch")
            scratch_reservation = (
                bridge_uint(scratch.get("base"), "scratch reservation base"),
                bridge_uint(scratch.get("words"), "scratch reservation words"),
            )
    return YulObject(
        name,
        dispatcher,
        functions,
        data_sections,
        subobjects,
        items,
        scratch_reservation,
    )


def decode_bridge_program(data: Any) -> Tuple[str, str, YulObject]:
    root = bridge_object(data, "root")
    schema = bridge_string(root.get("schema"), "schema")
    if schema != BRIDGE_JSON_SCHEMA:
        fail(f"Unsupported bridge JSON schema: {schema!r}")
    source_name = bridge_string(root.get("source"), "source")
    contract_name = bridge_string(root.get("contract"), "contract")
    selected_object = decode_bridge_object(root.get("selectedObject"))
    return source_name, contract_name, selected_object


def read_bridge_json_input(input_path: Path) -> Tuple[str, str, YulObject]:
    text = sys.stdin.read() if str(input_path) == "-" else input_path.read_text()
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError as exc:
        fail(f"Could not parse bridge JSON input: {exc}")
    return decode_bridge_program(parsed)


def read_bridge_json_input_with_frontend(
    input_path: Path,
) -> Tuple[str, str, YulObject, Optional[Json]]:
    text = sys.stdin.read() if str(input_path) == "-" else input_path.read_text()
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError as exc:
        fail(f"Could not parse bridge JSON input: {exc}")
    source_name, contract_name, obj = decode_bridge_program(parsed)
    frontend = normalize_bridge_json_frontend_metadata(
        bridge_object(parsed, "root").get("frontend"),
        "frontend",
    )
    return source_name, contract_name, obj, frontend


def bridge_json_from_text(text: str, path: Path) -> Tuple[str, str, YulObject]:
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError as exc:
        fail(f"Could not parse bridge JSON file {path}: {exc}")
    return decode_bridge_program(parsed)


def manifest_entry_string(entry: Any, key: str, manifest_path: Path) -> str:
    if not isinstance(entry, dict):
        fail(f"Bridge JSON manifest {manifest_path} has a non-object entry")
    value = entry.get(key)
    if not isinstance(value, str) or not value:
        fail(
            f"Bridge JSON manifest {manifest_path} entry has invalid "
            f"{key!r} field"
        )
    return value


def manifest_entry_bridge_json_path(manifest_path: Path, entry: Any) -> Path:
    path_text = manifest_entry_string(entry, "path", manifest_path)
    relative = PurePosixPath(path_text)
    if relative.is_absolute() or any(part == ".." for part in relative.parts):
        fail(
            f"Bridge JSON manifest {manifest_path} entry path must be relative "
            f"and stay under the manifest directory: {path_text!r}"
        )
    if not relative.parts or relative.parts == (".",):
        fail(
            f"Bridge JSON manifest {manifest_path} entry path is empty or invalid"
        )
    root = manifest_path.parent.resolve()
    resolved = (root / Path(*relative.parts)).resolve()
    try:
        resolved.relative_to(root)
    except ValueError:
        fail(
            f"Bridge JSON manifest {manifest_path} entry path escapes the "
            f"manifest directory: {path_text!r}"
        )
    if not resolved.exists():
        fail(f"Bridge JSON manifest entry file does not exist: {resolved}")
    if not resolved.is_file():
        fail(f"Bridge JSON manifest entry is not a file: {resolved}")
    return resolved


def manifest_entry_sha256(entry: Any, manifest_path: Path) -> Optional[str]:
    if not isinstance(entry, dict):
        fail(f"Bridge JSON manifest {manifest_path} has a non-object entry")
    value = entry.get("sha256")
    if value is None:
        return None
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        fail(
            f"Bridge JSON manifest {manifest_path} entry has invalid "
            "'sha256' field"
        )
    return value


def check_manifest_entry_sha256(
    manifest_path: Path,
    bridge_path: Path,
    entry: Any,
) -> None:
    expected_sha256 = manifest_entry_sha256(entry, manifest_path)
    if expected_sha256 is None:
        return
    actual_sha256 = hashlib.sha256(bridge_path.read_bytes()).hexdigest()
    if actual_sha256 != expected_sha256:
        fail(
            f"Bridge JSON file {bridge_path} sha256 is {actual_sha256}, "
            f"but manifest says {expected_sha256}"
        )


def bridge_json_manifest_entry_matches(
    entry: Any,
    manifest_path: Path,
    source_name: Optional[str],
    contract_name: Optional[str],
    object_selector: Optional[str],
) -> bool:
    source = manifest_entry_string(entry, "source", manifest_path)
    contract = manifest_entry_string(entry, "contract", manifest_path)
    selector = manifest_entry_string(entry, "selector", manifest_path)
    obj = manifest_entry_string(entry, "object", manifest_path)
    if source_name is not None and source != source_name:
        return False
    if contract_name is not None and contract != contract_name:
        return False
    if object_selector is not None and object_selector not in {selector, obj}:
        return False
    return True


def skipped_contract_matches(
    label: Any,
    manifest_path: Path,
    source_name: Optional[str],
    contract_name: Optional[str],
) -> bool:
    skipped_source, skipped_contract = skipped_contract_parts_from_label(
        label,
        manifest_path,
    )
    if source_name is not None and skipped_source != source_name:
        return False
    if contract_name is not None and skipped_contract != contract_name:
        return False
    return True


def skipped_contract_label_from_entry(entry: Any, manifest_path: Path) -> str:
    if not isinstance(entry, dict):
        fail(
            f"Bridge JSON manifest {manifest_path} has invalid skipped contract "
            f"entry: {entry!r}"
        )
    source = entry.get("source")
    contract = entry.get("contract")
    reason = entry.get("reason")
    if not isinstance(source, str) or not source:
        fail(
            f"Bridge JSON manifest {manifest_path} skipped contract entry has "
            "invalid source"
        )
    if not isinstance(contract, str) or not contract:
        fail(
            f"Bridge JSON manifest {manifest_path} skipped contract entry has "
            "invalid contract"
        )
    if not isinstance(reason, str) or not reason:
        fail(
            f"Bridge JSON manifest {manifest_path} skipped contract entry has "
            "invalid reason"
        )
    return contract_label(source, contract)


def bridge_json_manifest_skipped_contracts(
    manifest: Json,
    manifest_path: Path,
    source_name: Optional[str],
    contract_name: Optional[str],
) -> List[str]:
    skipped_contracts = manifest.get("skippedContracts", [])
    if skipped_contracts is None:
        skipped_contracts = []
    if not isinstance(skipped_contracts, list):
        fail(
            f"Bridge JSON manifest {manifest_path} has invalid "
            "skippedContracts field"
        )
    skipped_entries = manifest.get("skippedContractEntries")
    if skipped_entries is not None:
        if not isinstance(skipped_entries, list):
            fail(
                f"Bridge JSON manifest {manifest_path} has invalid "
                "skippedContractEntries field"
            )
        entry_labels = [
            skipped_contract_label_from_entry(entry, manifest_path)
            for entry in skipped_entries
        ]
        if sorted(entry_labels) != sorted(skipped_contracts):
            fail(
                f"Bridge JSON manifest {manifest_path} has inconsistent "
                "skippedContracts and skippedContractEntries"
            )
    return [
        label for label in skipped_contracts
        if skipped_contract_matches(label, manifest_path, source_name, contract_name)
    ]


def bridge_json_manifest_skipped_contract_entries(
    manifest: Json,
    manifest_path: Path,
    source_name: Optional[str],
    contract_name: Optional[str],
) -> List[Json]:
    matched_labels = bridge_json_manifest_skipped_contracts(
        manifest,
        manifest_path,
        source_name,
        contract_name,
    )
    skipped_entries = manifest.get("skippedContractEntries")
    if skipped_entries is None:
        return skipped_contract_entries_from_labels(
            matched_labels,
            manifest_path,
            "skipped",
        )
    matched_label_set = set(matched_labels)
    return [
        entry
        for entry in skipped_entries
        if skipped_contract_label_from_entry(entry, manifest_path) in matched_label_set
    ]


def validate_bridge_json_manifest_index(
    manifest: Json,
    manifest_path: Path,
) -> None:
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        fail(f"Bridge JSON manifest {manifest_path} has no entries array")
    bridge_json_manifest_linker_symbols(manifest, manifest_path)
    bridge_json_manifest_skipped_contracts(manifest, manifest_path, None, None)
    counts = manifest.get("counts")
    if counts is not None:
        if not isinstance(counts, dict) or counts.get("entries") != len(entries):
            fail(f"Bridge JSON manifest {manifest_path} has inconsistent counts.entries")
        skipped_contracts = manifest.get("skippedContracts")
        if skipped_contracts is not None and counts.get("skippedContracts") != len(
            skipped_contracts
        ):
            fail(
                f"Bridge JSON manifest {manifest_path} has inconsistent "
                "counts.skippedContracts"
            )
    seen_keys: set[tuple[str, str, str, str]] = set()
    seen_paths: set[str] = set()
    for entry in entries:
        source_name = manifest_entry_string(entry, "source", manifest_path)
        contract_name = manifest_entry_string(entry, "contract", manifest_path)
        selector = manifest_entry_string(entry, "selector", manifest_path)
        object_name = manifest_entry_string(entry, "object", manifest_path)
        path_text = manifest_entry_string(entry, "path", manifest_path)
        manifest_entry_sha256(entry, manifest_path)
        bridge_json_manifest_entry_object_layout(entry, manifest_path)
        bridge_json_manifest_entry_local_data_base(entry, manifest_path)
        key = (source_name, contract_name, selector, object_name)
        if key in seen_keys:
            fail(
                f"Bridge JSON manifest {manifest_path} has duplicate entry for "
                f"{source_name}:{contract_name}:{selector}:{object_name}"
            )
        if path_text in seen_paths:
            fail(
                f"Bridge JSON manifest {manifest_path} has duplicate bridge JSON "
                f"path {path_text!r}"
            )
        seen_keys.add(key)
        seen_paths.add(path_text)


def bridge_json_manifest_artifact(
    manifest_path: Path,
    entry: Any,
    lake: str,
    lake_cwd: Path,
) -> LeanJsonCheckArtifact:
    source_name = manifest_entry_string(entry, "source", manifest_path)
    contract_name = manifest_entry_string(entry, "contract", manifest_path)
    selector = manifest_entry_string(entry, "selector", manifest_path)
    object_name = manifest_entry_string(entry, "object", manifest_path)
    bridge_path = manifest_entry_bridge_json_path(manifest_path, entry)
    check_manifest_entry_sha256(manifest_path, bridge_path, entry)
    bridge_json = bridge_path.read_text()
    decoded_source, decoded_contract, decoded_object = bridge_json_from_text(
        bridge_json,
        bridge_path,
    )
    if decoded_source != source_name:
        fail(
            f"Bridge JSON file {bridge_path} source is {decoded_source!r}, "
            f"but manifest says {source_name!r}"
        )
    if decoded_contract != contract_name:
        fail(
            f"Bridge JSON file {bridge_path} contract is {decoded_contract!r}, "
            f"but manifest says {contract_name!r}"
        )
    if decoded_object.name != object_name:
        fail(
            f"Bridge JSON file {bridge_path} object is {decoded_object.name!r}, "
            f"but manifest says {object_name!r}"
        )
    output = check_bridge_json_with_lean(bridge_json, lake, lake_cwd)
    summary = parse_bridge_json_decode_output(output)
    if summary.get("source") != source_name:
        fail(
            "Lean bridge JSON decode runner reported source "
            f"{summary.get('source')!r}, expected {source_name!r}"
        )
    if summary.get("contract") != contract_name:
        fail(
            "Lean bridge JSON decode runner reported contract "
            f"{summary.get('contract')!r}, expected {contract_name!r}"
        )
    if summary.get("object") != object_name:
        fail(
            "Lean bridge JSON decode runner reported object "
            f"{summary.get('object')!r}, expected {object_name!r}"
        )
    return LeanJsonCheckArtifact(
        source_name=source_name,
        contract_name=contract_name,
        object_selector=selector,
        object_name=object_name,
        summary=summary,
        frontend=bridge_json_manifest_entry_frontend(entry, manifest_path),
    )


def bridge_json_manifest_backend_artifact(
    manifest_path: Path,
    entry: Any,
    lake: str,
    lake_cwd: Path,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
) -> LeanBackendCheckArtifact:
    source_name = manifest_entry_string(entry, "source", manifest_path)
    contract_name = manifest_entry_string(entry, "contract", manifest_path)
    selector = manifest_entry_string(entry, "selector", manifest_path)
    object_name = manifest_entry_string(entry, "object", manifest_path)
    bridge_path = manifest_entry_bridge_json_path(manifest_path, entry)
    check_manifest_entry_sha256(manifest_path, bridge_path, entry)
    bridge_json = bridge_path.read_text()
    decoded_source, decoded_contract, decoded_object = bridge_json_from_text(
        bridge_json,
        bridge_path,
    )
    if decoded_source != source_name:
        fail(
            f"Bridge JSON file {bridge_path} source is {decoded_source!r}, "
            f"but manifest says {source_name!r}"
        )
    if decoded_contract != contract_name:
        fail(
            f"Bridge JSON file {bridge_path} contract is {decoded_contract!r}, "
            f"but manifest says {contract_name!r}"
        )
    if decoded_object.name != object_name:
        fail(
            f"Bridge JSON file {bridge_path} object is {decoded_object.name!r}, "
            f"but manifest says {object_name!r}"
        )
    output = check_bridge_json_backend_with_lean(
        bridge_json,
        lake,
        lake_cwd,
        linker_symbols,
    )
    summary = parse_backend_check_output(output)
    if summary.get("source") != source_name:
        fail(
            "Lean backend check runner reported source "
            f"{summary.get('source')!r}, expected {source_name!r}"
        )
    if summary.get("contract") != contract_name:
        fail(
            "Lean backend check runner reported contract "
            f"{summary.get('contract')!r}, expected {contract_name!r}"
        )
    if summary.get("object") != object_name:
        fail(
            "Lean backend check runner reported object "
            f"{summary.get('object')!r}, expected {object_name!r}"
        )
    return LeanBackendCheckArtifact(
        source_name=source_name,
        contract_name=contract_name,
        object_selector=selector,
        object_name=object_name,
        summary=summary,
        frontend=bridge_json_manifest_entry_frontend(entry, manifest_path),
    )


def bridge_json_manifest_object(
    manifest_path: Path,
    entry: Any,
) -> Tuple[str, str, str, YulObject]:
    source_name = manifest_entry_string(entry, "source", manifest_path)
    contract_name = manifest_entry_string(entry, "contract", manifest_path)
    selector = manifest_entry_string(entry, "selector", manifest_path)
    object_name = manifest_entry_string(entry, "object", manifest_path)
    bridge_path = manifest_entry_bridge_json_path(manifest_path, entry)
    check_manifest_entry_sha256(manifest_path, bridge_path, entry)
    decoded_source, decoded_contract, decoded_object = bridge_json_from_text(
        bridge_path.read_text(),
        bridge_path,
    )
    if decoded_source != source_name:
        fail(
            f"Bridge JSON file {bridge_path} source is {decoded_source!r}, "
            f"but manifest says {source_name!r}"
        )
    if decoded_contract != contract_name:
        fail(
            f"Bridge JSON file {bridge_path} contract is {decoded_contract!r}, "
            f"but manifest says {contract_name!r}"
        )
    if decoded_object.name != object_name:
        fail(
            f"Bridge JSON file {bridge_path} object is {decoded_object.name!r}, "
            f"but manifest says {object_name!r}"
        )
    return source_name, contract_name, selector, decoded_object


def object_tree_lines(root: YulObject, level: int = 0) -> List[str]:
    pad = "  " * level
    lines = [f"{pad}object {root.name}"]
    listed_data = set()
    listed_objects = set()
    for item in root.items:
        if item.kind == "data" and item.index < len(root.data):
            listed_data.add(item.index)
            section = root.data[item.index]
            label = section.name if section.name is not None else "<anonymous>"
            lines.append(f"{pad}  data {label} {len(section.bytes)} bytes")
        elif item.kind == "object" and item.index < len(root.subobjects):
            listed_objects.add(item.index)
            lines.extend(object_tree_lines(root.subobjects[item.index], level + 1))
    for index, section in enumerate(root.data):
        if index not in listed_data:
            label = section.name if section.name is not None else "<anonymous>"
            lines.append(f"{pad}  data {label} {len(section.bytes)} bytes")
    for index, subobject in enumerate(root.subobjects):
        if index not in listed_objects:
            lines.extend(object_tree_lines(subobject, level + 1))
    return lines


def standard_json_input(
    source_name: str,
    content: str,
    via_ir: bool,
    optimized: bool,
    experimental: bool,
    include_sources: Optional[Dict[str, str]] = None,
    require_bytecode: bool = True,
) -> Json:
    settings: Json = {
        "viaIR": via_ir,
        "outputSelection": {"*": {"*": [], "": []}},
    }
    if optimized:
        settings["optimizer"] = {"enabled": True, "details": {"yul": True}}
    if experimental:
        settings["experimental"] = True
    sources = {source_name: {"content": content}}
    for include_name, include_content in (include_sources or {}).items():
        if include_name in sources:
            fail(f"Duplicate Solidity source name {include_name!r}")
        sources[include_name] = {"content": include_content}
    compiler_input = {
        "language": "Solidity",
        "sources": sources,
        "settings": settings,
    }
    ensure_standard_json_frontend_outputs(
        compiler_input,
        optimized=optimized,
        default_via_ir=via_ir,
        default_experimental=experimental,
        require_bytecode=require_bytecode,
    )
    return compiler_input


def yul_standard_json_input(
    source_name: str,
    content: str,
    experimental: bool,
) -> Json:
    compiler_input = {
        "language": "Yul",
        "sources": {source_name: {"content": content}},
        "settings": {
            "outputSelection": {"*": {"*": ["ast"]}},
        },
    }
    if experimental:
        compiler_input["settings"]["experimental"] = True
    return compiler_input


def required_contract_outputs(
    optimized: bool,
    require_bytecode: bool = True,
) -> List[str]:
    outputs = [
        solc_yul_ast_output(optimized),
        solc_yul_text_output(optimized),
    ]
    if require_bytecode:
        outputs.extend(
            [
                "abi",
                "metadata",
                "evm.bytecode.object",
                "evm.deployedBytecode.object",
                "evm.methodIdentifiers",
            ]
        )
    return outputs


def append_outputs(outputs: Any, required: Sequence[str], what: str) -> List[str]:
    if outputs is None:
        outputs = []
    if not isinstance(outputs, list) or not all(
        isinstance(item, str) for item in outputs
    ):
        fail(f"Malformed solc Standard JSON outputSelection for {what}")
    if "*" in outputs:
        return outputs
    for output in required:
        if output not in outputs:
            outputs.append(output)
    return outputs


def ensure_standard_json_frontend_outputs(
    compiler_input: Json,
    optimized: bool,
    default_via_ir: bool,
    default_experimental: bool,
    require_bytecode: bool = True,
) -> Json:
    if not isinstance(compiler_input, dict):
        fail("Expected solc Standard JSON input to be a JSON object")
    compiler_input.setdefault("language", "Solidity")
    settings = compiler_input.setdefault("settings", {})
    if not isinstance(settings, dict):
        fail("Malformed solc Standard JSON input: settings must be an object")
    settings.setdefault("viaIR", default_via_ir)
    if default_experimental:
        settings.setdefault("experimental", True)
    output_selection = settings.setdefault("outputSelection", {})
    if not isinstance(output_selection, dict):
        fail("Malformed solc Standard JSON input: outputSelection must be an object")
    by_source = output_selection.setdefault("*", {})
    if not isinstance(by_source, dict):
        fail("Malformed solc Standard JSON outputSelection for source '*'")
    by_source["*"] = append_outputs(
        by_source.get("*"),
        required_contract_outputs(optimized, require_bytecode),
        "contract '*'",
    )
    by_source[""] = append_outputs(by_source.get(""), ["ast"], "source AST")
    return compiler_input


def ensure_standard_json_yul_outputs(
    compiler_input: Json,
    default_experimental: bool,
) -> Json:
    if not isinstance(compiler_input, dict):
        fail("Expected solc Standard JSON input to be a JSON object")
    compiler_input["language"] = "Yul"
    settings = compiler_input.setdefault("settings", {})
    if not isinstance(settings, dict):
        fail("Malformed solc Standard JSON input: settings must be an object")
    if default_experimental:
        settings.setdefault("experimental", True)
    output_selection = settings.setdefault("outputSelection", {})
    if not isinstance(output_selection, dict):
        fail("Malformed solc Standard JSON outputSelection must be an object")
    by_source = output_selection.setdefault("*", {})
    if not isinstance(by_source, dict):
        fail("Malformed solc Standard JSON outputSelection for source '*'")
    by_source["*"] = append_outputs(
        by_source.get("*"),
        ["ast"],
        "Yul source AST",
    )
    return compiler_input


def solc_errors_reject_experimental(errors: Sequence[Any]) -> bool:
    for err in errors:
        if not isinstance(err, dict):
            continue
        message = err.get("formattedMessage") or err.get("message") or ""
        if 'Unknown key "experimental"' in str(message):
            return True
    return False


def run_solc(
    solc: str,
    compiler_input: Json,
    solc_args: Sequence[str] = (),
) -> Json:
    def invoke(input_json: Json) -> Tuple[subprocess.CompletedProcess[str], Json]:
        try:
            completed = subprocess.run(
                [solc, *solc_args, "--standard-json"],
                input=json.dumps(input_json),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except FileNotFoundError:
            fail(f"Could not find solc executable {solc!r}")
        try:
            output = json.loads(completed.stdout)
        except json.JSONDecodeError as exc:
            fail(f"solc did not return JSON: {exc}\nstdout was:\n{completed.stdout}")
        return completed, output

    completed, output = invoke(compiler_input)
    errors = output.get("errors", [])
    severe = [err for err in errors if err.get("severity") == "error"]
    if solc_errors_reject_experimental(severe):
        retry_input = copy.deepcopy(compiler_input)
        settings = retry_input.get("settings")
        if isinstance(settings, dict) and "experimental" in settings:
            del settings["experimental"]
            completed, output = invoke(retry_input)
            errors = output.get("errors", [])
            severe = [err for err in errors if err.get("severity") == "error"]
    if completed.stderr.strip():
        print(completed.stderr, file=sys.stderr)
    if completed.returncode != 0 or severe:
        messages = "\n".join(
            err.get("formattedMessage") or err.get("message") or repr(err)
            for err in severe
        )
        fail(messages or f"solc failed with exit code {completed.returncode}")
    return output


def run_lake_check(lake: str, lean_file: Path, cwd: Path) -> None:
    try:
        completed = subprocess.run(
            [lake, "env", "lean", str(lean_file)],
            cwd=str(cwd),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except FileNotFoundError:
        fail(
            f"Could not find lake executable {lake!r}. "
            "Install Lean with elan and put ~/.elan/bin on PATH."
        )
    if completed.returncode != 0:
        output = "\n".join(
            part
            for part in [completed.stdout.strip(), completed.stderr.strip()]
            if part
        )
        fail(f"`{lake} env lean {lean_file}` failed:\n{output}")


def parse_include_source_arg(value: str) -> Tuple[str, Path]:
    source_name, sep, path_text = value.partition("=")
    if sep:
        if not source_name or not path_text:
            fail(
                "Expected included source in the form [SOURCE_NAME=]PATH, "
                f"got {value!r}"
            )
        return source_name, Path(path_text)
    path = Path(value)
    if not path.name:
        fail(
            "Included source paths without an explicit source name must have a "
            f"file name, got {value!r}"
        )
    return path.name, path


@dataclass
class SoliditySourceFile:
    source_name: str
    path: Path
    content: str


def read_include_source_files(
    values: Sequence[str],
    main_source_name: str,
) -> Dict[str, SoliditySourceFile]:
    sources: Dict[str, SoliditySourceFile] = {}
    seen = {main_source_name}
    for value in values:
        source_name, path = parse_include_source_arg(value)
        if source_name in seen:
            fail(f"Duplicate Solidity source name {source_name!r}")
        try:
            content = path.read_text()
        except FileNotFoundError:
            fail(f"Included Solidity source {path} does not exist")
        sources[source_name] = SoliditySourceFile(
            source_name=source_name,
            path=path,
            content=content,
        )
        seen.add(source_name)
    return sources


def read_include_sources(
    values: Sequence[str],
    main_source_name: str,
) -> Dict[str, str]:
    return {
        source_name: source_file.content
        for source_name, source_file in read_include_source_files(
            values,
            main_source_name,
        ).items()
    }


def collect_local_import_sources(
    main_source_name: str,
    main_content: str,
    main_path: Optional[Path],
    explicit_sources: Dict[str, SoliditySourceFile],
    remappings: Sequence[ImportRemapping] = (),
) -> Dict[str, SoliditySourceFile]:
    sources = dict(explicit_sources)
    known_source_names = {main_source_name, *sources.keys()}
    queue: List[SoliditySourceFile] = []
    if main_path is not None:
        queue.append(
            SoliditySourceFile(
                source_name=main_source_name,
                path=main_path,
                content=main_content,
            )
        )
    queue.extend(sources.values())

    while queue:
        importer = queue.pop(0)
        for import_path in iter_solidity_import_paths(importer.content):
            is_relative = import_path.startswith(("./", "../"))
            if is_relative:
                source_name = resolve_relative_import_source_name(
                    importer.source_name,
                    import_path,
                )
                path = importer.path.parent / import_path
            else:
                source_name = import_path
                path = resolve_remapped_import_path(import_path, remappings)
                if path is None:
                    continue
            if source_name in known_source_names:
                continue
            try:
                content = path.read_text()
            except FileNotFoundError:
                import_kind = "relative" if is_relative else "remapped"
                fail(
                    f"Could not auto-include {import_kind} Solidity import "
                    f"{import_path!r} from {importer.source_name!r}: "
                    f"{path} does not exist. Use --include-source for custom "
                    "source-unit names or --no-auto-include-imports to let solc "
                    "report the import error."
                )
            source = SoliditySourceFile(
                source_name=source_name,
                path=path,
                content=content,
            )
            sources[source_name] = source
            known_source_names.add(source_name)
            queue.append(source)
    return sources


def read_source_input(input_path: Path, source_name: Optional[str]) -> Tuple[str, str]:
    if str(input_path) == "-":
        return source_name or "stdin.sol", sys.stdin.read()
    return source_name or input_path.name, input_path.read_text()


def read_standard_json_input(input_path: Path) -> Json:
    text = sys.stdin.read() if str(input_path) == "-" else input_path.read_text()
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError as exc:
        fail(f"Could not parse solc Standard JSON input: {exc}")
    if not isinstance(parsed, dict):
        fail("Expected solc Standard JSON input to be a JSON object")
    return parsed


def qualified_lean_name(namespace: Optional[str], name: str) -> str:
    if namespace:
        return f"{namespace}.{name}"
    return name


def bytecode_definition_name(
    definition: str,
    object_layout: Sequence[ObjectLayoutEntry],
    local_data_base: Optional[int],
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
) -> str:
    _ = object_layout
    _ = local_data_base
    if linker_symbols:
        return definition + "UncheckedBytecodeImageWithLinkerSymbols"
    return definition + "UncheckedBytecodeImage"


def object_image_definition_name(
    definition: str,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
) -> str:
    if linker_symbols:
        return definition + "UncheckedObjectImageWithLinkerSymbols"
    return definition + "UncheckedObjectImage"


def legacy_bytecode_definition_name(
    definition: str,
    object_layout: Sequence[ObjectLayoutEntry],
    local_data_base: Optional[int],
) -> str:
    if local_data_base is not None:
        return definition + "UncheckedBytecodeWithLocalDataBase"
    if object_layout:
        return definition + "UncheckedBytecodeWithLayout"
    return definition + "UncheckedBytecode"


def render_bytecode_runner(qualified_bytecode_definition: str) -> str:
    return f"""

def evmCompilerRunnerHexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | _ => 'f'

def evmCompilerRunnerByteHex (byte : UInt8) : String :=
  String.singleton (evmCompilerRunnerHexDigit (byte.toNat / 16)) ++
    String.singleton (evmCompilerRunnerHexDigit (byte.toNat % 16))

def evmCompilerRunnerBytesHex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map evmCompilerRunnerByteHex)

def main : IO Unit := do
  match {qualified_bytecode_definition} with
  | some bytes => IO.println ("0x" ++ evmCompilerRunnerBytesHex bytes)
  | none => IO.println "none"
"""


def render_object_image_runner(qualified_image_definition: str) -> str:
    return f"""

def evmCompilerRunnerHexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | _ => 'f'

def evmCompilerRunnerByteHex (byte : UInt8) : String :=
  String.singleton (evmCompilerRunnerHexDigit (byte.toNat / 16)) ++
    String.singleton (evmCompilerRunnerHexDigit (byte.toNat % 16))

def evmCompilerRunnerBytesHex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map evmCompilerRunnerByteHex)

def main : IO Unit := do
  match {qualified_image_definition} with
  | some image =>
      IO.println
        ("bytecode=0x" ++
          evmCompilerRunnerBytesHex
            (EvmCompiler.Assembly.Bytecode.ofList image.bytes))
      for entry in image.immutableReferences do
        for reference in entry.snd do
          IO.println
            ("immutable\\t" ++ entry.fst ++ "\\t" ++
              toString reference.start ++ "\\t" ++
              toString reference.length)
  | none => IO.println "none"
"""


def render_json_file_object_image_runner(
    json_path: Path,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> str:
    linker_symbols_rendered = lean_list(
        [entry.lean_ir() for entry in linker_symbols],
        1,
    )
    return f"""import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.Assembly.Bytecode

def evmCompilerRunnerBridgeJsonPath : String :=
  {lean_string(str(json_path))}

def evmCompilerRunnerLinkerSymbols :
    List (EvmCompiler.Solidity.Frontend.Name × EvmCompiler.Solidity.Frontend.Word) :=
  {linker_symbols_rendered}

def evmCompilerRunnerHexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | _ => 'f'

def evmCompilerRunnerByteHex (byte : UInt8) : String :=
  String.singleton (evmCompilerRunnerHexDigit (byte.toNat / 16)) ++
    String.singleton (evmCompilerRunnerHexDigit (byte.toNat % 16))

def evmCompilerRunnerBytesHex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map evmCompilerRunnerByteHex)

def evmCompilerRunnerTimedIO {{α : Type}} (name : String) (action : IO α) :
    IO α := do
  let start ← IO.monoMsNow
  let value ← action
  let finish ← IO.monoMsNow
  IO.println ("timing\t" ++ name ++ "\t" ++ toString (finish - start))
  pure value

def evmCompilerRunnerTimedPure {{α : Type}} (name : String)
    (thunk : Unit → Option α) : IO (Option α) := do
  let start ← IO.monoMsNow
  let value := thunk ()
  let ok := value.isSome
  let finish ← IO.monoMsNow
  IO.println
    ("timing\t" ++ name ++ "\t" ++ toString (finish - start) ++ "\t" ++
      if ok then "some" else "none")
  pure value

def evmCompilerRunnerDecodeProgram :
    IO EvmCompiler.Solidity.Frontend.Program := do
  let input ← IO.FS.readFile evmCompilerRunnerBridgeJsonPath
  match EvmCompiler.Solidity.Frontend.BridgeJson.parseProgram? input with
  | .ok program => pure program
  | .error err => throw (IO.userError ("bridge JSON decode failed: " ++ err))

def main : IO Unit := do
  let program ←
    evmCompilerRunnerTimedIO "decode" evmCompilerRunnerDecodeProgram
  let image? ←
    evmCompilerRunnerTimedPure "object_image" (fun _ =>
      program.object.bytecodeImageUncheckedWithLinkerSymbols?
        evmCompilerRunnerLinkerSymbols)
  match image? with
  | some image =>
      IO.println
        ("bytecode=0x" ++
          evmCompilerRunnerBytesHex
            (EvmCompiler.Assembly.Bytecode.ofList image.bytes))
      for entry in image.immutableReferences do
        for reference in entry.snd do
          IO.println
            ("immutable\\t" ++ entry.fst ++ "\\t" ++
              toString reference.start ++ "\\t" ++
              toString reference.length)
  | none => IO.println "none"
"""


def render_json_file_backend_check_runner(
    json_path: Path,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> str:
    linker_symbols_rendered = lean_list(
        [entry.lean_ir() for entry in linker_symbols],
        1,
    )
    return f"""import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Objects.Compiler

def evmCompilerRunnerBridgeJsonPath : String :=
  {lean_string(str(json_path))}

def evmCompilerRunnerLinkerSymbols :
    List (EvmCompiler.Solidity.Frontend.Name × EvmCompiler.Solidity.Frontend.Word) :=
  {linker_symbols_rendered}

def evmCompilerRunnerStageSome {{α : Type}} (value : Option α) : Bool :=
  match value with
  | some _ => true
  | none => false

def evmCompilerRunnerPrintStage (name : String) (ok : Bool) : IO Unit := do
  IO.println
    ("stage\\t" ++ name ++ "\\t" ++ if ok then "some" else "none")

def evmCompilerRunnerPrintLocalsProc
    (proc : EvmCompiler.Locals.Proc) : IO Unit := do
  IO.println
    ("locals_proc\\t" ++ proc.name ++ "\\t" ++
      if (proc.toExpressions?).isSome then "some" else "none")

def evmCompilerRunnerLocalsStmtKind :
    EvmCompiler.Locals.Stmt → String
  | .expr _ => "expr"
  | .exprs _ => "exprs"
  | .let_ name _ => "let:" ++ name
  | .assign name _ => "assign:" ++ name
  | .assignTop name => "assignTop:" ++ name
  | .assignTopWithOffset offset name =>
      "assignTopWithOffset:" ++ toString offset ++ ":" ++ name
  | .promoteName name => "promoteName:" ++ name
  | .discardName name => "discardName:" ++ name
  | .cleanupTo layout => "cleanupTo:" ++ toString layout.length
  | .block _ => "block"
  | .if_ _ _ => "if"
  | .switch _ _ _ => "switch"
  | .for_ _ _ _ _ => "for"
  | .brk => "break"
  | .cont => "continue"
  | .leave => "leave"
  | .call name => "call:" ++ name
  | .terminal _ => "terminal"
  | .terminalArgs _ _ => "terminalArgs"

mutual
  partial def evmCompilerRunnerLocalsExprVars {{results : Nat}} :
      EvmCompiler.Locals.Expr results → List EvmCompiler.Locals.Name
    | .lit _ => []
    | .var name => [name]
    | .code _ => []
    | .prim _ args => evmCompilerRunnerLocalsExprSeqVars args

  partial def evmCompilerRunnerLocalsExprSeqVars {{results : Nat}} :
      EvmCompiler.Locals.ExprSeq results → List EvmCompiler.Locals.Name
    | .nil => []
    | .cons head tail =>
        evmCompilerRunnerLocalsExprVars head ++
          evmCompilerRunnerLocalsExprSeqVars tail
end

def evmCompilerRunnerPrintLocalsVarDepths
    (owner : String) (idx : Nat) (ctx : EvmCompiler.Locals.Ctx)
    (names : List EvmCompiler.Locals.Name) : IO Unit := do
  for name in names do
    let depth :=
      match EvmCompiler.Locals.Layout.lookupDepth? name ctx.layout with
      | some value => toString value
      | none => "missing"
    IO.println
      ("locals_var\\t" ++ owner ++ "\\t" ++ toString idx ++ "\\t" ++
        name ++ "\\t" ++ depth)

def evmCompilerRunnerPrintLocalsTargetDepth
    (owner : String) (idx : Nat) (ctx : EvmCompiler.Locals.Ctx)
    (name : EvmCompiler.Locals.Name) (offset : Nat) : IO Unit := do
  let depth? := EvmCompiler.Locals.Layout.lookupDepth? name ctx.layout
  let depth :=
    match depth? with
    | some value => toString value
    | none => "missing"
  let accessDepth :=
    match depth? with
    | some value => toString (offset + value)
    | none => "missing"
  IO.println
    ("locals_target\\t" ++ owner ++ "\\t" ++ toString idx ++ "\\t" ++
      name ++ "\\t" ++ depth ++ "\\t" ++ accessDepth)

def evmCompilerRunnerPrintLocalsStmtFailureDetail
    (owner : String) (idx : Nat) (ctx : EvmCompiler.Locals.Ctx)
    (stmt : EvmCompiler.Locals.Stmt) : IO Unit := do
  IO.println
    ("locals_layout\\t" ++ owner ++ "\\t" ++ toString idx ++ "\\t" ++
      toString ctx.layout.length ++ "\\t" ++ toString ctx.layout)
  match stmt with
  | .expr expr =>
      evmCompilerRunnerPrintLocalsVarDepths owner idx ctx
        (evmCompilerRunnerLocalsExprVars expr)
  | .exprs exprs =>
      evmCompilerRunnerPrintLocalsVarDepths owner idx ctx
        (evmCompilerRunnerLocalsExprSeqVars exprs)
  | .let_ _ value =>
      evmCompilerRunnerPrintLocalsVarDepths owner idx ctx
        (evmCompilerRunnerLocalsExprVars value)
  | .assign name value =>
      evmCompilerRunnerPrintLocalsTargetDepth owner idx ctx name 0
      evmCompilerRunnerPrintLocalsVarDepths owner idx ctx
        (evmCompilerRunnerLocalsExprVars value)
  | .assignTop name =>
      evmCompilerRunnerPrintLocalsTargetDepth owner idx ctx name 0
  | .assignTopWithOffset offset name =>
      evmCompilerRunnerPrintLocalsTargetDepth owner idx ctx name offset
  | .terminalArgs _ args =>
      evmCompilerRunnerPrintLocalsVarDepths owner idx ctx
        (evmCompilerRunnerLocalsExprSeqVars args)
  | _ => pure ()

partial def evmCompilerRunnerPrintLocalsStmtTrace
    (owner : String) (idx : Nat) (ctx : EvmCompiler.Locals.Ctx)
    (stmts : List EvmCompiler.Locals.Stmt) : IO Unit := do
  match stmts with
  | [] => pure ()
  | stmt :: rest =>
      let result := EvmCompiler.Locals.Stmt.compile ctx stmt
      IO.println
        ("locals_stmt\\t" ++ owner ++ "\\t" ++ toString idx ++ "\\t" ++
          evmCompilerRunnerLocalsStmtKind stmt ++ "\\t" ++
          if result.isSome then "some" else "none")
      match result with
      | some (_code, nextCtx) =>
          evmCompilerRunnerPrintLocalsStmtTrace owner (idx + 1) nextCtx rest
      | none =>
          evmCompilerRunnerPrintLocalsStmtFailureDetail owner idx ctx stmt
          match stmt with
          | .block body =>
              evmCompilerRunnerPrintLocalsStmtTrace
                (owner ++ "/" ++ toString idx ++ ".block") 0 ctx body.stmts
          | .if_ _ body =>
              evmCompilerRunnerPrintLocalsStmtTrace
                (owner ++ "/" ++ toString idx ++ ".if") 0 ctx body.stmts
          | .switch _ cases defaultBody =>
              for pair in cases do
                evmCompilerRunnerPrintLocalsStmtTrace
                  (owner ++ "/" ++ toString idx ++ ".switch") 0 ctx pair.snd.stmts
              match defaultBody with
              | some body =>
                  evmCompilerRunnerPrintLocalsStmtTrace
                    (owner ++ "/" ++ toString idx ++ ".default") 0 ctx body.stmts
              | none => pure ()
          | .for_ init _ post body =>
              let initBase := ctx.withoutLoopControl
              evmCompilerRunnerPrintLocalsStmtTrace
                (owner ++ "/" ++ toString idx ++ ".for.init") 0 initBase
                init.stmts
              match EvmCompiler.Locals.Block.compileOpen initBase init with
              | some (_initCode, initCtx) =>
                  evmCompilerRunnerPrintLocalsStmtTrace
                    (owner ++ "/" ++ toString idx ++ ".for.post") 0
                    initCtx.withoutLoopControl post.stmts
                  evmCompilerRunnerPrintLocalsStmtTrace
                    (owner ++ "/" ++ toString idx ++ ".for.body") 0
                    (initCtx.withLoopControl initCtx.layout.length) body.stmts
              | none => pure ()
          | _ => pure ()

def evmCompilerRunnerFirstNone :
    List (String × Bool) → String
  | [] => "none"
  | (name, ok) :: rest =>
      if ok then evmCompilerRunnerFirstNone rest else name

def evmCompilerRunnerHexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | _ => 'f'

def evmCompilerRunnerByteHex (byte : UInt8) : String :=
  String.singleton (evmCompilerRunnerHexDigit (byte.toNat / 16)) ++
    String.singleton (evmCompilerRunnerHexDigit (byte.toNat % 16))

def evmCompilerRunnerBytesHex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map evmCompilerRunnerByteHex)

def evmCompilerRunnerTimedIO {{α : Type}} (name : String) (action : IO α) :
    IO α := do
  let start ← IO.monoMsNow
  let value ← action
  let finish ← IO.monoMsNow
  IO.println ("timing\t" ++ name ++ "\t" ++ toString (finish - start))
  pure value

def evmCompilerRunnerTimedPure {{α : Type}} (name : String)
    (thunk : Unit → Option α) : IO (Option α) := do
  let start ← IO.monoMsNow
  let value := thunk ()
  let ok := value.isSome
  let finish ← IO.monoMsNow
  IO.println
    ("timing\t" ++ name ++ "\t" ++ toString (finish - start) ++ "\t" ++
      if ok then "some" else "none")
  pure value

def evmCompilerRunnerDecodeProgram :
    IO EvmCompiler.Solidity.Frontend.Program := do
  let input ← IO.FS.readFile evmCompilerRunnerBridgeJsonPath
  match EvmCompiler.Solidity.Frontend.BridgeJson.parseProgram? input with
  | .ok program => pure program
  | .error err => throw (IO.userError ("bridge JSON decode failed: " ++ err))

def main : IO Unit := do
  let program ←
    evmCompilerRunnerTimedIO "decode" evmCompilerRunnerDecodeProgram
  let object := program.object
  let toYulContract? ←
    evmCompilerRunnerTimedPure "to_yul_contract" (fun _ =>
      object.toYulContract?)
  let lowerCodeUnchecked? ←
    evmCompilerRunnerTimedPure "lower_code_unchecked" (fun _ =>
      object.lowerCodeUnchecked?)
  let functionsCompile? ←
    evmCompilerRunnerTimedPure "functions_compile" (fun _ => do
    let lower ← lowerCodeUnchecked?
    EvmCompiler.Functions.Program.compile? lower)
  let functionsSourceAccepted? ←
    evmCompilerRunnerTimedPure "functions_source_accepted" (fun _ => do
    let lower ← lowerCodeUnchecked?
    if EvmCompiler.Functions.SourceAcceptedCheck.Program.sourceAccepted? lower then
      some ()
    else
      none)
  let functionsToLocals? ←
    evmCompilerRunnerTimedPure "functions_to_locals" (fun _ => do
    let lower ← lowerCodeUnchecked?
    EvmCompiler.Functions.Program.toLocals? lower)
  let localsToExpressions? ←
    evmCompilerRunnerTimedPure "locals_to_expressions" (fun _ => do
    let locals ← functionsToLocals?
    locals.toExpressions?)
  let localsCompile? ←
    evmCompilerRunnerTimedPure "locals_compile" (fun _ => do
    let locals ← functionsToLocals?
    locals.compile?)
  let expressionsCompile? ←
    evmCompilerRunnerTimedPure "expressions_compile" (fun _ => do
    let expressions ← localsToExpressions?
    expressions.compile?)
  let childImages? ←
    evmCompilerRunnerTimedPure "child_images" (fun _ =>
    EvmCompiler.Solidity.Frontend.Object.List.bytecodeImagesUncheckedWithLinkerSymbols?
      object.objects evmCompilerRunnerLinkerSymbols)
  let immutableNames := object.loadImmutableNames
  let zeroImmutableValues :=
    EvmCompiler.Solidity.Frontend.ImmutableReference.zeroEntries immutableNames
  let markerImmutableValues :=
    EvmCompiler.Solidity.Frontend.ImmutableReference.markerEntriesFromNat
      0 immutableNames
  let items? ←
    evmCompilerRunnerTimedPure "payload_items" (fun _ => do
    let childImages ← childImages?
    object.payloadItems? childImages)
  let childImmutableReferences? := do
    let childImages ← childImages?
    some
      (EvmCompiler.Solidity.Frontend.ObjectImage.immutableReferenceEntries
        childImages)
  let dataSizes? ←
    evmCompilerRunnerTimedPure "data_sizes" (fun _ => do
    let childImages ← childImages?
    let items ← items?
    EvmCompiler.Solidity.Frontend.ObjectItemRef.List.dataSizeEntries?
      object.data childImages items)
  let layout0? ←
    evmCompilerRunnerTimedPure "layout0" (fun _ => do
    let childImages ← childImages?
    let items ← items?
    EvmCompiler.Solidity.Frontend.ObjectItemRef.List.objectLayoutEntriesFromNat?
      object.data childImages 0 items)
  let dataOffsets0? ←
    evmCompilerRunnerTimedPure "data_offsets0" (fun _ => do
    let childImages ← childImages?
    let items ← items?
    EvmCompiler.Solidity.Frontend.ObjectItemRef.List.dataOffsetEntriesFromNat?
      object.data childImages 0 items)
  let payload? ←
    evmCompilerRunnerTimedPure "payload" (fun _ => do
    let childImages ← childImages?
    let items ← items?
    EvmCompiler.Solidity.Frontend.ObjectItemRef.List.payloadBytes?
      object.data childImages items)
  let placeholderContext? ←
    evmCompilerRunnerTimedPure "placeholder_context" (fun _ => do
    let layout0 ← layout0?
    let dataSizes ← dataSizes?
    let dataOffsets0 ← dataOffsets0?
    let childImmutableReferences ← childImmutableReferences?
    let placeholderLayout : EvmCompiler.Solidity.Frontend.ObjectLayout :=
      {{ entries := layout0 }}
    let placeholderContext : EvmCompiler.Solidity.Frontend.ObjectBuiltinContext :=
      {{ layout := placeholderLayout
        dataSizes := dataSizes
        dataOffsets := dataOffsets0
        linkerSymbols := evmCompilerRunnerLinkerSymbols
        immutableValues := zeroImmutableValues
        immutableReferences := childImmutableReferences
        selfSize? := some (object.name, EvmYul.UInt256.ofNat 0) }}
    some placeholderContext)
  let placeholderResolvedObject? ←
    evmCompilerRunnerTimedPure "placeholder_resolved_object" (fun _ => do
    let context ← placeholderContext?
    object.resolveObjectBuiltinsIn? context)
  let placeholderLowerUnchecked? ←
    evmCompilerRunnerTimedPure "placeholder_lower_unchecked" (fun _ => do
    let resolved ← placeholderResolvedObject?
    resolved.lowerCodeUnchecked?)
  let placeholderFunctionsCompile? ←
    evmCompilerRunnerTimedPure "placeholder_functions_compile" (fun _ => do
    let lower ← placeholderLowerUnchecked?
    EvmCompiler.Functions.Program.compile? lower)
  let placeholderFunctionsToLocals? ←
    evmCompilerRunnerTimedPure "placeholder_functions_to_locals" (fun _ => do
    let lower ← placeholderLowerUnchecked?
    EvmCompiler.Functions.Program.toLocals? lower)
  let placeholderLocalsToExpressions? ←
    evmCompilerRunnerTimedPure "placeholder_locals_to_expressions" (fun _ => do
    let locals ← placeholderFunctionsToLocals?
    locals.toExpressions?)
  let placeholderLocalsCompile? ←
    evmCompilerRunnerTimedPure "placeholder_locals_compile" (fun _ => do
    let locals ← placeholderFunctionsToLocals?
    locals.compile?)
  let placeholderExpressionsCompile? ←
    evmCompilerRunnerTimedPure "placeholder_expressions_compile" (fun _ => do
    let expressions ← placeholderLocalsToExpressions?
    expressions.compile?)
  let placeholderCode? ←
    evmCompilerRunnerTimedPure "placeholder_code" (fun _ => do
    let context ← placeholderContext?
    object.codeBytesUncheckedIn? context)
  let codeBase? := do
    let placeholderCode ← placeholderCode?
    some placeholderCode.length
  let layout? ←
    evmCompilerRunnerTimedPure "layout" (fun _ => do
    let childImages ← childImages?
    let items ← items?
    let codeBase ← codeBase?
    EvmCompiler.Solidity.Frontend.ObjectItemRef.List.objectLayoutEntriesFromNat?
      object.data childImages codeBase items)
  let dataOffsets? ←
    evmCompilerRunnerTimedPure "data_offsets" (fun _ => do
    let childImages ← childImages?
    let items ← items?
    let codeBase ← codeBase?
    EvmCompiler.Solidity.Frontend.ObjectItemRef.List.dataOffsetEntriesFromNat?
      object.data childImages codeBase items)
  let codeContext? ←
    evmCompilerRunnerTimedPure "code_context" (fun _ => do
    let codeBase ← codeBase?
    let payload ← payload?
    let dataSizes ← dataSizes?
    let layout ← layout?
    let dataOffsets ← dataOffsets?
    let childImmutableReferences ← childImmutableReferences?
    let selfSize := EvmYul.UInt256.ofNat (codeBase + payload.length)
    let context : EvmCompiler.Solidity.Frontend.ObjectBuiltinContext :=
      {{ layout := {{ entries := layout }}
        dataSizes := dataSizes
        dataOffsets := dataOffsets
        linkerSymbols := evmCompilerRunnerLinkerSymbols
        immutableValues := zeroImmutableValues
        immutableReferences := childImmutableReferences
        selfSize? := some (object.name, selfSize) }}
    some context)
  let codeResolvedObject? ←
    evmCompilerRunnerTimedPure "code_resolved_object" (fun _ => do
    let context ← codeContext?
    object.resolveObjectBuiltinsIn? context)
  let codeLowerUnchecked? ←
    evmCompilerRunnerTimedPure "code_lower_unchecked" (fun _ => do
    let resolved ← codeResolvedObject?
    resolved.lowerCodeUnchecked?)
  let codeFunctionsCompile? ←
    evmCompilerRunnerTimedPure "code_functions_compile" (fun _ => do
    let lower ← codeLowerUnchecked?
    EvmCompiler.Functions.Program.compile? lower)
  let codeFunctionsToLocals? ←
    evmCompilerRunnerTimedPure "code_functions_to_locals" (fun _ => do
    let lower ← codeLowerUnchecked?
    EvmCompiler.Functions.Program.toLocals? lower)
  let codeLocalsToExpressions? ←
    evmCompilerRunnerTimedPure "code_locals_to_expressions" (fun _ => do
    let locals ← codeFunctionsToLocals?
    locals.toExpressions?)
  let codeLocalsCompile? ←
    evmCompilerRunnerTimedPure "code_locals_compile" (fun _ => do
    let locals ← codeFunctionsToLocals?
    locals.compile?)
  let codeExpressionsCompile? ←
    evmCompilerRunnerTimedPure "code_expressions_compile" (fun _ => do
    let expressions ← codeLocalsToExpressions?
    expressions.compile?)
  let code? ←
    evmCompilerRunnerTimedPure "code" (fun _ => do
    let context ← codeContext?
    object.codeBytesUncheckedIn? context)
  let markerCode? ←
    evmCompilerRunnerTimedPure "marker_code" (fun _ => do
    let codeBase ← codeBase?
    let payload ← payload?
    let dataSizes ← dataSizes?
    let layout ← layout?
    let dataOffsets ← dataOffsets?
    let childImmutableReferences ← childImmutableReferences?
    let selfSize := EvmYul.UInt256.ofNat (codeBase + payload.length)
    let context : EvmCompiler.Solidity.Frontend.ObjectBuiltinContext :=
      {{ layout := {{ entries := layout }}
        dataSizes := dataSizes
        dataOffsets := dataOffsets
        linkerSymbols := evmCompilerRunnerLinkerSymbols
        immutableValues := markerImmutableValues
        immutableReferences := childImmutableReferences
        selfSize? := some (object.name, selfSize) }}
    object.codeBytesUncheckedIn? context)
  let objectImage? ←
    evmCompilerRunnerTimedPure "object_image" (fun _ =>
    object.bytecodeImageUncheckedWithLinkerSymbols?
      evmCompilerRunnerLinkerSymbols)
  let computedObjectData? ←
    evmCompilerRunnerTimedPure "computed_object_data" (fun _ =>
    object.computedObjectDataWithLinkerSymbols?
      evmCompilerRunnerLinkerSymbols)
  let resolvedObjectData? ←
    evmCompilerRunnerTimedPure "resolved_object_data" (fun _ =>
    program.resolveObjectBuiltinsWithComputedObjectDataAndLinkerSymbols?
      evmCompilerRunnerLinkerSymbols)
  let solcValidatedObjectData? ←
    evmCompilerRunnerTimedPure "solc_validation" (fun _ => do
    let resolved ← resolvedObjectData?
    resolved.object.toSolcYulProgram?)
  let stages :=
    [ ("to_yul_contract", evmCompilerRunnerStageSome toYulContract?)
    , ("lower_code_unchecked", evmCompilerRunnerStageSome lowerCodeUnchecked?)
    , ("functions_source_accepted", evmCompilerRunnerStageSome functionsSourceAccepted?)
    , ("functions_to_locals", evmCompilerRunnerStageSome functionsToLocals?)
    , ("locals_to_expressions", evmCompilerRunnerStageSome localsToExpressions?)
    , ("locals_compile", evmCompilerRunnerStageSome localsCompile?)
    , ("expressions_compile", evmCompilerRunnerStageSome expressionsCompile?)
    , ("functions_compile", evmCompilerRunnerStageSome functionsCompile?)
    , ("child_images", evmCompilerRunnerStageSome childImages?)
    , ("payload_items", evmCompilerRunnerStageSome items?)
    , ("data_sizes", evmCompilerRunnerStageSome dataSizes?)
    , ("layout0", evmCompilerRunnerStageSome layout0?)
    , ("data_offsets0", evmCompilerRunnerStageSome dataOffsets0?)
    , ("payload", evmCompilerRunnerStageSome payload?)
    , ("placeholder_context", evmCompilerRunnerStageSome placeholderContext?)
    , ("placeholder_resolved_object", evmCompilerRunnerStageSome placeholderResolvedObject?)
    , ("placeholder_lower_unchecked", evmCompilerRunnerStageSome placeholderLowerUnchecked?)
    , ("placeholder_functions_to_locals", evmCompilerRunnerStageSome placeholderFunctionsToLocals?)
    , ("placeholder_locals_to_expressions", evmCompilerRunnerStageSome placeholderLocalsToExpressions?)
    , ("placeholder_locals_compile", evmCompilerRunnerStageSome placeholderLocalsCompile?)
    , ("placeholder_expressions_compile", evmCompilerRunnerStageSome placeholderExpressionsCompile?)
    , ("placeholder_functions_compile", evmCompilerRunnerStageSome placeholderFunctionsCompile?)
    , ("placeholder_code", evmCompilerRunnerStageSome placeholderCode?)
    , ("layout", evmCompilerRunnerStageSome layout?)
    , ("data_offsets", evmCompilerRunnerStageSome dataOffsets?)
    , ("code_context", evmCompilerRunnerStageSome codeContext?)
    , ("code_resolved_object", evmCompilerRunnerStageSome codeResolvedObject?)
    , ("code_lower_unchecked", evmCompilerRunnerStageSome codeLowerUnchecked?)
    , ("code_functions_to_locals", evmCompilerRunnerStageSome codeFunctionsToLocals?)
    , ("code_locals_to_expressions", evmCompilerRunnerStageSome codeLocalsToExpressions?)
    , ("code_locals_compile", evmCompilerRunnerStageSome codeLocalsCompile?)
    , ("code_expressions_compile", evmCompilerRunnerStageSome codeExpressionsCompile?)
    , ("code_functions_compile", evmCompilerRunnerStageSome codeFunctionsCompile?)
    , ("code", evmCompilerRunnerStageSome code?)
    , ("marker_code", evmCompilerRunnerStageSome markerCode?)
    , ("computed_object_data", evmCompilerRunnerStageSome computedObjectData?)
    , ("resolved_object_data", evmCompilerRunnerStageSome resolvedObjectData?)
    , ("solc_validation", evmCompilerRunnerStageSome solcValidatedObjectData?)
    , ("object_image", evmCompilerRunnerStageSome objectImage?)
    ]
  let objectImageOk :=
    evmCompilerRunnerStageSome objectImage? &&
      evmCompilerRunnerStageSome solcValidatedObjectData?
  let firstNone :=
    if objectImageOk then
      "none"
    else
      evmCompilerRunnerFirstNone stages
  IO.println
    ("lean_backend_check=" ++ if objectImageOk then "pass" else "fail")
  IO.println ("source=" ++ program.source)
  IO.println ("contract=" ++ program.contract)
  IO.println ("object=" ++ object.name)
  for stage in stages do
    evmCompilerRunnerPrintStage stage.fst stage.snd
  if !objectImageOk then
    match functionsToLocals? with
    | none => pure ()
    | some locals =>
        IO.println
          ("locals_body\\tmain\\t" ++
            if (EvmCompiler.Locals.Block.compile
                  EvmCompiler.Locals.Ctx.initial locals.body).isSome then
              "some"
            else
              "none")
        evmCompilerRunnerPrintLocalsStmtTrace
          "main" 0 EvmCompiler.Locals.Ctx.initial locals.body.stmts
        for proc in locals.procs do
          evmCompilerRunnerPrintLocalsProc proc
          evmCompilerRunnerPrintLocalsStmtTrace
            proc.name 0
            (EvmCompiler.Locals.Ctx.procEntryWithLayoutAndRetc
              proc.entryLayout proc.retc)
            proc.body.stmts
    match placeholderFunctionsToLocals? with
    | none => pure ()
    | some locals =>
        IO.println
          ("locals_body\\tplaceholder_main\\t" ++
            if (EvmCompiler.Locals.Block.compile
                  EvmCompiler.Locals.Ctx.initial locals.body).isSome then
              "some"
            else
              "none")
        evmCompilerRunnerPrintLocalsStmtTrace
          "placeholder_main" 0 EvmCompiler.Locals.Ctx.initial locals.body.stmts
        for proc in locals.procs do
          IO.println
            ("locals_proc\\tplaceholder:" ++ proc.name ++ "\\t" ++
              if (proc.toExpressions?).isSome then "some" else "none")
          evmCompilerRunnerPrintLocalsStmtTrace
            ("placeholder:" ++ proc.name) 0
            (EvmCompiler.Locals.Ctx.procEntryWithLayoutAndRetc
              proc.entryLayout proc.retc)
            proc.body.stmts
  IO.println ("first_none=" ++ firstNone)
  match objectImage? with
  | some image =>
      IO.println ("bytecode_bytes=" ++ toString image.bytes.length)
  | none =>
      pure ()
"""


def render_json_file_decode_runner(json_path: Path) -> str:
    return f"""import EvmCompiler.Solidity.BridgeJson

def evmCompilerRunnerBridgeJsonPath : String :=
  {lean_string(str(json_path))}

def main : IO Unit := do
  let input ← IO.FS.readFile evmCompilerRunnerBridgeJsonPath
  match EvmCompiler.Solidity.Frontend.BridgeJson.parseProgram? input with
  | .ok program =>
      let object := program.object
      IO.println "lean_bridge_json_decode=pass"
      IO.println ("source=" ++ program.source)
      IO.println ("contract=" ++ program.contract)
      IO.println ("object=" ++ object.name)
      IO.println ("dispatcher_stmts=" ++ toString object.dispatcher.length)
      IO.println ("functions=" ++ toString object.functions.length)
      IO.println ("data_sections=" ++ toString object.data.length)
      IO.println ("subobjects=" ++ toString object.objects.length)
      IO.println ("items=" ++ toString object.items.length)
  | .error err =>
      throw (IO.userError ("bridge JSON decode failed: " ++ err))
"""


def run_lake_bytecode(lake: str, lean_source: str, cwd: Path) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="evm_compiler_bytecode_", delete=False
    ) as handle:
        handle.write(lean_source)
        temp_path = Path(handle.name)
    try:
        try:
            completed = subprocess.run(
                [lake, "env", "lean", "--run", str(temp_path)],
                cwd=str(cwd),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except FileNotFoundError:
            fail(
                f"Could not find lake executable {lake!r}. "
                "Install Lean with elan and put ~/.elan/bin on PATH."
            )
        if completed.returncode != 0:
            output = "\n".join(
                part
                for part in [
                    f"returncode={completed.returncode}",
                    completed.stdout.strip(),
                    completed.stderr.strip(),
                ]
                if part
            )
            fail(f"`{lake} env lean --run {temp_path}` failed:\n{output}")
        lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
        if not lines:
            fail("Lean bytecode runner produced no output")
        bytecode = lines[-1]
        if bytecode == "none":
            fail(
                "unchecked bytecode generation returned none; the selected object "
                "likely needs object layout/data-base resolution or uses unsupported Yul"
            )
        if not re.fullmatch(r"0x[0-9a-f]*", bytecode):
            fail(f"Lean bytecode runner produced unexpected output: {bytecode!r}")
        return bytecode
    finally:
        try:
            temp_path.unlink()
        except OSError:
            pass


def run_lake_bridge_json_decode(lake: str, lean_source: str, cwd: Path) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="evm_compiler_bridge_json_decode_", delete=False
    ) as handle:
        handle.write(lean_source)
        temp_path = Path(handle.name)
    try:
        try:
            completed = subprocess.run(
                [lake, "env", "lean", "--run", str(temp_path)],
                cwd=str(cwd),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except FileNotFoundError:
            fail(
                f"Could not find lake executable {lake!r}. "
                "Install Lean with elan and put ~/.elan/bin on PATH."
            )
        if completed.returncode != 0:
            output = "\n".join(
                part
                for part in [
                    f"returncode={completed.returncode}",
                    completed.stdout.strip(),
                    completed.stderr.strip(),
                ]
                if part
            )
            fail(f"`{lake} env lean --run {temp_path}` failed:\n{output}")
        if "lean_bridge_json_decode=pass" not in completed.stdout.splitlines():
            fail("Lean bridge JSON decode runner did not report success")
        return completed.stdout
    finally:
        try:
            temp_path.unlink()
        except OSError:
            pass


def parse_bridge_json_decode_output(output: str) -> Json:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines or lines[0] != "lean_bridge_json_decode=pass":
        fail("Lean bridge JSON decode runner did not report success")
    numeric_fields = {
        "dispatcher_stmts",
        "functions",
        "data_sections",
        "subobjects",
        "items",
    }
    summary: Json = {}
    for line in lines[1:]:
        key, sep, value = line.partition("=")
        if not sep or not key:
            fail(f"Lean bridge JSON decode runner produced malformed line: {line!r}")
        if key in numeric_fields:
            try:
                summary[key] = int(value)
            except ValueError:
                fail(
                    "Lean bridge JSON decode runner produced malformed numeric "
                    f"field: {line!r}"
                )
        else:
            summary[key] = value
    for required in ["source", "contract", "object"]:
        if required not in summary:
            fail(
                "Lean bridge JSON decode runner did not print required field "
                f"{required!r}"
            )
    return summary


def parse_backend_check_output(output: str) -> Json:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    status_lines = [
        line.removeprefix("lean_backend_check=")
        for line in lines
        if line.startswith("lean_backend_check=")
    ]
    if len(status_lines) != 1:
        fail("Lean backend check runner did not report status")
    status = status_lines[0]
    if status not in {"pass", "fail"}:
        fail(f"Lean backend check runner produced invalid status: {status!r}")
    summary: Json = {
        "status": status,
        "stages": {},
        "timingsMs": {},
        "localsBodies": {},
        "localsProcs": {},
        "localsStmtTrace": [],
        "localsLayouts": [],
        "localsVars": [],
        "localsTargets": [],
    }
    numeric_fields = {"bytecode_bytes"}
    for line in lines:
        if line.startswith("lean_backend_check="):
            continue
        if line.startswith("timing\t"):
            parts = line.split("\t")
            if len(parts) < 3 or not parts[1]:
                fail(f"Lean backend check runner produced malformed timing: {line!r}")
            try:
                summary["timingsMs"][parts[1]] = int(parts[2])
            except ValueError:
                fail(
                    "Lean backend check runner produced malformed timing "
                    f"duration: {line!r}"
                )
            continue
        if line.startswith("stage\t"):
            parts = line.split("\t")
            if len(parts) != 3 or not parts[1] or parts[2] not in {"some", "none"}:
                fail(f"Lean backend check runner produced malformed stage: {line!r}")
            summary["stages"][parts[1]] = parts[2]
            continue
        if line.startswith("locals_body\t"):
            parts = line.split("\t")
            if len(parts) != 3 or not parts[1] or parts[2] not in {"some", "none"}:
                fail(
                    "Lean backend check runner produced malformed locals body: "
                    f"{line!r}"
                )
            summary["localsBodies"][parts[1]] = parts[2]
            if parts[1] == "main":
                summary["localsBody"] = parts[2]
            continue
        if line.startswith("locals_proc\t"):
            parts = line.split("\t")
            if len(parts) != 3 or not parts[1] or parts[2] not in {"some", "none"}:
                fail(
                    "Lean backend check runner produced malformed locals proc: "
                    f"{line!r}"
                )
            summary["localsProcs"][parts[1]] = parts[2]
            continue
        if line.startswith("locals_stmt\t"):
            parts = line.split("\t")
            if (
                len(parts) != 5
                or not parts[1]
                or not parts[3]
                or parts[4] not in {"some", "none"}
            ):
                fail(
                    "Lean backend check runner produced malformed locals stmt: "
                    f"{line!r}"
                )
            try:
                index = int(parts[2])
            except ValueError:
                fail(
                    "Lean backend check runner produced malformed locals stmt "
                    f"index: {line!r}"
                )
            summary["localsStmtTrace"].append(
                {
                    "owner": parts[1],
                    "index": index,
                    "kind": parts[3],
                    "status": parts[4],
                }
            )
            continue
        if line.startswith("locals_layout\t"):
            parts = line.split("\t", 4)
            if len(parts) != 5 or not parts[1]:
                fail(
                    "Lean backend check runner produced malformed locals layout: "
                    f"{line!r}"
                )
            try:
                index = int(parts[2])
                length = int(parts[3])
            except ValueError:
                fail(
                    "Lean backend check runner produced malformed locals layout "
                    f"index/length: {line!r}"
                )
            summary["localsLayouts"].append(
                {
                    "owner": parts[1],
                    "index": index,
                    "length": length,
                    "layout": parts[4],
                }
            )
            continue
        if line.startswith("locals_var\t"):
            parts = line.split("\t")
            if len(parts) != 5 or not parts[1] or not parts[3] or not parts[4]:
                fail(
                    "Lean backend check runner produced malformed locals var: "
                    f"{line!r}"
                )
            try:
                index = int(parts[2])
            except ValueError:
                fail(
                    "Lean backend check runner produced malformed locals var "
                    f"index: {line!r}"
                )
            summary["localsVars"].append(
                {
                    "owner": parts[1],
                    "index": index,
                    "name": parts[3],
                    "depth": parts[4],
                }
            )
            continue
        if line.startswith("locals_target\t"):
            parts = line.split("\t")
            if (
                len(parts) != 6
                or not parts[1]
                or not parts[3]
                or not parts[4]
                or not parts[5]
            ):
                fail(
                    "Lean backend check runner produced malformed locals target: "
                    f"{line!r}"
                )
            try:
                index = int(parts[2])
            except ValueError:
                fail(
                    "Lean backend check runner produced malformed locals target "
                    f"index: {line!r}"
                )
            summary["localsTargets"].append(
                {
                    "owner": parts[1],
                    "index": index,
                    "name": parts[3],
                    "depth": parts[4],
                    "accessDepth": parts[5],
                }
            )
            continue
        key, sep, value = line.partition("=")
        if not sep or not key:
            fail(f"Lean backend check runner produced malformed line: {line!r}")
        if key in numeric_fields:
            try:
                summary[key] = int(value)
            except ValueError:
                fail(
                    "Lean backend check runner produced malformed numeric "
                    f"field: {line!r}"
                )
        else:
            summary[key] = value
    for required in ["source", "contract", "object", "first_none"]:
        if required not in summary:
            fail(
                "Lean backend check runner did not print required field "
                f"{required!r}"
            )
    object_image_stage = summary["stages"].get("object_image")
    if status == "pass" and summary["first_none"] != "none":
        fail(
            "Lean backend check runner reported pass with first_none="
            f"{summary['first_none']!r}"
        )
    if status == "pass" and object_image_stage != "some":
        fail(
            "Lean backend check runner reported pass without object_image=some"
        )
    if status == "fail" and summary["first_none"] == "none":
        fail("Lean backend check runner reported fail with first_none=none")
    return summary


def parse_object_image_output(output: str) -> CompiledObjectImage:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines:
        fail("Lean object-image runner produced no output")
    if lines[-1] == "none":
        fail(
            "unchecked object-image generation returned none; the selected object "
            "likely needs object layout/data-base resolution or uses unsupported Yul"
        )
    bytecode: Optional[str] = None
    immutable_references: Dict[str, List[Dict[str, int]]] = {}
    for line in lines:
        if line.startswith("timing\t"):
            continue
        if line.startswith("bytecode_bytes="):
            continue
        if line.startswith("bytecode="):
            bytecode = line.removeprefix("bytecode=")
            continue
        if line.startswith("immutable\t"):
            parts = line.split("\t")
            if len(parts) != 4:
                fail(f"Lean object-image runner produced malformed line: {line!r}")
            _tag, name, start_text, length_text = parts
            try:
                start = int(start_text)
                length = int(length_text)
            except ValueError as exc:
                fail(
                    "Lean object-image runner produced malformed immutable "
                    f"reference: {line!r}"
                )
            immutable_references.setdefault(name, []).append(
                {"start": start, "length": length}
            )
            continue
        fail(f"Lean object-image runner produced unexpected output: {line!r}")
    if bytecode is None:
        fail("Lean object-image runner did not print bytecode")
    if not re.fullmatch(r"0x[0-9a-f]*", bytecode):
        fail(f"Lean object-image runner produced unexpected bytecode: {bytecode!r}")
    return CompiledObjectImage(
        bytecode=bytecode,
        immutable_references=immutable_references,
    )


def run_lake_object_image(lake: str, lean_source: str, cwd: Path) -> CompiledObjectImage:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="evm_compiler_object_image_", delete=False
    ) as handle:
        handle.write(lean_source)
        temp_path = Path(handle.name)
    try:
        try:
            completed = subprocess.run(
                [lake, "env", "lean", "--run", str(temp_path)],
                cwd=str(cwd),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except FileNotFoundError:
            fail(
                f"Could not find lake executable {lake!r}. "
                "Install Lean with elan and put ~/.elan/bin on PATH."
            )
        if completed.returncode != 0:
            output = "\n".join(
                part
                for part in [
                    f"returncode={completed.returncode}",
                    completed.stdout.strip(),
                    completed.stderr.strip(),
                ]
                if part
            )
            fail(f"`{lake} env lean --run {temp_path}` failed:\n{output}")
        return parse_object_image_output(completed.stdout)
    finally:
        try:
            temp_path.unlink()
        except OSError:
            pass


def run_lake_native_object_image(
    lake: str,
    json_path: Path,
    cwd: Path,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> CompiledObjectImage:
    command = [
        lake,
        "exe",
        "evm-compiler-backend",
        "image",
        str(json_path),
    ]
    command.extend(
        f"{entry.name}={entry.value}" for entry in linker_symbols
    )
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except FileNotFoundError:
        fail(
            f"Could not find lake executable {lake!r}. "
            "Install Lean with elan and put ~/.elan/bin on PATH."
        )
    if completed.returncode != 0:
        output = "\n".join(
            part
            for part in [
                f"returncode={completed.returncode}",
                completed.stdout.strip(),
                completed.stderr.strip(),
            ]
            if part
        )
        fail(f"`{' '.join(command)}` failed:\n{output}")
    return parse_object_image_output(completed.stdout)


def run_lake_native_backend_check(
    lake: str,
    json_path: Path,
    cwd: Path,
    linker_symbols: Sequence[LinkerSymbolEntry],
) -> str:
    command = [
        lake,
        "exe",
        "evm-compiler-backend",
        "check",
        str(json_path),
    ]
    command.extend(
        f"{entry.name}={entry.value}" for entry in linker_symbols
    )
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except FileNotFoundError:
        fail(
            f"Could not find lake executable {lake!r}. "
            "Install Lean with elan and put ~/.elan/bin on PATH."
        )
    if completed.returncode != 0:
        output = "\n".join(
            part
            for part in [
                f"returncode={completed.returncode}",
                completed.stdout.strip(),
                completed.stderr.strip(),
            ]
            if part
        )
        fail(f"`{' '.join(command)}` failed:\n{output}")
    parse_backend_check_output(completed.stdout)
    return completed.stdout


def run_lake_backend_check(lake: str, lean_source: str, cwd: Path) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="evm_compiler_backend_check_", delete=False
    ) as handle:
        handle.write(lean_source)
        temp_path = Path(handle.name)
    try:
        try:
            completed = subprocess.run(
                [lake, "env", "lean", "--run", str(temp_path)],
                cwd=str(cwd),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except FileNotFoundError:
            fail(
                f"Could not find lake executable {lake!r}. "
                "Install Lean with elan and put ~/.elan/bin on PATH."
            )
        if completed.returncode != 0:
            output = "\n".join(
                part
                for part in [
                    f"returncode={completed.returncode}",
                    completed.stdout.strip(),
                    completed.stderr.strip(),
                ]
                if part
            )
            fail(f"`{lake} env lean --run {temp_path}` failed:\n{output}")
        parse_backend_check_output(completed.stdout)
        return completed.stdout
    finally:
        try:
            temp_path.unlink()
        except OSError:
            pass


def check_bridge_json_backend_with_lean(
    bridge_json: str,
    lake: str,
    lake_cwd: Path,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".bridge.json", prefix="evm_compiler_bridge_", delete=False
    ) as handle:
        handle.write(bridge_json)
        bridge_json_path = Path(handle.name)
    try:
        return run_lake_native_backend_check(
            lake,
            bridge_json_path,
            lake_cwd,
            linker_symbols,
        )
    finally:
        try:
            bridge_json_path.unlink()
        except OSError:
            pass


def compile_frontend_object_image(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    definition: str,
    namespace: Optional[str],
    object_layout: Sequence[ObjectLayoutEntry],
    local_data_base: Optional[int],
    linker_symbols: Sequence[LinkerSymbolEntry],
    lake: str,
    lake_cwd: Path,
) -> CompiledObjectImage:
    bridge_json = render_bridge_json(obj, source_name, contract_name)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".bridge.json", prefix="evm_compiler_bridge_", delete=False
    ) as handle:
        handle.write(bridge_json)
        bridge_json_path = Path(handle.name)
    try:
        try:
            return run_lake_native_object_image(
                lake,
                bridge_json_path,
                lake_cwd,
                linker_symbols,
            )
        except ConversionError as exc:
            if "unchecked object-image generation returned none" not in str(exc):
                raise
            diagnostic_source = render_json_file_backend_check_runner(
                bridge_json_path,
                linker_symbols,
            )
            diagnostic = run_lake_backend_check(
                lake,
                diagnostic_source,
                lake_cwd,
            )
            raise ConversionError(
                str(exc)
                + "\nLean backend handoff diagnostic:\n"
                + diagnostic.strip()
            ) from exc
    finally:
        try:
            bridge_json_path.unlink()
        except OSError:
            pass


def check_bridge_json_with_lean(
    bridge_json: str,
    lake: str,
    lake_cwd: Path,
) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".bridge.json", prefix="evm_compiler_bridge_", delete=False
    ) as handle:
        handle.write(bridge_json)
        bridge_json_path = Path(handle.name)
    rendered = render_json_file_decode_runner(bridge_json_path)
    try:
        return run_lake_bridge_json_decode(lake, rendered, lake_cwd)
    finally:
        try:
            bridge_json_path.unlink()
        except OSError:
            pass


def check_frontend_object_with_lean(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    object_selector: str,
    lake: str,
    lake_cwd: Path,
    frontend: Optional[Json] = None,
) -> LeanJsonCheckArtifact:
    normalized_frontend = normalize_bridge_json_frontend_metadata(
        frontend,
        "lean-json-check frontend",
    )
    output = check_bridge_json_with_lean(
        render_bridge_json(
            obj,
            source_name,
            contract_name,
            normalized_frontend.get("ast") if normalized_frontend is not None else None,
        ),
        lake,
        lake_cwd,
    )
    summary = parse_bridge_json_decode_output(output)
    if summary.get("source") != source_name:
        fail(
            "Lean bridge JSON decode runner reported source "
            f"{summary.get('source')!r}, expected {source_name!r}"
        )
    if summary.get("contract") != contract_name:
        fail(
            "Lean bridge JSON decode runner reported contract "
            f"{summary.get('contract')!r}, expected {contract_name!r}"
        )
    if summary.get("object") != obj.name:
        fail(
            "Lean bridge JSON decode runner reported object "
            f"{summary.get('object')!r}, expected {obj.name!r}"
        )
    return LeanJsonCheckArtifact(
        source_name=source_name,
        contract_name=contract_name,
        object_selector=object_selector,
        object_name=obj.name,
        summary=summary,
        frontend=normalized_frontend,
    )


def check_frontend_object_backend_with_lean(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    object_selector: str,
    lake: str,
    lake_cwd: Path,
    linker_symbols: Sequence[LinkerSymbolEntry] = (),
    frontend: Optional[Json] = None,
) -> LeanBackendCheckArtifact:
    normalized_frontend = normalize_bridge_json_frontend_metadata(
        frontend,
        "lean-backend-check frontend",
    )
    output = check_bridge_json_backend_with_lean(
        render_bridge_json(
            obj,
            source_name,
            contract_name,
            normalized_frontend.get("ast") if normalized_frontend is not None else None,
        ),
        lake,
        lake_cwd,
        linker_symbols,
    )
    summary = parse_backend_check_output(output)
    if summary.get("source") != source_name:
        fail(
            "Lean backend check runner reported source "
            f"{summary.get('source')!r}, expected {source_name!r}"
        )
    if summary.get("contract") != contract_name:
        fail(
            "Lean backend check runner reported contract "
            f"{summary.get('contract')!r}, expected {contract_name!r}"
        )
    if summary.get("object") != obj.name:
        fail(
            "Lean backend check runner reported object "
            f"{summary.get('object')!r}, expected {obj.name!r}"
        )
    return LeanBackendCheckArtifact(
        source_name=source_name,
        contract_name=contract_name,
        object_selector=object_selector,
        object_name=obj.name,
        summary=summary,
        frontend=normalized_frontend,
    )


def compile_frontend_object_bytecode(
    obj: YulObject,
    source_name: str,
    contract_name: str,
    definition: str,
    namespace: Optional[str],
    object_layout: Sequence[ObjectLayoutEntry],
    local_data_base: Optional[int],
    linker_symbols: Sequence[LinkerSymbolEntry],
    lake: str,
    lake_cwd: Path,
) -> str:
    return compile_frontend_object_image(
        obj,
        source_name,
        contract_name,
        definition,
        namespace,
        object_layout,
        local_data_base,
        linker_symbols,
        lake,
        lake_cwd,
    ).bytecode


def compile_contract_bytecode_artifact(
    root: YulObject,
    source_name: str,
    contract_name: str,
    definition_prefix: str,
    namespace: Optional[str],
    object_layout: Sequence[ObjectLayoutEntry],
    local_data_base: Optional[int],
    linker_symbols: Sequence[LinkerSymbolEntry],
    lake: str,
    lake_cwd: Path,
) -> ContractBytecodeArtifact:
    runtime = select_object(root, "runtime")
    effective_creation_linker_symbols = linker_symbols_with_zero_defaults(
        root,
        linker_symbols,
    )
    effective_runtime_linker_symbols = linker_symbols_with_zero_defaults(
        runtime,
        linker_symbols,
    )
    backend_compatibility = bridge_summary_aggregate_backend_compatibility(
        [
            bridge_json_summary_artifact(
                root,
                source_name,
                contract_name,
                "creation",
            ),
            bridge_json_summary_artifact(
                runtime,
                source_name,
                contract_name,
                "runtime",
            ),
        ]
    )
    creation_image = compile_frontend_object_image(
        root,
        source_name,
        contract_name,
        definition_prefix + "Creation",
        namespace,
        object_layout,
        local_data_base,
        effective_creation_linker_symbols,
        lake,
        lake_cwd,
    )
    runtime_image = compile_frontend_object_image(
        runtime,
        source_name,
        contract_name,
        definition_prefix + "Runtime",
        namespace,
        object_layout,
        local_data_base,
        effective_runtime_linker_symbols,
        lake,
        lake_cwd,
    )
    return ContractBytecodeArtifact(
        source_name=source_name,
        contract_name=contract_name,
        creation_object_name=root.name,
        runtime_object_name=runtime.name,
        creation_bytecode=creation_image.bytecode,
        runtime_bytecode=runtime_image.bytecode,
        runtime_immutable_references=runtime_image.immutable_references,
        backend_compatibility=backend_compatibility,
    )


def bytecode_size(bytecode: str) -> int:
    if not re.fullmatch(r"0x[0-9a-f]*", bytecode):
        fail(f"Expected lowercase hex bytecode, got {bytecode!r}")
    return (len(bytecode) - 2) // 2


def checked_prefixed_bytecode(bytecode: str) -> str:
    if not re.fullmatch(r"0x[0-9a-f]*", bytecode):
        fail(f"Expected lowercase hex bytecode, got {bytecode!r}")
    return bytecode


def render_bytecode_artifact_json(
    source_name: str,
    contract_name: str,
    creation_object_name: str,
    runtime_object_name: str,
    creation_bytecode: str,
    runtime_bytecode: str,
    runtime_immutable_references: Optional[
        Dict[str, List[Dict[str, int]]]
    ] = None,
    backend_compatibility: Optional[Json] = None,
    bridge_json: Optional[Json] = None,
) -> str:
    immutable_references = runtime_immutable_references or {}
    artifact: Json = {
        "schema": "evm-compiler.solidity-bytecode-artifact.v1",
        "source": source_name,
        "contract": contract_name,
        "yul": {
            "creationObject": creation_object_name,
            "runtimeObject": runtime_object_name,
        },
        "bytecode": {
            "creation": creation_bytecode,
            "runtime": runtime_bytecode,
        },
        "immutableReferences": {
            "runtime": immutable_references,
        },
        "sizes": {
            "creationBytes": bytecode_size(creation_bytecode),
            "runtimeBytes": bytecode_size(runtime_bytecode),
        },
    }
    if backend_compatibility is not None:
        artifact["backendCompatibility"] = copy.deepcopy(backend_compatibility)
    if bridge_json is not None:
        artifact["bridgeJson"] = copy.deepcopy(bridge_json)
    return (
        json.dumps(artifact, indent=2)
        + "\n"
    )


def parse_metadata_json(metadata: Any) -> Json:
    if not isinstance(metadata, str) or not metadata:
        return {}
    try:
        parsed = json.loads(metadata)
    except json.JSONDecodeError:
        return {}
    return parsed if isinstance(parsed, dict) else {}


def foundry_bytecode_section(
    bytecode: str,
    immutable_references: Optional[Dict[str, List[Dict[str, int]]]] = None,
) -> Json:
    section: Json = {
        "object": checked_prefixed_bytecode(bytecode),
        "sourceMap": "",
        "linkReferences": {},
    }
    if immutable_references is not None:
        section["immutableReferences"] = immutable_references
    return section


def render_forge_artifact_json(
    source_name: str,
    contract_name: str,
    creation_object_name: str,
    runtime_object_name: str,
    contract_output: Json,
    creation_bytecode: str,
    runtime_bytecode: str,
    runtime_immutable_references: Optional[
        Dict[str, List[Dict[str, int]]]
    ] = None,
    backend_compatibility: Optional[Json] = None,
    bridge_json: Optional[Json] = None,
) -> str:
    immutable_references = runtime_immutable_references or {}
    evm = contract_output.get("evm", {})
    if not isinstance(evm, dict):
        evm = {}
    raw_metadata = contract_output.get("metadata", "")
    if not isinstance(raw_metadata, str):
        raw_metadata = ""
    evm_compiler: Json = {
        "schema": "evm-compiler.forge-artifact.v1",
        "source": source_name,
        "contract": contract_name,
        "yul": {
            "creationObject": creation_object_name,
            "runtimeObject": runtime_object_name,
        },
        "sizes": {
            "creationBytes": bytecode_size(creation_bytecode),
            "runtimeBytes": bytecode_size(runtime_bytecode),
        },
        "bytecodeSource": "lean-unchecked-bytecode-image",
    }
    if backend_compatibility is not None:
        evm_compiler["backendCompatibility"] = copy.deepcopy(backend_compatibility)
    if bridge_json is not None:
        evm_compiler["bridgeJson"] = copy.deepcopy(bridge_json)
    return (
        json.dumps(
            {
                "abi": contract_output.get("abi", []),
                "bytecode": foundry_bytecode_section(creation_bytecode),
                "deployedBytecode": foundry_bytecode_section(
                    runtime_bytecode,
                    immutable_references,
                ),
                "methodIdentifiers": evm.get("methodIdentifiers", {}),
                "metadata": parse_metadata_json(raw_metadata),
                "rawMetadata": raw_metadata,
                "id": f"{source_name}:{contract_name}",
                "evmCompiler": evm_compiler,
            },
            indent=2,
        )
        + "\n"
    )


def solc_standard_json_bytecode_object(bytecode: str) -> str:
    prefixed = checked_prefixed_bytecode(bytecode)
    return prefixed[2:]


def apply_standard_json_bytecode_artifact(
    rendered_output: Json,
    artifact: ContractBytecodeArtifact,
) -> None:
    contracts_by_source = rendered_output.setdefault("contracts", {})
    if not isinstance(contracts_by_source, dict):
        fail("Malformed solc contracts output")
    contracts = contracts_by_source.setdefault(artifact.source_name, {})
    if not isinstance(contracts, dict):
        fail(f"Malformed solc contracts output for source {artifact.source_name!r}")
    contract_output = contracts.setdefault(artifact.contract_name, {})
    if not isinstance(contract_output, dict):
        fail(
            "Malformed solc contract output for "
            f"{artifact.source_name}:{artifact.contract_name}"
        )
    evm = contract_output.setdefault("evm", {})
    if not isinstance(evm, dict):
        fail(
            f"Malformed solc evm output for "
            f"{artifact.source_name}:{artifact.contract_name}"
        )
    bytecode = evm.setdefault("bytecode", {})
    deployed_bytecode = evm.setdefault("deployedBytecode", {})
    if not isinstance(bytecode, dict) or not isinstance(deployed_bytecode, dict):
        fail(
            "Malformed solc bytecode output for "
            f"{artifact.source_name}:{artifact.contract_name}"
        )
    bytecode["object"] = solc_standard_json_bytecode_object(
        artifact.creation_bytecode
    )
    bytecode["sourceMap"] = ""
    bytecode["linkReferences"] = {}
    bytecode["generatedSources"] = []
    deployed_bytecode["object"] = solc_standard_json_bytecode_object(
        artifact.runtime_bytecode
    )
    deployed_bytecode["sourceMap"] = ""
    deployed_bytecode["linkReferences"] = {}
    deployed_bytecode["generatedSources"] = []
    deployed_bytecode["immutableReferences"] = artifact.runtime_immutable_references
    contract_output["evmCompiler"] = {
        "schema": "evm-compiler.solc-standard-json-output.v1",
        "source": artifact.source_name,
        "contract": artifact.contract_name,
        "yul": {
            "creationObject": artifact.creation_object_name,
            "runtimeObject": artifact.runtime_object_name,
        },
        "sizes": {
            "creationBytes": bytecode_size(artifact.creation_bytecode),
            "runtimeBytes": bytecode_size(artifact.runtime_bytecode),
        },
        "bytecodeSource": "lean-unchecked-bytecode-image",
    }
    if artifact.backend_compatibility is not None:
        contract_output["evmCompiler"]["backendCompatibility"] = copy.deepcopy(
            artifact.backend_compatibility
        )
    if artifact.bridge_json is not None:
        contract_output["evmCompiler"]["bridgeJson"] = copy.deepcopy(
            artifact.bridge_json
        )


def render_standard_json_outputs(
    solc_output: Json,
    artifacts: Sequence[ContractBytecodeArtifact],
) -> str:
    rendered_output = copy.deepcopy(solc_output)
    for artifact in artifacts:
        apply_standard_json_bytecode_artifact(rendered_output, artifact)
    return json.dumps(rendered_output, indent=2) + "\n"


def render_standard_json_output(
    solc_output: Json,
    source_name: str,
    contract_name: str,
    creation_object_name: str,
    runtime_object_name: str,
    creation_bytecode: str,
    runtime_bytecode: str,
    runtime_immutable_references: Optional[
        Dict[str, List[Dict[str, int]]]
    ] = None,
    backend_compatibility: Optional[Json] = None,
    bridge_json: Optional[Json] = None,
) -> str:
    return render_standard_json_outputs(
        solc_output,
        [
            ContractBytecodeArtifact(
                source_name,
                contract_name,
                creation_object_name,
                runtime_object_name,
                creation_bytecode,
                runtime_bytecode,
                runtime_immutable_references or {},
                backend_compatibility,
                bridge_json,
            )
        ],
    )


def render_lean_json_check_outputs(
    artifacts: Sequence[LeanJsonCheckArtifact],
    skipped_contracts: Sequence[str],
) -> str:
    checked_contracts = sorted(
        {f"{artifact.source_name}:{artifact.contract_name}" for artifact in artifacts}
    )
    checked_objects = []
    for artifact in artifacts:
        entry: Json = {
            "source": artifact.source_name,
            "contract": artifact.contract_name,
            "selector": artifact.object_selector,
            "object": artifact.object_name,
            "dispatcherStatements": artifact.summary.get(
                "dispatcher_stmts",
                0,
            ),
            "functions": artifact.summary.get("functions", 0),
            "dataSections": artifact.summary.get("data_sections", 0),
            "subobjects": artifact.summary.get("subobjects", 0),
            "items": artifact.summary.get("items", 0),
        }
        frontend = normalize_bridge_json_frontend_metadata(
            artifact.frontend,
            "lean-json-check artifact frontend",
        )
        if frontend is not None:
            entry["frontend"] = frontend
        checked_objects.append(entry)
    return (
        json.dumps(
            {
                "schema": "evm-compiler.lean-json-check.v2",
                "checkedObjects": checked_objects,
                "checkedContracts": checked_contracts,
                "skippedContracts": list(skipped_contracts),
                "counts": {
                    "checkedObjects": len(artifacts),
                    "checkedContracts": len(checked_contracts),
                    "skippedContracts": len(skipped_contracts),
                },
            },
            indent=2,
        )
        + "\n"
    )


def render_lean_backend_check_outputs(
    artifacts: Sequence[LeanBackendCheckArtifact],
    skipped_contracts: Sequence[str],
) -> str:
    checked_contracts = sorted(
        {f"{artifact.source_name}:{artifact.contract_name}" for artifact in artifacts}
    )
    status_counts = Counter(
        str(artifact.summary.get("status", "unknown")) for artifact in artifacts
    )
    first_none_counts = Counter(
        str(artifact.summary.get("first_none", "missing"))
        for artifact in artifacts
        if artifact.summary.get("first_none") != "none"
    )
    checked_objects = []
    for artifact in artifacts:
        entry: Json = {
            "source": artifact.source_name,
            "contract": artifact.contract_name,
            "selector": artifact.object_selector,
            "object": artifact.object_name,
            "status": artifact.summary.get("status", "unknown"),
            "firstNone": artifact.summary.get("first_none", "missing"),
            "stages": artifact.summary.get("stages", {}),
        }
        for key in [
            "timingsMs",
            "localsProcs",
            "localsStmtTrace",
            "localsLayouts",
            "localsVars",
            "localsTargets",
        ]:
            value = artifact.summary.get(key)
            if value:
                entry[key] = value
        frontend = normalize_bridge_json_frontend_metadata(
            artifact.frontend,
            "lean-backend-check artifact frontend",
        )
        if frontend is not None:
            entry["frontend"] = frontend
        if "bytecode_bytes" in artifact.summary:
            entry["bytecodeBytes"] = artifact.summary["bytecode_bytes"]
        checked_objects.append(entry)
    return (
        json.dumps(
            {
                "schema": LEAN_BACKEND_CHECK_SCHEMA,
                "checkedObjects": checked_objects,
                "checkedContracts": checked_contracts,
                "skippedContracts": list(skipped_contracts),
                "counts": {
                    "checkedObjects": len(artifacts),
                    "checkedContracts": len(checked_contracts),
                    "skippedContracts": len(skipped_contracts),
                    "passedObjects": status_counts.get("pass", 0),
                    "failedObjects": status_counts.get("fail", 0),
                },
                "firstNoneCounts": dict(sorted(first_none_counts.items())),
            },
            indent=2,
        )
        + "\n"
    )


def contract_candidates(
    output: Json,
    source_name: Optional[str],
    contract_name: Optional[str],
) -> List[Tuple[str, str, Json]]:
    contracts_by_source = output.get("contracts", {})
    if not isinstance(contracts_by_source, dict):
        fail("Malformed solc contracts output")
    candidates: List[Tuple[str, str, Json]] = []
    for candidate_source_name, contracts in contracts_by_source.items():
        if not isinstance(candidate_source_name, str) or not isinstance(contracts, dict):
            continue
        if source_name is not None and candidate_source_name != source_name:
            continue
        for candidate_contract_name, contract_output in contracts.items():
            if not isinstance(candidate_contract_name, str) or not isinstance(
                contract_output,
                dict,
            ):
                continue
            if contract_name is None or candidate_contract_name == contract_name:
                candidates.append(
                    (candidate_source_name, candidate_contract_name, contract_output)
                )
    return candidates


def has_yul_ir_ast(contract_output: Json, optimized: bool) -> bool:
    ir_key = "irOptimizedAst" if optimized else "irAst"
    return isinstance(contract_output.get(ir_key), dict)


def has_lean_bytecode_artifact_inputs(contract_output: Json, optimized: bool) -> bool:
    if not has_yul_ir_ast(contract_output, optimized):
        return False
    return (
        bytecode_object(contract_output, deployed=False) is not None
        and bytecode_object(contract_output, deployed=True) is not None
    )


def lean_bytecode_contract_candidates(
    output: Json,
    source_name: Optional[str],
    optimized: bool,
) -> List[Tuple[str, str, Json]]:
    return [
        candidate
        for candidate in contract_candidates(output, source_name, None)
        if has_lean_bytecode_artifact_inputs(candidate[2], optimized)
    ]


def contract_label(source_name: str, contract_name: str) -> str:
    return f"{source_name}:{contract_name}"


def skipped_contract_labels(
    all_candidates: Sequence[Tuple[str, str, Json]],
    included_candidates: Sequence[Tuple[str, str, Json]],
) -> List[str]:
    included_labels = {
        contract_label(candidate_src, candidate_name)
        for candidate_src, candidate_name, _ in included_candidates
    }
    return [
        contract_label(candidate_src, candidate_name)
        for candidate_src, candidate_name, _ in all_candidates
        if contract_label(candidate_src, candidate_name) not in included_labels
    ]


def yul_ir_contract_candidates(
    output: Json,
    source_name: Optional[str],
    optimized: bool,
) -> List[Tuple[str, str, Json]]:
    return [
        candidate
        for candidate in contract_candidates(output, source_name, None)
        if has_yul_ir_ast(candidate[2], optimized)
    ]


def available_contract_labels(output: Json) -> List[str]:
    contracts_by_source = output.get("contracts", {})
    if not isinstance(contracts_by_source, dict):
        return []
    return [
        f"{src}:{name}"
        for src, contracts in contracts_by_source.items()
        if isinstance(src, str) and isinstance(contracts, dict)
        for name in contracts.keys()
        if isinstance(name, str)
    ]


def choose_contract(
    output: Json,
    source_name: Optional[str],
    contract_name: Optional[str],
) -> Tuple[str, str, Json]:
    contracts_by_source = output.get("contracts", {})
    if not isinstance(contracts_by_source, dict):
        fail("Malformed solc contracts output")
    if source_name is not None:
        if source_name not in contracts_by_source:
            available = ", ".join(contracts_by_source.keys())
            fail(
                f"solc output did not contain source {source_name!r}; "
                f"available: {available}"
            )
        contracts = contracts_by_source[source_name]
        if not isinstance(contracts, dict):
            fail(f"Malformed solc contracts output for source {source_name!r}")
        if contract_name is None:
            names = sorted(contracts.keys())
            if len(names) != 1:
                fail(f"Pass --contract; available contracts: {', '.join(names)}")
            contract_name = names[0]
        if contract_name not in contracts:
            fail(f"Contract {contract_name!r} not found in {source_name!r}")
        return source_name, contract_name, contracts[contract_name]

    candidates = contract_candidates(output, None, contract_name)
    if not candidates:
        available = available_contract_labels(output)
        fail(
            f"Contract {contract_name!r} not found; available contracts: "
            + ", ".join(available)
        )
    if len(candidates) > 1:
        available = ", ".join(f"{src}:{name}" for src, name, _ in candidates)
        fail(f"Pass --source-name to disambiguate; matching contracts: {available}")
    return candidates[0]


def load_ir_ast(contract_output: Json, optimized: bool) -> Json:
    key = "irOptimizedAst" if optimized else "irAst"
    ast = contract_output.get(key)
    if not isinstance(ast, dict):
        fail(f"solc output did not include {key}; check solc version/settings")
    return ast


def load_yul_source_ast(output: Json, source_name: Optional[str]) -> Tuple[str, Json]:
    sources = output.get("sources")
    if not isinstance(sources, dict):
        fail("solc Yul output did not include sources")
    if source_name is not None:
        if source_name not in sources:
            available = ", ".join(str(name) for name in sources.keys())
            fail(
                f"solc Yul output did not contain source {source_name!r}; "
                f"available: {available}"
            )
        source = sources[source_name]
        if not isinstance(source, dict):
            fail(f"Malformed solc Yul source output for {source_name!r}")
        ast = source.get("ast")
        if not isinstance(ast, dict):
            fail(f"solc Yul output did not include sources[{source_name!r}].ast")
        return source_name, ast

    candidates: List[Tuple[str, Json]] = []
    for candidate_source_name, source in sources.items():
        if not isinstance(candidate_source_name, str) or not isinstance(source, dict):
            continue
        ast = source.get("ast")
        if isinstance(ast, dict):
            candidates.append((candidate_source_name, ast))
    if not candidates:
        fail("solc Yul output did not include any source AST")
    if len(candidates) > 1:
        available = ", ".join(name for name, _ast in candidates)
        fail(f"Pass --source-name to select a Yul source; available: {available}")
    return candidates[0]


def recover_missing_contract_yul_asts(
    output: Json,
    source_name: Optional[str],
    contract_name: Optional[str],
    optimized: bool,
    experimental: bool,
    solc: str,
    solc_args: Sequence[str],
) -> int:
    ast_key = solc_yul_ast_output(optimized)
    text_key = solc_yul_text_output(optimized)
    recovered = 0
    for candidate_source, candidate_contract, contract_output in contract_candidates(
        output,
        source_name,
        contract_name,
    ):
        provenance_key = (candidate_source, candidate_contract)
        RECOVERED_YUL_AST_OUTPUTS.pop(provenance_key, None)
        if isinstance(contract_output.get(ast_key), dict):
            continue
        yul_text = contract_output.get(text_key)
        if not isinstance(yul_text, str):
            continue
        yul_source_name = (
            f"{candidate_source}:{candidate_contract}.{text_key}.yul"
        )
        yul_input = yul_standard_json_input(
            yul_source_name,
            yul_text,
            experimental=experimental,
        )
        yul_output = run_solc(solc, yul_input, solc_args)
        _parsed_source, root_ast = load_yul_source_ast(
            yul_output,
            yul_source_name,
        )
        recover_standalone_yul_data_names(root_ast, yul_text)
        contract_output[ast_key] = root_ast
        RECOVERED_YUL_AST_OUTPUTS[provenance_key] = (
            solc_standalone_yul_ast_output()
        )
        recovered += 1
    return recovered


def standard_json_source_content(
    compiler_input: Json,
    source_name: str,
) -> Optional[str]:
    sources = compiler_input.get("sources")
    if not isinstance(sources, dict):
        return None
    source = sources.get(source_name)
    if not isinstance(source, dict):
        return None
    content = source.get("content")
    return content if isinstance(content, str) else None


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "input",
        type=Path,
        help=(
            "Solidity or Yul source file, solc Standard JSON file, "
            "bridge JSON file, or '-' for stdin"
        ),
    )
    parser.add_argument(
        "--input-format",
        choices=[
            "solidity",
            "yul",
            "standard-json",
            "bridge-json",
            "bridge-json-manifest",
        ],
        default="solidity",
        help=(
            "Interpret input as Solidity source, standalone Yul source, as a "
            "solc Standard JSON request, as normalized bridge JSON, or as a "
            "bridge JSON manifest"
        ),
    )
    parser.add_argument("-o", "--output", type=Path, help="Output file to write")
    parser.add_argument("--solc", default=os.environ.get("SOLC", "solc"))
    parser.add_argument(
        "--solc-arg",
        action="append",
        default=[],
        metavar="ARG",
        help=(
            "Forward an extra CLI argument to solc before --standard-json. "
            "Repeat for options with values, e.g. --solc-arg=--base-path "
            "--solc-arg ."
        ),
    )
    parser.add_argument(
        "--yul-ast-solc",
        default=os.environ.get("YUL_AST_SOLC"),
        help=(
            "Optional solc executable used only to parse textual ir/irOptimized "
            "when the source solc omits irAst/irOptimizedAst. The exact Yul text "
            "still comes from --solc. Defaults to --solc."
        ),
    )
    parser.add_argument(
        "--yul-ast-solc-arg",
        action="append",
        default=[],
        metavar="ARG",
        help="Forward an extra CLI argument to --yul-ast-solc.",
    )
    parser.add_argument("--lake", default=os.environ.get("LAKE", default_lake()))
    parser.add_argument(
        "--lake-cwd",
        type=Path,
        default=Path.cwd(),
        help="Project directory to use when running `lake env lean`",
    )
    parser.add_argument(
        "--source-name",
        help=(
            "Source name to use in generated Standard JSON, or source name to "
            "select from solc output with --input-format standard-json"
        ),
    )
    parser.add_argument(
        "--include-source",
        action="append",
        default=[],
        metavar="[SOURCE_NAME=]PATH",
        help=(
            "Add another Solidity source to the Standard JSON input. When "
            "SOURCE_NAME is omitted, the file name is used, which matches "
            "simple imports such as './Lib.sol' from a root source named C.sol."
        ),
    )
    parser.add_argument(
        "--remapping",
        action="append",
        default=[],
        metavar="PREFIX=PATH",
        help=(
            "Map a non-relative Solidity import prefix to a local directory "
            "when auto-collecting Standard JSON sources, e.g. "
            "@openzeppelin/=lib/openzeppelin-contracts/"
        ),
    )
    parser.add_argument(
        "--remappings-file",
        action="append",
        default=[],
        type=Path,
        metavar="PATH",
        help=(
            "Read import remappings from a file such as remappings.txt. "
            "Relative targets in the file are resolved from the file's parent."
        ),
    )
    parser.add_argument(
        "--no-auto-include-imports",
        dest="auto_include_imports",
        action="store_false",
        help=(
            "Do not automatically add local relative/remapped Solidity imports from "
            "source files to the Standard JSON input"
        ),
    )
    parser.add_argument("--contract", help="Contract name to import")
    parser.add_argument(
        "--object",
        default=None,
        help=(
            "'runtime' (default), 'creation', or an explicit Yul object name; "
            "not used with artifact formats"
        ),
    )
    parser.add_argument(
        "--optimized",
        action="store_true",
        help=(
            "Request irOptimizedAst instead of irAst for Solidity input. "
            "Standalone Yul source imports use solc's source ast."
        ),
    )
    parser.add_argument(
        "--format",
        choices=[
            "lean",
            "lean-ir",
            "lean-json-ir",
            "bridge-json",
            "bridge-json-summary",
            "lean-json-check",
            "lean-backend-check",
            "bytecode",
            "bytecode-artifact",
            "forge-artifact",
            "standard-json-output",
        ],
        default="lean",
        help=(
            "Write backend Yul Lean (default), typed front-end Lean IR, "
            "typed front-end Lean IR backed by normalized JSON, the normalized "
            "bridge AST JSON, a Lean-free structural summary of bridge JSON, "
            "a Lean sidecar decode check for bridge JSON, a staged Lean "
            "backend handoff check, unchecked backend bytecode hex, a JSON "
            "artifact with creation and runtime bytecode, or a Foundry-shaped "
            "or solc Standard JSON artifact with Lean-produced bytecode"
        ),
    )
    parser.add_argument(
        "--bridge-json",
        type=Path,
        help="Also write the normalized bridge AST JSON for the selected object",
    )
    parser.add_argument(
        "--bridge-json-dir",
        type=Path,
        help=(
            "Also write normalized bridge AST JSON files under this directory "
            "for selected or artifact-compiled objects"
        ),
    )
    parser.add_argument(
        "--object-layout",
        action="append",
        default=[],
        metavar="NAME=OFFSET:SIZE",
        help=(
            "When emitting --format lean-ir, lean-json-ir, bytecode, "
            "bytecode-artifact, forge-artifact, or standard-json-output, also emit an explicit "
            "object layout entry used to resolve datasize/dataoffset during "
            "backend conversion"
        ),
    )
    parser.add_argument(
        "--auto-object-layout",
        action="store_true",
        help=(
            "When emitting --format lean-ir, lean-json-ir, bytecode, "
            "bytecode-artifact, forge-artifact, or standard-json-output, infer the main deployed "
            "object layout entry by locating solc's deployed bytecode inside "
            "creation bytecode"
        ),
    )
    parser.add_argument(
        "--data-base",
        type=parse_uint256_arg,
        help=(
            "When emitting --format lean-ir, lean-json-ir, bytecode, "
            "bytecode-artifact, forge-artifact, or standard-json-output, also emit a local data "
            "base used to compute named local dataoffset entries from ordered "
            "data sections"
        ),
    )
    parser.add_argument(
        "--linker-symbol",
        action="append",
        default=[],
        metavar="NAME=VALUE",
        help=(
            "Resolve a solc Yul linkersymbol(\"NAME\") object builtin to the "
            "given UInt256 VALUE before entering the backend"
        ),
    )
    parser.add_argument(
        "--scratch-reservation-base",
        type=parse_uint256_arg,
        help=(
            "Explicit source-facing byte address at which the compiler may "
            "reserve spill memory. This is a semantic promise, not an "
            "inference; the correctness theorem requires source execution to "
            "avoid the reserved interval."
        ),
    )
    parser.add_argument(
        "--scratch-reservation-words",
        type=int,
        help=(
            "Positive number of 32-byte words in the explicit source scratch "
            "reservation; requires --scratch-reservation-base."
        ),
    )
    parser.add_argument(
        "--list-objects",
        action="store_true",
        help="List Yul objects/data sections found in solc's IR AST and exit",
    )
    parser.add_argument(
        "--all-contracts",
        action="store_true",
        help=(
            "With --format standard-json-output, replace bytecode for every "
            "contract selected by solc output; with --format bridge-json, "
            "write a normalized bridge JSON package for every contract with "
            "Yul IR; with --format bridge-json-summary, summarize every "
            "contract Yul IR object without invoking Lean; with --format "
            "lean-json-check, ask Lean to decode every contract Yul IR object; "
            "with --format lean-backend-check, run staged Lean backend checks "
            "for every contract Yul IR object"
        ),
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="After emitting Lean, run `lake env lean` on it",
    )
    parser.add_argument("--no-via-ir", dest="via_ir", action="store_false")
    parser.add_argument("--no-experimental", dest="experimental", action="store_false")
    parser.add_argument("--namespace", help="Optional Lean namespace, e.g. Generated.C")
    parser.add_argument("--definition", default="program", help="Lean definition name")
    parser.set_defaults(via_ir=True, experimental=True, auto_include_imports=True)
    return parser


def emit_rendered_output(
    args: argparse.Namespace,
    rendered: str,
    source_name: str,
    contract_name: str,
    selected_name: str,
) -> None:
    if args.output:
        args.output.write_text(rendered)
        print(
            f"Wrote {args.output} from {source_name}:{contract_name} "
            f"Yul object {selected_name}",
            file=sys.stderr,
        )
    else:
        print(rendered, end="")


def check_rendered_lean(args: argparse.Namespace, rendered: str) -> None:
    if not args.check:
        return
    if args.output:
        run_lake_check(args.lake, args.output, args.lake_cwd)
        return
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as temp:
        temp.write(rendered)
        temp_path = Path(temp.name)
    try:
        run_lake_check(args.lake, temp_path, args.lake_cwd)
    finally:
        temp_path.unlink(missing_ok=True)


def reject_bridge_json_solc_options(args: argparse.Namespace) -> None:
    if args.include_source:
        fail("--include-source is only valid with --input-format solidity")
    if args.remapping or args.remappings_file:
        fail(
            "--remapping and --remappings-file are only valid with "
            "--input-format solidity"
        )
    if not args.auto_include_imports:
        fail("--no-auto-include-imports is only valid with --input-format solidity")
    if args.solc_arg:
        fail("--solc-arg is only valid with solc-backed input formats")
    if args.optimized:
        fail("--optimized is only valid with solc-backed input formats")
    if not args.via_ir:
        fail("--no-via-ir is only valid with solc-backed input formats")
    if not args.experimental:
        fail("--no-experimental is only valid with solc-backed input formats")
    if args.all_contracts:
        fail("--all-contracts is only valid with --input-format standard-json")


def render_bridge_json_input_output(
    args: argparse.Namespace,
) -> Tuple[str, str, str, str]:
    reject_bridge_json_solc_options(args)
    source_name, contract_name, root, frontend = read_bridge_json_input_with_frontend(
        args.input
    )
    if args.source_name is not None and args.source_name != source_name:
        fail(
            f"Bridge JSON source is {source_name!r}, not requested "
            f"--source-name {args.source_name!r}"
        )
    if args.contract is not None and args.contract != contract_name:
        fail(
            f"Bridge JSON contract is {contract_name!r}, not requested "
            f"--contract {args.contract!r}"
        )
    if args.list_objects:
        if args.check:
            fail("--check is only valid when emitting Lean")
        return (
            "\n".join(object_tree_lines(root)) + "\n",
            source_name,
            contract_name,
            root.name,
        )
    if args.format in {"forge-artifact", "standard-json-output"}:
        fail(
            f"--format {args.format} needs ABI/metadata from solc output; "
            "use --input-format solidity or standard-json"
        )
    if args.auto_object_layout:
        fail(
            "--auto-object-layout requires solc bytecode and is not valid with "
            "--input-format bridge-json"
        )

    if args.format == "bytecode-artifact":
        if requested_scratch_reservation(args) is not None:
            fail(
                "An explicit scratch reservation applies to one selected Yul "
                "object and is not valid with --format bytecode-artifact"
            )
        if args.object is not None:
            fail(
                "--object is not valid with --format bytecode-artifact; "
                "artifacts always emit creation and runtime bytecode"
            )
        if args.bridge_json:
            fail("--bridge-json is not valid with --format bytecode-artifact")
        if args.check:
            fail("--check is only valid when emitting Lean")
        explicit_layout = [
            parse_object_layout_entry(entry) for entry in args.object_layout
        ]
        linker_symbols = [
            parse_linker_symbol_entry(entry) for entry in args.linker_symbol
        ]
        write_artifact_bridge_json_outputs(
            args.bridge_json_dir,
            root,
            source_name,
            contract_name,
            linker_symbols,
            explicit_layout,
            args.data_base,
            ast_output=frontend.get("ast") if frontend is not None else None,
        )
        artifact = compile_contract_bytecode_artifact(
            root,
            source_name,
            contract_name,
            args.definition,
            args.namespace,
            explicit_layout,
            args.data_base,
            linker_symbols,
            args.lake,
            args.lake_cwd,
        )
        rendered = render_bytecode_artifact_json(
            source_name,
            contract_name,
            artifact.creation_object_name,
            artifact.runtime_object_name,
            artifact.creation_bytecode,
            artifact.runtime_bytecode,
            artifact.runtime_immutable_references,
            artifact.backend_compatibility,
        )
        selected_name = (
            f"{artifact.creation_object_name}/{artifact.runtime_object_name}"
        )
        return rendered, source_name, contract_name, selected_name

    selected = select_object(root, args.object) if args.object else root
    selected = with_requested_scratch_reservation(selected, args)
    selected_name = selected.name
    bridge_json = render_bridge_json(
        selected,
        source_name,
        contract_name,
        frontend.get("ast") if frontend is not None else None,
    )
    if args.bridge_json:
        args.bridge_json.write_text(bridge_json)
    if args.bridge_json_dir:
            write_bridge_json_output(
                args.bridge_json_dir,
                selected,
                source_name,
                contract_name,
                args.object or "selected",
                merged_linker_symbol_entries(args.linker_symbol),
                ast_output=frontend.get("ast") if frontend is not None else None,
            )

    if args.format == "bridge-json":
        if args.object_layout:
            fail(
                "--object-layout is only valid with --format lean-ir, "
                "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, "
                "or standard-json-output"
            )
        if args.auto_object_layout:
            fail(
                "--auto-object-layout requires solc bytecode and is not valid "
                "with --input-format bridge-json"
            )
        if args.data_base is not None:
            fail(
                "--data-base is only valid with --format lean-ir, "
                "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, "
                "or standard-json-output"
            )
        if args.linker_symbol:
            fail(
                "--linker-symbol is only valid with --format lean-ir, "
                "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, "
                "or standard-json-output"
            )
        if args.check:
            fail("--check is only valid when emitting Lean")
        return bridge_json, source_name, contract_name, selected_name

    if args.format == "bridge-json-summary":
        if args.object_layout:
            fail("--object-layout is not used with --format bridge-json-summary")
        if args.auto_object_layout:
            fail("--auto-object-layout is not used with --format bridge-json-summary")
        if args.data_base is not None:
            fail("--data-base is not used with --format bridge-json-summary")
        if args.linker_symbol:
            fail("--linker-symbol is not used with --format bridge-json-summary")
        if args.check:
            fail("--check is only valid when emitting Lean")
        return (
            render_bridge_json_summary(
                selected,
                source_name,
                contract_name,
                args.object or "selected",
                frontend,
            ),
            source_name,
            contract_name,
            selected_name,
        )

    if args.format == "lean-json-check":
        if args.object_layout:
            fail("--object-layout is not used with --format lean-json-check")
        if args.auto_object_layout:
            fail(
                "--auto-object-layout requires solc bytecode and is not valid "
                "with --input-format bridge-json"
            )
        if args.data_base is not None:
            fail("--data-base is not used with --format lean-json-check")
        if args.linker_symbol:
            fail("--linker-symbol is not used with --format lean-json-check")
        if args.check:
            fail("--check is only valid when emitting Lean")
        return (
            check_bridge_json_with_lean(bridge_json, args.lake, args.lake_cwd),
            source_name,
            contract_name,
            selected_name,
        )

    if args.format == "lean-backend-check":
        if args.object_layout:
            fail("--object-layout is not used with --format lean-backend-check")
        if args.auto_object_layout:
            fail(
                "--auto-object-layout requires solc bytecode and is not valid "
                "with --input-format bridge-json"
            )
        if args.data_base is not None:
            fail("--data-base is not used with --format lean-backend-check")
        if args.check:
            fail("--check is only valid when emitting Lean")
        linker_symbols = [
            parse_linker_symbol_entry(entry) for entry in args.linker_symbol
        ]
        return (
            check_bridge_json_backend_with_lean(
                bridge_json,
                args.lake,
                args.lake_cwd,
                linker_symbols,
            ),
            source_name,
            contract_name,
            selected_name,
        )

    if args.format in {"lean-ir", "lean-json-ir", "bytecode"}:
        explicit_layout = [
            parse_object_layout_entry(entry) for entry in args.object_layout
        ]
        linker_symbols = [
            parse_linker_symbol_entry(entry) for entry in args.linker_symbol
        ]
        if args.format == "lean-ir":
            rendered = render_frontend_module(
                selected,
                source_name,
                contract_name,
                args.definition,
                args.namespace,
                explicit_layout,
                args.data_base,
                linker_symbols,
            )
        elif args.format == "lean-json-ir":
            rendered = render_frontend_json_module(
                selected,
                source_name,
                contract_name,
                args.definition,
                args.namespace,
                explicit_layout,
                args.data_base,
                linker_symbols,
            )
        else:
            if args.check:
                fail("--check is only valid when emitting Lean")
            rendered = (
                compile_frontend_object_bytecode(
                    selected,
                    source_name,
                    contract_name,
                    args.definition,
                    args.namespace,
                    explicit_layout,
                    args.data_base,
                    linker_symbols,
                    args.lake,
                    args.lake_cwd,
                )
                + "\n"
            )
        return rendered, source_name, contract_name, selected_name

    if args.object_layout:
        fail(
            "--object-layout is only valid with --format lean-ir, "
            "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, or "
            "standard-json-output"
        )
    if args.data_base is not None:
        fail(
            "--data-base is only valid with --format lean-ir, "
            "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, or "
            "standard-json-output"
        )
    if args.linker_symbol:
        fail(
            "--linker-symbol is only valid with --format lean-ir, "
            "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, or "
            "standard-json-output"
        )
    rendered = render_module(
        selected,
        source_name,
        contract_name,
        args.definition,
        args.namespace,
    )
    return rendered, source_name, contract_name, selected_name


def reject_standalone_yul_solidity_options(args: argparse.Namespace) -> None:
    if args.include_source:
        fail("--include-source is only valid with --input-format solidity")
    if args.remapping or args.remappings_file:
        fail(
            "--remapping and --remappings-file are only valid with "
            "--input-format solidity"
        )
    if not args.auto_include_imports:
        fail("--no-auto-include-imports is only valid with --input-format solidity")
    if not args.via_ir:
        fail("--no-via-ir is only valid with Solidity input")
    if args.optimized:
        fail(
            "--optimized is not supported for standalone Yul source AST imports; "
            "solc exposes the parsed source ast, not an optimized Yul AST"
        )
    if args.all_contracts:
        fail("--all-contracts is only valid with Solidity Standard JSON input")


def render_standalone_yul_object_output(
    args: argparse.Namespace,
    root: YulObject,
    source_name: str,
    contract_name: str,
) -> Tuple[str, str, str, str]:
    ast_output = solc_standalone_yul_ast_output()
    if args.list_objects:
        if args.check:
            fail("--check is only valid when emitting Lean")
        return "\n".join(object_tree_lines(root)) + "\n", source_name, contract_name, root.name
    if args.auto_object_layout:
        fail(
            "--auto-object-layout requires Solidity creation/deployed bytecode "
            "and is not valid with standalone Yul input"
        )
    if args.format in {"bytecode-artifact", "forge-artifact", "standard-json-output"}:
        fail(
            f"--format {args.format} needs Solidity ABI/metadata and creation/"
            "runtime bytecode; use Solidity or Solidity Standard JSON input"
        )

    selected = select_object(root, args.object or "runtime")
    selected = with_requested_scratch_reservation(selected, args)
    selected_name = selected.name
    bridge_json = render_bridge_json(selected, source_name, contract_name, ast_output)
    linker_symbols = merged_linker_symbol_entries(args.linker_symbol)

    if args.bridge_json:
        args.bridge_json.write_text(bridge_json)
    if args.bridge_json_dir:
        write_bridge_json_output(
            args.bridge_json_dir,
            selected,
            source_name,
            contract_name,
            args.object or "runtime",
            linker_symbols,
            ast_output=ast_output,
        )

    if args.format == "bridge-json":
        if args.object_layout:
            fail(
                "--object-layout is only valid with --format lean-ir, "
                "lean-json-ir, or bytecode for standalone Yul input"
            )
        if args.data_base is not None:
            fail(
                "--data-base is only valid with --format lean-ir, "
                "lean-json-ir, or bytecode for standalone Yul input"
            )
        if args.linker_symbol:
            fail(
                "--linker-symbol is only valid with --format lean-ir, "
                "lean-json-ir, bytecode, or lean-backend-check"
            )
        if args.check:
            fail("--check is only valid when emitting Lean")
        return bridge_json, source_name, contract_name, selected_name

    if args.format == "bridge-json-summary":
        if args.object_layout:
            fail("--object-layout is not used with --format bridge-json-summary")
        if args.data_base is not None:
            fail("--data-base is not used with --format bridge-json-summary")
        if args.linker_symbol:
            fail("--linker-symbol is not used with --format bridge-json-summary")
        if args.check:
            fail("--check is only valid when emitting Lean")
        return (
            render_bridge_json_summary(
                selected,
                source_name,
                contract_name,
                args.object or "runtime",
                bridge_json_frontend_metadata(ast_output),
            ),
            source_name,
            contract_name,
            selected_name,
        )

    if args.format == "lean-json-check":
        if args.object_layout:
            fail("--object-layout is not used with --format lean-json-check")
        if args.data_base is not None:
            fail("--data-base is not used with --format lean-json-check")
        if args.linker_symbol:
            fail("--linker-symbol is not used with --format lean-json-check")
        if args.check:
            fail("--check is only valid when emitting Lean")
        return (
            check_bridge_json_with_lean(bridge_json, args.lake, args.lake_cwd),
            source_name,
            contract_name,
            selected_name,
        )

    if args.format == "lean-backend-check":
        if args.object_layout:
            fail("--object-layout is not used with --format lean-backend-check")
        if args.data_base is not None:
            fail("--data-base is not used with --format lean-backend-check")
        if args.check:
            fail("--check is only valid when emitting Lean")
        return (
            check_bridge_json_backend_with_lean(
                bridge_json,
                args.lake,
                args.lake_cwd,
                linker_symbols,
            ),
            source_name,
            contract_name,
            selected_name,
        )

    if args.format in {"lean-ir", "lean-json-ir", "bytecode"}:
        object_layout = [
            parse_object_layout_entry(entry) for entry in args.object_layout
        ]
        if args.format == "lean-ir":
            rendered = render_frontend_module(
                selected,
                source_name,
                contract_name,
                args.definition,
                args.namespace,
                object_layout,
                args.data_base,
                linker_symbols,
            )
        elif args.format == "lean-json-ir":
            rendered = render_frontend_json_module(
                selected,
                source_name,
                contract_name,
                args.definition,
                args.namespace,
                object_layout,
                args.data_base,
                linker_symbols,
            )
        else:
            if args.check:
                fail("--check is only valid when emitting Lean")
            rendered = (
                compile_frontend_object_bytecode(
                    selected,
                    source_name,
                    contract_name,
                    args.definition,
                    args.namespace,
                    object_layout,
                    args.data_base,
                    linker_symbols,
                    args.lake,
                    args.lake_cwd,
                )
                + "\n"
            )
        return rendered, source_name, contract_name, selected_name

    if args.object_layout:
        fail(
            "--object-layout is only valid with --format lean-ir, "
            "lean-json-ir, or bytecode for standalone Yul input"
        )
    if args.data_base is not None:
        fail(
            "--data-base is only valid with --format lean-ir, lean-json-ir, "
            "or bytecode for standalone Yul input"
        )
    if args.linker_symbol:
        fail(
            "--linker-symbol is only valid with --format lean-ir, lean-json-ir, "
            "bytecode, or lean-backend-check"
        )
    rendered = render_module(
        selected,
        source_name,
        contract_name,
        args.definition,
        args.namespace,
    )
    return rendered, source_name, contract_name, selected_name


def render_bridge_json_manifest_input_output(
    args: argparse.Namespace,
) -> Tuple[str, str, str, str]:
    reject_bridge_json_solc_options(args)
    if args.format not in {
        "bytecode-artifact",
        "lean-json-check",
        "lean-backend-check",
        "bridge-json-summary",
    }:
        fail(
            "--input-format bridge-json-manifest currently supports only "
            "--format bytecode-artifact, lean-json-check, lean-backend-check, or "
            "bridge-json-summary"
        )
    if args.bridge_json:
        fail("--bridge-json is not valid with --input-format bridge-json-manifest")
    if args.bridge_json_dir:
        fail(
            "--bridge-json-dir is not valid with "
            "--input-format bridge-json-manifest"
        )
    if args.list_objects:
        fail("--list-objects is not valid with --input-format bridge-json-manifest")
    if args.object_layout and args.format != "bytecode-artifact":
        fail(f"--object-layout is not used with --format {args.format}")
    if args.auto_object_layout:
        fail(f"--auto-object-layout is not used with --format {args.format}")
    if args.data_base is not None and args.format != "bytecode-artifact":
        fail(f"--data-base is not used with --format {args.format}")
    if args.linker_symbol and args.format not in {
        "bytecode-artifact",
        "lean-backend-check",
    }:
        fail(f"--linker-symbol is not used with --format {args.format}")
    if args.check:
        fail("--check is only valid when emitting Lean")

    manifest_path = args.input
    if str(manifest_path) == "-":
        fail("--input-format bridge-json-manifest requires a manifest file path")
    manifest = read_bridge_json_manifest_file(manifest_path)
    validate_bridge_json_manifest_index(manifest, manifest_path)
    entries = manifest["entries"]
    matched_entries = [
        entry for entry in entries
        if bridge_json_manifest_entry_matches(
            entry,
            manifest_path,
            args.source_name,
            args.contract,
            args.object,
        )
    ]
    skipped_contracts = bridge_json_manifest_skipped_contracts(
        manifest,
        manifest_path,
        args.source_name,
        args.contract,
    )
    skipped_contract_entries = bridge_json_manifest_skipped_contract_entries(
        manifest,
        manifest_path,
        args.source_name,
        args.contract,
    )
    if not matched_entries and not skipped_contracts:
        filters = []
        if args.source_name is not None:
            filters.append(f"source={args.source_name!r}")
        if args.contract is not None:
            filters.append(f"contract={args.contract!r}")
        if args.object is not None:
            filters.append(f"object={args.object!r}")
        suffix = f" matching {', '.join(filters)}" if filters else ""
        fail(f"Bridge JSON manifest {manifest_path} has no entries{suffix}")

    if args.format == "bytecode-artifact":
        creation_entries = [
            entry
            for entry in matched_entries
            if isinstance(entry, dict) and entry.get("selector") == "creation"
        ]
        if len(creation_entries) != 1:
            fail(
                "--input-format bridge-json-manifest --format bytecode-artifact "
                "requires exactly one matching creation entry; use --source-name "
                "and/or --contract to select one contract"
            )
        entry_source, entry_contract, selector, root = bridge_json_manifest_object(
            manifest_path,
            creation_entries[0],
        )
        if selector != "creation":
            fail(
                "--input-format bridge-json-manifest --format bytecode-artifact "
                "requires a creation entry"
            )
        linker_symbols = merged_linker_symbol_entries(
            args.linker_symbol,
            extra_entries=bridge_json_manifest_linker_symbols(
                manifest,
                manifest_path,
            ),
        )
        explicit_layout = [
            parse_object_layout_entry(entry) for entry in args.object_layout
        ]
        persisted_layout = bridge_json_manifest_entry_object_layout(
            creation_entries[0],
            manifest_path,
        )
        object_layout = merge_layout_entries(explicit_layout, persisted_layout)
        local_data_base = (
            args.data_base
            if args.data_base is not None
            else bridge_json_manifest_entry_local_data_base(
                creation_entries[0],
                manifest_path,
            )
        )
        artifact = compile_contract_bytecode_artifact(
            root,
            entry_source,
            entry_contract,
            args.definition,
            args.namespace,
            object_layout,
            local_data_base,
            linker_symbols,
            args.lake,
            args.lake_cwd,
        )
        artifact = attach_bridge_json_provenance(artifact, manifest_path.parent)
        rendered = render_bytecode_artifact_json(
            artifact.source_name,
            artifact.contract_name,
            artifact.creation_object_name,
            artifact.runtime_object_name,
            artifact.creation_bytecode,
            artifact.runtime_bytecode,
            artifact.runtime_immutable_references,
            artifact.backend_compatibility,
            artifact.bridge_json,
        )
        selected_name = (
            f"{artifact.creation_object_name}/{artifact.runtime_object_name}"
        )
    elif args.format == "bridge-json-summary":
        summaries = []
        for entry in matched_entries:
            entry_source, entry_contract, selector, obj = bridge_json_manifest_object(
                manifest_path,
                entry,
            )
            summaries.append(
                bridge_json_summary_artifact(
                    obj,
                    entry_source,
                    entry_contract,
                    selector,
                    bridge_json_manifest_entry_frontend(entry, manifest_path),
                )
            )
        rendered = render_bridge_json_summary_outputs(
            summaries,
            skipped_contracts,
            skipped_contract_entries,
        )
        selected_name = f"{len(summaries)} manifest object summaries"
    elif args.format == "lean-json-check":
        artifacts = [
            bridge_json_manifest_artifact(
                manifest_path,
                entry,
                args.lake,
                args.lake_cwd,
            )
            for entry in matched_entries
        ]
        rendered = render_lean_json_check_outputs(artifacts, skipped_contracts)
        selected_name = f"{len(artifacts)} manifest objects"
    else:
        linker_symbols = merged_linker_symbol_entries(
            args.linker_symbol,
            extra_entries=bridge_json_manifest_linker_symbols(
                manifest,
                manifest_path,
            ),
        )
        artifacts = [
            bridge_json_manifest_backend_artifact(
                manifest_path,
                entry,
                args.lake,
                args.lake_cwd,
                linker_symbols,
            )
            for entry in matched_entries
        ]
        rendered = render_lean_backend_check_outputs(artifacts, skipped_contracts)
        selected_name = f"{len(artifacts)} manifest backend checks"
    source_name = args.source_name or "*"
    contract_name = args.contract or "*"
    return rendered, source_name, contract_name, selected_name


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    try:
        if args.input_format == "bridge-json-manifest":
            rendered, source_name, contract_name, selected_name = (
                render_bridge_json_manifest_input_output(args)
            )
            emit_rendered_output(
                args,
                rendered,
                source_name,
                contract_name,
                selected_name,
            )
            return 0
        if args.input_format == "bridge-json":
            rendered, source_name, contract_name, selected_name = (
                render_bridge_json_input_output(args)
            )
            emit_rendered_output(
                args,
                rendered,
                source_name,
                contract_name,
                selected_name,
            )
            check_rendered_lean(args, rendered)
            return 0
        if args.input_format == "yul":
            reject_standalone_yul_solidity_options(args)
            source_name, content = read_source_input(args.input, args.source_name)
            compiler_input = yul_standard_json_input(
                source_name,
                content,
                experimental=args.experimental,
            )
            output = run_solc(args.solc, compiler_input, args.solc_arg)
            source_name, root_ast = load_yul_source_ast(output, source_name)
            recover_standalone_yul_data_names(root_ast, content)
            contract_name = raw_object_name(root_ast)
            if args.contract is not None and args.contract != contract_name:
                fail(
                    f"Standalone Yul root object is {contract_name!r}, not "
                    f"requested --contract {args.contract!r}"
                )
            root = parse_yul_object(root_ast)
            rendered, source_name, contract_name, selected_name = (
                render_standalone_yul_object_output(
                    args,
                    root,
                    source_name,
                    contract_name,
                )
            )
            emit_rendered_output(
                args,
                rendered,
                source_name,
                contract_name,
                selected_name,
            )
            check_rendered_lean(args, rendered)
            return 0
        require_solc_bytecode = args.auto_object_layout or args.format in {
            "bytecode-artifact",
            "forge-artifact",
            "standard-json-output",
        }
        if args.input_format == "standard-json":
            if args.include_source:
                fail("--include-source is only valid with --input-format solidity")
            if args.remapping or args.remappings_file:
                fail(
                    "--remapping and --remappings-file are only valid with "
                    "--input-format solidity"
                )
            compiler_input = read_standard_json_input(args.input)
            language = compiler_input.get("language", "Solidity")
            if language == "Yul":
                reject_standalone_yul_solidity_options(args)
                compiler_input = ensure_standard_json_yul_outputs(
                    compiler_input,
                    default_experimental=args.experimental,
                )
                output = run_solc(args.solc, compiler_input, args.solc_arg)
                source_name, root_ast = load_yul_source_ast(output, args.source_name)
                recover_standalone_yul_data_names(
                    root_ast,
                    standard_json_source_content(compiler_input, source_name),
                )
                contract_name = raw_object_name(root_ast)
                if args.contract is not None and args.contract != contract_name:
                    fail(
                        f"Standalone Yul root object is {contract_name!r}, not "
                        f"requested --contract {args.contract!r}"
                    )
                root = parse_yul_object(root_ast)
                rendered, source_name, contract_name, selected_name = (
                    render_standalone_yul_object_output(
                        args,
                        root,
                        source_name,
                        contract_name,
                    )
                )
                emit_rendered_output(
                    args,
                    rendered,
                    source_name,
                    contract_name,
                    selected_name,
                )
                check_rendered_lean(args, rendered)
                return 0
            if language != "Solidity":
                fail(f"Unsupported solc Standard JSON language: {language!r}")
            compiler_input = ensure_standard_json_frontend_outputs(
                compiler_input,
                optimized=args.optimized,
                default_via_ir=args.via_ir,
                default_experimental=args.experimental,
                require_bytecode=require_solc_bytecode,
            )
            source_name: Optional[str] = args.source_name
        else:
            source_name, content = read_source_input(args.input, args.source_name)
            explicit_include_sources = read_include_source_files(
                args.include_source,
                source_name,
            )
            import_remappings = read_import_remappings(
                args.remapping,
                args.remappings_file,
            )
            if args.auto_include_imports:
                main_path = None if str(args.input) == "-" else args.input
                include_source_files = collect_local_import_sources(
                    source_name,
                    content,
                    main_path,
                    explicit_include_sources,
                    import_remappings,
                )
            else:
                include_source_files = explicit_include_sources
            include_sources = {
                include_name: include_source.content
                for include_name, include_source in include_source_files.items()
            }
            compiler_input = standard_json_input(
                source_name,
                content,
                via_ir=args.via_ir,
                optimized=args.optimized,
                experimental=args.experimental,
                include_sources=include_sources,
                require_bytecode=require_solc_bytecode,
            )
        ast_output = solc_yul_ast_output(args.optimized)
        output = run_solc(args.solc, compiler_input, args.solc_arg)
        recover_missing_contract_yul_asts(
            output,
            source_name,
            args.contract,
            args.optimized,
            args.experimental,
            args.yul_ast_solc or args.solc,
            args.yul_ast_solc_arg,
        )
        compiler_input_linker_symbols = merged_linker_symbol_entries(
            args.linker_symbol,
            compiler_input,
        )
        if args.all_contracts:
            if requested_scratch_reservation(args) is not None:
                fail(
                    "An explicit scratch reservation must be attached to one "
                    "selected Yul object; it cannot be combined with "
                    "--all-contracts"
                )
            if args.format not in {
                "standard-json-output",
                "lean-json-check",
                "lean-backend-check",
                "bridge-json",
                "bridge-json-summary",
            }:
                fail(
                    "--all-contracts is only valid with --format "
                    "standard-json-output, lean-json-check, lean-backend-check, "
                    "bridge-json, or bridge-json-summary"
                )
            if args.contract is not None:
                fail("--contract cannot be combined with --all-contracts")
            if args.object is not None:
                fail("--object cannot be combined with --all-contracts")
            if args.bridge_json:
                fail("--bridge-json cannot be combined with --all-contracts")
            if args.check:
                fail("--check is only valid when emitting Lean")
            if args.list_objects:
                fail("--list-objects cannot be combined with --all-contracts")
            explicit_layout = [
                parse_object_layout_entry(entry) for entry in args.object_layout
            ]
            linker_symbols = compiler_input_linker_symbols
            all_candidates = contract_candidates(output, source_name, None)
            if not all_candidates:
                available = available_contract_labels(output)
                fail(
                    "No contracts found"
                    + (
                        f" for source {source_name!r}"
                        if source_name is not None
                        else ""
                        )
                    + (
                        f"; available contracts: {', '.join(available)}"
                        if available
                        else ""
                    )
                )
            if args.format == "bridge-json":
                if args.bridge_json_dir is None:
                    fail(
                        "--format bridge-json --all-contracts requires "
                        "--bridge-json-dir"
                    )
                if args.object_layout:
                    fail("--object-layout is not used with --format bridge-json")
                if args.auto_object_layout:
                    fail("--auto-object-layout is not used with --format bridge-json")
                if args.data_base is not None:
                    fail("--data-base is not used with --format bridge-json")
                if args.linker_symbol:
                    fail("--linker-symbol is not used with --format bridge-json")
                candidates = yul_ir_contract_candidates(
                    output,
                    source_name,
                    args.optimized,
                )
                skipped_contracts = skipped_contract_labels(all_candidates, candidates)
                for (
                    candidate_source_name,
                    candidate_contract_name,
                    candidate_contract_output,
                ) in candidates:
                    candidate_ast_output = contract_frontend_ast_output(
                        candidate_source_name,
                        candidate_contract_name,
                        args.optimized,
                    )
                    root_ast = load_ir_ast(candidate_contract_output, args.optimized)
                    root = parse_yul_object(root_ast)
                    write_artifact_bridge_json_outputs(
                        args.bridge_json_dir,
                        root,
                        candidate_source_name,
                        candidate_contract_name,
                        compiler_input_linker_symbols,
                        ast_output=candidate_ast_output,
                    )
                write_bridge_json_manifest_skipped_contracts(
                    args.bridge_json_dir,
                    skipped_contracts,
                    reason="no-yul-ir",
                )
                manifest = read_bridge_json_manifest_file(
                    bridge_json_manifest_path(args.bridge_json_dir)
                )
                rendered = json.dumps(manifest, indent=2) + "\n"
                selected_name = f"{manifest['counts']['entries']} bridge objects"
                if args.output:
                    expected_manifest_path = bridge_json_manifest_path(
                        args.bridge_json_dir
                    )
                    if args.output.resolve() != expected_manifest_path.resolve():
                        fail(
                            "--format bridge-json --all-contracts emits a "
                            "manifest whose paths are relative to "
                            "--bridge-json-dir; use "
                            f"--output {expected_manifest_path} or omit --output"
                        )
                    args.output.write_text(rendered)
                    print(
                        f"Wrote {args.output} from {source_name or '*'}:* "
                        f"Yul object {selected_name}",
                        file=sys.stderr,
                    )
                else:
                    print(rendered, end="")
                return 0
            if args.format == "bridge-json-summary":
                if args.object_layout:
                    fail("--object-layout is not used with --format bridge-json-summary")
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is not used with "
                        "--format bridge-json-summary"
                    )
                if args.data_base is not None:
                    fail("--data-base is not used with --format bridge-json-summary")
                if args.linker_symbol:
                    fail("--linker-symbol is not used with --format bridge-json-summary")
                candidates = yul_ir_contract_candidates(
                    output,
                    source_name,
                    args.optimized,
                )
                skipped_contracts = skipped_contract_labels(all_candidates, candidates)
                summaries = []
                for (
                    candidate_source_name,
                    candidate_contract_name,
                    candidate_contract_output,
                ) in candidates:
                    candidate_ast_output = contract_frontend_ast_output(
                        candidate_source_name,
                        candidate_contract_name,
                        args.optimized,
                    )
                    root_ast = load_ir_ast(candidate_contract_output, args.optimized)
                    root = parse_yul_object(root_ast)
                    if args.bridge_json_dir is not None:
                        write_artifact_bridge_json_outputs(
                            args.bridge_json_dir,
                            root,
                            candidate_source_name,
                            candidate_contract_name,
                            compiler_input_linker_symbols,
                            ast_output=candidate_ast_output,
                        )
                    objects_to_summarize = [("creation", root)]
                    runtime = select_object(root, "runtime")
                    if runtime.name != root.name:
                        objects_to_summarize.append(("runtime", runtime))
                    for object_selector, selected_object in objects_to_summarize:
                        summaries.append(
                            bridge_json_summary_artifact(
                                selected_object,
                                candidate_source_name,
                                candidate_contract_name,
                                object_selector,
                                bridge_json_frontend_metadata(candidate_ast_output),
                            )
                        )
                if args.bridge_json_dir is not None:
                    write_bridge_json_manifest_skipped_contracts(
                        args.bridge_json_dir,
                        skipped_contracts,
                        reason="no-yul-ir",
                    )
                rendered = render_bridge_json_summary_outputs(
                    summaries,
                    skipped_contracts,
                    skipped_contract_entries_from_labels(
                        skipped_contracts,
                        Path("<standard-json-summary>"),
                        "no-yul-ir",
                    ),
                )
                selected_name = f"{len(summaries)} object summaries"
                if args.output:
                    args.output.write_text(rendered)
                    print(
                        f"Wrote {args.output} from {source_name or '*'}:* "
                        f"Yul object {selected_name}",
                        file=sys.stderr,
                    )
                else:
                    print(rendered, end="")
                return 0
            if args.format == "lean-json-check":
                if args.object_layout:
                    fail("--object-layout is not used with --format lean-json-check")
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is not used with "
                        "--format lean-json-check"
                    )
                if args.data_base is not None:
                    fail("--data-base is not used with --format lean-json-check")
                if args.linker_symbol:
                    fail("--linker-symbol is not used with --format lean-json-check")
                candidates = yul_ir_contract_candidates(
                    output,
                    source_name,
                    args.optimized,
                )
                skipped_contracts = skipped_contract_labels(all_candidates, candidates)
                artifacts = []
                for (
                    candidate_source_name,
                    candidate_contract_name,
                    candidate_contract_output,
                ) in candidates:
                    candidate_ast_output = contract_frontend_ast_output(
                        candidate_source_name,
                        candidate_contract_name,
                        args.optimized,
                    )
                    root_ast = load_ir_ast(candidate_contract_output, args.optimized)
                    root = parse_yul_object(root_ast)
                    write_artifact_bridge_json_outputs(
                        args.bridge_json_dir,
                        root,
                        candidate_source_name,
                        candidate_contract_name,
                        compiler_input_linker_symbols,
                        ast_output=candidate_ast_output,
                    )
                    objects_to_check = [("creation", root)]
                    runtime = select_object(root, "runtime")
                    if runtime.name != root.name:
                        objects_to_check.append(("runtime", runtime))
                    for object_selector, selected_object in objects_to_check:
                        artifacts.append(
                            check_frontend_object_with_lean(
                                selected_object,
                                candidate_source_name,
                                candidate_contract_name,
                                object_selector,
                                args.lake,
                                args.lake_cwd,
                                bridge_json_frontend_metadata(candidate_ast_output),
                            )
                        )
                if args.bridge_json_dir is not None:
                    write_bridge_json_manifest_skipped_contracts(
                        args.bridge_json_dir,
                        skipped_contracts,
                        reason="no-yul-ir",
                    )
                rendered = render_lean_json_check_outputs(
                    artifacts,
                    skipped_contracts,
                )
                selected_name = f"{len(artifacts)} objects"
                if args.output:
                    args.output.write_text(rendered)
                    print(
                        f"Wrote {args.output} from {source_name or '*'}:* "
                        f"Yul object {selected_name}",
                        file=sys.stderr,
                    )
                else:
                    print(rendered, end="")
                return 0
            if args.format == "lean-backend-check":
                if args.object_layout:
                    fail("--object-layout is not used with --format lean-backend-check")
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is not used with "
                        "--format lean-backend-check"
                    )
                if args.data_base is not None:
                    fail("--data-base is not used with --format lean-backend-check")
                candidates = yul_ir_contract_candidates(
                    output,
                    source_name,
                    args.optimized,
                )
                skipped_contracts = skipped_contract_labels(all_candidates, candidates)
                artifacts = []
                for (
                    candidate_source_name,
                    candidate_contract_name,
                    candidate_contract_output,
                ) in candidates:
                    candidate_ast_output = contract_frontend_ast_output(
                        candidate_source_name,
                        candidate_contract_name,
                        args.optimized,
                    )
                    root_ast = load_ir_ast(candidate_contract_output, args.optimized)
                    root = parse_yul_object(root_ast)
                    write_artifact_bridge_json_outputs(
                        args.bridge_json_dir,
                        root,
                        candidate_source_name,
                        candidate_contract_name,
                        compiler_input_linker_symbols,
                        ast_output=candidate_ast_output,
                    )
                    objects_to_check = [("creation", root)]
                    runtime = select_object(root, "runtime")
                    if runtime.name != root.name:
                        objects_to_check.append(("runtime", runtime))
                    for object_selector, selected_object in objects_to_check:
                        artifacts.append(
                            check_frontend_object_backend_with_lean(
                                selected_object,
                                candidate_source_name,
                                candidate_contract_name,
                                object_selector,
                                args.lake,
                                args.lake_cwd,
                                linker_symbols,
                                bridge_json_frontend_metadata(candidate_ast_output),
                            )
                        )
                if args.bridge_json_dir is not None:
                    write_bridge_json_manifest_skipped_contracts(
                        args.bridge_json_dir,
                        skipped_contracts,
                        reason="no-yul-ir",
                    )
                rendered = render_lean_backend_check_outputs(
                    artifacts,
                    skipped_contracts,
                )
                selected_name = f"{len(artifacts)} backend checks"
                if args.output:
                    args.output.write_text(rendered)
                    print(
                        f"Wrote {args.output} from {source_name or '*'}:* "
                        f"Yul object {selected_name}",
                        file=sys.stderr,
                    )
                else:
                    print(rendered, end="")
                return 0
            candidates = lean_bytecode_contract_candidates(
                output,
                source_name,
                args.optimized,
            )
            skipped_contracts = skipped_contract_labels(all_candidates, candidates)
            artifacts = []
            for index, (
                candidate_source_name,
                candidate_contract_name,
                candidate_contract_output,
            ) in enumerate(candidates):
                candidate_ast_output = contract_frontend_ast_output(
                    candidate_source_name,
                    candidate_contract_name,
                    args.optimized,
                )
                root_ast = load_ir_ast(candidate_contract_output, args.optimized)
                root = parse_yul_object(root_ast)
                inferred_layout = (
                    infer_object_layout(root, candidate_contract_output)
                    if args.auto_object_layout
                    else []
                )
                object_layout = merge_layout_entries(explicit_layout, inferred_layout)
                write_artifact_bridge_json_outputs(
                    args.bridge_json_dir,
                    root,
                    candidate_source_name,
                    candidate_contract_name,
                    compiler_input_linker_symbols,
                    object_layout,
                    args.data_base,
                    candidate_ast_output,
                )
                artifact = compile_contract_bytecode_artifact(
                    root,
                    candidate_source_name,
                    candidate_contract_name,
                    f"{args.definition}Contract{index}",
                    args.namespace,
                    object_layout,
                    args.data_base,
                    linker_symbols,
                    args.lake,
                    args.lake_cwd,
                )
                artifacts.append(
                    attach_bridge_json_provenance(artifact, args.bridge_json_dir)
                )
            if args.bridge_json_dir is not None:
                write_bridge_json_manifest_skipped_contracts(
                    args.bridge_json_dir,
                    skipped_contracts,
                    reason="no-lean-bytecode-inputs",
                )
            rendered = render_standard_json_outputs(output, artifacts)
            selected_name = f"{len(artifacts)} contracts"
            if args.output:
                args.output.write_text(rendered)
                print(
                    f"Wrote {args.output} from {source_name or '*'}:* "
                    f"Yul object {selected_name}",
                    file=sys.stderr,
                )
            else:
                print(rendered, end="")
            return 0
        source_name, contract_name, contract_output = choose_contract(
            output,
            source_name,
            args.contract,
        )
        ast_output = contract_frontend_ast_output(
            source_name,
            contract_name,
            args.optimized,
        )
        root_ast = load_ir_ast(contract_output, args.optimized)
        if args.list_objects:
            print("\n".join(raw_object_tree_lines(root_ast)))
            return 0
        root = parse_yul_object(root_ast)

        artifact_formats = {
            "bytecode-artifact",
            "forge-artifact",
            "standard-json-output",
        }
        if args.format in artifact_formats:
            if requested_scratch_reservation(args) is not None:
                fail(
                    "An explicit scratch reservation applies to one selected "
                    f"Yul object and is not valid with --format {args.format}"
                )
            if args.object is not None:
                fail(
                    f"--object is not valid with --format {args.format}; "
                    "artifacts always emit creation and runtime bytecode"
                )
            if args.bridge_json:
                fail(f"--bridge-json is not valid with --format {args.format}")
            if args.check:
                fail("--check is only valid when emitting Lean")
            explicit_layout = [
                parse_object_layout_entry(entry) for entry in args.object_layout
            ]
            linker_symbols = compiler_input_linker_symbols
            inferred_layout = (
                infer_object_layout(root, contract_output)
                if args.auto_object_layout
                else []
            )
            object_layout = merge_layout_entries(explicit_layout, inferred_layout)
            write_artifact_bridge_json_outputs(
                args.bridge_json_dir,
                root,
                source_name,
                contract_name,
                linker_symbols,
                object_layout,
                args.data_base,
                ast_output,
            )
            artifact = compile_contract_bytecode_artifact(
                root,
                source_name,
                contract_name,
                args.definition,
                args.namespace,
                object_layout,
                args.data_base,
                linker_symbols,
                args.lake,
                args.lake_cwd,
            )
            artifact = attach_bridge_json_provenance(artifact, args.bridge_json_dir)
            if args.format == "forge-artifact":
                rendered = render_forge_artifact_json(
                    source_name,
                    contract_name,
                    artifact.creation_object_name,
                    artifact.runtime_object_name,
                    contract_output,
                    artifact.creation_bytecode,
                    artifact.runtime_bytecode,
                    artifact.runtime_immutable_references,
                    artifact.backend_compatibility,
                    artifact.bridge_json,
                )
            elif args.format == "standard-json-output":
                rendered = render_standard_json_output(
                    output,
                    source_name,
                    contract_name,
                    artifact.creation_object_name,
                    artifact.runtime_object_name,
                    artifact.creation_bytecode,
                    artifact.runtime_bytecode,
                    artifact.runtime_immutable_references,
                    artifact.backend_compatibility,
                    artifact.bridge_json,
                )
            else:
                rendered = render_bytecode_artifact_json(
                    source_name,
                    contract_name,
                    artifact.creation_object_name,
                    artifact.runtime_object_name,
                    artifact.creation_bytecode,
                    artifact.runtime_bytecode,
                    artifact.runtime_immutable_references,
                    artifact.backend_compatibility,
                    artifact.bridge_json,
                )
            selected_name = (
                f"{artifact.creation_object_name}/{artifact.runtime_object_name}"
            )
        else:
            selected = select_object(root, args.object or "runtime")
            selected = with_requested_scratch_reservation(selected, args)
            selected_name = selected.name
            bridge_json = render_bridge_json(
                selected,
                source_name,
                contract_name,
                ast_output,
            )
            if args.bridge_json:
                args.bridge_json.write_text(bridge_json)
            if args.bridge_json_dir:
                write_bridge_json_output(
                    args.bridge_json_dir,
                    selected,
                    source_name,
                    contract_name,
                    args.object or "runtime",
                    compiler_input_linker_symbols,
                    ast_output=ast_output,
                )

            if args.format == "bridge-json":
                if args.object_layout:
                    fail(
                        "--object-layout is only valid with --format lean-ir, "
                        "lean-json-ir, bytecode, bytecode-artifact, "
                        "forge-artifact, or standard-json-output"
                    )
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is only valid with "
                        "--format lean-ir, lean-json-ir, bytecode, "
                        "bytecode-artifact, forge-artifact, or standard-json-output"
                    )
                if args.data_base is not None:
                    fail(
                        "--data-base is only valid with --format lean-ir, "
                        "lean-json-ir, bytecode, bytecode-artifact, "
                        "forge-artifact, or standard-json-output"
                    )
                if args.linker_symbol:
                    fail(
                        "--linker-symbol is only valid with --format lean-ir, "
                        "lean-json-ir, bytecode, bytecode-artifact, "
                        "forge-artifact, or standard-json-output"
                    )
                if args.check:
                    fail("--check is only valid when emitting Lean")
                rendered = bridge_json
            elif args.format == "bridge-json-summary":
                if args.object_layout:
                    fail("--object-layout is not used with --format bridge-json-summary")
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is not used with "
                        "--format bridge-json-summary"
                    )
                if args.data_base is not None:
                    fail("--data-base is not used with --format bridge-json-summary")
                if args.linker_symbol:
                    fail("--linker-symbol is not used with --format bridge-json-summary")
                if args.check:
                    fail("--check is only valid when emitting Lean")
                rendered = render_bridge_json_summary(
                    selected,
                    source_name,
                    contract_name,
                    args.object or "runtime",
                    bridge_json_frontend_metadata(ast_output),
                )
            elif args.format == "lean-json-check":
                if args.object_layout:
                    fail("--object-layout is not used with --format lean-json-check")
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is not used with "
                        "--format lean-json-check"
                    )
                if args.data_base is not None:
                    fail("--data-base is not used with --format lean-json-check")
                if args.linker_symbol:
                    fail("--linker-symbol is not used with --format lean-json-check")
                if args.check:
                    fail("--check is only valid when emitting Lean")
                rendered = check_bridge_json_with_lean(
                    bridge_json,
                    args.lake,
                    args.lake_cwd,
                )
            elif args.format == "lean-backend-check":
                if args.object_layout:
                    fail("--object-layout is not used with --format lean-backend-check")
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is not used with "
                        "--format lean-backend-check"
                    )
                if args.data_base is not None:
                    fail("--data-base is not used with --format lean-backend-check")
                if args.check:
                    fail("--check is only valid when emitting Lean")
                linker_symbols = compiler_input_linker_symbols
                rendered = check_bridge_json_backend_with_lean(
                    bridge_json,
                    args.lake,
                    args.lake_cwd,
                    linker_symbols,
                )
            elif args.format in {"lean-ir", "lean-json-ir", "bytecode"}:
                explicit_layout = [
                    parse_object_layout_entry(entry) for entry in args.object_layout
                ]
                linker_symbols = compiler_input_linker_symbols
                inferred_layout = (
                    infer_object_layout(root, contract_output)
                    if args.auto_object_layout
                    else []
                )
                object_layout = merge_layout_entries(explicit_layout, inferred_layout)
                if args.format == "lean-ir":
                    rendered = render_frontend_module(
                        selected,
                        source_name,
                        contract_name,
                        args.definition,
                        args.namespace,
                        object_layout,
                        args.data_base,
                        linker_symbols,
                    )
                elif args.format == "lean-json-ir":
                    rendered = render_frontend_json_module(
                        selected,
                        source_name,
                        contract_name,
                        args.definition,
                        args.namespace,
                        object_layout,
                        args.data_base,
                        linker_symbols,
                    )
                else:
                    if args.check:
                        fail("--check is only valid when emitting Lean")
                    rendered = (
                        compile_frontend_object_bytecode(
                            selected,
                            source_name,
                            contract_name,
                            args.definition,
                            args.namespace,
                            object_layout,
                            args.data_base,
                            linker_symbols,
                            args.lake,
                            args.lake_cwd,
                        )
                        + "\n"
                    )
            else:
                if args.object_layout:
                    fail(
                        "--object-layout is only valid with --format lean-ir, "
                        "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, or "
                        "standard-json-output"
                    )
                if args.auto_object_layout:
                    fail(
                        "--auto-object-layout is only valid with "
                        "--format lean-ir, lean-json-ir, bytecode, bytecode-artifact, "
                        "forge-artifact, or standard-json-output"
                    )
                if args.data_base is not None:
                    fail(
                        "--data-base is only valid with --format lean-ir, "
                        "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, or "
                        "standard-json-output"
                    )
                if args.linker_symbol:
                    fail(
                        "--linker-symbol is only valid with --format lean-ir, "
                        "lean-json-ir, bytecode, bytecode-artifact, forge-artifact, or "
                        "standard-json-output"
                    )
                rendered = render_module(
                    selected,
                    source_name,
                    contract_name,
                    args.definition,
                    args.namespace,
                )
        if args.output:
            args.output.write_text(rendered)
            print(
                f"Wrote {args.output} from {source_name}:{contract_name} "
                f"Yul object {selected_name}",
                file=sys.stderr,
            )
        else:
            print(rendered, end="")
        if args.check:
            if args.output:
                run_lake_check(args.lake, args.output, args.lake_cwd)
            else:
                with tempfile.NamedTemporaryFile(
                    "w", suffix=".lean", delete=False
                ) as temp:
                    temp.write(rendered)
                    temp_path = Path(temp.name)
                try:
                    run_lake_check(args.lake, temp_path, args.lake_cwd)
                finally:
                    temp_path.unlink(missing_ok=True)
        return 0
    except ConversionError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
