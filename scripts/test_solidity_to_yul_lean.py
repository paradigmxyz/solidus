#!/usr/bin/env python3
import hashlib
import io
import json
import os
from collections import Counter
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

import compare_contract_call_bytecode as compare_call
import run_forge_project_compare as forge_project_compare
import solc_lean_standard_json as solc_lean_wrapper
import solidity_to_yul_lean as bridge
import validate_bridge_json

try:
    import jsonschema
except ImportError:
    jsonschema = None

# The bridge's bytecode-producing formats are gated as unverified
# diagnostics; the unit tests exercise them as such.
os.environ.setdefault("EVM_COMPILER_UNVERIFIED_DIAGNOSTIC", "1")


def literal(value):
    return {
        "nodeType": "YulLiteral",
        "kind": "number",
        "value": value,
        "nativeSrc": "0:0:0",
    }


def string_literal(value):
    return {
        "nodeType": "YulLiteral",
        "kind": "string",
        "value": value,
        "nativeSrc": "0:0:0",
    }


def hex_string_literal(hex_value, value=None):
    node = {
        "nodeType": "YulLiteral",
        "kind": "string",
        "hexValue": hex_value,
        "nativeSrc": "0:0:0",
    }
    if value is not None:
        node["value"] = value
    return node


def bool_literal(value):
    return {
        "nodeType": "YulLiteral",
        "kind": "bool",
        "value": value,
        "nativeSrc": "0:0:0",
    }


def identifier(name):
    return {"nodeType": "YulIdentifier", "name": name, "nativeSrc": "0:0:0"}


def call(name, args):
    return {
        "nodeType": "YulFunctionCall",
        "functionName": {"nodeType": "YulIdentifier", "name": name},
        "arguments": args,
        "nativeSrc": "0:0:0",
    }


def block(statements):
    return {"nodeType": "YulBlock", "statements": statements, "nativeSrc": "0:0:0"}


class SolidityToYulLeanTests(unittest.TestCase):
    def test_read_source_input_accepts_stdin(self):
        old_stdin = sys.stdin
        try:
            sys.stdin = io.StringIO("contract Stdin {}")
            source_name, content = bridge.read_source_input(Path("-"), None)
        finally:
            sys.stdin = old_stdin

        self.assertEqual(source_name, "stdin.sol")
        self.assertEqual(content, "contract Stdin {}")

    def test_read_source_input_uses_stdin_source_name_override(self):
        old_stdin = sys.stdin
        try:
            sys.stdin = io.StringIO("contract Named {}")
            source_name, content = bridge.read_source_input(Path("-"), "Named.sol")
        finally:
            sys.stdin = old_stdin

        self.assertEqual(source_name, "Named.sol")
        self.assertEqual(content, "contract Named {}")

    def test_include_source_arg_uses_file_name_by_default(self):
        source_name, path = bridge.parse_include_source_arg("contracts/MathLib.sol")
        self.assertEqual(source_name, "MathLib.sol")
        self.assertEqual(path, Path("contracts/MathLib.sol"))

    def test_include_source_arg_accepts_explicit_source_name(self):
        source_name, path = bridge.parse_include_source_arg(
            "vendor/MathLib.sol=deps/math/MathLib.sol"
        )
        self.assertEqual(source_name, "vendor/MathLib.sol")
        self.assertEqual(path, Path("deps/math/MathLib.sol"))

    def test_linker_symbol_arg_accepts_hex_value(self):
        entry = bridge.parse_linker_symbol_entry("MathLib.sol:MathLib=0x2a")
        self.assertEqual(entry.name, "MathLib.sol:MathLib")
        self.assertEqual(entry.value, 42)
        self.assertIn(
            '("MathLib.sol:MathLib", EvmYul.UInt256.ofNat 42)',
            entry.lean_ir(),
        )

    def test_standard_json_libraries_become_linker_symbols(self):
        entries = bridge.standard_json_linker_symbol_entries(
            {
                "language": "Solidity",
                "sources": {"UsesLibrary.sol": {"content": "contract C {}"}},
                "settings": {
                    "libraries": {
                        "MathLib.sol": {
                            "MathLib": "000000000000000000000000000000000000002a",
                        }
                    }
                },
            }
        )

        self.assertEqual(
            [(entry.name, entry.value) for entry in entries],
            [("MathLib.sol:MathLib", 42)],
        )

    def test_explicit_linker_symbols_override_standard_json_libraries(self):
        entries = bridge.merged_linker_symbol_entries(
            ["MathLib.sol:MathLib=0x2a"],
            {
                "settings": {
                    "libraries": {
                        "MathLib.sol": {
                            "MathLib": "0x0000000000000000000000000000000000000001",
                        }
                    }
                }
            },
        )

        self.assertEqual(
            [(entry.name, entry.value) for entry in entries],
            [("MathLib.sol:MathLib", 42)],
        )

    def test_import_remapping_arg_accepts_prefix_and_path(self):
        remapping = bridge.parse_import_remapping_arg(
            "@openzeppelin/=lib/openzeppelin-contracts/"
        )
        self.assertEqual(remapping.prefix, "@openzeppelin/")
        self.assertEqual(remapping.target, Path("lib/openzeppelin-contracts"))

    def test_remappings_file_resolves_relative_targets_from_file_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            remappings_file = root / "remappings.txt"
            remappings_file.write_text(
                "# comment\n@pkg/=lib/pkg/src/\n@alt/=../vendor/alt/\n"
            )
            remappings = bridge.read_import_remappings([], [remappings_file])
        self.assertEqual(
            remappings,
            [
                bridge.ImportRemapping("@pkg/", root / "lib/pkg/src"),
                bridge.ImportRemapping("@alt/", root / "../vendor/alt"),
            ],
        )

    def test_remapped_import_path_uses_longest_prefix_and_later_tie(self):
        remappings = [
            bridge.ImportRemapping("@pkg/", Path("lib/pkg")),
            bridge.ImportRemapping("@pkg/special/", Path("lib/pkg-special")),
            bridge.ImportRemapping("@pkg/special/", Path("override/special")),
        ]
        self.assertEqual(
            bridge.resolve_remapped_import_path(
                "@pkg/special/Thing.sol",
                remappings,
            ),
            Path("override/special/Thing.sol"),
        )
        self.assertIsNone(
            bridge.resolve_remapped_import_path("other/Thing.sol", remappings)
        )

    def test_read_include_sources_rejects_duplicate_main_source_name(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "UsesLibrary.sol"
            source.write_text("library UsesLibrary {}")
            with self.assertRaises(bridge.ConversionError):
                bridge.read_include_sources([str(source)], "UsesLibrary.sol")

    def test_standard_json_can_include_import_sources(self):
        request = bridge.standard_json_input(
            "UsesLibrary.sol",
            'import "./MathLib.sol"; contract UsesLibrary {}',
            via_ir=True,
            optimized=False,
            experimental=True,
            include_sources={"MathLib.sol": "library MathLib {}"},
        )
        self.assertIn("UsesLibrary.sol", request["sources"])
        self.assertIn("MathLib.sol", request["sources"])
        self.assertEqual(request["settings"]["evmVersion"], "cancun")
        self.assertEqual(
            request["sources"]["MathLib.sol"]["content"],
            "library MathLib {}",
        )

    def test_standard_json_preserves_optimizer_runs(self):
        request = bridge.standard_json_input(
            "Protocol.sol",
            "contract Protocol {}",
            via_ir=True,
            optimized=True,
            experimental=True,
            optimizer_runs=999999,
        )
        self.assertEqual(
            request["settings"]["optimizer"],
            {
                "enabled": True,
                "details": {"yul": True},
                "runs": 999999,
            },
        )

    def test_contract_compare_preserves_optimizer_and_yul_parser_options(self):
        parser = compare_call.build_arg_parser()
        args = parser.parse_args(
            [
                "Protocol.sol",
                "--contract",
                "Protocol",
                "--calldata",
                "0x",
                "--optimized",
                "--evm-version",
                "paris",
                "--optimizer-runs",
                "999999",
                "--yul-ast-solc",
                "/opt/solc-0.8.26",
                "--yul-ast-solc-arg=--base-path",
            ]
        )
        command = []
        compare_call.append_bridge_compile_options(command, args)
        self.assertIn("--optimizer-runs", command)
        self.assertIn("--evm-version", command)
        self.assertIn("paris", command)
        self.assertIn("999999", command)
        self.assertIn("--yul-ast-solc", command)
        self.assertIn("/opt/solc-0.8.26", command)
        self.assertIn("--yul-ast-solc-arg=--base-path", command)

    def test_yul_standard_json_input_requests_source_ast(self):
        request = bridge.yul_standard_json_input(
            "Object.yul",
            'object "Object" { code { let x := 1 } }',
            experimental=True,
        )

        self.assertEqual(request["language"], "Yul")
        self.assertNotIn("viaIR", request["settings"])
        self.assertEqual(request["settings"]["evmVersion"], "cancun")
        self.assertTrue(request["settings"]["experimental"])
        self.assertEqual(
            request["settings"]["outputSelection"]["*"]["*"],
            ["ast"],
        )

    def test_standard_json_yul_outputs_preserve_existing_outputs_and_add_ast(self):
        request = {
            "language": "Yul",
            "sources": {
                "Object.yul": {
                    "content": 'object "Object" { code { let x := 1 } }'
                }
            },
            "settings": {
                "outputSelection": {
                    "*": {
                        "*": ["evm.bytecode.object"],
                    }
                }
            },
        }

        updated = bridge.ensure_standard_json_yul_outputs(
            request,
            default_experimental=True,
        )

        self.assertTrue(updated["settings"]["experimental"])
        self.assertEqual(
            updated["settings"]["outputSelection"]["*"]["*"],
            ["evm.bytecode.object", "ast"],
        )

    def test_load_yul_source_ast_selects_standalone_yul_source(self):
        ast = {
            "nodeType": "YulObject",
            "name": "Object",
            "code": {"block": block([]), "nodeType": "YulCode"},
            "subObjects": [],
        }
        output = {
            "sources": {
                "Other.yul": {"id": 0},
                "Object.yul": {"id": 1, "ast": ast},
            }
        }

        source_name, loaded = bridge.load_yul_source_ast(output, "Object.yul")

        self.assertEqual(source_name, "Object.yul")
        self.assertIs(loaded, ast)

    def test_standalone_yul_data_name_recovery_annotates_solc_source_ast(self):
        source = """
        object "Object" {
          code {
            if 1 { let data := "not a declaration" }
          }
          data "blob" hex"00ff"
          object "Object_deployed" {
            code { stop() }
            data "nested" hex"aa"
          }
        }
        """
        ast = {
            "nodeType": "YulObject",
            "name": "Object",
            "code": {"block": block([]), "nodeType": "YulCode"},
            "subObjects": [
                {"nodeType": "YulData", "value": "00ff"},
                {
                    "nodeType": "YulObject",
                    "name": "Object_deployed",
                    "code": {"block": block([]), "nodeType": "YulCode"},
                    "subObjects": [
                        {"nodeType": "YulData", "value": "aa"},
                    ],
                },
            ],
        }

        bridge.recover_standalone_yul_data_names(ast, source)

        self.assertEqual(ast["subObjects"][0]["name"], "blob")
        self.assertEqual(ast["subObjects"][1]["subObjects"][0]["name"], "nested")

    def test_standalone_yul_render_preserves_yul_ast_frontend_metadata(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "Object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "x"}],
                                "value": literal("1"),
                                "nativeSrc": "0:0:0",
                            }
                        ]
                    ),
                    "nodeType": "YulCode",
                },
                "subObjects": [
                    {
                        "nodeType": "YulData",
                        "name": "blob",
                        "value": "00ff",
                    }
                ],
            }
        )
        args = SimpleNamespace(
            list_objects=False,
            check=False,
            auto_object_layout=False,
            format="bridge-json",
            object=None,
            bridge_json=None,
            bridge_json_dir=None,
            linker_symbol=[],
            object_layout=[],
            data_base=None,
            lake="lake",
            lake_cwd=Path.cwd(),
            definition="program",
            namespace=None,
        )

        rendered, source_name, contract_name, selected_name = (
            bridge.render_standalone_yul_object_output(
                args,
                root,
                "Object.yul",
                "Object",
            )
        )
        decoded = json.loads(rendered)

        self.assertEqual(source_name, "Object.yul")
        self.assertEqual(contract_name, "Object")
        self.assertEqual(selected_name, "Object")
        self.assertEqual(decoded["frontend"], {"producer": "solc", "ast": "yulAst", "evmVersion": "cancun"})
        self.assertEqual(decoded["selectedObject"]["data"][0]["name"], "blob")

    def test_import_path_scanner_handles_common_forms_and_comments(self):
        paths = bridge.iter_solidity_import_paths(
            """
            // import "./Commented.sol";
            import "./A.sol";
            import {B as Bee} from "../B.sol";
            import * as C from './C.sol';
            /* import "./AlsoCommented.sol"; */
            """
        )
        self.assertEqual(paths, ["./A.sol", "../B.sol", "./C.sol"])

    def test_relative_import_source_name_matches_standard_json_resolution(self):
        self.assertEqual(
            bridge.resolve_relative_import_source_name("UsesLibrary.sol", "./MathLib.sol"),
            "MathLib.sol",
        )
        self.assertEqual(
            bridge.resolve_relative_import_source_name(
                "contracts/UsesLibrary.sol",
                "./MathLib.sol",
            ),
            "contracts/MathLib.sol",
        )
        self.assertEqual(
            bridge.resolve_relative_import_source_name(
                "contracts/nested/UsesLibrary.sol",
                "../MathLib.sol",
            ),
            "contracts/MathLib.sol",
        )

    def test_collect_local_import_sources_recurses_over_relative_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "UsesLibrary.sol"
            subdir = Path(directory) / "lib"
            subdir.mkdir()
            math = subdir / "MathLib.sol"
            base = Path(directory) / "Base.sol"
            root.write_text('import "./lib/MathLib.sol"; contract UsesLibrary {}')
            math.write_text('import "../Base.sol"; library MathLib {}')
            base.write_text("library Base {}")

            sources = bridge.collect_local_import_sources(
                "UsesLibrary.sol",
                root.read_text(),
                root,
                {},
            )

        self.assertEqual(set(sources), {"lib/MathLib.sol", "Base.sol"})
        self.assertIn("library MathLib", sources["lib/MathLib.sol"].content)
        self.assertIn("library Base", sources["Base.sol"].content)

    def test_collect_local_import_sources_recurses_over_remapped_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root_dir = Path(directory)
            root = root_dir / "UsesPackage.sol"
            package = root_dir / "deps/pkg"
            package.mkdir(parents=True)
            math = package / "MathLib.sol"
            base = package / "Base.sol"
            root.write_text('import "@pkg/MathLib.sol"; contract UsesPackage {}')
            math.write_text('import "./Base.sol"; library MathLib {}')
            base.write_text("library Base {}")

            sources = bridge.collect_local_import_sources(
                "UsesPackage.sol",
                root.read_text(),
                root,
                {},
                [bridge.ImportRemapping("@pkg/", package)],
            )

        self.assertEqual(set(sources), {"@pkg/MathLib.sol", "@pkg/Base.sol"})
        self.assertIn("library MathLib", sources["@pkg/MathLib.sol"].content)
        self.assertIn("library Base", sources["@pkg/Base.sol"].content)

    def test_memoryguard_is_retained_as_object_builtin(self):
        expr = bridge.parse_expr(call("memoryguard", [literal("128")]))
        self.assertIsInstance(expr, bridge.Call)
        self.assertEqual(expr.callee, "memoryguard")
        self.assertEqual(expr.callee_kind, bridge.CALL_OBJECT_BUILTIN)
        self.assertEqual(expr.args, [bridge.Lit(128)])

    def test_yul_literals_accept_native_json_bool_and_number_values(self):
        number = bridge.parse_expr(
            {
                "nodeType": "YulLiteral",
                "kind": "number",
                "value": 42,
                "nativeSrc": "0:0:0",
            }
        )
        truth = bridge.parse_expr(
            {
                "nodeType": "YulLiteral",
                "kind": "bool",
                "value": True,
                "nativeSrc": "0:0:0",
            }
        )
        falsehood = bridge.parse_expr(
            {
                "nodeType": "YulLiteral",
                "kind": "bool",
                "value": False,
                "nativeSrc": "0:0:0",
            }
        )

        self.assertEqual(number, bridge.Lit(42))
        self.assertEqual(truth, bridge.Lit(1))
        self.assertEqual(falsehood, bridge.Lit(0))

    def test_yul_bool_literals_reject_malformed_string_values(self):
        truth = bridge.parse_expr(
            {
                "nodeType": "YulLiteral",
                "kind": "bool",
                "value": "true",
                "nativeSrc": "0:0:0",
            }
        )
        falsehood = bridge.parse_expr(
            {
                "nodeType": "YulLiteral",
                "kind": "bool",
                "value": "false",
                "nativeSrc": "0:0:0",
            }
        )

        self.assertEqual(truth, bridge.Lit(1))
        self.assertEqual(falsehood, bridge.Lit(0))
        with self.assertRaises(bridge.ConversionError):
            bridge.parse_expr(
                {
                    "nodeType": "YulLiteral",
                    "kind": "bool",
                    "value": "truthy",
                    "nativeSrc": "0:0:0",
                }
            )

    def test_bridge_json_accepts_memoryguard_object_builtin(self):
        expr = bridge.decode_bridge_expr(
            {
                "node": "call",
                "callee": "memoryguard",
                "calleeKind": "objectBuiltin",
                "args": [{"node": "literal", "value": 128}],
            }
        )

        self.assertIsInstance(expr, bridge.Call)
        self.assertEqual(expr.callee_kind, bridge.CALL_OBJECT_BUILTIN)
        compatibility = bridge.bridge_summary_backend_compatibility(
            {bridge.CALL_OBJECT_BUILTIN: Counter({"memoryguard": 1})}
        )
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["objectBuiltinNames"], ["memoryguard"])

    def test_bridge_json_rejects_compiler_scratch_contract(self):
        obj = bridge.YulObject("Runtime", [], [], [], [])
        encoded = obj.bridge_json()

        self.assertNotIn("memoryContract", encoded)
        self.assertIn("MemoryContract.unrestricted", obj.lean_ir())
        encoded["memoryContract"] = {"scratch": {"base": 256, "words": 9}}
        with self.assertRaisesRegex(
            bridge.ConversionError, "scratch memory contracts are not supported"
        ):
            bridge.decode_bridge_object(encoded)

    def test_bridge_json_requires_explicit_frontend_metadata(self):
        obj = bridge.YulObject("Runtime", [], [], [], [])
        encoded = json.loads(
            bridge.render_bridge_json(obj, "Simple.sol", "Simple")
        )
        self.assertEqual(
            encoded["frontend"],
            {
                "producer": "solc",
                "ast": "irOptimizedAst",
                "evmVersion": "cancun",
            },
        )
        del encoded["frontend"]
        with self.assertRaisesRegex(
            bridge.ConversionError, "frontend metadata is required"
        ):
            bridge.decode_bridge_program(encoded)

    def test_yul_object_lean_ir_records_declared_fork(self):
        obj = bridge.YulObject("Runtime", [], [], [], [])
        rendered = obj.lean_ir("london")
        self.assertIn("EvmVersion.london", rendered)
        self.assertNotIn("EvmVersion.cancun", rendered)

    def test_scratch_reservation_cli_is_removed(self):
        parser = bridge.build_arg_parser()
        with self.assertRaises(SystemExit):
            parser.parse_args(
                ["input.sol", "--scratch-reservation-base", "0x100"]
            )

    def test_primitive_call_emits_typed_yul_operation(self):
        expr = bridge.parse_expr(call("add", [identifier("x"), literal("1")]))
        rendered = expr.lean()
        self.assertIn("Sum.inl", rendered)
        self.assertIn("EvmYul.Operation.ADD", rendered)
        self.assertIn('EvmYul.Yul.Ast.Expr.Var "x"', rendered)
        self.assertEqual(expr.bridge_json()["calleeKind"], "primitive")

    def test_string_literal_emits_right_padded_word_for_yul_entrypoint(self):
        expr = bridge.parse_expr(string_literal("nope"))
        word = int.from_bytes(b"nope".ljust(32, b"\x00"), "big")

        self.assertEqual(bridge.yul_string_literal_word("nope"), word)
        self.assertIn(f"EvmYul.UInt256.ofNat {word}", expr.lean())
        self.assertIn('Expr.stringLit "nope"', expr.lean_ir())

    def test_string_literal_preserves_source_string_when_solc_also_emits_hex_value(self):
        expr = bridge.parse_expr(hex_string_literal("6162", value="ab"))

        self.assertEqual(expr, bridge.StringLit("ab"))
        self.assertEqual(expr.bridge_json(), {"node": "stringLiteral", "value": "ab"})

    def test_string_literal_rejects_more_than_one_word(self):
        with self.assertRaises(bridge.ConversionError):
            bridge.yul_string_literal_word("x" * 33)

    def test_hex_string_literal_emits_right_padded_word(self):
        expr = bridge.parse_expr(hex_string_literal("ff00"))
        word = int.from_bytes(bytes([0xFF, 0x00]).ljust(32, b"\x00"), "big")

        self.assertIsInstance(expr, bridge.BytesLit)
        self.assertEqual(expr.bytes, [0xFF, 0x00])
        self.assertEqual(bridge.yul_bytes_literal_word([0xFF, 0x00]), word)
        self.assertIn(f"EvmYul.UInt256.ofNat {word}", expr.lean())
        self.assertIn("Expr.bytesLit", expr.lean_ir())
        self.assertIn("UInt8.ofNat 255", expr.lean_ir())
        self.assertEqual(
            expr.bridge_json(),
            {"node": "bytesLiteral", "bytes": [0xFF, 0x00]},
        )

    def test_switch_cases_preserve_string_hex_and_bool_literals(self):
        stmt = bridge.parse_stmt(
            {
                "nodeType": "YulSwitch",
                "expression": identifier("x"),
                "cases": [
                    {
                        "value": string_literal("ok"),
                        "body": block([]),
                        "nativeSrc": "0:0:0",
                    },
                    {
                        "value": hex_string_literal("ff"),
                        "body": block([]),
                        "nativeSrc": "0:0:0",
                    },
                    {
                        "value": bool_literal(True),
                        "body": block([]),
                        "nativeSrc": "0:0:0",
                    },
                ],
                "nativeSrc": "0:0:0",
            }
        )

        self.assertIsInstance(stmt, bridge.Switch)
        self.assertEqual(
            [value.kind for value, _body in stmt.cases],
            [
                bridge.SWITCH_CASE_STRING,
                bridge.SWITCH_CASE_BYTES,
                bridge.SWITCH_CASE_BOOL,
            ],
        )
        self.assertEqual(
            [value.word() for value, _body in stmt.cases],
            [
                bridge.yul_string_literal_word("ok"),
                bridge.yul_bytes_literal_word([0xFF]),
                1,
            ],
        )
        self.assertEqual(
            [value.bridge_json()["node"] for value, _body in stmt.cases],
            ["stringLiteral", "bytesLiteral", "boolLiteral"],
        )
        self.assertIsInstance(
            bridge.decode_bridge_stmt(stmt.bridge_json()).cases[0][0],
            bridge.SwitchCaseValue,
        )

    def test_switch_case_string_literal_preserves_source_string_with_solc_hex_value(self):
        stmt = bridge.parse_stmt(
            {
                "nodeType": "YulSwitch",
                "expression": identifier("x"),
                "cases": [
                    {
                        "value": hex_string_literal("6f6b", value="ok"),
                        "body": block([]),
                        "nativeSrc": "0:0:0",
                    },
                    {
                        "value": hex_string_literal("ff"),
                        "body": block([]),
                        "nativeSrc": "0:0:0",
                    },
                ],
                "nativeSrc": "0:0:0",
            }
        )

        self.assertEqual(
            [value.kind for value, _body in stmt.cases],
            [bridge.SWITCH_CASE_STRING, bridge.SWITCH_CASE_BYTES],
        )
        self.assertEqual(
            [value.bridge_json()["node"] for value, _body in stmt.cases],
            ["stringLiteral", "bytesLiteral"],
        )

    def test_object_builtin_is_preserved_in_bridge_json_but_rejected_by_lean(self):
        expr = bridge.parse_expr(call("datasize", [string_literal("runtime")]))
        self.assertEqual(expr.bridge_json()["calleeKind"], "objectBuiltin")
        self.assertEqual(expr.bridge_json()["args"][0]["node"], "stringLiteral")
        with self.assertRaises(bridge.ConversionError):
            expr.lean()

    def test_immutable_object_builtins_are_preserved_structurally(self):
        load = bridge.parse_expr(call("loadimmutable", [string_literal("3")]))
        self.assertEqual(load.bridge_json()["calleeKind"], "objectBuiltin")
        self.assertEqual(load.bridge_json()["args"][0]["value"], "3")

        stmt = bridge.parse_stmt(
            {
                "nodeType": "YulExpressionStatement",
                "expression": call(
                    "setimmutable",
                    [identifier("_2"), string_literal("3"), identifier("value")],
                ),
                "nativeSrc": "0:0:0",
            }
        )
        rendered = stmt.bridge_json()
        self.assertEqual(rendered["expr"]["callee"], "setimmutable")
        self.assertEqual(rendered["expr"]["calleeKind"], "objectBuiltin")

    def test_top_level_functions_are_split_from_dispatcher(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulExpressionStatement",
                                "expression": call("stop", []),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [{"name": "x"}],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": identifier("x"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [
                    {
                        "nodeType": "YulData",
                        "name": "metadata",
                        "value": "aabbcc",
                        "nativeSrc": "0:0:0",
                    }
                ],
            }
        )
        self.assertEqual(len(root.dispatcher), 1)
        self.assertEqual([name for name, _ in root.functions], ["f"])
        self.assertEqual(root.data, [bridge.DataSection("metadata", [0xaa, 0xbb, 0xcc])])

    def test_nested_functions_are_hoisted_and_calls_rewritten(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            block(
                                [
                                    {
                                        "nodeType": "YulFunctionDefinition",
                                        "name": "f",
                                        "parameters": [],
                                        "returnVariables": [{"name": "r"}],
                                        "body": block(
                                            [
                                                {
                                                    "nodeType": "YulAssignment",
                                                    "variableNames": [identifier("r")],
                                                    "value": literal("1"),
                                                    "nativeSrc": "0:0:0",
                                                }
                                            ]
                                        ),
                                        "nativeSrc": "0:0:0",
                                    },
                                    {
                                        "nodeType": "YulFunctionDefinition",
                                        "name": "g",
                                        "parameters": [],
                                        "returnVariables": [{"name": "r"}],
                                        "body": block(
                                            [
                                                {
                                                    "nodeType": "YulAssignment",
                                                    "variableNames": [identifier("r")],
                                                    "value": call("f", []),
                                                    "nativeSrc": "0:0:0",
                                                }
                                            ]
                                        ),
                                        "nativeSrc": "0:0:0",
                                    },
                                    {
                                        "nodeType": "YulVariableDeclaration",
                                        "variables": [{"name": "y"}],
                                        "value": call("g", []),
                                        "nativeSrc": "0:0:0",
                                    },
                                ]
                            )
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        function_names = [name for name, _ in root.functions]
        self.assertEqual(function_names, ["__yul_gen_0_f", "__yul_gen_1_g"])
        dispatcher_block = root.dispatcher[0]
        self.assertIsInstance(dispatcher_block, bridge.Block)
        self.assertIsInstance(dispatcher_block.stmts[0], bridge.FunctionStmt)
        self.assertEqual(dispatcher_block.stmts[0].name, "f")
        self.assertIsInstance(dispatcher_block.stmts[1], bridge.FunctionStmt)
        self.assertEqual(dispatcher_block.stmts[1].name, "g")
        self.assertEqual(dispatcher_block.stmts[0].bridge_json()["node"], "function")
        self.assertIsInstance(
            bridge.decode_bridge_stmt(dispatcher_block.stmts[0].bridge_json()),
            bridge.FunctionStmt,
        )
        nested_let = dispatcher_block.stmts[2]
        self.assertIsInstance(nested_let, bridge.Let)
        self.assertIsInstance(nested_let.value, bridge.Call)
        self.assertEqual(nested_let.value.callee, "__yul_gen_1_g")

        _, g_fn = root.functions[1]
        g_assign = g_fn.body[0]
        self.assertIsInstance(g_assign, bridge.Assign)
        self.assertIsInstance(g_assign.value, bridge.Call)
        self.assertEqual(g_assign.value.callee, "__yul_gen_0_f")

    def test_single_result_user_calls_stay_direct(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": literal("1"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "x"}],
                                "value": call("f", []),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulAssignment",
                                "variableNames": [identifier("x")],
                                "value": call("f", []),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertEqual([name for name, _ in root.functions], ["f"])
        let_call = root.dispatcher[0]
        self.assertEqual(let_call, bridge.Let(["x"], bridge.Call("f", [], bridge.CALL_USER)))
        assign_call = root.dispatcher[1]
        self.assertEqual(assign_call, bridge.Assign(["x"], bridge.Call("f", [], bridge.CALL_USER)))

    def test_single_result_user_calls_with_simple_args_are_preserved(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [{"name": "a"}, {"name": "b"}],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": identifier("a"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "a"}],
                                "value": literal("1"),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "x"}],
                                "value": call("f", [identifier("a"), literal("2")]),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulAssignment",
                                "variableNames": [identifier("x")],
                                "value": call("f", [identifier("a"), literal("3")]),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertEqual([name for name, _ in root.functions], ["f"])
        self.assertEqual(root.dispatcher[0], bridge.Let(["a"], bridge.Lit(1)))
        self.assertEqual(
            root.dispatcher[1],
            bridge.Let(
                ["x"],
                bridge.Call(
                    "f",
                    [bridge.Var("a"), bridge.Lit(2)],
                    bridge.CALL_USER,
                ),
            ),
        )
        self.assertEqual(
            root.dispatcher[2],
            bridge.Assign(
                ["x"],
                bridge.Call(
                    "f",
                    [bridge.Var("a"), bridge.Lit(3)],
                    bridge.CALL_USER,
                ),
            ),
        )

        summary = bridge.bridge_json_summary_artifact(
            root,
            "SingleResultArgs.sol",
            "SingleResultArgs",
            "runtime",
        )
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(summary["backendCompatibility"]["unsupportedPrimitiveNames"], [])
        self.assertEqual(
            summary["calls"]["user"]["names"],
            [{"name": "f", "count": 2}],
        )

    def test_multi_result_user_calls_stay_direct_statement_forms(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [],
                                "returnVariables": [{"name": "a"}, {"name": "b"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("a")],
                                            "value": literal("1"),
                                            "nativeSrc": "0:0:0",
                                        },
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("b")],
                                            "value": literal("2"),
                                            "nativeSrc": "0:0:0",
                                        },
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "x"}, {"name": "y"}],
                                "value": call("f", []),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulAssignment",
                                "variableNames": [identifier("x"), identifier("y")],
                                "value": call("f", []),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertEqual([name for name, _ in root.functions], ["f"])
        self.assertEqual(
            root.dispatcher[0],
            bridge.Let(["x", "y"], bridge.Call("f", [], bridge.CALL_USER)),
        )
        self.assertEqual(
            root.dispatcher[1],
            bridge.Assign(["x", "y"], bridge.Call("f", [], bridge.CALL_USER)),
        )

        summary = bridge.bridge_json_summary_artifact(
            root,
            "MultiResult.sol",
            "MultiResult",
            "runtime",
        )
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(summary["backendCompatibility"]["unsupportedPrimitiveNames"], [])
        self.assertEqual(
            summary["calls"]["user"]["names"],
            [{"name": "f", "count": 2}],
        )

    def test_single_result_user_calls_can_be_nested_in_expressions(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": literal("1"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "x"}],
                                "value": call("add", [call("f", []), literal("2")]),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        nested_let = root.dispatcher[0]
        self.assertIsInstance(nested_let, bridge.Let)
        self.assertIsInstance(nested_let.value, bridge.Call)
        self.assertEqual(nested_let.value.callee_kind, bridge.CALL_PRIMITIVE)
        self.assertEqual(nested_let.value.callee, "add")
        self.assertEqual(
            nested_let.value.args[0],
            bridge.Call("f", [], bridge.CALL_USER),
        )

        summary = bridge.bridge_json_summary_artifact(
            root,
            "NestedCall.sol",
            "NestedCall",
            "runtime",
        )
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(summary["backendCompatibility"]["unsupportedPrimitiveNames"], [])
        self.assertEqual(
            summary["calls"]["primitive"]["names"],
            [{"name": "add", "count": 1}],
        )
        self.assertEqual(
            summary["calls"]["user"]["names"],
            [{"name": "f", "count": 1}],
        )

    def test_single_result_user_calls_can_be_control_conditions(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": literal("1"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulIf",
                                "condition": call("f", []),
                                "body": block([]),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulSwitch",
                                "expression": call("f", []),
                                "cases": [
                                    {
                                        "value": literal("1"),
                                        "body": block([]),
                                        "nativeSrc": "0:0:0",
                                    }
                                ],
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulForLoop",
                                "pre": block([]),
                                "condition": call("f", []),
                                "post": block([]),
                                "body": block([]),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        if_stmt, switch_stmt, for_stmt = root.dispatcher
        self.assertEqual(if_stmt, bridge.If(bridge.Call("f", [], bridge.CALL_USER), []))
        self.assertEqual(
            switch_stmt,
            bridge.Switch(
                bridge.Call("f", [], bridge.CALL_USER),
                [(bridge.SwitchCaseValue(bridge.SWITCH_CASE_WORD, 1), [])],
                [],
            ),
        )
        self.assertEqual(for_stmt, bridge.For([], bridge.Call("f", [], bridge.CALL_USER), [], []))

        summary = bridge.bridge_json_summary_artifact(
            root,
            "ControlCall.sol",
            "ControlCall",
            "runtime",
        )
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(summary["backendCompatibility"]["unsupportedPrimitiveNames"], [])
        self.assertEqual(
            summary["calls"]["user"]["names"],
            [{"name": "f", "count": 3}],
        )

    def test_single_result_user_calls_can_be_arguments_to_user_calls(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "g",
                                "parameters": [],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": literal("1"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "f",
                                "parameters": [{"name": "a"}],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": identifier("a"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "x"}],
                                "value": call("f", [call("g", [])]),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulAssignment",
                                "variableNames": [identifier("x")],
                                "value": call("f", [call("g", [])]),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertEqual([name for name, _ in root.functions], ["g", "f"])
        let_call = root.dispatcher[0]
        self.assertIsInstance(let_call, bridge.Let)
        self.assertEqual(let_call.names, ["x"])
        self.assertEqual(
            let_call.value,
            bridge.Call("f", [bridge.Call("g", [], bridge.CALL_USER)], bridge.CALL_USER),
        )
        assign_call = root.dispatcher[1]
        self.assertIsInstance(assign_call, bridge.Assign)
        self.assertEqual(assign_call.names, ["x"])
        self.assertEqual(
            assign_call.value,
            bridge.Call("f", [bridge.Call("g", [], bridge.CALL_USER)], bridge.CALL_USER),
        )

        summary = bridge.bridge_json_summary_artifact(
            root,
            "NestedUserCallArg.sol",
            "NestedUserCallArg",
            "runtime",
        )
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(summary["backendCompatibility"]["unsupportedPrimitiveNames"], [])
        self.assertEqual(
            summary["calls"]["user"]["names"],
            [{"name": "f", "count": 2}, {"name": "g", "count": 2}],
        )

    def test_for_init_functions_are_hoisted_across_loop_scope(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulForLoop",
                                "pre": block(
                                    [
                                        {
                                            "nodeType": "YulFunctionDefinition",
                                            "name": "f",
                                            "parameters": [],
                                            "returnVariables": [{"name": "r"}],
                                            "body": block(
                                                [
                                                    {
                                                        "nodeType": "YulAssignment",
                                                        "variableNames": [
                                                            identifier("r")
                                                        ],
                                                        "value": literal("1"),
                                                        "nativeSrc": "0:0:0",
                                                    }
                                                ]
                                            ),
                                            "nativeSrc": "0:0:0",
                                        },
                                        {
                                            "nodeType": "YulVariableDeclaration",
                                            "variables": [{"name": "i"}],
                                            "value": call("f", []),
                                            "nativeSrc": "0:0:0",
                                        },
                                    ]
                                ),
                                "condition": call("f", []),
                                "post": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("i")],
                                            "value": call("f", []),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulVariableDeclaration",
                                            "variables": [{"name": "y"}],
                                            "value": call("f", []),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            }
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertEqual([name for name, _ in root.functions], ["__yul_gen_0_f"])
        loop = root.dispatcher[0]
        self.assertIsInstance(loop, bridge.For)
        self.assertIsInstance(loop.pre[0], bridge.FunctionStmt)
        self.assertEqual(loop.pre[0].name, "f")
        init_let = loop.pre[1]
        self.assertIsInstance(init_let, bridge.Let)
        self.assertIsInstance(init_let.value, bridge.Call)
        self.assertEqual(init_let.value.callee, "__yul_gen_0_f")

        self.assertIsInstance(loop.cond, bridge.Call)
        self.assertEqual(loop.cond.callee, "__yul_gen_0_f")

        post_assign = loop.post[0]
        self.assertIsInstance(post_assign, bridge.Assign)
        self.assertIsInstance(post_assign.value, bridge.Call)
        self.assertEqual(post_assign.value.callee, "__yul_gen_0_f")

        body_let = loop.body[0]
        self.assertIsInstance(body_let, bridge.Let)
        self.assertIsInstance(body_let.value, bridge.Call)
        self.assertEqual(body_let.value.callee, "__yul_gen_0_f")

    def test_nested_function_source_shadowing_is_rejected_before_hoisting(self):
        with self.assertRaisesRegex(bridge.ConversionError, "already taken"):
            bridge.parse_yul_object(
                {
                    "nodeType": "YulObject",
                    "name": "object",
                    "code": {
                        "block": block(
                            [
                                block(
                                    [
                                        {
                                            "nodeType": "YulFunctionDefinition",
                                            "name": "f",
                                            "parameters": [],
                                            "returnVariables": [],
                                            "body": block([]),
                                            "nativeSrc": "0:0:0",
                                        },
                                        {
                                            "nodeType": "YulVariableDeclaration",
                                            "variables": [{"name": "f"}],
                                            "value": literal("2"),
                                            "nativeSrc": "0:0:0",
                                        },
                                    ]
                                )
                            ]
                        )
                    },
                    "subObjects": [],
                }
            )

    def test_nested_function_conflict_with_outer_variable_is_rejected(self):
        with self.assertRaisesRegex(bridge.ConversionError, "already taken"):
            bridge.parse_yul_object(
                {
                    "nodeType": "YulObject",
                    "name": "object",
                    "code": {
                        "block": block(
                            [
                                {
                                    "nodeType": "YulVariableDeclaration",
                                    "variables": [{"name": "x"}],
                                    "value": literal("1"),
                                    "nativeSrc": "0:0:0",
                                },
                                block(
                                    [
                                        {
                                            "nodeType": "YulFunctionDefinition",
                                            "name": "x",
                                            "parameters": [],
                                            "returnVariables": [],
                                            "body": block([]),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                            ]
                        )
                    },
                    "subObjects": [],
                }
            )

    def test_function_parameter_cannot_shadow_source_function_name(self):
        with self.assertRaisesRegex(bridge.ConversionError, "already taken"):
            bridge.parse_yul_object(
                {
                    "nodeType": "YulObject",
                    "name": "object",
                    "code": {
                        "block": block(
                            [
                                block(
                                    [
                                        {
                                            "nodeType": "YulFunctionDefinition",
                                            "name": "f",
                                            "parameters": [{"name": "f"}],
                                            "returnVariables": [],
                                            "body": block([]),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                )
                            ]
                        )
                    },
                    "subObjects": [],
                }
            )

    def test_clz_calls_are_expanded_to_generated_yul_helper(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulFunctionDefinition",
                                "name": "__yul_gen_0_clz",
                                "parameters": [],
                                "returnVariables": [{"name": "r"}],
                                "body": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("r")],
                                            "value": literal("0"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "z"}],
                                "value": call("clz", [identifier("x")]),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertEqual(
            [name for name, _ in root.functions],
            ["__yul_gen_0_clz", "__yul_gen_1_clz"],
        )
        clz_call = root.dispatcher[0].value
        self.assertIsInstance(clz_call, bridge.Call)
        self.assertEqual(clz_call.callee, "__yul_gen_1_clz")
        self.assertEqual(clz_call.callee_kind, bridge.CALL_USER)

        helper = root.functions[1][1]
        self.assertEqual(len(helper.params), 1)
        self.assertEqual(len(helper.returns), 1)
        self.assertEqual(helper.body[0], bridge.Assign([helper.returns[0]], bridge.Lit(256)))
        self.assertIn("EvmYul.Operation.SHR", helper.lean())

    def test_for_loop_init_function_definition_is_hoisted(self):
        ctx = bridge.ParseContext()
        stmt = bridge.parse_stmt(
            {
                "nodeType": "YulForLoop",
                "pre": block(
                    [
                        {
                            "nodeType": "YulFunctionDefinition",
                            "name": "f",
                            "parameters": [],
                            "returnVariables": [],
                            "body": block([]),
                            "nativeSrc": "0:0:0",
                        }
                    ]
                ),
                "condition": literal("1"),
                "post": block([]),
                "body": block([]),
                "nativeSrc": "0:0:0",
            },
            ctx,
        )

        self.assertIsInstance(stmt, bridge.For)
        self.assertIsInstance(stmt.pre[0], bridge.FunctionStmt)
        self.assertEqual(stmt.pre[0].name, "f")
        self.assertEqual([name for name, _ in ctx.hoisted_functions], ["__yul_gen_0_f"])

    def test_for_loop_init_scope_does_not_escape_source_scope(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "object",
                "code": {
                    "block": block(
                        [
                            {
                                "nodeType": "YulForLoop",
                                "pre": block(
                                    [
                                        {
                                            "nodeType": "YulVariableDeclaration",
                                            "variables": [{"name": "i"}],
                                            "value": literal("0"),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "condition": call(
                                    "lt",
                                    [identifier("i"), literal("1")],
                                ),
                                "post": block(
                                    [
                                        {
                                            "nodeType": "YulAssignment",
                                            "variableNames": [identifier("i")],
                                            "value": call(
                                                "add",
                                                [identifier("i"), literal("1")],
                                            ),
                                            "nativeSrc": "0:0:0",
                                        }
                                    ]
                                ),
                                "body": block([]),
                                "nativeSrc": "0:0:0",
                            },
                            {
                                "nodeType": "YulVariableDeclaration",
                                "variables": [{"name": "i"}],
                                "value": literal("2"),
                                "nativeSrc": "0:0:0",
                            },
                        ]
                    )
                },
                "subObjects": [],
            }
        )

        self.assertIsInstance(root.dispatcher[0], bridge.For)
        self.assertEqual(root.dispatcher[1], bridge.Let(["i"], bridge.Lit(2)))

    def test_bridge_json_preserves_selected_object_tree(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "root",
                "code": {"block": block([])},
                "subObjects": [
                    {
                        "nodeType": "YulObject",
                        "name": "root_deployed",
                        "code": {
                            "block": block(
                                [
                                    {
                                        "nodeType": "YulExpressionStatement",
                                        "expression": call("stop", []),
                                        "nativeSrc": "0:0:0",
                                    }
                                ]
                            )
                        },
                        "subObjects": [
                            {
                                "nodeType": "YulData",
                                "value": "aa",
                                "nativeSrc": "0:0:0",
                            }
                        ],
                    }
                ],
            }
        )
        selected = bridge.select_object(root, "runtime")
        rendered = bridge.render_bridge_json(selected, "Simple.sol", "Simple")
        self.assertIn('"schema": "evm-compiler.solc-yul-bridge.v3"', rendered)
        self.assertIn('"name": "root_deployed"', rendered)
        self.assertIn('"data": [', rendered)
        self.assertIn('"bytes": [', rendered)
        self.assertIn("170", rendered)
        rendered_with_frontend = json.loads(
            bridge.render_bridge_json(
                selected,
                "Simple.sol",
                "Simple",
                "irOptimizedAst",
            )
        )
        self.assertEqual(
            rendered_with_frontend["frontend"],
            {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
        )

    def test_bridge_frontend_metadata_accepts_post_cancun_fork_spellings(self):
        expected = {
            "prague": "prague",
            "pectra": "prague",
            "osaka": "osaka",
            "fusaka": "osaka",
        }
        for evm_version, lean_constructor in expected.items():
            with self.subTest(evm_version=evm_version):
                frontend = bridge.bridge_json_frontend_metadata("irAst", evm_version)
                self.assertEqual(frontend["evmVersion"], evm_version)
                self.assertEqual(
                    bridge.normalize_bridge_json_frontend_metadata(
                        frontend,
                        "frontend",
                    ),
                    frontend,
                )
                self.assertEqual(
                    bridge.lean_evm_version(evm_version),
                    (
                        "EvmCompiler.Yul.SolcValidation.EvmVersion."
                        f"{lean_constructor}"
                    ),
                )

    def test_ordered_subobjects_preserve_solc_payload_order(self):
        root = bridge.parse_yul_object(
            {
                "nodeType": "YulObject",
                "name": "root",
                "code": {"block": block([])},
                "subObjects": [
                    {
                        "nodeType": "YulData",
                        "name": "first_data",
                        "value": "aa",
                        "nativeSrc": "0:0:0",
                    },
                    {
                        "nodeType": "YulObject",
                        "name": "child",
                        "code": {"block": block([])},
                        "subObjects": [],
                    },
                    {
                        "nodeType": "YulData",
                        "name": "second_data",
                        "value": "bb",
                        "nativeSrc": "0:0:0",
                    },
                ],
            }
        )
        self.assertEqual(
            root.items,
            [
                bridge.ObjectItemRef("data", 0),
                bridge.ObjectItemRef("object", 0),
                bridge.ObjectItemRef("data", 1),
            ],
        )
        self.assertEqual(
            root.bridge_json()["items"],
            [
                {"kind": "data", "index": 0},
                {"kind": "object", "index": 0},
                {"kind": "data", "index": 1},
            ],
        )

        rendered = root.lean_ir()
        first = rendered.find("EvmCompiler.Solidity.Frontend.ObjectItemRef.data 0")
        child = rendered.find("EvmCompiler.Solidity.Frontend.ObjectItemRef.object 0")
        second = rendered.find("EvmCompiler.Solidity.Frontend.ObjectItemRef.data 1")
        self.assertTrue(0 <= first < child < second)

    def test_bridge_json_summary_counts_structural_features(self):
        child = bridge.YulObject(
            name="child",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "stop",
                        [],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.Let(
                    ["x"],
                    bridge.Call(
                        "sload",
                        [bridge.Lit(0)],
                        bridge.CALL_PRIMITIVE,
                    ),
                ),
                bridge.ExprStmt(
                    bridge.Call(
                        "datacopy",
                        [bridge.Lit(0), bridge.StringLit("metadata"), bridge.Lit(1)],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                ),
            ],
            functions=[
                (
                    "f",
                    bridge.FunctionDef(
                        params=["a"],
                        returns=["r"],
                        body=[
                            bridge.If(
                                bridge.Call(
                                    "iszero",
                                    [bridge.Var("a")],
                                    bridge.CALL_PRIMITIVE,
                                ),
                                [bridge.Control("Leave")],
                            ),
                            bridge.Assign(
                                ["r"],
                                bridge.Call(
                                    "helper",
                                    [bridge.Var("a")],
                                    bridge.CALL_USER,
                                ),
                            ),
                        ],
                    ),
                )
            ],
            data=[bridge.DataSection("metadata", [0xaa, 0xbb])],
            subobjects=[child],
            items=[bridge.ObjectItemRef("data", 0), bridge.ObjectItemRef("object", 0)],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "Summary.sol",
            "Summary",
            "runtime",
        )

        self.assertEqual(summary["schema"], "evm-compiler.solc-yul-bridge-summary.v1")
        self.assertEqual(summary["counts"]["objects"], 2)
        self.assertEqual(summary["counts"]["functions"], 1)
        self.assertEqual(summary["counts"]["dataSections"], 1)
        self.assertEqual(summary["counts"]["dataBytes"], 2)
        primitive_names = {
            entry["name"]: entry["count"]
            for entry in summary["calls"]["primitive"]["names"]
        }
        self.assertEqual(primitive_names["sload"], 1)
        self.assertEqual(primitive_names["iszero"], 1)
        self.assertEqual(primitive_names["stop"], 1)
        self.assertEqual(summary["calls"]["objectBuiltin"]["names"][0]["name"], "datacopy")
        self.assertEqual(summary["calls"]["user"]["names"][0]["name"], "helper")
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(
            summary["backendCompatibility"]["objectBuiltinNames"],
            ["datacopy"],
        )
        self.assertIn("object-builtins-computed", "\n".join(summary["backendHints"]))

    def test_bridge_json_summary_marks_current_backend_blockers(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "call",
                        [
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                        ],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "Calls.sol",
            "Calls",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["profile"], "current-yul-compiler")
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertIn("open external-boundary", " ".join(compatibility["notes"]))

    def test_bridge_json_summary_marks_external_effect_family_supported(self):
        external_primitives = [
            "call",
            "callcode",
            "delegatecall",
            "staticcall",
            "create",
            "create2",
        ]
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(name, [], bridge.CALL_PRIMITIVE)
                )
                for name in external_primitives
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "ExternalEffects.sol",
            "ExternalEffects",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertIn("open external-boundary", " ".join(compatibility["notes"]))
        self.assertIn(
            "external-effect-primitives-present: call, callcode, create, "
            "create2, delegatecall, staticcall",
            "\n".join(summary["backendHints"]),
        )

    def test_bridge_json_summary_marks_external_account_code_family_supported(self):
        external_primitives = ["balance", "extcodesize", "extcodecopy", "extcodehash"]
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(bridge.Call(name, [], bridge.CALL_PRIMITIVE))
                for name in external_primitives
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "ExternalCode.sol",
            "ExternalCode",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertIn("code-image preservation", " ".join(compatibility["notes"]))
        self.assertIn(
            "external-account-query-primitives-present: balance, "
            "extcodecopy, extcodehash, extcodesize",
            "\n".join(summary["backendHints"]),
        )

    def test_bridge_json_summary_marks_unsupported_dialect_builtins_blocked(self):
        pc_call = bridge.parse_expr(call("pc", []))
        self.assertIsInstance(pc_call, bridge.Call)
        self.assertEqual(pc_call.callee_kind, bridge.CALL_DIALECT_BUILTIN)

        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(pc_call),
                bridge.ExprStmt(bridge.parse_expr(call("dataloadn", [literal("0")]))),
                bridge.ExprStmt(bridge.parse_expr(call("verbatim_0i_0o", []))),
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "Dialect.sol",
            "Dialect",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "blocked")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertEqual(
            compatibility["dialectBuiltinNames"],
            ["dataloadn", "pc", "verbatim_0i_0o"],
        )
        self.assertIn("pc/raw-EVM and verbatim/EOF", " ".join(compatibility["notes"]))
        self.assertIn(
            "unsupported-dialect-builtins-present",
            "\n".join(summary["backendHints"]),
        )

    def test_reserved_raw_evm_opcodes_are_not_imported_as_user_calls(self):
        self.assertIn("clz", bridge.RESERVED_BINDING_NAMES)

        for name in [
            "jump",
            "jumpi",
            "jumpdest",
            "push0",
            "push32",
            "dup1",
            "dup16",
            "swap1",
            "swap16",
        ]:
            with self.subTest(name=name):
                expr = bridge.parse_expr(call(name, []))
                self.assertIsInstance(expr, bridge.Call)
                self.assertEqual(expr.callee_kind, bridge.CALL_DIALECT_BUILTIN)

        user_like_reserved_names = [
            name
            for name in bridge.RESERVED_BINDING_NAMES
            if name != "clz"
            if bridge.classify_call(name) == bridge.CALL_USER
        ]
        self.assertEqual(user_like_reserved_names, [])

    def test_bridge_json_summary_marks_gas_and_msize_executable_ready(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.Let(
                    ["g"],
                    bridge.Call("gas", [], bridge.CALL_PRIMITIVE),
                ),
                bridge.Let(
                    ["m"],
                    bridge.Call("msize", [], bridge.CALL_PRIMITIVE),
                ),
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "ResourceObservers.sol",
            "ResourceObservers",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertEqual(compatibility["dialectBuiltinNames"], [])
        self.assertTrue(
            any("gas() and msize() are covered" in note for note in compatibility["notes"])
        )

    def test_bridge_json_summary_marks_gas_only_executable_ready(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.Let(
                    ["g"],
                    bridge.Call("gas", [], bridge.CALL_PRIMITIVE),
                ),
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "GasObserver.sol",
            "GasObserver",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertTrue(
            any("gas() and msize() are covered" in note for note in compatibility["notes"])
        )

    def test_bridge_json_summary_marks_local_effects_and_code_image_ready(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "sstore",
                        [bridge.Lit(0), bridge.Lit(1)],
                        bridge.CALL_PRIMITIVE,
                    )
                ),
                bridge.ExprStmt(
                    bridge.Call(
                        "log3",
                        [
                            bridge.Lit(0),
                            bridge.Lit(32),
                            bridge.Lit(1),
                            bridge.Lit(2),
                            bridge.Lit(3),
                        ],
                        bridge.CALL_PRIMITIVE,
                    )
                ),
                bridge.ExprStmt(
                    bridge.Call(
                        "codecopy",
                        [bridge.Lit(0), bridge.Lit(0), bridge.Lit(32)],
                        bridge.CALL_PRIMITIVE,
                    )
                ),
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "Boundary.sol",
            "Boundary",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(
            compatibility["unsupportedPrimitiveNames"],
            [],
        )
        self.assertEqual(compatibility["notes"], [])

    def test_bridge_json_manifest_summary_uses_manifest_metadata_without_lean(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "sstore",
                        [bridge.Lit(0), bridge.Lit(1)],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        with tempfile.TemporaryDirectory() as directory:
            bridge_dir = Path(directory)
            bridge.write_bridge_json_output(
                bridge_dir,
                obj,
                "Input.sol",
                "Input",
                "runtime",
                ast_output="irAst",
            )
            args = SimpleNamespace(
                input=bridge.bridge_json_manifest_path(bridge_dir),
                format="bridge-json-summary",
                bridge_json=None,
                bridge_json_dir=None,
                list_objects=False,
                object_layout=[],
                auto_object_layout=False,
                data_base=None,
                linker_symbol=[],
                check=False,
                source_name=None,
                contract=None,
                object="runtime",
                include_source=[],
                remapping=[],
                remappings_file=[],
                auto_include_imports=True,
                solc_arg=[],
                optimized=False,
                via_ir=True,
                experimental=True,
                all_contracts=False,
                lake="/no/such/lake",
                lake_cwd=Path(directory),
            )

            rendered, source, contract, selected = (
                bridge.render_bridge_json_manifest_input_output(args)
            )

        summary = json.loads(rendered)
        self.assertEqual(source, "*")
        self.assertEqual(contract, "*")
        self.assertEqual(selected, "1 manifest object summaries")
        self.assertEqual(
            summary["schema"],
            "evm-compiler.solc-yul-bridge-manifest-summary.v1",
        )
        self.assertEqual(summary["counts"]["objects"], 1)
        self.assertEqual(summary["backendCompatibility"]["status"], "ready")
        self.assertEqual(
            summary["backendCompatibility"]["unsupportedPrimitiveNames"],
            [],
        )
        self.assertEqual(summary["objects"][0]["source"], "Input.sol")
        self.assertEqual(
            summary["objects"][0]["frontend"],
            {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
        )
        self.assertEqual(summary["objects"][0]["calls"]["primitive"]["names"][0]["name"], "sstore")

    def test_bridge_json_input_summary_preserves_frontend_metadata(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "mstore",
                        [bridge.Lit(0), bridge.Lit(1)],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bridge_path = root / "runtime.bridge.json"
            bridge_path.write_text(
                bridge.render_bridge_json(
                    obj,
                    "Optimized.sol",
                    "Optimized",
                    "irOptimizedAst",
                )
            )
            args = SimpleNamespace(
                input=bridge_path,
                format="bridge-json-summary",
                bridge_json=None,
                bridge_json_dir=None,
                list_objects=False,
                object_layout=[],
                auto_object_layout=False,
                data_base=None,
                linker_symbol=[],
                check=False,
                source_name=None,
                contract=None,
                object="runtime",
                include_source=[],
                remapping=[],
                remappings_file=[],
                auto_include_imports=True,
                solc_arg=[],
                optimized=False,
                via_ir=True,
                experimental=True,
                all_contracts=False,
                lake="/no/such/lake",
                lake_cwd=root,
            )

            rendered, source, contract, selected = (
                bridge.render_bridge_json_input_output(args)
            )

        summary = json.loads(rendered)
        self.assertEqual(source, "Optimized.sol")
        self.assertEqual(contract, "Optimized")
        self.assertEqual(selected, "runtime")
        self.assertEqual(
            summary["frontend"],
            {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
        )

    def test_bridge_json_manifest_summary_aggregates_backend_compatibility(self):
        object_builtin_obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "datacopy",
                        [bridge.Lit(0), bridge.StringLit("metadata"), bridge.Lit(1)],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        external_call_obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "call",
                        [
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                            bridge.Lit(0),
                        ],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        manifest_summary = json.loads(
            bridge.render_bridge_json_summary_outputs(
                [
                    bridge.bridge_json_summary_artifact(
                        object_builtin_obj,
                        "Data.sol",
                        "Data",
                        "runtime",
                    ),
                    bridge.bridge_json_summary_artifact(
                        external_call_obj,
                        "Calls.sol",
                        "Calls",
                        "runtime",
                    ),
                ],
                [],
            )
        )

        compatibility = manifest_summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertEqual(compatibility["objectBuiltinNames"], ["datacopy"])

    def test_bridge_json_manifest_summary_records_structured_skipped_entries(self):
        manifest_summary = json.loads(
            bridge.render_bridge_json_summary_outputs(
                [],
                ["Simple.sol:I"],
                [
                    {
                        "source": "Simple.sol",
                        "contract": "I",
                        "reason": "no-yul-ir",
                    }
                ],
            )
        )

        self.assertEqual(manifest_summary["counts"]["skippedContracts"], 1)
        self.assertEqual(manifest_summary["skippedContracts"], ["Simple.sol:I"])
        self.assertEqual(
            manifest_summary["skippedContractEntries"],
            [
                {
                    "source": "Simple.sol",
                    "contract": "I",
                    "reason": "no-yul-ir",
                }
            ],
        )

    def test_lean_ir_module_preserves_data_sections_as_structures(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[
                bridge.DataSection(None, [0xaa]),
                bridge.DataSection("named_data", [0xbb, 0xcc]),
            ],
            subobjects=[
                bridge.YulObject(
                    name="child",
                    dispatcher=[],
                    functions=[],
                    data=[bridge.DataSection("child_data", [0xdd])],
                    subobjects=[],
                )
            ],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
        )
        self.assertIn("EvmCompiler.Solidity.Frontend.DataSection.mk none", rendered)
        self.assertIn("UInt8.ofNat 170", rendered)
        self.assertIn(
            'EvmCompiler.Solidity.Frontend.DataSection.mk (some "named_data")',
            rendered,
        )
        self.assertIn(
            'EvmCompiler.Solidity.Frontend.DataSection.mk (some "child_data")',
            rendered,
        )
        self.assertIn(
            "noncomputable def programToObjects : Option EvmCompiler.Objects.Program",
            rendered,
        )
        self.assertIn(
            "def programArtifactTarget : "
            "Option EvmCompiler.Assembly.TargetProgram",
            rendered,
        )
        self.assertIn("program.compileArtifact?", rendered)
        self.assertIn("def programArtifactBytecode : Option ByteArray", rendered)
        self.assertIn("artifact.codeArtifact.compiled.target", rendered)
        self.assertIn("artifact.codeArtifact.bytes", rendered)
        self.assertIn(
            "def programArtifactBytecodeImage : Option ByteArray",
            rendered,
        )
        self.assertIn(
            "def programArtifactObjectImage : "
            "Option EvmCompiler.Solidity.Frontend.ObjectImage",
            rendered,
        )
        self.assertIn("program.compileImage?", rendered)
        self.assertIn("def programVerifiedArtifact", rendered)
        self.assertIn(
            "noncomputable def programCheckedBytecodeImage : Option ByteArray",
            rendered,
        )
        self.assertIn(
            "noncomputable def programCheckedObjectImage",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Solidity.Frontend.ObjectImage", rendered)
        self.assertIn(
            "def programLinkerSymbols :",
            rendered,
        )
        self.assertIn(
            "def programArtifactObjectImageWithLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "def programArtifactBytecodeImageWithLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "program.compileImageWithLinkerSymbols? programLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "def programVerifiedArtifactWithLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "noncomputable def programCheckedObjectImageWithLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "noncomputable def programCheckedBytecodeImageWithLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "def programResolvedObjectData :",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Solidity.Frontend.Program", rendered)
        self.assertIn(
            "EvmCompiler.Solidity.Frontend.Object.resolveObjectBuiltinsIn?",
            rendered,
        )
        self.assertIn(
            "def programToYulWithComputedObjectData :",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Yul.Program", rendered)
        self.assertIn(
            "resolved.toYulProgram?",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToObjectsWithComputedObjectData :",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Objects.Program", rendered)
        self.assertIn(
            "resolved.toObjects?",
            rendered,
        )
        self.assertIn(
            "noncomputable def programCompileArtifactWithComputedObjectData :",
            rendered,
        )
        self.assertIn(
            "Option EvmCompiler.Solidity.Frontend.Program.Artifact", rendered
        )
        self.assertIn(
            "programVerifiedArtifactWithLinkerSymbols",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToObjectsWithLayout",
            rendered,
        )
        self.assertIn(
            "def programArtifactTargetWithLayout : "
            "Option EvmCompiler.Assembly.TargetProgram",
            rendered,
        )
        self.assertIn("programVerifiedCodeArtifactAt 0", rendered)
        self.assertIn(
            "def programArtifactBytecodeWithLayout : Option ByteArray",
            rendered,
        )
        self.assertIn("def programVerifiedCodeArtifactAt (base : Nat)", rendered)
        self.assertIn("program.toObjectsWithLayout? objectLayout", rendered)

    def test_backend_yul_module_emits_checked_backend_artifacts(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        rendered = bridge.render_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
        )
        self.assertIn(
            "noncomputable def programCompileArtifact :",
            rendered,
        )
        self.assertIn(
            "Option EvmCompiler.Yul.Program.CompileArtifact", rendered
        )
        self.assertIn("EvmCompiler.Yul.Program.compileArtifact? program", rendered)
        self.assertIn(
            "noncomputable def programTarget : "
            "Option EvmCompiler.Assembly.TargetProgram",
            rendered,
        )
        self.assertIn("some compiled.target", rendered)
        self.assertIn("noncomputable def programBytecode : Option ByteArray", rendered)
        self.assertIn("EvmCompiler.Assembly.Bytecode.encodeTarget target", rendered)

    def test_lean_ir_module_preserves_object_builtin_shape(self):
        obj = bridge.YulObject(
            name="creation",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "datasize",
                        [bridge.StringLit("runtime")],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
        )
        self.assertIn("EvmCompiler.Solidity.Frontend.Expr.stringLit", rendered)
        self.assertIn("EvmCompiler.Solidity.Frontend.CallKind.objectBuiltin", rendered)
        self.assertIn("def programToYul : Option EvmCompiler.Yul.Program", rendered)
        self.assertIn(
            "noncomputable def programToYulCompileArtifact :",
            rendered,
        )
        self.assertIn(
            "Option EvmCompiler.Yul.Program.CompileArtifact", rendered
        )
        self.assertIn("let yul ← programToYul", rendered)
        self.assertIn("EvmCompiler.Yul.Program.compileArtifact? yul", rendered)
        self.assertIn(
            "noncomputable def programToYulTarget : "
            "Option EvmCompiler.Assembly.TargetProgram",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToYulBytecode : Option ByteArray",
            rendered,
        )

    def test_lean_ir_module_always_emits_layout_conversion(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "datasize",
                        [bridge.StringLit("metadata")],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                )
            ],
            functions=[],
            data=[bridge.DataSection("metadata", [0xaa, 0xbb, 0xcc])],
            subobjects=[],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
        )
        self.assertIn("def objectLayout : EvmCompiler.Solidity.Frontend.ObjectLayout", rendered)
        self.assertIn("EvmCompiler.Solidity.Frontend.ObjectLayout.mk []", rendered)
        self.assertIn("def programToYulWithLayout : Option EvmCompiler.Yul.Program", rendered)
        self.assertIn(
            "noncomputable def programToYulWithLayoutCompileArtifact",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToYulWithLayoutTarget",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToYulWithLayoutBytecode",
            rendered,
        )

    def test_lean_ir_module_can_emit_local_data_base_conversion(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "dataoffset",
                        [bridge.StringLit("metadata")],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                )
            ],
            functions=[],
            data=[
                bridge.DataSection(None, [0xaa, 0xbb]),
                bridge.DataSection("metadata", [0xcc]),
            ],
            subobjects=[],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
            local_data_base=32,
        )
        self.assertIn("def localDataBase : Nat", rendered)
        self.assertIn("32", rendered)
        self.assertIn(
            "def programToYulWithLocalDataBase : Option EvmCompiler.Yul.Program",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToObjectsWithLocalDataBase",
            rendered,
        )
        self.assertIn(
            "program.toYulProgramWithLocalDataBase? objectLayout localDataBase",
            rendered,
        )
        self.assertIn(
            "program.toObjectsWithLocalDataBase? objectLayout localDataBase",
            rendered,
        )
        self.assertIn(
            "def programArtifactTargetWithLocalDataBase : "
            "Option EvmCompiler.Assembly.TargetProgram",
            rendered,
        )
        self.assertIn(
            "programVerifiedCodeArtifactAt localDataBase",
            rendered,
        )
        self.assertIn(
            "def programArtifactBytecodeWithLocalDataBase : Option ByteArray",
            rendered,
        )
        self.assertIn(
            "EvmCompiler.Assembly.Bytecode.ofList artifact.bytes",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToYulWithLocalDataBaseCompileArtifact",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToYulWithLocalDataBaseTarget",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToYulWithLocalDataBaseBytecode",
            rendered,
        )

    def test_lean_ir_module_can_emit_explicit_object_layout(self):
        obj = bridge.YulObject(
            name="creation",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "datasize",
                        [bridge.StringLit("runtime")],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
            [bridge.ObjectLayoutEntry("runtime", 43, 418)],
        )
        self.assertIn("EvmCompiler.Solidity.Frontend.ObjectLayout.Entry.mk", rendered)
        self.assertIn("EvmYul.UInt256.ofNat 43", rendered)
        self.assertIn("def programToYulWithLayout : Option EvmCompiler.Yul.Program", rendered)

    def test_lean_ir_module_can_emit_linker_symbol_values(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.Let(
                    ["lib"],
                    bridge.Call(
                        "linkersymbol",
                        [bridge.StringLit("MathLib.sol:MathLib")],
                        bridge.CALL_OBJECT_BUILTIN,
                    ),
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "UsesLibrary.sol",
            "UsesLibrary",
            "program",
            "Generated.UsesLibrary",
            linker_symbols=[
                bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)
            ],
        )
        self.assertIn(
            '("MathLib.sol:MathLib", EvmYul.UInt256.ofNat 42)',
            rendered,
        )
        self.assertIn(
            "program.compileArtifactWithLinkerSymbols? programLinkerSymbols",
            rendered,
        )

    def test_bridge_json_summary_marks_linker_symbols_needing_resolution(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.Let(
                    ["lib"],
                    bridge.Call(
                        "linkersymbol",
                        [bridge.StringLit("MathLib.sol:MathLib")],
                        bridge.CALL_OBJECT_BUILTIN,
                    ),
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )

        summary = bridge.bridge_json_summary_artifact(
            obj,
            "UsesLibrary.sol",
            "UsesLibrary",
            "runtime",
        )

        compatibility = summary["backendCompatibility"]
        self.assertEqual(compatibility["status"], "needs-resolution")
        self.assertEqual(compatibility["objectBuiltinNames"], ["linkersymbol"])
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertIn("linkersymbol object builtin", " ".join(compatibility["notes"]))
        self.assertIn(
            "linker-symbols-present",
            "\n".join(summary["backendHints"]),
        )

    def test_lean_json_ir_module_embeds_bridge_json_decoder(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.Let(["x"], bridge.Lit(1)),
                bridge.ExprStmt(
                    bridge.Call("stop", [], bridge.CALL_PRIMITIVE)
                ),
            ],
            functions=[],
            data=[bridge.DataSection("metadata", [0xaa])],
            subobjects=[],
            items=[bridge.ObjectItemRef("data", 0)],
        )
        rendered = bridge.render_frontend_json_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
        )

        self.assertIn("import EvmCompiler.Solidity.BridgeJson", rendered)
        self.assertIn("def programJson : String", rendered)
        self.assertIn("evm-compiler.solc-yul-bridge.v3", rendered)
        self.assertIn(
            "EvmCompiler.Solidity.Frontend.BridgeJson.parseProgram? programJson",
            rendered,
        )
        self.assertIn(
            "def program : Option EvmCompiler.Solidity.Frontend.Program",
            rendered,
        )
        self.assertIn("let program ← program", rendered)
        self.assertIn("def programVerifiedArtifact", rendered)
        self.assertIn("program.compileImage?", rendered)
        self.assertIn(
            "def programResolvedObjectData :",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Solidity.Frontend.Program", rendered)
        self.assertIn(
            "EvmCompiler.Solidity.Frontend.Object.resolveObjectBuiltinsIn?",
            rendered,
        )
        self.assertIn(
            "def programToYulWithComputedObjectData :",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Yul.Program", rendered)
        self.assertIn(
            "resolved.toYulProgram?",
            rendered,
        )
        self.assertIn(
            "noncomputable def programToObjectsWithComputedObjectData :",
            rendered,
        )
        self.assertIn("Option EvmCompiler.Objects.Program", rendered)
        self.assertIn(
            "resolved.toObjects?",
            rendered,
        )
        self.assertIn(
            "noncomputable def programCompileArtifactWithComputedObjectData :",
            rendered,
        )
        self.assertIn(
            "Option EvmCompiler.Solidity.Frontend.Program.Artifact", rendered
        )
        self.assertIn(
            "programVerifiedArtifactWithLinkerSymbols",
            rendered,
        )

    def test_lean_ir_module_preserves_datacopy_until_layout_resolution(self):
        obj = bridge.YulObject(
            name="creation",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "datacopy",
                        [
                            bridge.Lit(0),
                            bridge.Call(
                                "dataoffset",
                                [bridge.StringLit("runtime")],
                                bridge.CALL_OBJECT_BUILTIN,
                            ),
                            bridge.Call(
                                "datasize",
                                [bridge.StringLit("runtime")],
                                bridge.CALL_OBJECT_BUILTIN,
                            ),
                        ],
                        bridge.CALL_OBJECT_BUILTIN,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        rendered = bridge.render_frontend_module(
            obj,
            "Simple.sol",
            "Simple",
            "program",
            "Generated.Simple",
            [bridge.ObjectLayoutEntry("runtime", 43, 418)],
        )
        self.assertIn('"datacopy"', rendered)
        self.assertIn('"dataoffset"', rendered)
        self.assertIn('"datasize"', rendered)
        self.assertIn("EvmCompiler.Solidity.Frontend.CallKind.objectBuiltin", rendered)

    def test_standard_json_requests_bytecode_for_auto_layout(self):
        request = bridge.standard_json_input(
            "Simple.sol",
            "contract Simple {}",
            via_ir=True,
            optimized=False,
            experimental=True,
        )
        selected = request["settings"]["outputSelection"]["*"]["*"]
        self.assertIn("irAst", selected)
        self.assertIn("ir", selected)
        self.assertIn("abi", selected)
        self.assertIn("metadata", selected)
        self.assertIn("evm.bytecode.object", selected)
        self.assertIn("evm.deployedBytecode.object", selected)
        self.assertIn("evm.methodIdentifiers", selected)

    def test_standard_json_input_mode_preserves_solc_shape_and_adds_outputs(self):
        request = {
            "language": "Solidity",
            "sources": {"A.sol": {"content": "contract A {}"}},
            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
        }
        augmented = bridge.ensure_standard_json_frontend_outputs(
            request,
            optimized=True,
            default_via_ir=True,
            default_experimental=True,
        )
        selected = augmented["settings"]["outputSelection"]["*"]["*"]
        self.assertIn("abi", selected)
        self.assertIn("irOptimizedAst", selected)
        self.assertIn("irOptimized", selected)
        self.assertIn("evm.bytecode.object", selected)
        self.assertTrue(augmented["settings"]["viaIR"])
        self.assertTrue(augmented["settings"]["experimental"])
        self.assertEqual(augmented["settings"]["evmVersion"], "cancun")

    def test_standard_json_rejects_an_unsupported_evm_version(self):
        request = {
            "language": "Solidity",
            "sources": {"A.sol": {"content": "contract A {}"}},
            "settings": {
                "evmVersion": "@future",
                "outputSelection": {"*": {"*": []}},
            },
        }
        with self.assertRaisesRegex(bridge.ConversionError, "evmVersion"):
            bridge.ensure_standard_json_frontend_outputs(
                request,
                optimized=True,
                default_via_ir=True,
                default_experimental=True,
            )

    def test_standard_json_preserves_supported_post_cancun_evm_versions(self):
        for evm_version in ("prague", "osaka"):
            with self.subTest(evm_version=evm_version):
                request = {
                    "language": "Solidity",
                    "sources": {"A.sol": {"content": "contract A {}"}},
                    "settings": {
                        "evmVersion": evm_version,
                        "outputSelection": {"*": {"*": []}},
                    },
                }
                augmented = bridge.ensure_standard_json_frontend_outputs(
                    request,
                    optimized=True,
                    default_via_ir=True,
                    default_experimental=True,
                )
                self.assertEqual(augmented["settings"]["evmVersion"], evm_version)

    def test_standard_json_rejects_post_cancun_family_aliases_for_solc(self):
        for evm_version in ("pectra", "fusaka"):
            with self.subTest(evm_version=evm_version):
                request = {
                    "language": "Solidity",
                    "sources": {"A.sol": {"content": "contract A {}"}},
                    "settings": {
                        "evmVersion": evm_version,
                        "outputSelection": {"*": {"*": []}},
                    },
                }
                with self.assertRaisesRegex(bridge.ConversionError, "evmVersion"):
                    bridge.ensure_standard_json_frontend_outputs(
                        request,
                        optimized=True,
                        default_via_ir=True,
                        default_experimental=True,
                    )

    def test_standard_json_preserves_a_supported_older_evm_version(self):
        request = {
            "language": "Solidity",
            "sources": {"A.sol": {"content": "contract A {}"}},
            "settings": {
                "evmVersion": "london",
                "outputSelection": {"*": {"*": []}},
            },
        }
        augmented = bridge.ensure_standard_json_frontend_outputs(
            request,
            optimized=True,
            default_via_ir=True,
            default_experimental=True,
        )
        self.assertEqual(augmented["settings"]["evmVersion"], "london")

    def test_bridge_only_standard_json_requests_yul_without_solc_bytecode(self):
        request = {
            "language": "Solidity",
            "sources": {"A.sol": {"content": "contract A {}"}},
            "settings": {"outputSelection": {"*": {"*": []}}},
        }
        augmented = bridge.ensure_standard_json_frontend_outputs(
            request,
            optimized=True,
            default_via_ir=True,
            default_experimental=True,
            require_bytecode=False,
        )
        selected = augmented["settings"]["outputSelection"]["*"]["*"]
        self.assertEqual(selected, ["irOptimizedAst", "irOptimized"])

    def test_recovers_missing_contract_ast_from_exact_solc_yul_text(self):
        yul_text = 'object "A_1" { code { } }'
        raw_ast = {
            "nodeType": "YulObject",
            "name": "A_1",
            "code": {"block": {"statements": []}},
            "subObjects": [],
        }
        contract_output = {"irOptimized": yul_text}
        output = {"contracts": {"A.sol": {"A": contract_output}}}
        captured = []
        old_run_solc = bridge.run_solc
        bridge.RECOVERED_YUL_AST_OUTPUTS.clear()
        try:
            def fake_run_solc(solc, compiler_input, solc_args=()):
                captured.append((solc, compiler_input, tuple(solc_args)))
                source_name = next(iter(compiler_input["sources"]))
                return {"sources": {source_name: {"ast": raw_ast}}}

            bridge.run_solc = fake_run_solc
            recovered = bridge.recover_missing_contract_yul_asts(
                output,
                "A.sol",
                "A",
                optimized=True,
                experimental=True,
                solc="solc-0.8.17",
                solc_args=("--base-path", "."),
            )
        finally:
            bridge.run_solc = old_run_solc

        self.assertEqual(recovered, 1)
        self.assertIs(contract_output["irOptimizedAst"], raw_ast)
        self.assertEqual(
            bridge.contract_frontend_ast_output("A.sol", "A", True),
            "yulAst",
        )
        self.assertEqual(captured[0][0], "solc-0.8.17")
        self.assertEqual(captured[0][1]["language"], "Yul")
        self.assertEqual(
            next(iter(captured[0][1]["sources"].values()))["content"],
            yul_text,
        )
        self.assertEqual(captured[0][2], ("--base-path", "."))

    def test_ast_recovery_skips_empty_abstract_contract_ir(self):
        abstract_output = {"irOptimized": "  \n"}
        concrete_output = {
            "irOptimizedAst": {
                "nodeType": "YulObject",
                "name": "Concrete_1",
            }
        }
        output = {
            "contracts": {
                "A.sol": {
                    "Abstract": abstract_output,
                    "Concrete": concrete_output,
                }
            }
        }
        old_run_solc = bridge.run_solc
        try:
            def unexpected_run_solc(*_args, **_kwargs):
                raise AssertionError("empty abstract IR must not be reparsed")

            bridge.run_solc = unexpected_run_solc
            recovered = bridge.recover_missing_contract_yul_asts(
                output,
                "A.sol",
                None,
                optimized=True,
                experimental=True,
                solc="solc",
                solc_args=(),
            )
        finally:
            bridge.run_solc = old_run_solc

        self.assertEqual(recovered, 0)
        self.assertNotIn("irOptimizedAst", abstract_output)
        self.assertEqual(
            bridge.yul_ir_contract_candidates(output, "A.sol", True),
            [("A.sol", "Concrete", concrete_output)],
        )

    def test_run_solc_retries_without_experimental_for_older_solc(self):
        calls = []

        def fake_run(cmd, input, text, stdout, stderr, check):
            calls.append(json.loads(input))
            if len(calls) == 1:
                return bridge.subprocess.CompletedProcess(
                    cmd,
                    0,
                    stdout=json.dumps(
                        {
                            "errors": [
                                {
                                    "severity": "error",
                                    "message": 'Unknown key "experimental"',
                                }
                            ]
                        }
                    ),
                    stderr="",
                )
            return bridge.subprocess.CompletedProcess(
                cmd,
                0,
                stdout=json.dumps({"contracts": {}}),
                stderr="",
            )

        old_run = bridge.subprocess.run
        try:
            bridge.subprocess.run = fake_run
            output = bridge.run_solc(
                "solc",
                {
                    "language": "Solidity",
                    "sources": {},
                    "settings": {"experimental": True, "viaIR": True},
                },
            )
        finally:
            bridge.subprocess.run = old_run

        self.assertEqual(output, {"contracts": {}})
        self.assertTrue(calls[0]["settings"]["experimental"])
        self.assertNotIn("experimental", calls[1]["settings"])
        self.assertTrue(calls[1]["settings"]["viaIR"])

    def test_read_standard_json_input_accepts_stdin(self):
        old_stdin = sys.stdin
        try:
            sys.stdin = io.StringIO('{"language":"Solidity","sources":{}}')
            parsed = bridge.read_standard_json_input(Path("-"))
        finally:
            sys.stdin = old_stdin
        self.assertEqual(parsed["language"], "Solidity")

    def test_choose_contract_can_select_unique_contract_without_source_name(self):
        output = {
            "contracts": {
                "A.sol": {"A": {"abi": []}},
                "B.sol": {"B": {"abi": []}},
            }
        }
        self.assertEqual(
            bridge.choose_contract(output, None, "B"),
            ("B.sol", "B", {"abi": []}),
        )
        with self.assertRaises(bridge.ConversionError):
            bridge.choose_contract(output, None, None)

    def test_contract_candidates_can_filter_by_source_for_all_contracts(self):
        output = {
            "contracts": {
                "A.sol": {"A": {"abi": []}},
                "B.sol": {"B": {"abi": []}, "C": {"abi": []}},
            }
        }
        self.assertEqual(
            bridge.contract_candidates(output, "B.sol", None),
            [
                ("B.sol", "B", {"abi": []}),
                ("B.sol", "C", {"abi": []}),
            ],
        )
        self.assertEqual(
            bridge.contract_candidates(output, None, "A"),
            [("A.sol", "A", {"abi": []})],
        )

    def test_lean_bytecode_candidates_skip_non_deployable_contract_outputs(self):
        deployable = {
            "irAst": {"nodeType": "YulObject", "name": "Impl"},
            "evm": {
                "bytecode": {"object": "60"},
                "deployedBytecode": {"object": "00"},
            },
        }
        interface = {
            "abi": [],
            "evm": {
                "bytecode": {"object": ""},
                "deployedBytecode": {"object": ""},
            },
        }
        abstract = {
            "irAst": {"nodeType": "YulObject", "name": "Base"},
            "evm": {
                "bytecode": {"object": ""},
                "deployedBytecode": {"object": ""},
            },
        }
        output = {
            "contracts": {
                "InterfaceCase.sol": {
                    "IFace": interface,
                    "Base": abstract,
                    "Impl": deployable,
                }
            }
        }

        self.assertTrue(
            bridge.has_lean_bytecode_artifact_inputs(deployable, optimized=False)
        )
        self.assertFalse(
            bridge.has_lean_bytecode_artifact_inputs(interface, optimized=False)
        )
        self.assertFalse(
            bridge.has_lean_bytecode_artifact_inputs(abstract, optimized=False)
        )
        self.assertEqual(
            bridge.lean_bytecode_contract_candidates(
                output,
                "InterfaceCase.sol",
                optimized=False,
            ),
            [("InterfaceCase.sol", "Impl", deployable)],
        )
        self.assertEqual(
            bridge.yul_ir_contract_candidates(
                output,
                "InterfaceCase.sol",
                optimized=False,
            ),
            [
                ("InterfaceCase.sol", "Base", abstract),
                ("InterfaceCase.sol", "Impl", deployable),
            ],
        )

    def test_render_lean_json_check_outputs_records_checked_and_skipped(self):
        rendered = bridge.render_lean_json_check_outputs(
            [
                bridge.LeanJsonCheckArtifact(
                    source_name="A.sol",
                    contract_name="A",
                    object_selector="creation",
                    object_name="A_1",
                    summary={
                        "source": "A.sol",
                        "contract": "A",
                        "object": "A_1",
                        "dispatcher_stmts": 2,
                        "functions": 3,
                        "data_sections": 1,
                        "subobjects": 0,
                        "items": 1,
                    },
                    frontend={"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                )
            ],
            ["A.sol:I"],
        )
        parsed = json.loads(rendered)
        self.assertEqual(parsed["schema"], "evm-compiler.lean-json-check.v2")
        self.assertEqual(
            parsed["counts"],
            {
                "checkedObjects": 1,
                "checkedContracts": 1,
                "skippedContracts": 1,
            },
        )
        self.assertEqual(parsed["checkedObjects"][0]["selector"], "creation")
        self.assertEqual(parsed["checkedObjects"][0]["object"], "A_1")
        self.assertEqual(parsed["checkedObjects"][0]["functions"], 3)
        self.assertEqual(
            parsed["checkedObjects"][0]["frontend"],
            {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
        )
        self.assertEqual(parsed["checkedContracts"], ["A.sol:A"])
        self.assertEqual(parsed["skippedContracts"], ["A.sol:I"])

    def test_render_lean_backend_check_outputs_records_stage_failures(self):
        rendered = bridge.render_lean_backend_check_outputs(
            [
                bridge.LeanBackendCheckArtifact(
                    source_name="A.sol",
                    contract_name="A",
                    object_selector="runtime",
                    object_name="A_1_deployed",
                    summary={
                        "source": "A.sol",
                        "contract": "A",
                        "object": "A_1_deployed",
                        "status": "fail",
                        "first_none": "functions_compile",
                        "stages": {
                            "to_yul_contract": "some",
                            "functions_compile": "none",
                            "object_image": "none",
                        },
                        "timingsMs": {"decode": 3},
                        "localsProcs": {"main": "none"},
                        "localsStmtTrace": [
                            {
                                "owner": "main",
                                "index": 2,
                                "kind": "expr",
                                "status": "none",
                            }
                        ],
                        "localsLayouts": [
                            {
                                "owner": "main",
                                "index": 2,
                                "length": 17,
                                "layout": "[deep]",
                            }
                        ],
                        "localsVars": [
                            {
                                "owner": "main",
                                "index": 2,
                                "name": "deep",
                                "depth": "17",
                            }
                        ],
                        "localsTargets": [
                            {
                                "owner": "main",
                                "index": 2,
                                "name": "target",
                                "depth": "18",
                                "accessDepth": "18",
                            }
                        ],
                    },
                    frontend={"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                ),
                bridge.LeanBackendCheckArtifact(
                    source_name="B.sol",
                    contract_name="B",
                    object_selector="runtime",
                    object_name="B_1_deployed",
                    summary={
                        "source": "B.sol",
                        "contract": "B",
                        "object": "B_1_deployed",
                        "status": "pass",
                        "first_none": "none",
                        "stages": {"object_image": "some"},
                        "bytecode_bytes": 12,
                    },
                    frontend={"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
                ),
            ],
            ["I.sol:I"],
        )
        parsed = json.loads(rendered)
        self.assertEqual(parsed["schema"], "evm-compiler.lean-backend-check.v1")
        self.assertEqual(parsed["counts"]["checkedObjects"], 2)
        self.assertEqual(parsed["counts"]["passedObjects"], 1)
        self.assertEqual(parsed["counts"]["failedObjects"], 1)
        self.assertEqual(parsed["firstNoneCounts"], {"functions_compile": 1})
        self.assertEqual(parsed["checkedObjects"][0]["firstNone"], "functions_compile")
        self.assertEqual(
            [item["frontend"]["ast"] for item in parsed["checkedObjects"]],
            ["irAst", "irOptimizedAst"],
        )
        self.assertEqual(parsed["checkedObjects"][0]["timingsMs"]["decode"], 3)
        self.assertEqual(parsed["checkedObjects"][0]["localsProcs"], {"main": "none"})
        self.assertEqual(
            parsed["checkedObjects"][0]["localsStmtTrace"][0]["kind"], "expr"
        )
        self.assertEqual(parsed["checkedObjects"][0]["localsLayouts"][0]["length"], 17)
        self.assertEqual(parsed["checkedObjects"][0]["localsVars"][0]["depth"], "17")
        self.assertEqual(
            parsed["checkedObjects"][0]["localsTargets"][0]["accessDepth"], "18"
        )
        self.assertNotIn("timingsMs", parsed["checkedObjects"][1])
        self.assertEqual(parsed["checkedObjects"][1]["bytecodeBytes"], 12)

    def test_auto_object_layout_finds_deployed_bytecode(self):
        root = bridge.YulObject(
            name="Simple_14",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[
                bridge.YulObject(
                    name="Simple_14_deployed",
                    dispatcher=[],
                    functions=[],
                    data=[],
                    subobjects=[],
                )
            ],
        )
        contract_output = {
            "evm": {
                "bytecode": {"object": "60016002036004"},
                "deployedBytecode": {"object": "600203"},
            }
        }
        inferred = bridge.infer_object_layout(root, contract_output)
        self.assertEqual(inferred, [bridge.ObjectLayoutEntry("Simple_14_deployed", 2, 3)])

    def test_explicit_object_layout_overrides_auto_entry(self):
        explicit = [bridge.ObjectLayoutEntry("runtime", 99, 100)]
        inferred = [
            bridge.ObjectLayoutEntry("runtime", 43, 418),
            bridge.ObjectLayoutEntry("other", 1, 2),
        ]
        merged = bridge.merge_layout_entries(explicit, inferred)
        self.assertEqual(
            merged,
            [
                bridge.ObjectLayoutEntry("runtime", 99, 100),
                bridge.ObjectLayoutEntry("other", 1, 2),
            ],
        )

    def test_bytecode_format_selects_most_resolved_definition(self):
        self.assertEqual(
            bridge.bytecode_definition_name("program", [], None),
            "programArtifactBytecodeImage",
        )
        self.assertEqual(
            bridge.bytecode_definition_name(
                "program",
                [bridge.ObjectLayoutEntry("runtime", 43, 418)],
                None,
            ),
            "programArtifactBytecodeImage",
        )
        self.assertEqual(
            bridge.bytecode_definition_name("program", [], 32),
            "programArtifactBytecodeImage",
        )
        self.assertEqual(
            bridge.bytecode_definition_name(
                "program",
                [],
                None,
                [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 0)],
            ),
            "programArtifactBytecodeImageWithLinkerSymbols",
        )

    def test_legacy_bytecode_definition_tracks_layout_witnesses(self):
        self.assertEqual(
            bridge.legacy_bytecode_definition_name("program", [], None),
            "programArtifactBytecode",
        )
        self.assertEqual(
            bridge.legacy_bytecode_definition_name(
                "program",
                [bridge.ObjectLayoutEntry("runtime", 43, 418)],
                None,
            ),
            "programArtifactBytecodeWithLayout",
        )
        self.assertEqual(
            bridge.legacy_bytecode_definition_name("program", [], 32),
            "programArtifactBytecodeWithLocalDataBase",
        )

    def test_bytecode_runner_prints_hex_from_selected_definition(self):
        rendered = bridge.render_bytecode_runner(
            "Generated.Simple.programArtifactBytecodeWithLayout"
        )
        self.assertIn(
            "match Generated.Simple.programArtifactBytecodeWithLayout with",
            rendered,
        )
        self.assertIn(
            'IO.println ("0x" ++ evmCompilerRunnerBytesHex bytes)',
            rendered,
        )
        self.assertIn('IO.println "none"', rendered)

    def test_compile_frontend_object_bytecode_runs_image_definition(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        calls = []
        bridge_json_paths = []
        old_run_lake_object_image = bridge.run_lake_native_object_image
        try:
            def fake_run_lake_object_image(lake, json_path, cwd, linker_symbols):
                calls.append((lake, json_path, cwd, linker_symbols))
                self.assertTrue(json_path.exists())
                bridge_json_paths.append(json_path)
                rendered_json = json.loads(json_path.read_text())
                self.assertEqual(
                    rendered_json["schema"],
                    "evm-compiler.solc-yul-bridge.v3",
                )
                self.assertEqual(rendered_json["selectedObject"]["name"], "runtime")
                return bridge.CompiledObjectImage("0x00")

            bridge.run_lake_native_object_image = fake_run_lake_object_image
            bytecode = bridge.compile_frontend_object_bytecode(
                obj,
                "Simple.sol",
                "Simple",
                "programCreation",
                "Generated.Artifact",
                [],
                None,
                [],
                "lake",
                Path("/tmp/project"),
            )
        finally:
            bridge.run_lake_native_object_image = old_run_lake_object_image

        self.assertEqual(bytecode, "0x00")
        self.assertEqual(calls[0][0], "lake")
        self.assertEqual(calls[0][2], Path("/tmp/project"))
        self.assertFalse(bridge_json_paths[0].exists())
        self.assertEqual(calls[0][3], [])

    def test_compile_frontend_object_image_adds_backend_diagnostic_on_none(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_run_lake_object_image = bridge.run_lake_native_object_image
        old_run_lake_backend_check = bridge.run_lake_backend_check
        try:
            def fake_run_lake_object_image(lake, json_path, cwd, linker_symbols):
                raise bridge.ConversionError(
                    "verified object-image generation returned none; "
                    "the selected object likely needs object layout/data-base "
                    "resolution or uses unsupported Yul"
                )

            def fake_run_lake_backend_check(lake, source, cwd):
                self.assertIn("functions_compile", source)
                return (
                    "lean_backend_check=fail\n"
                    "source=Simple.sol\n"
                    "contract=Simple\n"
                    "object=runtime\n"
                    "stage\tto_yul_contract\tsome\n"
                    "stage\tfunctions_compile\tnone\n"
                    "stage\tobject_image\tnone\n"
                    "first_none=functions_compile\n"
                )

            bridge.run_lake_native_object_image = fake_run_lake_object_image
            bridge.run_lake_backend_check = fake_run_lake_backend_check
            with self.assertRaises(bridge.ConversionError) as raised:
                bridge.compile_frontend_object_image(
                    obj,
                    "Simple.sol",
                    "Simple",
                    "programCreation",
                    "Generated.Artifact",
                    [],
                    None,
                    [],
                    "lake",
                    Path("/tmp/project"),
                )
        finally:
            bridge.run_lake_native_object_image = old_run_lake_object_image
            bridge.run_lake_backend_check = old_run_lake_backend_check

        message = str(raised.exception)
        self.assertIn("Lean backend handoff diagnostic", message)
        self.assertIn("first_none=functions_compile", message)

    def test_render_json_file_decode_runner_reports_object_shape(self):
        rendered = bridge.render_json_file_decode_runner(
            Path("/tmp/runtime.bridge.json")
        )
        self.assertIn("IO.FS.readFile evmCompilerRunnerBridgeJsonPath", rendered)
        self.assertIn("BridgeJson.parseProgram? input", rendered)
        self.assertIn('IO.println "lean_bridge_json_decode=pass"', rendered)
        self.assertIn('IO.println ("object=" ++ object.name)', rendered)
        self.assertNotIn("bytecodeImageUnchecked", rendered)

    def test_render_json_file_backend_check_runner_reports_stages(self):
        rendered = bridge.render_json_file_backend_check_runner(
            Path("/tmp/runtime.bridge.json"),
            [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)],
        )

        self.assertIn("IO.FS.readFile evmCompilerRunnerBridgeJsonPath", rendered)
        self.assertIn("BridgeJson.parseProgram? input", rendered)
        self.assertIn("compileVerifiedStackObjectArtifactWithLinkerSymbols?", rendered)
        self.assertNotIn("bytecodeImageUnchecked", rendered)
        self.assertIn('"functions_compile"', rendered)
        self.assertIn('"payload_items"', rendered)
        self.assertIn('"data_sizes"', rendered)
        self.assertIn('"placeholder_code"', rendered)
        self.assertIn('"computed_object_data"', rendered)
        self.assertIn('"resolved_object_data"', rendered)
        self.assertIn('"solc_validation"', rendered)
        self.assertIn('"object_image"', rendered)
        self.assertNotIn('"checked_computed_object_data"', rendered)
        self.assertNotIn('"checked_object_image"', rendered)
        self.assertNotIn("Functions.LiveLayout", rendered)
        self.assertNotIn("Functions.CallAwareSpill", rendered)
        self.assertNotIn("Functions.ScratchFrameSpill", rendered)
        self.assertNotIn('"live_layout_', rendered)
        self.assertNotIn('"call_aware_', rendered)
        self.assertNotIn('"adaptive_spill', rendered)
        self.assertNotIn('"scratch_frame_spill', rendered)
        self.assertIn('"lean_backend_check="', rendered)
        self.assertIn('("MathLib.sol:MathLib", EvmYul.UInt256.ofNat 42)', rendered)

    def test_parse_backend_check_output_records_first_none(self):
        parsed = bridge.parse_backend_check_output(
            "timing\tdecode\t3\n"
            "lean_backend_check=fail\n"
            "source=Simple.sol\n"
            "contract=Simple\n"
            "object=Simple_1_deployed\n"
            "stage\tto_yul_contract\tsome\n"
            "stage\tlower_code_unchecked\tsome\n"
            "stage\tfunctions_compile\tnone\n"
            "stage\tobject_image\tnone\n"
            "first_none=functions_compile\n"
        )

        self.assertEqual(parsed["status"], "fail")
        self.assertEqual(parsed["first_none"], "functions_compile")
        self.assertEqual(parsed["stages"]["functions_compile"], "none")
        self.assertEqual(parsed["stages"]["object_image"], "none")
        self.assertEqual(parsed["timingsMs"]["decode"], 3)

    def test_parse_backend_check_output_accepts_object_image_success(self):
        parsed = bridge.parse_backend_check_output(
            "lean_backend_check=pass\n"
            "source=Simple.sol\n"
            "contract=Simple\n"
            "object=Simple_1_deployed\n"
            "stage\tto_yul_contract\tsome\n"
            "stage\tobject_image\tsome\n"
            "first_none=none\n"
            "bytecode_bytes=12\n"
            "bytecode=0x6000\n"
        )

        self.assertEqual(parsed["status"], "pass")
        self.assertEqual(parsed["first_none"], "none")
        self.assertEqual(parsed["bytecode_bytes"], 12)
        self.assertEqual(parsed["bytecode"], "0x6000")

    def test_parse_backend_check_output_records_locals_diagnostics(self):
        parsed = bridge.parse_backend_check_output(
            "lean_backend_check=fail\n"
            "source=Simple.sol\n"
            "contract=Simple\n"
            "object=Simple_1_deployed\n"
            "stage\tfunctions_to_locals\tnone\n"
            "locals_body\tmain\tsome\n"
            "locals_proc\tfinalize_allocation\tnone\n"
            "locals_stmt\tfinalize_allocation\t2\tif\tnone\n"
            "first_none=functions_to_locals\n"
        )

        self.assertEqual(parsed["localsBody"], "some")
        self.assertEqual(
            parsed["localsProcs"], {"finalize_allocation": "none"}
        )
        self.assertEqual(
            parsed["localsStmtTrace"],
            [
                {
                    "owner": "finalize_allocation",
                    "index": 2,
                    "kind": "if",
                    "status": "none",
                }
            ],
        )

    def test_bridge_json_input_round_trips_to_python_ast(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[
                bridge.Let(["x"], bridge.Lit(1)),
                bridge.Assign(
                    ["x"],
                    bridge.Call(
                        "add",
                        [bridge.Var("x"), bridge.BytesLit([0x02])],
                        bridge.CALL_PRIMITIVE,
                    ),
                ),
                bridge.Switch(
                    bridge.Var("x"),
                    [
                        (
                            bridge.SwitchCaseValue(bridge.SWITCH_CASE_WORD, 3),
                            [bridge.Control("Break")],
                        )
                    ],
                    [bridge.Control("Continue")],
                ),
                bridge.For(
                    [],
                    bridge.Lit(1),
                    [bridge.ExprStmt(bridge.Call("pop", [bridge.Lit(0)], bridge.CALL_PRIMITIVE))],
                    [bridge.If(bridge.Var("x"), [bridge.Control("Leave")])],
                ),
            ],
            functions=[
                (
                    "readBlob",
                    bridge.FunctionDef(
                        ["offset"],
                        ["value"],
                        [
                            bridge.ExprStmt(
                                bridge.Call(
                                    "datasize",
                                    [bridge.StringLit("blob")],
                                    bridge.CALL_OBJECT_BUILTIN,
                                )
                            )
                        ],
                    ),
                )
            ],
            data=[bridge.DataSection("blob", [0, 255])],
            subobjects=[],
            items=[bridge.ObjectItemRef("data", 0)],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[bridge.Block([bridge.ExprStmt(bridge.Var("x"))])],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Simple.bridge.json"
            path.write_text(bridge.render_bridge_json(root, "Simple.sol", "Simple"))
            source_name, contract_name, decoded = bridge.read_bridge_json_input(path)

        self.assertEqual(source_name, "Simple.sol")
        self.assertEqual(contract_name, "Simple")
        self.assertEqual(decoded, root)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_schema_accepts_rendered_bridge_json(self):
        obj = bridge.YulObject(
            name="Schema_1",
            dispatcher=[
                bridge.Let(["x"], None),
                bridge.Assign(["x"], bridge.StringLit("blob")),
                bridge.Assign(["x"], bridge.BytesLit([0xAA, 0xBB])),
                bridge.ExprStmt(
                    bridge.Call(
                        "verbatim_0i_0o",
                        [],
                        bridge.CALL_DIALECT_BUILTIN,
                    )
                ),
                bridge.FunctionStmt(
                    "local",
                    bridge.FunctionDef([], [], [bridge.Control("Leave")]),
                ),
                bridge.Switch(
                    bridge.Var("x"),
                    [
                        (
                            bridge.SwitchCaseValue(bridge.SWITCH_CASE_WORD, 0),
                            [bridge.Control("Break")],
                        )
                    ],
                    [bridge.Control("Continue")],
                ),
                bridge.For(
                    [],
                    bridge.Lit(1),
                    [bridge.ExprStmt(bridge.Call("pop", [], bridge.CALL_PRIMITIVE))],
                    [bridge.If(bridge.Var("x"), [bridge.Control("Leave")])],
                ),
            ],
            functions=[
                (
                    "reader",
                    bridge.FunctionDef(
                        ["p"],
                        ["r"],
                        [
                            bridge.ExprStmt(
                                bridge.Call(
                                    "datasize",
                                    [bridge.StringLit("blob")],
                                    bridge.CALL_OBJECT_BUILTIN,
                                )
                            )
                        ],
                    ),
                )
            ],
            data=[bridge.DataSection(None, [0, 255])],
            subobjects=[],
            items=[bridge.ObjectItemRef("data", 0)],
        )
        schema_path = Path(bridge.__file__).with_name(
            "bridge-json-v3.schema.json"
        )
        schema = json.loads(schema_path.read_text())
        rendered = json.loads(
            bridge.render_bridge_json(obj, "Schema.yul", "Schema", "yulAst")
        )

        jsonschema.Draft202012Validator.check_schema(schema)
        jsonschema.validate(rendered, schema)
        self.assertEqual(rendered["frontend"], {"producer": "solc", "ast": "yulAst", "evmVersion": "cancun"})
        rendered_alias = json.loads(
            bridge.render_bridge_json(
                obj,
                "Schema.yul",
                "Schema",
                "yulAst",
                evm_version="pectra",
            )
        )
        jsonschema.validate(rendered_alias, schema)
        self.assertEqual(rendered_alias["frontend"]["evmVersion"], "pectra")

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_schema_rejects_unknown_statement_property(self):
        schema_path = Path(bridge.__file__).with_name(
            "bridge-json-v3.schema.json"
        )
        schema = json.loads(schema_path.read_text())
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        rendered = json.loads(bridge.render_bridge_json(obj, "Simple.sol", "Simple"))
        rendered["selectedObject"]["dispatcher"].append(
            {"node": "break", "extra": "not in schema"}
        )

        with self.assertRaises(jsonschema.ValidationError):
            jsonschema.validate(rendered, schema)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_summary_schema_accepts_object_and_manifest_summaries(self):
        schema_path = Path(bridge.__file__).with_name(
            "bridge-json-summary-v1.schema.json"
        )
        schema = json.loads(schema_path.read_text())
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "sload",
                        [bridge.Lit(0)],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        object_summary = bridge.bridge_json_summary_artifact(
            obj,
            "Simple.sol",
            "Simple",
            "runtime",
            {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
        )
        manifest_summary = json.loads(
            bridge.render_bridge_json_summary_outputs(
                [object_summary],
                ["Simple.sol:I"],
            )
        )

        jsonschema.Draft202012Validator.check_schema(schema)
        jsonschema.validate(object_summary, schema)
        jsonschema.validate(manifest_summary, schema)
        self.assertEqual(
            object_summary["frontend"],
            {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
        )
        self.assertEqual(
            manifest_summary["skippedContractEntries"],
            [
                {
                    "source": "Simple.sol",
                    "contract": "I",
                    "reason": "skipped",
                }
            ],
        )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_lean_backend_check_schema_accepts_rendered_report(self):
        schema_path = Path(bridge.__file__).with_name(
            "lean-backend-check-v1.schema.json"
        )
        schema = json.loads(schema_path.read_text())
        report = json.loads(
            bridge.render_lean_backend_check_outputs(
                [
                    bridge.LeanBackendCheckArtifact(
                        source_name="A.sol",
                        contract_name="A",
                        object_selector="runtime",
                        object_name="A_1_deployed",
                        summary={
                            "source": "A.sol",
                            "contract": "A",
                            "object": "A_1_deployed",
                            "status": "fail",
                            "first_none": "functions_compile",
                            "stages": {
                                "to_yul_contract": "some",
                                "functions_compile": "none",
                                "object_image": "none",
                            },
                        },
                        frontend={"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                    ),
                    bridge.LeanBackendCheckArtifact(
                        source_name="B.sol",
                        contract_name="B",
                        object_selector="creation",
                        object_name="B_1",
                        summary={
                            "source": "B.sol",
                            "contract": "B",
                            "object": "B_1",
                            "status": "pass",
                            "first_none": "none",
                            "stages": {
                                "to_yul_contract": "none",
                                "object_image": "some",
                            },
                            "bytecode_bytes": 12,
                        },
                        frontend={"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
                    ),
                ],
                ["I.sol:I"],
            )
        )

        jsonschema.Draft202012Validator.check_schema(schema)
        jsonschema.validate(report, schema)
        self.assertEqual(
            [item["frontend"]["ast"] for item in report["checkedObjects"]],
            ["irAst", "irOptimizedAst"],
        )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_provenance_schema_accepts_artifact_metadata(self):
        schema_path = Path(bridge.__file__).with_name(
            "bridge-json-provenance-v1.schema.json"
        )
        schema = json.loads(schema_path.read_text())
        provenance = {
            "schema": bridge.BRIDGE_JSON_PROVENANCE_SCHEMA,
            "manifestSchema": bridge.BRIDGE_JSON_MANIFEST_SCHEMA,
            "manifest": "/tmp/bridge-json/manifest.json",
            "entries": {
                "creation": {
                    "source": "Simple.sol",
                    "contract": "Simple",
                    "selector": "creation",
                    "object": "Simple_1",
                    "path": "Simple.creation.bridge.json",
                    "sha256": "0" * 64,
                },
                "runtime": {
                    "source": "Simple.sol",
                    "contract": "Simple",
                    "selector": "runtime",
                    "object": "Simple_1_deployed",
                    "path": "Simple.runtime.bridge.json",
                    "sha256": "1" * 64,
                },
            },
        }

        jsonschema.Draft202012Validator.check_schema(schema)
        jsonschema.validate(provenance, schema)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_embedded_bridge_provenance_schema_shapes_match_standalone(self):
        scripts_dir = Path(bridge.__file__).resolve().parent
        provenance_schema = json.loads(
            (scripts_dir / "bridge-json-provenance-v1.schema.json").read_text()
        )
        bytecode_schema = json.loads(
            (scripts_dir / "bytecode-artifact-v1.schema.json").read_text()
        )
        metadata_schema = json.loads(
            (scripts_dir / "evm-compiler-metadata-v1.schema.json").read_text()
        )

        jsonschema.Draft202012Validator.check_schema(provenance_schema)
        jsonschema.Draft202012Validator.check_schema(bytecode_schema)
        jsonschema.Draft202012Validator.check_schema(metadata_schema)

        standalone_defs = provenance_schema["$defs"]
        standalone_provenance = {
            key: provenance_schema[key]
            for key in ["type", "additionalProperties", "required", "properties"]
        }
        for embedded_schema in [bytecode_schema, metadata_schema]:
            embedded_defs = embedded_schema["$defs"]
            self.assertEqual(
                embedded_defs["manifestEntry"],
                standalone_defs["manifestEntry"],
            )
            self.assertEqual(
                embedded_defs["frontend"],
                standalone_defs["frontend"],
            )
            embedded_provenance = embedded_defs["bridgeJsonProvenance"]
            self.assertEqual(
                embedded_provenance["required"],
                standalone_provenance["required"],
            )
            self.assertEqual(
                embedded_provenance["properties"]["schema"],
                standalone_provenance["properties"]["schema"],
            )
            self.assertEqual(
                embedded_provenance["properties"]["manifestSchema"],
                standalone_provenance["properties"]["manifestSchema"],
            )
            self.assertEqual(
                embedded_provenance["properties"]["entries"],
                standalone_provenance["properties"]["entries"],
            )
            self.assertEqual(
                embedded_provenance["properties"]["linkerSymbols"],
                standalone_provenance["properties"]["linkerSymbols"],
            )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bytecode_artifact_and_metadata_schemas_accept_rendered_outputs(self):
        artifact_schema_path = Path(bridge.__file__).with_name(
            "bytecode-artifact-v1.schema.json"
        )
        metadata_schema_path = Path(bridge.__file__).with_name(
            "evm-compiler-metadata-v1.schema.json"
        )
        artifact_schema = json.loads(artifact_schema_path.read_text())
        metadata_schema = json.loads(metadata_schema_path.read_text())
        compatibility = {
            "profile": "current-yul-compiler",
            "status": "ready",
            "unsupportedPrimitiveNames": [],
            "objectBuiltinNames": [],
            "dialectBuiltinNames": [],
            "notes": [],
        }
        bridge_json = {
            "schema": bridge.BRIDGE_JSON_PROVENANCE_SCHEMA,
            "manifestSchema": bridge.BRIDGE_JSON_MANIFEST_SCHEMA,
            "manifest": "/tmp/bridge-json/manifest.json",
            "entries": {
                "creation": {
                    "source": "Simple.sol",
                    "contract": "Simple",
                    "selector": "creation",
                    "object": "Simple_14",
                    "path": "Simple.creation.bridge.json",
                    "sha256": "0" * 64,
                    "frontend": {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                },
                "runtime": {
                    "source": "Simple.sol",
                    "contract": "Simple",
                    "selector": "runtime",
                    "object": "Simple_14_deployed",
                    "path": "Simple.runtime.bridge.json",
                    "sha256": "1" * 64,
                    "frontend": {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
                },
            },
        }

        bytecode_artifact = json.loads(
            bridge.render_bytecode_artifact_json(
                "Simple.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                "0x6000",
                "0x00",
                {"3": [{"start": 12, "length": 32}]},
                compatibility,
                bridge_json,
            )
        )
        forge_artifact = json.loads(
            bridge.render_forge_artifact_json(
                "Simple.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                {"evm": {"methodIdentifiers": {}}, "metadata": "{}"},
                "0x6000",
                "0x00",
                {},
                compatibility,
                bridge_json,
            )
        )
        standard_json = json.loads(
            bridge.render_standard_json_output(
                {
                    "contracts": {
                        "Simple.sol": {
                            "Simple": {
                                "evm": {
                                    "bytecode": {},
                                    "deployedBytecode": {},
                                }
                            }
                        }
                    }
                },
                "Simple.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                "0x6000",
                "0x00",
                {},
                compatibility,
                bridge_json,
            )
        )

        jsonschema.Draft202012Validator.check_schema(artifact_schema)
        jsonschema.Draft202012Validator.check_schema(metadata_schema)
        jsonschema.validate(bytecode_artifact, artifact_schema)
        jsonschema.validate(forge_artifact["evmCompiler"], metadata_schema)
        jsonschema.validate(
            standard_json["contracts"]["Simple.sol"]["Simple"]["evmCompiler"],
            metadata_schema,
        )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_evm_compiler_metadata_schema_rejects_unknown_bytecode_source(self):
        schema_path = Path(bridge.__file__).with_name(
            "evm-compiler-metadata-v1.schema.json"
        )
        schema = json.loads(schema_path.read_text())
        metadata = {
            "schema": "evm-compiler.solc-standard-json-output.v1",
            "source": "Simple.sol",
            "contract": "Simple",
            "yul": {
                "creationObject": "Simple_14",
                "runtimeObject": "Simple_14_deployed",
            },
            "sizes": {"creationBytes": 2, "runtimeBytes": 1},
            "bytecodeSource": "solc-original-bytecode",
        }

        jsonschema.Draft202012Validator.check_schema(schema)
        with self.assertRaises(jsonschema.ValidationError):
            jsonschema.validate(metadata, schema)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_bridge_json_provenance(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge_dir = root_dir / "bridge-json"
                bridge.write_artifact_bridge_json_outputs(
                    bridge_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                    ast_output="irAst",
                )
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_1",
                    "Simple_1_deployed",
                    "0x60",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    bridge_dir,
                    artifact,
                )
                path = root_dir / "provenance.json"
                path.write_text(json.dumps(provenance))
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            provenance["entries"]["creation"]["frontend"],
            {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
        )
        self.assertIn("ok provenance", output)
        self.assertIn("entries=2", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_relative_provenance_manifest(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge_dir = root_dir / "bridge-json"
                bridge.write_artifact_bridge_json_outputs(
                    bridge_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                )
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_1",
                    "Simple_1_deployed",
                    "0x60",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    bridge_dir,
                    artifact,
                )
                provenance["manifest"] = "bridge-json/manifest.json"
                path = root_dir / "portable-provenance.json"
                path.write_text(json.dumps(provenance))
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok provenance", output)
        self.assertIn("entries=2", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_stale_bridge_json_provenance(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge_dir = root_dir / "bridge-json"
                bridge.write_artifact_bridge_json_outputs(
                    bridge_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                )
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_1",
                    "Simple_1_deployed",
                    "0x60",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    bridge_dir,
                    artifact,
                )
                provenance["entries"]["runtime"]["sha256"] = "0" * 64
                path = root_dir / "stale-provenance.json"
                path.write_text(json.dumps(provenance))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("does not match manifest entry", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_bytecode_artifact_provenance(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge_dir = root_dir / "bridge-json"
                bridge.write_artifact_bridge_json_outputs(
                    bridge_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                )
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_1",
                    "Simple_1_deployed",
                    "0x6000",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    bridge_dir,
                    artifact,
                )
                path = root_dir / "bytecode-artifact.json"
                path.write_text(
                    bridge.render_bytecode_artifact_json(
                        artifact.source_name,
                        artifact.contract_name,
                        artifact.creation_object_name,
                        artifact.runtime_object_name,
                        artifact.creation_bytecode,
                        artifact.runtime_bytecode,
                        bridge_json=provenance,
                    )
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok bytecode-artifact", output)
        self.assertIn("creationBytes=2", output)
        self.assertIn("runtimeBytes=1", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_bytecode_artifact_size_mismatch(self):
        artifact = json.loads(
            bridge.render_bytecode_artifact_json(
                "Simple.sol",
                "Simple",
                "Simple_1",
                "Simple_1_deployed",
                "0x6000",
                "0x00",
            )
        )
        artifact["sizes"]["runtimeBytes"] = 2
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad-bytecode-artifact.json"
                path.write_text(json.dumps(artifact))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("inconsistent sizes.runtimeBytes", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_forge_artifact_metadata(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge_dir = root_dir / "bridge-json"
                bridge.write_artifact_bridge_json_outputs(
                    bridge_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                )
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_1",
                    "Simple_1_deployed",
                    "0x6000",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    bridge_dir,
                    artifact,
                )
                path = root_dir / "forge-artifact.json"
                path.write_text(
                    bridge.render_forge_artifact_json(
                        artifact.source_name,
                        artifact.contract_name,
                        artifact.creation_object_name,
                        artifact.runtime_object_name,
                        {"abi": [], "evm": {"methodIdentifiers": {}}},
                        artifact.creation_bytecode,
                        artifact.runtime_bytecode,
                        bridge_json=provenance,
                    )
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok forge-artifact", output)
        self.assertIn("creationBytes=2", output)
        self.assertIn("runtimeBytes=1", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_standard_json_output_metadata(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge_dir = root_dir / "bridge-json"
                bridge.write_artifact_bridge_json_outputs(
                    bridge_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                )
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_1",
                    "Simple_1_deployed",
                    "0x6000",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    bridge_dir,
                    artifact,
                )
                path = root_dir / "standard-json-output.json"
                path.write_text(
                    bridge.render_standard_json_output(
                        {
                            "contracts": {
                                "Simple.sol": {
                                    "Simple": {
                                        "evm": {
                                            "bytecode": {},
                                            "deployedBytecode": {},
                                        }
                                    }
                                }
                            }
                        },
                        artifact.source_name,
                        artifact.contract_name,
                        artifact.creation_object_name,
                        artifact.runtime_object_name,
                        artifact.creation_bytecode,
                        artifact.runtime_bytecode,
                        bridge_json=provenance,
                    )
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok standard-json-output", output)
        self.assertIn("contracts=1", output)

    def test_validate_bridge_json_cli_accepts_standard_json_without_replacements(self):
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "interfaces-only.solc-output.json"
                path.write_text(
                    json.dumps(
                        {
                            "contracts": {
                                "I.sol": {
                                    "I": {"abi": [{"type": "function", "name": "f"}]},
                                    "Base": {"abi": []},
                                }
                            },
                            "sources": {"I.sol": {"id": 0}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok standard-json-output", output)
        self.assertIn("contracts=0", output)

    def test_validate_bridge_json_cli_rejects_malformed_standard_json_contract_map(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad-solc-output.json"
                path.write_text(json.dumps({"contracts": {"I.sol": []}}))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("contracts['I.sol']", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_summary(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "sload",
                        [bridge.Lit(0)],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "runtime.summary.json"
                path.write_text(
                    bridge.render_bridge_json_summary(
                        obj,
                        "Simple.sol",
                        "Simple",
                        "runtime",
                    )
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok summary", output)
        self.assertIn("source=Simple.sol", output)
        self.assertIn("object=runtime", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_lean_backend_check(self):
        report = bridge.render_lean_backend_check_outputs(
            [
                bridge.LeanBackendCheckArtifact(
                    source_name="A.sol",
                    contract_name="A",
                    object_selector="runtime",
                    object_name="A_1_deployed",
                    summary={
                        "source": "A.sol",
                        "contract": "A",
                        "object": "A_1_deployed",
                        "status": "fail",
                        "first_none": "functions_compile",
                        "stages": {
                            "to_yul_contract": "some",
                            "functions_compile": "none",
                            "object_image": "none",
                        },
                    },
                    frontend={"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                ),
                bridge.LeanBackendCheckArtifact(
                    source_name="B.sol",
                    contract_name="B",
                    object_selector="runtime",
                    object_name="B_1_deployed",
                    summary={
                        "source": "B.sol",
                        "contract": "B",
                        "object": "B_1_deployed",
                        "status": "pass",
                        "first_none": "none",
                        "stages": {"object_image": "some"},
                        "bytecode_bytes": 3,
                    },
                    frontend={"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
                ),
            ],
            [],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "backend-check.json"
                path.write_text(report)
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok backend-check", output)
        self.assertIn("objects=2", output)
        self.assertIn("failed=1", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_lean_backend_check_count_mismatch(self):
        report = json.loads(
            bridge.render_lean_backend_check_outputs(
                [
                    bridge.LeanBackendCheckArtifact(
                        source_name="A.sol",
                        contract_name="A",
                        object_selector="runtime",
                        object_name="A_1_deployed",
                        summary={
                            "source": "A.sol",
                            "contract": "A",
                            "object": "A_1_deployed",
                            "status": "fail",
                            "first_none": "functions_compile",
                            "stages": {
                                "functions_compile": "none",
                                "object_image": "none",
                            },
                        },
                    )
                ],
                [],
            )
        )
        report["firstNoneCounts"] = {}
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad-backend-check.json"
                path.write_text(json.dumps(report))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("inconsistent firstNoneCounts", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_lean_backend_check_pass_mismatch(self):
        report = json.loads(
            bridge.render_lean_backend_check_outputs(
                [
                    bridge.LeanBackendCheckArtifact(
                        source_name="A.sol",
                        contract_name="A",
                        object_selector="runtime",
                        object_name="A_1_deployed",
                        summary={
                            "source": "A.sol",
                            "contract": "A",
                            "object": "A_1_deployed",
                            "status": "pass",
                            "first_none": "none",
                            "stages": {"object_image": "some"},
                            "bytecode_bytes": 1,
                        },
                    )
                ],
                [],
            )
        )
        report["checkedObjects"][0]["stages"]["object_image"] = "none"
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad-backend-check.json"
                path.write_text(json.dumps(report))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("pass object lacks object_image=some", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_backend_fail_with_object_image(self):
        report = json.loads(
            bridge.render_lean_backend_check_outputs(
                [
                    bridge.LeanBackendCheckArtifact(
                        source_name="A.sol",
                        contract_name="A",
                        object_selector="runtime",
                        object_name="A_1_deployed",
                        summary={
                            "source": "A.sol",
                            "contract": "A",
                            "object": "A_1_deployed",
                            "status": "fail",
                            "first_none": "functions_compile",
                            "stages": {
                                "functions_compile": "none",
                                "object_image": "some",
                            },
                            "bytecode_bytes": 7,
                        },
                    )
                ],
                [],
            )
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "backend-check.json"
                path.write_text(json.dumps(report))
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok backend-check", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_lean_backend_check_duplicate_object(self):
        artifact = bridge.LeanBackendCheckArtifact(
            source_name="UniswapV4SqrtPriceMathFallback.sol",
            contract_name="UniswapV4SqrtPriceMathFallback",
            object_selector="runtime",
            object_name="UniswapV4SqrtPriceMathFallback_208_deployed",
            summary={
                "source": "UniswapV4SqrtPriceMathFallback.sol",
                "contract": "UniswapV4SqrtPriceMathFallback",
                "object": "UniswapV4SqrtPriceMathFallback_208_deployed",
                "status": "fail",
                "first_none": "functions_compile",
                "stages": {
                    "to_yul_contract": "some",
                    "functions_compile": "none",
                    "object_image": "none",
                },
            },
        )
        report = bridge.render_lean_backend_check_outputs([artifact, artifact], [])
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "duplicate-backend-check.json"
                path.write_text(report)
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("duplicate checked object", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_summary_count_mismatch(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "sload",
                        [bridge.Lit(0)],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.summary.json"
                summary = bridge.bridge_json_summary_artifact(
                    obj,
                    "Simple.sol",
                    "Simple",
                    "runtime",
                )
                summary["counts"]["calls"] += 1
                path.write_text(json.dumps(summary))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("inconsistent counts.calls", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_summary_duplicate_count_entry(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "sload",
                        [bridge.Lit(0)],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.summary.json"
                summary = bridge.bridge_json_summary_artifact(
                    obj,
                    "Simple.sol",
                    "Simple",
                    "runtime",
                )
                summary["calls"]["primitive"]["names"].append(
                    {"name": "sload", "count": 1}
                )
                summary["calls"]["primitive"]["total"] += 1
                summary["counts"]["calls"] += 1
                path.write_text(json.dumps(summary))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("duplicate count entry name: 'sload'", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_backend_compatibility_mismatch(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "gas",
                        [],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.summary.json"
                summary = bridge.bridge_json_summary_artifact(
                    obj,
                    "Calls.sol",
                    "Calls",
                    "runtime",
                )
                summary["backendCompatibility"]["status"] = "blocked"
                path.write_text(json.dumps(summary))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("inconsistent backendCompatibility.status", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_backend_compatibility_mismatch(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call(
                        "gas",
                        [],
                        bridge.CALL_PRIMITIVE,
                    )
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.manifest.summary.json"
                object_summary = bridge.bridge_json_summary_artifact(
                    obj,
                    "Calls.sol",
                    "Calls",
                    "runtime",
                )
                summary = json.loads(
                    bridge.render_bridge_json_summary_outputs(
                        [object_summary],
                        [],
                    )
                )
                summary["backendCompatibility"]["status"] = "blocked"
                path.write_text(json.dumps(summary))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn(
            "inconsistent aggregate backendCompatibility.status",
            error,
        )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_summary_skipped_entry_mismatch(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.manifest.summary.json"
                summary = json.loads(
                    bridge.render_bridge_json_summary_outputs(
                        [],
                        ["Simple.sol:I"],
                        [
                            {
                                "source": "Other.sol",
                                "contract": "I",
                                "reason": "no-yul-ir",
                            }
                        ],
                    )
                )
                path.write_text(json.dumps(summary))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(["--quiet", str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn(
            "inconsistent skippedContracts and skippedContractEntries",
            error,
        )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_valid_file(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "runtime.bridge.json"
                path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("source=Simple.sol", output)
        self.assertIn("contract=Simple", output)
        self.assertIn("object=runtime", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_schema_error(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.bridge.json"
                rendered = json.loads(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                rendered["selectedObject"]["dispatcher"].append(
                    {"node": "break", "extra": "not in schema"}
                )
                path.write_text(json.dumps(rendered))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main([str(path)])
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("schema validation failed", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_accepts_manifest(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                bridge.write_artifact_bridge_json_outputs(
                    Path(directory),
                    root,
                    "Simple.sol",
                    "Simple",
                )
                sys.stdout = io.StringIO()
                result = validate_bridge_json.main(
                    [str(Path(directory) / "manifest.json")]
                )
                output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("ok manifest entries=2", output)
        self.assertIn("object=Simple_1", output)
        self.assertIn("object=Simple_1_deployed", output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_frontend_mismatch(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root_dir = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    root_dir,
                    root,
                    "Simple.sol",
                    "Simple",
                    ast_output="irAst",
                )
                manifest_path = root_dir / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                manifest["entries"][0]["frontend"]["ast"] = "irOptimizedAst"
                manifest_path.write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(manifest_path)]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("frontend metadata does not match manifest entry", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_skipped_count_mismatch(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge_path = root / "runtime.bridge.json"
                bridge_path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [
                        {
                            "source": "Other.sol",
                            "contract": "Simple",
                            "selector": "runtime",
                            "object": "runtime",
                            "path": bridge_path.name,
                        }
                    ],
                    "skippedContracts": ["Simple.sol:I"],
                    "counts": {"entries": 1, "skippedContracts": 0},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("counts.skippedContracts", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_bad_skipped_label(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [],
                    "skippedContracts": ["NotALabel"],
                    "counts": {"entries": 0, "skippedContracts": 1},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("invalid skipped contract label", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_skipped_entry_mismatch(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [],
                    "skippedContracts": ["Simple.sol:I"],
                    "skippedContractEntries": [
                        {
                            "source": "Other.sol",
                            "contract": "I",
                            "reason": "no-yul-ir",
                        }
                    ],
                    "counts": {"entries": 0, "skippedContracts": 1},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("inconsistent skippedContracts", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_duplicate_entries(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                entry = {
                    "source": "Simple.sol",
                    "contract": "Simple",
                    "selector": "runtime",
                    "object": "runtime",
                    "path": "runtime.bridge.json",
                }
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [entry, dict(entry)],
                    "counts": {"entries": 2},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("duplicate entry", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_duplicate_paths(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [
                        {
                            "source": "Simple.sol",
                            "contract": "Simple",
                            "selector": "creation",
                            "object": "creation",
                            "path": "same.bridge.json",
                        },
                        {
                            "source": "Simple.sol",
                            "contract": "Simple",
                            "selector": "runtime",
                            "object": "runtime",
                            "path": "same.bridge.json",
                        },
                    ],
                    "counts": {"entries": 2},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("duplicate bridge JSON path", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_metadata_mismatch(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge_path = root / "runtime.bridge.json"
                bridge_path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [
                        {
                            "source": "Other.sol",
                            "contract": "Simple",
                            "selector": "runtime",
                            "object": "runtime",
                            "path": bridge_path.name,
                        }
                    ],
                    "counts": {"entries": 1},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("but manifest says 'Other.sol'", error)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_schema_error(self):
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [
                        {
                            "source": "Simple.sol",
                            "contract": "Simple",
                            "selector": "runtime",
                            "object": "runtime",
                            "path": "../runtime.bridge.json",
                        }
                    ],
                    "counts": {"entries": 1},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("manifest schema validation failed", error)

    def test_bridge_json_input_rejects_out_of_range_item_ref(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
            items=[],
        )
        raw = json.loads(bridge.render_bridge_json(obj, "Simple.sol", "Simple"))
        raw["selectedObject"]["items"] = [{"kind": "data", "index": 0}]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.bridge.json"
            path.write_text(json.dumps(raw))
            with self.assertRaises(bridge.ConversionError):
                bridge.read_bridge_json_input(path)

    def test_bridge_json_dir_writes_creation_and_runtime_files(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[bridge.DataSection(None, [0, 1])],
            subobjects=[],
            items=[bridge.ObjectItemRef("data", 0)],
        )
        root = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        with tempfile.TemporaryDirectory() as directory:
            bridge.write_artifact_bridge_json_outputs(
                Path(directory),
                root,
                "contracts/Simple.sol",
                "Simple",
            )
            paths = sorted(Path(directory).glob("*.bridge.json"))
            decoded = [
                bridge.read_bridge_json_input(path)[2].name
                for path in paths
            ]
            manifest = json.loads(
                (Path(directory) / "manifest.json").read_text()
            )
            manifest_paths_exist = all(
                (Path(directory) / entry["path"]).exists()
                for entry in manifest["entries"]
            )
            manifest_hashes_match = all(
                entry["sha256"]
                == hashlib.sha256(
                    (Path(directory) / entry["path"]).read_bytes()
                ).hexdigest()
                for entry in manifest["entries"]
            )

        self.assertEqual(
            sorted(decoded),
            ["Simple_1", "Simple_1_deployed"],
        )
        self.assertEqual(len(paths), 2)
        self.assertEqual(
            sorted(path.name for path in paths),
            sorted(
                [
                    bridge.bridge_json_output_stem(
                        "contracts/Simple.sol",
                        "Simple",
                        "creation",
                        "Simple_1",
                    )
                    + ".bridge.json",
                    bridge.bridge_json_output_stem(
                        "contracts/Simple.sol",
                        "Simple",
                        "runtime",
                        "Simple_1_deployed",
                    )
                    + ".bridge.json",
                ]
            ),
        )
        for path in paths:
            self.assertRegex(
                path.name,
                r"^contracts_Simple\.sol__Simple__(creation|runtime)__"
                r"Simple_1(?:_deployed)?__[0-9a-f]{12}\.bridge\.json$",
            )
        self.assertEqual(
            manifest["schema"],
            "evm-compiler.bridge-json-manifest.v1",
        )
        self.assertEqual(manifest["counts"], {"entries": 2})
        self.assertEqual(
            [
                (
                    entry["source"],
                    entry["contract"],
                    entry["selector"],
                    entry["object"],
                )
                for entry in manifest["entries"]
            ],
            [
                ("contracts/Simple.sol", "Simple", "creation", "Simple_1"),
                (
                    "contracts/Simple.sol",
                    "Simple",
                    "runtime",
                    "Simple_1_deployed",
                ),
            ],
        )
        self.assertTrue(manifest_paths_exist)
        self.assertTrue(manifest_hashes_match)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_dir_avoids_safe_path_collisions(self):
        obj = bridge.YulObject(
            name="Runtime_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                first = bridge.write_bridge_json_output(
                    root,
                    obj,
                    "contracts/A.sol",
                    "Collision",
                    "runtime",
                )
                second = bridge.write_bridge_json_output(
                    root,
                    obj,
                    "contracts_A.sol",
                    "Collision",
                    "runtime",
                )
                manifest_path = root / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                first_name = first.name
                second_name = second.name
                first_exists = first.exists()
                second_exists = second.exists()
                sys.stdout = io.StringIO()
                validation_result = validate_bridge_json.main([str(manifest_path)])
                validation_output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        self.assertNotEqual(first_name, second_name)
        self.assertTrue(first_exists)
        self.assertTrue(second_exists)
        self.assertEqual(len(manifest["entries"]), 2)
        self.assertEqual(
            {entry["source"] for entry in manifest["entries"]},
            {"contracts/A.sol", "contracts_A.sol"},
        )
        self.assertEqual(
            len({entry["path"] for entry in manifest["entries"]}),
            2,
        )
        for entry in manifest["entries"]:
            self.assertRegex(entry["path"], r"__[0-9a-f]{12}\.bridge\.json$")
        self.assertEqual(validation_result, 0)
        self.assertIn("ok manifest entries=2", validation_output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_manifest_records_linker_symbols(self):
        runtime = bridge.YulObject(
            name="UsesLibrary_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="UsesLibrary_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    root,
                    "UsesLibrary.sol",
                    "UsesLibrary",
                    [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)],
                )
                manifest_path = path / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                artifact = bridge.ContractBytecodeArtifact(
                    "UsesLibrary.sol",
                    "UsesLibrary",
                    "UsesLibrary_1",
                    "UsesLibrary_1_deployed",
                    "0x60",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    path,
                    artifact,
                )
                sys.stdout = io.StringIO()
                validation_result = validate_bridge_json.main([str(manifest_path)])
                validation_output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        expected_symbols = [
            {
                "name": "MathLib.sol:MathLib",
                "value": (
                    "0x000000000000000000000000000000000000000000000000"
                    "000000000000002a"
                ),
            }
        ]
        self.assertEqual(manifest["linkerSymbols"], expected_symbols)
        self.assertEqual(provenance["linkerSymbols"], expected_symbols)
        self.assertEqual(validation_result, 0)
        self.assertIn("ok manifest entries=2", validation_output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_bridge_json_manifest_records_object_layout_hints(self):
        runtime = bridge.YulObject(
            name="Simple_14_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root = bridge.YulObject(
            name="Simple_14",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
        )
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    root,
                    "Simple.sol",
                    "Simple",
                    object_layout=[
                        bridge.ObjectLayoutEntry("Simple_14_deployed", 43, 418)
                    ],
                    local_data_base=461,
                )
                manifest_path = path / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                artifact = bridge.ContractBytecodeArtifact(
                    "Simple.sol",
                    "Simple",
                    "Simple_14",
                    "Simple_14_deployed",
                    "0x60",
                    "0x00",
                )
                provenance = bridge.bridge_json_provenance_for_artifact(
                    path,
                    artifact,
                )
                sys.stdout = io.StringIO()
                validation_result = validate_bridge_json.main([str(manifest_path)])
                validation_output = sys.stdout.getvalue()
        finally:
            sys.stdout = old_stdout

        creation_entry = next(
            entry for entry in manifest["entries"]
            if entry["selector"] == "creation"
        )
        runtime_entry = next(
            entry for entry in manifest["entries"]
            if entry["selector"] == "runtime"
        )
        expected_layout = [
            {
                "name": "Simple_14_deployed",
                "offset": (
                    "0x000000000000000000000000000000000000000000000000"
                    "000000000000002b"
                ),
                "size": (
                    "0x000000000000000000000000000000000000000000000000"
                    "00000000000001a2"
                ),
            }
        ]
        expected_data_base = (
            "0x000000000000000000000000000000000000000000000000"
            "00000000000001cd"
        )
        self.assertEqual(creation_entry["objectLayout"], expected_layout)
        self.assertEqual(creation_entry["localDataBase"], expected_data_base)
        self.assertNotIn("objectLayout", runtime_entry)
        self.assertNotIn("localDataBase", runtime_entry)
        self.assertEqual(
            provenance["entries"]["creation"]["objectLayout"],
            expected_layout,
        )
        self.assertEqual(
            provenance["entries"]["creation"]["localDataBase"],
            expected_data_base,
        )
        self.assertEqual(validation_result, 0)
        self.assertIn("ok manifest entries=2", validation_output)

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_validate_bridge_json_cli_rejects_manifest_sha256_mismatch(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_stderr = sys.stderr
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge_path = root / "runtime.bridge.json"
                bridge_path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                manifest = {
                    "schema": "evm-compiler.bridge-json-manifest.v1",
                    "entries": [
                        {
                            "source": "Simple.sol",
                            "contract": "Simple",
                            "selector": "runtime",
                            "object": "runtime",
                            "path": bridge_path.name,
                            "sha256": "0" * 64,
                        }
                    ],
                    "counts": {"entries": 1},
                }
                (root / "manifest.json").write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = validate_bridge_json.main(
                    ["--quiet", str(root / "manifest.json")]
                )
                error = sys.stderr.getvalue()
        finally:
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("sha256", error)

    def test_bridge_json_manifest_input_lean_json_check_decodes_all_entries(self):
        def make_root(prefix):
            runtime = bridge.YulObject(
                name=f"{prefix}_deployed",
                dispatcher=[],
                functions=[],
                data=[bridge.DataSection(None, [0])],
                subobjects=[],
                items=[bridge.ObjectItemRef("data", 0)],
            )
            return bridge.YulObject(
                name=prefix,
                dispatcher=[],
                functions=[],
                data=[],
                subobjects=[runtime],
                items=[bridge.ObjectItemRef("object", 0)],
            )

        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        calls = []
        try:
            def fake_run_lake_bridge_json_decode(lake, source, cwd):
                calls.append((lake, source, cwd))
                rendered_path = None
                for line in source.splitlines():
                    stripped = line.strip()
                    if stripped.startswith('"/') and stripped.endswith('"'):
                        rendered_path = Path(json.loads(stripped))
                        break
                self.assertIsNotNone(rendered_path)
                rendered = json.loads(rendered_path.read_text())
                selected = rendered["selectedObject"]
                return (
                    "lean_bridge_json_decode=pass\n"
                    f"source={rendered['source']}\n"
                    f"contract={rendered['contract']}\n"
                    f"object={selected['name']}\n"
                    f"dispatcher_stmts={len(selected['dispatcher'])}\n"
                    f"functions={len(selected['functions'])}\n"
                    f"data_sections={len(selected['data'])}\n"
                    f"subobjects={len(selected['subobjects'])}\n"
                    f"items={len(selected.get('items', []))}\n"
                )

            bridge.run_lake_bridge_json_decode = fake_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    root,
                    make_root("A_1"),
                    "src/A.sol",
                    "A",
                    ast_output="irAst",
                )
                bridge.write_artifact_bridge_json_outputs(
                    root,
                    make_root("B_1"),
                    "src/B.sol",
                    "B",
                    ast_output="irOptimizedAst",
                )
                bridge.write_bridge_json_manifest_skipped_contracts(
                    root,
                    ["src/I.sol:I"],
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(root / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["schema"], "evm-compiler.lean-json-check.v2")
        self.assertEqual(
            output["counts"],
            {
                "checkedObjects": 4,
                "checkedContracts": 2,
                "skippedContracts": 1,
            },
        )
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["object"])
                for item in output["checkedObjects"]
            ],
            [
                ("src/A.sol", "A", "creation", "A_1"),
                ("src/A.sol", "A", "runtime", "A_1_deployed"),
                ("src/B.sol", "B", "creation", "B_1"),
                ("src/B.sol", "B", "runtime", "B_1_deployed"),
            ],
        )
        self.assertEqual(output["checkedContracts"], ["src/A.sol:A", "src/B.sol:B"])
        self.assertEqual(output["skippedContracts"], ["src/I.sol:I"])
        self.assertEqual(
            [
                (item["selector"], item["frontend"]["ast"])
                for item in output["checkedObjects"]
            ],
            [
                ("creation", "irAst"),
                ("runtime", "irAst"),
                ("creation", "irOptimizedAst"),
                ("runtime", "irOptimizedAst"),
            ],
        )
        self.assertEqual(len(calls), 4)

    def test_bridge_json_manifest_input_lean_backend_check_reports_all_entries(self):
        def make_root(prefix):
            runtime = bridge.YulObject(
                name=f"{prefix}_deployed",
                dispatcher=[],
                functions=[],
                data=[bridge.DataSection(None, [0])],
                subobjects=[],
                items=[bridge.ObjectItemRef("data", 0)],
            )
            return bridge.YulObject(
                name=prefix,
                dispatcher=[],
                functions=[],
                data=[],
                subobjects=[runtime],
                items=[bridge.ObjectItemRef("object", 0)],
            )

        old_run_lake_backend_check = bridge.run_lake_native_backend_check
        old_stdout = sys.stdout
        calls = []
        try:
            def fake_run_lake_backend_check(lake, json_path, cwd, linker_symbols):
                calls.append((lake, json_path, cwd, linker_symbols))
                self.assertEqual(
                    linker_symbols,
                    [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)],
                )
                rendered = json.loads(json_path.read_text())
                selected = rendered["selectedObject"]
                object_name = selected["name"]
                if object_name.endswith("_deployed"):
                    return (
                        "lean_backend_check=fail\n"
                        f"source={rendered['source']}\n"
                        f"contract={rendered['contract']}\n"
                        f"object={object_name}\n"
                        "stage\tto_yul_contract\tsome\n"
                        "stage\tfunctions_compile\tnone\n"
                        "stage\tobject_image\tnone\n"
                        "first_none=functions_compile\n"
                    )
                return (
                    "lean_backend_check=pass\n"
                    f"source={rendered['source']}\n"
                    f"contract={rendered['contract']}\n"
                    f"object={object_name}\n"
                    "stage\tto_yul_contract\tsome\n"
                    "stage\tobject_image\tsome\n"
                    "first_none=none\n"
                    "bytecode_bytes=7\n"
                )

            bridge.run_lake_native_backend_check = fake_run_lake_backend_check
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    root,
                    make_root("A_1"),
                    "src/A.sol",
                    "A",
                    ast_output="irAst",
                )
                bridge.write_artifact_bridge_json_outputs(
                    root,
                    make_root("B_1"),
                    "src/B.sol",
                    "B",
                    ast_output="irOptimizedAst",
                )
                bridge.write_bridge_json_manifest_skipped_contracts(
                    root,
                    ["src/I.sol:I"],
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(root / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-backend-check",
                        "--linker-symbol",
                        "MathLib.sol:MathLib=42",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_lake_native_backend_check = old_run_lake_backend_check
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["schema"], "evm-compiler.lean-backend-check.v1")
        self.assertEqual(output["counts"]["checkedObjects"], 4)
        self.assertEqual(output["counts"]["passedObjects"], 2)
        self.assertEqual(output["counts"]["failedObjects"], 2)
        self.assertEqual(output["firstNoneCounts"], {"functions_compile": 2})
        self.assertEqual(output["checkedContracts"], ["src/A.sol:A", "src/B.sol:B"])
        self.assertEqual(output["skippedContracts"], ["src/I.sol:I"])
        self.assertEqual(
            [
                (item["selector"], item["frontend"]["ast"])
                for item in output["checkedObjects"]
            ],
            [
                ("creation", "irAst"),
                ("runtime", "irAst"),
                ("creation", "irOptimizedAst"),
                ("runtime", "irOptimizedAst"),
            ],
        )
        self.assertEqual(
            [
                (item["selector"], item["status"], item["firstNone"])
                for item in output["checkedObjects"]
            ],
            [
                ("creation", "pass", "none"),
                ("runtime", "fail", "functions_compile"),
                ("creation", "pass", "none"),
                ("runtime", "fail", "functions_compile"),
            ],
        )
        self.assertEqual(len(calls), 4)

    def test_bridge_json_manifest_backend_check_uses_persisted_linker_symbols(self):
        root = bridge.YulObject(
            name="UsesLibrary_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[
                bridge.YulObject(
                    name="UsesLibrary_1_deployed",
                    dispatcher=[],
                    functions=[],
                    data=[],
                    subobjects=[],
                )
            ],
        )

        old_run_lake_backend_check = bridge.run_lake_native_backend_check
        old_stdout = sys.stdout
        calls = []
        try:
            def fake_run_lake_backend_check(lake, json_path, cwd, linker_symbols):
                calls.append(json_path)
                self.assertEqual(
                    linker_symbols,
                    [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)],
                )
                rendered = json.loads(json_path.read_text())
                selected = rendered["selectedObject"]
                return (
                    "lean_backend_check=pass\n"
                    f"source={rendered['source']}\n"
                    f"contract={rendered['contract']}\n"
                    f"object={selected['name']}\n"
                    "stage\tto_yul_contract\tsome\n"
                    "stage\tobject_image\tsome\n"
                    "first_none=none\n"
                    "bytecode_bytes=3\n"
                )

            bridge.run_lake_native_backend_check = fake_run_lake_backend_check
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    root,
                    "UsesLibrary.sol",
                    "UsesLibrary",
                    [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)],
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-backend-check",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(path),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_lake_native_backend_check = old_run_lake_backend_check
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["counts"]["checkedObjects"], 2)
        self.assertEqual(output["counts"]["passedObjects"], 2)
        self.assertEqual(len(calls), 2)

    def test_bridge_json_manifest_input_bytecode_artifact_replays_creation_entry(self):
        root = bridge.YulObject(
            name="UsesLibrary_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[
                bridge.YulObject(
                    name="UsesLibrary_1_deployed",
                    dispatcher=[],
                    functions=[],
                    data=[],
                    subobjects=[],
                )
            ],
        )
        observed_linker_symbols = []

        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            def fake_compile_contract_bytecode_artifact(
                root_obj,
                source_name,
                contract_name,
                definition_prefix,
                namespace,
                object_layout,
                local_data_base,
                linker_symbols,
                lake,
                lake_cwd,
            ):
                observed_linker_symbols.append(
                    [(entry.name, entry.value) for entry in linker_symbols]
                )
                self.assertEqual(root_obj.name, "UsesLibrary_1")
                self.assertEqual(source_name, "UsesLibrary.sol")
                self.assertEqual(contract_name, "UsesLibrary")
                self.assertEqual(object_layout, [])
                self.assertIsNone(local_data_base)
                return bridge.ContractBytecodeArtifact(
                    source_name,
                    contract_name,
                    root_obj.name,
                    "UsesLibrary_1_deployed",
                    "0x6000",
                    "0x00",
                )

            bridge.compile_contract_bytecode_artifact = (
                fake_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    root,
                    "UsesLibrary.sol",
                    "UsesLibrary",
                    [bridge.LinkerSymbolEntry("MathLib.sol:MathLib", 42)],
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "bytecode-artifact",
                        "--contract",
                        "UsesLibrary",
                    ]
                )
                artifact = json.loads(sys.stdout.getvalue())
        finally:
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            observed_linker_symbols,
            [[("MathLib.sol:MathLib", 42)]],
        )
        self.assertEqual(
            artifact["schema"],
            "evm-compiler.solidity-bytecode-artifact.v1",
        )
        self.assertEqual(artifact["bytecode"]["creation"], "0x6000")
        self.assertEqual(artifact["bytecode"]["runtime"], "0x00")
        self.assertEqual(
            artifact["bridgeJson"]["linkerSymbols"][0]["name"],
            "MathLib.sol:MathLib",
        )

    def test_bridge_json_manifest_input_bytecode_artifact_uses_persisted_layout(self):
        root = bridge.YulObject(
            name="Simple_14",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[
                bridge.YulObject(
                    name="Simple_14_deployed",
                    dispatcher=[],
                    functions=[],
                    data=[],
                    subobjects=[],
                )
            ],
        )
        observed_layouts = []
        observed_data_bases = []

        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            def fake_compile_contract_bytecode_artifact(
                root_obj,
                source_name,
                contract_name,
                definition_prefix,
                namespace,
                object_layout,
                local_data_base,
                linker_symbols,
                lake,
                lake_cwd,
            ):
                observed_layouts.append(
                    [(entry.name, entry.offset, entry.size) for entry in object_layout]
                )
                observed_data_bases.append(local_data_base)
                return bridge.ContractBytecodeArtifact(
                    source_name,
                    contract_name,
                    root_obj.name,
                    "Simple_14_deployed",
                    "0x6000",
                    "0x00",
                )

            bridge.compile_contract_bytecode_artifact = (
                fake_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    root,
                    "Simple.sol",
                    "Simple",
                    object_layout=[
                        bridge.ObjectLayoutEntry("Simple_14_deployed", 43, 418)
                    ],
                    local_data_base=461,
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "bytecode-artifact",
                        "--contract",
                        "Simple",
                    ]
                )
        finally:
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            observed_layouts,
            [[("Simple_14_deployed", 43, 418)]],
        )
        self.assertEqual(observed_data_bases, [461])

    def test_bridge_json_manifest_input_bytecode_artifact_cli_layout_overrides_persisted(self):
        root = bridge.YulObject(
            name="Simple_14",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[
                bridge.YulObject(
                    name="Simple_14_deployed",
                    dispatcher=[],
                    functions=[],
                    data=[],
                    subobjects=[],
                )
            ],
        )
        observed_layouts = []
        observed_data_bases = []

        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            def fake_compile_contract_bytecode_artifact(
                root_obj,
                source_name,
                contract_name,
                definition_prefix,
                namespace,
                object_layout,
                local_data_base,
                linker_symbols,
                lake,
                lake_cwd,
            ):
                observed_layouts.append(
                    [(entry.name, entry.offset, entry.size) for entry in object_layout]
                )
                observed_data_bases.append(local_data_base)
                return bridge.ContractBytecodeArtifact(
                    source_name,
                    contract_name,
                    root_obj.name,
                    "Simple_14_deployed",
                    "0x6000",
                    "0x00",
                )

            bridge.compile_contract_bytecode_artifact = (
                fake_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    root,
                    "Simple.sol",
                    "Simple",
                    object_layout=[
                        bridge.ObjectLayoutEntry("Simple_14_deployed", 43, 418)
                    ],
                    local_data_base=461,
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "bytecode-artifact",
                        "--contract",
                        "Simple",
                        "--object-layout",
                        "Simple_14_deployed=99:100",
                        "--data-base",
                        "77",
                    ]
                )
        finally:
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            observed_layouts,
            [[("Simple_14_deployed", 99, 100)]],
        )
        self.assertEqual(observed_data_bases, [77])

    def test_bridge_json_manifest_input_bytecode_artifact_requires_one_creation(self):
        def make_root(name):
            return bridge.YulObject(
                name=name,
                dispatcher=[],
                functions=[],
                data=[],
                subobjects=[
                    bridge.YulObject(
                        name=f"{name}_deployed",
                        dispatcher=[],
                        functions=[],
                        data=[],
                        subobjects=[],
                    )
                ],
            )

        old_compile = bridge.compile_contract_bytecode_artifact
        old_stderr = sys.stderr
        try:
            def unexpected_compile_contract_bytecode_artifact(*args, **kwargs):
                raise AssertionError("ambiguous manifest should not compile")

            bridge.compile_contract_bytecode_artifact = (
                unexpected_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    make_root("A_1"),
                    "src/A.sol",
                    "A",
                )
                bridge.write_artifact_bridge_json_outputs(
                    path,
                    make_root("B_1"),
                    "src/B.sol",
                    "B",
                )
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        str(path / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "bytecode-artifact",
                    ]
                )
                error = sys.stderr.getvalue()
        finally:
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("exactly one matching creation entry", error)

    def test_bridge_json_manifest_input_rejects_sha256_mismatch_before_lean(self):
        root = bridge.YulObject(
            name="A_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stderr = sys.stderr
        try:
            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("sha256 mismatch should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                bridge.write_bridge_json_output(
                    path,
                    root,
                    "src/A.sol",
                    "A",
                    "creation",
                )
                manifest_path = path / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                manifest["entries"][0]["sha256"] = "0" * 64
                manifest_path.write_text(json.dumps(manifest))
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        str(manifest_path),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(path),
                    ]
                )
                error = sys.stderr.getvalue()
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("sha256", error)

    def test_bridge_json_manifest_input_rejects_duplicate_entry_before_lean(self):
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stderr = sys.stderr
        try:
            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("duplicate manifest entry should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                entry = {
                    "source": "src/A.sol",
                    "contract": "A",
                    "selector": "creation",
                    "object": "A_1",
                    "path": "missing.bridge.json",
                }
                manifest_path = path / "manifest.json"
                manifest_path.write_text(
                    json.dumps(
                        {
                            "schema": "evm-compiler.bridge-json-manifest.v1",
                            "entries": [entry, dict(entry)],
                            "counts": {"entries": 2},
                        }
                    )
                )
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        str(manifest_path),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                    ]
                )
                error = sys.stderr.getvalue()
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("duplicate entry", error)
        self.assertNotIn("does not exist", error)

    def test_bridge_json_manifest_input_rejects_bad_counts_before_lean(self):
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stderr = sys.stderr
        try:
            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("bad manifest counts should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)
                manifest_path = path / "manifest.json"
                manifest_path.write_text(
                    json.dumps(
                        {
                            "schema": "evm-compiler.bridge-json-manifest.v1",
                            "entries": [],
                            "skippedContracts": ["src/A.sol:I"],
                            "counts": {"entries": 0, "skippedContracts": 0},
                        }
                    )
                )
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        str(manifest_path),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                    ]
                )
                error = sys.stderr.getvalue()
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("counts.skippedContracts", error)

    def test_bridge_json_manifest_input_lean_json_check_allows_skipped_only(self):
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("skipped-only manifest should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge.write_bridge_json_manifest_skipped_contracts(
                    root,
                    ["src/I.sol:I", "src/I.sol:IOther"],
                    reason="no-yul-ir",
                )
                manifest = json.loads((root / "manifest.json").read_text())
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(root / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["schema"], "evm-compiler.lean-json-check.v2")
        self.assertEqual(output["checkedObjects"], [])
        self.assertEqual(output["checkedContracts"], [])
        self.assertEqual(
            output["skippedContracts"],
            ["src/I.sol:I", "src/I.sol:IOther"],
        )
        self.assertEqual(
            manifest["skippedContractEntries"],
            [
                {
                    "source": "src/I.sol",
                    "contract": "I",
                    "reason": "no-yul-ir",
                },
                {
                    "source": "src/I.sol",
                    "contract": "IOther",
                    "reason": "no-yul-ir",
                },
            ],
        )
        self.assertEqual(
            output["counts"],
            {
                "checkedObjects": 0,
                "checkedContracts": 0,
                "skippedContracts": 2,
            },
        )

    def test_bridge_json_manifest_input_filters_skipped_contracts(self):
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge.write_bridge_json_manifest_skipped_contracts(
                    root,
                    ["src/A.sol:I", "src/B.sol:I", "src/B.sol:J"],
                    reason="no-yul-ir",
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(root / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                        "--source-name",
                        "src/B.sol",
                        "--contract",
                        "I",
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["checkedObjects"], [])
        self.assertEqual(output["skippedContracts"], ["src/B.sol:I"])
        self.assertEqual(output["counts"]["skippedContracts"], 1)

    def test_bridge_json_manifest_summary_filters_structured_skipped_entries(self):
        old_stdout = sys.stdout
        try:
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge.write_bridge_json_manifest_skipped_contracts(
                    root,
                    ["src/A.sol:I", "src/B.sol:I", "src/B.sol:J"],
                    reason="no-yul-ir",
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(root / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "bridge-json-summary",
                        "--source-name",
                        "src/B.sol",
                        "--contract",
                        "I",
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            output["counts"],
            {"objects": 0, "skippedContracts": 1, "calls": 0},
        )
        self.assertEqual(output["skippedContracts"], ["src/B.sol:I"])
        self.assertEqual(
            output["skippedContractEntries"],
            [
                {
                    "source": "src/B.sol",
                    "contract": "I",
                    "reason": "no-yul-ir",
                }
            ],
        )

    def test_bridge_json_manifest_input_filters_contract_and_object(self):
        runtime = bridge.YulObject(
            name="A_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root_object = bridge.YulObject(
            name="A_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            def fake_run_lake_bridge_json_decode(lake, source, cwd):
                rendered_path = None
                for line in source.splitlines():
                    stripped = line.strip()
                    if stripped.startswith('"/') and stripped.endswith('"'):
                        rendered_path = Path(json.loads(stripped))
                        break
                self.assertIsNotNone(rendered_path)
                rendered = json.loads(rendered_path.read_text())
                selected = rendered["selectedObject"]
                return (
                    "lean_bridge_json_decode=pass\n"
                    f"source={rendered['source']}\n"
                    f"contract={rendered['contract']}\n"
                    f"object={selected['name']}\n"
                    "dispatcher_stmts=0\n"
                    "functions=0\n"
                    "data_sections=0\n"
                    "subobjects=0\n"
                    "items=0\n"
                )

            bridge.run_lake_bridge_json_decode = fake_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                bridge.write_artifact_bridge_json_outputs(
                    root,
                    root_object,
                    "src/A.sol",
                    "A",
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(root / "manifest.json"),
                        "--input-format",
                        "bridge-json-manifest",
                        "--format",
                        "lean-json-check",
                        "--contract",
                        "A",
                        "--object",
                        "runtime",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["counts"]["checkedObjects"], 1)
        self.assertEqual(
            [
                (item["contract"], item["selector"], item["object"])
                for item in output["checkedObjects"]
            ],
            [("A", "runtime", "A_1_deployed")],
        )

    def test_bridge_json_input_bytecode_routes_through_lean_sidecar(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_run_lake_object_image = bridge.run_lake_native_object_image
        old_stdout = sys.stdout
        calls = []
        try:
            def fake_run_lake_object_image(lake, json_path, cwd, linker_symbols):
                calls.append((lake, json_path, cwd, linker_symbols))
                self.assertTrue(json_path.exists())
                return bridge.CompiledObjectImage("0x00")

            bridge.run_lake_native_object_image = fake_run_lake_object_image
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / "runtime.bridge.json"
                path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path),
                        "--input-format",
                        "bridge-json",
                        "--format",
                        "bytecode",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = sys.stdout.getvalue()
        finally:
            bridge.run_lake_native_object_image = old_run_lake_object_image
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output, "0x00\n")
        self.assertEqual(calls[0][0], "lake")

    def test_bridge_json_input_lean_json_check_routes_through_lean_sidecar(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call("stop", [], bridge.CALL_PRIMITIVE)
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        calls = []
        try:
            def fake_run_lake_bridge_json_decode(lake, source, cwd):
                calls.append((lake, source, cwd))
                self.assertIn("IO.FS.readFile evmCompilerRunnerBridgeJsonPath", source)
                self.assertIn("BridgeJson.parseProgram? input", source)
                rendered_path = None
                for line in source.splitlines():
                    stripped = line.strip()
                    if stripped.startswith('"/') and stripped.endswith('"'):
                        rendered_path = Path(json.loads(stripped))
                        break
                self.assertIsNotNone(rendered_path)
                self.assertTrue(rendered_path.exists())
                rendered_json = json.loads(rendered_path.read_text())
                self.assertEqual(rendered_json["selectedObject"]["name"], "runtime")
                return (
                    "lean_bridge_json_decode=pass\n"
                    "source=Simple.sol\n"
                    "contract=Simple\n"
                    "object=runtime\n"
                )

            bridge.run_lake_bridge_json_decode = fake_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / "runtime.bridge.json"
                path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path),
                        "--input-format",
                        "bridge-json",
                        "--format",
                        "lean-json-check",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = sys.stdout.getvalue()
        finally:
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("lean_bridge_json_decode=pass", output)
        self.assertIn("object=runtime", output)
        self.assertEqual(calls[0][0], "lake")

    def test_bridge_json_input_lean_backend_check_routes_through_lean_sidecar(self):
        obj = bridge.YulObject(
            name="runtime",
            dispatcher=[
                bridge.ExprStmt(
                    bridge.Call("stop", [], bridge.CALL_PRIMITIVE)
                )
            ],
            functions=[],
            data=[],
            subobjects=[],
        )
        old_run_lake_backend_check = bridge.run_lake_native_backend_check
        old_stdout = sys.stdout
        calls = []
        try:
            def fake_run_lake_backend_check(lake, json_path, cwd, linker_symbols):
                calls.append((lake, json_path, cwd, linker_symbols))
                self.assertTrue(json_path.exists())
                rendered_json = json.loads(json_path.read_text())
                self.assertEqual(rendered_json["selectedObject"]["name"], "runtime")
                return (
                    "lean_backend_check=pass\n"
                    "source=Simple.sol\n"
                    "contract=Simple\n"
                    "object=runtime\n"
                    "stage\tto_yul_contract\tsome\n"
                    "stage\tobject_image\tsome\n"
                    "first_none=none\n"
                    "bytecode_bytes=1\n"
                    "bytecode=0x00\n"
                )

            bridge.run_lake_native_backend_check = fake_run_lake_backend_check
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / "runtime.bridge.json"
                path.write_text(
                    bridge.render_bridge_json(obj, "Simple.sol", "Simple")
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path),
                        "--input-format",
                        "bridge-json",
                        "--format",
                        "lean-backend-check",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = sys.stdout.getvalue()
        finally:
            bridge.run_lake_native_backend_check = old_run_lake_backend_check
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("lean_backend_check=pass", output)
        self.assertIn("first_none=none", output)
        self.assertEqual(calls[0][0], "lake")

    def test_bridge_json_input_backend_check_uses_root_object_by_default(self):
        runtime = bridge.YulObject(
            name="Simple_1_deployed",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[],
        )
        root_object = bridge.YulObject(
            name="Simple_1",
            dispatcher=[],
            functions=[],
            data=[],
            subobjects=[runtime],
            items=[bridge.ObjectItemRef("object", 0)],
        )
        old_run_lake_backend_check = bridge.run_lake_native_backend_check
        old_stdout = sys.stdout
        try:
            def fake_run_lake_backend_check(lake, json_path, cwd, linker_symbols):
                rendered_json = json.loads(json_path.read_text())
                self.assertEqual(rendered_json["selectedObject"]["name"], "Simple_1")
                return (
                    "lean_backend_check=pass\n"
                    "source=Simple.sol\n"
                    "contract=Simple\n"
                    "object=Simple_1\n"
                    "stage\tobject_image\tsome\n"
                    "first_none=none\n"
                    "bytecode_bytes=1\n"
                )

            bridge.run_lake_native_backend_check = fake_run_lake_backend_check
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / "creation.bridge.json"
                path.write_text(
                    bridge.render_bridge_json(root_object, "Simple.sol", "Simple")
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(path),
                        "--input-format",
                        "bridge-json",
                        "--format",
                        "lean-backend-check",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = sys.stdout.getvalue()
        finally:
            bridge.run_lake_native_backend_check = old_run_lake_backend_check
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertIn("object=Simple_1", output)

    def test_standard_json_all_contracts_lean_json_check_decodes_ir_contracts(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "A.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        )
                    },
                    "I": {"abi": []},
                },
                "B.sol": {
                    "B": {"irAst": raw_object("B_1")},
                },
            }
        }
        old_run_solc = bridge.run_solc
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def fake_run_lake_bridge_json_decode(lake, source, cwd):
                rendered_path = None
                for line in source.splitlines():
                    stripped = line.strip()
                    if stripped.startswith('"/') and stripped.endswith('"'):
                        rendered_path = Path(json.loads(stripped))
                        break
                self.assertIsNotNone(rendered_path)
                rendered_json = json.loads(rendered_path.read_text())
                self.assertEqual(
                    rendered_json["frontend"],
                    {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                )
                selected = rendered_json["selectedObject"]
                return (
                    "lean_bridge_json_decode=pass\n"
                    f"source={rendered_json['source']}\n"
                    f"contract={rendered_json['contract']}\n"
                    f"object={selected['name']}\n"
                    "dispatcher_stmts=0\n"
                    "functions=0\n"
                    "data_sections=0\n"
                    "subobjects=0\n"
                    "items=0\n"
                )

            bridge.run_lake_bridge_json_decode = fake_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "lean-json-check",
                        "--all-contracts",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["schema"], "evm-compiler.lean-json-check.v2")
        self.assertEqual(
            output["counts"],
            {
                "checkedObjects": 3,
                "checkedContracts": 2,
                "skippedContracts": 1,
            },
        )
        self.assertEqual(output["skippedContracts"], ["A.sol:I"])
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["object"])
                for item in output["checkedObjects"]
            ],
            [
                ("A.sol", "A", "creation", "A_1"),
                ("A.sol", "A", "runtime", "A_1_deployed"),
                ("B.sol", "B", "creation", "B_1"),
            ],
        )
        self.assertEqual(output["checkedContracts"], ["A.sol:A", "B.sol:B"])
        self.assertEqual(
            [item["frontend"] for item in output["checkedObjects"]],
            [
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
            ],
        )

    def test_standard_json_all_contracts_lean_backend_check_reports_stage_status(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "A.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        )
                    },
                    "I": {"abi": []},
                },
                "B.sol": {
                    "B": {"irAst": raw_object("B_1")},
                },
            }
        }
        old_run_solc = bridge.run_solc
        old_run_lake_backend_check = bridge.run_lake_native_backend_check
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def fake_run_lake_backend_check(lake, json_path, cwd, linker_symbols):
                rendered_json = json.loads(json_path.read_text())
                self.assertEqual(
                    rendered_json["frontend"],
                    {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                )
                selected = rendered_json["selectedObject"]
                object_name = selected["name"]
                if object_name.endswith("_deployed"):
                    return (
                        "lean_backend_check=fail\n"
                        f"source={rendered_json['source']}\n"
                        f"contract={rendered_json['contract']}\n"
                        f"object={object_name}\n"
                        "stage\tto_yul_contract\tsome\n"
                        "stage\tfunctions_compile\tnone\n"
                        "stage\tobject_image\tnone\n"
                        "first_none=functions_compile\n"
                    )
                return (
                    "lean_backend_check=pass\n"
                    f"source={rendered_json['source']}\n"
                    f"contract={rendered_json['contract']}\n"
                    f"object={object_name}\n"
                    "stage\tto_yul_contract\tsome\n"
                    "stage\tobject_image\tsome\n"
                    "first_none=none\n"
                    "bytecode_bytes=3\n"
                )

            bridge.run_lake_native_backend_check = fake_run_lake_backend_check
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "lean-backend-check",
                        "--all-contracts",
                        "--lake",
                        "lake",
                        "--lake-cwd",
                        str(root),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_native_backend_check = old_run_lake_backend_check
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["schema"], "evm-compiler.lean-backend-check.v1")
        self.assertEqual(output["counts"]["checkedObjects"], 3)
        self.assertEqual(output["counts"]["passedObjects"], 2)
        self.assertEqual(output["counts"]["failedObjects"], 1)
        self.assertEqual(output["firstNoneCounts"], {"functions_compile": 1})
        self.assertEqual(output["skippedContracts"], ["A.sol:I"])
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["status"])
                for item in output["checkedObjects"]
            ],
            [
                ("A.sol", "A", "creation", "pass"),
                ("A.sol", "A", "runtime", "fail"),
                ("B.sol", "B", "creation", "pass"),
            ],
        )
        self.assertEqual(
            [item["frontend"] for item in output["checkedObjects"]],
            [
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
            ],
        )

    def test_standard_json_all_contracts_bridge_json_writes_manifest_without_lean(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "A.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        )
                    },
                    "I": {"abi": []},
                },
            }
        }
        old_run_solc = bridge.run_solc
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("bridge-json package generation should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                bridge_dir = root / "bridge-json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
                manifest = json.loads((bridge_dir / "manifest.json").read_text())
                bridge_paths_exist = [
                    (bridge_dir / entry["path"]).exists()
                    for entry in manifest["entries"]
                ]
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output["schema"], "evm-compiler.bridge-json-manifest.v1")
        self.assertEqual(output, manifest)
        self.assertEqual(
            output["counts"],
            {"entries": 2, "skippedContracts": 1},
        )
        self.assertEqual(output["skippedContracts"], ["A.sol:I"])
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["object"])
                for item in output["entries"]
            ],
            [
                ("A.sol", "A", "creation", "A_1"),
                ("A.sol", "A", "runtime", "A_1_deployed"),
            ],
        )
        self.assertEqual(bridge_paths_exist, [True, True])

    def test_standard_json_all_contracts_bridge_json_records_frontend_ast_kind(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "A.sol": {
                    "A": {
                        "irOptimizedAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        )
                    },
                },
            }
        }
        captured_inputs = []
        old_run_solc = bridge.run_solc
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            def fake_run_solc(solc, compiler_input, solc_args=()):
                captured_inputs.append(compiler_input)
                return fake_output

            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("bridge-json package generation should not run Lean")

            bridge.run_solc = fake_run_solc
            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                bridge_dir = root / "bridge-json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                        "--optimized",
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
                manifest = json.loads((bridge_dir / "manifest.json").read_text())
                bridge_payloads = [
                    json.loads((bridge_dir / entry["path"]).read_text())
                    for entry in manifest["entries"]
                ]
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output, manifest)
        self.assertIn(
            "irOptimizedAst",
            captured_inputs[0]["settings"]["outputSelection"]["*"]["*"],
        )
        self.assertEqual(
            [entry["frontend"] for entry in manifest["entries"]],
            [
                {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
            ],
        )
        self.assertEqual(
            [payload["frontend"] for payload in bridge_payloads],
            [
                {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irOptimizedAst", "evmVersion": "cancun"},
            ],
        )

    def test_standard_json_all_contracts_bridge_json_writes_skipped_only_manifest(self):
        fake_output = {
            "contracts": {
                "I.sol": {
                    "IFace": {"abi": []},
                    "IOther": {"abi": []},
                },
            },
        }
        old_run_solc = bridge.run_solc
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("bridge-json package generation should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                bridge_dir = root / "bridge-json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {
                                "I.sol": {
                                    "content": "interface IFace {} interface IOther {}"
                                }
                            },
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
                manifest = json.loads((bridge_dir / "manifest.json").read_text())
                bridge_files = list(bridge_dir.glob("*.bridge.json"))
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(output, manifest)
        self.assertEqual(
            output["counts"],
            {"entries": 0, "skippedContracts": 2},
        )
        self.assertEqual(output["entries"], [])
        self.assertEqual(output["skippedContracts"], ["I.sol:IFace", "I.sol:IOther"])
        self.assertEqual(bridge_files, [])

    def test_source_all_contracts_bridge_json_writes_manifest_without_lean(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "Input.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        )
                    },
                    "B": {"irAst": raw_object("B_1")},
                },
                "Imported.sol": {
                    "Imported": {"irAst": raw_object("Imported_1")},
                },
            }
        }
        captured_inputs = []
        old_run_solc = bridge.run_solc
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        old_stdout = sys.stdout
        try:
            def fake_run_solc(solc, compiler_input, solc_args=()):
                captured_inputs.append(compiler_input)
                return fake_output

            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("source bridge package generation should not run Lean")

            bridge.run_solc = fake_run_solc
            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                source = root / "Input.sol"
                source.write_text("contract A {} contract B {}")
                bridge_dir = root / "bridge-json"
                sys.stdout = io.StringIO()
                manifest_path = bridge_dir / "manifest.json"
                result = bridge.main(
                    [
                        str(source),
                        "--source-name",
                        "Input.sol",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                        "--output",
                        str(manifest_path),
                    ]
                )
                output = json.loads(manifest_path.read_text())
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            list(captured_inputs[0]["sources"].keys()),
            ["Input.sol"],
        )
        self.assertEqual(
            output["counts"],
            {"entries": 4, "skippedContracts": 0},
        )
        self.assertEqual(output["skippedContracts"], [])
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["object"])
                for item in output["entries"]
            ],
            [
                ("Input.sol", "A", "creation", "A_1"),
                ("Input.sol", "A", "runtime", "A_1_deployed"),
                ("Input.sol", "B", "creation", "B_1"),
                ("Input.sol", "B", "runtime", "B_1"),
            ],
        )

    def test_source_all_contracts_bridge_json_records_skipped_root_contracts(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "Input.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        )
                    },
                    "I": {"abi": []},
                },
                "Imported.sol": {
                    "Imported": {"abi": []},
                },
            }
        }
        old_run_solc = bridge.run_solc
        old_run_lake_bridge_json_decode = bridge.run_lake_bridge_json_decode
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def unexpected_run_lake_bridge_json_decode(lake, source, cwd):
                raise AssertionError("source bridge package generation should not run Lean")

            bridge.run_lake_bridge_json_decode = unexpected_run_lake_bridge_json_decode
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                source = root / "Input.sol"
                source.write_text("interface I {} contract A {}")
                bridge_dir = root / "bridge-json"
                manifest_path = bridge_dir / "manifest.json"
                result = bridge.main(
                    [
                        str(source),
                        "--source-name",
                        "Input.sol",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                        "--output",
                        str(manifest_path),
                    ]
                )
                output = json.loads(manifest_path.read_text())
        finally:
            bridge.run_solc = old_run_solc
            bridge.run_lake_bridge_json_decode = old_run_lake_bridge_json_decode

        self.assertEqual(result, 0)
        self.assertEqual(
            output["counts"],
            {"entries": 2, "skippedContracts": 1},
        )
        self.assertEqual(output["skippedContracts"], ["Input.sol:I"])
        self.assertNotIn("Imported.sol:Imported", output["skippedContracts"])
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["object"])
                for item in output["entries"]
            ],
            [
                ("Input.sol", "A", "creation", "A_1"),
                ("Input.sol", "A", "runtime", "A_1_deployed"),
            ],
        )

    def test_standard_json_all_contracts_summary_records_uniswap_interface_skips(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "v4-core/src/interfaces/IHooks.sol": {
                    "IHooks": {"abi": []},
                },
                "UniswapV4HooksFallback.sol": {
                    "UniswapV4HooksFallback": {
                        "irAst": raw_object(
                            "UniswapV4HooksFallback_1",
                            [raw_object("UniswapV4HooksFallback_1_deployed")],
                        )
                    },
                },
            }
        }
        old_run_solc = bridge.run_solc
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {
                                "UniswapV4HooksFallback.sol": {
                                    "content": "contract UniswapV4HooksFallback {}"
                                }
                            },
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "bridge-json-summary",
                        "--all-contracts",
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
        finally:
            bridge.run_solc = old_run_solc
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            output["counts"],
            {"objects": 2, "skippedContracts": 1, "calls": 0},
        )
        self.assertEqual(
            output["skippedContracts"],
            ["v4-core/src/interfaces/IHooks.sol:IHooks"],
        )
        self.assertEqual(
            output["skippedContractEntries"],
            [
                {
                    "source": "v4-core/src/interfaces/IHooks.sol",
                    "contract": "IHooks",
                    "reason": "no-yul-ir",
                }
            ],
        )
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"])
                for item in output["objects"]
            ],
            [
                (
                    "UniswapV4HooksFallback.sol",
                    "UniswapV4HooksFallback",
                    "creation",
                ),
                (
                    "UniswapV4HooksFallback.sol",
                    "UniswapV4HooksFallback",
                    "runtime",
                ),
            ],
        )
        self.assertEqual(
            [item["frontend"] for item in output["objects"]],
            [
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
                {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"},
            ],
        )

    def test_standard_json_output_all_contracts_manifest_records_skipped(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "A.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        ),
                        "evm": {
                            "bytecode": {"object": "6000"},
                            "deployedBytecode": {"object": "00"},
                        },
                    },
                    "Base": {
                        "irAst": raw_object("Base_1"),
                        "evm": {
                            "bytecode": {"object": ""},
                            "deployedBytecode": {"object": ""},
                        },
                    },
                    "I": {
                        "abi": [],
                        "evm": {
                            "bytecode": {"object": ""},
                            "deployedBytecode": {"object": ""},
                        },
                    },
                },
            }
        }

        old_run_solc = bridge.run_solc
        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def fake_compile_contract_bytecode_artifact(
                root,
                source_name,
                contract_name,
                definition_prefix,
                namespace,
                object_layout,
                local_data_base,
                linker_symbols,
                lake,
                lake_cwd,
            ):
                runtime = root.subobjects[0] if root.subobjects else root
                return bridge.ContractBytecodeArtifact(
                    source_name,
                    contract_name,
                    root.name,
                    runtime.name,
                    "0x60",
                    "0x00",
                )

            bridge.compile_contract_bytecode_artifact = (
                fake_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                bridge_dir = root / "bridge-json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "standard-json-output",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
                manifest = json.loads((bridge_dir / "manifest.json").read_text())
        finally:
            bridge.run_solc = old_run_solc
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            manifest["counts"],
            {"entries": 2, "skippedContracts": 2},
        )
        self.assertEqual(manifest["skippedContracts"], ["A.sol:Base", "A.sol:I"])
        self.assertEqual(
            [
                (item["source"], item["contract"], item["selector"], item["object"])
                for item in manifest["entries"]
            ],
            [
                ("A.sol", "A", "creation", "A_1"),
                ("A.sol", "A", "runtime", "A_1_deployed"),
            ],
        )
        selected = output["contracts"]["A.sol"]["A"]
        self.assertEqual(selected["evm"]["bytecode"]["object"], "60")
        self.assertEqual(selected["evm"]["deployedBytecode"]["object"], "00")
        self.assertEqual(
            selected["evmCompiler"]["schema"],
            "evm-compiler.solc-standard-json-output.v1",
        )
        bridge_json = selected["evmCompiler"]["bridgeJson"]
        self.assertEqual(
            bridge_json["schema"],
            bridge.BRIDGE_JSON_PROVENANCE_SCHEMA,
        )
        self.assertEqual(
            bridge_json["manifestSchema"],
            bridge.BRIDGE_JSON_MANIFEST_SCHEMA,
        )
        self.assertEqual(
            bridge_json["manifest"],
            str(bridge_dir / "manifest.json"),
        )
        self.assertEqual(bridge_json["entries"]["creation"], manifest["entries"][0])
        self.assertEqual(bridge_json["entries"]["runtime"], manifest["entries"][1])
        self.assertNotIn("evmCompiler", output["contracts"]["A.sol"]["Base"])
        self.assertNotIn("evmCompiler", output["contracts"]["A.sol"]["I"])

    def test_standard_json_output_uses_settings_libraries_as_linker_symbols(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "UsesLibrary.sol": {
                    "UsesLibrary": {
                        "irAst": raw_object(
                            "UsesLibrary_1",
                            [raw_object("UsesLibrary_1_deployed")],
                        ),
                        "evm": {
                            "bytecode": {"object": "6000"},
                            "deployedBytecode": {"object": "00"},
                        },
                    },
                },
            }
        }
        observed_linker_symbols = []

        old_run_solc = bridge.run_solc
        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def fake_compile_contract_bytecode_artifact(
                root,
                source_name,
                contract_name,
                definition_prefix,
                namespace,
                object_layout,
                local_data_base,
                linker_symbols,
                lake,
                lake_cwd,
            ):
                observed_linker_symbols.append(
                    [(entry.name, entry.value) for entry in linker_symbols]
                )
                runtime = root.subobjects[0] if root.subobjects else root
                return bridge.ContractBytecodeArtifact(
                    source_name,
                    contract_name,
                    root.name,
                    runtime.name,
                    "0x60",
                    "0x00",
                )

            bridge.compile_contract_bytecode_artifact = (
                fake_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {
                                "UsesLibrary.sol": {
                                    "content": "contract UsesLibrary {}"
                                }
                            },
                            "settings": {
                                "libraries": {
                                    "MathLib.sol": {
                                        "MathLib": (
                                            "0x000000000000000000000000"
                                            "00000000000000aa"
                                        )
                                    }
                                },
                                "outputSelection": {"*": {"*": ["abi"]}},
                            },
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "standard-json-output",
                        "--all-contracts",
                        "--linker-symbol",
                        "MathLib.sol:MathLib=0x2a",
                    ]
                )
        finally:
            bridge.run_solc = old_run_solc
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            observed_linker_symbols,
            [[("MathLib.sol:MathLib", 42)]],
        )

    @unittest.skipIf(jsonschema is None, "jsonschema package is unavailable")
    def test_standard_json_output_bridge_json_provenance_validates(self):
        def raw_object(name, subobjects=None):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": subobjects or [],
            }

        fake_output = {
            "contracts": {
                "A.sol": {
                    "A": {
                        "irAst": raw_object(
                            "A_1",
                            [raw_object("A_1_deployed")],
                        ),
                        "evm": {
                            "bytecode": {"object": "6000"},
                            "deployedBytecode": {"object": "00"},
                        },
                    },
                },
            }
        }

        old_run_solc = bridge.run_solc
        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def fake_compile_contract_bytecode_artifact(
                root,
                source_name,
                contract_name,
                definition_prefix,
                namespace,
                object_layout,
                local_data_base,
                linker_symbols,
                lake,
                lake_cwd,
            ):
                runtime = root.subobjects[0] if root.subobjects else root
                return bridge.ContractBytecodeArtifact(
                    source_name,
                    contract_name,
                    root.name,
                    runtime.name,
                    "0x60",
                    "0x00",
                )

            bridge.compile_contract_bytecode_artifact = (
                fake_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                bridge_dir = root / "bridge-json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "standard-json-output",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
                provenance = output["contracts"]["A.sol"]["A"]["evmCompiler"][
                    "bridgeJson"
                ]
                provenance_path = root / "standard-json-provenance.json"
                provenance_path.write_text(json.dumps(provenance))
                sys.stdout = io.StringIO()
                validate_result = validate_bridge_json.main([str(provenance_path)])
                validate_output = sys.stdout.getvalue()
        finally:
            bridge.run_solc = old_run_solc
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(validate_result, 0)
        self.assertIn("ok provenance", validate_output)
        self.assertIn("entries=2", validate_output)

    def test_standard_json_output_all_contracts_manifest_records_all_skipped(self):
        def raw_object(name):
            return {
                "nodeType": "YulObject",
                "name": name,
                "code": {"block": {"statements": []}},
                "subObjects": [],
            }

        fake_output = {
            "contracts": {
                "I.sol": {
                    "Base": {
                        "irAst": raw_object("Base_1"),
                        "evm": {
                            "bytecode": {"object": ""},
                            "deployedBytecode": {"object": ""},
                        },
                    },
                    "IFace": {
                        "abi": [{"type": "function", "name": "f"}],
                        "evm": {
                            "bytecode": {"object": ""},
                            "deployedBytecode": {"object": ""},
                        },
                    },
                },
            },
        }

        old_run_solc = bridge.run_solc
        old_compile = bridge.compile_contract_bytecode_artifact
        old_stdout = sys.stdout
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): fake_output

            def unexpected_compile_contract_bytecode_artifact(*args, **kwargs):
                raise AssertionError("non-deployable batch should not invoke Lean")

            bridge.compile_contract_bytecode_artifact = (
                unexpected_compile_contract_bytecode_artifact
            )
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                bridge_dir = root / "bridge-json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {
                                "I.sol": {
                                    "content": "interface IFace {} abstract contract Base {}"
                                }
                            },
                            "settings": {"outputSelection": {"*": {"*": ["abi"]}}},
                        }
                    )
                )
                sys.stdout = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "standard-json-output",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(bridge_dir),
                    ]
                )
                output = json.loads(sys.stdout.getvalue())
                manifest = json.loads((bridge_dir / "manifest.json").read_text())
        finally:
            bridge.run_solc = old_run_solc
            bridge.compile_contract_bytecode_artifact = old_compile
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        self.assertEqual(
            manifest["counts"],
            {"entries": 0, "skippedContracts": 2},
        )
        self.assertEqual(manifest["entries"], [])
        self.assertEqual(manifest["skippedContracts"], ["I.sol:Base", "I.sol:IFace"])
        self.assertEqual(output, fake_output)

    def test_standard_json_all_contracts_bridge_json_requires_output_dir(self):
        old_run_solc = bridge.run_solc
        old_stderr = sys.stderr
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): {
                "contracts": {"A.sol": {"A": {"irAst": {
                    "nodeType": "YulObject",
                    "name": "A_1",
                    "code": {"block": {"statements": []}},
                    "subObjects": [],
                }}}}
            }
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                        }
                    )
                )
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                    ]
                )
                error = sys.stderr.getvalue()
        finally:
            bridge.run_solc = old_run_solc
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("requires --bridge-json-dir", error)

    def test_standard_json_all_contracts_bridge_json_rejects_external_manifest_output(self):
        old_run_solc = bridge.run_solc
        old_stderr = sys.stderr
        try:
            bridge.run_solc = lambda solc, compiler_input, solc_args=(): {
                "contracts": {"A.sol": {"A": {"irAst": {
                    "nodeType": "YulObject",
                    "name": "A_1",
                    "code": {"block": {"statements": []}},
                    "subObjects": [],
                }}}}
            }
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                standard_json = root / "input.json"
                standard_json.write_text(
                    json.dumps(
                        {
                            "language": "Solidity",
                            "sources": {"A.sol": {"content": "contract A {}"}},
                        }
                    )
                )
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        str(standard_json),
                        "--input-format",
                        "standard-json",
                        "--format",
                        "bridge-json",
                        "--all-contracts",
                        "--bridge-json-dir",
                        str(root / "bridge-json"),
                        "--output",
                        str(root / "manifest.json"),
                    ]
                )
                error = sys.stderr.getvalue()
        finally:
            bridge.run_solc = old_run_solc
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertIn("paths are relative to --bridge-json-dir", error)

    def test_parse_object_image_output_records_immutable_references(self):
        image = bridge.parse_object_image_output(
            "timing\tdecode\t3\n"
            "timing\tobject_image\t7\n"
            "bytecode=0x6000\n"
            "immutable\t3\t12\t32\n"
            "immutable\t3\t44\t32\n"
            "immutable\t7\t80\t32\n"
        )

        self.assertEqual(image.bytecode, "0x6000")
        self.assertEqual(
            image.immutable_references,
            {
                "3": [{"start": 12, "length": 32}, {"start": 44, "length": 32}],
                "7": [{"start": 80, "length": 32}],
            },
        )

    def test_bytecode_artifact_json_records_creation_and_runtime(self):
        compatibility = {
            "profile": "current-yul-compiler",
            "status": "ready",
            "unsupportedPrimitiveNames": [],
            "objectBuiltinNames": [],
            "dialectBuiltinNames": [],
            "notes": [],
        }
        bridge_json = {
            "schema": bridge.BRIDGE_JSON_PROVENANCE_SCHEMA,
            "manifestSchema": bridge.BRIDGE_JSON_MANIFEST_SCHEMA,
            "manifest": "/tmp/bridge-json/manifest.json",
            "entries": {
                "creation": {"path": "Simple.creation.bridge.json"},
                "runtime": {"path": "Simple.runtime.bridge.json"},
            },
        }
        artifact = json.loads(
            bridge.render_bytecode_artifact_json(
                "stdin.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                "0x6000",
                "0x00",
                {"3": [{"start": 12, "length": 32}]},
                compatibility,
                bridge_json,
            )
        )
        self.assertEqual(
            artifact["schema"],
            "evm-compiler.solidity-bytecode-artifact.v1",
        )
        self.assertEqual(artifact["source"], "stdin.sol")
        self.assertEqual(artifact["contract"], "Simple")
        self.assertEqual(artifact["yul"]["creationObject"], "Simple_14")
        self.assertEqual(artifact["yul"]["runtimeObject"], "Simple_14_deployed")
        self.assertEqual(artifact["bytecode"]["creation"], "0x6000")
        self.assertEqual(artifact["bytecode"]["runtime"], "0x00")
        self.assertEqual(
            artifact["immutableReferences"]["runtime"],
            {"3": [{"start": 12, "length": 32}]},
        )
        self.assertEqual(artifact["sizes"]["creationBytes"], 2)
        self.assertEqual(artifact["sizes"]["runtimeBytes"], 1)
        self.assertEqual(artifact["backendCompatibility"], compatibility)
        self.assertEqual(artifact["bridgeJson"], bridge_json)

    def test_bytecode_artifact_rejects_non_lowercase_hex(self):
        with self.assertRaises(bridge.ConversionError):
            bridge.render_bytecode_artifact_json(
                "Simple.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                "0x6000",
                "0xAA",
            )

    def test_forge_artifact_json_replaces_bytecode_but_keeps_abi_metadata(self):
        compatibility = {
            "profile": "current-yul-compiler",
            "status": "ready",
            "unsupportedPrimitiveNames": [],
            "objectBuiltinNames": ["dataoffset"],
            "dialectBuiltinNames": [],
            "notes": ["computed object/data builtins are resolved by the object-image path"],
        }
        bridge_json = {
            "schema": bridge.BRIDGE_JSON_PROVENANCE_SCHEMA,
            "manifestSchema": bridge.BRIDGE_JSON_MANIFEST_SCHEMA,
            "manifest": "/tmp/bridge-json/manifest.json",
            "entries": {
                "creation": {"path": "Simple.creation.bridge.json"},
                "runtime": {"path": "Simple.runtime.bridge.json"},
            },
        }
        artifact = json.loads(
            bridge.render_forge_artifact_json(
                "Simple.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                {
                    "abi": [{"type": "function", "name": "f"}],
                    "metadata": '{"language":"Solidity"}',
                    "evm": {"methodIdentifiers": {"f()": "26121ff0"}},
                },
                "0x6000",
                "0x00",
                {"3": [{"start": 12, "length": 32}]},
                compatibility,
                bridge_json,
            )
        )
        self.assertEqual(artifact["abi"], [{"type": "function", "name": "f"}])
        self.assertEqual(artifact["bytecode"]["object"], "0x6000")
        self.assertEqual(artifact["deployedBytecode"]["object"], "0x00")
        self.assertEqual(
            artifact["deployedBytecode"]["immutableReferences"],
            {"3": [{"start": 12, "length": 32}]},
        )
        self.assertEqual(artifact["bytecode"]["sourceMap"], "")
        self.assertEqual(artifact["methodIdentifiers"], {"f()": "26121ff0"})
        self.assertEqual(artifact["metadata"], {"language": "Solidity"})
        self.assertEqual(artifact["rawMetadata"], '{"language":"Solidity"}')
        self.assertEqual(
            artifact["evmCompiler"]["schema"],
            "evm-compiler.forge-artifact.v1",
        )
        self.assertEqual(artifact["evmCompiler"]["sizes"]["creationBytes"], 2)
        self.assertEqual(artifact["evmCompiler"]["sizes"]["runtimeBytes"], 1)
        self.assertEqual(
            artifact["evmCompiler"]["backendCompatibility"],
            compatibility,
        )
        self.assertEqual(artifact["evmCompiler"]["bridgeJson"], bridge_json)

    def test_standard_json_output_replaces_selected_contract_bytecode(self):
        compatibility = {
            "profile": "current-yul-compiler",
            "status": "ready",
            "unsupportedPrimitiveNames": [],
            "objectBuiltinNames": [],
            "dialectBuiltinNames": [],
            "notes": [
                "CALL/CALLCODE/DELEGATECALL/STATICCALL and CREATE/CREATE2 are "
                "covered by the open external-boundary proof surface"
            ],
        }
        bridge_json = {
            "schema": bridge.BRIDGE_JSON_PROVENANCE_SCHEMA,
            "manifestSchema": bridge.BRIDGE_JSON_MANIFEST_SCHEMA,
            "manifest": "/tmp/bridge-json/manifest.json",
            "entries": {
                "creation": {"path": "Simple.creation.bridge.json"},
                "runtime": {"path": "Simple.runtime.bridge.json"},
            },
        }
        solc_output = {
            "errors": [{"severity": "warning", "message": "kept"}],
            "contracts": {
                "Simple.sol": {
                    "Simple": {
                        "abi": [{"type": "function", "name": "f"}],
                        "evm": {
                            "bytecode": {
                                "object": "deadbeef",
                                "sourceMap": "1:2:3",
                                "linkReferences": {
                                    "Lib.sol": {"Lib": [{"start": 1, "length": 20}]}
                                },
                                "generatedSources": [{"id": 1, "name": "#utility"}],
                            },
                            "deployedBytecode": {
                                "object": "beef",
                                "sourceMap": "4:5:6",
                                "linkReferences": {
                                    "RunLib.sol": {
                                        "RunLib": [{"start": 3, "length": 20}]
                                    }
                                },
                                "generatedSources": [{"id": 2, "name": "#runtime"}],
                            },
                        },
                    },
                    "Other": {
                        "evm": {
                            "bytecode": {"object": "1111"},
                            "deployedBytecode": {"object": "22"},
                        }
                    },
                }
            },
        }
        rendered = json.loads(
            bridge.render_standard_json_output(
                solc_output,
                "Simple.sol",
                "Simple",
                "Simple_14",
                "Simple_14_deployed",
                "0x6000",
                "0x00",
                {"3": [{"start": 12, "length": 32}]},
                compatibility,
                bridge_json,
            )
        )

        selected = rendered["contracts"]["Simple.sol"]["Simple"]
        self.assertEqual(selected["evm"]["bytecode"]["object"], "6000")
        self.assertEqual(selected["evm"]["bytecode"]["sourceMap"], "")
        self.assertEqual(selected["evm"]["bytecode"]["linkReferences"], {})
        self.assertEqual(selected["evm"]["bytecode"]["generatedSources"], [])
        self.assertEqual(selected["evm"]["deployedBytecode"]["object"], "00")
        self.assertEqual(selected["evm"]["deployedBytecode"]["sourceMap"], "")
        self.assertEqual(selected["evm"]["deployedBytecode"]["linkReferences"], {})
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["generatedSources"],
            [],
        )
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["immutableReferences"],
            {"3": [{"start": 12, "length": 32}]},
        )
        self.assertEqual(selected["abi"], [{"type": "function", "name": "f"}])
        self.assertEqual(
            selected["evmCompiler"]["schema"],
            "evm-compiler.solc-standard-json-output.v1",
        )
        self.assertEqual(selected["evmCompiler"]["sizes"]["creationBytes"], 2)
        self.assertEqual(selected["evmCompiler"]["sizes"]["runtimeBytes"], 1)
        self.assertEqual(
            selected["evmCompiler"]["backendCompatibility"],
            compatibility,
        )
        self.assertEqual(selected["evmCompiler"]["bridgeJson"], bridge_json)
        other = rendered["contracts"]["Simple.sol"]["Other"]
        self.assertEqual(other["evm"]["bytecode"]["object"], "1111")
        self.assertEqual(
            solc_output["contracts"]["Simple.sol"]["Simple"]["evm"]["bytecode"][
                "object"
            ],
            "deadbeef",
        )

    def test_standard_json_outputs_replaces_multiple_contracts(self):
        rendered = json.loads(
            bridge.render_standard_json_outputs(
                {
                    "contracts": {
                        "A.sol": {
                            "A": {"evm": {"bytecode": {}, "deployedBytecode": {}}},
                        },
                        "B.sol": {
                            "B": {"evm": {"bytecode": {}, "deployedBytecode": {}}},
                        },
                    }
                },
                [
                    bridge.ContractBytecodeArtifact(
                        "A.sol",
                        "A",
                        "A_1",
                        "A_1_deployed",
                        "0x60",
                        "0x00",
                    ),
                    bridge.ContractBytecodeArtifact(
                        "B.sol",
                        "B",
                        "B_1",
                        "B_1_deployed",
                        "0x6000",
                        "0x01",
                        {"9": [{"start": 4, "length": 32}]},
                    ),
                ],
            )
        )
        selected_a = rendered["contracts"]["A.sol"]["A"]
        selected_b = rendered["contracts"]["B.sol"]["B"]
        self.assertEqual(selected_a["evm"]["bytecode"]["object"], "60")
        self.assertEqual(selected_a["evm"]["deployedBytecode"]["object"], "00")
        self.assertEqual(selected_b["evm"]["bytecode"]["object"], "6000")
        self.assertEqual(selected_b["evm"]["deployedBytecode"]["object"], "01")
        self.assertEqual(
            selected_b["evm"]["deployedBytecode"]["immutableReferences"],
            {"9": [{"start": 4, "length": 32}]},
        )
        self.assertEqual(selected_b["evmCompiler"]["sizes"]["creationBytes"], 2)

    def test_standard_json_output_clears_stale_immutable_references(self):
        rendered = json.loads(
            bridge.render_standard_json_outputs(
                {
                    "contracts": {
                        "A.sol": {
                            "A": {
                                "evm": {
                                    "bytecode": {},
                                    "deployedBytecode": {
                                        "immutableReferences": {
                                            "3": [{"start": 97, "length": 32}]
                                        }
                                    },
                                }
                            }
                        }
                    }
                },
                [
                    bridge.ContractBytecodeArtifact(
                        "A.sol",
                        "A",
                        "A_1",
                        "A_1_deployed",
                        "0x60",
                        "0x00",
                    ),
                ],
            )
        )

        selected = rendered["contracts"]["A.sol"]["A"]
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["immutableReferences"],
            {},
        )

    def test_compile_contract_artifact_records_yul_backend_compatibility(self):
        old_compile_frontend_object_image = bridge.compile_frontend_object_image
        try:
            def fake_compile_frontend_object_image(
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
            ):
                return bridge.CompiledObjectImage(bytecode="0x00")

            bridge.compile_frontend_object_image = fake_compile_frontend_object_image
            root = bridge.YulObject(
                "Calls_1",
                [
                    bridge.ExprStmt(
                        bridge.Call("call", [], bridge.CALL_PRIMITIVE)
                    )
                ],
                [],
                [],
                [
                    bridge.YulObject(
                        "Calls_1_deployed",
                        [
                            bridge.ExprStmt(
                                bridge.Call("mstore", [], bridge.CALL_PRIMITIVE)
                            )
                        ],
                        [],
                        [],
                        [],
                    )
                ],
            )
            artifact = bridge.compile_contract_bytecode_artifact(
                root,
                "Calls.sol",
                "Calls",
                "Calls",
                None,
                [],
                None,
                [],
                "lake",
                Path("."),
            )
        finally:
            bridge.compile_frontend_object_image = old_compile_frontend_object_image

        compatibility = artifact.backend_compatibility
        self.assertIsNotNone(compatibility)
        self.assertEqual(compatibility["status"], "ready")
        self.assertEqual(compatibility["unsupportedPrimitiveNames"], [])
        self.assertEqual(compatibility["objectBuiltinNames"], [])

    def test_compile_contract_artifact_defaults_unresolved_linker_symbols_to_zero(self):
        old_compile_frontend_object_image = bridge.compile_frontend_object_image
        calls = []
        try:
            def fake_compile_frontend_object_image(
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
            ):
                calls.append(
                    (
                        definition,
                        {entry.name: entry.value for entry in linker_symbols},
                    )
                )
                return bridge.CompiledObjectImage(bytecode="0x00")

            bridge.compile_frontend_object_image = fake_compile_frontend_object_image
            root = bridge.YulObject(
                "UsesLibraries_1",
                [
                    bridge.Let(
                        ["creationLib"],
                        bridge.Call(
                            "linkersymbol",
                            [bridge.StringLit("CreationLib.sol:CreationLib")],
                            bridge.CALL_OBJECT_BUILTIN,
                        ),
                    )
                ],
                [],
                [],
                [
                    bridge.YulObject(
                        "UsesLibraries_1_deployed",
                        [
                            bridge.Let(
                                ["runtimeLib"],
                                bridge.Call(
                                    "linkersymbol",
                                    [bridge.StringLit("RuntimeLib.sol:RuntimeLib")],
                                    bridge.CALL_OBJECT_BUILTIN,
                                ),
                            )
                        ],
                        [],
                        [],
                        [],
                    )
                ],
            )
            bridge.compile_contract_bytecode_artifact(
                root,
                "UsesLibraries.sol",
                "UsesLibraries",
                "UsesLibraries",
                None,
                [],
                None,
                [bridge.LinkerSymbolEntry("RuntimeLib.sol:RuntimeLib", 42)],
                "lake",
                Path("."),
            )
        finally:
            bridge.compile_frontend_object_image = old_compile_frontend_object_image

        self.assertEqual(len(calls), 2)
        creation_symbols = calls[0][1]
        runtime_symbols = calls[1][1]
        self.assertEqual(
            creation_symbols["CreationLib.sol:CreationLib"],
            0,
        )
        self.assertEqual(
            creation_symbols["RuntimeLib.sol:RuntimeLib"],
            42,
        )
        self.assertEqual(
            runtime_symbols["RuntimeLib.sol:RuntimeLib"],
            42,
        )
        self.assertNotIn("CreationLib.sol:CreationLib", runtime_symbols)

    def test_parser_accepts_artifact_formats(self):
        args = bridge.build_arg_parser().parse_args(
            [
                "-",
                "--source-name",
                "Input.sol",
                "--include-source",
                "MathLib.sol=examples/MathLib.sol",
                "--remapping",
                "@pkg/=lib/pkg/src/",
                "--remappings-file",
                "remappings.txt",
                "--linker-symbol",
                "MathLib.sol:MathLib=0x0",
                "--solc-arg=--base-path",
                "--solc-arg",
                ".",
                "--format",
                "bytecode-artifact",
                "--no-auto-include-imports",
            ]
        )
        self.assertEqual(str(args.input), "-")
        self.assertEqual(args.source_name, "Input.sol")
        self.assertEqual(args.include_source, ["MathLib.sol=examples/MathLib.sol"])
        self.assertEqual(args.remapping, ["@pkg/=lib/pkg/src/"])
        self.assertEqual(args.remappings_file, [Path("remappings.txt")])
        self.assertEqual(args.linker_symbol, ["MathLib.sol:MathLib=0x0"])
        self.assertEqual(args.solc_arg, ["--base-path", "."])
        self.assertEqual(args.format, "bytecode-artifact")
        self.assertFalse(args.auto_include_imports)
        forge_args = bridge.build_arg_parser().parse_args(
            [
                "examples/Simple.sol",
                "--contract",
                "Simple",
                "--format",
                "forge-artifact",
            ]
        )
        self.assertEqual(forge_args.format, "forge-artifact")
        standard_json_output_args = bridge.build_arg_parser().parse_args(
            [
                "examples/Simple.sol",
                "--contract",
                "Simple",
                "--format",
                "standard-json-output",
            ]
        )
        self.assertEqual(standard_json_output_args.format, "standard-json-output")
        self.assertFalse(standard_json_output_args.all_contracts)
        all_contract_args = bridge.build_arg_parser().parse_args(
            [
                "-",
                "--input-format",
                "standard-json",
                "--format",
                "standard-json-output",
                "--all-contracts",
            ]
        )
        self.assertTrue(all_contract_args.all_contracts)
        standard_json_args = bridge.build_arg_parser().parse_args(
            [
                "-",
                "--input-format",
                "standard-json",
                "--contract",
                "Simple",
                "--format",
                "bridge-json",
            ]
        )
        self.assertEqual(standard_json_args.input_format, "standard-json")
        bridge_json_args = bridge.build_arg_parser().parse_args(
            [
                "Simple.bridge.json",
                "--input-format",
                "bridge-json",
                "--format",
                "bytecode",
            ]
        )
        self.assertEqual(bridge_json_args.input_format, "bridge-json")
        bridge_json_manifest_args = bridge.build_arg_parser().parse_args(
            [
                "manifest.json",
                "--input-format",
                "bridge-json-manifest",
                "--format",
                "lean-json-check",
            ]
        )
        self.assertEqual(
            bridge_json_manifest_args.input_format,
            "bridge-json-manifest",
        )
        json_ir_args = bridge.build_arg_parser().parse_args(
            ["Simple.sol", "--format", "lean-json-ir"]
        )
        self.assertEqual(json_ir_args.format, "lean-json-ir")
        lean_json_check_args = bridge.build_arg_parser().parse_args(
            [
                "Simple.bridge.json",
                "--input-format",
                "bridge-json",
                "--format",
                "lean-json-check",
            ]
        )
        self.assertEqual(lean_json_check_args.format, "lean-json-check")

    @staticmethod
    def _wrapper_solc_output(creation="aaaa", runtime="bbbb"):
        return {
            "contracts": {
                "A.sol": {
                    "A": {
                        "abi": [],
                        "irOptimizedAst": {
                            "nodeType": "YulObject",
                            "name": "A_1",
                            "code": {
                                "block": {
                                    "nodeType": "YulBlock",
                                    "statements": [],
                                }
                            },
                            "subObjects": [
                                {
                                    "nodeType": "YulObject",
                                    "name": "A_1_deployed",
                                    "code": {
                                        "block": {
                                            "nodeType": "YulBlock",
                                            "statements": [],
                                        }
                                    },
                                    "subObjects": [],
                                }
                            ],
                        },
                        "evm": {
                            "bytecode": {"object": creation},
                            "deployedBytecode": {"object": runtime},
                        },
                    }
                }
            }
        }

    def run_wrapper_standard_json(
        self,
        solc_output,
        argv=None,
        backend_stdout="bytecode=0x6000\nbytecode_bytes=2\n",
        backend_returncode=0,
        env=None,
        input_text='{"language":"Solidity","sources":{}}',
    ):
        old_run = solc_lean_wrapper.subprocess.run
        old_stdin = sys.stdin
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        old_env = dict(os.environ)
        calls = []
        try:
            def fake_run(command, **kwargs):
                calls.append((list(command), kwargs))

                class Completed:
                    pass

                completed = Completed()
                if "--standard-json" in command:
                    completed.returncode = 0
                    completed.stdout = (
                        solc_output
                        if isinstance(solc_output, str)
                        else json.dumps(solc_output)
                    )
                    completed.stderr = ""
                else:
                    completed.returncode = backend_returncode
                    completed.stdout = backend_stdout
                    completed.stderr = (
                        "" if backend_returncode == 0 else "backend diagnostic"
                    )
                return completed

            solc_lean_wrapper.subprocess.run = fake_run
            sys.stdin = io.StringIO(input_text)
            sys.stdout = io.StringIO()
            sys.stderr = io.StringIO()
            os.environ.clear()
            os.environ.update(
                env
                if env is not None
                else {
                    "SOLC_LEAN_REAL_SOLC": "/tmp/real-solc",
                    "SOLC_LEAN_VALIDATE_OUTPUT": "0",
                }
            )
            result = solc_lean_wrapper.main(argv or ["--standard-json"])
            output = sys.stdout.getvalue()
            error = sys.stderr.getvalue()
        finally:
            solc_lean_wrapper.subprocess.run = old_run
            sys.stdin = old_stdin
            sys.stdout = old_stdout
            sys.stderr = old_stderr
            os.environ.clear()
            os.environ.update(old_env)
        return result, output, error, calls

    def test_solc_lean_wrapper_compiles_via_raw_backend(self):
        result, output, _, calls = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            argv=["--standard-json", "--base-path", "."],
        )
        self.assertEqual(result, 0)
        solc_command = calls[0][0]
        self.assertEqual(solc_command[0], "/tmp/real-solc")
        self.assertIn("--standard-json", solc_command)
        self.assertIn("--base-path", solc_command)
        self.assertIn(".", solc_command)
        solc_input = json.loads(calls[0][1]["input"])
        self.assertTrue(solc_input["settings"]["viaIR"])
        star_selection = solc_input["settings"]["outputSelection"]["*"]["*"]
        self.assertIn("irOptimizedAst", star_selection)
        self.assertIn("evm.bytecode.object", star_selection)
        self.assertIn("evm.deployedBytecode.object", star_selection)
        backend_calls = [command for command, _ in calls[1:]]
        self.assertEqual(len(backend_calls), 2)
        for command, selector in zip(backend_calls, ["creation", "runtime"]):
            self.assertEqual(
                command[:4],
                [
                    solc_lean_wrapper.default_lake(),
                    "exe",
                    "solidus-backend",
                    "raw-image",
                ],
            )
            self.assertEqual(command[5:], ["A.sol", "A", selector])
        rendered = json.loads(output)
        selected = rendered["contracts"]["A.sol"]["A"]
        self.assertEqual(selected["evm"]["bytecode"]["object"], "6000")
        self.assertEqual(selected["evm"]["deployedBytecode"]["object"], "6000")
        self.assertEqual(
            selected["evmCompiler"]["schema"],
            "evm-compiler.solc-standard-json-output.v1",
        )
        self.assertEqual(
            selected["evmCompiler"]["yul"],
            {"creationObject": "A_1", "runtimeObject": "A_1_deployed"},
        )
        self.assertNotIn("irOptimizedAst", selected)

    def test_solc_lean_wrapper_parses_immutable_references(self):
        result, output, _, calls = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            backend_stdout=(
                "bytecode=0x6000\nimmutable\t7\t2\t32\nbytecode_bytes=2\n"
            ),
        )
        self.assertEqual(result, 0)
        rendered = json.loads(output)
        selected = rendered["contracts"]["A.sol"]["A"]
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["immutableReferences"],
            {"7": [{"start": 2, "length": 32}]},
        )

    def test_solc_lean_wrapper_parses_link_references(self):
        result, output, _, calls = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            backend_stdout=(
                "bytecode=0x6000\n"
                "immutable\tA.sol:Lib\t2\t32\n"
                "linkref\tA.sol:Lib\t14\t20\n"
                "linkref\tA.sol:Lib\t50\t20\n"
                "bytecode_bytes=2\n"
            ),
        )
        self.assertEqual(result, 0)
        rendered = json.loads(output)
        selected = rendered["contracts"]["A.sol"]["A"]
        expected = {
            "A.sol": {
                "Lib": [
                    {"start": 14, "length": 20},
                    {"start": 50, "length": 20},
                ]
            }
        }
        self.assertEqual(
            selected["evm"]["bytecode"]["linkReferences"], expected
        )
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["linkReferences"], expected
        )
        # Unlinked library marker groups are not immutables in solc's shape.
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["immutableReferences"], {}
        )

    def test_solc_lean_wrapper_link_references_empty_when_linked(self):
        result, output, _, _ = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            backend_stdout="bytecode=0x6000\nbytecode_bytes=2\n",
        )
        self.assertEqual(result, 0)
        rendered = json.loads(output)
        selected = rendered["contracts"]["A.sol"]["A"]
        self.assertEqual(selected["evm"]["bytecode"]["linkReferences"], {})
        self.assertEqual(
            selected["evm"]["deployedBytecode"]["linkReferences"], {}
        )

    def test_solc_link_references_shape(self):
        shaped = solc_lean_wrapper.solc_link_references(
            {
                "src/lib/ScaleLib.sol:ScaleLib": [
                    {"start": 12, "length": 20}
                ],
                "src/lib/Other.sol:Other": [{"start": 90, "length": 20}],
            }
        )
        self.assertEqual(
            shaped,
            {
                "src/lib/ScaleLib.sol": {
                    "ScaleLib": [{"start": 12, "length": 20}]
                },
                "src/lib/Other.sol": {
                    "Other": [{"start": 90, "length": 20}]
                },
            },
        )

    def test_solc_lean_wrapper_preserves_requested_ir_output(self):
        result, output, _, _ = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            input_text=json.dumps(
                {
                    "language": "Solidity",
                    "sources": {},
                    "settings": {
                        "outputSelection": {
                            "*": {"*": ["abi", "irOptimizedAst"]}
                        }
                    },
                }
            ),
        )
        self.assertEqual(result, 0)
        rendered = json.loads(output)
        self.assertIn("irOptimizedAst", rendered["contracts"]["A.sol"]["A"])

    def test_solc_lean_wrapper_fails_when_raw_backend_fails(self):
        result, output, error, _ = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            backend_returncode=1,
        )
        self.assertEqual(result, 1)
        self.assertEqual(output, "")
        self.assertIn("verified raw backend failed", error)
        self.assertIn("backend diagnostic", error)

    def test_solc_lean_wrapper_skips_non_deployable_contracts(self):
        solc_output = {
            "contracts": {
                "I.sol": {
                    "I": {"abi": [{"type": "function", "name": "f"}]},
                    "Base": {"abi": []},
                }
            },
            "sources": {"I.sol": {"id": 0}},
        }
        result, output, _, calls = self.run_wrapper_standard_json(solc_output)
        self.assertEqual(result, 0)
        self.assertEqual(len(calls), 1)
        self.assertEqual(json.loads(output), solc_output)

    def test_solc_lean_wrapper_passes_through_solc_errors(self):
        solc_output = {
            "errors": [
                {
                    "severity": "error",
                    "message": "ParserError: expected ';'",
                }
            ]
        }
        result, output, _, calls = self.run_wrapper_standard_json(solc_output)
        self.assertEqual(result, 0)
        self.assertEqual(len(calls), 1)
        self.assertEqual(json.loads(output), solc_output)

    def test_solc_lean_wrapper_notes_retired_bridge_json_dir(self):
        result, _, error, _ = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            env={
                "SOLC_LEAN_REAL_SOLC": "/tmp/real-solc",
                "SOLC_LEAN_VALIDATE_OUTPUT": "0",
                "SOLC_LEAN_BRIDGE_JSON_DIR": "/tmp/bridge-json",
            },
        )
        self.assertEqual(result, 0)
        self.assertIn("SOLC_LEAN_BRIDGE_JSON_DIR is ignored", error)

    def test_solc_lean_wrapper_delegates_non_standard_json_probe(self):
        old_run = solc_lean_wrapper.subprocess.run
        old_env = dict(os.environ)
        calls = []
        try:
            class Completed:
                returncode = 7

            def fake_run(command):
                calls.append(command)
                return Completed()

            solc_lean_wrapper.subprocess.run = fake_run
            os.environ.clear()
            os.environ.update({"SOLC_LEAN_REAL_SOLC": "/tmp/real-solc"})
            result = solc_lean_wrapper.main(["--version"])
        finally:
            solc_lean_wrapper.subprocess.run = old_run
            os.environ.clear()
            os.environ.update(old_env)

        self.assertEqual(result, 7)
        self.assertEqual(calls, [["/tmp/real-solc", "--version"]])

    def test_solc_lean_wrapper_reports_missing_real_solc_for_probe(self):
        old_run = solc_lean_wrapper.subprocess.run
        old_stderr = sys.stderr
        old_env = dict(os.environ)
        try:
            def fake_run(command):
                raise FileNotFoundError(command[0])

            solc_lean_wrapper.subprocess.run = fake_run
            sys.stderr = io.StringIO()
            os.environ.clear()
            os.environ.update({"SOLC_LEAN_REAL_SOLC": "/tmp/missing-solc"})
            result = solc_lean_wrapper.main(["--version"])
            error = sys.stderr.getvalue()
        finally:
            solc_lean_wrapper.subprocess.run = old_run
            sys.stderr = old_stderr
            os.environ.clear()
            os.environ.update(old_env)

        self.assertEqual(result, 1)
        self.assertIn("could not find real solc executable", error)
        self.assertIn("SOLC_LEAN_REAL_SOLC", error)

    def test_solc_lean_wrapper_validates_standard_json_output(self):
        try:
            import jsonschema  # noqa: F401
        except ImportError:
            self.skipTest("jsonschema is not installed")
        result, output, _, _ = self.run_wrapper_standard_json(
            self._wrapper_solc_output(),
            env={"SOLC_LEAN_REAL_SOLC": "/tmp/real-solc"},
        )
        self.assertEqual(result, 0)
        selected = json.loads(output)["contracts"]["A.sol"]["A"]
        self.assertEqual(selected["evm"]["bytecode"]["object"], "6000")

    def test_solc_lean_wrapper_rejects_invalid_standard_json_output(self):
        old_validate = solc_lean_wrapper.validate_standard_json_output
        try:
            solc_lean_wrapper.validate_standard_json_output = lambda output: 3
            result, output, error, _ = self.run_wrapper_standard_json(
                self._wrapper_solc_output(),
                env={"SOLC_LEAN_REAL_SOLC": "/tmp/real-solc"},
            )
        finally:
            solc_lean_wrapper.validate_standard_json_output = old_validate
        self.assertEqual(result, 3)
        self.assertEqual(output, "")
        self.assertIn("invalid Standard JSON output", error)

    def test_solc_lean_wrapper_can_skip_output_validation(self):
        result, output, _, _ = self.run_wrapper_standard_json('{"contracts":{}}')
        self.assertEqual(result, 0)
        self.assertEqual(json.loads(output), {"contracts": {}})

    def test_artifact_formats_refuse_without_unverified_diagnostic(self):
        old_env = os.environ.get("EVM_COMPILER_UNVERIFIED_DIAGNOSTIC")
        old_stderr = sys.stderr
        try:
            if old_env is not None:
                del os.environ["EVM_COMPILER_UNVERIFIED_DIAGNOSTIC"]
            for artifact_format in sorted(bridge.UNVERIFIED_ARTIFACT_FORMATS):
                sys.stderr = io.StringIO()
                result = bridge.main(
                    [
                        "ignored.sol",
                        "--format",
                        artifact_format,
                    ]
                )
                error = sys.stderr.getvalue()
                self.assertEqual(result, 1)
                self.assertIn("unverified Python Yul translation", error)
                self.assertIn("--unverified-diagnostic", error)
                self.assertIn("raw", error)
        finally:
            sys.stderr = old_stderr
            if old_env is not None:
                os.environ["EVM_COMPILER_UNVERIFIED_DIAGNOSTIC"] = old_env

    def test_famous_repo_smoke_runner_keeps_pinned_uniswap_coverage(self):
        scripts_dir = Path(__file__).resolve().parent
        runner = (scripts_dir / "test_famous_repo_bridge_smokes.sh").read_text()
        self.assertIn("test_uniswap_v4_extload_summary_smoke.sh", runner)
        self.assertIn("test_uniswap_v4_bridge_smoke.sh", runner)
        self.assertIn("test_uniswap_v4_position_bridge_smoke.sh", runner)
        self.assertIn("test_uniswap_universal_router_smoke.sh", runner)
        self.assertIn("test_uniswap_permit2_bridge_smoke.sh", runner)
        self.assertIn("test_aave_v3_bridge_smoke.sh", runner)
        self.assertIn("test_solmate_bridge_smoke.sh", runner)
        self.assertIn("test_solady_bridge_smoke.sh", runner)
        self.assertIn("test_openzeppelin_bridge_smoke.sh", runner)
        self.assertIn("test_chainlink_cbor_bridge_smoke.sh", runner)
        self.assertIn("test_additional_real_contracts_bridge_smoke.sh", runner)
        self.assertIn("test_protocol_diversity_bridge_smoke.sh", runner)

        v4_extload_smoke = (
            scripts_dir / "test_uniswap_v4_extload_summary_smoke.sh"
        ).read_text()
        v4_smoke = (scripts_dir / "test_uniswap_v4_bridge_smoke.sh").read_text()
        v4_position_smoke = (
            scripts_dir / "test_uniswap_v4_position_bridge_smoke.sh"
        ).read_text()
        universal_router_smoke = (
            scripts_dir / "test_uniswap_universal_router_smoke.sh"
        ).read_text()
        permit2_smoke = (
            scripts_dir / "test_uniswap_permit2_bridge_smoke.sh"
        ).read_text()

        self.assertRegex(
            v4_smoke,
            r"UNISWAP_V4_REF=\"\$\{UNISWAP_V4_REF:-[0-9a-f]{40}\}\"",
        )
        self.assertRegex(
            v4_extload_smoke,
            r"UNISWAP_V4_REF=\"\$\{UNISWAP_V4_REF:-[0-9a-f]{40}\}\"",
        )
        self.assertRegex(
            v4_position_smoke,
            r"UNISWAP_V4_REF=\"\$\{UNISWAP_V4_REF:-[0-9a-f]{40}\}\"",
        )
        self.assertRegex(
            universal_router_smoke,
            (
                r"UNISWAP_UNIVERSAL_ROUTER_REF=\"\$\{"
                r"UNISWAP_UNIVERSAL_ROUTER_REF:-[0-9a-f]{40}\}\""
            ),
        )
        self.assertRegex(
            permit2_smoke,
            (
                r"UNISWAP_PERMIT2_REF=\"\$\{"
                r"UNISWAP_PERMIT2_REF:-[0-9a-f]{40}\}\""
            ),
        )
        for behavior in [
            "Extsload",
            "Exttload",
            "tstore(slot, value)",
            "tload",
            "uniswap_v4_extload_frontend_metadata=yes",
            "uniswap_v4_extload_summary_primitives=yes",
        ]:
            self.assertIn(behavior, v4_extload_smoke)
        for behavior in [
            "SwapMath.getSqrtPriceTarget",
            "FullMath.mulDiv",
            "LiquidityMath.addDelta",
            "LPFeeLibrary",
            "BitMath",
            "CurrencyDelta",
            "Lock",
            "ProtocolFeeLibrary",
            "SafeCast",
        ]:
            self.assertIn(behavior, v4_smoke)
        for behavior in [
            "Position.calculatePositionKey",
            "positions.get(owner, tickLower, tickUpper, salt)",
            "position.update(0, 3 * Q128, 5 * Q128)",
            "type(uint256).max - Q128 + 1",
            "CannotUpdateEmptyPosition",
            "compare_contract_call_bytecode.py",
            "--contract UniswapV4PositionFallback",
            "--runtime-only",
            "--format lean-backend-check",
            '!= ("pass", "none")',
            "uniswap_v4_position_runtime_backend_check=",
            "uniswap_v4_position_runtime_backend_first_none=",
            "uniswap_v4_position_runtime_compare=",
            "uniswap_v4_position_compare_calls=",
            "uniswap_v4_position_storage_behavior=yes",
            "irOptimizedAst",
        ]:
            self.assertIn(behavior, v4_position_smoke)
        self.assertIn("UnsupportedProtocol", universal_router_smoke)
        for behavior in [
            "UniswapUniversalRouterCommandsFallback",
            "Commands.FLAG_ALLOW_REVERT",
            "Commands.COMMAND_TYPE_MASK",
            "Commands.PAY_PORTION_FULL_PRECISION",
            "Commands.EXECUTE_SUB_PLAN",
            "Commands.ACROSS_V4_DEPOSIT_V3",
            "universal_router_commands_summary_calls=",
            "universal_router_commands_backend_check=pass",
            "unsupported_manifest_report_frontend_metadata=yes",
            "universal_router_commands_backend_frontend_metadata=yes",
        ]:
            self.assertIn(behavior, universal_router_smoke)
        for behavior in [
            "SafeCast160.toUint160",
            "UniswapPermit2NonceBitmapFallback",
            "InvalidNonce",
            "nonceBitmap[from][wordPos] ^= bit",
            "permit2_nonce_bitmap_compare_calls=",
            "PermitHash.hash",
            "IAllowanceTransfer.PermitBatch",
            "ISignatureTransfer.PermitTransferFrom",
            "--format lean-backend-check",
            "permit2_hash_backend_check_objects=",
            "permit2_hash_runtime_backend_check=",
            "permit2_hash_runtime_backend_first_none=",
            'hash_runtime_backend != ("pass", "none", "some")',
            "permit2_signature_backend_check_objects=",
            "permit2_signature_runtime_backend_check=",
            "permit2_signature_runtime_backend_first_none=",
            'signature_runtime_backend != ("pass", "none", "some")',
            "permit2_signature_backend_check_failed=",
        ]:
            self.assertIn(behavior, permit2_smoke)

    def test_additional_real_contract_smoke_keeps_pinned_behavior_coverage(self):
        scripts_dir = Path(__file__).resolve().parent
        smoke = (
            scripts_dir / "test_additional_real_contracts_bridge_smoke.sh"
        ).read_text()

        for ref_name in [
            "PRB_MATH_REF",
            "SOLBASE_REF",
            "BALANCER_V3_REF",
            "SEAPORT_REF",
        ]:
            self.assertRegex(
                smoke,
                rf'{ref_name}="\$\{{{ref_name}:-[0-9a-f]{{40}}\}}"',
            )

        for behavior in [
            "PRBMathRealWorldFallback",
            "avg(wrap(2e18), wrap(4e18))",
            "powu(wrap(2e18), 10)",
            "SolbaseRealWorldFallback",
            "FixedPointMathLib.expWad(1e18)",
            "FixedPointMathLib.lnWad(0)",
            "BalancerV3RealWorldFallback",
            "FixedPoint.powUp(2e18, 1.5e18)",
            "FixedPoint.divUp(1, 0)",
            "runtime-only",
            "SeaportMerkleRealWorldFallback",
            "MerkleLib.getProof",
            "MerkleLib.verifyProof",
            "compare_contract_call_bytecode.py",
            "--format lean-backend-check",
            "real_contract_repositories=4",
            "real_contract_compare_calls=48",
        ]:
            self.assertIn(behavior, smoke)

    def test_protocol_diversity_smoke_keeps_pinned_strict_coverage(self):
        scripts_dir = Path(__file__).resolve().parent
        smoke = (
            scripts_dir / "test_protocol_diversity_bridge_smoke.sh"
        ).read_text()

        for ref_name in [
            "MORPHO_BLUE_REF",
            "SAFE_SMART_ACCOUNT_REF",
            "ENS_CONTRACTS_REF",
            "ACCOUNT_ABSTRACTION_REF",
            "OPENZEPPELIN_REF",
        ]:
            self.assertRegex(
                smoke,
                rf'{ref_name}="\$\{{{ref_name}:-[0-9a-f]{{40}}\}}"',
            )

        for behavior in [
            "contract MorphoCorpus is Morpho",
            "--optimizer-runs",
            "999999",
            "--yul-ast-solc",
            "contract SafeCreateCorpus is CreateCall",
            "performCreate(uint256,bytes)",
            "contracts/Safe.sol",
            "safe_account",
            "ENSBytesCorpus",
            "data.substring(5, 20)",
            "AccountAbstractionCorpus",
            "UserOperationLib.unpackPaymasterStaticFields",
            "contracts/core/EntryPoint.sol",
            "account_abstraction_entrypoint",
            "--format lean-backend-check",
            "first_none=none",
            "compare_contract_call_bytecode.py",
            "protocol_diversity_strict_backend_objects=12",
            "protocol_diversity_compare_calls=14",
        ]:
            self.assertIn(behavior, smoke)

    def test_proxy_lifecycle_surface_keeps_executed_delegate_state_coverage(self):
        scripts_dir = Path(__file__).resolve().parent
        fixture = (
            scripts_dir.parent / "examples" / "ProxyLifecycleSurfaceBox.sol"
        ).read_text()
        smoke = (
            scripts_dir / "test_proxy_lifecycle_surface_backend.sh"
        ).read_text()
        matrix = (scripts_dir / "test_supported_solc_versions.sh").read_text()

        for behavior in [
            "contract ProxyLifecycleLogicV1",
            "contract ProxyLifecycleLogicV2",
            "contract ProxyLifecycleSurfaceBox",
            "eip1967.proxy.implementation",
            "delegatecall(gas(), target",
            "address(this).call",
            "failAfterStore",
            "new ProxyLifecycleLogicV2",
        ]:
            self.assertIn(behavior, fixture)
        for behavior in [
            "--all-contracts",
            "--format lean-backend-check",
            "compare_contract_call_bytecode.py",
            "proxy_lifecycle_checked_objects=6",
            "proxy_lifecycle_compare_calls=11",
            "proxy_lifecycle_reentrant_self_call=true",
            "proxy_lifecycle_revert_rollback=true",
        ]:
            self.assertIn(behavior, smoke)
        self.assertIn("test_proxy_lifecycle_surface_backend.sh", matrix)

    def test_uniswap_universal_router_smoke_covers_command_byte_dispatch(self):
        scripts_dir = Path(__file__).resolve().parent
        universal_router_smoke = (
            scripts_dir / "test_uniswap_universal_router_smoke.sh"
        ).read_text()

        for behavior in [
            "UniswapUniversalRouterCommandsFallback",
            "FLAG_ALLOW_REVERT",
            "COMMAND_TYPE_MASK",
            "PAY_PORTION_FULL_PRECISION",
            "BALANCE_CHECK_ERC20",
            "V4_POSITION_MANAGER_CALL",
            "EXECUTE_SUB_PLAN",
            "ACROSS_V4_DEPOSIT_V3",
            'assembly ("memory-safe")',
            "byte(0, calldataload(0))",
            "lean-backend-check",
            "universal_router_commands_frontend_metadata=yes",
            "universal_router_commands_summary_frontend_metadata=yes",
            "universal_router_commands_backend_frontend_metadata=yes",
            "universal_router_commands_summary_calls=",
            "universal_router_commands_backend_check=pass",
        ]:
            self.assertIn(behavior, universal_router_smoke)

    def test_uniswap_v4_smoke_covers_hooks_permission_summary(self):
        scripts_dir = Path(__file__).resolve().parent
        v4_smoke = (scripts_dir / "test_uniswap_v4_bridge_smoke.sh").read_text()

        for behavior in [
            "UniswapV4HooksFallback",
            "Hooks.BEFORE_SWAP_FLAG",
            "Hooks.AFTER_SWAP_RETURNS_DELTA_FLAG",
            "validateHookPermissions",
            "isValidHookAddress",
            "LPFeeLibrary.DYNAMIC_FEE_FLAG",
            "hooks_runtime_summary_primitives=yes",
            "hooks_runtime_lean_decode=",
            "hooks_runtime_summary_calls=",
        ]:
            self.assertIn(behavior, v4_smoke)

    def test_uniswap_v4_position_smoke_covers_storage_library_updates(self):
        scripts_dir = Path(__file__).resolve().parent
        position_smoke = (
            scripts_dir / "test_uniswap_v4_position_bridge_smoke.sh"
        ).read_text()

        for behavior in [
            "UniswapV4PositionFallback",
            "mapping(bytes32 => Position.State)",
            "Position.State storage position",
            "fun_calculatePositionKey",
            "fun_update",
            "fun_mulDiv",
            "position.update(1000, Q128, 2 * Q128)",
            "position.update(0, 3 * Q128, 5 * Q128)",
            "position.update(-400, 0, 0)",
            "CannotUpdateEmptyPosition",
            "lean-backend-check",
            '(runtime_check_status, runtime_first_none) != ("pass", "none")',
            'runtime_compare = "yes"',
            "contract_call_compare",
            "bridge_summary_1_frontends",
            "frontend_label",
            "UniswapV4PositionFallback:runtime",
            "uniswap_v4_position_frontend_metadata=yes",
            "uniswap_v4_position_summary_primitives=yes",
            "uniswap_v4_position_summary_user_calls=yes",
            "uniswap_v4_position_runtime_compare=",
        ]:
            self.assertIn(behavior, position_smoke)

    def test_uniswap_v4_extload_summary_smoke_covers_transient_external_loads(self):
        scripts_dir = Path(__file__).resolve().parent
        extload_smoke = (
            scripts_dir / "test_uniswap_v4_extload_summary_smoke.sh"
        ).read_text()

        for behavior in [
            "UniswapV4ExtloadWrapper",
            "v4-core/src/Extsload.sol",
            "v4-core/src/Exttload.sol",
            'assembly ("memory-safe")',
            "sstore(slot, value)",
            "tstore(slot, value)",
            '"sload"',
            '"sstore"',
            '"tload"',
            '"tstore"',
            "uniswap_v4_extload_summary_calls=",
            "uniswap_v4_extload_backend_compatibility=",
        ]:
            self.assertIn(behavior, extload_smoke)

    def test_aave_v3_smoke_covers_famous_math_libraries(self):
        scripts_dir = Path(__file__).resolve().parent
        aave_smoke = (scripts_dir / "test_aave_v3_bridge_smoke.sh").read_text()

        self.assertRegex(
            aave_smoke,
            r"AAVE_V3_REF=\"\$\{AAVE_V3_REF:-[0-9a-f]{40}\}\"",
        )
        for behavior in [
            "WadRayMath.wadMul",
            "WadRayMath.rayDiv",
            "WadRayMath.rayToWad",
            "WadRayMath.wadToRay",
            "PercentageMath.percentMul",
            "PercentageMath.percentDiv",
            "MathUtils.calculateCompoundedInterest",
            "lean-backend-check",
            "aave_v3_math_summary_primitives=yes",
            "aave_v3_math_runtime_backend_check=",
            "aave_v3_math_runtime_backend_first_none=",
            'status != "pass"',
            'object_image != "some"',
            "aave_v3_interest_summary_primitives=yes",
            "aave_v3_interest_runtime_backend_check=",
            "aave_v3_interest_runtime_backend_first_none=",
        ]:
            self.assertIn(behavior, aave_smoke)

    def test_solmate_smoke_covers_tokens_transfers_and_fixed_point_math(self):
        scripts_dir = Path(__file__).resolve().parent
        solmate_smoke = (scripts_dir / "test_solmate_bridge_smoke.sh").read_text()

        self.assertRegex(
            solmate_smoke,
            r"SOLMATE_REF=\"\$\{SOLMATE_REF:-[0-9a-f]{40}\}\"",
        )
        for behavior in [
            "SolmateHarness is ERC20, Owned",
            "SafeTransferLib.safeTransferETH",
            "receive() external payable",
            "lean-backend-check",
            "solmate_backend_check_objects=",
            "solmate_runtime_backend_check=",
            "solmate_runtime_backend_first_none=",
            "linked Solmate backend failed",
            "--linker-symbol",
            "FixedPointMathLib.mulWadDown",
            "FixedPointMathLib.mulWadUp",
            "FixedPointMathLib.sqrt",
            "FixedPointMathLib.mulDivDown",
            "fixed_point_fallback_compare_calls=",
        ]:
            self.assertIn(behavior, solmate_smoke)

    def test_solady_smoke_covers_bit_twiddling_and_linker_summary(self):
        scripts_dir = Path(__file__).resolve().parent
        solady_smoke = (scripts_dir / "test_solady_bridge_smoke.sh").read_text()

        self.assertRegex(
            solady_smoke,
            r"SOLADY_REF=\"\$\{SOLADY_REF:-[0-9a-f]{40}\}\"",
        )
        for behavior in [
            "LibBit.fls",
            "LibBit.clz",
            "LibBit.ffs",
            "LibBit.popCount",
            "LibBit.countZeroBytes",
            "LibBit.reverseBytes",
            "lean-backend-check",
            "solady_backend_check_objects=",
            "solady_runtime_backend_check=",
            "solady_runtime_backend_first_none=",
            "linked Solady backend failed",
            "--linker-symbol",
            "libbit_fallback_compare_calls=",
            "linkersymbol",
        ]:
            self.assertIn(behavior, solady_smoke)

    def test_openzeppelin_smoke_covers_erc20_safecast_and_strings(self):
        scripts_dir = Path(__file__).resolve().parent
        openzeppelin_smoke = (
            scripts_dir / "test_openzeppelin_bridge_smoke.sh"
        ).read_text()

        self.assertRegex(
            openzeppelin_smoke,
            (
                r"OPENZEPPELIN_REF=\"\$\{"
                r"OPENZEPPELIN_REF:-[0-9a-f]{40}\}\""
            ),
        )
        for behavior in [
            "OzToken is ERC20, Ownable, Pausable",
            "whenNotPaused",
            "lean-backend-check",
            "openzeppelin_backend_check_objects=",
            "openzeppelin_runtime_backend_check=",
            "openzeppelin_runtime_backend_first_none=",
            "SafeCast.toUint64",
            "SafeCast.toInt128",
            "safecast_fallback_compare_calls=",
            "Strings.toString",
            "Strings.toHexString",
            "Strings.equal",
            "strings_runtime_backend_check=",
            "strings_runtime_backend_first_none=",
            "strings_runtime_summary_primitives=yes",
        ]:
            self.assertIn(behavior, openzeppelin_smoke)

    def test_chainlink_smoke_covers_cbor_buffer_summary(self):
        scripts_dir = Path(__file__).resolve().parent
        chainlink_smoke = (
            scripts_dir / "test_chainlink_cbor_bridge_smoke.sh"
        ).read_text()

        self.assertRegex(
            chainlink_smoke,
            r"CHAINLINK_REF=\"\$\{CHAINLINK_REF:-[0-9a-f]{40}\}\"",
        )
        for behavior in [
            "BufferChainlink",
            "CBORChainlink",
            "ChainlinkCborBufferFallback",
            "buf.init(16)",
            "buf.encodeUInt(uint256(type(uint64).max) + 1)",
            "buf.encodeInt(-5)",
            "buf.encodeString(\"oracle\")",
            "buf.startArray()",
            "buf.encodeBytes(msg.data)",
            "buf.endSequence()",
            "bytes32 digest = keccak256(msg.data)",
            "buf.encodeBytes(abi.encode(digest))",
            "buf.appendUint8(mode)",
            "buf.truncate()",
            "compare_contract_call_bytecode.py",
            "--runtime-only",
            "if [[ \"$RUNTIME_BACKEND_STATUS\" != \"pass\" ]]",
            "--format lean-backend-check",
            "chainlink_cbor_runtime_backend_check=",
            "chainlink_cbor_runtime_backend_first_none=",
            "chainlink_cbor_runtime_compare_calls=",
            "runtime_compare = \"yes\"",
            'runtime_check_status != "pass" or runtime_first_none != "none"',
            "contract_call_compare",
            "full_runtime_bytes",
            "lean_runtime_bytes",
            "bridge_summary_1_backend_compatibility",
            "bridge_summary_1_object_selectors",
            "ChainlinkCborBufferFallback:runtime",
            "bridge_summary_1_frontends",
            "solc:irAst",
            "bridge_summary_1_unsupported_primitives",
            "chainlink_cbor_frontend_metadata=yes",
            "chainlink_cbor_manifest_lean_decode=yes",
            "chainlink_cbor_manifest_decode_objects=",
            "chainlink_cbor_summary_primitives=yes",
            "chainlink_cbor_summary_user_calls=yes",
            "--format lean-json-check",
            "AggregatorV3Interface",
            "ChainlinkAggregatorRoundFallback",
            "event AnswerUpdated",
            "transmit(-123456789, 1000)",
            "markStale(latestRoundId)",
            "getRoundData(roundId)",
            "latestRoundData()",
            "StaleRound",
            "NoDataPresent",
            "chainlink_aggregator_runtime_backend_check=",
            "chainlink_aggregator_runtime_backend_first_none=",
            "chainlink_aggregator_runtime_compare_calls=",
            "chainlink_aggregator_summary_primitives=yes",
            "chainlink_aggregator_summary_user_calls=yes",
        ]:
            self.assertIn(behavior, chainlink_smoke)

    def test_uniswap_permit2_smoke_covers_signature_verification_summary(self):
        scripts_dir = Path(__file__).resolve().parent
        permit2_smoke = (
            scripts_dir / "test_uniswap_permit2_bridge_smoke.sh"
        ).read_text()

        for behavior in [
            "SignatureVerification.verify",
            "msg.data[1:]",
            '"staticcall"',
            "permit2_signature_backend_check_objects=",
            "permit2_signature_runtime_backend_check=",
            "permit2_signature_runtime_backend_first_none=",
            'signature_runtime_backend != ("pass", "none", "some")',
            "permit2_signature_summary_primitives=yes",
        ]:
            self.assertIn(behavior, permit2_smoke)

    def test_uniswap_permit2_smoke_covers_nonce_bitmap_call_compare(self):
        scripts_dir = Path(__file__).resolve().parent
        permit2_smoke = (
            scripts_dir / "test_uniswap_permit2_bridge_smoke.sh"
        ).read_text()

        for behavior in [
            "UniswapPermit2NonceBitmapFallback",
            "bitmapPositions",
            "_useUnorderedNonce",
            "nonceBitmap[owner][wordPos] |= mask",
            "UnorderedNonceInvalidation",
            "compare_contract_call_bytecode.py",
            "--contract UniswapPermit2NonceBitmapFallback",
            "--optimized > \"$NONCE_BITMAP_COMPARE\"",
            "permit2_nonce_bitmap_compare_calls=",
        ]:
            self.assertIn(behavior, permit2_smoke)

    def test_forge_compare_smoke_runner_covers_default_import_library_and_optimized_paths(self):
        scripts_dir = Path(__file__).resolve().parent
        runner = (scripts_dir / "test_solidity_forge_compare_all.sh").read_text()
        default_smoke = (scripts_dir / "test_solidity_forge_compare.sh").read_text()
        import_smoke = (
            scripts_dir / "test_solidity_forge_compare_imports.sh"
        ).read_text()
        library_smoke = (
            scripts_dir / "test_solidity_forge_compare_libraries.sh"
        ).read_text()
        inline_assembly_smoke = (
            scripts_dir / "test_solidity_forge_compare_inline_assembly.sh"
        ).read_text()
        optimized_smoke = (
            scripts_dir / "test_solidity_forge_compare_optimized.sh"
        ).read_text()

        self.assertIn("test_solidity_forge_compare.sh", runner)
        self.assertIn("test_solidity_forge_compare_imports.sh", runner)
        self.assertIn("test_solidity_forge_compare_libraries.sh", runner)
        self.assertIn("test_solidity_forge_compare_inline_assembly.sh", runner)
        self.assertIn("test_solidity_forge_compare_optimized.sh", runner)
        self.assertIn("forge_compare_smokes_count=", runner)
        self.assertIn("compare_forge_solc_lean.sh", default_smoke)
        self.assertIn("compare_forge_solc_lean.sh", import_smoke)
        self.assertIn("compare_forge_solc_lean.sh", library_smoke)
        self.assertIn("compare_forge_solc_lean.sh", inline_assembly_smoke)
        self.assertIn("compare_forge_solc_lean.sh", optimized_smoke)
        self.assertIn("--match-test testAddOne", default_smoke)
        self.assertIn("--match-test testImported", import_smoke)
        self.assertIn("--match-test testLibrary", library_smoke)
        self.assertIn("--match-test testInlineAssembly", inline_assembly_smoke)
        for smoke, expected_count in [
            (default_smoke, "1"),
            (optimized_smoke, "1"),
            (import_smoke, "2"),
            (library_smoke, "2"),
            (inline_assembly_smoke, "2"),
        ]:
            self.assertIn("results_match=yes", smoke)
            self.assertIn(f"forge_compare_result_count={expected_count}", smoke)
            self.assertIn(f"forge_compare_tests_passed={expected_count}", smoke)
            self.assertIn("forge_compare_tests_failed=0", smoke)
            self.assertIn("forge_compare_tests_skipped=0", smoke)
        for smoke, expected_name in [
            (default_smoke, "testAddOne"),
            (optimized_smoke, "testFold"),
            (import_smoke, "testImportedScore"),
            (import_smoke, "testImportedFolded"),
            (library_smoke, "testLibraryScore"),
            (library_smoke, "testLibraryFolded"),
            (inline_assembly_smoke, "testInlineAssemblyArithmetic"),
            (inline_assembly_smoke, "testInlineAssemblyStorageAndHash"),
        ]:
            self.assertIn(expected_name, smoke)
            self.assertIn("forge_compare_result_", smoke)
        for behavior in [
            'import {ScaleBase} from "./lib/ScaleBase.sol"',
            'import {ImportedHarness} from "../src/ImportedHarness.sol"',
            "contract ImportCompareTest is ImportedHarness",
        ]:
            self.assertIn(behavior, import_smoke)
        for behavior in [
            'libraries = ["src/lib/ScaleLib.sol:ScaleLib:',
            'import {ScaleLib} from "./lib/ScaleLib.sol"',
            "contract LibraryCompareTest is LibraryHarness",
        ]:
            self.assertIn(behavior, library_smoke)
        for behavior in [
            "contract InlineAssemblyHarness",
            "contract InlineAssemblyCompareTest is InlineAssemblyHarness",
            'assembly ("memory-safe")',
            "sload(stored.slot)",
            "sstore(stored.slot, next)",
            "keccak256(add(input, 0x20), length)",
            "checkedDiv(4) != 25",
        ]:
            self.assertIn(behavior, inline_assembly_smoke)
        self.assertIn("--match-test testFold", optimized_smoke)

    def test_local_solidity_smoke_runner_covers_bytecode_frontend_target_and_wrapper_gates(self):
        scripts_dir = Path(__file__).resolve().parent
        runner = (scripts_dir / "test_solidity_local_smokes.sh").read_text()

        self.assertIn("test_solidity_bytecode_smoke.sh", runner)
        self.assertIn("test_solidity_frontend_summary_all.sh", runner)
        self.assertIn("test_solidity_frontend_decode_smokes.sh", runner)
        self.assertIn("test_solidity_target_bytecode_smokes.sh", runner)
        self.assertIn("test_solidity_forge_compare_all.sh", runner)
        self.assertIn("solidity_local_smokes_count=", runner)
        self.assertIn("solidity_local_smokes=pass", runner)

    def test_bytecode_smoke_covers_inline_assembly_artifact_and_batch_paths(self):
        scripts_dir = Path(__file__).resolve().parent
        smoke = (scripts_dir / "test_solidity_bytecode_smoke.sh").read_text()

        for behavior in [
            "InlineAssemblyBox.sol",
            "Generated.InlineAssemblyBoxArtifactSmoke",
            "inline_assembly_artifact",
            '("InlineAssemblyBox.sol", "InlineAssemblyBox")',
            "InlineAssemblyBox.sol:InlineAssemblyBox",
            "multi_standard_json_output_contracts=21",
            'manifest_counts.get("entries") != 42',
            'total_contracts != 23',
            'validate_artifact("inline_assembly_box"',
        ]:
            self.assertIn(behavior, smoke)

    def test_target_bytecode_smoke_runner_covers_forge_and_call_compare_paths(self):
        scripts_dir = Path(__file__).resolve().parent
        runner = (
            scripts_dir / "test_solidity_target_bytecode_smokes.sh"
        ).read_text()
        forge_smoke = (scripts_dir / "test_solidity_forge_smoke.sh").read_text()
        manifest_replay_smoke = (
            scripts_dir / "test_solidity_manifest_replay_smoke.sh"
        ).read_text()
        call_compare_smoke = (
            scripts_dir / "test_solidity_contract_call_compare.sh"
        ).read_text()

        self.assertIn("test_solidity_forge_smoke.sh", runner)
        self.assertIn("test_solidity_manifest_replay_smoke.sh", runner)
        self.assertIn("test_solidity_contract_call_compare.sh", runner)
        self.assertIn("target_bytecode_smokes_count=", runner)
        self.assertIn("target_bytecode_smokes=pass", runner)
        self.assertIn("LeanRuntimeSmokeTest", forge_smoke)
        self.assertIn("forge_smoke=pass", forge_smoke)
        for behavior in [
            "--input-format bridge-json-manifest",
            "--format bytecode-artifact",
            "--auto-object-layout",
            "--data-base 461",
            "manifest_replay_manifest_hints=yes",
            "manifest_replay_manifest_object_layout_entries=",
            "manifest_replay_manifest_local_data_base=yes",
            "manifest_replay_without_layout_flags=pass",
            "manifest_replay_local_data_base=yes",
        ]:
            self.assertIn(behavior, manifest_replay_smoke)
        self.assertIn("compare_contract_call_bytecode.py", call_compare_smoke)
        for behavior in [
            "ConstructorAbiBox",
            "EventMatrix",
            "PayableVault",
            "FallbackBox",
            "StorageArrayBox",
            "StorageStructBox",
            "MiniToken",
            "ArithmeticBox",
            "AbiBox",
            "ArrayBox",
            "EnvBox",
            "StringBox",
            "LoopBox",
            "StructBox",
            "BitwiseBox",
            "ModifierBox",
            "InterfaceCase",
            "--contract Impl",
            "InlineAssemblyBox",
            "EnumBytesBox",
            "ErrorPanicBox",
        ]:
            self.assertIn(behavior, call_compare_smoke)

        fallback_fixture = (
            scripts_dir.parent / "examples" / "FallbackBox.sol"
        ).read_text()
        for behavior in [
            "receive() external payable",
            "fallback(bytes calldata input) external payable returns (bytes memory)",
            "abi.encode(input.length, msg.value, last)",
            "event Hit",
        ]:
            self.assertIn(behavior, fallback_fixture)
        for calldata in ["--calldata 0x", "--calldata 0x12345678aabbcc"]:
            self.assertIn(calldata, call_compare_smoke)
        self.assertIn("--value 7", call_compare_smoke)

        storage_array_fixture = (
            scripts_dir.parent / "examples" / "StorageArrayBox.sol"
        ).read_text()
        for behavior in [
            "uint256[] private values",
            "values.push(value)",
            "values.push(items[i])",
            "values.pop()",
            "values[index] = value",
            "for (uint256 i = 0; i < values.length; i++)",
        ]:
            self.assertIn(behavior, storage_array_fixture)
        for calldata in [
            "--calldata 0x1e6ad596",
            "--calldata 0x53b8a6c6",
            "--calldata 0x853255cc",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        storage_struct_fixture = (
            scripts_dir.parent / "examples" / "StorageStructBox.sol"
        ).read_text()
        for behavior in [
            "mapping(address => Position) private positions",
            "Position storage position = positions[owner]",
            "position.flags = position.x ^ position.y",
            "last = Position",
            "delete positions[owner]",
        ]:
            self.assertIn(behavior, storage_struct_fixture)
        for calldata in [
            "--calldata 0x1974a47e",
            "--calldata 0x984a3eeb",
            "--calldata 0x4558aed6",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        mini_token_fixture = (
            scripts_dir.parent / "examples" / "MiniToken.sol"
        ).read_text()
        for behavior in [
            "mapping(address => uint256) private balances",
            "mapping(address => mapping(address => uint256)) private allowances",
            "emit Transfer(address(0), msg.sender, initialSupply)",
            "allowances[msg.sender][msg.sender]",
            'require(fromBalance >= amount, "balance")',
        ]:
            self.assertIn(behavior, mini_token_fixture)
        for calldata in [
            "--creation-only",
            "--calldata 0x18160ddd",
            "--calldata 0xcdacab4a",
            "--calldata 0xa9059cbb",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        arithmetic_fixture = (
            scripts_dir.parent / "examples" / "ArithmeticBox.sol"
        ).read_text()
        for behavior in [
            "function checkedAdd",
            "function uncheckedAdd",
            "unchecked {",
            "return left * right",
            "return left / right",
        ]:
            self.assertIn(behavior, arithmetic_fixture)
        for calldata in [
            "--calldata 0x460785c2",
            "--calldata 0xb277f199",
            "--calldata 0x8bcf6f66",
            "--calldata 0x6d0b772e",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        enum_bytes_fixture = (
            scripts_dir.parent / "examples" / "EnumBytesBox.sol"
        ).read_text()
        for behavior in [
            "enum Mode",
            "event Changed(Mode indexed mode, bytes4 tag)",
            "function set(Mode next, bytes4 nextTag)",
            "return (mode, tag, mode == Mode.Hot)",
            "mixed = left ^ right",
            "uint8(input[0]) + uint8(input[3])",
        ]:
            self.assertIn(behavior, enum_bytes_fixture)
        for calldata in [
            "--constructor-args 0x12345678",
            "--calldata 0xa9c4ea82",
            "--calldata 0x63ae30d9",
            "--calldata 0xa69fe148",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        error_panic_fixture = (
            scripts_dir.parent / "examples" / "ErrorPanicBox.sol"
        ).read_text()
        for behavior in [
            "error OutOfRange(uint256 seen, uint256 max)",
            "event Checked(uint256 indexed value, uint256 doubled)",
            "revert OutOfRange(value, 10)",
            'require(value != 0, "zero")',
            "assert(value < 5)",
            "unchecked {",
        ]:
            self.assertIn(behavior, error_panic_fixture)
        for calldata in [
            "--calldata 0x2e53fee2",
            "--calldata 0x0b7fb335",
            "--calldata 0x94ccacf8",
            "--calldata 0x1736138a",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        interface_fixture = (
            scripts_dir.parent / "examples" / "InterfaceCase.sol"
        ).read_text()
        for behavior in [
            "interface IFace",
            "abstract contract Base",
            "function g() public virtual",
            "function g() public pure override",
            "return x + 1",
        ]:
            self.assertIn(behavior, interface_fixture)
        for calldata in [
            "--calldata 0xb3de648b",
            "--calldata 0xe2179b8e",
        ]:
            self.assertIn(calldata, call_compare_smoke)

        inline_assembly_fixture = (
            scripts_dir.parent / "examples" / "InlineAssemblyBox.sol"
        ).read_text()
        for behavior in [
            'assembly ("memory-safe")',
            "sload(value.slot)",
            "sstore(value.slot, next)",
            "keccak256(add(input, 0x20), length)",
            "calldataload(input.offset)",
            "shl(224, 0x4e487b71)",
        ]:
            self.assertIn(behavior, inline_assembly_fixture)
        for calldata in [
            "--calldata 0x6cbb5ae3",
            "--calldata 0x6057361d",
            "--calldata 0xaa1e84de",
            "--calldata 0x4863be8a",
            "--calldata 0xb8f985a7",
        ]:
            self.assertIn(calldata, call_compare_smoke)

    def test_contract_call_compare_covers_custom_error_and_panic_paths(self):
        scripts_dir = Path(__file__).resolve().parent
        call_compare_smoke = (
            scripts_dir / "test_solidity_contract_call_compare.sh"
        ).read_text()
        fixture = (scripts_dir.parent / "examples" / "ErrorPanicBox.sol").read_text()

        self.assertIn("ErrorPanicBox.sol", call_compare_smoke)
        self.assertIn("--contract ErrorPanicBox", call_compare_smoke)
        for behavior in [
            "error OutOfRange(uint256 seen, uint256 max)",
            "event Checked(uint256 indexed value, uint256 doubled)",
            "revert OutOfRange(value, 10)",
            'require(value != 0, "zero")',
            "assert(value < 5)",
            "unchecked {",
        ]:
            self.assertIn(behavior, fixture)
        for calldata in [
            "--calldata 0x2e53fee2",
            "--calldata 0x0b7fb335",
            "--calldata 0x94ccacf8",
            "--calldata 0x1736138a",
        ]:
            self.assertIn(calldata, call_compare_smoke)

    def test_contract_call_compare_covers_resource_observer_opcodes(self):
        scripts_dir = Path(__file__).resolve().parent
        call_compare_smoke = (
            scripts_dir / "test_solidity_contract_call_compare.sh"
        ).read_text()
        fixture = (
            scripts_dir.parent / "examples" / "ResourceObserverBox.sol"
        ).read_text()

        self.assertIn("ResourceObserverBox.sol", call_compare_smoke)
        self.assertIn("--contract ResourceObserverBox", call_compare_smoke)
        self.assertIn("--calldata 0x14fc78fc", call_compare_smoke)
        self.assertIn("pop(gas())", fixture)
        self.assertIn("pop(msize())", fixture)

    def test_frontend_decode_smoke_runner_covers_external_call_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        external_smoke = (
            scripts_dir / "test_solidity_external_call_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "ExternalCallBox.sol").read_text()

        self.assertIn("test_solidity_frontend_decode_smoke.sh", runner)
        self.assertIn("test_solidity_object_tree_smoke.sh", runner)
        self.assertIn("test_solidity_external_call_decode_smoke.sh", runner)
        self.assertIn("frontend_decode_smokes_count=", runner)
        self.assertIn("ExternalCallBox.sol", external_smoke)
        self.assertIn("lean-json-check", external_smoke)
        self.assertIn("lean-backend-check", external_smoke)
        self.assertIn("bridge-json-summary", external_smoke)
        self.assertIn("open external-boundary", external_smoke)
        self.assertIn("external_call_decode_backend_check_failed=", external_smoke)
        self.assertIn("external_call_decode_backend_compatibility=ready", external_smoke)
        self.assertIn("external_call_decode_creation_backend_check=pass", external_smoke)
        self.assertIn("external_call_decode_runtime_backend_check=pass", external_smoke)
        self.assertIn(
            '("ExternalCallBox", "runtime"): ("pass", "none")',
            external_smoke,
        )
        for primitive in [
            "call",
            "staticcall",
            "delegatecall",
            "returndatasize",
            "returndatacopy",
            "gas",
        ]:
            self.assertIn(primitive, external_smoke)
        for behavior in [
            ".call{value: amount}",
            ".staticcall(payload)",
            ".delegatecall(payload)",
            "returndatacopy(ptr, 0, size)",
            "ExternalFailed",
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_decode_smoke_runner_covers_selfdestruct_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        selfdestruct_smoke = (
            scripts_dir / "test_solidity_selfdestruct_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "SelfDestructBox.sol").read_text()

        self.assertIn("test_solidity_selfdestruct_decode_smoke.sh", runner)
        self.assertIn("SelfDestructBox.sol", selfdestruct_smoke)
        self.assertIn("lean-json-check", selfdestruct_smoke)
        self.assertIn("lean-backend-check", selfdestruct_smoke)
        self.assertIn("bridge-json-summary", selfdestruct_smoke)
        self.assertIn("selfdestruct_decode_primitive=yes", selfdestruct_smoke)
        self.assertIn("selfdestruct_decode_backend_compatibility=ready", selfdestruct_smoke)
        self.assertIn("selfdestruct_decode_backend_check=pass", selfdestruct_smoke)
        self.assertIn("selfdestruct_decode_backend_check_passed=", selfdestruct_smoke)
        self.assertIn('("SelfDestructBox", "runtime"): ("pass", "none")', selfdestruct_smoke)
        self.assertIn("incorrectly marked selfdestruct unsupported", selfdestruct_smoke)
        self.assertIn("incorrectly marked sstore unsupported", selfdestruct_smoke)
        for behavior in [
            "selfdestruct(recipient)",
            "selfdestruct(0)",
            "receive() external payable",
            "error NotArmed",
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_decode_smoke_runner_covers_fallback_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        fallback_smoke = (
            scripts_dir / "test_solidity_fallback_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "FallbackBox.sol").read_text()

        self.assertIn("test_solidity_fallback_decode_smoke.sh", runner)
        self.assertIn("FallbackBox.sol", fallback_smoke)
        self.assertIn("lean-json-check", fallback_smoke)
        self.assertIn("lean-backend-check", fallback_smoke)
        self.assertIn("bridge-json-summary", fallback_smoke)
        self.assertIn("fallback_decode_frontend_metadata=yes", fallback_smoke)
        self.assertIn("fallback_decode_primitives=yes", fallback_smoke)
        self.assertIn("fallback_decode_backend_compatibility=ready", fallback_smoke)
        self.assertIn("fallback_decode_backend_check=pass", fallback_smoke)
        self.assertIn("fallback_decode_backend_check_passed=", fallback_smoke)
        self.assertIn('("FallbackBox", "runtime"): ("pass", "none")', fallback_smoke)
        for primitive in [
            "callvalue",
            "calldataload",
            "calldatasize",
            "log2",
            "return",
            "sstore",
        ]:
            self.assertIn(primitive, fallback_smoke)
        for behavior in [
            "receive() external payable",
            "fallback(bytes calldata input) external payable returns (bytes memory)",
            "msg.value + input.length",
            "emit Hit(2, msg.value, input.length)",
            "abi.encode(input.length, msg.value, last)",
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_decode_smoke_runner_covers_event_matrix_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        event_matrix_smoke = (
            scripts_dir / "test_solidity_event_matrix_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "EventMatrix.sol").read_text()

        self.assertIn("test_solidity_event_matrix_decode_smoke.sh", runner)
        self.assertIn("EventMatrix.sol", event_matrix_smoke)
        self.assertIn("lean-json-check", event_matrix_smoke)
        self.assertIn("lean-backend-check", event_matrix_smoke)
        self.assertIn("bridge-json-summary", event_matrix_smoke)
        self.assertIn("event_matrix_decode_frontend_metadata=yes", event_matrix_smoke)
        self.assertIn("event_matrix_decode_log_primitives=yes", event_matrix_smoke)
        self.assertIn("event_matrix_decode_backend_compatibility=ready", event_matrix_smoke)
        self.assertIn("event_matrix_decode_backend_check=pass", event_matrix_smoke)
        self.assertIn("event_matrix_decode_backend_check_passed=", event_matrix_smoke)
        self.assertIn('("EventMatrix", "runtime"): ("pass", "none")', event_matrix_smoke)
        for primitive in ["log0", "log1", "log2", "log3", "log4"]:
            self.assertIn(primitive, event_matrix_smoke)
        for behavior in [
            "event AnonymousZero(uint256 value) anonymous",
            "event AnonymousFour",
            "event Two(address indexed sender, bytes32 indexed salt, uint256 value)",
            "emit AnonymousZero(11)",
            "emit Plain(22)",
            "emit One(msg.sender, 33)",
            "emit Two(msg.sender, bytes32(uint256(44)), 55)",
            "emit Three(msg.sender, bytes32(uint256(44)), 55, 66)",
            "emit AnonymousFour(msg.sender, bytes32(uint256(77)), 88, 99)",
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_decode_smoke_runner_covers_try_catch_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        try_catch_smoke = (
            scripts_dir / "test_solidity_try_catch_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "TryCatchBox.sol").read_text()

        self.assertIn("test_solidity_try_catch_decode_smoke.sh", runner)
        self.assertIn("TryCatchBox.sol", try_catch_smoke)
        self.assertIn("TryCatchBox", try_catch_smoke)
        self.assertIn("TryCatchTarget", try_catch_smoke)
        self.assertIn("lean-json-check", try_catch_smoke)
        self.assertIn("lean-backend-check", try_catch_smoke)
        self.assertIn("bridge-json-summary", try_catch_smoke)
        self.assertIn("try_catch_decode_primitives=yes", try_catch_smoke)
        self.assertIn("try_catch_decode_backend_compatibility=ready", try_catch_smoke)
        self.assertIn("try_catch_decode_backend_check_objects=", try_catch_smoke)
        self.assertIn("try_catch_decode_backend_check_passed=", try_catch_smoke)
        self.assertIn("try_catch_decode_backend_check_failed=", try_catch_smoke)
        self.assertIn("try_catch_decode_box_runtime_first_none=", try_catch_smoke)
        self.assertIn("try_catch_decode_target_runtime_first_none=", try_catch_smoke)
        for primitive in [
            "call",
            "returndatacopy",
            "returndatasize",
            "revert",
            "log2",
            "gas",
        ]:
            self.assertIn(primitive, try_catch_smoke)
        for behavior in [
            "try TryCatchTarget(target).maybe(mode)",
            "catch Error(string memory reason)",
            "catch Panic(uint256 code)",
            "catch (bytes memory data)",
            "error Custom",
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_decode_smoke_runner_covers_minitoken_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        minitoken_smoke = (
            scripts_dir / "test_solidity_minitoken_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "MiniToken.sol").read_text()

        self.assertIn("test_solidity_minitoken_decode_smoke.sh", runner)
        self.assertIn("MiniToken.sol", minitoken_smoke)
        self.assertIn("lean-json-check", minitoken_smoke)
        self.assertIn("lean-backend-check", minitoken_smoke)
        self.assertIn("bridge-json-summary", minitoken_smoke)
        self.assertIn("minitoken_decode_backend_check_objects=", minitoken_smoke)
        self.assertIn("minitoken_decode_backend_check_passed=", minitoken_smoke)
        self.assertIn("minitoken_decode_backend_check_failed=", minitoken_smoke)
        self.assertIn("minitoken_decode_runtime_backend_status=", minitoken_smoke)
        self.assertIn("minitoken_decode_runtime_first_none=", minitoken_smoke)
        self.assertIn("minitoken_decode_frontend_metadata=yes", minitoken_smoke)
        self.assertIn("minitoken_decode_primitives=yes", minitoken_smoke)
        self.assertIn("minitoken_decode_backend_compatibility=ready", minitoken_smoke)
        for primitive in [
            "caller",
            "keccak256",
            "log3",
            "revert",
            "sload",
            "sstore",
        ]:
            self.assertIn(primitive, minitoken_smoke)
        for behavior in [
            "mapping(address => uint256) private balances",
            "mapping(address => mapping(address => uint256)) private allowances",
            "emit Transfer(address(0), msg.sender, initialSupply)",
            "emit Approval(msg.sender, msg.sender, amount)",
            'require(allowed >= amount, "allowance")',
            'require(fromBalance >= amount, "balance")',
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_decode_smoke_runner_covers_error_panic_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_decode_smokes.sh"
        ).read_text()
        error_panic_smoke = (
            scripts_dir / "test_solidity_error_panic_decode_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "ErrorPanicBox.sol").read_text()

        self.assertIn("test_solidity_error_panic_decode_smoke.sh", runner)
        self.assertIn("ErrorPanicBox.sol", error_panic_smoke)
        self.assertIn("lean-json-check", error_panic_smoke)
        self.assertIn("lean-backend-check", error_panic_smoke)
        self.assertIn("bridge-json-summary", error_panic_smoke)
        self.assertIn("error_panic_decode_frontend_metadata=yes", error_panic_smoke)
        self.assertIn("error_panic_decode_primitives=yes", error_panic_smoke)
        self.assertIn("error_panic_decode_backend_compatibility=ready", error_panic_smoke)
        self.assertIn("error_panic_decode_backend_check_objects=", error_panic_smoke)
        self.assertIn("error_panic_decode_backend_check_passed=", error_panic_smoke)
        self.assertIn("error_panic_decode_backend_check_failed=", error_panic_smoke)
        self.assertIn("error_panic_decode_runtime_first_none=", error_panic_smoke)
        for primitive in ["div", "log2", "revert", "sload", "sstore"]:
            self.assertIn(primitive, error_panic_smoke)
        for behavior in [
            "error OutOfRange(uint256 seen, uint256 max)",
            "event Checked(uint256 indexed value, uint256 doubled)",
            "revert OutOfRange(value, 10)",
            'require(value != 0, "zero")',
            "assert(value < 5)",
            "unchecked {",
        ]:
            self.assertIn(behavior, fixture)

    def test_frontend_summary_smoke_runner_covers_lean_free_behavior_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        runner = (
            scripts_dir / "test_solidity_frontend_summary_smokes.sh"
        ).read_text()
        local_runner = (scripts_dir / "test_solidity_local_smokes.sh").read_text()
        summary_all_runner = (
            scripts_dir / "test_solidity_frontend_summary_all.sh"
        ).read_text()

        self.assertIn("test_solidity_frontend_summary_all.sh", local_runner)
        self.assertIn("test_solidity_frontend_summary_smokes.sh", summary_all_runner)
        self.assertIn("frontend_summary_all_count=", summary_all_runner)
        self.assertIn("frontend_summary_smokes_count=12", runner)
        self.assertIn("--format bridge-json", runner)
        self.assertIn("--format bridge-json-summary", runner)
        self.assertIn("validate_bridge_json.py", runner)
        self.assertNotIn("lean-json-check", runner)
        self.assertNotIn("--lake", runner)
        for source in [
            "PackedStorageBox.sol",
            "ExternalCallBox.sol",
            "FallbackBox.sol",
            "EventMatrix.sol",
            "TryCatchBox.sol",
            "ErrorPanicBox.sol",
            "MiniToken.sol",
            "FactoryBox.sol",
            "StorageArrayBox.sol",
            "AbiBox.sol",
            "EnvBox.sol",
            "PostCancunPrecompileBoundary.sol",
        ]:
            self.assertIn(source, runner)
        for primitive in [
            "create,create2",
            "call,delegatecall,staticcall",
            "returndatacopy,returndatasize,gas",
            "staticcall,gas",
            "log0,log1,log2,log3,log4",
            "caller,origin,chainid,timestamp,callvalue",
            "calldatacopy,keccak256,revert",
        ]:
            self.assertIn(primitive, runner)
        for fixture_name, behavior in [
            ("FactoryBox.sol", "new ChildBox{salt: salt, value: msg.value}(seed)"),
            ("StorageArrayBox.sol", "values.push(items[i])"),
            ("AbiBox.sol", "abi.decode(payload, (uint256, bytes))"),
            ("EnvBox.sol", "block.prevrandao"),
            ("PostCancunPrecompileBoundary.sol", "callPrecompile(0x0b, input, 128)"),
            ("PostCancunPrecompileBoundary.sol", "callPrecompile(0x11, input, 256)"),
            ("PostCancunPrecompileBoundary.sol", "callPrecompile(0x100, input, 32)"),
        ]:
            self.assertIn(behavior, (examples_dir / fixture_name).read_text())

    def test_frontend_optimized_summary_smoke_runner_covers_structured_ast_metadata(self):
        scripts_dir = Path(__file__).resolve().parent
        runner = (
            scripts_dir / "test_solidity_frontend_optimized_summary_smoke.sh"
        ).read_text()
        local_runner = (scripts_dir / "test_solidity_local_smokes.sh").read_text()
        summary_all_runner = (
            scripts_dir / "test_solidity_frontend_summary_all.sh"
        ).read_text()

        self.assertIn("test_solidity_frontend_summary_all.sh", local_runner)
        self.assertIn("test_solidity_frontend_optimized_summary_smoke.sh", summary_all_runner)
        self.assertIn("frontend_summary_all=pass", summary_all_runner)
        self.assertIn("frontend_optimized_summary_smoke_count=4", runner)
        self.assertIn("--optimized", runner)
        self.assertIn("irOptimizedAst", runner)
        self.assertIn("--format bridge-json", runner)
        self.assertIn("--format bridge-json-summary", runner)
        self.assertIn("validate_bridge_json.py", runner)
        self.assertNotIn("lean-json-check", runner)
        self.assertNotIn("--lake", runner)
        for source in [
            "ExternalCallBox.sol",
            "EventMatrix.sol",
            "InlineAssemblyBox.sol",
            "MiniToken.sol",
        ]:
            self.assertIn(source, runner)
        for primitive in [
            "call,delegatecall,staticcall",
            "returndatacopy,returndatasize,gas",
            "log0,log1,log2,log3,log4",
            "calldataload,keccak256,log2,revert,sload,sstore",
            "caller,keccak256,log3,revert,sload,sstore",
        ]:
            self.assertIn(primitive, runner)

    def test_packed_storage_frontend_smoke_records_backend_handoff_blockers(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        smoke = (scripts_dir / "test_solidity_frontend_decode_smoke.sh").read_text()
        fixture = (examples_dir / "PackedStorageBox.sol").read_text()

        self.assertIn("lean-backend-check", smoke)
        self.assertIn("frontend_decode_packed_backend_check=pass", smoke)
        self.assertIn('"creation": ("pass", "none")', smoke)
        self.assertIn('"runtime": ("pass", "none")', smoke)
        for behavior in [
            "bool public flag",
            "uint8 public small",
            "int16 public signedSmall",
            "Mode public mode",
            "Pair public pair",
            "pair = Pair",
        ]:
            self.assertIn(behavior, fixture)

    def test_object_tree_smoke_covers_create_and_create2_preflight(self):
        scripts_dir = Path(__file__).resolve().parent
        examples_dir = scripts_dir.parent / "examples"
        object_tree_smoke = (
            scripts_dir / "test_solidity_object_tree_smoke.sh"
        ).read_text()
        fixture = (examples_dir / "FactoryBox.sol").read_text()

        self.assertIn("bridge-json-summary", object_tree_smoke)
        self.assertIn("lean-backend-check", object_tree_smoke)
        self.assertIn("object_tree_factory_create_primitives=yes", object_tree_smoke)
        self.assertIn("object_tree_factory_backend_compatibility=ready", object_tree_smoke)
        self.assertIn("object_tree_child_creation_backend_check=pass", object_tree_smoke)
        self.assertIn("object_tree_child_runtime_backend_check=pass", object_tree_smoke)
        self.assertIn("object_tree_factory_creation_backend_check=pass", object_tree_smoke)
        self.assertIn("object_tree_factory_runtime_backend_check=pass", object_tree_smoke)
        self.assertIn('("ChildBox", "creation"): ("pass", "none")', object_tree_smoke)
        self.assertIn('("ChildBox", "runtime"): ("pass", "none")', object_tree_smoke)
        self.assertIn('("FactoryBox", "creation"): ("pass", "none")', object_tree_smoke)
        self.assertIn('("FactoryBox", "runtime"): ("pass", "none")', object_tree_smoke)
        for primitive in ["create", "create2", "gas"]:
            self.assertIn(primitive, object_tree_smoke)
        for behavior in [
            "new ChildBox{value: msg.value}(seed)",
            "new ChildBox{salt: salt, value: msg.value}(seed)",
            "return (address(child), result)",
        ]:
            self.assertIn(behavior, fixture)

    def test_contract_call_compare_links_full_solc_bytecode(self):
        placeholder = "__$" + ("0" * 34) + "$__"
        linked = compare_call.link_solc_bytecode(
            "60" + placeholder + "00",
            {"Lib.sol": {"Lib": [{"start": 1, "length": 20}]}},
            [
                SimpleNamespace(
                    name="Lib.sol:Lib",
                    value=int("11" * 20, 16),
                )
            ],
            "solc runtime bytecode",
        )

        self.assertEqual(linked, "0x60" + ("11" * 20) + "00")

    def test_contract_call_compare_requires_full_solc_linker_symbol(self):
        placeholder = "__$" + ("0" * 34) + "$__"
        with self.assertRaisesRegex(ValueError, "pass --linker-symbol"):
            compare_call.link_solc_bytecode(
                "60" + placeholder + "00",
                {"Lib.sol": {"Lib": [{"start": 1, "length": 20}]}},
                [],
                "solc runtime bytecode",
            )

    def test_contract_call_compare_runtime_only_ignores_creation_link_placeholders(self):
        placeholder = "__$" + ("0" * 34) + "$__"
        full_creation, full_runtime = compare_call.link_compared_full_solc_bytecode(
            "60" + placeholder + "00",
            "6000",
            {"Lib.sol": {"Lib": [{"start": 1, "length": 20}]}},
            {},
            [],
            compare_creation=False,
            compare_runtime=True,
        )

        self.assertEqual(full_creation, "0x")
        self.assertEqual(full_runtime, "0x6000")

    def test_contract_call_compare_creation_only_ignores_runtime_link_placeholders(self):
        placeholder = "__$" + ("0" * 34) + "$__"
        full_creation, full_runtime = compare_call.link_compared_full_solc_bytecode(
            "6000",
            "60" + placeholder + "00",
            {},
            {"Lib.sol": {"Lib": [{"start": 1, "length": 20}]}},
            [],
            compare_creation=True,
            compare_runtime=False,
        )

        self.assertEqual(full_creation, "0x6000")
        self.assertEqual(full_runtime, "0x")

    def test_contract_call_compare_persists_bridge_json_dir(self):
        old_run = compare_call.subprocess.run
        calls = []
        try:
            class Completed:
                returncode = 1
                stdout = ""
                stderr = "bytecode failed"

            def fake_run(command, **kwargs):
                calls.append((command, kwargs))
                return Completed()

            compare_call.subprocess.run = fake_run
            with tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "lean-artifact.json"
                args = SimpleNamespace(
                    input=Path("Input.sol"),
                    solc="solc",
                    lake="lake",
                    lake_cwd=Path("."),
                    contract="Input",
                    namespace="Generated.Compare",
                    source_name=None,
                    optimized=False,
                    via_ir=True,
                    experimental=True,
                    auto_include_imports=True,
                    include_source=[],
                    remapping=[],
                    remappings_file=[],
                    linker_symbol=[],
                    solc_arg=[],
                )
                with self.assertRaises(RuntimeError) as raised:
                    compare_call.run_bridge_artifact(Path("/repo"), args, output)
                expected_bridge_dir = str(Path(directory) / "bridge-json")

            command, kwargs = calls[0]
        finally:
            compare_call.subprocess.run = old_run

        self.assertTrue(kwargs["text"])
        self.assertIn("--bridge-json-dir", command)
        self.assertEqual(
            command[command.index("--bridge-json-dir") + 1],
            expected_bridge_dir,
        )
        self.assertIn(f"bridge_json_dir={expected_bridge_dir}", str(raised.exception))

    def test_contract_call_compare_writes_bridge_summary(self):
        old_run = compare_call.subprocess.run
        calls = []
        try:
            class Completed:
                returncode = 0
                stdout = ""
                stderr = ""

            def fake_run(command, **kwargs):
                calls.append((command, kwargs))
                if "--format" in command and "bytecode-artifact" in command:
                    output_path = Path(command[command.index("--output") + 1])
                    bridge_dir = Path(command[command.index("--bridge-json-dir") + 1])
                    bridge_dir.mkdir(parents=True)
                    (bridge_dir / "manifest.json").write_text(
                        json.dumps(
                            {
                                "schema": "evm-compiler.bridge-json-manifest.v1",
                                "entries": [],
                                "counts": {"entries": 0},
                            }
                        )
                    )
                    output_path.write_text(
                        json.dumps(
                            {
                                "bytecode": {
                                    "creation": "0x00",
                                    "runtime": "0x00",
                                }
                            }
                        )
                    )
                elif "--format" in command and "bridge-json-summary" in command:
                    output_path = Path(command[command.index("--output") + 1])
                    output_path.write_text(
                        json.dumps(
                            {
                                "schema": (
                                    "evm-compiler.solc-yul-bridge-"
                                    "manifest-summary.v1"
                                ),
                                "counts": {
                                    "objects": 0,
                                    "skippedContracts": 0,
                                    "calls": 0,
                                },
                                "objects": [],
                                "skippedContracts": [],
                                "backendCompatibility": {
                                    "profile": "current-yul-compiler",
                                    "status": "ready",
                                    "unsupportedPrimitiveNames": [],
                                    "objectBuiltinNames": [],
                                    "dialectBuiltinNames": [],
                                    "notes": [],
                                },
                            }
                        )
                    )
                return Completed()

            compare_call.subprocess.run = fake_run
            with tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "lean-artifact.json"
                args = SimpleNamespace(
                    input=Path("Input.sol"),
                    solc="solc",
                    lake="lake",
                    lake_cwd=Path("."),
                    contract="Input",
                    namespace="Generated.Compare",
                    source_name=None,
                    optimized=False,
                    via_ir=True,
                    experimental=True,
                    auto_include_imports=True,
                    include_source=[],
                    remapping=[],
                    remappings_file=[],
                    linker_symbol=[],
                    solc_arg=[],
                )
                artifact = compare_call.run_bridge_artifact(Path("/repo"), args, output)
                summary_path = Path(directory) / "bridge-json-summary.json"
                self.assertTrue(summary_path.exists())
        finally:
            compare_call.subprocess.run = old_run

        self.assertEqual(artifact["bytecode"]["runtime"], "0x00")
        summary_commands = [
            command for command, _kwargs in calls
            if "bridge-json-summary" in command
        ]
        self.assertEqual(len(summary_commands), 1)
        self.assertIn("--input-format", summary_commands[0])
        self.assertIn("bridge-json-manifest", summary_commands[0])
        validate_commands = [
            command for command, _kwargs in calls
            if str(command[1]).endswith("validate_bridge_json.py")
        ]
        self.assertEqual(len(validate_commands), 1)
        self.assertIn("--quiet", validate_commands[0])

    def test_contract_call_compare_formats_bridge_summary_report(self):
        with tempfile.TemporaryDirectory() as directory:
            summary = Path(directory) / "bridge-json-runtime-summary.json"
            summary.write_text(
                json.dumps(
                    {
                        "counts": {
                            "objects": 1,
                            "skippedContracts": 0,
                        },
                        "objects": [
                            {
                                "contract": "Box",
                                "selector": "runtime",
                                "object": "Box_1_deployed",
                                "frontend": {
                                    "producer": "solc",
                                    "ast": "irOptimizedAst",
                                },
                            }
                        ],
                        "backendCompatibility": {
                            "status": "ready",
                            "unsupportedPrimitiveNames": [],
                            "objectBuiltinNames": ["datasize"],
                            "dialectBuiltinNames": [],
                        },
                    }
                )
            )

            lines = compare_call.bridge_summary_report_lines(summary, 2)

        self.assertEqual(
            lines,
            [
                "bridge_summary_2_backend_compatibility=ready",
                "bridge_summary_2_objects=1",
                "bridge_summary_2_object_selectors=Box:runtime",
                "bridge_summary_2_frontends=solc:irOptimizedAst",
                "bridge_summary_2_skipped_contracts=0",
                "bridge_summary_2_unsupported_primitives=none",
                "bridge_summary_2_object_builtins=datasize",
                "bridge_summary_2_dialect_builtins=none",
            ],
        )

    def test_contract_call_compare_requires_bridge_summary_report(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(RuntimeError) as raised:
                compare_call.require_bridge_summary_paths(Path(directory))

        self.assertIn("produced no bridge summaries", str(raised.exception))
        self.assertIn("structured Yul bridge handoff", str(raised.exception))

    def test_contract_call_compare_main_reports_bridge_summary_diagnostics(self):
        old_load_bridge = compare_call.load_bridge
        old_load_full_solc_bytecode = compare_call.load_full_solc_bytecode
        old_run_bridge_bytecode = compare_call.run_bridge_bytecode
        old_run_forge_harness = compare_call.run_forge_harness
        old_stdout = sys.stdout
        try:
            def fake_load_bridge(_script_dir):
                return SimpleNamespace(parse_linker_symbol_entry=lambda entry: entry)

            def fake_load_full_solc_bytecode(_bridge_module, _args):
                return ("Input.sol", "Input", "6000", "6001", {}, {})

            def fake_run_bridge_bytecode(_root, _args, output_path, object_selector):
                self.assertEqual(object_selector, "runtime")
                summary_path = output_path.parent / "bridge-json-runtime-summary.json"
                summary_path.write_text(
                    json.dumps(
                        {
                            "counts": {
                                "objects": 1,
                                "skippedContracts": 0,
                            },
                            "objects": [
                                {
                                    "contract": "Input",
                                    "selector": "runtime",
                                    "object": "Input_1_deployed",
                                    "frontend": {
                                        "producer": "solc",
                                        "ast": "irAst",
                                    },
                                }
                            ],
                            "backendCompatibility": {
                                "status": "ready",
                                "unsupportedPrimitiveNames": [],
                                "objectBuiltinNames": [],
                                "dialectBuiltinNames": [],
                            },
                        }
                    )
                )
                output_path.write_text("0x6001\n")
                return "0x6001"

            def fake_run_forge_harness(
                _forge, _solc, _outdir, harness, evm_version
            ):
                self.assertIn("testRuntimeBytecodeCallResultsMatch", harness)
                self.assertEqual(evm_version, "london")

            compare_call.load_bridge = fake_load_bridge
            compare_call.load_full_solc_bytecode = fake_load_full_solc_bytecode
            compare_call.run_bridge_bytecode = fake_run_bridge_bytecode
            compare_call.run_forge_harness = fake_run_forge_harness
            sys.stdout = io.StringIO()

            result = compare_call.main(
                [
                    "Input.sol",
                    "--contract",
                    "Input",
                    "--calldata",
                    "0x00",
                    "--runtime-only",
                    "--solc",
                    "/tmp/solc",
                    "--lake",
                    "/tmp/lake",
                    "--forge",
                    "/tmp/forge",
                    "--forge-evm-version",
                    "london",
                ]
            )
            output_lines = set(sys.stdout.getvalue().splitlines())
        finally:
            compare_call.load_bridge = old_load_bridge
            compare_call.load_full_solc_bytecode = old_load_full_solc_bytecode
            compare_call.run_bridge_bytecode = old_run_bridge_bytecode
            compare_call.run_forge_harness = old_run_forge_harness
            sys.stdout = old_stdout

        self.assertEqual(result, 0)
        for line in [
            "contract_call_compare=pass",
            "source=Input.sol",
            "contract=Input",
            "calls=1",
            "bridge_summary_count=1",
            "bridge_summary_1_backend_compatibility=ready",
            "bridge_summary_1_objects=1",
            "bridge_summary_1_object_selectors=Input:runtime",
            "bridge_summary_1_frontends=solc:irAst",
            "bridge_summary_1_unsupported_primitives=none",
        ]:
            self.assertIn(line, output_lines)

    def test_contract_call_compare_main_fails_without_bridge_summary(self):
        old_load_bridge = compare_call.load_bridge
        old_load_full_solc_bytecode = compare_call.load_full_solc_bytecode
        old_run_bridge_bytecode = compare_call.run_bridge_bytecode
        old_run_forge_harness = compare_call.run_forge_harness
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        try:
            def fake_load_bridge(_script_dir):
                return SimpleNamespace(parse_linker_symbol_entry=lambda entry: entry)

            def fake_load_full_solc_bytecode(_bridge_module, _args):
                return ("Input.sol", "Input", "6000", "6001", {}, {})

            def fake_run_bridge_bytecode(_root, _args, _output_path, object_selector):
                self.assertEqual(object_selector, "runtime")
                return "0x6001"

            def fake_run_forge_harness(
                _forge, _solc, _outdir, _harness, evm_version
            ):
                self.assertEqual(evm_version, "cancun")
                return None

            compare_call.load_bridge = fake_load_bridge
            compare_call.load_full_solc_bytecode = fake_load_full_solc_bytecode
            compare_call.run_bridge_bytecode = fake_run_bridge_bytecode
            compare_call.run_forge_harness = fake_run_forge_harness
            sys.stdout = io.StringIO()
            sys.stderr = io.StringIO()

            result = compare_call.main(
                [
                    "Input.sol",
                    "--contract",
                    "Input",
                    "--calldata",
                    "0x00",
                    "--runtime-only",
                    "--solc",
                    "/tmp/solc",
                    "--lake",
                    "/tmp/lake",
                    "--forge",
                    "/tmp/forge",
                ]
            )
            stdout = sys.stdout.getvalue()
            stderr = sys.stderr.getvalue()
        finally:
            compare_call.load_bridge = old_load_bridge
            compare_call.load_full_solc_bytecode = old_load_full_solc_bytecode
            compare_call.run_bridge_bytecode = old_run_bridge_bytecode
            compare_call.run_forge_harness = old_run_forge_harness
            sys.stdout = old_stdout
            sys.stderr = old_stderr

        self.assertEqual(result, 1)
        self.assertEqual(stdout, "")
        self.assertIn("produced no bridge summaries", stderr)
        self.assertIn("structured Yul bridge handoff", stderr)

    def test_contract_call_compare_runtime_bytecode_uses_selected_object(self):
        old_run = compare_call.subprocess.run
        calls = []
        try:
            class Completed:
                returncode = 0
                stdout = ""
                stderr = ""

            def fake_run(command, **kwargs):
                calls.append((command, kwargs))
                if "--format" in command and "bytecode" in command:
                    output_path = Path(command[command.index("--output") + 1])
                    bridge_dir = Path(command[command.index("--bridge-json-dir") + 1])
                    bridge_dir.mkdir(parents=True)
                    (bridge_dir / "manifest.json").write_text(
                        json.dumps(
                            {
                                "schema": "evm-compiler.bridge-json-manifest.v1",
                                "entries": [],
                                "counts": {"entries": 0},
                            }
                        )
                    )
                    output_path.write_text("0x00\n")
                elif "--format" in command and "bridge-json-summary" in command:
                    output_path = Path(command[command.index("--output") + 1])
                    output_path.write_text(
                        json.dumps(
                            {
                                "schema": (
                                    "evm-compiler.solc-yul-bridge-"
                                    "manifest-summary.v1"
                                ),
                                "counts": {
                                    "objects": 0,
                                    "skippedContracts": 0,
                                    "calls": 0,
                                },
                                "objects": [],
                                "skippedContracts": [],
                                "backendCompatibility": {
                                    "profile": "current-yul-compiler",
                                    "status": "ready",
                                    "unsupportedPrimitiveNames": [],
                                    "objectBuiltinNames": [],
                                    "dialectBuiltinNames": [],
                                    "notes": [],
                                },
                            }
                        )
                    )
                return Completed()

            compare_call.subprocess.run = fake_run
            with tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "lean-runtime.hex"
                args = SimpleNamespace(
                    input=Path("Input.sol"),
                    solc="solc",
                    lake="lake",
                    lake_cwd=Path("."),
                    contract="Input",
                    namespace="Generated.Compare",
                    source_name=None,
                    optimized=True,
                    via_ir=True,
                    experimental=True,
                    auto_include_imports=True,
                    include_source=[],
                    remapping=[],
                    remappings_file=[],
                    linker_symbol=[],
                    solc_arg=[],
                )
                bytecode = compare_call.run_bridge_bytecode(
                    Path("/repo"),
                    args,
                    output,
                    "runtime",
                )
                summary_path = Path(directory) / "bridge-json-runtime-summary.json"
                self.assertTrue(summary_path.exists())
        finally:
            compare_call.subprocess.run = old_run

        self.assertEqual(bytecode, "0x00")
        bytecode_commands = [
            command for command, _kwargs in calls
            if "--format" in command and "bytecode" in command
        ]
        self.assertEqual(len(bytecode_commands), 1)
        self.assertIn("--object", bytecode_commands[0])
        self.assertEqual(
            bytecode_commands[0][bytecode_commands[0].index("--object") + 1],
            "runtime",
        )

    def test_contract_call_compare_can_render_creation_only_harness(self):
        harness = compare_call.render_harness(
            "0x00",
            "0x01",
            "0x02",
            "0x03",
            "0x",
            ["0x1234"],
            [0],
            0,
            compare_runtime=False,
        )

        self.assertIn("testCreationBytecodeCallResultsMatch", harness)
        self.assertNotIn("testRuntimeBytecodeCallResultsMatch", harness)
        self.assertNotIn("vm.etch", harness)

    def test_contract_call_compare_can_render_runtime_only_harness(self):
        harness = compare_call.render_harness(
            "0x00",
            "0x01",
            "0x",
            "0x03",
            "0x",
            ["0x1234"],
            [0],
            0,
            compare_creation=False,
        )

        self.assertNotIn("testCreationBytecodeCallResultsMatch", harness)
        self.assertIn("testRuntimeBytecodeCallResultsMatch", harness)
        self.assertIn("vm.etch", harness)

    def run_fake_forge_compare(
        self,
        full_status: int,
        lean_status: int,
        emit_results: bool = True,
        emit_summary: bool = True,
        summary_passed=None,
        summary_failed=None,
        summary_skipped=None,
        full_result_names=None,
        lean_result_names=None,
    ):
        root = Path(bridge.__file__).resolve().parent.parent
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            fake_solc = temp / "solc"
            fake_solc.write_text("#!/usr/bin/env bash\nexit 0\n")
            fake_solc.chmod(0o755)

            if emit_results:
                if full_result_names is None:
                    full_result_names = ["testAddOne()"]
                if lean_result_names is None:
                    lean_result_names = full_result_names
                if summary_passed is None:
                    summary_passed = len(full_result_names) if full_status == 0 else 0
                if summary_failed is None:
                    summary_failed = 0 if full_status == 0 else len(full_result_names)
                if summary_skipped is None:
                    summary_skipped = 0
                summary_line = (
                    f"Ran 1 test suite in 0.00s: {summary_passed} tests passed, "
                    f"{summary_failed} failed, {summary_skipped} skipped"
                )

                def result_echoes(status, names, indent):
                    result = "PASS" if status == 0 else "FAIL"
                    return "\n".join(
                        f'{indent}echo "[{result}] {name}"' for name in names
                    )

                lean_summary_echo = (
                    f'    echo "{summary_line}"' if emit_summary else ""
                )
                full_summary_echo = f'echo "{summary_line}"' if emit_summary else ""
                lean_result_block = f"""
  if [[ {lean_status} -eq 0 ]]; then
{result_echoes(0, lean_result_names, "    ")}
{lean_summary_echo}
  else
{result_echoes(1, lean_result_names, "    ")}
{lean_summary_echo}
  fi"""
                full_result_block = f"""
if [[ {full_status} -eq 0 ]]; then
{result_echoes(0, full_result_names, "  ")}
{full_summary_echo}
else
{result_echoes(1, full_result_names, "  ")}
{full_summary_echo}
fi"""
            else:
                lean_result_block = (
                    '\n  echo "No tests match the provided selectors"'
                )
                full_result_block = (
                    '\necho "No tests match the provided selectors"'
                )

            fake_forge = temp / "forge"
            fake_forge.write_text(
                f"""#!/usr/bin/env bash
set -euo pipefail
if [[ -n "${{SOLC_LEAN_REAL_SOLC:-}}" ]]; then{lean_result_block}
  exit {lean_status}
fi
{full_result_block}
exit {full_status}
"""
            )
            fake_forge.chmod(0o755)

            env = dict(os.environ)
            env.update(
                {
                    "SOLC": str(fake_solc),
                    "FORGE": str(fake_forge),
                    "LAKE": "lake",
                    "PYTHON": sys.executable,
                    "KEEP_TMP": "1",
                }
            )
            completed = subprocess.run(
                [
                    str(root / "scripts" / "compare_forge_solc_lean.sh"),
                    "--match-test",
                    "testAddOne",
                ],
                cwd=root,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        return completed

    def test_forge_compare_fails_on_status_mismatch(self):
        completed = self.run_fake_forge_compare(full_status=0, lean_status=1)
        self.assertEqual(completed.returncode, 1, completed.stderr)
        self.assertIn("forge_compare=fail", completed.stdout)
        self.assertIn("full_solc_status=0", completed.stdout)
        self.assertIn("solc_lean_status=1", completed.stdout)
        self.assertIn("--- solc-lean tail ---", completed.stdout)

    def test_forge_compare_reports_same_failure(self):
        completed = self.run_fake_forge_compare(full_status=1, lean_status=1)
        self.assertEqual(completed.returncode, 1, completed.stderr)
        self.assertIn("forge_compare=same_failure", completed.stdout)
        self.assertIn("status=1", completed.stdout)

    def test_forge_compare_passes_on_matching_results(self):
        completed = self.run_fake_forge_compare(full_status=0, lean_status=0)
        self.assertEqual(completed.returncode, 0, completed.stderr)

        output_lines = set(completed.stdout.splitlines())
        self.assertIn("forge_compare=pass", output_lines)
        self.assertIn("results_match=yes", output_lines)
        self.assertIn("forge_compare_result_count=1", output_lines)
        self.assertIn("forge_compare_result_1=PASS testAddOne()", output_lines)
        self.assertIn("forge_compare_tests_passed=1", output_lines)
        self.assertIn("forge_compare_tests_failed=0", output_lines)
        self.assertIn("forge_compare_tests_skipped=0", output_lines)

    def test_forge_compare_treats_result_order_as_set(self):
        completed = self.run_fake_forge_compare(
            full_status=0,
            lean_status=0,
            full_result_names=["testBeta()", "testAlpha()"],
            lean_result_names=["testAlpha()", "testBeta()"],
            summary_passed=2,
            summary_failed=0,
            summary_skipped=0,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)

        output_lines = set(completed.stdout.splitlines())
        self.assertIn("forge_compare=pass", output_lines)
        self.assertIn("results_match=yes", output_lines)
        self.assertIn("forge_compare_result_count=2", output_lines)
        self.assertIn("forge_compare_result_1=PASS testAlpha()", output_lines)
        self.assertIn("forge_compare_result_2=PASS testBeta()", output_lines)
        self.assertIn("forge_compare_tests_passed=2", output_lines)
        self.assertIn("forge_compare_tests_failed=0", output_lines)
        self.assertIn("forge_compare_tests_skipped=0", output_lines)

    def test_forge_compare_fails_when_selection_runs_no_tests(self):
        completed = self.run_fake_forge_compare(
            full_status=0,
            lean_status=0,
            emit_results=False,
        )
        self.assertEqual(completed.returncode, 1, completed.stderr)

        output_lines = set(completed.stdout.splitlines())
        self.assertIn("forge_compare=fail", output_lines)
        self.assertIn("reason=no_forge_test_results", output_lines)
        self.assertIn("status=0", output_lines)
        self.assertIn("--- full solc tail ---", completed.stdout)
        self.assertIn("--- solc-lean tail ---", completed.stdout)

    def test_forge_compare_fails_when_summary_is_missing(self):
        completed = self.run_fake_forge_compare(
            full_status=0,
            lean_status=0,
            emit_summary=False,
        )
        self.assertEqual(completed.returncode, 1, completed.stderr)

        output_lines = set(completed.stdout.splitlines())
        self.assertIn("forge_compare=fail", output_lines)
        self.assertIn("reason=forge_summary_missing", output_lines)
        self.assertIn("forge_compare_result_count=1", output_lines)

    def test_forge_compare_fails_when_result_count_disagrees_with_summary(self):
        completed = self.run_fake_forge_compare(
            full_status=0,
            lean_status=0,
            summary_passed=2,
            summary_failed=0,
            summary_skipped=0,
        )
        self.assertEqual(completed.returncode, 1, completed.stderr)

        output_lines = set(completed.stdout.splitlines())
        self.assertIn("forge_compare=fail", output_lines)
        self.assertIn("reason=forge_result_count_mismatch", output_lines)
        self.assertIn("forge_compare_result_count=1", output_lines)
        self.assertIn("forge_compare_summary_count=2", output_lines)
        self.assertIn("forge_compare_tests_passed=2", output_lines)
        self.assertIn("forge_compare_tests_failed=0", output_lines)
        self.assertIn("forge_compare_tests_skipped=0", output_lines)

    def test_forge_project_compare_runs_local_project_and_writes_report(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            project = root / "project"
            project.mkdir()
            fake_compare = root / "compare.sh"
            fake_compare.write_text(
                """#!/usr/bin/env bash
set -euo pipefail
printf 'forge_compare=pass\\n'
printf 'bridge_json_backend_compatibility=ready\\n'
printf 'bridge_json_summary_unsupported_primitives=none\\n'
printf 'bridge_json_summary_object_builtins=none\\n'
printf 'bridge_json_summary_dialect_builtins=none\\n'
printf 'bridge_json_summary_objects=1\\n'
printf 'bridge_json_summary_skipped_contracts=0\\n'
"""
            )
            fake_compare.chmod(0o755)
            out_dir = root / "out"
            old_stdout = sys.stdout
            try:
                sys.stdout = io.StringIO()
                result = forge_project_compare.main(
                    [
                        "--project-dir",
                        str(project),
                        "--out-dir",
                        str(out_dir),
                        "--compare-script",
                        str(fake_compare),
                        "--match-test",
                        "testFoo",
                        "--solc",
                        "/bin/echo",
                        "--lake",
                        "/bin/echo",
                        "--forge",
                        "/bin/echo",
                        "--python",
                        sys.executable,
                    ]
                )
                stdout = sys.stdout.getvalue()
            finally:
                sys.stdout = old_stdout

            report = json.loads((out_dir / "report.json").read_text())

        self.assertEqual(result, 0)
        self.assertIn("forge_project_compare=pass", stdout)
        self.assertEqual(report["schema"], forge_project_compare.REPORT_SCHEMA)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(report["compare"]["status"], "pass")
        self.assertEqual(
            report["compare"]["keyValues"]["bridge_json_backend_compatibility"],
            "ready",
        )
        compare_command = report["commands"][-1]["command"]
        self.assertIn("--match-test", compare_command)
        self.assertIn("testFoo", compare_command)

    def test_switch_default_is_separated_from_literal_cases(self):
        stmt = bridge.parse_stmt(
            {
                "nodeType": "YulSwitch",
                "expression": identifier("selector"),
                "cases": [
                    {
                        "nodeType": "YulCase",
                        "value": literal("0x12"),
                        "body": block([]),
                        "nativeSrc": "0:0:0",
                    },
                    {
                        "nodeType": "YulCase",
                        "value": "default",
                        "body": block(
                            [
                                {
                                    "nodeType": "YulBreak",
                                    "nativeSrc": "0:0:0",
                                }
                            ]
                        ),
                        "nativeSrc": "0:0:0",
                    },
                ],
                "nativeSrc": "0:0:0",
            }
        )
        self.assertIsInstance(stmt, bridge.Switch)
        self.assertEqual(stmt.cases[0][0].word(), 0x12)
        self.assertEqual(len(stmt.default), 1)


if __name__ == "__main__":
    unittest.main()
