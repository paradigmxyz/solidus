#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
SOLC_835="${SOLC_835:-$HOME/.solc-select/artifacts/solc-0.8.35/solc-0.8.35}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-frontend.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

if ! command -v "$PYTHON_BIN" >/dev/null 2>&1; then
  printf 'error: required executable not found: %s\n' "$PYTHON_BIN" >&2
  exit 1
fi

for executable in "$LAKE_BIN" "$SOLC_826" "$SOLC_835"; do
  if [[ ! -x "$executable" ]]; then
    printf 'error: required executable not found: %s\n' "$executable" >&2
    exit 1
  fi
done

"$PYTHON_BIN" - "$ROOT" "$OUTDIR" "$SOLC_826" "$SOLC_835" <<'PY'
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
outdir = pathlib.Path(sys.argv[2])
solcs = {
    "0.8.26": (pathlib.Path(sys.argv[3]), False),
    "0.8.35": (pathlib.Path(sys.argv[4]), True),
}
source = (root / "examples" / "Simple.sol").read_text()

def standard_input(experimental: bool) -> dict:
    settings = {
        "viaIR": True,
        "evmVersion": "cancun",
        "optimizer": {"enabled": True, "details": {"yul": True}},
        "outputSelection": {
            "*": {
                "*": [
                    "irOptimizedAst",
                    "irOptimized",
                    "metadata",
                    "evm.bytecode.object",
                    "evm.deployedBytecode.object",
                ],
                "": ["ast"],
            }
        },
    }
    if experimental:
        settings["experimental"] = True
    return {
        "language": "Solidity",
        "sources": {"Simple.sol": {"content": source}},
        "settings": settings,
    }

for version, (solc, experimental) in solcs.items():
    completed = subprocess.run(
        [str(solc), "--standard-json"],
        input=json.dumps(standard_input(experimental)),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    data = json.loads(completed.stdout)
    if "contracts" not in data:
        raise SystemExit(f"solc {version} did not produce contracts: {data.get('errors')!r}")
    (outdir / f"simple-{version}.standard-output.json").write_text(
        json.dumps(data, separators=(",", ":"))
    )

malformed = json.loads((outdir / "simple-0.8.26.standard-output.json").read_text())
malformed["contracts"]["Simple.sol"]["Simple"]["irOptimizedAst"]["nodeType"] = "YulBogus"
(outdir / "malformed-node.standard-output.json").write_text(json.dumps(malformed))

mixed = {
    "contracts": {
        "Fixture.sol": {
            "Fixture": {
                "metadata": json.dumps({"settings": {"evmVersion": "cancun"}}),
                "irOptimizedAst": {
                    "nodeType": "YulObject",
                    "name": "Fixture",
                    "code": {"block": {"nodeType": "YulBlock", "statements": []}},
                    "subObjects": [
                        {"nodeType": "YulData", "name": "first", "value": "aa"},
                        {
                            "nodeType": "YulObject",
                            "name": "Child",
                            "code": {"block": {"nodeType": "YulBlock", "statements": []}},
                            "subObjects": [],
                        },
                        {"nodeType": "YulData", "name": "second", "value": "bbcc"},
                    ],
                },
            }
        }
    }
}
(outdir / "mixed-order.standard-output.json").write_text(json.dumps(mixed))

nested_clz = {
    "contracts": {
        "Fixture.sol": {
            "Fixture": {
                "metadata": json.dumps({"settings": {"evmVersion": "cancun"}}),
                "irOptimizedAst": {
                    "nodeType": "YulObject",
                    "name": "Fixture",
                    "code": {
                        "block": {
                            "nodeType": "YulBlock",
                            "statements": [
                                {
                                    "nodeType": "YulFunctionDefinition",
                                    "name": "f",
                                    "parameters": [],
                                    "returnVariables": [],
                                    "body": {
                                        "nodeType": "YulBlock",
                                        "statements": [
                                            {
                                                "nodeType": "YulFunctionDefinition",
                                                "name": "g",
                                                "parameters": [],
                                                "returnVariables": [],
                                                "body": {
                                                    "nodeType": "YulBlock",
                                                    "statements": [
                                                        {
                                                            "nodeType": "YulVariableDeclaration",
                                                            "variables": [{"name": "x"}],
                                                            "value": {
                                                                "nodeType": "YulFunctionCall",
                                                                "functionName": {"name": "clz"},
                                                                "arguments": [
                                                                    {
                                                                        "nodeType": "YulLiteral",
                                                                        "kind": "number",
                                                                        "value": "1",
                                                                    }
                                                                ],
                                                            },
                                                        }
                                                    ],
                                                },
                                            },
                                            {
                                                "nodeType": "YulExpressionStatement",
                                                "expression": {
                                                    "nodeType": "YulFunctionCall",
                                                    "functionName": {"name": "g"},
                                                    "arguments": [],
                                                },
                                            },
                                        ],
                                    },
                                },
                                {
                                    "nodeType": "YulExpressionStatement",
                                    "expression": {
                                        "nodeType": "YulFunctionCall",
                                        "functionName": {"name": "f"},
                                        "arguments": [],
                                    },
                                },
                            ],
                        }
                    },
                    "subObjects": [],
                },
            }
        }
    }
}
(outdir / "nested-clz.standard-output.json").write_text(json.dumps(nested_clz))

bad_scope = json.loads(json.dumps(nested_clz))
bad_scope["contracts"]["Fixture.sol"]["Fixture"]["irOptimizedAst"]["code"]["block"][
    "statements"
] = [
    {
        "nodeType": "YulAssignment",
        "variableNames": [{"name": "missing"}],
        "value": {"nodeType": "YulLiteral", "kind": "number", "value": "1"},
    }
]
(outdir / "bad-scope.standard-output.json").write_text(json.dumps(bad_scope))

linker_metadata = {
    "contracts": {
        "Fixture.sol": {
            "Fixture": {
                "metadata": json.dumps(
                    {
                        "settings": {
                            "evmVersion": "cancun",
                            "libraries": {
                                "MathLib.sol": {
                                    "MathLib": "000000000000000000000000000000000000002a",
                                }
                            },
                        }
                    }
                ),
                "irOptimizedAst": {
                    "nodeType": "YulObject",
                    "name": "Fixture",
                    "code": {
                        "block": {
                            "nodeType": "YulBlock",
                            "statements": [
                                {
                                    "nodeType": "YulVariableDeclaration",
                                    "variables": [{"name": "linked"}],
                                    "value": {
                                        "nodeType": "YulFunctionCall",
                                        "functionName": {"name": "linkersymbol"},
                                        "arguments": [
                                            {
                                                "nodeType": "YulLiteral",
                                                "kind": "string",
                                                "value": "MathLib.sol:MathLib",
                                            }
                                        ],
                                    },
                                }
                            ],
                        }
                    },
                    "subObjects": [],
                },
            }
        }
    }
}
(outdir / "linker-metadata.standard-output.json").write_text(
    json.dumps(linker_metadata)
)

bad_linker_metadata = json.loads(json.dumps(linker_metadata))
bad_linker_metadata["contracts"]["Fixture.sol"]["Fixture"]["metadata"] = json.dumps(
    {
        "settings": {
            "evmVersion": "cancun",
            "libraries": {"MathLib.sol": {"MathLib": "not-hex"}},
        }
    }
)
(outdir / "bad-linker-metadata.standard-output.json").write_text(
    json.dumps(bad_linker_metadata)
)
PY

cat > "$OUTDIR/raw_decode_runner.lean" <<LEAN
import EvmCompiler.Solidity.RawAstPublic

open EvmCompiler
open EvmCompiler.Solidity

def readRaw (name : String) : IO String :=
  IO.FS.readFile ("$OUTDIR/" ++ name)

def decodeSimple (version : String) (selector : RawAst.ObjectSelector) : IO Unit := do
  let raw <- readRaw ("simple-" ++ version ++ ".standard-output.json")
  let selection : RawAst.Selection :=
    { source? := some "Simple.sol"
      contract? := some "Simple"
      objectSelector := selector
      astOutput := "irOptimizedAst" }
  match RawAst.decodeAndElaborateSolcIr? raw selection with
  | none => throw <| IO.userError ("raw decode failed for solc " ++ version)
  | some program =>
      IO.println <|
        "raw_solc_frontend_" ++ version ++
        "_object=" ++ program.object.name ++
        " dispatcher=" ++ toString program.object.dispatcher.length ++
        " functions=" ++ toString program.object.functions.length ++
        " data=" ++ toString program.object.data.length ++
        " children=" ++ toString program.object.objects.length ++
        " items=" ++ toString program.object.items.length

def compileSimpleRuntime (version : String) : IO Unit := do
  let raw <- readRaw ("simple-" ++ version ++ ".standard-output.json")
  let selection : RawAst.Selection :=
    { source? := some "Simple.sol"
      contract? := some "Simple"
      objectSelector := .runtime
      astOutput := "irOptimizedAst" }
  match RawAst.compileArtifactFromRawSolcIr? raw selection with
  | none => throw <| IO.userError ("raw artifact compile failed for solc " ++ version)
  | some artifact =>
      IO.println <|
        "raw_solc_frontend_" ++ version ++
        "_artifact_bytes=" ++ toString artifact.image.bytes.length

def expectMalformedRejected : IO Unit := do
  let raw <- readRaw "malformed-node.standard-output.json"
  let selection : RawAst.Selection :=
    { source? := some "Simple.sol"
      contract? := some "Simple"
      astOutput := "irOptimizedAst" }
  match RawAst.decodeAndElaborateSolcIr? raw selection with
  | none => IO.println "raw_solc_frontend_malformed_node=rejected"
  | some _ => throw <| IO.userError "malformed raw Yul node was accepted"

def expectMixedOrder : IO Unit := do
  let raw <- readRaw "mixed-order.standard-output.json"
  let selection : RawAst.Selection :=
    { source? := some "Fixture.sol"
      contract? := some "Fixture"
      astOutput := "irOptimizedAst" }
  match RawAst.decodeAndElaborateSolcIr? raw selection with
  | none => throw <| IO.userError "mixed object/data raw decode failed"
  | some program =>
      match program.object.items with
      | [.data 0, .object 0, .data 1] =>
          IO.println "raw_solc_frontend_mixed_order=preserved"
      | other =>
          throw <| IO.userError ("mixed object/data order drift: " ++ reprStr other)

def hasFunctionStmtFuel : Nat -> List Frontend.Stmt -> Bool
  | 0, _ => false
  | _, [] => false
  | _fuel + 1, .functionDef _ _ _ _ :: _ => true
  | fuel + 1, .block body :: rest =>
      hasFunctionStmtFuel fuel body || hasFunctionStmtFuel fuel rest
  | fuel + 1, .switch _ cases defaultBody :: rest =>
      cases.any (fun item => hasFunctionStmtFuel fuel item.snd) ||
        hasFunctionStmtFuel fuel defaultBody || hasFunctionStmtFuel fuel rest
  | fuel + 1, .forLoop pre _ post body :: rest =>
      hasFunctionStmtFuel fuel pre || hasFunctionStmtFuel fuel post ||
        hasFunctionStmtFuel fuel body || hasFunctionStmtFuel fuel rest
  | fuel + 1, .ifThen _ body :: rest =>
      hasFunctionStmtFuel fuel body || hasFunctionStmtFuel fuel rest
  | fuel + 1, _ :: rest => hasFunctionStmtFuel fuel rest

def hasFunctionStmt (stmts : List Frontend.Stmt) : Bool :=
  hasFunctionStmtFuel 100000 stmts

def expectNestedClz : IO Unit := do
  let raw <- readRaw "nested-clz.standard-output.json"
  let selection : RawAst.Selection :=
    { source? := some "Fixture.sol"
      contract? := some "Fixture"
      astOutput := "irOptimizedAst" }
  match RawAst.decodeAndElaborateSolcIr? raw selection with
  | none => throw <| IO.userError "nested/clz raw decode failed"
  | some program =>
      let names := program.object.functions.map Prod.fst
      if !(names.contains "f") then
        throw <| IO.userError ("missing top-level f: " ++ reprStr names)
      if !(names.contains "__yul_gen_0_g") then
        throw <| IO.userError ("missing hoisted nested g: " ++ reprStr names)
      if !(names.contains "__yul_gen_1_clz") then
        throw <| IO.userError ("missing clz helper: " ++ reprStr names)
      match program.object.functions.find? (fun entry => entry.fst == "f") with
      | none => throw <| IO.userError "missing f body"
      | some (_, fn) =>
          if hasFunctionStmt fn.body then
            IO.println "raw_solc_frontend_nested_clz=checked"
          else
            throw <| IO.userError "nested function definition was erased"

def expectBadScopeRejected : IO Unit := do
  let raw <- readRaw "bad-scope.standard-output.json"
  let selection : RawAst.Selection :=
    { source? := some "Fixture.sol"
      contract? := some "Fixture"
      astOutput := "irOptimizedAst" }
  match RawAst.decodeAndElaborateSolcIr? raw selection with
  | none => IO.println "raw_solc_frontend_bad_scope=rejected"
  | some _ => throw <| IO.userError "bad lexical scope was accepted"

def expectLinkerMetadata : IO Unit := do
  let raw <- readRaw "linker-metadata.standard-output.json"
  let selection : RawAst.Selection :=
    { source? := some "Fixture.sol"
      contract? := some "Fixture"
      astOutput := "irOptimizedAst" }
  match RawAst.decodeLinkerSymbols? raw selection with
  | some [("MathLib.sol:MathLib", value)] =>
      if value != EvmYul.UInt256.ofNat 42 then
        throw <| IO.userError ("unexpected linker value: " ++ reprStr value)
  | other =>
      throw <| IO.userError ("unexpected linker metadata: " ++ reprStr other)
  match RawAst.compileArtifactFromRawSolcIrWithLinkerSymbols? raw selection [] with
  | none => IO.println "raw_solc_frontend_linker_empty_symbols=rejected"
  | some _ =>
      throw <| IO.userError "explicit empty linker symbols unexpectedly compiled"
  match RawAst.compileArtifactFromRawSolcIr? raw selection with
  | none => throw <| IO.userError "embedded linker metadata artifact compile failed"
  | some artifact =>
      IO.println <|
        "raw_solc_frontend_linker_metadata_artifact_bytes=" ++
          toString artifact.image.bytes.length

def expectBadLinkerMetadataRejected : IO Unit := do
  let raw <- readRaw "bad-linker-metadata.standard-output.json"
  let selection : RawAst.Selection :=
    { source? := some "Fixture.sol"
      contract? := some "Fixture"
      astOutput := "irOptimizedAst" }
  match RawAst.decodeLinkerSymbols? raw selection with
  | none => IO.println "raw_solc_frontend_bad_linker_metadata=rejected"
  | some symbols =>
      throw <| IO.userError ("bad linker metadata was accepted: " ++ reprStr symbols)
  match RawAst.compileArtifactFromRawSolcIr? raw selection with
  | none => pure ()
  | some _ => throw <| IO.userError "bad linker metadata artifact compiled"

def main : IO Unit := do
  decodeSimple "0.8.26" .creation
  decodeSimple "0.8.26" .runtime
  compileSimpleRuntime "0.8.26"
  decodeSimple "0.8.35" .creation
  decodeSimple "0.8.35" .runtime
  compileSimpleRuntime "0.8.35"
  expectMalformedRejected
  expectMixedOrder
  expectNestedClz
  expectBadScopeRejected
  expectLinkerMetadata
  expectBadLinkerMetadataRejected
  IO.println "raw_solc_frontend_smoke=pass"
LEAN

"$LAKE_BIN" env lean --run "$OUTDIR/raw_decode_runner.lean"
