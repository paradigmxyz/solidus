#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
SOLC_835="${SOLC_835:-$HOME/.solc-select/artifacts/solc-0.8.35/solc-0.8.35}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-differential.XXXXXX")"
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

"$PYTHON_BIN" - \
  "$ROOT" "$OUTDIR" "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_826" "$SOLC_835" <<'PY'
import copy
import importlib.util
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
outdir = pathlib.Path(sys.argv[2])
python_bin = pathlib.Path(sys.argv[3])
lake_bin = pathlib.Path(sys.argv[4])
solcs = {
    "0.8.26": pathlib.Path(sys.argv[5]),
    "0.8.35": pathlib.Path(sys.argv[6]),
}

bridge_path = root / "scripts" / "solidity_to_yul_lean.py"
spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
bridge = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = bridge
spec.loader.exec_module(bridge)

cases = [
    ("simple", "Simple.sol", "Simple"),
    ("loop", "LoopBox.sol", "LoopBox"),
    ("abi-control", "AbiControlSurfaceBox.sol", "AbiControlSurfaceBox"),
    ("dynamic-storage", "DynamicStorageSurfaceBox.sol", "DynamicStorageSurfaceBox"),
    ("effect-ordering", "EffectOrderingSurfaceBox.sol", "EffectOrderingSurfaceBox"),
    ("proxy-lifecycle", "ProxyLifecycleSurfaceBox.sol", "ProxyLifecycleSurfaceBox"),
    ("immutable", "ImmutableBox.sol", "ImmutableBox"),
    ("external-call", "ExternalCallBox.sol", "ExternalCallBox"),
]

lean_cases = []
for version, solc in solcs.items():
    for label, filename, contract in cases:
        source_path = root / "examples" / filename
        source_name = source_path.name
        request = bridge.standard_json_input(
            source_name,
            source_path.read_text(),
            via_ir=True,
            optimized=True,
            experimental=True,
            require_bytecode=True,
            evm_version="cancun",
        )
        stem = f"{label}-{version}"
        request_path = outdir / f"{stem}.standard-input.json"
        request_path.write_text(json.dumps(request, separators=(",", ":")))

        raw_output = bridge.run_solc(str(solc), copy.deepcopy(request), ())
        raw_path = outdir / f"{stem}.standard-output.json"
        raw_path.write_text(json.dumps(raw_output, separators=(",", ":")))

        for selector in ("runtime", "creation"):
            bridge_json_path = outdir / f"{stem}-{selector}.bridge.json"
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
                    contract,
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
            lean_cases.append(
                {
                    "label": f"{stem}-{selector}",
                    "raw": str(raw_path),
                    "bridge": str(bridge_json_path),
                    "source": source_name,
                    "contract": contract,
                    "selector": selector,
                    "linker_symbols": [],
                }
            )

linked_library_sources = {
    "src/lib/ScaleLib.sol": """
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

library ScaleLib {
    function scale(uint256 value) internal pure returns (uint256) {
        return value * 7 + 3;
    }

    function folded(uint256 first, uint256 second, uint256 third)
        internal
        pure
        returns (uint256)
    {
        return scale(first) + scale(second) + scale(third);
    }
}
""",
    "src/LibraryHarness.sol": """
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ScaleLib} from "./lib/ScaleLib.sol";

contract LibraryHarness {
    using ScaleLib for uint256;

    function score(uint256 value) public pure returns (uint256) {
        return value.scale() + (value ^ 0x55);
    }

    function folded(uint256 first, uint256 second, uint256 third)
        public
        pure
        returns (uint256)
    {
        return ScaleLib.folded(first, second, third);
    }
}
""",
}

linked_library_symbols = [("src/lib/ScaleLib.sol:ScaleLib", 42)]
for version, solc in solcs.items():
    label = f"linked-library-{version}"
    source_name = "src/LibraryHarness.sol"
    contract = "LibraryHarness"
    request = {
        "language": "Solidity",
        "sources": {
            name: {"content": content}
            for name, content in linked_library_sources.items()
        },
        "settings": {
            "viaIR": True,
            "evmVersion": "cancun",
            "experimental": True,
            "optimizer": {"enabled": True, "details": {"yul": True}},
            "libraries": {
                "src/lib/ScaleLib.sol": {
                    "ScaleLib": "0x000000000000000000000000000000000000002a",
                }
            },
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
        },
    }
    request_path = outdir / f"{label}.standard-input.json"
    request_path.write_text(json.dumps(request, separators=(",", ":")))

    raw_output = bridge.run_solc(str(solc), copy.deepcopy(request), ())
    raw_path = outdir / f"{label}.standard-output.json"
    raw_path.write_text(json.dumps(raw_output, separators=(",", ":")))

    for selector in ("runtime", "creation"):
        bridge_json_path = outdir / f"{label}-{selector}.bridge.json"
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
                contract,
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
        lean_cases.append(
            {
                "label": f"{label}-{selector}",
                "raw": str(raw_path),
                "bridge": str(bridge_json_path),
                "source": source_name,
                "contract": contract,
                "selector": selector,
                "linker_symbols": linked_library_symbols,
            }
        )

def lean_string(value: str) -> str:
    return bridge.lean_string(value)

def lean_selector(value: str) -> str:
    if value == "creation":
        return "RawAst.ObjectSelector.creation"
    if value == "runtime":
        return "RawAst.ObjectSelector.runtime"
    raise AssertionError(value)

def lean_linker_symbols(entries) -> str:
    if not entries:
        return "[]"
    rendered = [
        f"({lean_string(name)}, EvmYul.UInt256.ofNat {value})"
        for name, value in entries
    ]
    return "[" + ", ".join(rendered) + "]"

lean_case_entries = []
for case in lean_cases:
    lean_case_entries.append(
        "\n".join(
            [
                "  {",
                f"    label := {lean_string(case['label'])}",
                f"    rawPath := {lean_string(case['raw'])}",
                f"    bridgePath := {lean_string(case['bridge'])}",
                f"    source := {lean_string(case['source'])}",
                f"    contract := {lean_string(case['contract'])}",
                f"    selector := {lean_selector(case['selector'])}",
                f"    linkerSymbols := {lean_linker_symbols(case['linker_symbols'])}",
                "  }",
            ]
        )
    )

runner = f"""import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.BridgeJson

open EvmCompiler
open EvmCompiler.Solidity

structure DifferentialCase where
  label : String
  rawPath : String
  bridgePath : String
  source : String
  contract : String
  selector : RawAst.ObjectSelector
  linkerSymbols : List (Frontend.Name × Frontend.Word)

def differentialCases : List DifferentialCase :=
[
{','.join(lean_case_entries)}
]

def fail {{α : Type}} (message : String) : IO α :=
  throw (IO.userError message)

def optionNameString : Option Frontend.Name -> String
  | none => "_"
  | some name => name

def itemRefString : Frontend.ObjectItemRef -> String
  | .data index => "data:" ++ toString index
  | .object index => "object:" ++ toString index

def bytesChecksum (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => (acc * 131 + byte.toNat) % 1000000007) 0

def dataSectionString (data : Frontend.DataSection) : String :=
  optionNameString data.name? ++ ":" ++ toString data.bytes.length ++ ":" ++
    toString (bytesChecksum data.bytes)

def joinStrings (values : List String) : String :=
  String.intercalate "," values

def stringDigest (text : String) : String :=
  let bytes := text.toUTF8.toList
  toString bytes.length ++ ":" ++ toString (bytesChecksum bytes)

def reprDigest {{α : Type}} [Repr α] (value : α) : String :=
  stringDigest (reprStr value)

def functionString (entry : Frontend.Name × Frontend.FunctionDef) : String :=
  entry.fst ++ ":" ++ reprDigest entry.snd

def firstDiffIndexAux : List Char -> List Char -> Nat -> Nat
  | [], [], index => index
  | [], _ :: _, index => index
  | _ :: _, [], index => index
  | a :: as, b :: bs, index =>
      if a == b then firstDiffIndexAux as bs (index + 1) else index

def firstDiffIndex (left right : String) : Nat :=
  firstDiffIndexAux left.toList right.toList 0

def stringWindow (text : String) (start size : Nat) : String :=
  String.ofList ((text.toList.drop start).take size)

def reprDiffReport {{α : Type}} [Repr α] (left right : α) : String :=
  let leftText := reprStr left
  let rightText := reprStr right
  let index := firstDiffIndex leftText rightText
  "firstDiff=" ++ toString index ++
    "\\nrawWindow=" ++ stringWindow leftText index 240 ++
    "\\nbridgeWindow=" ++ stringWindow rightText index 240

def objectShapeFuel : Nat -> Frontend.Object -> String
  | 0, object => object.name ++ ":fuel"
  | fuel + 1, object =>
      joinStrings
        [ object.name
        , toString object.dispatcher.length ++ ":" ++ reprDigest object.dispatcher
        , joinStrings (object.functions.map functionString)
        , joinStrings (object.data.map dataSectionString)
        , joinStrings (object.objects.map (objectShapeFuel fuel))
        , joinStrings (object.items.map itemRefString)
        ]

def objectShape (object : Frontend.Object) : String :=
  objectShapeFuel 100000 object

def artifactShapeFuel :
    Nat -> Frontend.VerifiedStackObjectArtifact -> String
  | 0, artifact => artifact.image.name ++ ":fuel"
  | fuel + 1, artifact =>
      joinStrings
        [ artifact.image.name
        , toString artifact.image.size
        , joinStrings (artifact.children.map (artifactShapeFuel fuel))
        ]

def artifactShapeWith? (program : Frontend.Program)
    (linkerSymbols : List (Frontend.Name × Frontend.Word)) : Option String := do
  let artifact <- program.compileArtifactWithLinkerSymbols? linkerSymbols
  some (artifactShapeFuel 100000 artifact)

def selectionFor (case : DifferentialCase) : RawAst.Selection :=
  {{ source? := some case.source
    contract? := some case.contract
    objectSelector := case.selector
    astOutput := "irOptimizedAst" }}

def rawArtifactShape? (case : DifferentialCase) : IO (Option String) := do
  let input <- IO.FS.readFile case.rawPath
  match RawAst.compileArtifactFromRawSolcIr? input (selectionFor case) with
  | some artifact => pure (some (artifactShapeFuel 100000 artifact))
  | none => pure none

def expectRawLinkerSymbols (case : DifferentialCase) : IO Unit := do
  let input <- IO.FS.readFile case.rawPath
  match RawAst.decodeLinkerSymbols? input (selectionFor case) with
  | some symbols =>
      if symbols != case.linkerSymbols then
        fail (case.label ++ ": linker symbol metadata mismatch " ++
          reprStr symbols ++ " != " ++ reprStr case.linkerSymbols)
  | none => fail (case.label ++ ": raw linker metadata decode failed")

def decodeBridgeProgram (path : String) : IO Frontend.Program := do
  let input <- IO.FS.readFile path
  match Frontend.BridgeJson.parseProgram? input with
  | .ok program => pure program
  | .error err => fail ("bridge decode failed: " ++ err)

def decodeRawProgram (case : DifferentialCase) : IO Frontend.Program := do
  let input <- IO.FS.readFile case.rawPath
  match RawAst.decodeAndElaborateSolcIr? input (selectionFor case) with
  | some program => pure program
  | none => fail ("raw decode failed for " ++ case.label)

def comparePrograms (case : DifferentialCase)
    (raw bridge : Frontend.Program) : IO String := do
  if raw.source != bridge.source then
    fail (case.label ++ ": source mismatch " ++ raw.source ++ " != " ++ bridge.source)
  if raw.contract != bridge.contract then
    fail (case.label ++ ": contract mismatch " ++ raw.contract ++ " != " ++ bridge.contract)
  let rawShape := objectShape raw.object
  let bridgeShape := objectShape bridge.object
  if rawShape != bridgeShape then
    fail (case.label ++ ": object shape mismatch\\n" ++
      reprDiffReport raw.object.dispatcher bridge.object.dispatcher ++
      "\\nraw=" ++ rawShape ++ "\\nbridge=" ++ bridgeShape)
  let rawArtifact <- rawArtifactShape? case
  let bridgeArtifact := artifactShapeWith? bridge case.linkerSymbols
  match rawArtifact, bridgeArtifact with
  | some rawArtifact, some bridgeArtifact =>
      if rawArtifact != bridgeArtifact then
        fail (case.label ++ ": artifact mismatch " ++ rawArtifact ++ " != " ++ bridgeArtifact)
  | none, some _ =>
      fail (case.label ++ ": raw artifact failed while bridge artifact compiled")
  | some _, none =>
      fail (case.label ++ ": bridge artifact failed while raw artifact compiled")
  | none, none =>
      fail (case.label ++ ": both artifacts failed")
  pure (rawArtifact.getD "none")

def runCase (case : DifferentialCase) : IO Unit := do
  expectRawLinkerSymbols case
  let raw <- decodeRawProgram case
  let bridge <- decodeBridgeProgram case.bridgePath
  let artifact <- comparePrograms case raw bridge
  IO.println
    ("raw_solc_frontend_differential\\t" ++ case.label ++
      "\\tobject=" ++ raw.object.name ++
      "\\tshape=" ++ objectShape raw.object ++
      "\\tlinkers=" ++ toString case.linkerSymbols.length ++
      "\\tartifact=" ++ artifact)

def main : IO Unit := do
  for case in differentialCases do
    runCase case
  IO.println ("raw_solc_frontend_differential_count=" ++ toString differentialCases.length)
  IO.println "raw_solc_frontend_differential=pass"
"""

(outdir / "raw_bridge_differential_runner.lean").write_text(runner)
PY

"$LAKE_BIN" env lean --run "$OUTDIR/raw_bridge_differential_runner.lean"
