"""Generate Lean raw-vs-bridge frontend differential runners."""

from __future__ import annotations

from pathlib import Path
from typing import Callable, Iterable, Mapping, Sequence


LinkerSymbol = tuple[str, int]
DifferentialCase = Mapping[str, object]


def lean_selector(value: str) -> str:
    if value == "creation":
        return "RawAst.ObjectSelector.creation"
    if value == "runtime":
        return "RawAst.ObjectSelector.runtime"
    raise ValueError(f"unsupported raw object selector: {value!r}")


def lean_linker_symbols(
    entries: Sequence[LinkerSymbol],
    *,
    lean_string: Callable[[str], str],
) -> str:
    if not entries:
        return "[]"
    rendered = [
        f"({lean_string(name)}, EvmYul.UInt256.ofNat {value})"
        for name, value in entries
    ]
    return "[" + ", ".join(rendered) + "]"


def case_to_lean(
    case: DifferentialCase,
    *,
    lean_string: Callable[[str], str],
) -> str:
    linker_symbols = case.get("linker_symbols", [])
    if not isinstance(linker_symbols, list):
        raise TypeError(f"{case.get('label', '<unknown>')}: linker_symbols must be a list")

    return "\n".join(
        [
            "  {",
            f"    label := {lean_string(str(case['label']))}",
            f"    rawPath := {lean_string(str(case['raw']))}",
            f"    bridgePath := {lean_string(str(case['bridge']))}",
            f"    source := {lean_string(str(case['source']))}",
            f"    contract := {lean_string(str(case['contract']))}",
            f"    selector := {lean_selector(str(case['selector']))}",
            "    compareArtifacts := "
            + ("true" if case.get("compare_artifacts", True) else "false"),
            "    linkerSymbols := "
            + lean_linker_symbols(linker_symbols, lean_string=lean_string),
            "  }",
        ]
    )


def write_runner(
    path: Path,
    cases: Iterable[DifferentialCase],
    *,
    lean_string: Callable[[str], str],
) -> None:
    case_entries = [case_to_lean(case, lean_string=lean_string) for case in cases]
    rendered_cases = ",".join(case_entries)
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
  compareArtifacts : Bool
  linkerSymbols : List (Frontend.Name × Frontend.Word)

def differentialCases : List DifferentialCase :=
[
{rendered_cases}
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
  if !case.compareArtifacts then
    pure "skipped"
  else
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
    path.write_text(runner)
