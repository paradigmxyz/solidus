#!/usr/bin/env bash
# Unlinked-library smoke: compile examples/ExternalMathLib.sol without
# settings.libraries, export solc-compatible linkReferences, and check —
# executably, on real solc output — the link-time patch equation of
# Object.patchImmutablesAndLibraries_image_ofCompileUnlinked, plus the
# linked compile through the ordinary path.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-unlinked-library.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

for executable in "$LAKE_BIN" "$SOLC_826"; do
  if [[ ! -x "$executable" ]]; then
    printf 'error: required executable not found: %s\n' "$executable" >&2
    exit 1
  fi
done

"$PYTHON_BIN" - "$ROOT" "$OUTDIR" "$SOLC_826" <<'PY'
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
outdir = pathlib.Path(sys.argv[2])
solc = sys.argv[3]

source = (root / "examples" / "ExternalMathLib.sol").read_text()
selection = {
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
}


def run_solc(libraries):
    settings = {
        "viaIR": True,
        "evmVersion": "cancun",
        "optimizer": {"enabled": True, "details": {"yul": True}},
        "outputSelection": selection,
    }
    if libraries:
        settings["libraries"] = libraries
    request = {
        "language": "Solidity",
        "sources": {"examples/ExternalMathLib.sol": {"content": source}},
        "settings": settings,
    }
    completed = subprocess.run(
        [solc, "--standard-json"],
        input=json.dumps(request),
        capture_output=True,
        text=True,
        check=True,
    )
    output = json.loads(completed.stdout)
    errors = [
        e for e in output.get("errors", []) if e.get("severity") == "error"
    ]
    assert not errors, errors
    return completed.stdout


(outdir / "unlinked.standard-output.json").write_text(run_solc(None))
(outdir / "linked.standard-output.json").write_text(
    run_solc(
        {
            "examples/ExternalMathLib.sol": {
                "ExternalMathLib": "0x1234567890AbcdEF1234567890aBcdef12345678"
            }
        }
    )
)
PY

RUNNER="$OUTDIR/unlinked_library_runner.lean"
cat > "$RUNNER" <<EOF
import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.ImmutablePatch

open EvmCompiler
open EvmCompiler.Solidity

def unlinkedPath : String := "$OUTDIR/unlinked.standard-output.json"
def linkedPath : String := "$OUTDIR/linked.standard-output.json"
EOF
cat >> "$RUNNER" <<'EOF'

def libraryName : Frontend.Name :=
  "examples/ExternalMathLib.sol:ExternalMathLib"

def libraryAddress : Frontend.Word :=
  EvmYul.UInt256.ofNat 0x1234567890AbcdEF1234567890aBcdef12345678

def fail {alpha : Type} (message : String) : IO alpha :=
  throw (IO.userError message)

def selectionFor (selector : RawAst.ObjectSelector) : RawAst.Selection :=
  { source? := some "examples/ExternalMathLib.sol"
    contract? := some "ExternalMathBox"
    objectSelector := selector
    astOutput := "irOptimizedAst" }

def checkSelector (label : String) (selector : RawAst.ObjectSelector)
    (expectOwnLinkRefs : Bool) : IO Unit := do
  let input <- IO.FS.readFile unlinkedPath
  let some program :=
      RawAst.decodeAndElaborateSolcIr? input (selectionFor selector)
    | fail (label ++ ": raw decode failed")
  let some linkerSymbols :=
      RawAst.decodeLinkerSymbols? input (selectionFor selector)
    | fail (label ++ ": linker metadata decode failed")
  if linkerSymbols != [] then
    fail (label ++ ": expected empty linker metadata")
  let missing := program.object.missingLinkerSymbolNames linkerSymbols
  if missing != [libraryName] then
    fail (label ++ ": unexpected missing names " ++ toString missing)
  let some artifact := program.compileArtifactUnlinked? linkerSymbols
    | fail (label ++ ": unlinked compile returned none")
  let substituted :=
    program.object.substituteUnlinkedLibraries missing
  let ownRefs := artifact.ownImmutableReferences substituted
  let linkRefs := artifact.image.linkReferences missing
  let ownLinkCount :=
    (ownRefs.filter (fun entry => missing.contains entry.fst)).foldl
      (fun acc entry => acc + entry.snd.length) 0
  if expectOwnLinkRefs && ownLinkCount == 0 then
    fail (label ++ ": expected exported own-code link references")
  -- Deploy values: every substituted immutable name bound; library names
  -- get the address, real immutables keep the base zero.
  let values := substituted.loadImmutableNames.map
    (fun name =>
      (name,
        if missing.contains name then libraryAddress
        else EvmYul.UInt256.ofNat 0))
  let some withValues :=
      Frontend.Object.compileVerifiedStackCodeArtifactWithImmutableValues?
        substituted artifact.computed.context values
    | fail (label ++ ": value compile returned none")
  -- The endpoint equation of
  -- Object.patchImmutablesAndLibraries_image_ofCompileUnlinked, executed.
  let patched := Frontend.Bytecode.patchImmutablesAndLibraries
    artifact.image.bytes ownRefs missing values
  if patched != withValues.bytes ++ artifact.computed.payload then
    fail (label ++ ": patched image differs from the value compile")
  -- The exported 20-byte view patches to the same bytes when every own
  -- group is a library group (this fixture has no immutables).
  if expectOwnLinkRefs then
    let viewPatched := Frontend.Bytecode.patchLibraries
      artifact.image.bytes linkRefs values
    if viewPatched != patched then
      fail (label ++ ": link-reference view patch differs")
  IO.println
    ("unlinked_library_smoke\t" ++ label ++
      "\timage_bytes=" ++ toString artifact.image.bytes.length ++
      "\tlink_windows=" ++
        toString (linkRefs.foldl (fun acc e => acc + e.snd.length) 0) ++
      "\town_link_windows=" ++ toString ownLinkCount)

def checkLinked : IO Unit := do
  let input <- IO.FS.readFile linkedPath
  for (label, selector) in
      [("linked-runtime", RawAst.ObjectSelector.runtime),
        ("linked-creation", RawAst.ObjectSelector.creation)] do
    let some artifact :=
        RawAst.compileArtifactFromRawSolcIr? input (selectionFor selector)
      | fail (label ++ ": linked compile returned none")
    let some program :=
        RawAst.decodeAndElaborateSolcIr? input (selectionFor selector)
      | fail (label ++ ": linked decode failed")
    let some linkerSymbols :=
        RawAst.decodeLinkerSymbols? input (selectionFor selector)
      | fail (label ++ ": linked linker metadata decode failed")
    if program.object.missingLinkerSymbolNames linkerSymbols != [] then
      fail (label ++ ": linked input still has missing names")
    IO.println
      ("unlinked_library_smoke\t" ++ label ++
        "\timage_bytes=" ++ toString artifact.image.bytes.length)

def main : IO Unit := do
  checkSelector "unlinked-runtime" RawAst.ObjectSelector.runtime true
  checkSelector "unlinked-creation" RawAst.ObjectSelector.creation false
  checkLinked
  IO.println "unlinked_library_smoke=pass"
EOF

cd "$ROOT"
"$LAKE_BIN" env lean --run "$RUNNER"
