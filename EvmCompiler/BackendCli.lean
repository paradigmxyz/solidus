import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Objects.Compiler

namespace EvmCompiler.BackendCli

open EvmCompiler

inductive Mode where
  | image
  | summary
  | check

structure Config where
  mode : Mode
  bridgePath : String
  linkerSymbols :
    List (Solidity.Frontend.Name × Solidity.Frontend.Word)

def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('a'.toNat + (n - 10))

def byteHex (byte : UInt8) : String :=
  String.singleton (hexDigit (byte.toNat / 16)) ++
    String.singleton (hexDigit (byte.toNat % 16))

def bytesHex (bytes : List UInt8) : String :=
  String.join (bytes.map byteHex)

def parseMode? : String → Option Mode
  | "image" => some .image
  | "summary" => some .summary
  | "check" => some .check
  | _ => none

def parseLinkerSymbol? (arg : String) : Option
    (Solidity.Frontend.Name × Solidity.Frontend.Word) :=
  match arg.splitOn "=" with
  | [name, value] => do
      let value ← value.toNat?
      some (name, EvmYul.UInt256.ofNat value)
  | _ => none

def parseLinkerSymbols? : List String → Option
    (List (Solidity.Frontend.Name × Solidity.Frontend.Word))
  | [] => some []
  | arg :: rest => do
      let symbol ← parseLinkerSymbol? arg
      let symbols ← parseLinkerSymbols? rest
      some (symbol :: symbols)

def parseConfig? : List String → Option Config
  | mode :: bridgePath :: linkerArgs => do
      let mode ← parseMode? mode
      let linkerSymbols ← parseLinkerSymbols? linkerArgs
      some { mode, bridgePath, linkerSymbols }
  | _ => none

def printImage (mode : Mode)
    (image : Solidity.Frontend.ObjectImage) : IO Unit := do
  match mode with
  | .image => IO.println ("bytecode=0x" ++ bytesHex image.bytes)
  | .summary | .check => pure ()
  for entry in image.immutableReferences do
    for reference in entry.snd do
      IO.println
        ("immutable\t" ++ entry.fst ++ "\t" ++
          toString reference.start ++ "\t" ++
          toString reference.length)
  IO.println ("bytecode_bytes=" ++ toString image.bytes.length)

def resolveForSolcValidation?
    (object : Solidity.Frontend.Object)
    (computed : Solidity.Frontend.Object.ObjectComputedObjectData) :
    Option Solidity.Frontend.Object := do
  let memoryContract ←
    Solidity.Frontend.MemoryGuard.Object.inferredContract? object
  let context := { computed.context with memoryContract := memoryContract }
  let dispatcher ←
    Solidity.Frontend.Stmt.List.resolveObjectBuiltinsIn?
      object.dispatcher context
  let functions ←
    Solidity.Frontend.FunctionDef.List.resolveObjectBuiltinsIn?
      object.functions context
  some { object with dispatcher, functions, memoryContract }

def printCheck
    (program : Solidity.Frontend.Program)
    (image? : Option Solidity.Frontend.ObjectImage)
    (solcOk : Bool) : IO Unit := do
  let imageOk := image?.isSome
  let ok := imageOk && solcOk
  IO.println ("lean_backend_check=" ++ if ok then "pass" else "fail")
  IO.println ("source=" ++ program.source)
  IO.println ("contract=" ++ program.contract)
  IO.println ("object=" ++ program.object.name)
  IO.println
    ("stage\tsolc_validation\t" ++ if solcOk then "some" else "none")
  IO.println
    ("stage\tobject_image\t" ++ if imageOk then "some" else "none")
  IO.println
    ("first_none=" ++
      if !imageOk then "object_image"
      else if !solcOk then "solc_validation"
      else "none")
  match image? with
  | some image => IO.println ("bytecode_bytes=" ++ toString image.bytes.length)
  | none => pure ()

def run (config : Config) : IO Unit := do
  let decodeStart ← IO.monoMsNow
  let input ← IO.FS.readFile config.bridgePath
  let program ←
    match Solidity.Frontend.BridgeJson.parseProgram? input with
    | .ok program => pure program
    | .error err => throw (IO.userError ("bridge JSON decode failed: " ++ err))
  let decodeFinish ← IO.monoMsNow
  IO.println ("timing\tdecode\t" ++ toString (decodeFinish - decodeStart))
  let compileStart ← IO.monoMsNow
  let computedAndImage? :=
    program.object.computedImageUncheckedWithLinkerSymbols?
      config.linkerSymbols
  let byteLength :=
    match computedAndImage? with
    | some pair => pair.snd.bytes.length
    | none => 0
  let compileFinish ← IO.monoMsNow
  IO.println
    ("timing\tobject_image\t" ++ toString (compileFinish - compileStart) ++
      "\tbytes=" ++ toString byteLength)
  match computedAndImage? with
  | none =>
      match config.mode with
      | .check => printCheck program none false
      | .image | .summary =>
          throw (IO.userError "unchecked object-image generation returned none")
  | some (computed, image) =>
      match config.mode with
      | .image | .summary => printImage config.mode image
      | .check =>
          let solcOk :=
            match resolveForSolcValidation? program.object computed with
            | some resolved => resolved.toSolcYulProgram?.isSome
            | none => false
          printCheck program (some image) solcOk

def usage : String :=
  "usage: evm-compiler-backend (image|summary|check) BRIDGE_JSON [NAME=DECIMAL ...]"

def cliMain (args : List String) : IO UInt32 := do
  match parseConfig? args with
  | none =>
      IO.eprintln usage
      pure 2
  | some config =>
      try
        run config
        pure 0
      catch err =>
        IO.eprintln err.toString
        pure 1

end EvmCompiler.BackendCli

def main (args : List String) : IO UInt32 :=
  EvmCompiler.BackendCli.cliMain args
