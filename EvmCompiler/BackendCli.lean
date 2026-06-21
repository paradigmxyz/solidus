import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Functions.StackDiagnostics
import EvmCompiler.Objects.Compiler

namespace EvmCompiler.BackendCli

open EvmCompiler

inductive Mode where
  | image
  | summary
  | check
  | stackDiagnostics
  deriving BEq

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
  | "stack-diagnostics" => some .stackDiagnostics
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
  | .summary | .check | .stackDiagnostics => pure ()
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

def functionsForStackDiagnostics?
    (object : Solidity.Frontend.Object)
    (linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)) :
    Option Functions.Program := do
  let layout : Solidity.Frontend.ObjectLayout := { entries := [] }
  let context :=
    object.builtinContextWithLocalDataBaseAndLinkerSymbols
      layout 0 linkerSymbols
  let context :=
    { context with
      immutableValues :=
        Solidity.Frontend.ImmutableReference.zeroEntries
          object.loadImmutableNames }
  let resolved ← object.resolveObjectBuiltinsIn? context
  resolved.lowerCodeUnchecked?

def boolString (value : Bool) : String :=
  if value then "true" else "false"

def printStackDiagnostics
    (source : String) (contract objectName : String)
    (functions : Functions.Program) : IO Unit := do
  let reports := Functions.StackDiagnostics.programReports functions
  let summary := Functions.StackDiagnostics.summarize reports
  IO.println "stack_diagnostics=complete"
  IO.println ("source=" ++ source)
  IO.println ("contract=" ++ contract)
  IO.println ("object=" ++ objectName)
  IO.println ("units=" ++ toString summary.units)
  IO.println ("liveness_ok=" ++ toString summary.livenessOk)
  IO.println ("schedule_ok=" ++ toString summary.scheduleOk)
  IO.println ("lowering_ok=" ++ toString summary.loweringOk)
  IO.println ("next_use_ok=" ++ toString summary.nextUseOk)
  IO.println ("points=" ++ toString summary.metrics.points)
  IO.println ("peak_live=" ++ toString summary.metrics.peakLive)
  IO.println
    ("live_points_over_16=" ++ toString summary.metrics.livePointsOver16)
  IO.println ("joins=" ++ toString summary.metrics.joins)
  IO.println
    ("dormant_call_sites=" ++ toString summary.metrics.dormantCallSites)
  IO.println ("peak_dormant=" ++ toString summary.metrics.peakDormant)
  IO.println
    ("inaccessible_depth_failures=" ++ toString summary.accessFailures)
  match Functions.StackDiagnostics.firstFailure? reports with
  | none => IO.println "first_failure=none"
  | some (unitName, failure) =>
      IO.println ("first_failure_unit=" ++ unitName)
      IO.println ("first_failure_path=" ++ failure.path)
      IO.println ("first_failure_phase=" ++ failure.phase)
      IO.println ("first_failure_reason=" ++ failure.reason)
  for report in reports do
    IO.println
      ("unit\t" ++ report.name ++
        "\tpeak_live=" ++ toString report.metrics.peakLive ++
        "\tover16=" ++ toString report.metrics.livePointsOver16 ++
        "\tjoins=" ++ toString report.metrics.joins ++
        "\tdormant_calls=" ++ toString report.metrics.dormantCallSites ++
        "\tpeak_dormant=" ++ toString report.metrics.peakDormant ++
        "\tliveness=" ++ boolString report.livenessOk ++
        "\tschedule=" ++ boolString report.scheduleOk ++
        "\taccess_failures=" ++ toString report.accessFailures ++
        "\tlowering=" ++ boolString report.loweringOk ++
        "\tnext_use=" ++ boolString report.nextUseOk)
    match report.firstFailure? with
    | none => pure ()
    | some failure =>
        IO.println
          ("failure\t" ++ report.name ++
            "\tpath=" ++ failure.path ++
            "\tphase=" ++ failure.phase ++
            "\treason=" ++ failure.reason)
    match report.nextUseFailure? with
    | none => pure ()
    | some failure =>
        IO.println
          ("next-use-failure\t" ++ report.name ++
            "\tpath=" ++ failure.path ++
            "\tphase=" ++ failure.phase ++
            "\treason=" ++ failure.reason)

def runStackDiagnostics (config : Config)
    (program : Solidity.Frontend.Program) : IO Unit := do
  match functionsForStackDiagnostics? program.object config.linkerSymbols with
  | none =>
      throw
        (IO.userError
          "stack diagnostic Yul-to-Functions normalization returned none")
  | some functions =>
      printStackDiagnostics program.source program.contract
        program.object.name functions

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
  if config.mode == .stackDiagnostics then
    runStackDiagnostics config program
    return
  let compileStart ← IO.monoMsNow
  let compiledObject? :=
    program.object.compileObjectArtifactWithLinkerSymbols?
      config.linkerSymbols
  let byteLength :=
    match compiledObject? with
    | some artifact => artifact.image.bytes.length
    | none => 0
  let compileFinish ← IO.monoMsNow
  IO.println
    ("timing\tobject_image\t" ++ toString (compileFinish - compileStart) ++
      "\tbytes=" ++ toString byteLength)
  match compiledObject? with
  | none =>
      match config.mode with
      | .check => printCheck program none false
      | .image | .summary =>
          throw (IO.userError "unchecked object-image generation returned none")
      | .stackDiagnostics => pure ()
  | some artifact =>
      match config.mode with
      | .image | .summary => printImage config.mode artifact.image
      | .check =>
          let solcOk :=
            match resolveForSolcValidation? program.object artifact.computed with
            | some resolved => resolved.toSolcYulProgram?.isSome
            | none => false
          printCheck program (some artifact.image) solcOk
      | .stackDiagnostics => pure ()

def usage : String :=
  "usage: evm-compiler-backend (image|summary|check|stack-diagnostics) " ++
    "BRIDGE_JSON [NAME=DECIMAL ...]"

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
