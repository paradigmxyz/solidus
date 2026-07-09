import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.Compact
import EvmCompiler.Functions.StackDiagnostics
import EvmCompiler.Compiler.StackArtifact
import EvmCompiler.Solidity.VerifiedStackObjectArtifact
import EvmCompiler.Solidity.StackHeadroomEndToEnd
import EvmCompiler.Solidus.Defs

namespace EvmCompiler.BackendCli

open EvmCompiler

inductive Mode where
  | image
  | summary
  | check
  | stackAnalysis
  | stackDiagnostics
  | rawImage
  | rawSummary
  | rawCheck
  deriving BEq

structure Config where
  mode : Mode
  bridgePath : String
  linkerSymbols :
    List (Solidity.Frontend.Name × Solidity.Frontend.Word)

structure RawConfig where
  mode : Mode
  rawPath : String
  selection : Solidity.RawAst.Selection

inductive Command where
  | bridge (config : Config)
  | raw (config : RawConfig)

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
  | "stack-analysis" => some .stackAnalysis
  | "stack-diagnostics" => some .stackDiagnostics
  | "raw-image" => some .rawImage
  | "raw-summary" => some .rawSummary
  | "raw-check" => some .rawCheck
  | _ => none

def Mode.raw? : Mode → Bool
  | .rawImage | .rawSummary | .rawCheck => true
  | _ => false

def Mode.bridge? (mode : Mode) : Bool :=
  !mode.raw?

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

def parseRawObjectSelector (value : String) : Solidity.RawAst.ObjectSelector :=
  match value with
  | "creation" => .creation
  | "runtime" => .runtime
  | name => .named name

def parseBridgeConfig? : List String → Option Config
  | mode :: bridgePath :: linkerArgs => do
      let mode ← parseMode? mode
      if !mode.bridge? then
        none
      else
      let linkerSymbols ← parseLinkerSymbols? linkerArgs
      some { mode, bridgePath, linkerSymbols }
  | _ => none

def parseRawConfig? : List String → Option RawConfig
  | mode :: rawPath :: source :: contract :: objectSelector :: [] => do
      let mode ← parseMode? mode
      if !mode.raw? then
        none
      else
      let selection : Solidity.RawAst.Selection :=
        { source? := some source
          contract? := some contract
          objectSelector := parseRawObjectSelector objectSelector
          astOutput := "irOptimizedAst" }
      some { mode, rawPath, selection }
  | _ => none

def parseCommand? (args : List String) : Option Command :=
  match parseRawConfig? args with
  | some config => some (.raw config)
  | none =>
      match parseBridgeConfig? args with
      | some config => some (.bridge config)
      | none => none

/-- Emit an object image, but take the emitted `bytecode` bytes from an
explicit `bytes` argument (the reference/immutable metadata still comes from
`image`). This lets the raw path ship exactly the byte list returned by the
frozen public entry `Solidus.compile?` while reusing the image's link and
immutable reference tables (which are definitionally the same bytes on the
certified linked path). -/
def printImageBytes (mode : Mode)
    (bytes : List UInt8)
    (image : Solidity.Frontend.ObjectImage)
    (unlinkedLibraryNames : List Solidity.Frontend.Name := []) : IO Unit := do
  match mode with
  | .image | .rawImage => IO.println ("bytecode=0x" ++ bytesHex bytes)
  | .summary | .rawSummary | .check | .rawCheck | .stackAnalysis
  | .stackDiagnostics => pure ()
  for entry in image.immutableReferences do
    for reference in entry.snd do
      IO.println
        ("immutable\t" ++ entry.fst ++ "\t" ++
          toString reference.start ++ "\t" ++
          toString reference.length)
  for entry in image.linkReferences unlinkedLibraryNames do
    for reference in entry.snd do
      IO.println
        ("linkref\t" ++ entry.fst ++ "\t" ++
          toString reference.start ++ "\t" ++
          toString reference.length)
  IO.println ("bytecode_bytes=" ++ toString bytes.length)

def printImage (mode : Mode)
    (image : Solidity.Frontend.ObjectImage)
    (unlinkedLibraryNames : List Solidity.Frontend.Name := []) : IO Unit :=
  printImageBytes mode image.bytes image unlinkedLibraryNames

/-- EIP-170 runtime code size cap (bytes). -/
def eip170RuntimeCap : Nat := 24576

/-- EIP-3860 initcode size cap (bytes). -/
def eip3860InitcodeCap : Nat := 49152

/-- Whether the environment requests the oversize opt-out. Mirrors the
`env_flag_default` truthiness used by the Python harness glue. -/
def allowOversizeFromEnv : IO Bool := do
  match ← IO.getEnv "EVM_COMPILER_ALLOW_OVERSIZE" with
  | none => pure false
  | some raw =>
      let v := raw.trim
      pure !(v == "" || v == "0" || v == "false" || v == "False"
        || v == "FALSE" || v == "no" || v == "off" || v == "OFF")

/-- Fail-closed deployability guard on the emitted image. This is a
product-level check, NOT a theorem-covered property: the public correctness
theorem (`Solidus.compile_correct`) says nothing about EIP-170/EIP-3860
admission. Runtime images larger than the EIP-170 cap and creation initcode
larger than the EIP-3860 cap cannot be deployed on mainnet, so the CLI refuses
to emit them unless the caller opts out (`EVM_COMPILER_ALLOW_OVERSIZE`). Named
objects carry no creation/runtime classification, so no cap is applied to
them. -/
def checkImageSizeCap (selector : Solidity.RawAst.ObjectSelector)
    (byteLen : Nat) (allowOversize : Bool) : IO Unit := do
  let spec? : Option (Nat × String × String × Bool) :=
    match selector with
    | .runtime => some (eip170RuntimeCap, "runtime code", "EIP-170", false)
    | .creation => some (eip3860InitcodeCap, "creation initcode", "EIP-3860", true)
    | .named _ => none
  match spec? with
  | none => pure ()
  | some (cap, what, eip, isCreation) =>
      if byteLen > cap then
        let over := byteLen - cap
        let core :=
          "compiled " ++ what ++ " is " ++ toString byteLen ++
            " bytes, exceeding the " ++ eip ++ " cap of " ++ toString cap ++
            " bytes by " ++ toString over ++ " bytes"
        let detail :=
          if isCreation then
            core ++ " (the " ++ eip ++ " cap applies to the full initcode " ++
              "INCLUDING the constructor arguments appended by the deployer at " ++
              "deploy time, so there are 0 bytes of headroom remaining)"
          else core
        if allowOversize then
          IO.eprintln ("warning: " ++ detail ++
            "; emitting anyway because EVM_COMPILER_ALLOW_OVERSIZE is set")
        else
          throw (IO.userError ("error: " ++ detail ++
            "; the image is not deployable — set EVM_COMPILER_ALLOW_OVERSIZE=1 " ++
            "to emit it anyway"))

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

def verifiedStackCodeArtifact?
    (object : Solidity.Frontend.Object)
    (linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)) :
    Option Solidity.Frontend.Object.VerifiedStackCodeArtifact := do
  let layout : Solidity.Frontend.ObjectLayout := { entries := [] }
  let context :=
    object.builtinContextWithLocalDataBaseAndLinkerSymbols
      layout 0 linkerSymbols
  let context :=
    { context with
      immutableValues :=
        Solidity.Frontend.ImmutableReference.zeroEntries
          object.loadImmutableNames }
  object.compileVerifiedStackCodeArtifactIn? context

def boolString (value : Bool) : String :=
  if value then "true" else "false"

def structuredStmtKind : Structured.Stmt → String
  | .code _ => "code"
  | .if_ _ _ => "if"
  | .switch _ _ _ => "switch"
  | .for_ _ _ _ _ => "for"
  | .brk => "break"
  | .cont => "continue"
  | .leave => "leave"
  | .call name => "call:" ++ name
  | .terminal _ => "terminal"

def firstCfgPrefixFailureFrom?
    (proc : Structured.Proc) (ctx : Structured.TypedCfgCompiler.Context)
    (count : Nat) : Option Nat :=
  if count > proc.body.stmts.length then
    none
  else
    let prefixBlock : Structured.Block :=
      { stmts := proc.body.stmts.take count }
    if (Structured.TypedCfgCompiler.compileBlock? prefixBlock ctx 0
        (Structured.ProcLabel.entry proc.name)
        (Structured.TypedCfgCompiler.Shape.procEntry proc)
        (Structured.ProcLabel.exit proc.name)).isNone then
      some count
    else
      firstCfgPrefixFailureFrom? proc ctx (count + 1)
termination_by proc.body.stmts.length + 1 - count

def firstCfgPrefixFailure?
    (allProcs : List Structured.Proc) (proc : Structured.Proc) : Option Nat :=
  let ctx : Structured.TypedCfgCompiler.Context :=
    { procs := allProcs
      leaveLabel? := some (Structured.ProcLabel.exit proc.name)
      leaveShape? := some (Structured.TypedCfgCompiler.Shape.procExit proc) }
  firstCfgPrefixFailureFrom? proc ctx 0

def firstBlockPrefixFailureFrom?
    (block : Structured.Block) (ctx : Structured.TypedCfgCompiler.Context)
    (supply : Nat) (entry : Assembly.Label) (input : TypedCfg.Shape)
    (regular : Assembly.Label) (count : Nat) : Option (Nat × String) :=
  if count > block.stmts.length then
    none
  else
    let prefixBlock : Structured.Block :=
      { stmts := block.stmts.take count }
    if (Structured.TypedCfgCompiler.compileBlock? prefixBlock ctx supply entry
        input regular).isNone then
      let kind :=
        block.stmts[count - 1]?.map structuredStmtKind |>.getD "unknown"
      some (count, kind)
    else
      firstBlockPrefixFailureFrom? block ctx supply entry input regular
        (count + 1)
termination_by block.stmts.length + 1 - count

def firstBlockPrefixFailure?
    (block : Structured.Block) (ctx : Structured.TypedCfgCompiler.Context)
    (supply : Nat) (entry : Assembly.Label) (input : TypedCfg.Shape)
    (regular : Assembly.Label) : Option (Nat × String) :=
  firstBlockPrefixFailureFrom? block ctx supply entry input regular 0

def firstBlockFailureContext?
    (block : Structured.Block) (ctx : Structured.TypedCfgCompiler.Context)
    (supply : Nat) (entry : Assembly.Label) (input : TypedCfg.Shape)
    (regular : Assembly.Label) :
    Option (Nat × Structured.Stmt × Nat × TypedCfg.Shape) := do
  let (count, _) ←
    firstBlockPrefixFailure? block ctx supply entry input regular
  let stmt ← block.stmts[count - 1]?
  let prefixBlock : Structured.Block :=
    { stmts := block.stmts.take (count - 1) }
  let before ←
    Structured.TypedCfgCompiler.compileBlock? prefixBlock ctx supply entry
      input regular
  let stmtInput ← before.fallthrough?
  some (count, stmt, before.next, stmtInput)

def blockFailureLabel
    (block : Structured.Block) (ctx : Structured.TypedCfgCompiler.Context)
    (supply : Nat) (entry : Assembly.Label) (input : TypedCfg.Shape)
    (regular : Assembly.Label) (fallback : String) : String :=
  match firstBlockPrefixFailure? block ctx supply entry input regular with
  | none => fallback
  | some (count, kind) => fallback ++ "[" ++ toString count ++ "]:" ++ kind

def firstSwitchCaseFailure?
    (cases : List (Structured.Word × Structured.Block))
    (ctx : Structured.TypedCfgCompiler.Context) (bodyShape : TypedCfg.Shape)
    (regular : Assembly.Label) (index : Nat := 0) : Option String :=
  match cases with
  | [] => none
  | (_, body) :: rest =>
      let supply := 100000 + index * 1000
      let entry := Assembly.Label.generated supply 1
      match Structured.TypedCfgCompiler.compileBlock? body ctx supply entry
          bodyShape regular with
      | none =>
          some
            (blockFailureLabel body ctx supply entry bodyShape regular
              ("switch-case[" ++ toString index ++ "]"))
      | some result =>
          if result.requireFallthrough? bodyShape |>.isNone then
            some ("switch-case[" ++ toString index ++ "]-fallthrough")
          else
            firstSwitchCaseFailure? rest ctx bodyShape regular (index + 1)

def cfgStmtFailurePhaseFuel
    (depth : Nat) (stmt : Structured.Stmt)
    (ctx : Structured.TypedCfgCompiler.Context)
    (supply : Nat) (input : TypedCfg.Shape) : String :=
  if hDepth : depth = 0 then
    "diagnostic-fuel"
  else (
  let fuel := Structured.TypedCfgCompiler.stmtFuel stmt + 1
  let entry := Assembly.Label.generated supply 90000
  let regular := Assembly.Label.generated supply 90001
  match stmt with
  | .if_ cond body =>
      let bodyLabel := Structured.LabelSupply.label supply 0
      match Structured.TypedCfgCompiler.mkCodeBlock? entry input cond
          (.jumpi bodyLabel regular) with
      | none => "if-condition-code"
      | some head =>
          let condOutput := head.output
          match Structured.TypedCfgCompiler.Shape.requireSourceWords?
              1 condOutput with
          | none => "if-condition-result"
          | some _ =>
              let branchInput :=
                { condOutput with slots := condOutput.slots.tail }
              match Structured.TypedCfgCompiler.compileBlockFuel? fuel body ctx
                  (supply + 1) bodyLabel branchInput regular with
              | none =>
                  match firstBlockFailureContext? body ctx (supply + 1)
                      bodyLabel branchInput regular with
                  | none => "if-body"
                  | some (count, nested, nestedSupply, nestedInput) =>
                      "if-body[" ++ toString count ++ "]/" ++
                        cfgStmtFailurePhaseFuel (depth - 1) nested ctx
                          nestedSupply nestedInput
              | some bodyResult =>
                  if bodyResult.requireFallthrough? branchInput |>.isNone then
                    "if-body-fallthrough"
                  else
                    "if-unknown"
  | .switch scrutinee cases defaultBody =>
      let defaultLabel := Structured.LabelSupply.label supply 1
      let firstTest :=
        match cases with
        | [] => defaultLabel
        | _ => Structured.TypedCfgCompiler.switchTestLabel supply 0
      match Structured.TypedCfgCompiler.mkCodeBlock? entry input scrutinee
          (.jump firstTest) with
      | none => "switch-scrutinee-code"
      | some head =>
          let valueShape := head.output
          match Structured.TypedCfgCompiler.Shape.requireSourceWords?
              1 valueShape with
          | none => "switch-scrutinee-result"
          | some _ =>
              let bodyShape :=
                { valueShape with slots := valueShape.slots.tail }
              match Structured.TypedCfgCompiler.compileCasesFuel? fuel cases
                  ctx supply (supply + 1) 0 valueShape bodyShape regular with
              | none =>
                  (firstSwitchCaseFailure? cases ctx bodyShape regular).getD
                    "switch-cases"
              | some caseResult =>
                  match Structured.TypedCfgCompiler.compileDefaultFuel? fuel
                      defaultBody ctx caseResult.next defaultLabel valueShape
                      bodyShape regular with
                  | none => "switch-default"
                  | some _ => "switch-unknown"
  | .for_ init cond post body =>
      let loopLabel := Structured.LabelSupply.label supply 0
      let bodyLabel := Structured.LabelSupply.label supply 1
      let postLabel := Structured.LabelSupply.label supply 2
      let outerCtx :=
        { ctx with
          breakLabel? := none
          breakShape? := none
          continueLabel? := none
          continueShape? := none }
      match Structured.TypedCfgCompiler.compileBlockFuel? fuel init outerCtx
          (supply + 1) entry input loopLabel with
      | none => "for-init"
      | some initResult =>
          match initResult.fallthrough? with
          | none => "for-init-fallthrough"
          | some loopInput =>
              match Structured.TypedCfgCompiler.mkCodeBlock? loopLabel
                  loopInput cond (.jumpi bodyLabel regular) with
              | none => "for-condition-code"
              | some loopBlock =>
                  let condOutput := loopBlock.output
                  match Structured.TypedCfgCompiler.Shape.requireSourceWords?
                      1 condOutput with
                  | none => "for-condition-result"
                  | some _ =>
                      let branchInput :=
                        { condOutput with slots := condOutput.slots.tail }
                      let bodyCtx :=
                        { ctx with
                          breakLabel? := some regular
                          breakShape? := some branchInput
                          continueLabel? := some postLabel
                          continueShape? := some branchInput }
                      match Structured.TypedCfgCompiler.compileBlockFuel? fuel
                          body bodyCtx initResult.next bodyLabel branchInput
                          postLabel with
                      | none =>
                          match firstBlockFailureContext? body bodyCtx
                              initResult.next bodyLabel branchInput postLabel with
                          | none => "for-body"
                          | some (count, nested, nestedSupply, nestedInput) =>
                              "for-body[" ++ toString count ++ "]/" ++
                                cfgStmtFailurePhaseFuel (depth - 1) nested
                                  bodyCtx nestedSupply nestedInput
                      | some bodyResult =>
                          match bodyResult.requireFallthrough? branchInput with
                          | none => "for-body-fallthrough"
                          | some _ =>
                              match
                                  Structured.TypedCfgCompiler.compileBlockFuel?
                                    fuel post outerCtx bodyResult.next postLabel
                                    branchInput loopLabel with
                              | none => "for-post"
                              | some postResult =>
                                  match postResult.requireFallthrough? loopInput with
                                  | none => "for-post-fallthrough"
                                  | some _ => "for-unknown"
  | _ => structuredStmtKind stmt)
termination_by depth
decreasing_by
  all_goals
    exact Nat.sub_lt (Nat.zero_lt_of_ne_zero hDepth) (by omega)

def cfgStmtFailurePhase
    (stmt : Structured.Stmt) (ctx : Structured.TypedCfgCompiler.Context)
    (supply : Nat) (input : TypedCfg.Shape) : String :=
  cfgStmtFailurePhaseFuel
    (Structured.TypedCfgCompiler.stmtFuel stmt + 1) stmt ctx supply input

def firstCfgFailurePhase?
    (allProcs : List Structured.Proc) (proc : Structured.Proc)
    (count : Nat) : Option String := do
  let stmt ← proc.body.stmts[count - 1]?
  let ctx : Structured.TypedCfgCompiler.Context :=
    { procs := allProcs
      leaveLabel? := some (Structured.ProcLabel.exit proc.name)
      leaveShape? := some (Structured.TypedCfgCompiler.Shape.procExit proc) }
  let prefixBlock : Structured.Block :=
    { stmts := proc.body.stmts.take (count - 1) }
  let prefixResult ←
    Structured.TypedCfgCompiler.compileBlock? prefixBlock ctx 0
      (Structured.ProcLabel.entry proc.name)
      (Structured.TypedCfgCompiler.Shape.procEntry proc)
      (Structured.ProcLabel.exit proc.name)
  let input ← prefixResult.fallthrough?
  some (cfgStmtFailurePhase stmt ctx prefixResult.next input)

structure CompactFamilyStats where
  labels : Nat := 0
  labelBytes : Nat := 0
  constants : Nat := 0
  constantBytes : Nat := 0
  jumps : Nat := 0
  jumpBytes : Nat := 0
  jumpis : Nat := 0
  jumpiBytes : Nat := 0
  prims : Nat := 0
  primBytes : Nat := 0
  adds : Nat := 0
  pops : Nat := 0
  dups : Nat := 0
  swaps : Nat := 0
  otherPrims : Nat := 0

def CompactFamilyStats.addBlock (stats : CompactFamilyStats)
    (block : Assembly.Compact.SourceBlock) : CompactFamilyStats :=
  let bytes := Assembly.Compact.Program.codeByteLength block.code
  match block.sourceInstr with
  | .label _ =>
      { stats with
        labels := stats.labels + 1
        labelBytes := stats.labelBytes + bytes }
  | .push _ | .pushLabel _ =>
      { stats with
        constants := stats.constants + 1
        constantBytes := stats.constantBytes + bytes }
  | .jump _ | .jumpDynamic =>
      { stats with
        jumps := stats.jumps + 1
        jumpBytes := stats.jumpBytes + bytes }
  | .jumpi _ =>
      { stats with
        jumpis := stats.jumpis + 1
        jumpiBytes := stats.jumpiBytes + bytes }
  | .prim op =>
      let opcode := (EvmYul.EVM.serializeInstr op.toEVM).toNat
      let isDup := decide (0x80 <= opcode ∧ opcode <= 0x8f)
      let isSwap := decide (0x90 <= opcode ∧ opcode <= 0x9f)
      { stats with
        prims := stats.prims + 1
        primBytes := stats.primBytes + bytes
        adds := stats.adds + if op = .add then 1 else 0
        pops := stats.pops + if op = .pop then 1 else 0
        dups := stats.dups + if isDup then 1 else 0
        swaps := stats.swaps + if isSwap then 1 else 0
        otherPrims := stats.otherPrims +
          if op != .add && op != .pop && !isDup && !isSwap then 1 else 0 }

def compactFamilyStats (artifact : Assembly.Compact.Artifact) :
    CompactFamilyStats :=
  artifact.blocks.foldl CompactFamilyStats.addBlock {}

structure ControlPatternStats where
  adjacentJump : Nat := 0
  adjacentJumpi : Nat := 0
  conditionalDiamond : Nat := 0
  labelJump : Nat := 0
  consecutiveLabels : Nat := 0
  pushPop : Nat := 0
  swapPair : Nat := 0

def ControlPatternStats.addPair (stats : ControlPatternStats)
    (first second : Assembly.Instr) : ControlPatternStats :=
  match first, second with
  | .jump target, .label next =>
      { stats with adjacentJump := stats.adjacentJump +
          if target = next then 1 else 0 }
  | .jumpi target, .label next =>
      { stats with adjacentJumpi := stats.adjacentJumpi +
          if target = next then 1 else 0 }
  | .label _, .jump _ =>
      { stats with labelJump := stats.labelJump + 1 }
  | .label _, .label _ =>
      { stats with consecutiveLabels := stats.consecutiveLabels + 1 }
  | .push _, .prim .pop =>
      { stats with pushPop := stats.pushPop + 1 }
  | .prim left, .prim right =>
      let leftOp := (EvmYul.EVM.serializeInstr left.toEVM).toNat
      let rightOp := (EvmYul.EVM.serializeInstr right.toEVM).toNat
      { stats with swapPair := stats.swapPair +
          if 0x90 <= leftOp && leftOp <= 0x9f && leftOp = rightOp then
            1
          else
            0 }
  | _, _ => stats

def ControlPatternStats.addTriple (stats : ControlPatternStats)
    (first second third : Assembly.Instr) : ControlPatternStats :=
  match first, second, third with
  | .jumpi target, .jump _, .label next =>
      { stats with conditionalDiamond := stats.conditionalDiamond +
          if target = next then 1 else 0 }
  | _, _, _ => stats

structure ControlPatternFold where
  stats : ControlPatternStats := {}
  previous2? : Option Assembly.Instr := none
  previous? : Option Assembly.Instr := none

def ControlPatternFold.addInstr (state : ControlPatternFold)
    (current : Assembly.Instr) : ControlPatternFold :=
  let stats :=
    match state.previous? with
    | none => state.stats
    | some previous => state.stats.addPair previous current
  let stats :=
    match state.previous2?, state.previous? with
    | some previous2, some previous =>
        stats.addTriple previous2 previous current
    | _, _ => stats
  { stats, previous2? := state.previous?, previous? := some current }

def controlPatternStats (source : Assembly.Program) : ControlPatternStats :=
  (source.foldl ControlPatternFold.addInstr {}).stats

structure ReturnDispatchStats where
  dispatches : Nat := 0
  sites : Nat := 0
  repeatedCleanupSwaps : Nat := 0
  sharedCleanupSwaps : Nat := 0

def returnDispatchStats (program : TypedCfg.Program) : ReturnDispatchStats :=
  program.blocks.foldl
    (fun stats block =>
      match block.term with
      | .returnDispatch returnCount sites =>
          { dispatches := stats.dispatches + 1
            sites := stats.sites + sites.length
            repeatedCleanupSwaps :=
              stats.repeatedCleanupSwaps + returnCount * sites.length
            sharedCleanupSwaps := stats.sharedCleanupSwaps + returnCount }
      | _ => stats)
    {}

def printStackDiagnostics
    (source : String) (contract objectName : String)
    (functions : Functions.Program) : IO Unit := do
  let compileStart ← IO.monoMsNow
  let stackArtifact? := Compiler.StackArtifact.compile? functions
  let sourceAccepted :=
    Functions.SourceAcceptedCheck.Program.sourceAccepted? functions
  let normalized := Functions.StackPressureNormalization.Program.normalize functions
  let normalizedAccepted :=
    Functions.SourceAcceptedCheck.Program.sourceAccepted? normalized
  let normalizedLowered? := Functions.StackLowering.lowerProgram? normalized
  let normalizedExpressions? := normalizedLowered?.bind Locals.Program.toExpressions?
  let normalizedStructured? := normalizedExpressions?.map Expressions.Program.toStructured
  let normalizedStructuredWf := normalizedStructured?.any
    Structured.SourceAcceptedCheck.Program.wf?
  let normalizedGenerated? := normalizedStructured?.bind fun structured =>
    Structured.TypedCfgCompiler.artifactWithProcEntryShapes? structured []
  let normalizedIndependent := normalizedGenerated?.any fun generated =>
    generated.cfg.programCounterIndependent?
  let normalizedCertified? := normalizedGenerated?.bind fun generated =>
    generated.cfg.compileCertified?
  let normalizedExecutable? := normalizedCertified?.bind fun certified =>
    Assembly.compileExecutable? certified.target
  let normalizedDecodeWindow := normalizedExecutable?.any
    Assembly.Bytecode.targetFitsDecodeWindow?
  let sourceOpenSupported :=
    Functions.OpenSupportCheck.Program.openSupported? functions
  let normalizedOpenSupported :=
    Functions.OpenSupportCheck.Program.openSupported? normalized
  let lowered? := Functions.StackLowering.lowerProgram? functions
  let expressions? := lowered?.bind Locals.Program.toExpressions?
  let structured? := expressions?.map Expressions.Program.toStructured
  let cfgGenerated? :=
    structured?.bind Structured.TypedCfgCompiler.generate?
  let cfg? := structured?.bind Structured.TypedCfgCompiler.compile?
  let certified? := cfg?.bind TypedCfg.Program.compileCertified?
  let compiled? := certified?.bind fun artifact =>
    Assembly.compileExecutable? artifact.target
  let assemblyInstrs := compiled?.map (·.code.length) |>.getD 0
  let stackBytes :=
    stackArtifact?.map
      (fun artifact =>
        (Assembly.Bytecode.encodeTargetFast artifact.target).size)
      |>.getD 0
  let compactArtifact? := stackArtifact?.bind fun artifact =>
    Assembly.Compact.compile? artifact.certified.target
  let compactBytes := compactArtifact?.map (·.bytes.size) |>.getD 0
  let compactBranchWidth :=
    compactArtifact?.map (·.branchWidth) |>.getD 0
  let assemblyStats :=
    stackArtifact?.map
      (fun artifact =>
        Assembly.Compact.sourceStats artifact.certified.target)
      |>.getD {}
  let physicalStats :=
    compactArtifact?.map
      (fun artifact => Assembly.Compact.sourceStats artifact.physicalSource)
      |>.getD {}
  let compactStats := compactArtifact?.map compactFamilyStats |>.getD {}
  let controlStats :=
    compactArtifact?.map
      (fun artifact => controlPatternStats artifact.physicalSource)
      |>.getD {}
  let dispatchStats :=
    stackArtifact?.map (fun artifact => returnDispatchStats artifact.cfg)
      |>.getD {}
  let compileFinish ← IO.monoMsNow
  let reports := Functions.StackDiagnostics.programReports functions
  let summary := Functions.StackDiagnostics.summarize reports
  IO.println "stack_diagnostics=complete"
  IO.println ("source=" ++ source)
  IO.println ("contract=" ++ contract)
  IO.println ("object=" ++ objectName)
  IO.println
    ("stack_program_artifact=" ++ boolString stackArtifact?.isSome)
  IO.println
    ("stack_program_production_stages=" ++
      "source_accepted=" ++ boolString sourceAccepted ++
      "\tnormalized_accepted=" ++ boolString normalizedAccepted ++
      "\tnormalized_lowering=" ++ boolString normalizedLowered?.isSome ++
      "\tnormalized_expressions=" ++ boolString normalizedExpressions?.isSome ++
      "\tnormalized_structured_wf=" ++ boolString normalizedStructuredWf ++
      "\tnormalized_cfg=" ++ boolString normalizedGenerated?.isSome ++
      "\tnormalized_independent=" ++ boolString normalizedIndependent ++
      "\tnormalized_certified=" ++ boolString normalizedCertified?.isSome ++
      "\tnormalized_executable=" ++ boolString normalizedExecutable?.isSome ++
      "\tdecode_window=" ++ boolString normalizedDecodeWindow ++
      "\tsource_open=" ++ boolString sourceOpenSupported ++
      "\tnormalized_open=" ++ boolString normalizedOpenSupported)
  IO.println ("stack_program_lowering=" ++ boolString lowered?.isSome)
  IO.println
    ("stack_program_to_expressions=" ++ boolString expressions?.isSome)
  IO.println
    ("stack_program_cfg_generated=" ++ boolString cfgGenerated?.isSome)
  IO.println ("stack_program_cfg_checked=" ++ boolString cfg?.isSome)
  IO.println
    ("stack_program_assembly_generated=" ++ boolString certified?.isSome)
  IO.println ("stack_program_compilation=" ++ boolString compiled?.isSome)
  IO.println ("stack_program_assembly_instrs=" ++ toString assemblyInstrs)
  IO.println ("stack_program_bytecode_bytes=" ++ toString stackBytes)
  IO.println
    ("stack_program_compact_artifact=" ++
      boolString compactArtifact?.isSome)
  IO.println
    ("stack_program_compact_bytecode_bytes=" ++ toString compactBytes)
  IO.println
    ("stack_program_compact_branch_width=" ++
      toString compactBranchWidth)
  IO.println
    ("stack_program_instruction_mix=" ++
      "source=" ++ toString assemblyStats.instructions ++
      "\tlabels=" ++ toString assemblyStats.labels ++
      "\tpushes=" ++ toString assemblyStats.pushes ++
      "\tzero_pushes=" ++ toString assemblyStats.zeroPushes ++
      "\tjumps=" ++ toString assemblyStats.jumps ++
      "\tjumpis=" ++ toString assemblyStats.jumpis ++
      "\tadds=" ++ toString assemblyStats.adds ++
      "\tpops=" ++ toString assemblyStats.pops ++
      "\tdups=" ++ toString assemblyStats.dups ++
      "\tswaps=" ++ toString assemblyStats.swaps ++
      "\tother_prims=" ++ toString assemblyStats.otherPrims)
  IO.println
    ("stack_program_prepared_mix=" ++
      "source=" ++ toString physicalStats.instructions ++
      "\tlabels=" ++ toString physicalStats.labels ++
      "\tpushes=" ++ toString physicalStats.pushes ++
      "\tjumps=" ++ toString physicalStats.jumps ++
      "\tjumpis=" ++ toString physicalStats.jumpis ++
      "\tadds=" ++ toString physicalStats.adds ++
      "\tpops=" ++ toString physicalStats.pops ++
      "\tdups=" ++ toString physicalStats.dups ++
      "\tswaps=" ++ toString physicalStats.swaps ++
      "\tother_prims=" ++ toString physicalStats.otherPrims)
  IO.println
    ("stack_program_compact_family_bytes=" ++
      "labels=" ++ toString compactStats.labelBytes ++
      "\tconstants=" ++ toString compactStats.constantBytes ++
      "\tjumps=" ++ toString compactStats.jumpBytes ++
      "\tjumpis=" ++ toString compactStats.jumpiBytes ++
      "\tprims=" ++ toString compactStats.primBytes ++
      "\tadds=" ++ toString compactStats.adds ++
      "\tpops=" ++ toString compactStats.pops ++
      "\tdups=" ++ toString compactStats.dups ++
      "\tswaps=" ++ toString compactStats.swaps ++
      "\tother_prims=" ++ toString compactStats.otherPrims)
  IO.println
    ("stack_program_control_patterns=" ++
      "adjacent_jump=" ++ toString controlStats.adjacentJump ++
      "\tadjacent_jumpi=" ++ toString controlStats.adjacentJumpi ++
      "\tconditional_diamond=" ++ toString controlStats.conditionalDiamond ++
      "\tlabel_jump=" ++ toString controlStats.labelJump ++
      "\tconsecutive_labels=" ++ toString controlStats.consecutiveLabels ++
      "\tpush_pop=" ++ toString controlStats.pushPop ++
      "\tswap_pair=" ++ toString controlStats.swapPair)
  IO.println
    ("stack_program_return_dispatch=" ++
      "dispatches=" ++ toString dispatchStats.dispatches ++
      "\tsites=" ++ toString dispatchStats.sites ++
      "\trepeated_cleanup_swaps=" ++
        toString dispatchStats.repeatedCleanupSwaps ++
      "\tshared_cleanup_swaps=" ++
        toString dispatchStats.sharedCleanupSwaps)
  IO.println
    ("timing\tstack_program\t" ++ toString (compileFinish - compileStart))
  match lowered? with
  | none => pure ()
  | some lowered =>
      match lowered.procs.find? fun proc => proc.toExpressions?.isNone with
      | some proc =>
          IO.println ("stack_program_first_proc_failure=" ++ proc.name)
          let entry :=
            Locals.Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc
          match Locals.Block.compileOpen entry proc.body with
          | none =>
              IO.println "stack_program_first_proc_open=false"
          | some (code, finalCtx) =>
              IO.println "stack_program_first_proc_open=true"
              IO.println
                ("stack_program_first_proc_final_depth=" ++
                  toString finalCtx.layout.length)
              IO.println
                ("stack_program_first_proc_direct_exit=" ++
                  boolString
                    (Locals.StmtList.hasDirectExit proc.body.stmts))
              IO.println
                ("stack_program_first_proc_finish=" ++
                  boolString
                    (Locals.finishToPreserving finalCtx proc.retc 0 code).isSome)
      | none =>
          if (Locals.Block.compile Locals.Ctx.initial lowered.body).isNone then
            IO.println "stack_program_first_proc_failure=program-body"
          else
            pure ()
  match structured? with
  | none => pure ()
  | some structured =>
      match structured.procs.find? fun proc =>
          (Structured.TypedCfgCompiler.compileProcBodies?
            structured.procs [proc] 0).isNone with
      | some proc =>
          IO.println ("stack_program_first_cfg_proc_failure=" ++ proc.name)
          IO.println
            ("stack_program_first_cfg_proc_statements=" ++
              toString proc.body.stmts.length)
          match firstCfgPrefixFailure? structured.procs proc with
          | none =>
              IO.println "stack_program_first_cfg_prefix_failure=fallthrough"
          | some count =>
              IO.println
                ("stack_program_first_cfg_prefix_failure=" ++ toString count)
              match proc.body.stmts[count - 1]? with
              | none => pure ()
              | some stmt =>
                  IO.println
                    ("stack_program_first_cfg_statement_kind=" ++
                      structuredStmtKind stmt)
              match firstCfgFailurePhase? structured.procs proc count with
              | none => pure ()
              | some phase =>
                  IO.println
                    ("stack_program_first_cfg_failure_phase=" ++ phase)
      | none =>
          let mainCtx : Structured.TypedCfgCompiler.Context :=
            { procs := structured.procs }
          if (Structured.TypedCfgCompiler.compileBlock? structured.body
              mainCtx 0 Structured.TypedCfgCompiler.entryLabel
              TypedCfg.Shape.caller Structured.ProcLabel.programEnd).isNone then
            IO.println "stack_program_first_cfg_proc_failure=program-body"
          else
            pure ()
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
  IO.println
    ("direct_discard_viability=" ++
      "transitions=" ++ toString summary.discardMetrics.transitions ++
      "\tsuccessful=" ++ toString summary.discardMetrics.successful ++
      "\tfailures=" ++ toString summary.discardMetrics.failures ++
      "\told_swaps=" ++ toString summary.discardMetrics.oldSwaps ++
      "\tdirect_swaps=" ++ toString summary.discardMetrics.directSwaps ++
      "\trestore_failures=" ++
        toString summary.discardMetrics.restoreFailures ++
      "\trestore_swaps=" ++ toString summary.discardMetrics.restoreSwaps ++
      "\tdiscards=" ++ toString summary.discardMetrics.discards)
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
  let artifactStart ← IO.monoMsNow
  let objectArtifact? :=
    program.object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
      config.linkerSymbols
  let frontendArtifact? :=
    objectArtifact?.map Solidity.Frontend.VerifiedStackObjectArtifact.codeArtifact
  let compactFrontendArtifact? := frontendArtifact?.map (·.compact)
  IO.println
    ("stack_frontend_object_artifact=" ++ boolString objectArtifact?.isSome)
  IO.println
    ("stack_frontend_object_bytecode_bytes=" ++
      toString
        (objectArtifact?.map (fun artifact => artifact.image.bytes.length)
          |>.getD 0))
  let artifactFinish ← IO.monoMsNow
  IO.println
    ("timing\tstack_frontend_object\t" ++
      toString (artifactFinish - artifactStart))
  IO.println
    ("stack_frontend_code_artifact=" ++ boolString frontendArtifact?.isSome)
  IO.println
    ("stack_frontend_compact_code_artifact=" ++
      boolString compactFrontendArtifact?.isSome)
  IO.println
    ("stack_frontend_compact_code_bytecode_bytes=" ++
      toString (compactFrontendArtifact?.map (·.bytes.size) |>.getD 0))
  IO.println
    ("stack_frontend_compact_pinned_pushes=" ++
      toString
        (compactFrontendArtifact?.map (·.pinnedPushPcs.length) |>.getD 0))
  match functionsForStackDiagnostics? program.object config.linkerSymbols with
  | none =>
      throw
        (IO.userError
          "stack diagnostic Yul-to-Functions normalization returned none")
  | some functions =>
      printStackDiagnostics program.source program.contract
        program.object.name functions

def runCompactAnalysis (source : Assembly.Program) : IO Unit := do
  let sourceFits := decide source.PCFits
  IO.println ("compact_source_pc_fits=" ++ boolString sourceFits)
  if !sourceFits then return
  IO.println
    ("compact_source_instructions=" ++ toString source.length)
  let elided := Assembly.Compact.elideFallthroughJumpsFast source
  IO.println
    ("compact_elided_instructions=" ++ toString elided.length)
  let referenced := Assembly.Compact.referencedLabelsFast elided
  IO.println
    ("compact_referenced_labels=" ++ toString referenced.length)
  let physical :=
    Assembly.Compact.pruneUnreferencedLabelsFast referenced elided
  IO.println
    ("compact_prepared=true\tinstructions=" ++ toString physical.length)
  let preparation? :=
    Assembly.Compact.alignPreparationFast? source physical
  IO.println
    ("compact_preparation=" ++ boolString preparation?.isSome)
  let some preparation := preparation? | return
  let preparationSafe :=
    Assembly.Compact.preparationSafeIndexed? source physical preparation
  IO.println
    ("compact_preparation_safe=" ++ boolString preparationSafe)
  if !preparationSafe then return
  let branchWidth? := Assembly.Compact.branchWidthFor? [] physical
  IO.println
    ("compact_branch_width=" ++
      match branchWidth? with
      | none => "none"
      | some width => toString width)
  let some branchWidth := branchWidth? | return
  let layout? := Assembly.Compact.layout? [] physical branchWidth
  IO.println ("compact_layout=" ++ boolString layout?.isSome)
  let some (labels, codeLength) := layout? | return
  IO.println
    ("compact_layout_labels=" ++ toString labels.length ++
      "\tbytes=" ++ toString codeLength)
  let emitted? := Assembly.Compact.emit? [] physical branchWidth labels
  IO.println ("compact_emit=" ++ boolString emitted?.isSome)
  let some emitted := emitted? | return
  IO.println
    ("compact_emit_instructions=" ++ toString emitted.code.length)
  let blocks? :=
    Assembly.Compact.emitBlocksFast? [] physical branchWidth labels
  IO.println ("compact_blocks=" ++ boolString blocks?.isSome)
  let some blocks := blocks? | return
  IO.println ("compact_block_count=" ++ toString blocks.length)
  let blockCodeMatches :=
    Assembly.Compact.blocksCodeMatches? blocks emitted.code
  IO.println
    ("compact_block_code=" ++ boolString blockCodeMatches)
  let labelsConsistent := Assembly.Compact.labelsConsistent? blocks labels
  IO.println
    ("compact_labels_consistent=" ++ boolString labelsConsistent)
  let wellFormed := emitted.wellFormedFast?
  IO.println ("compact_well_formed=" ++ boolString wellFormed)
  let bytes := Assembly.Compact.encode emitted
  IO.println ("compact_encoded_bytes=" ++ toString bytes.size)

def runStackAnalysis (config : Config)
    (program : Solidity.Frontend.Program) : IO Unit := do
  match functionsForStackDiagnostics? program.object config.linkerSymbols with
  | none =>
      throw
        (IO.userError
          "stack analysis Yul-to-Functions normalization returned none")
  | some functions =>
      let normalized :=
        Functions.StackPressureNormalization.Program.normalize functions
      IO.println
        ("source_accepted=" ++ boolString
          (Functions.SourceAcceptedCheck.Program.sourceAccepted? functions))
      IO.println
        ("normalized_source_accepted=" ++ boolString
          (Functions.SourceAcceptedCheck.Program.sourceAccepted? normalized))
      IO.println
        ("source_open_supported=" ++ boolString
          (Functions.OpenSupportCheck.Program.openSupported? functions))
      IO.println
        ("normalized_open_supported=" ++ boolString
          (Functions.OpenSupportCheck.Program.openSupported? normalized))
      let locals? := Functions.StackLowering.lowerProgram? normalized
      IO.println
        ("normalized_lowering=" ++ boolString
          locals?.isSome)
      let expressions? := locals?.bind Locals.Program.toExpressions?
      IO.println
        ("normalized_expressions=" ++ boolString expressions?.isSome)
      let structuredWF := expressions?.any fun expressions =>
        Structured.SourceAcceptedCheck.Program.wf? expressions.toStructured
      IO.println ("normalized_structured_wf=" ++ boolString structuredWF)
      let generated? := expressions?.bind fun expressions =>
        Structured.TypedCfgCompiler.artifactWithProcEntryShapes?
          expressions.toStructured []
      IO.println
        ("normalized_cfg_generated=" ++ boolString generated?.isSome)
      let independent := generated?.any fun generated =>
        generated.cfg.programCounterIndependent?
      IO.println
        ("normalized_cfg_independent=" ++ boolString independent)
      let certified? := generated?.bind fun generated =>
        if generated.cfg.programCounterIndependent? then
          generated.cfg.compileCertified?
        else
          none
      IO.println
        ("normalized_cfg_certified=" ++ boolString certified?.isSome)
      match certified? with
      | none => pure ()
      | some certified => runCompactAnalysis certified.target
      let target? := certified?.bind fun certified =>
        Assembly.compileExecutable? certified.target
      IO.println ("normalized_target=" ++ boolString target?.isSome)
      let decodeWindow := target?.any
        Assembly.Bytecode.targetFitsDecodeWindow?
      IO.println ("normalized_decode_window=" ++ boolString decodeWindow)
      let reports := Functions.StackDiagnostics.programReports normalized
      let summary := Functions.StackDiagnostics.summarize reports
      IO.println "stack_analysis=complete"
      IO.println ("units=" ++ toString summary.units)
      IO.println ("liveness_ok=" ++ toString summary.livenessOk)
      IO.println ("schedule_ok=" ++ toString summary.scheduleOk)
      IO.println ("lowering_ok=" ++ toString summary.loweringOk)
      IO.println ("next_use_ok=" ++ toString summary.nextUseOk)
      IO.println ("peak_live=" ++ toString summary.metrics.peakLive)
      IO.println
        ("inaccessible_depth_failures=" ++ toString summary.accessFailures)
      match Functions.StackDiagnostics.firstFailure? reports with
      | none => IO.println "first_failure=none"
      | some (unitName, failure) =>
          IO.println ("first_failure_unit=" ++ unitName)
          IO.println ("first_failure_path=" ++ failure.path)
          IO.println ("first_failure_phase=" ++ failure.phase)
          IO.println ("first_failure_reason=" ++ failure.reason)

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
  if config.mode == .stackAnalysis then
    runStackAnalysis config program
    return
  if config.mode == .stackDiagnostics then
    runStackDiagnostics config program
    return
  let compileStart ← IO.monoMsNow
  let compiledObject? :=
    program.object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
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
          throw (IO.userError "verified object-image generation returned none")
      | .stackAnalysis | .stackDiagnostics => pure ()
      | .rawImage | .rawSummary | .rawCheck => pure ()
  | some artifact =>
      match config.mode with
      | .image | .summary =>
          -- Fail-closed: emit only theorem-covered bytes. The public
          -- correctness theorem is conditioned on the stack-headroom
          -- certificate; without it the image is not covered. This mirrors
          -- the raw path and `Solidus.compile?`'s own success condition.
          match artifact.stackHeadroomCert? with
          | none =>
              throw (IO.userError
                "object-image rejected: no stack-headroom certificate")
          | some _ => printImage config.mode artifact.image
      | .check =>
          let solcOk :=
            match resolveForSolcValidation? program.object artifact.computed with
            | some resolved => resolved.toSolcYulProgram?.isSome
            | none => false
          printCheck program (some artifact.image) solcOk
      | .stackAnalysis | .stackDiagnostics => pure ()
      | .rawImage | .rawSummary | .rawCheck => pure ()

def runRaw (config : RawConfig) : IO Unit := do
  let allowOversize ← allowOversizeFromEnv
  let decodeStart ← IO.monoMsNow
  let input ← IO.FS.readFile config.rawPath
  let program? :=
    Solidity.RawAst.decodeAndElaborateSolcIr? input config.selection
  let decodeFinish ← IO.monoMsNow
  IO.println ("timing\tdecode\t" ++ toString (decodeFinish - decodeStart))
  let compileStart ← IO.monoMsNow
  let artifact? :=
    Solidity.RawAst.compileArtifactFromRawSolcIr? input config.selection
  let byteLength :=
    match artifact? with
    | some artifact => artifact.image.bytes.length
    | none => 0
  let compileFinish ← IO.monoMsNow
  IO.println
    ("timing\tobject_image\t" ++ toString (compileFinish - compileStart) ++
      "\tbytes=" ++ toString byteLength)
  match artifact? with
  | none =>
      match config.mode with
      | .rawCheck =>
          match program? with
          | some program => printCheck program none false
          | none => throw (IO.userError "raw Standard JSON decode failed")
      | .rawImage | .rawSummary =>
          -- Unlinked-library fallback: compile with the missing
          -- `linkersymbol` names exported as link references.
          let unlinked? :=
            Solidity.RawAst.compileArtifactUnlinkedFromRawSolcIr?
              input config.selection
          match unlinked?, program?,
              Solidity.RawAst.decodeLinkerSymbols? input config.selection with
          | some artifact, some program, some linkerSymbols =>
              -- Fail-closed: emit only theorem-covered bytes. The public
              -- correctness theorem is conditioned on the stack-headroom
              -- certificate; without it the image is not covered.
              match artifact.stackHeadroomCert? with
              | none =>
                  throw (IO.userError
                    "raw object-image rejected: no stack-headroom certificate")
              | some _ =>
                  checkImageSizeCap config.selection.objectSelector
                    artifact.image.bytes.length allowOversize
                  printImage config.mode artifact.image
                    (program.object.missingLinkerSymbolNames linkerSymbols)
          | _, _, _ =>
              throw
                (IO.userError "raw object-image generation returned none")
      | .image | .summary | .check | .stackAnalysis | .stackDiagnostics =>
          pure ()
  | some artifact =>
      match config.mode with
      | .rawImage | .rawSummary =>
          -- Ship the frozen public entry's bytes verbatim. `Solidus.compile?`
          -- IS the value the correctness theorem quantifies over: it runs the
          -- same `compileArtifactFromRawSolcIr?` pipeline, gates success on the
          -- stack-headroom certificate, and returns `artifact.image.bytes`.
          -- Emitting its result (rather than re-reading `artifact.image`
          -- directly) makes the shipped bytes definitionally the theorem's
          -- bytes. The decoded `artifact` is reused only for the (byte-
          -- identical) link/immutable reference metadata.
          match Solidus.compile? input config.selection with
          | none =>
              throw (IO.userError
                "raw object-image rejected: no stack-headroom certificate")
          | some bytes =>
              checkImageSizeCap config.selection.objectSelector
                bytes.length allowOversize
              printImageBytes config.mode bytes artifact.image
      | .rawCheck =>
          match program? with
          | none => throw (IO.userError "raw Standard JSON decode failed")
          | some program =>
              let solcOk :=
                match resolveForSolcValidation? program.object artifact.computed with
                | some resolved => resolved.toSolcYulProgram?.isSome
                | none => false
              printCheck program (some artifact.image) solcOk
      | .image | .summary | .check | .stackAnalysis | .stackDiagnostics =>
          pure ()

def usage : String :=
  "usage: evm-compiler-backend " ++
    "(image|summary|check|stack-analysis|stack-diagnostics) " ++
    "BRIDGE_JSON [NAME=DECIMAL ...]\n" ++
    "   or: evm-compiler-backend " ++
    "(raw-image|raw-summary|raw-check) " ++
    "RAW_STANDARD_JSON SOURCE CONTRACT (creation|runtime|OBJECT_NAME)"

def cliMain (args : List String) : IO UInt32 := do
  match parseCommand? args with
  | none =>
      IO.eprintln usage
      pure 2
  | some command =>
      try
        match command with
        | .bridge config => run config
        | .raw config => runRaw config
        pure 0
      catch err =>
        IO.eprintln err.toString
        pure 1

end EvmCompiler.BackendCli

def main (args : List String) : IO UInt32 :=
  EvmCompiler.BackendCli.cliMain args
