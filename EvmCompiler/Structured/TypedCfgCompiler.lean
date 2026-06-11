import EvmCompiler.Structured.ControlLabels
import EvmCompiler.TypedCfg

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompiler

abbrev Shape := TypedCfg.Shape
abbrev CfgBlock := TypedCfg.Block

def entryLabel : Assembly.Label :=
  .named "structured:typedcfg:entry"

def restLabel (supply : LabelSupply) : Assembly.Label :=
  .generated supply 100

def switchTestLabel (base idx : Nat) : Assembly.Label :=
  .generated base (1000 + idx)

structure Context where
  procs : List Proc
  breakLabel? : Option Assembly.Label := none
  continueLabel? : Option Assembly.Label := none
  leaveLabel? : Option Assembly.Label := none

structure DispatchSite where
  procName : Name
  token : Word
  returnLabel : Assembly.Label
  caseLabel : Assembly.Label
  deriving DecidableEq, Repr

structure Result where
  blocks : List CfgBlock
  next : LabelSupply
  calls : List DispatchSite
  fallthrough? : Option Shape

namespace Result

def append (left right : Result) : Result where
  blocks := left.blocks ++ right.blocks
  next := right.next
  calls := left.calls ++ right.calls
  fallthrough? := right.fallthrough?

end Result

namespace Shape

def words (count : Nat) (tail : TypedCfg.FrameTail := .caller) : Shape :=
  { slots := List.replicate count .word, tail := tail }

def procEntry (proc : Proc) : Shape :=
  { slots :=
      List.replicate proc.argc .word ++ [.returnToken]
    tail := .caller }

def namedProcEntry? (proc : Proc) (names : List Name) : Option Shape :=
  if names.length = proc.argc then
    some
      { slots := names.map TypedCfg.Slot.local ++ [.returnToken]
        tail := .caller }
  else
    none

def procExit (proc : Proc) : Shape :=
  { slots :=
      List.replicate proc.retc .word ++ [.returnToken]
    tail := .caller }

def afterCall (input : Shape) (argc retc : Nat) : Option Shape :=
  if argc ≤ input.length then
    some (TypedCfg.Shape.pushWords retc (TypedCfg.Shape.pop argc input))
  else
    none

end Shape

namespace BasicInstr

def toCfg : BasicInstr → TypedCfg.Instr
  | .push value => .push value
  | .op op => .prim op.toPrimOp

end BasicInstr

namespace Code

def toCfg (code : Code) : List TypedCfg.Instr :=
  code.map BasicInstr.toCfg

def type? (code : Code) (input : Shape) : Option Shape :=
  TypedCfg.Block.bodyType? (Code.toCfg code) input

end Code

def mkBlock? (label : Assembly.Label) (input : Shape)
    (body : List TypedCfg.Instr) (term : TypedCfg.Terminator) :
    Option CfgBlock := do
  let output ← TypedCfg.Block.bodyType? body input
  some
    { label := label
      input := input
      body := body
      output := output
      term := term }

def sinkTopUnder : Nat → List TypedCfg.Instr
  | 0 => []
  | depth + 1 => .swap depth :: sinkTopUnder depth

def jumpOrInvalid (target? : Option Assembly.Label) : TypedCfg.Terminator :=
  match target? with
  | some target => .jump target
  | none => .invalid

mutual
  def blockFuel : Block → Nat
    | ⟨stmts⟩ => stmtListFuel stmts + 1

  def stmtFuel : Stmt → Nat
    | .code _ => 1
    | .if_ _ body => blockFuel body + 1
    | .switch _ cases defaultBody =>
        caseListFuel cases + defaultFuel defaultBody + 1
    | .for_ init _ post body =>
        blockFuel init + blockFuel post + blockFuel body + 1
    | .brk | .cont | .leave | .call _ | .terminal _ => 1

  def stmtListFuel : List Stmt → Nat
    | [] => 1
    | stmt :: rest => stmtFuel stmt + stmtListFuel rest + 1

  def caseListFuel : List (Word × Block) → Nat
    | [] => 1
    | (_, body) :: rest => blockFuel body + caseListFuel rest + 1

  def defaultFuel : Option Block → Nat
    | none => 1
    | some body => blockFuel body + 1
end

mutual
  def compileBlockFuel? : Nat → Block → Context →
      LabelSupply → Assembly.Label → Shape → Assembly.Label → Option Result
    | 0, _block, _ctx, _supply, _entry, _input, _regular => none
    | fuel + 1, block, ctx, supply, entry, input, regular =>
      compileStmtListFuel? fuel block.stmts ctx supply entry input regular

  def compileStmtListFuel? : Nat → List Stmt → Context →
      LabelSupply → Assembly.Label → Shape → Assembly.Label → Option Result
    | 0, _stmts, _ctx, _supply, _entry, _input, _regular => none
    | fuel + 1, stmts, ctx, supply, entry, input, regular =>
      match stmts with
      | [] => do
          let block ← mkBlock? entry input [] (.jump regular)
          some
            { blocks := [block]
              next := supply
              calls := []
              fallthrough? := some input }
      | stmt :: rest => do
          let nextEntry := restLabel supply
          let head ←
            compileStmtFuel? fuel stmt ctx supply entry input nextEntry
          match head.fallthrough? with
          | none => some head
          | some nextInput =>
              let tail ←
                compileStmtListFuel? fuel rest ctx head.next nextEntry
                  nextInput regular
              some (head.append tail)

  def compileStmtFuel? : Nat → Stmt → Context →
      LabelSupply → Assembly.Label → Shape → Assembly.Label → Option Result
    | 0, _stmt, _ctx, _supply, _entry, _input, _regular => none
    | fuel + 1, stmt, ctx, supply, entry, input, regular =>
      match stmt with
      | .code code => do
          let body := Code.toCfg code
          let block ← mkBlock? entry input body (.jump regular)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := some block.output }
      | .if_ cond body => do
          let bodyLabel := LabelSupply.label supply 0
          let condBody := Code.toCfg cond
          let condOutput ← TypedCfg.Block.bodyType? condBody input
          let condition ← condOutput.slots.head?
          let branchInput :=
            { condOutput with slots := condOutput.slots.tail }
          let head ←
            mkBlock? entry input condBody (.jumpi bodyLabel regular)
          let bodyResult ←
            compileBlockFuel? fuel body ctx (supply + 1) bodyLabel
              branchInput regular
          let _ := condition
          some
            { blocks := head :: bodyResult.blocks
              next := bodyResult.next
              calls := bodyResult.calls
              fallthrough? := some branchInput }
      | .switch scrutinee cases defaultBody => do
          let defaultLabel := LabelSupply.label supply 1
          let firstTest :=
            match cases with
            | [] => defaultLabel
            | _ => switchTestLabel supply 0
          let scrutineeBody := Code.toCfg scrutinee
          let valueShape ← TypedCfg.Block.bodyType? scrutineeBody input
          let _value ← valueShape.slots.head?
          let bodyShape :=
            { valueShape with slots := valueShape.slots.tail }
          let head ← mkBlock? entry input scrutineeBody (.jump firstTest)
          let caseResult ←
            compileCasesFuel? fuel cases ctx supply (supply + 1) 0 valueShape
              bodyShape regular
          let defaultResult ←
            compileDefaultFuel? fuel defaultBody ctx caseResult.next
              defaultLabel valueShape bodyShape regular
          some
            { blocks := head :: caseResult.blocks ++ defaultResult.blocks
              next := defaultResult.next
              calls := caseResult.calls ++ defaultResult.calls
              fallthrough? := some bodyShape }
      | .for_ init cond post body => do
          let loopLabel := LabelSupply.label supply 0
          let bodyLabel := LabelSupply.label supply 1
          let postLabel := LabelSupply.label supply 2
          let endLabel := regular
          let outerCtx :=
            { ctx with breakLabel? := none, continueLabel? := none }
          let initResult ←
            compileBlockFuel? fuel init outerCtx (supply + 1) entry input
              loopLabel
          let loopInput ← initResult.fallthrough?
          let condBody := Code.toCfg cond
          let condOutput ← TypedCfg.Block.bodyType? condBody loopInput
          let _condition ← condOutput.slots.head?
          let branchInput :=
            { condOutput with slots := condOutput.slots.tail }
          let loopBlock ←
            mkBlock? loopLabel loopInput condBody (.jumpi bodyLabel endLabel)
          let bodyCtx :=
            { ctx with
              breakLabel? := some endLabel
              continueLabel? := some postLabel }
          let bodyResult ←
            compileBlockFuel? fuel body bodyCtx initResult.next bodyLabel
              branchInput postLabel
          let postInput := bodyResult.fallthrough?.getD branchInput
          let postResult ←
            compileBlockFuel? fuel post outerCtx bodyResult.next postLabel
              postInput loopLabel
          some
            { blocks :=
                initResult.blocks ++ [loopBlock] ++ bodyResult.blocks ++
                  postResult.blocks
              next := postResult.next
              calls :=
                initResult.calls ++ bodyResult.calls ++ postResult.calls
              fallthrough? := some branchInput }
      | .brk => do
          let block ←
            mkBlock? entry input [] (jumpOrInvalid ctx.breakLabel?)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }
      | .cont => do
          let block ←
            mkBlock? entry input [] (jumpOrInvalid ctx.continueLabel?)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }
      | .leave => do
          let block ←
            mkBlock? entry input [] (jumpOrInvalid ctx.leaveLabel?)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }
      | .call name => do
          let proc ← ProcList.lookup? name ctx.procs
          let returnShape ← Shape.afterCall input proc.argc proc.retc
          let token := Stmt.callToken supply
          let body := .returnToken token :: sinkTopUnder proc.argc
          let block ←
            mkBlock? entry input body (.jump (ProcLabel.entry name))
          some
            { blocks := [block]
              next := supply + 1
              calls :=
                [{ procName := name
                   token := token
                   returnLabel := regular
                   caseLabel := .generated supply 10000 }]
              fallthrough? := some returnShape }
      | .terminal kind => do
          let block ← mkBlock? entry input [] (.halt kind)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }

  def compileCasesFuel? : Nat → List (Word × Block) → Context →
      Nat → Nat → Nat → Shape → Shape → Assembly.Label → Option Result
    | 0, _cases, _ctx, _base, _supply, _idx, _valueShape, _bodyShape,
        _regular => none
    | fuel + 1, cases, ctx, base, supply, idx, valueShape, bodyShape,
        regular =>
      match cases with
      | [] =>
          some
            { blocks := []
              next := supply
              calls := []
              fallthrough? := some bodyShape }
      | (value, body) :: rest => do
          let testLabel := switchTestLabel base idx
          let caseLabel := LabelSupply.label base (idx + 2)
          let caseBodyLabel := Assembly.Label.generated base (2000 + idx)
          let nextTest :=
            match rest with
            | [] => LabelSupply.label base 1
            | _ => switchTestLabel base (idx + 1)
          let testBody : List TypedCfg.Instr :=
            [.dup 0, .push value, .prim .eq]
          let testBlock ←
            mkBlock? testLabel valueShape testBody
              (.jumpi caseLabel nextTest)
          let bodyEntry ←
            mkBlock? caseLabel valueShape [.pop] (.jump caseBodyLabel)
          let bodyResult ←
            compileBlockFuel? fuel body ctx supply caseBodyLabel bodyShape
              regular
          let tail ←
            compileCasesFuel? fuel rest ctx base bodyResult.next (idx + 1)
              valueShape bodyShape regular
          some
            { blocks :=
                testBlock :: bodyEntry :: bodyResult.blocks ++ tail.blocks
              next := tail.next
              calls := bodyResult.calls ++ tail.calls
              fallthrough? := some bodyShape }

  def compileDefaultFuel? : Nat → Option Block → Context →
      LabelSupply → Assembly.Label → Shape → Shape → Assembly.Label →
        Option Result
    | 0, _defaultBody, _ctx, _supply, _entry, _valueShape, _bodyShape,
        _regular => none
    | fuel + 1, defaultBody, ctx, supply, entry, valueShape, bodyShape,
        regular =>
      match defaultBody with
      | none => do
          let block ← mkBlock? entry valueShape [.pop] (.jump regular)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := some bodyShape }
      | some body => do
          let bodyLabel := Assembly.Label.generated supply 2000
          let entryBlock ←
            mkBlock? entry valueShape [.pop] (.jump bodyLabel)
          let bodyResult ←
            compileBlockFuel? fuel body ctx (supply + 1) bodyLabel bodyShape
              regular
          some
            { blocks := entryBlock :: bodyResult.blocks
              next := bodyResult.next
              calls := bodyResult.calls
              fallthrough? := some bodyShape }
end

def compileBlock? (block : Block) (ctx : Context)
      (supply : LabelSupply) (entry : Assembly.Label) (input : Shape)
      (regular : Assembly.Label) : Option Result :=
  compileBlockFuel? (blockFuel block + 1) block ctx supply entry input regular

abbrev ProcEntryShapes := List (Name × Shape)

namespace ProcEntryShapes

def find? (shapes : ProcEntryShapes) (name : Name) : Option Shape :=
  (List.find? (fun candidate : Name × Shape =>
    decide (candidate.1 = name)) shapes).map Prod.snd

end ProcEntryShapes

def lowerProcBodiesWithShapes? (entryShapes : ProcEntryShapes)
    (allProcs : List Proc) :
    List Proc → LabelSupply →
      Option (List CfgBlock × LabelSupply × List DispatchSite)
  | [], supply => some ([], supply, [])
  | proc :: rest, supply => do
      let ctx : Context :=
        { procs := allProcs
          leaveLabel? := some (ProcLabel.exit proc.name) }
      let body ← match entryShapes.find? proc.name with
        | none =>
            compileBlock? proc.body ctx supply (ProcLabel.entry proc.name)
              (Shape.procEntry proc) (ProcLabel.exit proc.name)
        | some bodyInput => do
            let adapter ←
              mkBlock? (ProcLabel.entry proc.name) (Shape.procEntry proc)
                [.relabel bodyInput] (.jump (ProcLabel.body proc.name))
            let compiled ←
              compileBlock? proc.body ctx supply (ProcLabel.body proc.name)
                bodyInput (ProcLabel.exit proc.name)
            some { compiled with blocks := adapter :: compiled.blocks }
      let (tailBlocks, next, tailCalls) ←
        lowerProcBodiesWithShapes? entryShapes allProcs rest body.next
      some (body.blocks ++ tailBlocks, next, body.calls ++ tailCalls)

def compileProcBodies? (allProcs : List Proc) :
    List Proc → LabelSupply →
      Option (List CfgBlock × LabelSupply × List DispatchSite) :=
  lowerProcBodiesWithShapes? [] allProcs

def returnSitesFor (name : Name) (calls : List DispatchSite) :
    List TypedCfg.ReturnSite :=
  calls.filterMap fun site =>
    if site.procName = name then
      some
        { token := site.token
          target := site.returnLabel
          caseLabel := site.caseLabel }
    else
      none

def dispatchBlock (proc : Proc) (calls : List DispatchSite) : CfgBlock :=
  let sites := returnSitesFor proc.name calls
  let term :=
    if sites.isEmpty then
      TypedCfg.Terminator.invalid
    else
      TypedCfg.Terminator.returnDispatch proc.retc sites
  { label := ProcLabel.exit proc.name
    input := Shape.procExit proc
    body := []
    output := Shape.procExit proc
    term := term }

def dispatchBlocks (procs : List Proc) (calls : List DispatchSite) :
    List CfgBlock :=
  procs.map fun proc => dispatchBlock proc calls

structure CompileArtifact where
  cfg : TypedCfg.Program
  wellTyped : cfg.WellTyped

def generateWithProcEntryShapes? (program : Program)
    (entryShapes : ProcEntryShapes) : Option TypedCfg.Program := do
  let mainCtx : Context := { procs := program.procs }
  let mainInput := TypedCfg.Shape.caller
  let main ←
    compileBlock? program.body mainCtx 0 entryLabel mainInput
      ProcLabel.programEnd
  let (procBlocks, _next, procCalls) ←
    lowerProcBodiesWithShapes? entryShapes program.procs program.procs
      main.next
  let calls := main.calls ++ procCalls
  if (calls.map DispatchSite.token).Nodup then
    let endInput := main.fallthrough?.getD mainInput
    let endBlock : CfgBlock :=
      { label := ProcLabel.programEnd
        input := endInput
        body := []
        output := endInput
        term := .invalid }
    let cfg : TypedCfg.Program :=
      { entry := entryLabel
        blocks :=
          main.blocks ++ procBlocks ++
            dispatchBlocks program.procs calls ++ [endBlock] }
    some cfg
  else
    none

def generate? (program : Program) : Option TypedCfg.Program :=
  generateWithProcEntryShapes? program []

def artifactWithProcEntryShapes? (program : Program)
    (entryShapes : ProcEntryShapes) : Option CompileArtifact := do
  let cfg ← generateWithProcEntryShapes? program entryShapes
  if hCheck : cfg.wellTyped? = true then
    some
      { cfg := cfg
        wellTyped := TypedCfg.Program.wellTyped_of_check hCheck }
  else
    none

def compileArtifact? (program : Program) : Option CompileArtifact :=
  artifactWithProcEntryShapes? program []

def lowerWithProcEntryShapes? (program : Program)
    (entryShapes : ProcEntryShapes) : Option TypedCfg.Program :=
  (artifactWithProcEntryShapes? program entryShapes).map
    CompileArtifact.cfg

def compile? (program : Program) : Option TypedCfg.Program :=
  (compileArtifact? program).map CompileArtifact.cfg

theorem compile?_wellTyped {program : Program} {cfg : TypedCfg.Program}
    (hCompile : compile? program = some cfg) :
    cfg.WellTyped := by
  unfold compile? at hCompile
  cases hArtifact : compileArtifact? program with
  | none =>
      simp [hArtifact] at hCompile
  | some artifact =>
      simp [hArtifact] at hCompile
      cases hCompile
      exact artifact.wellTyped

namespace Examples

def emptyProgram : Program :=
  { procs := []
    body := { stmts := [] } }

def branchProgram : Program :=
  { procs := []
    body :=
      { stmts :=
          [.if_ [.push (EvmYul.UInt256.ofNat 1)]
            { stmts :=
                [.code
                  [.push (EvmYul.UInt256.ofNat 2), .op .pop]] }] } }

def switchProgram : Program :=
  { procs := []
    body :=
      { stmts :=
          [.switch [.push (EvmYul.UInt256.ofNat 1)]
            [(EvmYul.UInt256.ofNat 1, { stmts := [] })]
            (some { stmts := [] })] } }

def leafProc : Proc :=
  { name := "leaf"
    argc := 0
    retc := 0
    body := { stmts := [] } }

def callProgram : Program :=
  { procs := [leafProc]
    body := { stmts := [.call "leaf"] } }

def loopProgram : Program :=
  { procs := []
    body :=
      { stmts :=
          [.for_ { stmts := [] }
            [.push (EvmYul.UInt256.ofNat 0)]
            { stmts := [] }
            { stmts := [] }] } }

def breakLoopProgram : Program :=
  { procs := []
    body :=
      { stmts :=
          [.for_ { stmts := [] }
            [.push (EvmYul.UInt256.ofNat 1)]
            { stmts := [] }
            { stmts := [.brk] }] } }

def identityProc : Proc :=
  { name := "identity"
    argc := 1
    retc := 1
    body := { stmts := [] } }

def arityCallProgram : Program :=
  { procs := [identityProc]
    body :=
      { stmts :=
          [.code [.push (EvmYul.UInt256.ofNat 7)], .call "identity",
            .code [.op .pop]] } }

def resourceObserverProgram : Program :=
  { procs := []
    body :=
      { stmts :=
          [.code [.op .gas, .op .pop, .op .msize, .op .pop]] } }

def externalCallProgram : Program :=
  { procs := []
    body :=
      { stmts :=
          [.code
            [.push (EvmYul.UInt256.ofNat 0),
              .push (EvmYul.UInt256.ofNat 0),
              .push (EvmYul.UInt256.ofNat 0),
              .push (EvmYul.UInt256.ofNat 0),
              .push (EvmYul.UInt256.ofNat 0),
              .push (EvmYul.UInt256.ofNat 0),
              .op .staticcall,
              .op .pop]] } }

def compilesCertified (program : Program) : Bool :=
  match compile? program with
  | none => false
  | some cfg => cfg.compileCertified?.isSome

def namedArityCallBodyShape : Shape :=
  { slots := [.local "value", .returnToken]
    tail := .caller }

def namedArityCallBodyShapeRecorded : Bool :=
  match
      lowerWithProcEntryShapes? arityCallProgram
        [("identity", namedArityCallBodyShape)] with
  | none => false
  | some cfg =>
      decide
        (cfg.labelShape? (ProcLabel.entry "identity") =
            some (Shape.procEntry identityProc) ∧
          cfg.labelShape? (ProcLabel.body "identity") =
            some namedArityCallBodyShape)

example : (compile? emptyProgram).isSome = true := by
  native_decide

example : (compile? branchProgram).isSome = true := by
  native_decide

example : (compile? switchProgram).isSome = true := by
  native_decide

example : (compile? callProgram).isSome = true := by
  native_decide

example : (compile? loopProgram).isSome = true := by
  native_decide

example : (compile? breakLoopProgram).isSome = true := by
  native_decide

example : (compile? arityCallProgram).isSome = true := by
  native_decide

example : compilesCertified arityCallProgram = true := by
  native_decide

example : namedArityCallBodyShapeRecorded = true := by
  native_decide

example : compilesCertified resourceObserverProgram = true := by
  native_decide

example : compilesCertified externalCallProgram = true := by
  native_decide

end Examples

end TypedCfgCompiler
end Structured
end EvmCompiler
