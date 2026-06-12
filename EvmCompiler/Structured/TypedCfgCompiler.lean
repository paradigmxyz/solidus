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
  breakShape? : Option Shape := none
  continueLabel? : Option Assembly.Label := none
  continueShape? : Option Shape := none
  leaveLabel? : Option Assembly.Label := none
  leaveShape? : Option Shape := none

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

/--
Check that every regular path through a nested fragment reaches the enclosing
join with the shape expected there. A fragment with no regular path is
compatible with any join shape.
-/
def requireFallthrough? (result : Result) (expected : Shape) : Option Unit :=
  match result.fallthrough? with
  | none => some ()
  | some actual =>
      if actual = expected then some () else none

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

/--
The stack shape visible to Structured source execution.

When a compiler-owned return token is present, source execution sees exactly
the slots above that token. The token and caller suffix remain target-only
representation details.
-/
def sourceView (shape : Shape) : Shape :=
  match shape.returnTokenDepth? with
  | none => shape
  | some depth =>
      { slots := shape.slots.take depth
        tail := .closed }

def sourceLength (shape : Shape) : Nat :=
  shape.sourceView.length

def SourceFrameFits (shape : Shape) (stackLength : Nat) : Prop :=
  shape.sourceLength ≤ stackLength ∧
    ∀ depth,
      shape.returnTokenDepth? = some depth →
        stackLength = depth

def requireSourceWords? (count : Nat) (shape : Shape) : Option Unit :=
  if count ≤ shape.sourceLength then some () else none

def requireReturnTokenDepth? (depth : Nat) (shape : Shape) : Option Unit :=
  if shape.returnTokenDepth? = some depth then some () else none

end Shape

namespace BasicInstr

def basicOpToCfg : BasicOp → TypedCfg.Instr
  | .pop => .pop
  | .dup1 => .dup 0
  | .dup2 => .dup 1
  | .dup3 => .dup 2
  | .dup4 => .dup 3
  | .dup5 => .dup 4
  | .dup6 => .dup 5
  | .dup7 => .dup 6
  | .dup8 => .dup 7
  | .dup9 => .dup 8
  | .dup10 => .dup 9
  | .dup11 => .dup 10
  | .dup12 => .dup 11
  | .dup13 => .dup 12
  | .dup14 => .dup 13
  | .dup15 => .dup 14
  | .dup16 => .dup 15
  | .swap1 => .swap 0
  | .swap2 => .swap 1
  | .swap3 => .swap 2
  | .swap4 => .swap 3
  | .swap5 => .swap 4
  | .swap6 => .swap 5
  | .swap7 => .swap 6
  | .swap8 => .swap 7
  | .swap9 => .swap 8
  | .swap10 => .swap 9
  | .swap11 => .swap 10
  | .swap12 => .swap 11
  | .swap13 => .swap 12
  | .swap14 => .swap 13
  | .swap15 => .swap 14
  | .swap16 => .swap 15
  | op => .prim op.toPrimOp

def toCfg : BasicInstr → TypedCfg.Instr
  | .push value => .push value
  | .op op => basicOpToCfg op
  | .bindLocals offset names => .bindLocals offset names
  | .bindScratch baseDepth name slot => .bindScratch baseDepth name slot

/--
Source instructions may use only slots above the compiler-owned return token.

Generated call-entry shuffles are typed directly as TypedCfg instructions and
therefore remain able to move the token into place. This check applies only to
Structured source code, preventing target execution from satisfying a missing
source operand with hidden call-frame data.
-/
def sourceSafe? (instr : BasicInstr) (input output : Shape) : Bool :=
  decide
    (TypedCfg.Instr.type? (toCfg instr) input.sourceView =
      some output.sourceView)

theorem sourceType_of_sourceSafe
    {instr : BasicInstr} {input output : Shape}
    (hSafe : sourceSafe? instr input output = true) :
    TypedCfg.Instr.type? (toCfg instr) input.sourceView =
      some output.sourceView := by
  simpa [sourceSafe?] using of_decide_eq_true hSafe

end BasicInstr

namespace Code

def toCfg (code : Code) : List TypedCfg.Instr :=
  code.map BasicInstr.toCfg

def type? : Code → Shape → Option Shape
  | [], input => some input
  | instr :: rest, input =>
      do
        let middle ← TypedCfg.Instr.type? (BasicInstr.toCfg instr) input
        if BasicInstr.sourceSafe? instr input middle = true then
          type? rest middle
        else
          none

theorem bodyType?_toCfg_of_type?
    {code : Code} {input output : Shape}
    (hType : type? code input = some output) :
    TypedCfg.Block.bodyType? (toCfg code) input = some output := by
  induction code generalizing input with
  | nil =>
      simpa [type?, toCfg, TypedCfg.Block.bodyType?] using hType
  | cons instr rest ih =>
      unfold type? at hType
      cases hInstr :
          TypedCfg.Instr.type? (BasicInstr.toCfg instr) input with
      | none =>
          simp [hInstr] at hType
      | some middle =>
          cases hSafe :
              BasicInstr.sourceSafe? instr input middle with
          | false =>
              simp [hInstr, hSafe] at hType
          | true =>
            have hTail :
                type? rest middle = some output := by
              simpa [hInstr, hSafe] using hType
            simp only [toCfg, List.map_cons,
              TypedCfg.Block.bodyType?, hInstr]
            exact ih hTail

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

def mkCodeBlock? (label : Assembly.Label) (input : Shape)
    (code : Code) (term : TypedCfg.Terminator) :
    Option CfgBlock := do
  let output ← Code.type? code input
  some
    { label := label
      input := input
      body := Code.toCfg code
      output := output
      term := term }

def sinkTopUnder : Nat → List TypedCfg.Instr
  | 0 => []
  | depth + 1 => .swap depth :: sinkTopUnder depth

def jumpOrInvalid (target? : Option Assembly.Label) : TypedCfg.Terminator :=
  match target? with
  | some target => .jump target
  | none => .invalid

def checkedJumpOrInvalid
    (target? : Option Assembly.Label) (expected? : Option Shape)
    (input : Shape) : Option TypedCfg.Terminator := do
  let target ← target?
  let expected ← expected?
  if input = expected then
    some (.jump target)
  else
    none

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
          let block ← mkCodeBlock? entry input code (.jump regular)
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := some block.output }
      | .if_ cond body => do
          let bodyLabel := LabelSupply.label supply 0
          let head ←
            mkCodeBlock? entry input cond (.jumpi bodyLabel regular)
          let condOutput := head.output
          let _ ← Shape.requireSourceWords? 1 condOutput
          let condition ← condOutput.slots.head?
          let branchInput :=
            { condOutput with slots := condOutput.slots.tail }
          let bodyResult ←
            compileBlockFuel? fuel body ctx (supply + 1) bodyLabel
              branchInput regular
          let _ ← bodyResult.requireFallthrough? branchInput
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
          let head ←
            mkCodeBlock? entry input scrutinee (.jump firstTest)
          let valueShape := head.output
          let _ ← Shape.requireSourceWords? 1 valueShape
          let _value ← valueShape.slots.head?
          let bodyShape :=
            { valueShape with slots := valueShape.slots.tail }
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
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
          let initResult ←
            compileBlockFuel? fuel init outerCtx (supply + 1) entry input
              loopLabel
          let loopInput ← initResult.fallthrough?
          let loopBlock ←
            mkCodeBlock? loopLabel loopInput cond
              (.jumpi bodyLabel endLabel)
          let condOutput := loopBlock.output
          let _ ← Shape.requireSourceWords? 1 condOutput
          let _condition ← condOutput.slots.head?
          let branchInput :=
            { condOutput with slots := condOutput.slots.tail }
          let bodyCtx :=
            { ctx with
              breakLabel? := some endLabel
              breakShape? := some branchInput
              continueLabel? := some postLabel
              continueShape? := some branchInput }
          let bodyResult ←
            compileBlockFuel? fuel body bodyCtx initResult.next bodyLabel
              branchInput postLabel
          let _ ← bodyResult.requireFallthrough? branchInput
          let postResult ←
            compileBlockFuel? fuel post outerCtx bodyResult.next postLabel
              branchInput loopLabel
          let _ ← postResult.requireFallthrough? loopInput
          some
            { blocks :=
                initResult.blocks ++ [loopBlock] ++ bodyResult.blocks ++
                  postResult.blocks
              next := postResult.next
              calls :=
                initResult.calls ++ bodyResult.calls ++ postResult.calls
              fallthrough? := some branchInput }
      | .brk => do
          let term ←
            checkedJumpOrInvalid ctx.breakLabel? ctx.breakShape? input
          let block ←
            mkBlock? entry input [] term
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }
      | .cont => do
          let term ←
            checkedJumpOrInvalid ctx.continueLabel? ctx.continueShape? input
          let block ←
            mkBlock? entry input [] term
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }
      | .leave => do
          let term ←
            checkedJumpOrInvalid ctx.leaveLabel? ctx.leaveShape? input
          let block ←
            mkBlock? entry input [] term
          some
            { blocks := [block]
              next := supply + 1
              calls := []
              fallthrough? := none }
      | .call name => do
          let proc ← ProcList.lookup? name ctx.procs
          let _ ← Shape.requireSourceWords? proc.argc input
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
          let _ ← Shape.requireSourceWords? kind.argCount input
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
          let _ ← bodyResult.requireFallthrough? bodyShape
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
          let _ ← bodyResult.requireFallthrough? bodyShape
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
          leaveLabel? := some (ProcLabel.exit proc.name)
          leaveShape? := some (Shape.procExit proc) }
      let body ← match entryShapes.find? proc.name with
        | none => do
            let compiled ←
              compileBlock? proc.body ctx supply
                (ProcLabel.entry proc.name) (Shape.procEntry proc)
                (ProcLabel.exit proc.name)
            let _ ← compiled.requireFallthrough? (Shape.procExit proc)
            some compiled
        | some bodyInput => do
            let _ ← Shape.requireReturnTokenDepth? proc.argc bodyInput
            let adapter ←
              mkBlock? (ProcLabel.entry proc.name) (Shape.procEntry proc)
                [.relabel bodyInput] (.jump (ProcLabel.body proc.name))
            let compiled ←
              compileBlock? proc.body ctx supply (ProcLabel.body proc.name)
                bodyInput (ProcLabel.exit proc.name)
            let _ ← compiled.requireFallthrough? (Shape.procExit proc)
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

theorem generateWithProcEntryShapes?_entry
    {program : Program} {entryShapes : ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      generateWithProcEntryShapes? program entryShapes = some cfg) :
    cfg.entry = entryLabel := by
  unfold generateWithProcEntryShapes? at hGenerate
  cases hMain :
      compileBlock? program.body { procs := program.procs } 0 entryLabel
        TypedCfg.Shape.caller ProcLabel.programEnd with
  | none =>
      simp [hMain] at hGenerate
  | some main =>
      cases hProcs :
          lowerProcBodiesWithShapes? entryShapes program.procs program.procs
            main.next with
      | none =>
          simp [hMain, hProcs] at hGenerate
      | some procResult =>
          rcases procResult with ⟨procBlocks, next, procCalls⟩
          simp [hMain, hProcs] at hGenerate
          rcases hGenerate with ⟨_hTokens, hCfg⟩
          simpa using
            congrArg TypedCfg.Program.entry hCfg.symm

theorem artifactWithProcEntryShapes?_entry
    {program : Program} {entryShapes : ProcEntryShapes}
    {artifact : CompileArtifact}
    (hArtifact :
      artifactWithProcEntryShapes? program entryShapes = some artifact) :
    artifact.cfg.entry = entryLabel := by
  unfold artifactWithProcEntryShapes? at hArtifact
  cases hGenerate :
      generateWithProcEntryShapes? program entryShapes with
  | none =>
      simp [hGenerate] at hArtifact
  | some cfg =>
      by_cases hCheck : cfg.wellTyped? = true
      · simp [hGenerate, hCheck] at hArtifact
        cases hArtifact
        exact generateWithProcEntryShapes?_entry hGenerate
      · simp [hGenerate, hCheck] at hArtifact

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

end Examples

end TypedCfgCompiler
end Structured
end EvmCompiler
