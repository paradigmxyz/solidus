import EvmCompiler.Structured.InteractionCallPreservation
import EvmCompiler.Structured.InteractionBoundaryPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionOwnerPreservation

namespace OpenOutcome

abbrev StopPolicy :=
  InteractionControlPreservation.OpenOutcome.StopPolicy

abbrev Rel :=
  InteractionControlPreservation.OpenOutcome.Rel

abbrev ExecPreservesUnder :=
  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder

abbrev BoundaryShapes :=
  InteractionBoundaryPreservation.OpenOutcome.BoundaryShapes

abbrev RecursiveBoundary :=
  InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary

/--
The complete local contract needed by the execution-indexed owner for one
compiled Structured fragment.
-/
structure FragmentContract
    (cfg : TypedCfg.Program)
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (supply : LabelSupply)
    (entry regular : Assembly.Label)
    (input : TypedCfg.Shape)
    (source : RunState) (tokens : List Word)
    (policy : StopPolicy) : Prop where
  fits :
    TypedCfgCompiler.Shape.SourceFrameFits
      input source.evm.stack.length
  regularAt :
    TypedCfgCompilerFacts.RegularAtSupply regular supply
  before :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      ctx regular supply
  activation :
    TypedCfgPreservation.ActivationInput tokens input
  boundary :
    RecursiveBoundary
      cfg source.returns tokens policy supply regular
  shapes :
    BoundaryShapes cfg result ctx regular
  stops :
    ∀ {sourceOutcome targetOutcome},
      Rel result ctx regular source.returns tokens
          sourceOutcome targetOutcome →
        InteractionControlPreservation.OpenOutcome.TargetStoppedBy
          policy targetOutcome
  nonregular :
    InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular
      policy ctx source.returns tokens

namespace FragmentContract

end FragmentContract

/--
Statement-local variant of `FragmentContract`.

A statement-list head may use the current compiler `restLabel` as its regular
continuation. Lexical nonregular continuations still predate the statement,
while the regular label is tracked by `RegularAtSupply`.
-/
structure StmtContract
    (cfg : TypedCfg.Program)
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (supply : LabelSupply)
    (entry regular : Assembly.Label)
    (input : TypedCfg.Shape)
    (source : RunState) (tokens : List Word)
    (policy : StopPolicy) : Prop where
  fits :
    TypedCfgCompiler.Shape.SourceFrameFits
      input source.evm.stack.length
  regularAt :
    TypedCfgCompilerFacts.RegularAtSupply regular supply
  before :
    TypedCfgCompilerFacts.NonregularLabelsBeforeSupply ctx supply
  activation :
    TypedCfgPreservation.ActivationInput tokens input
  boundary :
    RecursiveBoundary
      cfg source.returns tokens policy supply regular
  shapes :
    BoundaryShapes cfg result ctx regular
  stops :
    ∀ {sourceOutcome targetOutcome},
      Rel result ctx regular source.returns tokens
          sourceOutcome targetOutcome →
        InteractionControlPreservation.OpenOutcome.TargetStoppedBy
          policy targetOutcome
  nonregular :
    InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular
      policy ctx source.returns tokens

namespace StmtContract

theorem before_succ
    {cfg : TypedCfg.Program}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      ctx regular (supply + 1) :=
  (contract.before.mono (Nat.le_succ supply)).with_regular
    contract.regularAt.before_succ

end StmtContract

theorem FragmentContract.stmt
    {cfg : TypedCfg.Program}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    (contract :
      FragmentContract cfg result ctx supply entry regular input
        source tokens policy) :
    StmtContract cfg result ctx supply entry regular input
      source tokens policy :=
  { fits := contract.fits
    regularAt := contract.regularAt
    before := contract.before.nonregular
    activation := contract.activation
    boundary := contract.boundary
    shapes := contract.shapes
    stops := contract.stops
    nonregular := contract.nonregular }

/--
Capability supplied to one statement owner for every recursively executed
source block at a fixed smaller source-fuel index.
-/
def BlockOwnerAt
    (sourceFuel : Nat)
    (program : Structured.Program)
    (entryShapes : TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg) : Prop :=
  ∀ {blockSourceFuel compilerFuel : Nat} {block : Structured.Block}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result}
      {source : RunState} {tokens : List Word}
      {policy : StopPolicy}
      {canBreak canContinue canLeave : Bool},
    blockSourceFuel ≤ sourceFuel →
    TypedCfgCompiler.compileBlockFuel? compilerFuel block ctx
        supply entry input regular =
      some result →
    TypedCfgPreservation.BlocksInProgram result cfg →
    TypedCfgPreservation.CallsInProgram result generated.calls →
    Structured.Block.WF canBreak canContinue canLeave block →
    block.FrameSafe →
    Structured.ProcList.BlockCallsResolved program.procs block →
    TypedCfgPreservation.OutcomeSimulation.ContextSupports
      ctx canBreak canContinue canLeave →
    ctx.procs = program.procs →
    (canLeave = true →
      ∃ frame rest, source.returns = frame :: rest) →
    FragmentContract cfg result ctx supply entry regular input
      source tokens policy →
    ExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        program blockSourceFuel block source)
      policy

theorem BlockOwnerAt.mono
    {smaller larger : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    (hOwner : BlockOwnerAt larger program entryShapes cfg generated)
    (hLe : smaller ≤ larger) :
    BlockOwnerAt smaller program entryShapes cfg generated := by
  intro blockSourceFuel compilerFuel block ctx supply entry regular input
    result source tokens policy canBreak canContinue canLeave hBlockLe
  exact hOwner (Nat.le_trans hBlockLe hLe)

namespace BoundaryShapes

theorem with_regular
    {cfg : TypedCfg.Program}
    {parent child : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {parentRegular childRegular : Assembly.Label}
    (hParent : BoundaryShapes cfg parent ctx parentRegular)
    (hRegular :
      ∀ {shape},
        child.fallthrough? = some shape →
          TypedCfgPreservation.LabelShape cfg childRegular shape) :
    BoundaryShapes cfg child ctx childRegular where
  regular := hRegular
  break_ := hParent.break_
  continue_ := hParent.continue_
  leave := hParent.leave

theorem of_fallthrough_none
    {cfg : TypedCfg.Program}
    {parent child : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {parentRegular childRegular : Assembly.Label}
    (hParent : BoundaryShapes cfg parent ctx parentRegular)
    (hNone : child.fallthrough? = none) :
    BoundaryShapes cfg child ctx childRegular :=
  hParent.with_regular (by
    intro shape hShape
    rw [hNone] at hShape
    cases hShape)

theorem of_required_fallthrough
    {cfg : TypedCfg.Program}
    {parent child : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label}
    {expected : TypedCfg.Shape}
    (hParent : BoundaryShapes cfg parent ctx regular)
    (hRequire : child.requireFallthrough? expected = some ())
    (hParentFallthrough : parent.fallthrough? = some expected) :
    BoundaryShapes cfg child ctx regular :=
  hParent.with_regular (by
    intro shape hShape
    have hExpected :
        child.fallthrough? = some expected := by
      rcases
          TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
            hRequire with
        hNone | hSome
      · rw [hNone] at hShape
        cases hShape
      · exact hSome
    have hShapeEq : shape = expected :=
      Option.some.inj (hShape.symm.trans hExpected)
    subst shape
    exact hParent.regular hParentFallthrough)

end BoundaryShapes

/-!
Transport of every label-indexed contract across a shift of the dense
call-token counter `Context.callBase`.

`TypedCfgCompiler.Context.advance` (and the explicit `callBase` literals the
statement-list, switch and loop arms now install) changes only that counter.
`ContextSupports`, `ContinuationLabelsBeforeSupply`, `BoundaryShapes`,
`Rel` and hence `FragmentContract` read a compiler context solely through its
continuation labels and shapes, so each transports definitionally.
-/
namespace CallBase

theorem contextSupports
    {ctx : TypedCfgCompiler.Context}
    {canBreak canContinue canLeave : Bool}
    (base : Nat)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave) :
    TypedCfgPreservation.OutcomeSimulation.ContextSupports
      { ctx with callBase := base } canBreak canContinue canLeave where
  breakLabel := hSupports.breakLabel
  continueLabel := hSupports.continueLabel
  leaveLabel := hSupports.leaveLabel

theorem continuationLabels
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (base : Nat)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply) :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      { ctx with callBase := base } regular supply where
  regular := hBefore.regular
  breakLabel := hBefore.breakLabel
  continueLabel := hBefore.continueLabel
  leaveLabel := hBefore.leaveLabel

theorem boundaryShapes
    {cfg : TypedCfg.Program}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label}
    (base : Nat)
    (hShapes : BoundaryShapes cfg result ctx regular) :
    BoundaryShapes cfg result { ctx with callBase := base } regular where
  regular := hShapes.regular
  break_ := hShapes.break_
  continue_ := hShapes.continue_
  leave := hShapes.leave

theorem fragmentContract
    {cfg : TypedCfg.Program}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    (base : Nat)
    (contract :
      FragmentContract cfg result ctx supply entry regular input
        source tokens policy) :
    FragmentContract cfg result { ctx with callBase := base } supply entry
      regular input source tokens policy where
  fits := contract.fits
  regularAt := contract.regularAt
  before := continuationLabels base contract.before
  activation := contract.activation
  boundary := contract.boundary
  shapes := boundaryShapes base contract.shapes
  stops := by
    intro sourceOutcome targetOutcome hRel
    exact
      contract.stops
        (sourceOutcome := sourceOutcome) (targetOutcome := targetOutcome)
        hRel
  nonregular := by
    intro childResult childRegular sourceOutcome targetOutcome hMode hRel
    exact contract.nonregular hMode hRel

end CallBase

namespace LoopContract

theorem outer_before
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label}
    {supply next : LabelSupply}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular supply)
    (hSupply : supply ≤ next) :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      (InteractionLoopPreservation.Loop.outerContext ctx)
      regular next := by
  have hMono := hBefore.mono hSupply
  exact
    { regular := hMono.regular
      breakLabel := by
        intro label hLabel
        simp [InteractionLoopPreservation.Loop.outerContext] at hLabel
      continueLabel := by
        intro label hLabel
        simp [InteractionLoopPreservation.Loop.outerContext] at hLabel
      leaveLabel := by
        intro label hLabel
        apply hMono.leaveLabel label
        simpa [InteractionLoopPreservation.Loop.outerContext] using hLabel }

theorem generated_before
    {supply next tag : Nat}
    (hSupply : supply + 1 ≤ next) :
    TypedCfgCompilerFacts.LabelBeforeSupply
      (LabelSupply.label supply tag) next := by
  simp [TypedCfgCompilerFacts.LabelBeforeSupply, LabelSupply.label]
  omega

theorem outer_generated_before
    {ctx : TypedCfgCompiler.Context}
    {parentRegular : Assembly.Label}
    {supply next tag : Nat}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx parentRegular (supply + 1))
    (hSupply : supply + 1 ≤ next) :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      (InteractionLoopPreservation.Loop.outerContext ctx)
      (LabelSupply.label supply tag) next := by
  have hOuter := outer_before hBefore hSupply
  exact
    { regular := generated_before hSupply
      breakLabel := hOuter.breakLabel
      continueLabel := hOuter.continueLabel
      leaveLabel := hOuter.leaveLabel }

theorem body_before
    {ctx : TypedCfgCompiler.Context}
    {parentRegular childRegular : Assembly.Label}
    {branchInput : TypedCfg.Shape}
    {supply next postTag : Nat}
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx parentRegular (supply + 1))
    (hSupply : supply + 1 ≤ next)
    (hChildRegular :
      TypedCfgCompilerFacts.LabelBeforeSupply childRegular next) :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      (InteractionLoopPreservation.Loop.bodyContext
        ctx parentRegular (LabelSupply.label supply postTag)
        branchInput)
      childRegular next := by
  have hMono := hBefore.mono hSupply
  exact
    { regular := hChildRegular
      breakLabel := by
        intro label hLabel
        simp [InteractionLoopPreservation.Loop.bodyContext] at hLabel
        subst label
        exact hMono.regular
      continueLabel := by
        intro label hLabel
        simp [InteractionLoopPreservation.Loop.bodyContext] at hLabel
        subst label
        exact generated_before hSupply
      leaveLabel := by
        intro label hLabel
        apply hMono.leaveLabel label
        simpa [InteractionLoopPreservation.Loop.bodyContext] using hLabel }

theorem outer_shapes
    {cfg : TypedCfg.Program}
    {parent child : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {parentRegular childRegular : Assembly.Label}
    {expected : TypedCfg.Shape}
    (hParent : BoundaryShapes cfg parent ctx parentRegular)
    (hRequire : child.requireFallthrough? expected = some ())
    (hRegularShape :
      TypedCfgPreservation.LabelShape cfg childRegular expected) :
    BoundaryShapes cfg child
      (InteractionLoopPreservation.Loop.outerContext ctx)
      childRegular := by
  exact
    { regular := by
        intro shape hShape
        rcases
            TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
              hRequire with
          hNone | hSome
        · rw [hNone] at hShape
          cases hShape
        · have hEq : shape = expected :=
            Option.some.inj (hShape.symm.trans hSome)
          subst shape
          exact hRegularShape
      break_ := by
        intro label shape hLabel _hShape
        simp [InteractionLoopPreservation.Loop.outerContext] at hLabel
      continue_ := by
        intro label shape hLabel _hShape
        simp [InteractionLoopPreservation.Loop.outerContext] at hLabel
      leave := by
        intro label shape hLabel hShape
        apply hParent.leave
        · simpa [InteractionLoopPreservation.Loop.outerContext] using hLabel
        · simpa [InteractionLoopPreservation.Loop.outerContext] using hShape }

theorem body_shapes
    {cfg : TypedCfg.Program}
    {parent bodyResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {parentRegular postLabel : Assembly.Label}
    {branchInput : TypedCfg.Shape}
    (hParent : BoundaryShapes cfg parent ctx parentRegular)
    (hParentFallthrough :
      parent.fallthrough? = some branchInput)
    (hBodyRequire :
      bodyResult.requireFallthrough? branchInput = some ())
    (hPostShape :
      TypedCfgPreservation.LabelShape cfg postLabel branchInput) :
    BoundaryShapes cfg bodyResult
      (InteractionLoopPreservation.Loop.bodyContext
        ctx parentRegular postLabel branchInput)
      postLabel := by
  exact
    { regular := by
        intro shape hShape
        rcases
            TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
              hBodyRequire with
          hNone | hSome
        · rw [hNone] at hShape
          cases hShape
        · have hEq : shape = branchInput :=
            Option.some.inj (hShape.symm.trans hSome)
          subst shape
          exact hPostShape
      break_ := by
        intro label shape hLabel hShape
        simp [InteractionLoopPreservation.Loop.bodyContext] at hLabel hShape
        subst label
        subst shape
        exact hParent.regular hParentFallthrough
      continue_ := by
        intro label shape hLabel hShape
        simp [InteractionLoopPreservation.Loop.bodyContext] at hLabel hShape
        subst label
        subst shape
        exact hPostShape
      leave := by
        intro label shape hLabel hShape
        apply hParent.leave
        · simpa [InteractionLoopPreservation.Loop.bodyContext] using hLabel
        · simpa [InteractionLoopPreservation.Loop.bodyContext] using hShape }

end LoopContract

namespace CallContract

theorem extension
    {source : RunState} {tokens : List Word}
    {args callerStack : EvmYul.Stack Word}
    {retc supply : Nat} :
    TypedCfgPreservation.ActivationExtension
      source.returns tokens
      (((source.withEVM { source.evm with stack := args }).pushReturn
        callerStack retc).returns)
      (Structured.Stmt.callToken supply :: tokens) := by
  simpa using
    TypedCfgPreservation.ActivationExtension.one
      source.returns tokens
      { callerStack := callerStack, retc := retc }
      (Structured.Stmt.callToken supply)

theorem before
    {program : Structured.Program} {proc : Structured.Proc}
    {supply : LabelSupply} (callBase : Nat) :
    TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
      (InteractionCallPreservation.Call.procContext program proc callBase)
      (ProcLabel.exit proc.name) supply := by
  exact
    { regular := by trivial
      breakLabel := by
        intro label hLabel
        simp [InteractionCallPreservation.Call.procContext] at hLabel
      continueLabel := by
        intro label hLabel
        simp [InteractionCallPreservation.Call.procContext] at hLabel
      leaveLabel := by
        intro label hLabel
        simp [InteractionCallPreservation.Call.procContext] at hLabel
        subst label
        trivial }

theorem shapes
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc)
    (fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes program.procs proc
        generated.procBlocks generated.procCalls)
    (callBase : Nat) :
    BoundaryShapes cfg fragment.result
      (InteractionCallPreservation.Call.procContext program proc callBase)
      (ProcLabel.exit proc.name) := by
  have hExitShape :=
    TypedCfgPreservation.LabelShape.procExit generated hLookup
  exact
    { regular := by
        intro shape hShape
        rcases
            TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
              fragment.fallthrough with
          hNone | hSome
        · rw [hNone] at hShape
          cases hShape
        · have hEq :
              shape = TypedCfgCompiler.Shape.procExit proc :=
            Option.some.inj (hShape.symm.trans hSome)
          subst shape
          exact hExitShape
      break_ := by
        intro label shape hLabel _hShape
        simp [InteractionCallPreservation.Call.procContext] at hLabel
      continue_ := by
        intro label shape hLabel _hShape
        simp [InteractionCallPreservation.Call.procContext] at hLabel
      leave := by
        intro label shape hLabel hShape
        simp [InteractionCallPreservation.Call.procContext] at hLabel hShape
        subst label
        subst shape
        exact hExitShape }

theorem supports
    (program : Structured.Program) (proc : Structured.Proc)
    (callBase : Nat) :
    TypedCfgPreservation.OutcomeSimulation.ContextSupports
      (InteractionCallPreservation.Call.procContext program proc callBase)
      false false true := by
  exact
    { breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by
        intro _hAllowed
        exact ⟨ProcLabel.exit proc.name, rfl⟩ }

end CallContract

private theorem block_sourceFuel_zero_no_success
    {program : Structured.Program} {block : Structured.Block}
    {source : RunState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Structured.Outcome}
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Block.openRun program 0 block source)
        transcript (.ok outcome)) :
    False := by
  simp only [
    InteractionSemantics.Block.openRun,
    EffectSemantics.Control.Block.run] at hExec
  cases hExec

namespace Stmt

theorem code_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.code code) source)
      policy :=
  InteractionControlPreservation.OpenOutcome.PreservesUnder.exec
    (InteractionControlPreservation.Stmt.openRun_code_under_of_compileStmtFuel?
      (regularExit := .stop)
      hCompile hBlocks contract.fits contract.stops)

theorem if_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF
        canBreak canContinue canLeave (.if_ cond body))
    (hFrameSafe : Structured.Stmt.FrameSafe (.if_ cond body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved
        program.procs (.if_ cond body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.if_ cond body) source)
      policy := by
  cases hWF with
  | if_ hBodyWF =>
      cases hFrameSafe with
      | if_ _hCondSafe hBodySafe =>
          cases hCalls with
          | if_ hBodyCallsResolved =>
              apply
                InteractionBranchPreservation.Stmt.openRun_if_exec_under_of_compileStmtFuel?
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation
                  contract.boundary contract.stops
              intro output bodyResult afterCond
                hBodyCompile hBodyBlocks hBodyCalls hReturns
                hBodyFits hRequire hFallthrough
              apply
                hBlockOwner (Nat.le_refl sourceFuel)
                  hBodyCompile hBodyBlocks hBodyCalls
                  hBodyWF hBodySafe hBodyCallsResolved hSupports hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt :=
                      Or.inl contract.regularAt.before_succ
                    before := contract.before_succ
                    activation :=
                      contract.activation.stmtFallthrough
                        hCompile hFallthrough
                    boundary :=
                      (contract.boundary.mono
                        (Nat.le_succ supply)).congr_returns hReturns.symm
                    shapes :=
                      contract.shapes.of_required_fallthrough
                        hRequire hFallthrough
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      apply contract.stops
                      have hWhole :=
                        InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hRequire hFallthrough hRel
                      simpa [hReturns] using hWhole
                    nonregular := by
                      intro childResult childRegular
                        sourceOutcome targetOutcome hMode hRel
                      apply contract.nonregular hMode
                      simpa [hReturns] using hRel }

theorem switch_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave
        (.switch scrutinee cases defaultBody))
    (hFrameSafe :
      Structured.Stmt.FrameSafe
        (.switch scrutinee cases defaultBody))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs
        (.switch scrutinee cases defaultBody))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      policy := by
  cases hWF with
  | switch hCasesWF hDefaultWF =>
      cases hFrameSafe with
      | switch _hScrutineeSafe hCasesSafe hDefaultSafe =>
          cases hCalls with
          | switch hCasesCalls hDefaultCalls =>
              apply
                InteractionSwitchPreservation.Stmt.openRun_switch_exec_under_of_compileStmtFuel?
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation
                  contract.boundary contract.stops
              intro bodyCompilerFuel bodySupply bodyCallBase bodyEntry
                bodyInput body bodyResult afterPop value hSelect
                hBodyCompile hBodyBlocks hBodyResultCalls hBodySupply
                hReturns hBodyFits hRequire hFallthrough
              have hSelectedWF :=
                Structured.Switch.wf_of_select
                  hCasesWF hDefaultWF hSelect
              have hSelectedFrameSafe :=
                TypedCfgCompilerFacts.switch_property_of_select
                  hCasesSafe hDefaultSafe hSelect
              have hSelectedCalls :=
                TypedCfgCompilerFacts.switch_property_of_select
                  hCasesCalls hDefaultCalls hSelect
              have hSupply : supply ≤ bodySupply :=
                Nat.le_trans (Nat.le_succ supply) hBodySupply
              have hBefore := contract.before_succ.mono hBodySupply
              apply
                hBlockOwner (Nat.le_refl sourceFuel)
                  hBodyCompile hBodyBlocks hBodyResultCalls
                  hSelectedWF hSelectedFrameSafe hSelectedCalls
                  (CallBase.contextSupports bodyCallBase hSupports) hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt :=
                      Or.inl
                        (contract.regularAt.before_succ.mono hBodySupply)
                    before :=
                      CallBase.continuationLabels bodyCallBase hBefore
                    activation :=
                      contract.activation.stmtFallthrough
                        hCompile hFallthrough
                    boundary :=
                      (contract.boundary.mono hSupply).congr_returns
                        hReturns.symm
                    shapes :=
                      CallBase.boundaryShapes bodyCallBase
                        (contract.shapes.of_required_fallthrough
                          hRequire hFallthrough)
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      apply contract.stops
                      have hWhole :=
                        InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hRequire hFallthrough hRel
                      simpa [hReturns] using hWhole
                    nonregular := by
                      intro childResult childRegular sourceOutcome
                        targetOutcome hMode hRel
                      apply contract.nonregular hMode
                      simpa [hReturns] using hRel }

theorem for_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave
        (.for_ init cond post body))
    (hFrameSafe :
      Structured.Stmt.FrameSafe (.for_ init cond post body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs
        (.for_ init cond post body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program (sourceFuel + 1)
        (.for_ init cond post body) source)
      policy := by
  cases hWF with
  | for_ hInitWF hPostWF hBodyWF =>
      cases hFrameSafe with
      | for_ hInitSafe _hCondSafe hPostSafe hBodySafe =>
          cases hCalls with
          | for_ hInitCalls hPostCalls hBodyCalls =>
              apply
                InteractionLoopPreservation.Loop.Stmt.openRun_for_exec_under_of_compileStmtFuel?
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation
                  contract.boundary contract.stops
              · intro initResult loopInput hInitCompile hInitBlocks
                  hInitResultCalls hLoopShape hInitFallthrough
                have hInitRequire :
                    initResult.requireFallthrough? loopInput = some () :=
                  TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
                    (Or.inr hInitFallthrough)
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hInitRequire hLoopShape
                apply
                  hBlockOwner (Nat.le_refl sourceFuel)
                    hInitCompile hInitBlocks hInitResultCalls
                    hInitWF hInitSafe hInitCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · exact hSourceReturns
                · simpa [
                      InteractionLoopPreservation.Loop.initStopPolicy] using
                    (show
                      FragmentContract cfg initResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        (supply + 1) entry
                        (LabelSupply.label supply 0) input source tokens
                        (InteractionLoopPreservation.Loop.initStopPolicy
                          initResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := contract.fits
                        regularAt := Or.inl hInitBefore.regular
                        before := hInitBefore
                        activation := contract.activation
                        boundary :=
                          (contract.boundary.mono
                            (Nat.le_succ supply)).push
                              hInitShapes hOuterBefore
                        shapes := hInitShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel
                        nonregular :=
                          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                            policy })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel bodySource hFuel hBodyCompile hPostCompile
                  hBodyBlocks hFacts hBodyFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply ≤ initResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.initSupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    hFacts.initSupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                have hBodyBoundaryBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 0)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyShapes :
                    BoundaryShapes cfg bodyResult
                      (InteractionLoopPreservation.Loop.bodyContext
                        ctx regular (LabelSupply.label supply 2)
                        branchInput)
                      (LabelSupply.label supply 2) := by
                  simpa [branchInput] using
                    (LoopContract.body_shapes contract.shapes
                      hFacts.enclosingFallthrough hFacts.bodyRequire
                      hFacts.postShape)
                have hBodyBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 2)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyBoundary :=
                  hPostBoundary.push hBodyShapes hBodyBoundaryBefore
                apply
                  hBlockOwner (Nat.le_of_lt hFuel)
                    hBodyCompile hBodyBlocks hFacts.bodyCalls
                    hBodyWF hBodySafe hBodyCalls
                    (CallBase.contextSupports
                      (ctx.callBase + initResult.calls.length)
                      (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                        hSupports regular (LabelSupply.label supply 2)
                        branchInput))
                    (by
                      simpa [InteractionLoopPreservation.Loop.bodyContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ :=
                    hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [
                      branchInput,
                      InteractionLoopPreservation.Loop.bodyStopPolicy,
                      InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg bodyResult
                        { InteractionLoopPreservation.Loop.bodyContext
                            ctx regular (LabelSupply.label supply 2)
                            branchInput with
                          callBase :=
                            ctx.callBase + initResult.calls.length }
                        initResult.next
                        (LabelSupply.label supply 1)
                        (LabelSupply.label supply 2)
                        branchInput bodySource tokens
                        (InteractionLoopPreservation.Loop.bodyStopPolicy
                          bodyResult postResult ctx regular
                          (LabelSupply.label supply 2)
                          (LabelSupply.label supply 0)
                          branchInput source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hBodyFits
                        regularAt := Or.inl hBodyBefore.regular
                        before :=
                          CallBase.continuationLabels
                            (ctx.callBase + initResult.calls.length)
                            hBodyBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hBodyBoundary.congr_returns hReturns.symm
                        shapes :=
                          CallBase.boundaryShapes
                            (ctx.callBase + initResult.calls.length)
                            hBodyShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel bodyResult
                                (InteractionLoopPreservation.Loop.bodyContext
                                  ctx regular (LabelSupply.label supply 2)
                                  branchInput)
                                (LabelSupply.label supply 2)
                                source.returns tokens
                                sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx
                                (LabelSupply.label supply 0)
                                source.returns tokens policy)
                              hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx
                                (LabelSupply.label supply 0)
                                source.returns tokens policy)
                              hMode
                          simpa [hReturns] using hRel })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel postSource hFuel hPostCompile hPostBlocks
                  hFacts hPostFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply ≤ bodyResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.bodySupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    hFacts.bodySupply
                have hPostBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ hFacts.bodySupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                apply
                  hBlockOwner (Nat.le_of_lt hFuel)
                    hPostCompile hPostBlocks hFacts.postCalls
                    hPostWF hPostSafe hPostCalls
                    (CallBase.contextSupports
                      (ctx.callBase + initResult.calls.length +
                        bodyResult.calls.length)
                      (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                        hSupports))
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ :=
                    hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [
                      branchInput,
                      InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg postResult
                        { InteractionLoopPreservation.Loop.outerContext ctx with
                          callBase :=
                            ctx.callBase + initResult.calls.length +
                              bodyResult.calls.length }
                        bodyResult.next
                        (LabelSupply.label supply 2)
                        (LabelSupply.label supply 0)
                        branchInput postSource tokens
                        (InteractionLoopPreservation.Loop.postStopPolicy
                          postResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hPostFits
                        regularAt := Or.inl hPostBefore.regular
                        before :=
                          CallBase.continuationLabels
                            (ctx.callBase + initResult.calls.length +
                              bodyResult.calls.length)
                            hPostBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hPostBoundary.congr_returns hReturns.symm
                        shapes :=
                          CallBase.boundaryShapes
                            (ctx.callBase + initResult.calls.length +
                              bodyResult.calls.length)
                            hPostShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel postResult
                                (InteractionLoopPreservation.Loop.outerContext ctx)
                                (LabelSupply.label supply 0)
                                source.returns tokens
                                sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              policy hMode
                          simpa [hReturns] using hRel })

theorem call_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {name : Structured.Name}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.call name) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs (.call name))
    (hProcs : ctx.procs = program.procs)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.call name) source)
      policy := by
  cases hCalls with
  | call hContains =>
      obtain ⟨proc, hLookup⟩ :=
        Structured.ProcList.exists_lookup?_of_contains hContains
      have hProcWF :=
        Structured.Program.procWF_of_lookup? hProgramWF hLookup
      have hProcFrameSafe :=
        Structured.Program.procFrameSafe_of_lookup?
          hProgramFrameSafe hLookup
      have hProcCalls :=
        Structured.Program.procCallsResolved_of_lookup?
          hProgramWF hLookup
      apply
        InteractionCallPreservation.Call.openRun_call_exec_under_of_compileStmtFuel?
          generated hLookup hProcs hCompile hBlocks hResultCalls
          contract.fits hProcWF contract.stops
      · intro args callerStack targetState hSplit hStateRel
        have hExtension :=
          CallContract.extension
            (source := source) (tokens := tokens)
            (args := args) (callerStack := callerStack)
            (retc := proc.retc) (supply := ctx.callBase)
        exact
          contract.boundary.ownership.eq_false_of_stateRel_extension
            (TypedCfgPreservation.LabelShape.procEntry generated hLookup)
            (TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc)
            hExtension hStateRel
            (TypedCfgPreservation.SourceFrameFits.procEntry_of_splitArgs
              hSplit)
      · intro args callerStack bodyState targetState
          hSplit hStateRel hFits hReturns
        have hExtension :
            TypedCfgPreservation.ActivationExtension
              source.returns tokens bodyState.returns
              (Structured.Stmt.callToken ctx.callBase :: tokens) := by
          rw [hReturns]
          exact
            CallContract.extension
              (source := source) (tokens := tokens)
              (args := args) (callerStack := callerStack)
              (retc := proc.retc) (supply := ctx.callBase)
        exact
          contract.boundary.ownership.eq_false_of_stateRel_extension
            (TypedCfgPreservation.LabelShape.procExit generated hLookup)
            (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
            hExtension hStateRel hFits
      · intro fragment args callerStack targetState hSplit hStateRel
        have hExtension :=
          CallContract.extension
            (source := source) (tokens := tokens)
            (args := args) (callerStack := callerStack)
            (retc := proc.retc) (supply := ctx.callBase)
        have hFragmentShape :
            TypedCfgPreservation.LabelShape
              cfg fragment.entry fragment.input :=
          TypedCfgPreservation.LabelShape.of_compileBlock?
            fragment.compile
            (by
              apply
                TypedCfgPreservation.BlocksInProgram.of_subset_of_wellTyped
                  generated.wellTyped
              intro block hMem
              rw [generated.cfgEq]
              have hProcMem := fragment.blocks block hMem
              simp [hProcMem, List.append_assoc])
        exact
          contract.boundary.ownership.eq_false_of_stateRel_extension
            hFragmentShape fragment.input_returnTokenDepth
            hExtension hStateRel
            (fragment.input_sourceFrameFits_of_splitArgs hSplit)
      · intro fragment hFragmentBlocks hFragmentCalls
          args callerStack hSplit
        let callSource : RunState :=
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
        have hFragmentCompile :
            TypedCfgCompiler.compileBlockFuel?
                (TypedCfgCompiler.blockFuel proc.body + 1)
                proc.body
                (InteractionCallPreservation.Call.procContext program proc
                  fragment.callBase)
                fragment.supply fragment.entry fragment.input
                (ProcLabel.exit proc.name) =
              some fragment.result := by
          simpa [
            TypedCfgCompiler.compileBlock?,
            InteractionCallPreservation.Call.procContext] using
            fragment.compile
        have hExtension :
            TypedCfgPreservation.ActivationExtension
              source.returns tokens callSource.returns
              (Structured.Stmt.callToken ctx.callBase :: tokens) := by
          simpa [callSource] using
            (CallContract.extension
              (source := source) (tokens := tokens)
              (args := args) (callerStack := callerStack)
              (retc := proc.retc) (supply := ctx.callBase))
        have hShapes :=
          CallContract.shapes generated hLookup fragment fragment.callBase
        apply
          hBlockOwner (Nat.le_refl sourceFuel)
            hFragmentCompile hFragmentBlocks hFragmentCalls
            hProcWF.2.2 hProcFrameSafe hProcCalls
            (CallContract.supports program proc fragment.callBase) rfl
        · intro _hCanLeave
          exact
            ⟨{ callerStack := callerStack, retc := proc.retc },
              source.returns, by simp [callSource]⟩
        · exact
            { fits :=
                fragment.input_sourceFrameFits_of_splitArgs hSplit
              regularAt := Or.inl (by trivial)
              before := CallContract.before fragment.callBase
              activation :=
                TypedCfgPreservation.ActivationInput.active
                  ⟨proc.argc, fragment.input_returnTokenDepth⟩
              boundary :=
                contract.boundary.push_child hExtension hShapes
                  (CallContract.before fragment.callBase)
              shapes := hShapes
              stops := by
                intro sourceOutcome targetOutcome hRel
                exact
                  InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                    policy hRel
              nonregular :=
                InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                  policy }

theorem brk_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .brk)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .brk source)
      policy := by
  cases hWF with
  | brk hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.breakLabel hAllowed
      exact
        InteractionControlPreservation.OpenOutcome.PreservesUnder.exec
          (InteractionLeafPreservation.Stmt.openRun_brk_under_of_compileStmtFuel?
            (regularExit := .stop)
            hExit hCompile hBlocks contract.fits contract.nonregular)

theorem cont_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .cont)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .cont source)
      policy := by
  cases hWF with
  | cont hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.continueLabel hAllowed
      exact
        InteractionControlPreservation.OpenOutcome.PreservesUnder.exec
          (InteractionLeafPreservation.Stmt.openRun_cont_under_of_compileStmtFuel?
            (regularExit := .stop)
            hExit hCompile hBlocks contract.fits contract.nonregular)

theorem leave_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .leave)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .leave source)
      policy := by
  cases hWF with
  | leave hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.leaveLabel hAllowed
      obtain ⟨frame, rest, hReturns⟩ := hSourceReturns hAllowed
      exact
        InteractionControlPreservation.OpenOutcome.PreservesUnder.exec
          (InteractionLeafPreservation.Stmt.openRun_leave_under_of_compileStmtFuel?
            (regularExit := .stop)
            hExit hReturns hCompile hBlocks contract.fits
            contract.nonregular)

theorem terminal_exec
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.terminal kind) source)
      policy :=
  InteractionControlPreservation.OpenOutcome.PreservesUnder.exec
    (InteractionLeafPreservation.Stmt.openRun_terminal_under_of_compileStmtFuel?
      (regularExit := .stop)
      hCompile hBlocks contract.fits contract.nonregular)

theorem exec_succ
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {stmt : Structured.Stmt}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          stmt ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave stmt)
    (hFrameSafe : Structured.Stmt.FrameSafe stmt)
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs stmt)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) stmt source)
      policy := by
  cases stmt with
  | code code =>
      exact code_exec hCompile hBlocks contract
  | if_ cond body =>
      exact
        if_exec hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
          hSupports hProcs hSourceReturns hBlockOwner contract
  | switch scrutinee cases defaultBody =>
      exact
        switch_exec hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
          hSupports hProcs hSourceReturns hBlockOwner contract
  | for_ init cond post body =>
      exact
        for_exec hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
          hSupports hProcs hSourceReturns hBlockOwner contract
  | brk =>
      exact brk_exec hCompile hBlocks hWF hSupports contract
  | cont =>
      exact cont_exec hCompile hBlocks hWF hSupports contract
  | leave =>
      exact
        leave_exec hCompile hBlocks hWF hSupports hSourceReturns contract
  | call name =>
      exact
        call_exec hCompile hBlocks hResultCalls hCalls hProcs
          hProgramWF hProgramFrameSafe hBlockOwner contract
  | terminal kind =>
      exact terminal_exec hCompile hBlocks contract

theorem exec_zero
    {compilerFuel : Nat}
    {program : Structured.Program} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          stmt ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave stmt)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program 0 stmt source)
      policy := by
  cases stmt with
  | code code =>
      exact code_exec hCompile hBlocks contract
  | if_ cond body
  | switch cond body defaultBody
  | for_ body cond defaultBody body_1
  | call cond =>
      intro target hStateRel transcript sourceOutcome hExec
      simp only [
        InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] at hExec
      cases hExec
  | brk =>
      exact brk_exec hCompile hBlocks hWF hSupports contract
  | cont =>
      exact cont_exec hCompile hBlocks hWF hSupports contract
  | leave =>
      exact
        leave_exec hCompile hBlocks hWF hSupports hSourceReturns contract
  | terminal kind =>
      exact terminal_exec hCompile hBlocks contract

end Stmt

/--
Fuel-founded owner for every successfully executed Structured block in one
checked generated program.

Statement-list recursion is structural. Procedure and structured-control
recursion is discharged only through strictly smaller source fuel.
-/
theorem block_owner
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) :
    BlockOwnerAt sourceFuel program entryShapes cfg generated := by
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      unfold BlockOwnerAt
      intro blockSourceFuel compilerFuel block ctx supply entry regular input
        result source tokens policy canBreak canContinue canLeave
        hSourceFuel hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
        hSupports hProcs hSourceReturns contract
      cases blockSourceFuel with
      | zero =>
          intro target hStateRel transcript sourceOutcome hExec
          exact False.elim (block_sourceFuel_zero_no_success hExec)
      | succ innerFuel =>
          have hInnerLt : innerFuel < sourceFuel := by omega
          have hInnerOwner :
              BlockOwnerAt innerFuel program entryShapes cfg generated :=
            ih innerFuel hInnerLt
          cases compilerFuel with
          | zero =>
              simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
          | succ listFuel =>
              unfold TypedCfgCompiler.compileBlockFuel? at hCompile
              cases listFuel with
              | zero =>
                  simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
              | succ compilerFuel =>
                  cases block with
                  | mk stmts =>
                      cases stmts with
                      | nil =>
                          exact
                            InteractionControlPreservation.Block.openRun_nil_exec_under_of_compileStmtListFuel?
                              hCompile hBlocks contract.fits contract.stops
                      | cons stmt rest =>
                          cases compilerFuel with
                          | zero =>
                              simp [
                                TypedCfgCompiler.compileStmtListFuel?,
                                TypedCfgCompiler.compileStmtFuel?] at hCompile
                          | succ stmtCompilerFuel =>
                              cases hWF with
                              | cons hStmtWF hRestWF =>
                                  cases hFrameSafe with
                                  | cons hStmtSafe hRestSafe =>
                                      cases hCalls with
                                      | mk hStmtListCalls =>
                                          cases hStmtListCalls with
                                          | cons hStmtCalls hRestCalls =>
                                              apply
                                                InteractionControlPreservation.Block.openRun_cons_exec_under_of_compileStmtListFuel?
                                                  hCompile hBlocks
                                                  hResultCalls
                                              · intro headResult tailResult
                                                  tailInput middleSource
                                                  targetMiddle hHeadCompile
                                                  hFallthrough hTailCompile
                                                  hTailBlocks hRel
                                                have hTailShape :
                                                    TypedCfgPreservation.LabelShape
                                                      cfg
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      tailInput :=
                                                  TypedCfgPreservation.LabelShape.of_compileStmtListFuel?
                                                    hTailCompile hTailBlocks
                                                obtain
                                                    ⟨targetState, hTarget,
                                                      hStateRel⟩ :=
                                                  TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                                                    hRel.1
                                                have hTargetEq :
                                                    targetState =
                                                      targetMiddle := by
                                                  cases hTarget
                                                  rfl
                                                subst targetState
                                                rcases hRel.2.1 with
                                                  ⟨shape, hShape, hFits⟩
                                                have hReturns :
                                                    middleSource.returns =
                                                      source.returns := by
                                                  simpa [
                                                    InteractionControlPreservation.OpenOutcome.ActivationRestored]
                                                    using hRel.2.2
                                                have hShapeEq :
                                                    shape = tailInput :=
                                                  Option.some.inj
                                                    (hShape.symm.trans
                                                      hFallthrough)
                                                subst shape
                                                exact
                                                  (contract.boundary.congr_returns
                                                    hReturns.symm).eq_false_of_stateRel
                                                    (source := middleSource)
                                                    (scope := supply)
                                                    (tag := 100)
                                                    (Nat.le_refl supply)
                                                    (contract.before.regular.generated_ne
                                                      (Nat.le_refl supply))
                                                    hTailShape
                                                    (contract.activation.stmtFallthrough
                                                      hHeadCompile
                                                      hFallthrough)
                                                    hStateRel hFits
                                              · exact contract.nonregular
                                              · intro headResult
                                                  hHeadCompile hHeadBlocks
                                                  hHeadCalls hFallthrough
                                                have hHeadContract :
                                                    StmtContract cfg headResult
                                                      ctx supply entry
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      input source tokens
                                                      policy :=
                                                  { fits := contract.fits
                                                    regularAt := Or.inr rfl
                                                    before :=
                                                      contract.before.nonregular
                                                    activation :=
                                                      contract.activation
                                                    boundary :=
                                                      contract.boundary.rebase_regular
                                                        contract.before.regular
                                                    shapes :=
                                                      contract.shapes.of_fallthrough_none
                                                        hFallthrough
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      exact
                                                        contract.nonregular
                                                          (hRel.mode_ne_regular_of_fallthrough_none
                                                            hFallthrough)
                                                          hRel
                                                    nonregular :=
                                                      contract.nonregular }
                                                cases innerFuel with
                                                | zero =>
                                                    exact
                                                      Stmt.exec_zero
                                                        hHeadCompile
                                                        hHeadBlocks hStmtWF
                                                        hSupports
                                                        hSourceReturns
                                                        hHeadContract
                                                | succ recursiveFuel =>
                                                    exact
                                                      Stmt.exec_succ
                                                        hHeadCompile
                                                        hHeadBlocks
                                                        hHeadCalls hStmtWF
                                                        hStmtSafe hStmtCalls
                                                        hSupports hProcs
                                                        hSourceReturns
                                                        hProgramWF
                                                        hProgramFrameSafe
                                                        (hInnerOwner.mono
                                                          (Nat.le_succ
                                                            recursiveFuel))
                                                        hHeadContract
                                              · intro headResult tailResult
                                                  tailInput
                                                  hHeadCompile hHeadBlocks
                                                  hHeadCalls hFallthrough
                                                  hTailCompile hTailBlocks
                                                  hWhole
                                                have wholeContract :
                                                    FragmentContract cfg
                                                      (headResult.append
                                                        tailResult)
                                                      ctx supply entry regular
                                                      input source tokens
                                                      policy := by
                                                  simpa [hWhole] using
                                                    contract
                                                have hTailShape :
                                                    TypedCfgPreservation.LabelShape
                                                      cfg
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      tailInput := by
                                                  exact
                                                    TypedCfgPreservation.LabelShape.of_compileStmtListFuel?
                                                      hTailCompile hTailBlocks
                                                have hHeadShapes :
                                                    BoundaryShapes cfg
                                                      headResult ctx
                                                      (TypedCfgCompiler.restLabel
                                                        supply) :=
                                                  wholeContract.shapes.with_regular
                                                    (by
                                                      intro shape hShape
                                                      have hShapeEq :
                                                          shape = tailInput :=
                                                        Option.some.inj
                                                          (hShape.symm.trans
                                                            hFallthrough)
                                                      subst shape
                                                      exact hTailShape)
                                                have hHeadContract :
                                                    StmtContract cfg headResult
                                                      ctx supply entry
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      input source tokens
                                                      (InteractionControlPreservation.OpenOutcome.pushStopJump
                                                        headResult ctx
                                                        (TypedCfgCompiler.restLabel
                                                          supply)
                                                        source.returns tokens
                                                        policy) :=
                                                  { fits := contract.fits
                                                    regularAt := Or.inr rfl
                                                    before :=
                                                      contract.before.nonregular
                                                    activation :=
                                                      wholeContract.activation
                                                    boundary :=
                                                      wholeContract.boundary.push_current
                                                        wholeContract.regularAt
                                                        wholeContract.before.nonregular
                                                        rfl hHeadShapes
                                                    shapes := hHeadShapes
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      exact
                                                        InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                                                          policy hRel
                                                    nonregular :=
                                                      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                                                        policy }
                                                cases innerFuel with
                                                | zero =>
                                                    exact
                                                      Stmt.exec_zero
                                                        hHeadCompile
                                                        hHeadBlocks hStmtWF
                                                        hSupports
                                                        hSourceReturns
                                                        hHeadContract
                                                | succ recursiveFuel =>
                                                    exact
                                                      Stmt.exec_succ
                                                        hHeadCompile
                                                        hHeadBlocks
                                                        hHeadCalls hStmtWF
                                                        hStmtSafe hStmtCalls
                                                        hSupports hProcs
                                                        hSourceReturns
                                                        hProgramWF
                                                        hProgramFrameSafe
                                                        (hInnerOwner.mono
                                                          (Nat.le_succ
                                                            recursiveFuel))
                                                        hHeadContract
                                              · intro headResult tailResult
                                                  tailInput middleSource
                                                  hHeadCompile hFallthrough
                                                  hTailCompile hTailBlocks
                                                  hTailCalls hReturns
                                                  hFrameFits hWhole
                                                have wholeContract :
                                                    FragmentContract cfg
                                                      (headResult.append
                                                        tailResult)
                                                      ctx supply entry regular
                                                      input source tokens
                                                      policy := by
                                                  simpa [hWhole] using
                                                    contract
                                                have hHeadNext :
                                                    supply + 1 ≤
                                                      headResult.next :=
                                                  TypedCfgCompilerFacts.Supply.stmt_next_ge_succ
                                                    hHeadCompile
                                                have hTailFits :
                                                    TypedCfgCompiler.Shape.SourceFrameFits
                                                      tailInput
                                                      middleSource.evm.stack.length := by
                                                  rcases hFrameFits with
                                                    ⟨shape, hShape, hFits⟩
                                                  have hShapeEq :
                                                      shape = tailInput :=
                                                    Option.some.inj
                                                      (hShape.symm.trans
                                                        hFallthrough)
                                                  subst shape
                                                  exact hFits
                                                have hTailShapes :
                                                    BoundaryShapes cfg
                                                      tailResult ctx regular :=
                                                  wholeContract.shapes.with_regular
                                                    (by
                                                      intro shape hShape
                                                      apply
                                                        wholeContract.shapes.regular
                                                      simp [
                                                        TypedCfgCompiler.Result.append,
                                                        hShape])
                                                have hTailContract :
                                                    FragmentContract cfg
                                                      tailResult ctx
                                                      headResult.next
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      regular tailInput
                                                      middleSource tokens
                                                      policy :=
                                                  { fits := hTailFits
                                                    regularAt :=
                                                      Or.inl
                                                        (contract.before.regular.mono
                                                          (Nat.le_trans
                                                            (Nat.le_succ
                                                              supply)
                                                            hHeadNext))
                                                    before :=
                                                      contract.before.mono
                                                        (Nat.le_trans
                                                          (Nat.le_succ
                                                            supply)
                                                          hHeadNext)
                                                    activation :=
                                                      contract.activation.stmtFallthrough
                                                        hHeadCompile
                                                        hFallthrough
                                                    boundary :=
                                                      (contract.boundary.mono
                                                        (Nat.le_trans
                                                          (Nat.le_succ
                                                            supply)
                                                          hHeadNext)).congr_returns
                                                        hReturns.symm
                                                    shapes := hTailShapes
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      apply
                                                        wholeContract.stops
                                                      have hRel' :
                                                          Rel tailResult ctx
                                                            regular
                                                            source.returns
                                                            tokens
                                                            sourceOutcome
                                                            targetOutcome := by
                                                        simpa [hReturns] using
                                                          hRel
                                                      exact
                                                        InteractionControlPreservation.OpenOutcome.Rel.append_right
                                                          hRel'
                                                    nonregular := by
                                                      intro childResult
                                                        childRegular
                                                        sourceOutcome
                                                        targetOutcome hMode
                                                        hRel
                                                      apply
                                                        contract.nonregular
                                                          hMode
                                                      simpa [hReturns] using
                                                        hRel }
                                                have hTailBlockCompile :
                                                    TypedCfgCompiler.compileBlockFuel?
                                                        (Nat.succ
                                                          (stmtCompilerFuel +
                                                            1))
                                                        { stmts := rest }
                                                        (ctx.advance
                                                          headResult)
                                                        headResult.next
                                                        (TypedCfgCompiler.restLabel
                                                          supply)
                                                        tailInput regular =
                                                      some tailResult := by
                                                  unfold
                                                    TypedCfgCompiler.compileBlockFuel?
                                                  exact hTailCompile
                                                apply
                                                  hInnerOwner
                                                    (blockSourceFuel :=
                                                      innerFuel)
                                                    (compilerFuel :=
                                                      Nat.succ
                                                        (stmtCompilerFuel + 1))
                                                    (block :=
                                                      { stmts := rest })
                                                    (ctx :=
                                                      ctx.advance headResult)
                                                    (supply :=
                                                      headResult.next)
                                                    (entry :=
                                                      TypedCfgCompiler.restLabel
                                                        supply)
                                                    (regular := regular)
                                                    (input := tailInput)
                                                    (result := tailResult)
                                                    (source := middleSource)
                                                    (tokens := tokens)
                                                    (policy := policy)
                                                    (canBreak := canBreak)
                                                    (canContinue :=
                                                      canContinue)
                                                    (canLeave := canLeave)
                                                    (Nat.le_refl innerFuel)
                                                    hTailBlockCompile
                                                    hTailBlocks hTailCalls
                                                    hRestWF hRestSafe
                                                    (.mk hRestCalls)
                                                    (CallBase.contextSupports
                                                      (ctx.callBase +
                                                        headResult.calls.length)
                                                      hSupports)
                                                    (by
                                                      simpa
                                                        [TypedCfgCompiler.Context.advance]
                                                        using hProcs)
                                                · intro hCanLeave
                                                  obtain
                                                      ⟨frame, remaining,
                                                        hSourceEq⟩ :=
                                                    hSourceReturns hCanLeave
                                                  exact
                                                    ⟨frame, remaining,
                                                      hReturns.trans
                                                        hSourceEq⟩
                                                · exact
                                                    CallBase.fragmentContract
                                                      (ctx.callBase +
                                                        headResult.calls.length)
                                                      hTailContract

namespace GeneratedProgram

def topPolicy
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (source : RunState) : StopPolicy :=
  InteractionControlPreservation.OpenOutcome.pushStopJump
    generated.main { procs := program.procs } ProcLabel.programEnd
    source.returns [] (fun _ _ => false)

theorem main_shapes
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg) :
    BoundaryShapes cfg generated.main
      { procs := program.procs } ProcLabel.programEnd := by
  exact
    { regular := by
        intro shape hShape
        simpa [hShape] using
          (TypedCfgPreservation.LabelShape.programEnd generated)
      break_ := by
        intro label shape hLabel _hShape
        simp at hLabel
      continue_ := by
        intro label shape hLabel _hShape
        simp at hLabel
      leave := by
        intro label shape hLabel _hShape
        simp at hLabel }

theorem main_exec
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    ExecPreservesUnder generated.main cfg
      TypedCfgCompiler.entryLabel
      { procs := program.procs }
      ProcLabel.programEnd source []
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)
      (topPolicy generated source) := by
  have hMainCompile :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel program.body + 1)
          program.body { procs := program.procs }
          0 TypedCfgCompiler.entryLabel TypedCfg.Shape.caller
          ProcLabel.programEnd =
        some generated.main := by
    simpa [TypedCfgCompiler.compileBlock?] using
      generated.mainCompile
  have hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        { procs := program.procs } false false false :=
    { breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by simp }
  have hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        { procs := program.procs } ProcLabel.programEnd 0 :=
    { regular := by trivial
      breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by simp }
  have hShapes := main_shapes generated
  have hBaseBoundary :
      RecursiveBoundary cfg source.returns []
        (fun _ _ => false) 0 ProcLabel.programEnd :=
    { ownership :=
        InteractionBoundaryPreservation.OpenOutcome.StopPolicy.ActivationProtected.empty
          cfg source.returns []
      fresh :=
        InteractionBoundaryPreservation.OpenOutcome.StopPolicy.ActivationFreshExcept.of_static
          (by
            intro scope tag target hScope hNe
            rfl) }
  have hBoundary :
      RecursiveBoundary cfg source.returns []
        (topPolicy generated source) 0 ProcLabel.programEnd := by
    simpa [topPolicy] using
      hBaseBoundary.push hShapes hBefore
  have hOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated :=
    block_owner generated hProgramWF hProgramFrameSafe sourceFuel
  apply
    hOwner
      (blockSourceFuel := sourceFuel)
      (compilerFuel := TypedCfgCompiler.blockFuel program.body + 1)
      (block := program.body)
      (ctx := { procs := program.procs })
      (supply := 0)
      (entry := TypedCfgCompiler.entryLabel)
      (regular := ProcLabel.programEnd)
      (input := TypedCfg.Shape.caller)
      (result := generated.main)
      (source := source)
      (tokens := [])
      (policy := topPolicy generated source)
      (canBreak := false)
      (canContinue := false)
      (canLeave := false)
      (Nat.le_refl sourceFuel)
      hMainCompile generated.mainBlocks generated.mainCalls
      hProgramWF.2.2.2.2 hProgramFrameSafe.2 hProgramWF.2.2.2.1
      hSupports rfl
  · intro hFalse
    cases hFalse
  · exact
      { fits := by
          simp [
            TypedCfgCompiler.Shape.SourceFrameFits,
            TypedCfgCompiler.Shape.sourceLength,
            TypedCfgCompiler.Shape.sourceView,
            TypedCfg.Shape.caller,
            TypedCfg.Shape.length,
            TypedCfg.Shape.returnTokenDepth?,
            TypedCfg.Shape.returnTokenDepthList?]
        regularAt := Or.inl (by trivial)
        before := hBefore
        activation := TypedCfgPreservation.ActivationInput.top _
        boundary := hBoundary
        shapes := hShapes
        stops := by
          intro sourceOutcome targetOutcome hRel
          exact
            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
              (fun _ _ => false) hRel
        nonregular :=
          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
            (fun _ _ => false) }

/--
Successful checked generation preserves the complete Structured main-block
execution. The compiler-owned recursive context is constructed internally
from the adjacent pass rather than accepted as a public premise.
-/
theorem generateWithProcEntryShapes?_main_exec
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? program entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    ∃ generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg,
      ExecPreservesUnder generated.main cfg
        TypedCfgCompiler.entryLabel
        { procs := program.procs }
        ProcLabel.programEnd source []
        (InteractionSemantics.Block.openRun
          program sourceFuel program.body source)
        (topPolicy generated source) := by
  let generated :=
    TypedCfgPreservation.Program.GeneratedContext.of_generate
      hGenerate hWellTyped
  exact
    ⟨generated,
      main_exec generated hProgramWF hProgramFrameSafe
        sourceFuel source⟩

end GeneratedProgram

end OpenOutcome

end InteractionOwnerPreservation
end Structured
end EvmCompiler
