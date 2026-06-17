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
  ∀ {compilerFuel : Nat} {block : Structured.Block}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result}
      {source : RunState} {tokens : List Word}
      {policy : StopPolicy}
      {canBreak canContinue canLeave : Bool},
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
        program sourceFuel block source)
      policy

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
      FragmentContract cfg result ctx supply entry regular input
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
      FragmentContract cfg result ctx supply entry regular input
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
                hBlockOwner hBodyCompile hBodyBlocks hBodyCalls
                  hBodyWF hBodySafe hBodyCallsResolved hSupports hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt :=
                      Or.inl contract.regularAt.before_succ
                    before :=
                      contract.before.mono (Nat.le_succ supply)
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
      FragmentContract cfg result ctx supply entry regular input
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
      FragmentContract cfg result ctx supply entry regular input
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
      FragmentContract cfg result ctx supply entry regular input
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
      FragmentContract cfg result ctx supply entry regular input
        source tokens policy) :
    ExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.terminal kind) source)
      policy :=
  InteractionControlPreservation.OpenOutcome.PreservesUnder.exec
    (InteractionLeafPreservation.Stmt.openRun_terminal_under_of_compileStmtFuel?
      (regularExit := .stop)
      hCompile hBlocks contract.fits contract.nonregular)

end Stmt

end OpenOutcome

end InteractionOwnerPreservation
end Structured
end EvmCompiler
