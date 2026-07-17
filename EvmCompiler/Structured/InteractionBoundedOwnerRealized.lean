import EvmCompiler.Structured.InteractionBoundedOwnerPreservation
import EvmCompiler.Structured.InteractionEntryRealizedBounded

/-!
# Leaf realizing cases at the BOUNDED owner layer (Step A / item 3b, leaves)

This module lands the leaf `*_bounded_realizing` cases of the bounded realizing
family `RealizingBoundedExecPreservesUnder` (defined in
`InteractionEntryRealizedBounded.lean`).  They mirror the existing (green,
unchanged) leaf `*_bounded` theorems in `InteractionBoundedOwnerPreservation.lean`
(`code_bounded`/`terminal_bounded`/`brk_bounded`/`cont_bounded`/`leave_bounded`)
but produce the additive realizing family, whose second conjunct is the target-side
per-entry accumulator `∀ tf ≤ targetBudget, AllEntriesRealized …`.

Session 15 pinned the bounded owner layer (`InteractionBoundedOwnerPreservation`,
budget `InteractionStaticCost.blockBudget`/`stmtBudget`) as the exact mirror target
for the item-3b threading (NOT the plain `InteractionOwnerPreservation` `*_exec`
layer, whose `targetFuel` is existential).  These leaves are the base cases of that
mirror.

For a leaf, the compiled fragment is ONE block whose single `openStep` jumps
straight to a recursive boundary that the fragment's stop policy halts on, so the
open run visits **no** block entry beyond the start.  The accumulator therefore
reduces (`AllEntriesRealized.of_first_jump_stops` / `.of_zero`, via the helper
`allEntriesRealized_of_first_jump_stops` below) to the single fact
`realized entry target`, taken here as the hypothesis
`hEntry : ∀ target, StateRel source tokens target → realized entry target` — keeping
`realized` ABSTRACT exactly as `InteractionOwnerRealized.lean`'s forward leaves do.
The composite recursors (later) instantiate `realized` to the concrete
source-witness and discharge `hEntry` from the extracted child `StateRel`.

The `.bounded` (outcome) conjunct is the existing `*_bounded` theorem verbatim; the
stops argument for the accumulator is identical to the forward leaves in
`InteractionOwnerRealized.lean`.  Everything here is **additive** — no existing
statement is touched, `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionBoundedOwnerPreservation
namespace OpenOutcome

open InteractionControlPreservation.OpenOutcome (RealizingBoundedExecPreservesUnder)
open TypedCfg.InteractionSemantics.Program (AllEntriesRealized)

/--
Generic accumulator discharge for a single-block fragment.

When every concrete first-step jump out of the starting entry lands on a
policy-stopping target, the open run visits no entry beyond the start, so realizing
the start entry (`hHere`) realizes every entry at *any* fuel — folding
`AllEntriesRealized.of_zero` (fuel 0) and `AllEntriesRealized.of_first_jump_stops`
(fuel `n + 1`) into one `∀ fuel` fact.  This is the exact shape
`RealizingBoundedExecPreservesUnder.mk` consumes at the leaf budget.
-/
theorem allEntriesRealized_of_first_jump_stops
    {cfg : TypedCfg.Program} {policy : StopPolicy}
    {entry : Assembly.Label} {target : EVMState}
    {realized : Assembly.Label → EVMState → Prop}
    (hHere : realized entry target)
    (hStops :
      ∀ (transcript : Simulation.Interaction.Transcript)
        (next : Assembly.Label) (state' : EVMState),
        Simulation.Interaction.Executes
          (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
          transcript (Except.ok (TypedCfg.Outcome.jump next state')) →
        policy next state' = true) :
    ∀ fuel, AllEntriesRealized cfg policy fuel entry target realized := by
  intro fuel
  cases fuel with
  | zero => exact AllEntriesRealized.of_zero hHere
  | succ n => exact AllEntriesRealized.of_first_jump_stops hHere hStops

namespace Stmt

/-- Leaf realizing case for straight-line code (mirrors `code_bounded`). -/
theorem code_bounded_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.code code) source)
      (InteractionStaticCost.stmtBudget program sourceFuel (.code code))
      policy realized := by
  refine RealizingBoundedExecPreservesUnder.mk (code_bounded hCompile hBlocks contract) ?_
  intro target hStateRel
  refine allEntriesRealized_of_first_jump_stops (hEntry target hStateRel) ?_ _
  intro transcript next state' hExec
  obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right
      (InteractionControlPreservation.Stmt.openStep_code_of_compileStmtFuel?
        (sourceProgram := program) (sourceFuel := sourceFuel)
        hCompile hBlocks contract.fits hStateRel)
      hExec
  cases hDone with
  | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for a terminal (halt) fragment (mirrors `terminal_bounded`). -/
theorem terminal_bounded_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.terminal kind) source)
      (InteractionStaticCost.stmtBudget program sourceFuel (.terminal kind))
      policy realized := by
  refine RealizingBoundedExecPreservesUnder.mk (terminal_bounded hCompile hBlocks contract) ?_
  intro target hStateRel
  refine allEntriesRealized_of_first_jump_stops (hEntry target hStateRel) ?_ _
  intro transcript next state' hExec
  obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right
      (InteractionLeafPreservation.Stmt.openStep_terminal_of_compileStmtFuel?
        (sourceProgram := program) (sourceFuel := sourceFuel)
        hCompile hBlocks contract.fits hStateRel)
      hExec
  cases hDone with
  | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for `break` (mirrors `brk_bounded`). -/
theorem brk_bounded_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .brk)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .brk source)
      (InteractionStaticCost.stmtBudget program sourceFuel .brk)
      policy realized := by
  cases hWF with
  | brk hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.breakLabel hAllowed
      refine RealizingBoundedExecPreservesUnder.mk
        (brk_bounded hCompile hBlocks (.brk hAllowed) hSupports contract) ?_
      intro target hStateRel
      refine allEntriesRealized_of_first_jump_stops (hEntry target hStateRel) ?_ _
      intro transcript next state' hExec
      obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
        Simulation.Interaction.Rel.executes_right
          (InteractionLeafPreservation.Stmt.openStep_brk_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            hExit hCompile hBlocks contract.fits hStateRel)
          hExec
      cases hDone with
      | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for `continue` (mirrors `cont_bounded`). -/
theorem cont_bounded_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .cont)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .cont source)
      (InteractionStaticCost.stmtBudget program sourceFuel .cont)
      policy realized := by
  cases hWF with
  | cont hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.continueLabel hAllowed
      refine RealizingBoundedExecPreservesUnder.mk
        (cont_bounded hCompile hBlocks (.cont hAllowed) hSupports contract) ?_
      intro target hStateRel
      refine allEntriesRealized_of_first_jump_stops (hEntry target hStateRel) ?_ _
      intro transcript next state' hExec
      obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
        Simulation.Interaction.Rel.executes_right
          (InteractionLeafPreservation.Stmt.openStep_cont_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            hExit hCompile hBlocks contract.fits hStateRel)
          hExec
      cases hDone with
      | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for `leave` (mirrors `leave_bounded`). -/
theorem leave_bounded_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular = some result)
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
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .leave source)
      (InteractionStaticCost.stmtBudget program sourceFuel .leave)
      policy realized := by
  cases hWF with
  | leave hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.leaveLabel hAllowed
      obtain ⟨frame, rest, hReturns⟩ := hSourceReturns hAllowed
      refine RealizingBoundedExecPreservesUnder.mk
        (leave_bounded hCompile hBlocks (.leave hAllowed) hSupports hSourceReturns contract) ?_
      intro target hStateRel
      refine allEntriesRealized_of_first_jump_stops (hEntry target hStateRel) ?_ _
      intro transcript next state' hExec
      obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
        Simulation.Interaction.Rel.executes_right
          (InteractionLeafPreservation.Stmt.openStep_leave_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            hExit hReturns hCompile hBlocks contract.fits hStateRel)
          hExec
      cases hDone with
      | ok hRel => exact contract.stops hRel

end Stmt
end OpenOutcome
end InteractionBoundedOwnerPreservation
end Structured
end EvmCompiler
