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

/--
The source-realization witness `realized` predicate pinned in the session-15
recipe.  A target block entry `(label, state)` is *realized* when it is the entry
of a compiled cfg block whose source shape is inhabited by a source `StateRel`
witness at the entry stack depth.

This is the concrete instantiation the composite recursors require (per sessions
14/15: at composites `realized` must be the source witness, since the child entry
realization is discharged from the *extracted* child `StateRel`; the abstract
pass-through only survives at the leaves).  Downstream (Step B), the swap depth
guard `TypedCfg.StackRealizes block.input state` is produced from this witness by
`stackRealizes_of_stateRel_of_{returnTokenDepth?_eq_none,token_last_of_tokens_cons}`
(sessions 8/9), which consume exactly `SourceFrameFits block.input
source.evm.stack.length`.
-/
def realizedWitness (cfg : TypedCfg.Program) :
    Assembly.Label → EVMState → Prop :=
  fun label state =>
    ∃ (source : RunState) (tokens : List Word) (block : TypedCfg.Block),
      cfg.findBlock? label = some block ∧
      TypedCfgPreservation.StateRel source tokens state ∧
      TypedCfgCompiler.Shape.SourceFrameFits block.input source.evm.stack.length

/--
Realizing counterpart of `BlockOwnerAt`: the source-budgeted recursive block
capability, strengthened so every recursively executed block additionally yields
the target-side per-entry accumulator at the concrete source witness
`realizedWitness cfg`.

This is the mutual-recursion anchor for the item-3b threading.  The composite
`*_bounded_realizing` recursors consume this at strictly-smaller fuel for the child
fragment; `block_owner_realizing` will produce it by the same
`Nat.strong_induction_on sourceFuel` as the existing `block_owner`.
-/
def RealizingBlockOwnerAt
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
        supply entry input regular = some result →
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
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        program blockSourceFuel block source)
      (InteractionStaticCost.blockBudget
        program blockSourceFuel block)
      policy (realizedWitness cfg)

/-- The realizing owner forgets its accumulator to recover the existing
`BlockOwnerAt` (each recursively executed block's outcome leg via
`RealizingBoundedExecPreservesUnder.bounded`).  This lets a realizing composite
feed the unchanged bounded spine while retaining the accumulator. -/
theorem RealizingBlockOwnerAt.owner
    {sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    (h : RealizingBlockOwnerAt sourceFuel program entryShapes cfg generated) :
    BlockOwnerAt sourceFuel program entryShapes cfg generated := by
  intro blockSourceFuel compilerFuel block ctx supply entry regular input
    result source tokens policy canBreak canContinue canLeave
    hLe hCompile hBlocks hCalls hWF hFrameSafe hResolved hSupports hProcs
    hReturns contract
  exact
    (h hLe hCompile hBlocks hCalls hWF hFrameSafe hResolved hSupports hProcs
        hReturns contract).bounded

/-- Lower the realizing owner's source-fuel ceiling (mirrors `BlockOwnerAt.mono`). -/
theorem RealizingBlockOwnerAt.mono
    {smaller larger : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    (hOwner : RealizingBlockOwnerAt larger program entryShapes cfg generated)
    (hLe : smaller ≤ larger) :
    RealizingBlockOwnerAt smaller program entryShapes cfg generated := by
  intro blockSourceFuel compilerFuel block ctx supply entry regular input
    result source tokens policy canBreak canContinue canLeave hBlockLe
  exact hOwner (Nat.le_trans hBlockLe hLe)

end OpenOutcome
end InteractionBoundedOwnerPreservation
end Structured
end EvmCompiler
