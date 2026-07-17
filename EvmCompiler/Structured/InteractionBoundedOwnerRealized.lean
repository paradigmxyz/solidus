import EvmCompiler.Structured.InteractionBoundedOwnerPreservation
import EvmCompiler.Structured.InteractionEntryRealizedBounded
import EvmCompiler.Structured.InteractionBranchEntryRealized
import EvmCompiler.Structured.InteractionCallEntryRealized

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

/--
Accumulator-threading step for a `jumpi`-branch composite entry (`if` and, via the
shared `InteractionBranchPreservation.Condition.DoneRel`, `for`'s loop-condition
block).

This packages the `AllEntriesRealized.of_succ` recursion for one composite whose
first `openStep` is a two-way branch related to the source condition run by the
branch `DoneRel`.  It consumes the branch relation **strengthened with the
source-condition returns invariant** (`Rel.strengthen_left` +
`openRunCondition_returns`), so that both branches recover
`afterCond.returns = sourceReturns` — the fact the child body `FragmentContract`
reconstruction requires.  It consumes:
* `hHere` — the entry is realized (entry witness);
* `hStrong` — the returns-strengthened branch relation;
* `hFalseStops` — for the false/exit label the fragment's stop policy halts,
  proved **from the extracted child `StateRel`/returns/`SourceFrameFits`** (the
  fragment's `contract.stops` on the reconstructed regular-exit `Rel`), which
  rules out the non-body branch under `of_succ`'s non-stopping hypothesis.  NOTE:
  this is a **conditional** stop obligation — the unconditional
  `∀ state', policy falseLabel state' = true` form used in the session-16 draft is
  *not* dischargeable, since `policy` is arbitrary and only stops for
  frame-matching states;
* `hBody` — for the taken (true/body) branch, the child fragment realizes every
  entry of its `bodyBudget`-fuel run from the extracted child `StateRel` /
  `SourceFrameFits` / returns (supplied by the child's `RealizingBlockOwnerAt`).

The residual budget is exactly `bodyBudget`, matching
`stmtBudget (.if_ cond body) = 1 + blockBudget body` (`stmtBudget_if_succ`), so no
upward-monotone accumulator step is needed.
-/
theorem allEntriesRealized_branch_step
    {cfg : TypedCfg.Program} {policy : StopPolicy}
    {entry trueLabel falseLabel : Assembly.Label} {target : EVMState}
    {tokens : List Word} {sourceReturns : List ReturnDest}
    {restShape : TypedCfg.Shape}
    {srcRun : Simulation.Interaction EVMException (RunState × Bool)}
    {bodyBudget : Nat}
    {realized : Assembly.Label → EVMState → Prop}
    (hHere : realized entry target)
    (hStrong :
      Simulation.Interaction.Rel
        (fun leftDone rightDone =>
          InteractionBranchPreservation.Condition.DoneRel
              trueLabel falseLabel tokens restShape leftDone rightDone ∧
            InteractionSemantics.Code.ConditionReturnsEq sourceReturns leftDone)
        srcRun
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target))
    (hFalseStops :
      ∀ (afterCond : RunState) (state' : EVMState),
        afterCond.returns = sourceReturns →
        TypedCfgPreservation.StateRel afterCond tokens state' →
        TypedCfgCompiler.Shape.SourceFrameFits
          restShape afterCond.evm.stack.length →
        policy falseLabel state' = true)
    (hBody :
      ∀ (afterCond : RunState) (state' : EVMState),
        afterCond.returns = sourceReturns →
        TypedCfgPreservation.StateRel afterCond tokens state' →
        TypedCfgCompiler.Shape.SourceFrameFits
          restShape afterCond.evm.stack.length →
        AllEntriesRealized cfg policy bodyBudget trueLabel state' realized) :
    AllEntriesRealized cfg policy (bodyBudget + 1) entry target realized := by
  refine AllEntriesRealized.of_succ hHere ?_
  intro transcript next state' hExec hStop
  obtain ⟨leftOutcome, _hLeftExec, hStrongDone⟩ :=
    Simulation.Interaction.Rel.executes_right hStrong hExec
  cases leftOutcome with
  | error e =>
      obtain ⟨hDone, _⟩ := hStrongDone
      cases hDone
  | ok conditionResult =>
      obtain ⟨hDone, hRet⟩ := hStrongDone
      cases hDone with
      | ok hResultRel =>
          obtain ⟨targetState, hEq, hAfterCondRel, hAfterCondFits⟩ := hResultRel
          rcases conditionResult with ⟨afterCond, cond⟩
          have hReturns : afterCond.returns = sourceReturns := by
            simpa [InteractionSemantics.Code.ConditionReturnsEq] using hRet
          injection hEq with hNext hState
          cases cond with
          | false =>
              simp only [Bool.false_eq_true, if_false] at hNext
              rw [hNext, hState,
                hFalseStops afterCond targetState hReturns hAfterCondRel
                  hAfterCondFits] at hStop
              exact absurd hStop (by decide)
          | true =>
              simp only [if_true] at hNext
              rw [hNext, hState]
              exact
                hBody afterCond targetState hReturns hAfterCondRel hAfterCondFits

/--
Accumulator-threading step for a `pure`-jump composite entry (`switch`'s silent
`pop;jump`/test blocks and `call`'s silent call-site block).

Packages the `AllEntriesRealized.of_succ` recursion for a composite whose first
`openStep` reduces to a concrete `pure (.jump childLabel childState)` (as
`openStep_pop_jump`/`openStep_test`/`openStep_entry_of_compileStmtFuel?` establish).
The child label/`StateRel` are read off the concrete `Executes` through the landed
`jump_state_rel_of_pure` (no backward simulation, and no branch to rule out — the
single jump is non-stopping).  `hChild` supplies the child fragment's realization
of its `childBudget`-fuel run at the extracted `StateRel`.
-/
theorem allEntriesRealized_pure_step
    {cfg : TypedCfg.Program} {policy : StopPolicy}
    {entry childLabel : Assembly.Label} {target childState : EVMState}
    {childSource : RunState} {childTokens : List Word}
    {childBudget : Nat}
    {realized : Assembly.Label → EVMState → Prop}
    (hHere : realized entry target)
    (hStep :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump childLabel childState))
    (hChildRel :
      TypedCfgPreservation.StateRel childSource childTokens childState)
    (hChild :
      ∀ state',
        TypedCfgPreservation.StateRel childSource childTokens state' →
        AllEntriesRealized cfg policy childBudget childLabel state' realized) :
    AllEntriesRealized cfg policy (childBudget + 1) entry target realized := by
  refine AllEntriesRealized.of_succ hHere ?_
  intro transcript next state' hExec hStop
  obtain ⟨hNext, hRel'⟩ :=
    InteractionCallPreservation.Call.jump_state_rel_of_pure hStep hChildRel hExec
  subst hNext
  exact hChild state' hRel'

namespace Stmt

/--
Composite realizing recursor for `if`.

`.bounded` conjunct is the existing green `if_bounded` (fed the realizing owner's
forgetful `.owner` projection); `.allEntriesRealized` conjunct threads the
target-side per-entry accumulator through the `if`-head's first `openStep`
(`AllEntriesRealized.of_succ`).  The child (body) branch discharges its residual
`AllEntriesRealized` by invoking the realizing block owner at the extracted child
`StateRel`; the false/regular branch is ruled out because the fragment's stop
policy halts there (`contract.stops` on the reconstructed regular-exit `Rel`),
contradicting `of_succ`'s non-stopping hypothesis.

The entry witness and body `FragmentContract` are reconstructed here additively
(mirroring the plumbing inside `if_bounded` / `openRun_if_bounded_under_of_compileStmtFuel?`);
the returns equality `afterCond.returns = source.returns` is threaded via
`Rel.strengthen_left` + `openRunCondition_returns`, as the underlying preservation
does.
-/
theorem if_bounded_realizing
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
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave (.if_ cond body))
    (hFrameSafe : Structured.Stmt.FrameSafe (.if_ cond body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs (.if_ cond body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true →
        ∃ frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      RealizingBlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.if_ cond body) source)
      (InteractionStaticCost.stmtBudget
        program (sourceFuel + 1) (.if_ cond body))
      policy (realizedWitness cfg) := by
  -- Body-local well-formedness facts (extracted without consuming the whole hyps,
  -- which `if_bounded` still needs).
  have hBodyWF : Structured.Block.WF canBreak canContinue canLeave body := by
    cases hWF with | if_ h => exact h
  have hBodySafe : body.FrameSafe := by
    cases hFrameSafe with | if_ _ h => exact h
  have hBodyCallsResolved :
      Structured.ProcList.BlockCallsResolved program.procs body := by
    cases hCalls with | if_ h => exact h
  refine RealizingBoundedExecPreservesUnder.mk
    (if_bounded hCompile hBlocks hResultCalls hWF hFrameSafe hCalls hSupports
      hProcs hSourceReturns hBlockOwner.owner contract) ?_
  intro target hStateRel
  -- Rewrite the budget so the head's single `openStep` fits `of_succ`.
  have hBudgetEq :
      InteractionStaticCost.stmtBudget program (sourceFuel + 1) (.if_ cond body) =
        InteractionStaticCost.blockBudget program sourceFuel body + 1 := by
    rw [InteractionStaticCost.stmtBudget_if_succ]; omega
  rw [hBudgetEq]
  -- Reconstruct the compiler-owned entry block and body compile facts.
  obtain
      ⟨output, _condition, bodyResult,
        hType, hSource, _hHead, hBodyCompile,
        hBodyRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
  set bodyInput : TypedCfg.Shape :=
    { output with slots := output.slots.tail } with hBodyInput
  have hFallthrough : result.fallthrough? = some bodyInput := by
    simp [bodyInput, hResult]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hResult, hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram bodyResult generated.calls := by
    intro site hMem
    apply hResultCalls site
    simp [hResult, hMem]
  set entryBlock : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term := .jumpi (LabelSupply.label supply 0) regular } with hEntryBlock
  have hFind : cfg.findBlock? entry = some entryBlock := by
    exact hBlocks entryBlock (by simp [entryBlock, hResult])
  have hHeadRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens bodyInput)
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa [entryBlock, bodyInput] using
      (InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := entry)
        (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular)
        hType hSource contract.fits hStateRel)
  have hHeadWithReturns :=
    Simulation.Interaction.Rel.strengthen_left hHeadRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  -- Accumulator via the corrected branch step (entry witness + returns-strengthened
  -- head relation + conditional false-branch stopping + child-body realization).
  refine allEntriesRealized_branch_step
    ⟨source, tokens, entryBlock, hFind, hStateRel, contract.fits⟩
    hHeadWithReturns ?_ ?_
  · -- False/regular branch stops: reconstruct the regular-exit `Rel`, apply
    -- `contract.stops` (the fragment halts at its boundary `regular`).
    intro afterCond state' hReturns hAfterCondRel hAfterCondFits
    have hWholeRel :
        InteractionControlPreservation.OpenOutcome.Rel
          result ctx regular source.returns tokens
          (Structured.Outcome.regular afterCond)
          (.jump regular state') := by
      refine ⟨?_, ?_, ?_⟩
      · exact
          TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
            ⟨rfl, hAfterCondRel⟩
      · exact ⟨bodyInput, hFallthrough, hAfterCondFits⟩
      · simpa [
          InteractionControlPreservation.OpenOutcome.ActivationRestored]
          using hReturns
    have hStops := contract.stops hWholeRel
    simpa only [
      InteractionControlPreservation.OpenOutcome.TargetStoppedBy]
      using hStops
  · -- Body branch: invoke the realizing block owner at the extracted child
    -- `StateRel`, reconstructing the body `FragmentContract`.
    intro afterCond state' hReturns hAfterCondRel hAfterCondFits
    have hBodyReturns :
        canLeave = true →
          ∃ frame rest, afterCond.returns = frame :: rest := by
      intro hCanLeave
      obtain ⟨frame, rest, hSourceEq⟩ := hSourceReturns hCanLeave
      exact ⟨frame, rest, hReturns.trans hSourceEq⟩
    have bodyContract :
        FragmentContract cfg bodyResult ctx (supply + 1)
          (LabelSupply.label supply 0) regular bodyInput
          afterCond tokens policy :=
      { fits := hAfterCondFits
        regularAt := Or.inl contract.before_succ.regular
        before := contract.before_succ
        activation :=
          contract.activation.stmtFallthrough
            hCompile hFallthrough
        boundary :=
          (contract.boundary.mono
            (Nat.le_succ supply)).congr_returns hReturns.symm
        shapes :=
          contract.shapes.of_required_fallthrough
            hBodyRequire hFallthrough
        stops := by
          intro sourceOutcome targetOutcome hRel
          apply contract.stops
          have hWhole :=
            InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
              hBodyRequire hFallthrough hRel
          simpa [hReturns] using hWhole
        nonregular := by
          intro childResult childRegular sourceOutcome
            targetOutcome hMode hRel
          apply contract.nonregular hMode
          simpa [hReturns] using hRel }
    exact
      (hBlockOwner (Nat.le_refl sourceFuel)
          hBodyCompile hBodyBlocks hBodyCalls
          hBodyWF hBodySafe hBodyCallsResolved hSupports hProcs
          hBodyReturns bodyContract).allEntriesRealized
        hAfterCondRel (Nat.le_refl _)

end Stmt

end OpenOutcome
end InteractionBoundedOwnerPreservation
end Structured
end EvmCompiler
