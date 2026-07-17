import EvmCompiler.Structured.InteractionEntryRealizedForward
import EvmCompiler.Structured.InteractionOwnerPreservation
import EvmCompiler.Structured.InteractionBoundedOwnerRealized

/-!
# The per-outcome existential-fuel realizing family (Step A, route C — session 23)

This module is the **route-C correction** of the realizing preservation family
(see `TypedCfg/PEEPHOLE_PROGRESS.md`, session-23 route decision).

Sessions 12-17 attached the per-entry realization accumulator at a **static**
`targetBudget` (`RealizingBoundedExecPreservesUnder`,
`InteractionEntryRealizedBounded.lean`).  That static budget
(`stmtBudget`/`blockBudget`, `InteractionStaticCost.lean`) is a fuel-indexed
over-approximation, so on source-`OutOfFuel` (truncation) branches the accumulator
`AllEntriesRealized … targetBudget …` quantifies over entries the actual run never
settles into — entries with no source `StateRel` witness.  That is precisely the
session-22 obstruction 3 that walled `switch`/`call`/`for`.

`ExecPreservesUnder` (`InteractionControlPreservation.lean:936`) instead binds the
target fuel **existentially per `(transcript, sourceOutcome)`**, and the run at
that fuel produces `.stopped` — the ACTUAL settling fuel, never `.exhausted`.
Attaching `AllEntriesRealized` under that SAME existential `targetFuel`
(`RealizingExecPreservesUnder` below) means the accumulator only ever quantifies
over entries of the settled run, all of which the source simulation covers.  There
is no static over-approximation, hence no witnessless entry, hence obstruction 3
does not arise.

This file lands the family, its projections, the generic single-block constructor
`of_exec_first_jump_stops`, and the five single-block leaf cases
(`code`/`terminal`/`brk`/`cont`/`leave`), mirroring the forward leaves in
`InteractionOwnerRealized.lean` but on the existential-fuel `*_exec` outcome leg.
Everything is **additive**: no existing statement is touched; the existing
`*_exec` (producing `ExecPreservesUnder`) and the forward realizing family sit
beside these.

`realized` stays abstract (the source-witness instantiation is a spine-level
concern, exactly as in `InteractionEntryRealized`).
-/

namespace EvmCompiler
namespace Structured
namespace InteractionControlPreservation
namespace OpenOutcome

open TypedCfg.InteractionSemantics.Program (AllEntriesRealized)

/--
The per-outcome existential-fuel realizing family.

For every `StateRel`-related target and every successful source outcome, the
canonical open runner reaches a matching stopped outcome at some `targetFuel`
(this is exactly `ExecPreservesUnder`), AND — under that SAME existential
`targetFuel` — every block entry the `targetFuel`-fuel run visits satisfies the
abstract per-entry predicate `realized`.

Because the accumulator rides the ACTUAL settling fuel (the run at `targetFuel`
produces `.stopped`, never `.exhausted`), it never quantifies over the
over-approximated post-settlement entries that killed the static-budget family on
truncation branches.
-/
def RealizingExecPreservesUnder
    (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (policy : StopPolicy)
    (realized : Assembly.Label → EVMState → Prop) : Prop :=
  ∀ target,
    TypedCfgPreservation.StateRel source tokens target →
      ∀ transcript sourceOutcome,
        Simulation.Interaction.Executes
            sourceRun transcript (.ok sourceOutcome) →
          ∃ targetFuel remaining targetOutcome,
            Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                  policy cfg targetFuel entry target)
                transcript
                (.ok (.stopped remaining targetOutcome)) ∧
              Rel result ctx regular source.returns tokens
                sourceOutcome targetOutcome ∧
              AllEntriesRealized cfg policy targetFuel entry target realized

namespace RealizingExecPreservesUnder

variable
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}

/-- The execution outcome leg (forget the accumulator), recovering the existing
pass-wide `ExecPreservesUnder` interface.  This is how a realizing composite feeds
the unchanged spine while retaining its accumulator for the peephole leg. -/
theorem exec
    (h :
      RealizingExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun policy realized) :
    ExecPreservesUnder result cfg entry ctx regular source tokens sourceRun policy := by
  intro target hStateRel transcript sourceOutcome hExec
  obtain ⟨targetFuel, remaining, targetOutcome, hRun, hRel, _⟩ :=
    h target hStateRel transcript sourceOutcome hExec
  exact ⟨targetFuel, remaining, targetOutcome, hRun, hRel⟩

/--
Derive the per-outcome existential-fuel realizing family from the **bounded**
realizing family.

Whenever a fragment's bounded realizing family closes at a *static* budget
(`RealizingBoundedExecPreservesUnder … targetBudget …`), its exec-level realizing
family follows with no extra reachability argument:

* the bounded outcome leg (`BoundedExecPreservesUnder`) supplies, for each
  successful source outcome, a *settling* `targetFuel ≤ targetBudget` (the run at
  it produces `.stopped`);
* the bounded accumulator, specialized to that very `targetFuel` (which is
  `≤ targetBudget`), supplies `AllEntriesRealized cfg policy targetFuel …` — exactly
  the conjunct the exec family attaches under its existential `targetFuel`.

This is the clean landing for every composite whose *bounded* family already
closes.  It applies to `if` (`if_bounded_realizing`, session 17, whose
`stmtBudget = 1 + blockBudget body` matches its child exactly).  It does **not**
help `switch`/`call`/`for`, whose bounded families do not close (their static
`stmtBudget` carries strict slack, quantifying the accumulator over witnessless
truncation-branch entries — the session-22 obstruction 3); those must build the
exec family directly at the settling fuel.
-/
theorem of_bounded
    {targetBudget : Nat}
    (h :
      RealizingBoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy realized) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun policy realized := by
  intro target hStateRel transcript sourceOutcome hExec
  obtain ⟨targetFuel, remaining, targetOutcome, hLe, hRun, hRel⟩ :=
    h.bounded target hStateRel transcript sourceOutcome hExec
  exact
    ⟨targetFuel, remaining, targetOutcome, hRun, hRel,
      h.allEntriesRealized hStateRel hLe⟩

/--
Generic single-block leaf constructor.

Given
* the existential-fuel execution outcome leg (`ExecPreservesUnder`),
* the start-entry realization (`realized entry target` for every related target),
* and that every concrete first-step jump out of the entry lands on a
  policy-stopping target,

the realizing family holds.  For each successful outcome the outcome leg supplies
the settling `targetFuel` (with a `.stopped` result, so `targetFuel ≥ 1`); the run
visits no entry beyond the start (every first jump stops), so the accumulator
reduces to the single start-entry fact via
`AllEntriesRealized.of_first_jump_stops` at that fuel.

This is the exact discharge shape for the leaf `code`/`terminal`/`brk`/`cont`/
`leave` realizing cases — each compiles to one block whose terminator is a `.jump`
the fragment's stop policy halts on.
-/
theorem of_exec_first_jump_stops
    (hExec :
      ExecPreservesUnder result cfg entry ctx regular source tokens sourceRun policy)
    (hRealized :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target)
    (hStops :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          ∀ transcript next state',
            Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.openStep
                  cfg entry target)
                transcript
                (Except.ok (TypedCfg.Outcome.jump next state')) →
              policy next state' = true) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun policy realized := by
  intro target hStateRel transcript sourceOutcome hExecSource
  obtain ⟨targetFuel, remaining, targetOutcome, hRun, hRel⟩ :=
    hExec target hStateRel transcript sourceOutcome hExecSource
  refine ⟨targetFuel, remaining, targetOutcome, hRun, hRel, ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, targetFuel = f + 1 := by
    cases targetFuel with
    | zero =>
        rw [TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_zero]
          at hRun
        cases hRun
    | succ f => exact ⟨f, rfl⟩
  exact
    AllEntriesRealized.of_first_jump_stops
      (hRealized target hStateRel)
      (fun transcript next state' hExec =>
        hStops target hStateRel transcript next state' hExec)

end RealizingExecPreservesUnder

/--
Leaf realizing case for straight-line code, at the existential-fuel exec level.

Mirrors `code_forward_realizing` but on the `code_exec` outcome leg: the compiled
code block's single `openStep` (backward-simulated via
`openStep_code_of_compileStmtFuel?` + `Rel.executes_right`) only reaches
policy-stopping jumps (`contract.stops`), so the accumulator collapses to the
start entry at whatever fuel `code_exec` settles at.
-/
theorem code_exec_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      InteractionOwnerPreservation.OpenOutcome.StmtContract
        cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.code code) source)
      policy realized := by
  refine
    RealizingExecPreservesUnder.of_exec_first_jump_stops
      (InteractionOwnerPreservation.OpenOutcome.Stmt.code_exec
        (program := program) (sourceFuel := sourceFuel)
        hCompile hBlocks contract)
      hEntry ?_
  intro target hStateRel transcript next state' hExec
  obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right
      (InteractionControlPreservation.Stmt.openStep_code_of_compileStmtFuel?
        (sourceProgram := program) (sourceFuel := sourceFuel)
        hCompile hBlocks contract.fits hStateRel)
      hExec
  cases hDone with
  | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for a terminal (halt) fragment, exec level. -/
theorem terminal_exec_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      InteractionOwnerPreservation.OpenOutcome.StmtContract
        cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.terminal kind) source)
      policy realized := by
  refine
    RealizingExecPreservesUnder.of_exec_first_jump_stops
      (InteractionOwnerPreservation.OpenOutcome.Stmt.terminal_exec
        (program := program) (sourceFuel := sourceFuel)
        hCompile hBlocks contract)
      hEntry ?_
  intro target hStateRel transcript next state' hExec
  obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right
      (InteractionLeafPreservation.Stmt.openStep_terminal_of_compileStmtFuel?
        (sourceProgram := program) (sourceFuel := sourceFuel)
        hCompile hBlocks contract.fits hStateRel)
      hExec
  cases hDone with
  | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for `break`, exec level. -/
theorem brk_exec_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    {realized : Assembly.Label → EVMState → Prop}
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
      InteractionOwnerPreservation.OpenOutcome.StmtContract
        cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .brk source)
      policy realized := by
  refine
    RealizingExecPreservesUnder.of_exec_first_jump_stops
      (InteractionOwnerPreservation.OpenOutcome.Stmt.brk_exec
        (program := program) (sourceFuel := sourceFuel)
        hCompile hBlocks hWF hSupports contract)
      hEntry ?_
  intro target hStateRel transcript next state' hExec
  cases hWF with
  | brk hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.breakLabel hAllowed
      obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
        Simulation.Interaction.Rel.executes_right
          (InteractionLeafPreservation.Stmt.openStep_brk_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            hExit hCompile hBlocks contract.fits hStateRel)
          hExec
      cases hDone with
      | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for `continue`, exec level. -/
theorem cont_exec_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    {realized : Assembly.Label → EVMState → Prop}
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
      InteractionOwnerPreservation.OpenOutcome.StmtContract
        cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .cont source)
      policy realized := by
  refine
    RealizingExecPreservesUnder.of_exec_first_jump_stops
      (InteractionOwnerPreservation.OpenOutcome.Stmt.cont_exec
        (program := program) (sourceFuel := sourceFuel)
        hCompile hBlocks hWF hSupports contract)
      hEntry ?_
  intro target hStateRel transcript next state' hExec
  cases hWF with
  | cont hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.continueLabel hAllowed
      obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
        Simulation.Interaction.Rel.executes_right
          (InteractionLeafPreservation.Stmt.openStep_cont_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            hExit hCompile hBlocks contract.fits hStateRel)
          hExec
      cases hDone with
      | ok hRel => exact contract.stops hRel

/-- Leaf realizing case for `leave`, exec level.  Also consumes the live-frame
witness `hSourceReturns`. -/
theorem leave_exec_realizing
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    {realized : Assembly.Label → EVMState → Prop}
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
      InteractionOwnerPreservation.OpenOutcome.StmtContract
        cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .leave source)
      policy realized := by
  refine
    RealizingExecPreservesUnder.of_exec_first_jump_stops
      (InteractionOwnerPreservation.OpenOutcome.Stmt.leave_exec
        (program := program) (sourceFuel := sourceFuel)
        hCompile hBlocks hWF hSupports hSourceReturns contract)
      hEntry ?_
  intro target hStateRel transcript next state' hExec
  cases hWF with
  | leave hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.leaveLabel hAllowed
      obtain ⟨frame, rest, hReturns⟩ := hSourceReturns hAllowed
      obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
        Simulation.Interaction.Rel.executes_right
          (InteractionLeafPreservation.Stmt.openStep_leave_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            hExit hReturns hCompile hBlocks contract.fits hStateRel)
          hExec
      cases hDone with
      | ok hRel => exact contract.stops hRel

/--
Composite realizing recursor for `if`, at the existential-fuel exec level.

The `if` fragment's *bounded* realizing family already closes at its static budget
(`InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.if_bounded_realizing`,
session 17 — `stmtBudget (.if_ cond body) = 1 + blockBudget body`, an exact child
match with no slack).  So the exec-level family follows directly by
`RealizingExecPreservesUnder.of_bounded`: the bounded outcome leg supplies a
settling `targetFuel ≤ stmtBudget`, and the bounded accumulator specialized to
that same `targetFuel` supplies `AllEntriesRealized` under the exec family's
existential fuel.  No separate reachability argument is needed (contrast
`switch`/`call`/`for`, whose bounded families do NOT close — see
`TypedCfg/PEEPHOLE_PROGRESS.md`, session-24).
-/
theorem if_exec_realizing
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
      InteractionBoundedOwnerPreservation.OpenOutcome.RealizingBlockOwnerAt
        sourceFuel program entryShapes cfg generated)
    (contract :
      InteractionOwnerPreservation.OpenOutcome.StmtContract
        cfg result ctx supply entry regular input source tokens policy) :
    RealizingExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.if_ cond body) source)
      policy
      (InteractionBoundedOwnerPreservation.OpenOutcome.realizedWitness cfg) :=
  RealizingExecPreservesUnder.of_bounded
    (InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.if_bounded_realizing
      hCompile hBlocks hResultCalls hWF hFrameSafe hCalls hSupports hProcs
      hSourceReturns hBlockOwner contract)

end OpenOutcome
end InteractionControlPreservation
end Structured
end EvmCompiler
