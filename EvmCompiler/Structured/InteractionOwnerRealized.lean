import EvmCompiler.Structured.InteractionEntryRealizedForward
import EvmCompiler.Structured.InteractionOwnerPreservation

/-!
# Leaf realizing cases (Step A / item 2, leaves)

The leaf `*_forward_realizing` cases of the additive realizing family
(`RealizingForwardPreservesUnder`, defined in
`InteractionEntryRealizedForward.lean`).  Per the session-11/12 recipe these are
now one application of the generic single-block constructor
`RealizingForwardPreservesUnder.of_forward_first_jump_stops`:

* the forward outcome leg reuses the EXISTING (green) single-`targetFuel`
  `PreservesUnder … 1 policy` leaf (`openRun_code_under_of_compileStmtFuel?` /
  `openRun_terminal_under_of_compileStmtFuel?`), weakened to `ForwardPreservesUnder`
  via `ForwardRel.ofRel`;
* the per-entry accumulator is discharged by `of_first_jump_stops`: a `code` /
  `terminal` fragment compiles to ONE block whose `openStep` (characterized by the
  existing `openStep_*_of_compileStmtFuel?` relation) relates the source to the
  target; any first-step jump therefore backward-simulates
  (`Rel.executes_right`) to a related source outcome, and the fragment contract's
  `stops` field forces that target jump to be policy-stopping.  So the run visits
  no entry beyond the start.

The per-entry realization at the START entry (`realized entry target`) is taken as
a hypothesis `hEntry` (relayed by the enclosing recursion), keeping `realized`
abstract at this layer exactly as `InteractionEntryRealized` intends — the source
witness instantiation is supplied one layer up.

These leaves modify no existing statement; the existing `code_exec` / `terminal_exec`
(producing `ExecPreservesUnder`) are untouched and sit beside these.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionOwnerPreservation
namespace OpenOutcome

open InteractionControlPreservation.OpenOutcome (RealizingForwardPreservesUnder)

/--
Leaf realizing case for straight-line code.

Mirrors `code_exec` but concludes at the single-`targetFuel = 1` realizing forward
level.  The forward outcome leg is the existing `PreservesUnder … 1` code leaf
weakened by `ForwardRel.ofRel`; the accumulator is discharged because the compiled
code block's single `openStep` only reaches policy-stopping jumps
(`contract.stops` via the backward simulation of `openStep_code_of_compileStmtFuel?`).
-/
theorem code_forward_realizing
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
      StmtContract cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingForwardPreservesUnder result cfg entry ctx regular .stop
      source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.code code) source)
      1 policy realized := by
  have hPreserves :=
    InteractionControlPreservation.Stmt.openRun_code_under_of_compileStmtFuel?
      (regularExit := .stop) (sourceProgram := program) (sourceFuel := sourceFuel)
      hCompile hBlocks contract.fits contract.stops
  refine
    RealizingForwardPreservesUnder.of_forward_first_jump_stops
      (fun target hStateRel =>
        Simulation.Interaction.ForwardRel.ofRel (hPreserves target hStateRel))
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

/--
Leaf realizing case for a terminal (halt) fragment.

Mirrors `terminal_exec`.  The forward outcome leg is the existing
`PreservesUnder … 1` terminal leaf (built from `contract.nonregular`) weakened by
`ForwardRel.ofRel`; the accumulator is discharged as for `code` — the compiled
terminal block's single `openStep` (backward-simulated via
`openStep_terminal_of_compileStmtFuel?`) reaches only policy-stopping outcomes
(`contract.stops`).
-/
theorem terminal_forward_realizing
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
      StmtContract cfg result ctx supply entry regular input
        source tokens policy)
    (hEntry :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target) :
    RealizingForwardPreservesUnder result cfg entry ctx regular .stop
      source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.terminal kind) source)
      1 policy realized := by
  have hPreserves :=
    InteractionLeafPreservation.Stmt.openRun_terminal_under_of_compileStmtFuel?
      (regularExit := .stop) (sourceProgram := program) (sourceFuel := sourceFuel)
      hCompile hBlocks contract.fits contract.nonregular
  refine
    RealizingForwardPreservesUnder.of_forward_first_jump_stops
      (fun target hStateRel =>
        Simulation.Interaction.ForwardRel.ofRel (hPreserves target hStateRel))
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

end OpenOutcome
end InteractionOwnerPreservation
end Structured
end EvmCompiler
