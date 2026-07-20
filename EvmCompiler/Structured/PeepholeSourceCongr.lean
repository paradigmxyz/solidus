import EvmCompiler.TypedCfg.PeepholeProgram
import EvmCompiler.Structured.InteractionHInvClose
import EvmCompiler.Structured.TokenBottomThread

/-!
# Source-threaded whole-program peephole congruences (Step B)

The unconditional whole-program peephole congruences (`PeepholeProgram.lean`)
relate the original program run to the peepholed run purely from `SameRuntimeData`.
Once the block-body peephole gains the `swap d ; swap d → ε` arm (Step D), the
per-block congruence acquires a runtime depth guard, discharged at each visited
block entry from `TypedCfg.StackRealizes block.input state` — which the source
tower supplies via `stackRealizes_of_realizedWitnessFC_total` given the
strengthened entry witness `realizedWitnessFC` at that entry.

This file threads that witness through the fuel-bounded open runners:
`openRunN_peephole_congr_of_source` / `openRunNPrefix_peephole_congr_of_source`
carry a seed `realizedWitnessFC … cfg.entry state1` and re-establish it at every
successor entry the run jumps to.  The conclusion is the SAME
`Rel RuntimeOutcomeRel` the unconditional congruence produces — the threading is
internal, its purpose being to place the entry witness in scope at each `openStep`
so Step D's swap arm can consume it.

The genuine structural obstacle (frontier item, §Session-50) was that the fuel
recursion goes through `Rel.bind`, whose value-level continuation exposes the jump
*outcomes* but NOT an `Executes (openStep …) transcript (.ok (jump …))` fact —
which `openStep_preserves_realizedWitnessFC` needs to re-derive the successor
witness.  The connector below dissolves it: `Rel.strengthen_left` folds a
LEFT-tree leaf invariant (`AllDone`) into the step congruence's `doneRel`, so the
successor witness travels ALONGSIDE the `RuntimeOutcomeRel` value at each jump
leaf and is available in the `Rel.bind` continuation.  The leaf invariant itself
is `allDone_realizedWitnessFC_jump`, built from the per-leaf
`openStep_preserves_realizedWitnessFC` via the generic Executes→AllDone converse
`allDone_of_forall_executes`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

universe u v

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-- **Executes → AllDone converse.**  If a leaf property holds at every concrete
execution outcome of an interaction tree, it holds at every terminal leaf.  This
is the converse of `AllDone.property_of_executes`: it turns a branchwise
`Executes`-quantified fact into the structural `AllDone` invariant. -/
theorem allDone_of_forall_executes
    {Error : Type u} {Result : Type v}
    {property : Except Error Result → Prop}
    {interaction : Simulation.Interaction Error Result}
    (h : ∀ transcript outcome,
      Simulation.Interaction.Executes interaction transcript outcome →
        property outcome) :
    Simulation.Interaction.AllDone property interaction := by
  induction interaction with
  | done outcome =>
      exact .done (h [] outcome (Simulation.Interaction.Executes.done outcome))
  | request query resume ih =>
      refine .request (fun answer => ih answer ?_)
      intro transcript outcome hExec
      exact h ({ query := query, answer := answer } :: transcript) outcome
        (Simulation.Interaction.Executes.request answer hExec)

/-- **The `openStep` jump-leaf witness invariant** (the Step-B connector).  At an
entry whose strengthened witness holds, every jump leaf `.ok (.jump lbl s1)` of
`openStep cfg label state1` carries the strengthened witness at its successor
`(lbl, s1)`.  Packaged as an `AllDone` so `Rel.strengthen_left` can fold it into
the step congruence's `doneRel`. -/
theorem allDone_realizedWitnessFC_jump
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {label : Assembly.Label} {state1 : EVMState}
    (hReal : realizedWitnessFC source cfg context.calls label state1) :
    Simulation.Interaction.AllDone
      (fun o : Except EVMException TypedCfg.Outcome =>
        ∀ lbl s1, o = Except.ok (TypedCfg.Outcome.jump lbl s1) →
          realizedWitnessFC source cfg context.calls lbl s1)
      (InteractionSemantics.Program.openStep cfg label state1) := by
  refine allDone_of_forall_executes ?_
  intro transcript outcome hExec lbl s1 hEq
  subst hEq
  exact Structured.InteractionFrameConsistent.openStep_preserves_realizedWitnessFC
    context hSourceWF hReal hExec

end Peephole
end TypedCfg
end EvmCompiler
