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

/-- **Source-threaded one-step whole-program peephole congruence** (Step B).  The
step congruence `openStep_peephole_congr`, strengthened so that each jump leaf of
the ORIGINAL `openStep` carries the successor entry witness alongside its
`RuntimeOutcomeRel` value.  `Rel.strengthen_left` folds the left-tree leaf
invariant (`allDone_realizedWitnessFC_jump`) into the value relation; the
`Rel.mono` step re-seats the conjunction inside the `ExceptRel.ok` payload so the
result is an `ExceptRel`-shaped `doneRel` that `Rel.bind` can decompose. -/
theorem openStep_peephole_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Assembly.Label} {state1 state2 : EVMState}
    (hReal : realizedWitnessFC source cfg context.calls label state1)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun v1 v2 : TypedCfg.Outcome =>
          Outcome.RuntimeRel v1 v2 ∧
            (∀ lbl s1, v1 = TypedCfg.Outcome.jump lbl s1 →
              realizedWitnessFC source cfg context.calls lbl s1)))
      (InteractionSemantics.Program.openStep cfg label state1)
      (InteractionSemantics.Program.openStep (peepholeProgram cfg) label state2) := by
  have hStep :=
    openStep_peephole_congr (program := cfg) hTyped hIndependent hRel (label := label)
  have hAll := allDone_realizedWitnessFC_jump context hSourceWF hReal
  have hStrong := Simulation.Interaction.Rel.strengthen_left hStep hAll
  refine Simulation.Interaction.Rel.mono hStrong ?_
  rintro o1 o2 ⟨hER, hProp⟩
  cases hER with
  | error he => exact Simulation.Interaction.ExceptRel.error he
  | ok hrr =>
      exact Simulation.Interaction.ExceptRel.ok
        ⟨hrr, fun lbl s1 hv => hProp lbl s1 (by rw [hv])⟩

/-- **Source-threaded fuel-bounded whole-program peephole congruence** (Step B).
Same conclusion as the unconditional `openRunN_peephole_congr`, but carrying a seed
`realizedWitnessFC … cfg.entry state1`.  At each `openStep` the source-threaded step
congruence supplies the successor entry witness at every jump leaf, which the fuel
recursion consumes to re-seed itself at the jump target.  This places the entry
witness in scope at every reached block entry — the hook Step D's swap arm uses to
discharge its runtime depth guard (`stackRealizes_of_realizedWitnessFC_total`). -/
theorem openRunN_peephole_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent) :
    ∀ (fuel : Nat) (label : Assembly.Label) (state1 state2 : EVMState),
      realizedWitnessFC source cfg context.calls label state1 →
      SameRuntimeData state1 state2 →
      Simulation.Interaction.Rel Block.RuntimeOutcomeRel
        (InteractionSemantics.Program.openRunN cfg fuel label state1)
        (InteractionSemantics.Program.openRunN (peepholeProgram cfg) fuel label state2)
  | 0, label, state1, state2, _hReal, hRel => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (.ok (Outcome.RuntimeRel.jump label hRel))
  | fuel + 1, label, state1, state2, hReal, hRel => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStep :=
        openStep_peephole_congr_of_source context hSourceWF hTyped hIndependent hReal hRel
      apply Simulation.Interaction.Rel.bind hStep
      intro o1 o2 hOut
      obtain ⟨hRR, hWit⟩ := hOut
      cases hRR with
      | jump lbl hState =>
          exact openRunN_peephole_congr_of_source context hSourceWF hTyped hIndependent
            fuel lbl _ _ (hWit lbl _ rfl) hState
      | fallthrough hState =>
          exact .done (.ok (Outcome.RuntimeRel.fallthrough hState))
      | returnDispatch hState =>
          exact .done (.ok (Outcome.RuntimeRel.returnDispatch hState))
      | halt kind hState =>
          exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
      | invalid hState =>
          exact .done (.ok (Outcome.RuntimeRel.invalid hState))

/-- **Source-threaded whole-program prefix peephole congruence** (Step B).  The
finite-prefix witness the compile spine feeds to `Rel.executes` / `OpenBlock.runtime_left`,
carrying the seed entry witness so the swap arm's per-entry depth guard is
dischargeable along the run.  Conclusion identical to `openRunNPrefix_peephole_congr`. -/
theorem openRunNPrefix_peephole_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    (fuel : Nat) (label : Assembly.Label) (state1 state2 : EVMState)
    (hReal : realizedWitnessFC source cfg context.calls label state1)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix cfg fuel label state1)
      (InteractionSemantics.Program.openRunNPrefix (peepholeProgram cfg)
        fuel label state2) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_peephole_congr_of_source context hSourceWF hTyped hIndependent
      fuel label state1 state2 hReal hRel
  apply Simulation.Interaction.Rel.bind hRun
  intro o1 o2 hOut
  cases hOut with
  | halt kind hState =>
      exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
  | jump lbl hState =>
      exact .done (.error rfl)
  | fallthrough hState =>
      exact .done (.error rfl)
  | returnDispatch hState =>
      exact .done (.error rfl)
  | invalid hState =>
      exact .done (.error rfl)

end Peephole
end TypedCfg
end EvmCompiler
