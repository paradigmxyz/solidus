import EvmCompiler.Structured.InteractionBoundedOwnerRealized

/-!
# Per-leg `realizedWitness` successor lemmas (framing-2 `hInv` discharge substrate)

Session 27 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-26).

The route-B master lever `AllEntriesRealized.of_openStep_invariant`
(`TypedCfg/InteractionEntryRealized.lean:271`) reduces the whole peephole endgame
to one obligation: `realizedWitness cfg` is an `openStep`-jump invariant, i.e.

    realizedWitness cfg entry target →
    Executes (openStep cfg entry target) transcript (.ok (.jump next state')) →
    realizedWitness cfg next state'.

Session 26 established this is NOT provable standalone from `realizedWitness cfg
entry target`, because reconstructing the child `StateRel` at `state'` requires the
`entry` block's **source-construct compile-fact** (the source-coupling
`Rel (DoneRel …)` / the silent `pure`-jump equation), which `realizedWitness`
(`findBlock?` + `StateRel` + `SourceFrameFits`) does not carry.  Framing 2 supplies
that coupling from the source run threaded at the OIC splice.

This module banks the **per-leg successor step**: GIVEN the source coupling at the
`entry` block (the fact the invariant's proof recovers per construct from the
in-scope source run) plus the target block's declared shape (`LabelShape`), it
produces the child `realizedWitness cfg next state'` directly.  Each lemma is a
green composition of an existing child-`StateRel` extraction
(`InteractionBranchEntryRealized.jump_state_rel_of_rel` /
`InteractionCallEntryRealized.jump_state_rel_of_pure`) with the uniform
entry-witness supplier
(`InteractionBoundedOwnerPreservation.realizedWitness_of_stateRel`,
session 16).

These are the `if`/branch and `call`/pure legs of the invariant.  They isolate the
exact remaining input the invariant's proof must supply at each reached entry — the
source coupling and the target `LabelShape` — leaving the provenance recovery (which
construct owns `entry`, recovered via `GeneratedContext`/the source run) as the sole
open frontier, and the widening `returnDispatch` caller-frame leg (deferred) beside
it.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionRealizedWitnessSuccessor

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness realizedWitness_of_stateRel)

/--
**Branch/`if` leg of the `realizedWitness` `openStep`-jump invariant.**

For an `if`-style condition block whose `openStep` is source-coupled to the source
condition run by `Rel (DoneRel trueLabel falseLabel tokens restShape)`, any concrete
non-stopping first jump to `(next, state')` lands a child `realizedWitness cfg next
state'`, provided the ambient CFG block at `next` expects the branch's `restShape`
(`LabelShape cfg next restShape`).

Proof: `jump_state_rel_of_rel` reads off the child `StateRel`/`SourceFrameFits` at
`state'`; `realizedWitness_of_stateRel` packages them with the target `LabelShape`.
-/
theorem realizedWitness_of_branch_jump
    {cfg : TypedCfg.Program}
    {entry : Assembly.Label} {target : EVMState}
    {trueLabel falseLabel : Assembly.Label}
    {tokens : List Word} {restShape : TypedCfg.Shape}
    {srcRun : Simulation.Interaction EVMException (RunState × Bool)}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel
          trueLabel falseLabel tokens restShape)
        srcRun
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target))
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape : TypedCfgPreservation.LabelShape cfg next restShape) :
    realizedWitness cfg next state' := by
  obtain ⟨srcState, cond, _hNext, hStateRel, hFits⟩ :=
    InteractionBranchPreservation.Condition.jump_state_rel_of_rel hRel hExec
  exact realizedWitness_of_stateRel hLabelShape hStateRel hFits

/--
**Call leg of the `realizedWitness` `openStep`-jump invariant.**

For a silent compiled call-site block whose `openStep` reduces to the concrete
`pure (.jump childLabel childState)` with child `StateRel childSource childTokens
childState`, any concrete first jump to `(next, state')` lands a child
`realizedWitness cfg next state'`, provided the ambient CFG block at `childLabel`
expects `childInput` (`LabelShape cfg childLabel childInput`) and the child frame
fits (`SourceFrameFits childInput childSource.evm.stack.length`).

Proof: `jump_state_rel_of_pure` forces `next = childLabel` and transports the child
`StateRel` to `state'`; `realizedWitness_of_stateRel` packages it with the target
`LabelShape`.
-/
theorem realizedWitness_of_pure_jump
    {cfg : TypedCfg.Program}
    {entry childLabel next : Assembly.Label}
    {childInput : TypedCfg.Shape}
    {target childState state' : EVMState}
    {childSource : RunState} {childTokens : List Word}
    {transcript : Simulation.Interaction.Transcript}
    (hStep :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump childLabel childState))
    (hChildRel :
      TypedCfgPreservation.StateRel childSource childTokens childState)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape : TypedCfgPreservation.LabelShape cfg childLabel childInput)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        childInput childSource.evm.stack.length) :
    realizedWitness cfg next state' := by
  obtain ⟨hNext, hStateRel⟩ :=
    InteractionCallPreservation.Call.jump_state_rel_of_pure hStep hChildRel hExec
  subst hNext
  exact realizedWitness_of_stateRel hLabelShape hStateRel hFits

end InteractionRealizedWitnessSuccessor
end Structured
end EvmCompiler
