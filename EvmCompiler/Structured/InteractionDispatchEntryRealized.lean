import EvmCompiler.Structured.InteractionCallEntryRealized

/-!
# Caller-continuation `StateRel` extraction for the `returnDispatch` terminator
(the widening frame-model leg deferred since session 5)

This module is the `returnDispatch` analogue of
`InteractionCallPreservation.Call.jump_state_rel_of_pure`
(`InteractionCallEntryRealized.lean`).  It lands the concrete sub-lemma the
`realizedWitness` `openStep`-jump invariant turns on at a **procedure-exit**
block: from a concrete non-stopping first jump of the compiled return-dispatch
block, extract the **caller-side** `StateRel` for the jumped-to caller
continuation.

The key structural fact — established across sessions 5–7 as "the genuine
frame-model step" — is that the compiled procedure-exit block is *silent* at the
shared CFG interaction level.  The frame-model work (reading the return token off
the caller frame, dispatching to the registered call site, and peeling one
activation frame off the runtime stack while restoring the caller state) is
already performed and proved by

    InteractionCallPreservation.Call.openStep_dispatch
      (`InteractionCallPreservation.lean:747`)

whose conclusion is precisely a concrete `pure`-jump

    Program.openStep cfg (ProcLabel.exit proc.name) target
      = pure (.jump site.returnLabel targetFinal)

together with the **caller** `StateRel (returned.withEVM …) tokens targetFinal`
(via `TypedCfgPreservation.CallStack.eraseReturnToken_preserves`,
`Core.lean:1761`, i.e. the `realizeStack`/`StateRel`/`ActivationExtension`
machinery).  Because that is exactly the abstract `pure`-jump characterization
`jump_state_rel_of_pure` is phrased over, the `returnDispatch` extraction is a
direct composition: no new backward simulation and no re-derivation of the frame
model is required — the dispatch is *not* a widening `jumpi` branch at the CFG
level, it is a silent `pure` jump whose target/state the frame model already
pins.

`jump_state_rel_of_dispatch` below packages that composition over the concrete
`openStep_dispatch` hypotheses (which the invariant's proof recovers per
procedure exit from the in-scope source run) plus a concrete `Executes`, and
emits the caller `StateRel` at the jumped-to `state'`.  It is exactly the witness
the invariant's `returnDispatch` case relays to `realizedWitness_of_stateRel`
(see `realizedWitness_of_dispatch_jump` in
`InteractionRealizedWitnessSuccessor.lean`).

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionCallPreservation
namespace Call

/--
Extract the caller-continuation `StateRel` (and the taken caller label) from a
concrete first-step jump of a compiled procedure-exit (return-dispatch) block.

The compiled exit block is silent, so its `openStep` reduces to a concrete
`pure (.jump site.returnLabel targetFinal)` — this is exactly what
`openStep_dispatch` establishes, with the caller `StateRel` for `targetFinal`
obtained by peeling one activation frame off the runtime stack
(`eraseReturnToken_preserves`).  Any concrete `Executes` of that `pure` to a
`.jump next state'` leaf forces `next = site.returnLabel` and
`state' = targetFinal`, so the supplied caller `StateRel` transports to `state'`.

This is the `returnDispatch` counterpart of
`InteractionCallPreservation.Call.jump_state_rel_of_pure`, and it is the widening
caller-frame leg deferred since session 5.  The frame model it depends on is
entirely inside `openStep_dispatch`; this lemma only relays its `pure`-jump
characterization through the generic pure-jump extraction.
-/
theorem jump_state_rel_of_dispatch
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {site : TypedCfgCompiler.DispatchSite}
    {bodyState returned : RunState} {frame : ReturnDest}
    {stack : EvmYul.Stack Word} {tokens : List Word}
    {target state' : EVMState}
    {next : Assembly.Label}
    {transcript : Simulation.Interaction.Transcript}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hSiteProc : site.procName = proc.name)
    (hSiteMem : site ∈ context.calls)
    (hRel :
      TypedCfgPreservation.StateRel
        bodyState (site.token :: tokens) target)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hRetc : frame.retc = proc.retc)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg (ProcLabel.exit proc.name) target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    next = site.returnLabel ∧
      TypedCfgPreservation.StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        tokens state' := by
  obtain ⟨targetFinal, hStep, hChildRel⟩ :=
    openStep_dispatch context hLookup hSiteProc hSiteMem hRel hPop hAttach hRetc
  exact jump_state_rel_of_pure hStep hChildRel hExec

end Call
end InteractionCallPreservation
end Structured
end EvmCompiler
