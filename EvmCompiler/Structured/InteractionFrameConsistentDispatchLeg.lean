import EvmCompiler.Structured.InteractionFrameConsistentCodeLeg

/-!
# Strengthened (`realizedWitnessFC`) `hInv` leg — the dispatch (pop) arm (session 46)

Session 46 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-45 frontier item 1).

The dispatch arm is `block_category`'s third arm: a compiled procedure-exit (return-dispatch)
block pops one ghost return frame and jumps to the caller continuation.  This is the arm that
MOTIVATED the strengthening (session 45's counterexample): the entry witness's `FrameConsistent`
conjunct is exactly what supplies the two source-frame-safety atoms the dispatch finisher needs
(`frame.retc = proc.retc` + the caller-continuation shape), which `realizedWitness` alone cannot.

This module banks `realizedWitnessFC_of_dispatch_arm`: from the entry `realizedWitnessFC` at a
procedure exit, it

* reads the head frame's `FrameHeadConsistent` off the entry `FrameConsistent` (instantiated at
  the runtime-selected return site + the exiting proc) to discharge the atoms — no residual
  `hFinish`, no `source.FrameSafe` hypothesis; and
* transports the TAIL `FrameConsistent` (`FrameConsistent.tail`) to the popped caller witness,
  landing the strengthened successor.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**The dispatch (pop) arm at the strengthened predicate.**

From the entry `realizedWitnessFC` at `ProcLabel.exit proc.name` (whose `FrameConsistent`
conjunct carries the head frame's consistency) and any concrete first jump, land the successor
`realizedWitnessFC` at the caller continuation.  The head frame's `FrameHeadConsistent` supplies
`frame.retc = proc.retc` and the caller `LabelShape` + restored-frame `SourceFrameFits`
(discharging the finisher); `FrameConsistent.tail` gives the popped caller activation's
consistency. -/
theorem realizedWitnessFC_of_dispatch_arm
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext sourceProgram entryShapes cfg)
    {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? proc.name sourceProgram.procs = some proc)
    {target state' : EVMState}
    {next : Assembly.Label} {transcript : Simulation.Interaction.Transcript}
    (hReal :
      realizedWitnessFC sourceProgram cfg context.calls
        (ProcLabel.exit proc.name) target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg (ProcLabel.exit proc.name) target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg context.calls next state' := by
  -- Unify the entry witness block with the dispatch block to pin the exit shape.
  obtain ⟨bodyState, tokens, block, hFindReal, hStateRel, hFits0, hFC, _hLive⟩ := hReal
  have hFindDispatch :
      cfg.findBlock? (ProcLabel.exit proc.name) =
        some (TypedCfgCompiler.dispatchBlock proc context.calls) :=
    context.dispatchBlock hLookup
  have hBlockEq : block = TypedCfgCompiler.dispatchBlock proc context.calls :=
    Option.some.inj (hFindReal.symm.trans hFindDispatch)
  subst hBlockEq
  have hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procExit proc) bodyState.evm.stack.length := hFits0
  -- Invert the dispatch jump to the runtime-selected return site.
  obtain ⟨site, rest, hMem, hSiteProc, hTok, _hNext, _hState'⟩ :=
    InteractionDispatchInversion.dispatch_openStep_jump_inv
      context hLookup hStateRel hFits hExec
  subst hTok
  -- Pop the head frame off the exit `StateRel`.
  obtain ⟨frame, returns, hReturns, hPop⟩ :=
    dispatch_popReturn?_of_stateRel hStateRel
  -- Split the entry `FrameConsistent` into head + tail.
  have hFCcons :
      FrameConsistent sourceProgram cfg context.calls (frame :: returns)
        (site.token :: rest) := by
    rw [← hReturns]; exact hFC
  have hHead : FrameHeadConsistent sourceProgram cfg context.calls frame site.token :=
    (FrameConsistent_cons_cons.mp hFCcons).1
  have hContLive :
      FrameContinuationLive cfg context.calls site.token rest :=
    (FrameConsistent_cons_cons.mp hFCcons).2.1
  have hTail : FrameConsistent sourceProgram cfg context.calls returns rest :=
    (FrameConsistent_cons_cons.mp hFCcons).2.2
  -- Instantiate the head consistency at the selected site + the exiting proc.
  have hLookupSite :
      Structured.ProcList.lookup? site.procName sourceProgram.procs = some proc := by
    rw [hSiteProc]; exact hLookup
  obtain ⟨hRetc, callerInput, hLabelShape, hFitsCaller⟩ :=
    hHead site proc hMem rfl hLookupSite
  -- Reattach the return vector onto the caller stack.
  have hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some (bodyState.evm.stack ++ frame.callerStack) :=
    InteractionDispatchInversion.attachReturns?_of_procExit_fit hFits hRetc
  -- Read the popped caller `StateRel` off the dispatch jump.
  obtain ⟨hNextEq, hChildRel⟩ :=
    InteractionCallPreservation.Call.jump_state_rel_of_dispatch
      context hLookup hSiteProc hMem hStateRel hPop hAttach hRetc hExec
  subst hNextEq
  -- Package the strengthened caller witness.
  have hStackLen : bodyState.evm.stack.length = frame.retc := by
    have hDepth :=
      hFits.2 proc.retc
        (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
    rw [hDepth, hRetc]
  refine realizedWitnessFC_of_stateRel hLabelShape hChildRel ?_ ?_ ?_
  · -- child frame-fit at the restored caller stack length
    have hLen :
        (({ bodyState with returns := returns } : RunState).withEVM
            { bodyState.evm with
              stack := bodyState.evm.stack ++ frame.callerStack }).evm.stack.length =
          frame.retc + frame.callerStack.length := by
      simp only [RunState.withEVM_evm, List.length_append, hStackLen]
    rw [hLen]
    exact hFitsCaller
  · -- child frame-consistency is the tail of the entry's
    have hReturned :
        (({ bodyState with returns := returns } : RunState).withEVM
            { bodyState.evm with
              stack := bodyState.evm.stack ++ frame.callerStack }).returns = returns := by
      simp [RunState.withEVM_returns]
    rw [hReturned]
    exact hTail
  · -- child liveness: the caller continuation `callerInput` owning a return token forces the
    -- residual realization `rest` to be non-empty — exactly the head frame's continuation-liveness
    -- coupling, read off the entry `FrameConsistent`.
    intro d hd
    exact hContLive site callerInput hMem rfl hLabelShape (by simp [hd])

end InteractionFrameConsistent
end Structured
end EvmCompiler
