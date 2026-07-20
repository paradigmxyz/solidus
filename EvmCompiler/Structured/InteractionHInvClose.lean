import EvmCompiler.Structured.InteractionFrameConsistentCallLeg
import EvmCompiler.Structured.InteractionHInvAssemblyRegular
import EvmCompiler.Structured.InteractionHInvAssembly
import EvmCompiler.Structured.TypedCfgPreservation.StackRealizesEntry

/-!
# The `hInv` assembly — the strengthened `openStep`-jump invariant and its `AllEntriesRealized`
production (session 47)

Session 47 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-46 frontier item 1).

This is the campaign's convergence point.  Every ingredient is now banked:

* `block_category` (`InteractionBlockProvenance.lean`) classifies the block found at an
  arbitrary reached entry into one of the four generated categories;
* `main_blockGenShapeReg` / `proc_blockGenShapeReg`
  (`InteractionHInvAssemblyRegular.lean`) turn the main/proc-body membership into the
  strengthened `BlockGenShapeReg cfg source context.calls block` classification (which now
  carries, on `callHead`, the `hProcs`/`hResultCalls`/`hReg` fields the push leg needs);
* the nine `realizedWitnessFC_of_*_dispatch` legs
  (`InteractionFrameConsistent{Legs,BranchLegs,CodeLeg,DispatchLeg,CallLeg}.lean`) land the
  strengthened successor per disjunct;
* `realizedWitnessFC_of_dispatch_arm` handles the return-dispatch arm;
* `programEnd_openStep_no_jump` discharges the terminal arm vacuously.

`realizedWitnessFC_of_blockGenShapeReg` case-splits the nine disjuncts once (shared by the
main and proc arms).  `openStep_preserves_realizedWitnessFC` assembles the four
`block_category` arms into the global `openStep`-jump invariant at `realizedWitnessFC`.
`allEntriesRealized_realizedWitness_of_context` feeds it to the route-B master lever
`AllEntriesRealized.of_openStep_invariant` and weakens the result to the bare
`realizedWitness cfg` the downstream (Step B) consumer wants.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)
open TypedCfg.InteractionSemantics.Program (AllEntriesRealized)

/--
**The nine-disjunct case split, shared by the main and proc arms.**  Given the strengthened
`BlockGenShapeReg` classification of the block at `block.label`, the entry witness
`realizedWitnessFC … block.label t`, and a first-step jump out of it, produce the successor
witness by dispatching to the matching `realizedWitnessFC_of_*_dispatch` leg. -/
theorem realizedWitnessFC_of_blockGenShapeReg
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block} {t : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hGen :
      InteractionBlockGenShapeRegular.BlockGenShapeReg cfg source context.calls block)
    (hReal : realizedWitnessFC source cfg context.calls block.label t)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg block.label t)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC source cfg context.calls next state' := by
  cases hGen with
  | codeHead hCompile hBlocks hReg =>
      exact
        realizedWitnessFC_of_codeHead_dispatch (codeSourceProgram := source)
          (sourceFuel := 0) hReal hCompile hBlocks hReg hExec
  | ifHead hCompile hBlocks hReg =>
      exact realizedWitnessFC_of_ifHead_dispatch hReal hCompile hBlocks hReg hExec
  | callHead hProcs hLookup hCompile hBlocks hResultCalls hEntryShape hProcWF hReg =>
      exact
        realizedWitnessFC_of_callHead_dispatch context hProcs hLookup hCompile hBlocks
          hResultCalls hEntryShape hProcWF hReg hReal hExec
  | forCond hType hSource hFindF hFalseShape hTrueShape =>
      exact
        realizedWitnessFC_of_forCond_dispatch hReal hType hSource hFindF hFalseShape
          hTrueShape hExec
  | switchTest hHead hBlocks hMem hPopExists hCaseShape hNextShape =>
      exact
        realizedWitnessFC_of_switchTest_dispatch hReal hBlocks hMem hHead hPopExists
          hCaseShape hNextShape hExec
  | caseEntryPop hType hBlocks hMem hExit hPopTransport =>
      exact
        realizedWitnessFC_of_caseEntryPop_dispatch hReal hBlocks hMem hType hExit
          hPopTransport hExec
  | nilJoin hFindN hExit =>
      exact realizedWitnessFC_of_nilJoin_dispatch hReal hFindN hExit hExec
  | procAdapter hType hFindA hBodyShape hTransport hInputActive =>
      exact
        realizedWitnessFC_of_procAdapter_dispatch hReal hType hFindA hBodyShape
          hTransport hInputActive hExec
  | terminalHalt hFindT =>
      exact realizedWitnessFC_of_terminalHalt_dispatch hFindT hExec

/--
**The strengthened `openStep`-jump invariant** (the campaign's convergence point).  At an
arbitrary reached entry `e` whose entry witness is `realizedWitnessFC … e t`, any non-stopping
first-step jump to `(n, s)` preserves the strengthened witness.  Proof: recover the block at
`e` from the witness (pinning `block.label = e`), classify it with `block_category`, and
discharge each of the four arms — main/proc bodies via
`realizedWitnessFC_of_blockGenShapeReg`, the dispatch arm via
`realizedWitnessFC_of_dispatch_arm`, the terminal arm vacuously via
`programEnd_openStep_no_jump`. -/
theorem openStep_preserves_realizedWitnessFC
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {e : Assembly.Label} {t : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {n : Assembly.Label} {s : EVMState}
    (hReal : realizedWitnessFC source cfg context.calls e t)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg e t)
        transcript (Except.ok (TypedCfg.Outcome.jump n s))) :
    realizedWitnessFC source cfg context.calls n s := by
  have hReal2 := hReal
  obtain ⟨src, tokens, block, hFind, hStateRel, hFits, hFC, hLive⟩ := hReal2
  have hLabel : block.label = e := by
    have h := hFind
    unfold TypedCfg.Program.findBlock? at h
    simpa using List.find?_some h
  subst e
  rcases context.block_category hFind with hMain | hProc | hDispatch | hEnd
  · exact
      realizedWitnessFC_of_blockGenShapeReg context
        (InteractionBlockGenShapeRegular.main_blockGenShapeReg context hSourceWF hMain)
        hReal hExec
  · exact
      realizedWitnessFC_of_blockGenShapeReg context
        (InteractionBlockGenShapeRegular.proc_blockGenShapeReg context hSourceWF hProc)
        hReal hExec
  · obtain ⟨proc, hProcMem, hLookup, hBlockEq⟩ :=
      dispatchBlock_provenance context hSourceWF hDispatch
    subst hBlockEq
    exact realizedWitnessFC_of_dispatch_arm context hLookup hReal hExec
  · subst hEnd
    exact (context.programEnd_openStep_no_jump hExec).elim

/--
**The `AllEntriesRealized` production.**  Feed the strengthened invariant to the route-B master
lever `AllEntriesRealized.of_openStep_invariant`, seed it with the entry witness, then weaken
the strengthened predicate back to the bare `realizedWitness cfg` (`allEntriesRealized_realizedWitness_of_FC`)
that the downstream Step-B consumer expects. -/
theorem allEntriesRealized_realizedWitness_of_context
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy} {fuel : Nat}
    {entry : Assembly.Label} {target : EVMState}
    (hSeed : realizedWitnessFC source cfg context.calls entry target) :
    AllEntriesRealized cfg policy fuel entry target (realizedWitness cfg) :=
  allEntriesRealized_realizedWitness_of_FC
    (AllEntriesRealized.of_openStep_invariant
      (fun _e _t _transcript _n _s hR hE =>
        openStep_preserves_realizedWitnessFC context hSourceWF hR hE)
      hSeed)

/-!
## Step B ingredient — the token-free block-entry `StackRealizes` bridge (session 47)

At a reached entry `label`, the `realizedWitness cfg` fact the `AllEntriesRealized` production
supplies unpacks to `StateRel` + `SourceFrameFits` on the block found there.  For a block whose
input shape carries **no** compiler-owned return token
(`block.input.returnTokenDepth? = none`), that already gives the full target-stack realization
the swap peephole arm's depth guard consumes — no run-structure information needed
(`stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none`, sessions 8/9).  This is the
token-free half of the per-entry `StackRealizes` discharge Step B threads at each entry.

The token-BEARING half (`block.input.returnTokenDepth? = some (length-1)`) is NOT bridgeable
from the bare `realizedWitness` alone: it needs `source.returns ≠ []` (equivalently a non-empty
realization token list `token :: tokens`) at that entry, which the bare predicate does not carry
— see the §Session-47 Step-B design finding in `PEEPHOLE_PROGRESS.md`.
-/

/-- **Token-free block-entry `StackRealizes` bridge.**  Unpack the entry's `realizedWitness`
and, for a token-free input shape, discharge `StackRealizes block.input state` outright. -/
theorem stackRealizes_of_realizedWitness_of_returnTokenDepth?_eq_none
    {cfg : TypedCfg.Program} {label : Assembly.Label} {state : EVMState}
    {block : TypedCfg.Block}
    (hReal : realizedWitness cfg label state)
    (hFind : cfg.findBlock? label = some block)
    (hDepth : block.input.returnTokenDepth? = none) :
    TypedCfg.StackRealizes block.input state := by
  obtain ⟨source, tokens, block', hFind', hRel, hFits⟩ := hReal
  obtain rfl : block' = block := Option.some.inj (hFind'.symm.trans hFind)
  exact
    TypedCfgPreservation.stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none
      hRel hFits hDepth

/--
**The un-weakened (`realizedWitnessFC`) `AllEntriesRealized` production** (session 48).  Same as
`allEntriesRealized_realizedWitness_of_context` but keeps the STRENGTHENED predicate — the form
the token-owning `StackRealizes` bridge (below) consumes, since the bare `realizedWitness` drops
the local liveness `hLive` conjunct the token-bearing case needs. -/
theorem allEntriesRealized_realizedWitnessFC_of_context
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy} {fuel : Nat}
    {entry : Assembly.Label} {target : EVMState}
    (hSeed : realizedWitnessFC source cfg context.calls entry target) :
    AllEntriesRealized cfg policy fuel entry target
      (realizedWitnessFC source cfg context.calls) :=
  AllEntriesRealized.of_openStep_invariant
    (fun _e _t _transcript _n _s hR hE =>
      openStep_preserves_realizedWitnessFC context hSourceWF hR hE)
    hSeed

/-- **Token-owning block-entry `StackRealizes` bridge** (session 48).  The token-bearing sibling
of `stackRealizes_of_realizedWitness_of_returnTokenDepth?_eq_none`.  For a block whose input owns
its return token at the bottom (`returnTokenDepth? = some (length - 1)`, as `TypedCfgCompiler`
emits for every proc-internal block), the strengthened witness's local liveness `hLive` supplies
the non-empty realization token list `token :: tokens`, and the session-8/9 procedure-entry lemma
`stackRealizes_of_stateRel_of_token_last_of_tokens_cons` discharges the full realization. -/
theorem stackRealizes_of_realizedWitnessFC_of_token_last
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {label : Assembly.Label} {state : EVMState} {block : TypedCfg.Block}
    (hReal : realizedWitnessFC source cfg calls label state)
    (hFind : cfg.findBlock? label = some block)
    (hLast : block.input.returnTokenDepth? = some (block.input.length - 1)) :
    TypedCfg.StackRealizes block.input state := by
  obtain ⟨src, tokens, block', hFind', hRel, hFits, _hFC, hLive⟩ := hReal
  obtain rfl : block' = block := Option.some.inj (hFind'.symm.trans hFind)
  obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil (hLive _ hLast)
  exact
    TypedCfgPreservation.stackRealizes_of_stateRel_of_token_last_of_tokens_cons
      hRel hFits hLast

end InteractionFrameConsistent
end Structured
end EvmCompiler
