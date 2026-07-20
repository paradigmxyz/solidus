import EvmCompiler.Structured.InteractionHInvAssembly
import EvmCompiler.Structured.InteractionRealizedWitnessSuccessor

/-!
# The dispatch `openStep`-jump inversion substrate (session 44)

Session 44 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-43 frontier item 1).

The dispatch arm of the `hInv` `openStep`-jump invariant lands its successor
`realizedWitness` through `InteractionRealizedWitnessSuccessor.realizedWitness_of_dispatch_jump`,
which CONSUMES the site facts `hSiteProc`/`hSiteMem`/`hRel`/`hPop`/`hAttach`/`hRetc`.
`InteractionHInvAssembly.dispatchBlock_provenance` recovers the owning proc + `hLookup`;
`dispatch_popReturn?_of_stateRel` gives `hPop` once the token list is known non-empty.  The
missing move is the *inversion*: from `hExec` (the exit block's `openStep` produced a
`.jump`) recover the matching return `site` and the token correspondence.  This module banks
the two clean, source-run-free intermediate substrates:

* **`findTarget?_returnSitesFor_inv`** — `findTarget?`-some inversion.  A successful
  `findTarget?` over `returnSitesFor name calls` exposes the owning `DispatchSite ∈ calls`
  with the matching `procName`/`token`/`returnLabel`.  Pure list induction over the
  `filterMap`; the exact reverse of `findTarget?_returnSitesFor_of_mem`.

* **`get_retc_of_stateRel_procExit`** — the `StateRel`-at-`procExit` runtime/ghost token
  correspondence.  At a procedure-exit shape the return token is realized at runtime stack
  depth `proc.retc`; reading that slot recovers exactly the head ghost token
  (`target.stack[proc.retc]? = tokens.head?`).  This simultaneously pins the runtime token to
  the ghost head AND, when the slot is populated (as the `returnDispatch` jump requires),
  forces the ghost token list non-empty — the hypothesis `dispatch_popReturn?_of_stateRel`
  and `realizedWitness_of_dispatch_jump` both need.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionDispatchInversion

/--
**`findTarget?`-some inversion over `returnSitesFor`.**

A successful return-dispatch table hit `findTarget? token (returnSitesFor name calls) =
some target` is realized by exactly one registered `DispatchSite ∈ calls` whose `procName`
is `name`, whose `token` is the read token, and whose `returnLabel` is the jumped-to target.

This is the exact reverse of `TypedCfgCompilerFacts.Call.findTarget?_returnSitesFor_of_mem`
and the first half of the dispatch `openStep`-jump inversion: it turns the runtime dispatch
result into the `site ∈ context.calls` / `site.procName` / `site.returnLabel` facts the
successor supplier `realizedWitness_of_dispatch_jump` consumes as `hSiteMem`/`hSiteProc`. -/
theorem findTarget?_returnSitesFor_inv
    {name : Structured.Name} {calls : List TypedCfgCompiler.DispatchSite}
    {token : Word} {target : Assembly.Label}
    (hFind :
      TypedCfg.Block.ReturnSite.findTarget? token
          (TypedCfgCompiler.returnSitesFor name calls) = some target) :
    ∃ site : TypedCfgCompiler.DispatchSite,
      site ∈ calls ∧
        site.procName = name ∧ site.token = token ∧ site.returnLabel = target := by
  induction calls with
  | nil =>
      simp [TypedCfgCompiler.returnSitesFor, TypedCfg.Block.ReturnSite.findTarget?] at hFind
  | cons head tail ih =>
      simp only [TypedCfgCompiler.returnSitesFor, List.filterMap_cons] at hFind
      by_cases hName : head.procName = name
      · rw [if_pos hName] at hFind
        rw [TypedCfg.Block.ReturnSite.findTarget?] at hFind
        by_cases hTok : head.token = token
        · rw [if_pos hTok] at hFind
          exact ⟨head, List.mem_cons_self, hName, hTok, Option.some.inj hFind⟩
        · rw [if_neg hTok] at hFind
          obtain ⟨site, hMem, h1, h2, h3⟩ :=
            ih (by simpa [TypedCfgCompiler.returnSitesFor] using hFind)
          exact ⟨site, List.mem_cons_of_mem _ hMem, h1, h2, h3⟩
      · rw [if_neg hName] at hFind
        obtain ⟨site, hMem, h1, h2, h3⟩ :=
          ih (by simpa [TypedCfgCompiler.returnSitesFor] using hFind)
        exact ⟨site, List.mem_cons_of_mem _ hMem, h1, h2, h3⟩

/--
**`StateRel`-at-`procExit` runtime/ghost token correspondence.**

At a procedure-exit shape (`Shape.procExit proc`, whose `returnTokenDepth?` is `proc.retc`)
the source ghost return frames are realized into the target stack with the head return token
sitting at runtime depth `proc.retc`.  Reading that slot therefore recovers exactly the head
of the ghost token list — `none` iff the token list is empty (in which case the source has no
pending return and the slot is out of range at length `proc.retc`), `some token` at the head
otherwise.

For the dispatch inversion this pins the runtime `returnDispatch` token (`target.stack[proc.retc]?`)
to the ghost head token AND, since a successful `returnDispatch` jump forces the slot populated,
witnesses the token list non-empty (feeding `dispatch_popReturn?_of_stateRel`). -/
theorem get_retc_of_stateRel_procExit
    {bodyState : RunState} {tokens : List Word} {target : EVMState}
    {proc : Structured.Proc}
    (hRel : TypedCfgPreservation.StateRel bodyState tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procExit proc) bodyState.evm.stack.length) :
    target.stack[proc.retc]? = tokens.head? := by
  have hLen : bodyState.evm.stack.length = proc.retc :=
    hFits.2 proc.retc (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
  rcases hRel with ⟨realized, hRealize, hSame⟩
  have hTargetStack : target.stack = realized := by
    simpa using Assembly.SameRuntimeData.stack_eq hSame
  rw [hTargetStack]
  cases tokens with
  | nil =>
      cases hReturns : bodyState.returns with
      | nil =>
          rw [hReturns] at hRealize
          simp only [TypedCfgPreservation.realizeStack, Option.some.injEq] at hRealize
          subst hRealize
          rw [List.getElem?_eq_none (by omega), List.head?_nil]
      | cons frame rest =>
          rw [hReturns] at hRealize
          simp [TypedCfgPreservation.realizeStack] at hRealize
  | cons token tokens' =>
      cases hReturns : bodyState.returns with
      | nil =>
          rw [hReturns] at hRealize
          simp [TypedCfgPreservation.realizeStack] at hRealize
      | cons frame rest =>
          rw [hReturns] at hRealize
          simp only [TypedCfgPreservation.realizeStack] at hRealize
          rw [TypedCfgPreservation.realizeStack_append_prefix] at hRealize
          cases hRest :
              TypedCfgPreservation.realizeStack frame.callerStack rest tokens' with
          | none =>
              rw [hRest] at hRealize
              simp at hRealize
          | some hiddenRest =>
              rw [hRest] at hRealize
              simp only [Option.map_some, Option.some.injEq] at hRealize
              subst hRealize
              rw [List.head?_cons, List.append_assoc,
                List.getElem?_append_right (by omega)]
              simp [hLen]

/--
**The dispatch `openStep`-jump inversion (source-run-free core).**

At a procedure-exit (return-dispatch) block, whose `openStep` is the silent `runTerm` of
the `returnDispatch` terminator, any concrete first jump `hExec` forces the terminator to
have SUCCEEDED — the runtime return token was read at depth `proc.retc` and a registered
call site matched it.  Inverting that success recovers:

* the matching `DispatchSite ∈ context.calls` with `site.procName = proc.name` (via bank
  `findTarget?_returnSitesFor_inv`),
* the token list as a `cons` whose head IS `site.token` (via bank
  `get_retc_of_stateRel_procExit` — the runtime token equals the ghost head),
* the jumped-to label `next = site.returnLabel` and the peeled runtime state
  `state' = { target with stack := target.stack.eraseIdx proc.retc }`.

This is the exact reverse of `InteractionCallPreservation.Call.openStep_dispatch`.  It supplies
`hSiteProc`/`hSiteMem`/(the `cons`-form of) `hRel` that
`InteractionRealizedWitnessSuccessor.realizedWitness_of_dispatch_jump` consumes; the residual
frame facts `hPop`/`hAttach`/`hRetc` are the deferred (`source.FrameSafe`-dependent) half
threaded at the capstone assembly.  No source run required. -/
theorem dispatch_openStep_jump_inv
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? proc.name source.procs = some proc)
    {bodyState : RunState} {tokens : List Word} {target state' : EVMState}
    {next : Assembly.Label} {transcript : Simulation.Interaction.Transcript}
    (hRel : TypedCfgPreservation.StateRel bodyState tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procExit proc) bodyState.evm.stack.length)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg (ProcLabel.exit proc.name) target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    ∃ (site : TypedCfgCompiler.DispatchSite) (rest : List Word),
      site ∈ context.calls ∧
        site.procName = proc.name ∧
        tokens = site.token :: rest ∧
        next = site.returnLabel ∧
        state' = { target with stack := target.stack.eraseIdx proc.retc } := by
  have hBlock := context.dispatchBlock hLookup
  have hGet := get_retc_of_stateRel_procExit hRel hFits
  set sites := TypedCfgCompiler.returnSitesFor proc.name context.calls with hSitesDef
  -- The dispatch block is empty-bodied with `input = output = procExit proc`; its
  -- `openStep` reduces to the silent `pure (runTerm procExit term target)`.
  by_cases hEmpty : sites.isEmpty = true
  · -- Empty return-site table ⇒ terminator is `.invalid`, never a jump: `hExec` is absurd.
    have hBlock' :
        cfg.findBlock? (ProcLabel.exit proc.name) =
          some
            { label := ProcLabel.exit proc.name
              input := TypedCfgCompiler.Shape.procExit proc
              body := []
              output := TypedCfgCompiler.Shape.procExit proc
              term := .invalid } := by
      rw [hBlock]; simp [TypedCfgCompiler.dispatchBlock, ← hSitesDef, hEmpty]
    have hStep :
        TypedCfg.InteractionSemantics.Program.openStep
            cfg (ProcLabel.exit proc.name) target =
          Simulation.Interaction.pure (TypedCfg.Outcome.invalid target) := by
      simp only [TypedCfg.InteractionSemantics.Program.openStep,
        TypedCfg.Control.Program.step, hBlock',
        TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody]
      change
        Simulation.Interaction.bind
            (Simulation.Interaction.done
              (Except.ok (target, TypedCfgCompiler.Shape.procExit proc)))
            (fun result =>
              if result.2 = TypedCfgCompiler.Shape.procExit proc then
                match TypedCfg.Block.runTermChecked
                    (TypedCfgCompiler.Shape.procExit proc) .invalid result.1 with
                | .ok outcome => Simulation.Interaction.pure outcome
                | .error err => Simulation.Interaction.error err
              else
                Simulation.Interaction.done
                  (Except.error (.InvalidInstruction : EVMException))) =
          Simulation.Interaction.pure (TypedCfg.Outcome.invalid target)
      simp [Simulation.Interaction.bind, TypedCfg.Block.runTerm]
    rw [hStep] at hExec
    simp only [Simulation.Interaction.pure] at hExec
    cases hExec
  · -- Nonempty table ⇒ terminator is `returnDispatch proc.retc sites`.
    have hFalse : sites.isEmpty = false := by
      simpa using hEmpty
    have hBlock' :
        cfg.findBlock? (ProcLabel.exit proc.name) =
          some
            { label := ProcLabel.exit proc.name
              input := TypedCfgCompiler.Shape.procExit proc
              body := []
              output := TypedCfgCompiler.Shape.procExit proc
              term := .returnDispatch proc.retc sites } := by
      rw [hBlock]; simp [TypedCfgCompiler.dispatchBlock, ← hSitesDef, hFalse]
    have hStep :
        TypedCfg.InteractionSemantics.Program.openStep
            cfg (ProcLabel.exit proc.name) target =
          Simulation.Interaction.pure
            (TypedCfg.Block.runTerm (TypedCfgCompiler.Shape.procExit proc)
              (.returnDispatch proc.retc sites) target) := by
      simp only [TypedCfg.InteractionSemantics.Program.openStep,
        TypedCfg.Control.Program.step, hBlock',
        TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody]
      change
        Simulation.Interaction.bind
            (Simulation.Interaction.done
              (Except.ok (target, TypedCfgCompiler.Shape.procExit proc)))
            (fun result =>
              if result.2 = TypedCfgCompiler.Shape.procExit proc then
                match TypedCfg.Block.runTermChecked
                    (TypedCfgCompiler.Shape.procExit proc)
                    (.returnDispatch proc.retc sites) result.1 with
                | .ok outcome => Simulation.Interaction.pure outcome
                | .error err => Simulation.Interaction.error err
              else
                Simulation.Interaction.done
                  (Except.error (.InvalidInstruction : EVMException))) =
          Simulation.Interaction.pure
            (TypedCfg.Block.runTerm (TypedCfgCompiler.Shape.procExit proc)
              (.returnDispatch proc.retc sites) target)
      simp [Simulation.Interaction.bind]
    -- Reduce `runTerm` of the return-dispatch terminator using the exit depth + token facts.
    rw [hStep] at hExec
    simp only [TypedCfg.Block.runTerm,
      TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit] at hExec
    simp only [ne_eq, not_true_eq_false, ite_false, hGet] at hExec
    cases tokens with
    | nil =>
        -- No pending return token ⇒ `.invalid`, contradicting the jump.
        simp only [List.head?_nil] at hExec
        simp only [Simulation.Interaction.pure] at hExec
        cases hExec
    | cons token rest =>
        simp only [List.head?_cons] at hExec
        cases hFind : TypedCfg.Block.ReturnSite.findTarget? token sites with
        | none =>
            rw [hFind] at hExec
            simp only [Simulation.Interaction.pure] at hExec
            cases hExec
        | some tgt =>
            rw [hFind] at hExec
            simp only [Simulation.Interaction.pure] at hExec
            cases hExec
            obtain ⟨site, hMem, hSiteProc, hSiteTok, hSiteRet⟩ :=
              findTarget?_returnSitesFor_inv (name := proc.name) (calls := context.calls)
                (by rw [← hSitesDef]; exact hFind)
            exact
              ⟨site, rest, hMem, hSiteProc, by rw [hSiteTok], hSiteRet.symm, rfl⟩

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**The dispatch arm of the `hInv` `openStep`-jump invariant** (`block_category`'s third arm).

From the entry `realizedWitness` at a procedure-exit block (supplying the exit `StateRel`
`bodyState`/`tokens` and the `procExit` `SourceFrameFits`) and any concrete first jump `hExec`,
this lands the successor `realizedWitness cfg next state'` — modulo the residual, genuinely
source-frame-safety-dependent finisher `hFinish`.

The plumbing is fully discharged here:
* the openStep-jump inversion `dispatch_openStep_jump_inv` recovers the matching return
  `site ∈ context.calls`, `site.procName = proc.name`, and `tokens = site.token :: rest`;
* `dispatch_popReturn?_of_stateRel` derives the return-frame pop `hPop` from the (now
  `cons`-form) exit `StateRel`;
* `realizedWitness_of_dispatch_jump` relays the caller `StateRel` at `state'`.

`hFinish` isolates *exactly* the two deferred obligations the entry `realizedWitness` does not
carry — supplied, at the eventual capstone assembly, from `source.FrameSafe` and the call-site
provenance: (1) the popped frame reattaches (`attachReturns?`) and has `retc = proc.retc`
(procedure-identity / frame-safety), and (2) the caller continuation `site.returnLabel` expects
a shape the restored caller frame fits (`LabelShape` + `SourceFrameFits`).  This mirrors the
additive threaded-finisher discipline of `realizedWitness_of_caseEntryPop_dispatch` /
`realizedWitness_of_procAdapter_dispatch`. -/
theorem realizedWitness_of_dispatch_arm
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? proc.name source.procs = some proc)
    {bodyState : RunState} {tokens : List Word} {target state' : EVMState}
    {next : Assembly.Label} {transcript : Simulation.Interaction.Transcript}
    (hRel : TypedCfgPreservation.StateRel bodyState tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procExit proc) bodyState.evm.stack.length)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg (ProcLabel.exit proc.name) target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hFinish :
      ∀ (site : TypedCfgCompiler.DispatchSite) (rest : List Word)
        (frame : ReturnDest) (returns : List ReturnDest),
        site ∈ context.calls →
        site.procName = proc.name →
        tokens = site.token :: rest →
        bodyState.returns = frame :: returns →
        ∃ (stack : EvmYul.Stack Word) (callerInput : TypedCfg.Shape),
          Structured.StackFrame.attachReturns? frame bodyState.evm.stack = some stack ∧
          frame.retc = proc.retc ∧
          TypedCfgPreservation.LabelShape cfg site.returnLabel callerInput ∧
          TypedCfgCompiler.Shape.SourceFrameFits callerInput stack.length) :
    realizedWitness cfg next state' := by
  obtain ⟨site, rest, hMem, hSiteProc, hTok, hNext, _hState'⟩ :=
    dispatch_openStep_jump_inv context hLookup hRel hFits hExec
  subst hTok
  obtain ⟨frame, returns, hReturns, hPop⟩ :=
    dispatch_popReturn?_of_stateRel hRel
  obtain ⟨stack, callerInput, hAttach, hRetc, hLabelShape, hFitsCaller⟩ :=
    hFinish site rest frame returns hMem hSiteProc rfl hReturns
  exact
    InteractionRealizedWitnessSuccessor.realizedWitness_of_dispatch_jump
      context hLookup hSiteProc hMem hRel hPop hAttach hRetc hExec
      hLabelShape (callerInput := callerInput) hFitsCaller
