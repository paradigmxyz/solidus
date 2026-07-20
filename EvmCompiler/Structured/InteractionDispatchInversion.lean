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
