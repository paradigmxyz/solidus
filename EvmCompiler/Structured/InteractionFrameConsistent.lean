import EvmCompiler.Structured.InteractionDispatchInversion

/-!
# The per-witness source frame-consistency invariant (session 46)

Session 46 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-45 frontier item 1).

Session 45 proved (concrete counterexample, `dispatch_hFinish_of_frameConsistent`) that the
bare `realizedWitness` predicate is too weak to close the dispatch arm of the `hInv`
`openStep`-jump invariant: `StateRel`/`realizeStack` place NO constraint on a ghost return
frame's `retc`, so a `realizedWitness` witness need not have `attachReturns?`-reattachable
return frames.  The fix is to **strengthen the realized predicate** with a per-witness source
frame-consistency invariant that travels alongside the source witness.

This module defines that invariant and the strengthened predicate, plus the foundational
plumbing (projection to `realizedWitness`, the uniform `realizedWitnessFC_of_stateRel`
packager, the entry seed at empty return frames, the pop/tail weakening, and the
`AllEntriesRealized` monotone weakening that recovers the bare `realizedWitness` consumer at
the end).

**`FrameConsistent` is a function of `(source.returns, tokens)` and the STATIC context only**
(never the runtime EVM stack): atom (ii)'s frame-fit is stated at `frame.retc +
frame.callerStack.length`, not `bodyState.evm.stack.length + …` — the two coincide at a
`procExit proc` witness because there `bodyState.evm.stack.length = proc.retc = frame.retc`.
This stack-independence is what makes the seven non-call `hInv` legs transport the invariant
with no work (their child witness has the SAME `returns`/`tokens`, only a shifted EVM stack).

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome
  (realizedWitness realizedWitness_of_stateRel)

/--
**Per-frame source frame-consistency.**

A single pending ghost return frame `frame`, realized by return token `token`, is
*head-consistent* when: for every registered call site whose return token is `token` and
whose callee (`site.procName` resolved in `sourceProgram.procs`) is `proc`,

* the frame's return count matches the callee's (`frame.retc = proc.retc` —
  procedure-identity), and
* the recorded return continuation `site.returnLabel` expects a shape the restored caller
  frame (return vector reattached onto `frame.callerStack`) fits, at the stack length
  `frame.retc + frame.callerStack.length`.

These are exactly the two irreducible source-frame-safety atoms
`dispatch_hFinish_of_frameConsistent` reduces the dispatch finisher to — stated
stack-independently (see the module note).  Quantifying over *all* matching sites (rather than
selecting one) means the dispatch arm can consume it at whatever site the runtime dispatch
selects, with no token-uniqueness reasoning here. -/
def FrameHeadConsistent
    (sourceProgram : Structured.Program)
    (cfg : TypedCfg.Program)
    (calls : List TypedCfgCompiler.DispatchSite)
    (frame : ReturnDest) (token : Word) : Prop :=
  ∀ (site : TypedCfgCompiler.DispatchSite) (proc : Structured.Proc),
    site ∈ calls →
    site.token = token →
    Structured.ProcList.lookup? site.procName sourceProgram.procs = some proc →
    frame.retc = proc.retc ∧
      ∃ callerInput : TypedCfg.Shape,
        TypedCfgPreservation.LabelShape cfg site.returnLabel callerInput ∧
        TypedCfgCompiler.Shape.SourceFrameFits callerInput
          (frame.retc + frame.callerStack.length)

/--
**Whole-activation source frame-consistency.**

Lockstep recursion over the ghost return frames `source.returns` and the realization tokens
`tokens`: every pending frame is `FrameHeadConsistent`.  (Mismatched lengths never arise under
a `StateRel` witness — `realizeStack` forces equal lengths — so the off-diagonal cases are
`True`.) -/
def FrameConsistent
    (sourceProgram : Structured.Program)
    (cfg : TypedCfg.Program)
    (calls : List TypedCfgCompiler.DispatchSite) :
    List ReturnDest → List Word → Prop
  | [], [] => True
  | frame :: returns, token :: tokens =>
      FrameHeadConsistent sourceProgram cfg calls frame token ∧
        FrameConsistent sourceProgram cfg calls returns tokens
  | [], _ :: _ => True
  | _ :: _, [] => True

@[simp] theorem FrameConsistent_nil_nil
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite} :
    FrameConsistent sourceProgram cfg calls [] [] = True := rfl

theorem FrameConsistent_cons_cons
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {frame : ReturnDest} {returns : List ReturnDest}
    {token : Word} {tokens : List Word} :
    FrameConsistent sourceProgram cfg calls (frame :: returns) (token :: tokens) =
      (FrameHeadConsistent sourceProgram cfg calls frame token ∧
        FrameConsistent sourceProgram cfg calls returns tokens) := rfl

/-- Nil activations are vacuously consistent (the entry-seed case). -/
theorem FrameConsistent.nil
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite} :
    FrameConsistent sourceProgram cfg calls [] [] := trivial

/-- **Pop/tail weakening.**  Dropping the head frame (the dispatch pop) preserves
consistency: the residual caller activation `returns`/`tokens` is a suffix of a consistent
one. -/
theorem FrameConsistent.tail
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {frame : ReturnDest} {returns : List ReturnDest}
    {token : Word} {tokens : List Word}
    (h : FrameConsistent sourceProgram cfg calls (frame :: returns) (token :: tokens)) :
    FrameConsistent sourceProgram cfg calls returns tokens :=
  (FrameConsistent_cons_cons.mp h).2

/-- **Push/head construction.**  Prepending a head-consistent frame preserves consistency
(the callHead push). -/
theorem FrameConsistent.cons
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {frame : ReturnDest} {returns : List ReturnDest}
    {token : Word} {tokens : List Word}
    (hHead : FrameHeadConsistent sourceProgram cfg calls frame token)
    (hRest : FrameConsistent sourceProgram cfg calls returns tokens) :
    FrameConsistent sourceProgram cfg calls (frame :: returns) (token :: tokens) :=
  FrameConsistent_cons_cons.mpr ⟨hHead, hRest⟩

/--
**The strengthened realized predicate** (frontier item 1).

`realizedWitness` enriched with the per-witness `FrameConsistent` invariant on the same
existential source witness.  The dispatch arm reads the head frame's `FrameHeadConsistent` off
this (feeding `hCons`); each `hInv` leg re-exhibits it for its child witness (trivially for the
seven non-call legs, whose child `returns`/`tokens` are unchanged; via `FrameConsistent.cons` /
`FrameConsistent.tail` for callHead / dispatch). -/
def realizedWitnessFC
    (sourceProgram : Structured.Program)
    (cfg : TypedCfg.Program)
    (calls : List TypedCfgCompiler.DispatchSite) :
    Assembly.Label → EVMState → Prop :=
  fun label state =>
    ∃ (source : RunState) (tokens : List Word) (block : TypedCfg.Block),
      cfg.findBlock? label = some block ∧
      TypedCfgPreservation.StateRel source tokens state ∧
      TypedCfgCompiler.Shape.SourceFrameFits block.input source.evm.stack.length ∧
      FrameConsistent sourceProgram cfg calls source.returns tokens

/-- **Projection.**  The strengthened predicate forgets its frame-consistency conjunct to
recover the bare `realizedWitness` — the free weakening the final `AllEntriesRealized`
consumer needs. -/
theorem realizedWitnessFC.realizedWitness
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {label : Assembly.Label} {state : EVMState}
    (h : realizedWitnessFC sourceProgram cfg calls label state) :
    realizedWitness cfg label state := by
  obtain ⟨source, tokens, block, hFind, hRel, hFits, _hFC⟩ := h
  exact ⟨source, tokens, block, hFind, hRel, hFits⟩

/--
**Uniform strengthened entry-witness packager** (the `realizedWitness_of_stateRel` sibling).

Given a fragment's `LabelShape` (the ambient block at `entry` expects `input`), a child
`StateRel`, its frame-fit, AND the frame-consistency of `(source.returns, tokens)`, package the
strengthened witness `realizedWitnessFC … entry target`.  Every `hInv` leg lands its child
witness through this. -/
theorem realizedWitnessFC_of_stateRel
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hLabelShape : TypedCfgPreservation.LabelShape cfg entry input)
    (hStateRel : TypedCfgPreservation.StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hFC : FrameConsistent sourceProgram cfg calls source.returns tokens) :
    realizedWitnessFC sourceProgram cfg calls entry target := by
  obtain ⟨block, hFind, hInputEq⟩ := hLabelShape
  refine ⟨source, tokens, block, hFind, hStateRel, ?_, hFC⟩
  rw [hInputEq]
  exact hFits

/-- **Entry seed.**  At the program entry the source activation is empty
(`RunState.initial`), so the frame-consistency conjunct is vacuous and the strengthened seed
reduces to the bare entry witness. -/
theorem realizedWitnessFC_of_stateRel_nil
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hLabelShape : TypedCfgPreservation.LabelShape cfg entry input)
    (hStateRel : TypedCfgPreservation.StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hReturns : source.returns = [])
    (hTokens : tokens = []) :
    realizedWitnessFC sourceProgram cfg calls entry target :=
  realizedWitnessFC_of_stateRel hLabelShape hStateRel hFits
    (by rw [hReturns, hTokens]; exact FrameConsistent.nil)

open TypedCfg.InteractionSemantics.Program (AllEntriesRealized)

/-- **Monotone weakening of `AllEntriesRealized` in the realized predicate.**  Realizing every
reached entry under a stronger predicate realizes them all under any weaker one.  This is the
final step that turns the strengthened `AllEntriesRealized … (realizedWitnessFC …)` (the form
the invariant produces) back into the bare `AllEntriesRealized … (realizedWitness cfg)` the
downstream (Step B) consumer expects. -/
theorem AllEntriesRealized.weaken
    {cfg : TypedCfg.Program} {policy : InteractionControlPreservation.OpenOutcome.StopPolicy} {fuel : Nat}
    {entry : Assembly.Label} {target : EVMState}
    {realized realized' : Assembly.Label → EVMState → Prop}
    (hle : ∀ label state, realized label state → realized' label state)
    (h : AllEntriesRealized cfg policy fuel entry target realized) :
    AllEntriesRealized cfg policy fuel entry target realized' :=
  fun label state hReach => hle label state (h label state hReach)

/-- Specialization: weaken the strengthened predicate's `AllEntriesRealized` to the bare
`realizedWitness cfg`. -/
theorem allEntriesRealized_realizedWitness_of_FC
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy} {fuel : Nat}
    {entry : Assembly.Label} {target : EVMState}
    (h :
      AllEntriesRealized cfg policy fuel entry target
        (realizedWitnessFC sourceProgram cfg calls)) :
    AllEntriesRealized cfg policy fuel entry target (realizedWitness cfg) :=
  AllEntriesRealized.weaken
    (fun _label _state hR => realizedWitnessFC.realizedWitness hR) h

end InteractionFrameConsistent
end Structured
end EvmCompiler
