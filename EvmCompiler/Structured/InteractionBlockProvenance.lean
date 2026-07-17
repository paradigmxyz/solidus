import EvmCompiler.Structured.InteractionRealizedWitnessSuccessor

/-!
# Per-entry block-provenance substrate (obligation (1) at the OIC splice)

Session 29 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-28).

The route-B master lever
`AllEntriesRealized.of_openStep_invariant`
(`TypedCfg/InteractionEntryRealized.lean:271`) reduces the whole peephole endgame
to a single **global** `openStep`-jump invariant

    hInv : realizedWitness cfg e t →
           Executes (openStep cfg e t) transcript (.ok (.jump n s)) →
           realizedWitness cfg n s.

Sessions 27/28 banked the three per-terminator *successor legs*
(`realizedWitness_of_{branch,pure,dispatch}_jump`,
`InteractionRealizedWitnessSuccessor.lean`) that discharge the *conclusion*
GIVEN the source coupling at `e`.  The sole remaining hole (obligation (1)) is
**per-entry source-construct provenance**: at an ARBITRARY reached entry `e` one
must first recover which source construct compiled to the block at `e`, so as to
produce the coupling the successor legs consume.  `realizedWitness` carries the
child `StateRel`/`SourceFrameFits` but neither the coupling nor the construct
identity; recovering it is a decomposition of `cfg.findBlock? e` over the
`GeneratedContext` block layout
(`Core.lean:3387`: `cfg.blocks = main.blocks ++ procBlocks ++ dispatchBlocks …
++ [programEnd]`).

This module lands the **reverse-classification substrate** of that decomposition
(the first, unavoidable move of the `block_owner` provenance recovery, absent from
the tower until now — the existing `GeneratedContext` `findBlock?` lemmas are all
*forward*, category ⟶ block):

* `block_category` — from `cfg.findBlock? label = some block` under a
  `GeneratedContext`, classify `block` into exactly one of the four generated
  categories (main body / proc body / dispatch / programEnd).
* `programEnd_openStep_eq` / `programEnd_openStep_no_jump` — the programEnd
  category discharges `hInv` cleanly and *unconditionally*: its terminator is
  `.halt .stop`, so its `openStep` yields `.done (.ok (.halt .stop …))` and can
  never `Executes`-produce a `.jump` outcome.  This closes the programEnd arm of
  the eventual `hInv` case split (no source coupling needed there).

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace Program
namespace GeneratedContext

/-- The programEnd block generated for a `GeneratedContext` (its explicit form as
pinned by `cfgEq`). -/
def programEndBlockOf
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    TypedCfg.Block :=
  { label := ProcLabel.programEnd
    input := context.main.fallthrough?.getD TypedCfg.Shape.caller
    body := []
    output := context.main.fallthrough?.getD TypedCfg.Shape.caller
    term := .halt .stop }

/--
**Reverse block classification under a `GeneratedContext`.**

Every block the CFG's `findBlock?` returns is exactly one of the four generated
categories: a main-body block, a procedure-body block, a dispatch block, or the
single terminal `programEnd` block.  This is the first move of the per-entry
source-construct provenance recovery the `hInv` invariant needs: it tells the
invariant's proof *which* compile fact governs the jumped-from block at `e`.

Proof: `findBlock?` returns a member (`List.mem_of_find?_eq_some`); rewrite
`cfg.blocks` by `cfgEq` and split the four appended segments.
-/
theorem block_category
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {label : Assembly.Label} {block : TypedCfg.Block}
    (hFind : cfg.findBlock? label = some block) :
    block ∈ context.main.blocks ∨
      block ∈ context.procBlocks ∨
      block ∈
        TypedCfgCompiler.dispatchBlocks source.procs
          (context.main.calls ++ context.procCalls) ∨
      block = context.programEndBlockOf := by
  have hMem : block ∈ cfg.blocks :=
    List.mem_of_find?_eq_some hFind
  rw [context.cfgEq] at hMem
  simp only [TypedCfg.Program.blocks, List.mem_append, List.mem_singleton]
    at hMem
  rcases hMem with ((hMain | hProc) | hDispatch) | hEnd
  · exact Or.inl hMain
  · exact Or.inr (Or.inl hProc)
  · exact Or.inr (Or.inr (Or.inl hDispatch))
  · exact Or.inr (Or.inr (Or.inr hEnd))

/--
The programEnd block's `openStep` reduces to a single completed `.halt .stop`
outcome: its body is empty and its terminator is `.halt .stop`, so no interaction
requests are issued and control never jumps.
-/
theorem programEnd_openStep_eq
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    (t : EVMState) :
    TypedCfg.InteractionSemantics.Program.openStep cfg ProcLabel.programEnd t =
      .done (.ok (TypedCfg.Outcome.halt .stop t)) := by
  unfold TypedCfg.InteractionSemantics.Program.openStep
    TypedCfg.Control.Program.step
  rw [context.programEndBlock]
  simp only [TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody,
    TypedCfg.Block.runTermChecked, TypedCfg.Block.runTerm]
  show Simulation.Interaction.bind
      (Simulation.Interaction.pure
        (t, context.main.fallthrough?.getD TypedCfg.Shape.caller)) _ = _
  rw [Simulation.Interaction.pure, Simulation.Interaction.bind_done_ok,
    if_pos rfl]
  rfl

/--
**programEnd arm of the `hInv` invariant, discharged unconditionally.**

Because `programEnd_openStep_eq` shows the programEnd block's `openStep` is a
completed `.halt .stop` outcome, it can never `Executes`-produce a `.jump`, so the
`hInv` obligation at a programEnd entry is vacuous — no source coupling is
required there.  (The eventual `hInv` proof classifies the entry with
`block_category`; this closes the programEnd case, leaving only the three
compiled-construct categories to the source-coupled successor legs.)
-/
theorem programEnd_openStep_no_jump
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {t : EVMState} {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          cfg ProcLabel.programEnd t)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    False := by
  rw [programEnd_openStep_eq context] at hExec
  cases hExec

end GeneratedContext
end Program
end TypedCfgPreservation
end Structured
end EvmCompiler
