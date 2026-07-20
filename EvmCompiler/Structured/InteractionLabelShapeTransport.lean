import EvmCompiler.Structured.TypedCfgPreservation.GeneratedBoundary

/-!
# Successor `LabelShape` transport — the WellTyped edge-extraction half

Session 37 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-36 frontier item 2).

The route-B `hInv` suppliers (`InteractionRealizedWitnessSuccessor.lean`) each consume
`hLabelShape : LabelShape cfg next restShape` for the *target* block `next` the current
block jumps to.  `LabelShape` (`GeneratedBoundary.lean:11`) is
`∃ block, cfg.findBlock? next = some block ∧ block.input = restShape` — a STRICT input
equality, which `realizedWitness_of_stateRel` (`InteractionBoundedOwnerRealized.lean:334`)
needs to rewrite the child `SourceFrameFits` onto the ambient block's declared input.

Two kinds of successor arise at each classified block:

* **Internal successors** — blocks that live in the *same* construct's compile `result`
  (e.g. an `if`'s body-entry `trueLabel`).  Their exact `LabelShape` is already available
  from the disjunct's own compile fact via `LabelShape.of_compileBlockFuel?` /
  `of_hasEntry` restricted to the sub-result (the forward proofs use exactly this,
  cf. `InteractionBranchPreservation.lean:543`).

* **The external `regular` successor** — the block the construct's fallthrough jumps to,
  which is NOT in the construct's own result.  Its exact `LabelShape` is a
  *generation-threaded* fact (the block declared at `regular` was generated with input =
  this construct's fallthrough output); the forward preservation proofs never needed it
  because they STOP at `regular` (recursive boundary), whereas the whole-program route-B
  invariant continues into it.  This is the genuine sticking point of sessions 26–35.

This module banks the **WellTyped edge-extraction** building block, which every
transport route needs regardless of how the exact shape is finally pinned: from the
ambient `cfg.WellTyped` (all blocks well-typed) alone, a block's `.jump`/`.jumpi`
terminator target is guaranteed to be a block *present in `cfg`* whose input is
`Shape.compatible` with the source block's output.  This supplies the **existence** of
the target block (the `∃ block, findBlock? … = some block` half of `LabelShape`) plus the
`compatible` relation; the remaining `compatible ⟶ exact` step is the generation-threaded
residual documented in the progress note.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace LabelShape

/--
**Ambient block extraction for a well-typed block.**  Any block that `cfg.findBlock?`
returns is a member of `cfg.blocks` and therefore well-typed under `cfg.WellTyped`. -/
theorem block_wellTyped_of_findBlock?
    {cfg : TypedCfg.Program} {label : Assembly.Label} {block : TypedCfg.Block}
    (hWT : cfg.WellTyped)
    (hFind : cfg.findBlock? label = some block) :
    block.WellTyped cfg := by
  have hMem : block ∈ cfg.blocks := by
    unfold TypedCfg.Program.findBlock? at hFind
    exact List.mem_of_find?_eq_some hFind
  exact List.forall_iff_forall_mem.mp hWT.2.1 block hMem

/--
**WellTyped `.jump` edge extraction.**  A block found in a well-typed `cfg` whose
terminator is `.jump target` guarantees the target names a block *present in `cfg`* whose
input is `Shape.compatible` with the source block's output.  Delivers the *existence* half
of `LabelShape cfg target …` (a concrete `LabelShape cfg target targetShape`) plus the
`compatible` relation to the source output. -/
theorem edge_jump_of_wellTyped
    {cfg : TypedCfg.Program} {label target : Assembly.Label}
    {block : TypedCfg.Block}
    (hWT : cfg.WellTyped)
    (hFind : cfg.findBlock? label = some block)
    (hTerm : block.term = .jump target) :
    ∃ targetShape,
      LabelShape cfg target targetShape ∧
        block.output.compatible targetShape = true := by
  have hBlockWT := block_wellTyped_of_findBlock? hWT hFind
  have hType := hBlockWT.2
  rw [hTerm] at hType
  simp only [TypedCfg.Terminator.type?, TypedCfg.Terminator.typeWith?] at hType
  cases hLS : cfg.labelShape? target with
  | none => rw [hLS] at hType; simp at hType
  | some targetShape =>
      rw [hLS] at hType
      simp only [Option.bind_eq_bind, Option.bind_some] at hType
      by_cases hCompat : block.output.compatible targetShape = true
      · obtain ⟨targetBlock, hTargetFind, hTargetInput⟩ :=
          Option.map_eq_some_iff.mp hLS
        exact ⟨targetShape, ⟨targetBlock, hTargetFind, hTargetInput⟩, hCompat⟩
      · simp only [hCompat, if_false] at hType
        exact absurd hType (by simp)

end LabelShape
end TypedCfgPreservation
end Structured
end EvmCompiler
