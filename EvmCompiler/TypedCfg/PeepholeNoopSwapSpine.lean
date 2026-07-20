import EvmCompiler.TypedCfg.PeepholeNoopSwapProgram
import EvmCompiler.TypedCfg.PeepholeNoopSwapConj

/-!
# `normalizeProgram` preserves whole-program `WellTyped` (session-59, item 1)

The Route-3 analogue of `PeepholeSpine`'s `peepholeProgram_wellTyped`.  The
normalization (`swap d ; z* ; swap d → (remap d z)*`) touches only straight-line
block bodies; labels, terminators and block input/output shapes are untouched, so:

* `labelShape?` is invariant (block lookup + `.input` both preserved), hence
  `Terminator.type?` (which reads only `program.labelShape?`) is invariant;
* each block body keeps its `bodyType?` (`normalizeBody_bodyType?`);
* `LabelsUnique` / `EmittedLabelsUnique` / entry existence are label-only
  predicates, all preserved.

This is the ingredient the peephole leg of the combined transform
`peepholeProgram (normalizeProgram cfg)` needs for its `hWellTyped` after the
normalization step (session-59 splice).
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-- The normalization preserves the per-label input shape index. -/
theorem labelShape?_normalizeProgram (program : Program) (label : Label) :
    (normalizeProgram program).labelShape? label =
      program.labelShape? label := by
  unfold Program.labelShape?
  rw [findBlock?_normalizeProgram]
  cases program.findBlock? label with
  | none => rfl
  | some block => rfl

/-- `Terminator.type?` reads only `labelShape?`, so it is normalize-invariant. -/
theorem terminator_type?_normalizeProgram (program : Program) (shape : Shape)
    (term : Terminator) :
    term.type? (normalizeProgram program) shape =
      term.type? program shape := by
  unfold Terminator.type?
  rw [show (normalizeProgram program).labelShape? = program.labelShape? from
    funext (labelShape?_normalizeProgram program)]

/-- Each normalized block stays `WellTyped` in the normalized program. -/
theorem block_wellTyped_normalizeProgram {program : Program} {block : Block}
    (hTyped : block.WellTyped program) :
    (normalizeBlock block).WellTyped (normalizeProgram program) := by
  refine ⟨?_, ?_⟩
  · simp only [normalizeBlock_body, normalizeBlock_input, normalizeBlock_output]
    exact normalizeBody_bodyType? _ _ _ hTyped.1
  · simp only [normalizeBlock_output, normalizeBlock_term]
    rw [terminator_type?_normalizeProgram]
    exact hTyped.2

/-- The normalization preserves the emitted-label multiset (labels + terminator
defined labels are untouched). -/
theorem emittedLabels_normalizeProgram (program : Program) :
    (normalizeProgram program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [normalizeProgram_blocks, List.flatMap_map]
  rfl

/-- The normalization preserves whole-program `LabelsUnique`. -/
theorem labelsUnique_normalizeProgram {program : Program}
    (h : program.LabelsUnique) :
    (normalizeProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [normalizeProgram_blocks]
  rw [List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [normalizeBlock_label] using hab

/-- **The normalization preserves whole-program `WellTyped`.** -/
theorem normalizeProgram_wellTyped {program : Program}
    (h : program.WellTyped) :
    (normalizeProgram program).WellTyped := by
  obtain ⟨hUnique, hBlocks, hEntry, hEmitted⟩ := h
  refine ⟨labelsUnique_normalizeProgram hUnique, ?_, ?_, ?_⟩
  · -- AllBlocksTyped
    unfold Program.AllBlocksTyped
    rw [normalizeProgram_blocks, List.forall_iff_forall_mem]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    exact block_wellTyped_normalizeProgram
      ((List.forall_iff_forall_mem.mp hBlocks) b0 hb0)
  · -- entry block exists
    rw [normalizeProgram_entry, findBlock?_normalizeProgram]
    cases hFind : program.findBlock? program.entry with
    | none => exact absurd hFind hEntry
    | some block => simp
  · -- EmittedLabelsUnique
    unfold Program.EmittedLabelsUnique
    rw [emittedLabels_normalizeProgram]
    exact hEmitted

end Peephole
end TypedCfg
end EvmCompiler
