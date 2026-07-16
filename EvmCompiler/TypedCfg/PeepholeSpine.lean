import EvmCompiler.TypedCfg.PeepholeProgram

/-!
# Peephole preserves whole-program `WellTyped`

Milestone (f): `peepholeProgram` preserves `Program.WellTyped`.  The peephole
touches only straight-line block bodies (`push v ; pop` cancellation); labels,
terminators and block input/output shapes are untouched, so:

* `labelShape?` is invariant (block lookup + `.input` both preserved), hence
  `Terminator.type?` (which reads only `program.labelShape?`) is invariant;
* each block body keeps its `bodyType?` (`peepholeBody_bodyType?`);
* `LabelsUnique` / `EmittedLabelsUnique` / entry existence are label-only
  predicates, all preserved.

This is what makes `(peepholeProgram cfg).compileCertified?` succeed whenever
`cfg`'s does, so wiring the peephole into the compile spine keeps every corpus
contract compiling.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-- The peephole preserves the per-label input shape index. -/
theorem labelShape?_peepholeProgram (program : Program) (label : Label) :
    (peepholeProgram program).labelShape? label =
      program.labelShape? label := by
  unfold Program.labelShape?
  rw [findBlock?_peepholeProgram]
  cases program.findBlock? label with
  | none => rfl
  | some block => rfl

/-- `Terminator.type?` reads only `labelShape?`, so it is peephole-invariant. -/
theorem terminator_type?_peepholeProgram (program : Program) (shape : Shape)
    (term : Terminator) :
    term.type? (peepholeProgram program) shape =
      term.type? program shape := by
  unfold Terminator.type?
  rw [show (peepholeProgram program).labelShape? = program.labelShape? from
    funext (labelShape?_peepholeProgram program)]

/-- Each peepholed block stays `WellTyped` in the peepholed program. -/
theorem block_wellTyped_peepholeProgram {program : Program} {block : Block}
    (hTyped : block.WellTyped program) :
    (peepholeBlock block).WellTyped (peepholeProgram program) := by
  refine ⟨?_, ?_⟩
  · simp only [peepholeBlock_body, peepholeBlock_input, peepholeBlock_output]
    rw [peepholeBody_bodyType?]
    exact hTyped.1
  · simp only [peepholeBlock_output, peepholeBlock_term]
    rw [terminator_type?_peepholeProgram]
    exact hTyped.2

/-- The peephole preserves the emitted-label multiset (labels + terminator
defined labels are untouched). -/
theorem emittedLabels_peepholeProgram (program : Program) :
    (peepholeProgram program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [peepholeProgram_blocks, List.flatMap_map]
  rfl

/-- The peephole preserves whole-program `LabelsUnique`. -/
theorem labelsUnique_peepholeProgram {program : Program}
    (h : program.LabelsUnique) :
    (peepholeProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [peepholeProgram_blocks]
  rw [List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [peepholeBlock_label] using hab

/-- **The peephole preserves whole-program `WellTyped`.** -/
theorem peepholeProgram_wellTyped {program : Program}
    (h : program.WellTyped) :
    (peepholeProgram program).WellTyped := by
  obtain ⟨hUnique, hBlocks, hEntry, hEmitted⟩ := h
  refine ⟨labelsUnique_peepholeProgram hUnique, ?_, ?_, ?_⟩
  · -- AllBlocksTyped
    unfold Program.AllBlocksTyped
    rw [peepholeProgram_blocks, List.forall_iff_forall_mem]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    exact block_wellTyped_peepholeProgram
      ((List.forall_iff_forall_mem.mp hBlocks) b0 hb0)
  · -- entry block exists
    rw [peepholeProgram_entry, findBlock?_peepholeProgram]
    cases hFind : program.findBlock? program.entry with
    | none => exact absurd hFind hEntry
    | some block => simp
  · -- EmittedLabelsUnique
    unfold Program.EmittedLabelsUnique
    rw [emittedLabels_peepholeProgram]
    exact hEmitted

end Peephole
end TypedCfg
end EvmCompiler
