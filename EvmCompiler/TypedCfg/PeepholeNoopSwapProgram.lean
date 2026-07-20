import EvmCompiler.TypedCfg.PeepholeNoopSwapRuntime
import EvmCompiler.TypedCfg.PeepholeProgram

/-!
# `normalizeBody` as a block / whole-program transform (session-58, step 4)

Lifts the open runtime congruence `openRunBody_normalize_congr` to the block level
(`Block.openRun_normalize_runtimeRel`) and to the one-step whole-program level
(`openStep_normalize_congr`), plus the `normalizeBlock` / `normalizeProgram`
packaging and the `ProgramCounterIndependent` preservation.  These are the exact
analogues of `PeepholeProgram`'s `peepholeBlock` / `peepholeProgram` /
`openStep_peephole_congr`, threaded through the Route-3 window transform.

Still ahead of the splice (documented in PEEPHOLE_PROGRESS §Session-58 frontier):
the SOURCE-THREADED fuel-bounded congruences (`openRunN{,Prefix}` carrying
`realizedWitnessFC`) and the `fuelBudget_normalizeProgram_le` bound, which the five
OIC consumption sites require, then rewiring `StackArtifact.compile?` to
`peepholeProgram (normalizeProgram cfg)`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-! ## `ProgramCounterIndependent` preservation -/

/-- Every zero-width instruction is `ProgramCounterIndependent` (its effects are
empty, independent of its position parameters). -/
theorem pcIndependent_of_zeroWidth {z : Instr} (h : isZeroWidth z = true) :
    z.ProgramCounterIndependent := by
  cases z <;>
    simp_all [isZeroWidth, Instr.ProgramCounterIndependent, Instr.effects]

/-- The normalization preserves whole-body `ProgramCounterIndependent`. -/
theorem forall_pcIndependent_normalize :
    ∀ (body : List Instr), body.Forall Instr.ProgramCounterIndependent →
      (normalizeBody body).Forall Instr.ProgramCounterIndependent := by
  intro body
  induction body using normalizeBody.induct with
  | case1 => intro _; simp [normalizeBody]
  | case2 d rest d' rest' hTail hGuard ih =>
      intro h
      obtain ⟨hdd, hSafe⟩ := hGuard
      subst hdd
      have happ : (leadingZeroWidth rest).1 ++ Instr.swap d :: rest' = rest := by
        conv_rhs => rw [← leadingZeroWidth_append rest]
        rw [hTail]
      have hRestPC : rest.Forall Instr.ProgramCounterIndependent :=
        forall_pcIndependent_tail_of_cons h
      have hrest'PC : rest'.Forall Instr.ProgramCounterIndependent := by
        rw [List.forall_iff_forall_mem] at hRestPC ⊢
        intro x hx; apply hRestPC x
        rw [← happ]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
      rw [normalizeBody_fire d rest rest' hTail hSafe, List.forall_iff_forall_mem]
      intro x hx
      rw [List.mem_append] at hx
      cases hx with
      | inl hxmap =>
          obtain ⟨z0, hz0, hz0eq⟩ := List.mem_map.mp hxmap
          subst hz0eq
          apply pcIndependent_of_zeroWidth
          rw [isZeroWidth_remapZeroWidth]
          exact remapSafe_isZeroWidth (List.all_eq_true.mp hSafe z0 hz0)
      | inr hxrest =>
          exact (List.forall_iff_forall_mem.mp (ih hrest'PC)) x hxrest
  | case3 d rest d' rest' hTail hGuard ih =>
      intro h
      have hunfold : normalizeBody (Instr.swap d :: rest)
          = Instr.swap d :: normalizeBody rest := by
        by_cases hdd : d = d'
        · have hUnsafe : (leadingZeroWidth rest).1.all RemapSafe = false := by
            by_contra hne; simp only [Bool.not_eq_false] at hne
            exact hGuard ⟨hdd, hne⟩
          exact normalizeBody_keep_unsafe d d' rest rest' hTail hUnsafe
        · exact normalizeBody_keep_swap d d' rest rest' hTail hdd
      rw [hunfold]
      rw [List.forall_cons] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | case4 d rest hNoTail ih =>
      intro h
      rw [normalizeBody_keep_noTail d rest (fun d' rest' hh => hNoTail d' rest' hh)]
      rw [List.forall_cons] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | case5 instr rest hNotSwap ih =>
      intro h
      rw [normalizeBody_cons_generic instr rest (fun d hh => hNotSwap d hh)]
      rw [List.forall_cons] at h ⊢
      exact ⟨h.1, ih h.2⟩

/-! ## Block-level packaging + congruence -/

/-- The normalized block: same label/input/output/terminator, window-cancelled
body. -/
def normalizeBlock (block : Block) : Block :=
  { block with body := normalizeBody block.body }

@[simp] theorem normalizeBlock_body (block : Block) :
    (normalizeBlock block).body = normalizeBody block.body := rfl
@[simp] theorem normalizeBlock_input (block : Block) :
    (normalizeBlock block).input = block.input := rfl
@[simp] theorem normalizeBlock_output (block : Block) :
    (normalizeBlock block).output = block.output := rfl
@[simp] theorem normalizeBlock_term (block : Block) :
    (normalizeBlock block).term = block.term := rfl
@[simp] theorem normalizeBlock_label (block : Block) :
    (normalizeBlock block).label = block.label := rfl

/-- **Open normalize block congruence.** Normalizing a `ProgramCounterIndependent`
block preserves `Block.openRun` up to `RuntimeOutcomeRel`, from the same input
state. -/
theorem Block.openRun_normalize_runtimeRel
    {program : Program} (block : Block) (state : EVMState)
    (hTyped : block.WellTyped program)
    (hIndependent : block.ProgramCounterIndependent)
    (hReal : StackRealizes block.input state) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Block.openRun (normalizeBlock block) state)
      (InteractionSemantics.Block.openRun block state) := by
  have hBody :=
    openRunBody_normalize_congr block.body block.input block.output
      state state hTyped.1 hIndependent hReal (SameRuntimeData.refl state)
  unfold InteractionSemantics.Block.openRun Control.Block.run
  simp only [normalizeBlock_body, normalizeBlock_input, normalizeBlock_output,
    normalizeBlock_term]
  apply Simulation.Interaction.Rel.bind hBody
  intro leftPair rightPair hPair
  rcases leftPair with ⟨leftAfter, leftShape⟩
  rcases rightPair with ⟨rightAfter, rightShape⟩
  rcases hPair with ⟨hAfter, hLeftShape, hRightShape⟩
  change SameRuntimeData leftAfter rightAfter at hAfter
  change leftShape = block.output at hLeftShape
  change rightShape = block.output at hRightShape
  subst leftShape; subst rightShape
  simp only [↓reduceIte]
  have hChecked :=
    InteractionCongruence.Block.runTermChecked_runtimeRel
      (shape := block.output) (term := block.term) hAfter
  cases hLeft : TypedCfg.Block.runTermChecked block.output block.term leftAfter <;>
    cases hRight : TypedCfg.Block.runTermChecked block.output block.term rightAfter <;>
    simp [hLeft, hRight] at hChecked ⊢
  all_goals exact .done hChecked

/-! ## Whole-program packaging + one-step congruence -/

/-- Normalize every block body of a program; the CFG (labels/terminators) is
untouched. -/
def normalizeProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map normalizeBlock }

@[simp] theorem normalizeProgram_entry (program : Program) :
    (normalizeProgram program).entry = program.entry := rfl

@[simp] theorem normalizeProgram_blocks (program : Program) :
    (normalizeProgram program).blocks = program.blocks.map normalizeBlock := rfl

/-- Block lookup commutes with the normalization (labels are preserved). -/
theorem findBlock?_normalizeProgram (program : Program) (label : Label) :
    (normalizeProgram program).findBlock? label =
      (program.findBlock? label).map normalizeBlock := by
  simp only [normalizeProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, normalizeBlock_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]; exact ih

/-- The normalization preserves whole-program `ProgramCounterIndependent`. -/
theorem normalizeProgram_programCounterIndependent {program : Program}
    (h : program.ProgramCounterIndependent) :
    (normalizeProgram program).ProgramCounterIndependent := by
  unfold Program.ProgramCounterIndependent at h ⊢
  rw [normalizeProgram_blocks]
  rw [List.forall_iff_forall_mem] at h ⊢
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨b0, hb0, rfl⟩ := hb
  have hb0Ind := h b0 hb0
  unfold Block.ProgramCounterIndependent at hb0Ind ⊢
  simpa only [normalizeBlock_body] using forall_pcIndependent_normalize _ hb0Ind

/-- **One-step whole-program normalize congruence.** The original program stepped
from `state1` and the normalized program stepped from any
`SameRuntimeData`-equivalent `state2` expose the same open interaction up to
`RuntimeOutcomeRel`. -/
theorem openStep_normalize_congr {program : Program} {label : Label}
    {state1 state2 : EVMState}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hReal2 : ∀ block, program.findBlock? label = some block →
      StackRealizes block.input state2)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openStep program label state1)
      (InteractionSemantics.Program.openStep (normalizeProgram program)
        label state2) := by
  unfold InteractionSemantics.Program.openStep Control.Program.step
  rw [findBlock?_normalizeProgram]
  cases hFind : program.findBlock? label with
  | none =>
      simp only [hFind, Option.map_none]
      exact .done (.ok (Outcome.RuntimeRel.invalid hRel))
  | some block =>
      simp only [hFind, Option.map_some]
      have hMem : block ∈ program.blocks := List.mem_of_find?_eq_some hFind
      have hBlockTyped : block.WellTyped program :=
        (List.forall_iff_forall_mem.mp hTyped.2.1) block hMem
      have hBlockIndep : block.ProgramCounterIndependent :=
        (List.forall_iff_forall_mem.mp hIndependent) block hMem
      have h1 :
          Simulation.Interaction.Rel
            InteractionCongruence.Block.RuntimeOutcomeRel
            (InteractionSemantics.Block.openRun block state1)
            (InteractionSemantics.Block.openRun block state2) :=
        InteractionCongruence.Block.openRun_runtimeRel
          hBlockTyped hBlockIndep hRel
      have h2 :
          Simulation.Interaction.Rel
            InteractionCongruence.Block.RuntimeOutcomeRel
            (InteractionSemantics.Block.openRun (normalizeBlock block) state2)
            (InteractionSemantics.Block.openRun block state2) :=
        Block.openRun_normalize_runtimeRel block state2 hBlockTyped hBlockIndep
          (hReal2 block hFind)
      refine Simulation.Interaction.Rel.mono
        (Simulation.Interaction.Rel.trans h1 (rel_runtimeOutcomeRel_symm h2)) ?_
      rintro l r ⟨m, ha, hb⟩
      exact runtimeOutcomeRel_trans ha hb

end Peephole
end TypedCfg
end EvmCompiler
