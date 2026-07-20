import EvmCompiler.TypedCfg.PeepholeFuel
import EvmCompiler.TypedCfg.PeepholeNoopSwapProgram

/-!
# `normalizeProgram` does not increase the compiled fuel budget (session-58)

The Route-3 analogue of `PeepholeFuel`: `fuelBudget (normalizeProgram cfg) ≤
fuelBudget cfg` for a well-typed `cfg`.  A firing window drops the two enclosing
`swap d` fragments and replaces the interior zero-width run by its
`remapZeroWidth`-image — but zero-width instructions (and their residue) lower to
`[]`, so the normalized body emits strictly fewer-or-equal Assembly bytes.  The
`LowerLe` / `LowerLe.cons` / `lowerAt?_swap_of_type?` scaffolding is pass-agnostic
and reused from `PeepholeFuel`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-- A zero-width instruction lowers to the empty fragment (advancing only the
shape). -/
theorem lowerAt?_zeroWidth {z : Instr} (h : isZeroWidth z = true)
    {s s' : Shape} (hType : Instr.type? z s = some s') :
    Instr.lowerAt? z s = some ([], s') := by
  cases z <;>
    simp_all [isZeroWidth, Instr.lowerAt?, Instr.lower?]

/-- Lowering a zero-width run emits nothing and merely advances the shape. -/
theorem lowerBodyFrom?_zeroWidth_run (zrun : List Instr) :
    ∀ (tail : List Instr) (shape shape' : Shape),
      (∀ z ∈ zrun, isZeroWidth z = true) →
      Block.bodyType? zrun shape = some shape' →
      Block.lowerBodyFrom? (zrun ++ tail) shape
        = Block.lowerBodyFrom? tail shape' := by
  induction zrun with
  | nil =>
      intro tail shape shape' _ hType
      simp only [Block.bodyType?, Option.some.injEq] at hType; subst hType; rfl
  | cons z rest ih =>
      intro tail shape shape' hAll hType
      have hz : isZeroWidth z = true := hAll z (List.mem_cons_self ..)
      rw [bodyType?_cons] at hType
      cases hzt : Instr.type? z shape with
      | none => rw [hzt] at hType; simp at hType
      | some z1 =>
          rw [hzt, Option.bind_some] at hType
          rw [List.cons_append, lowerBodyFrom?_cons, lowerAt?_zeroWidth hz hzt]
          simp only [Option.bind, List.nil_append]
          rw [ih tail z1 shape'
            (fun z' hz' => hAll z' (List.mem_cons_of_mem z hz')) hType]
          cases Block.lowerBodyFrom? tail shape' <;> rfl

/-- The normalized lowering (if defined) has the same output shape and no more
bytes than the original lowering. -/
theorem lowerBodyFrom?_normalize_le (body : List Instr) :
    ∀ (input output : Shape),
      Block.bodyType? body input = some output →
      LowerLe (Block.lowerBodyFrom? (normalizeBody body) input)
        (Block.lowerBodyFrom? body input) := by
  induction body using normalizeBody.induct with
  | case1 =>
      intro input _output _hType c' o' hEq
      simp only [normalizeBody, Block.lowerBodyFrom?, Option.some.injEq,
        Prod.mk.injEq] at hEq
      obtain ⟨hc, ho⟩ := hEq; subst hc; subst ho
      exact ⟨[], rfl, le_refl _⟩
  | case2 d rest d' rest' hTail hGuard ih =>
      intro input output hType
      obtain ⟨hdd, hSafe⟩ := hGuard
      subst hdd
      have happ : (leadingZeroWidth rest).1 ++ Instr.swap d :: rest' = rest := by
        conv_rhs => rw [← leadingZeroWidth_append rest]
        rw [hTail]
      have hAllSafe : ∀ z ∈ (leadingZeroWidth rest).1, RemapSafe z = true :=
        fun z hz => List.all_eq_true.mp hSafe z hz
      have hAllZW : ∀ z ∈ (leadingZeroWidth rest).1, isZeroWidth z = true :=
        fun z hz => remapSafe_isZeroWidth (hAllSafe z hz)
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨s1, h1, hTypeRest⟩ := hType
      obtain ⟨hi0, hid1⟩ := swap_bounds h1
      obtain ⟨hs1slots, hs1tail⟩ := type?_swap_eq h1
      have hs1len : s1.slots.length = input.slots.length := by
        rw [hs1slots, swapPos_length]
      have hs1eq : s1 = remapShape d input := by
        rcases s1 with ⟨sl1, tl1⟩
        simp only at hs1slots hs1tail
        subst hs1slots; subst hs1tail; rfl
      rw [← happ, bodyType?_append, Option.bind_eq_some_iff] at hTypeRest
      obtain ⟨sInner, hzt, hTypeRest⟩ := hTypeRest
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hTypeRest
      obtain ⟨s3, h3, hTypeRest'⟩ := hTypeRest
      obtain ⟨hs3slots, hs3tail⟩ := type?_swap_eq h3
      obtain ⟨sc1, hLA1⟩ := lowerAt?_swap_of_type? h1
      obtain ⟨sc2, hLA2⟩ := lowerAt?_swap_of_type? h3
      -- the normalized `map`-run advances to s3
      have hfoldT : Block.bodyType?
          ((leadingZeroWidth rest).1.map (remapZeroWidth d)) input = some s3 := by
        have hinput_eq : input = remapShape d s1 := by
          rw [hs1eq, remapShape_involutive d input hi0 hid1]
        rw [hinput_eq, bodyType?_map_remap_conj d (leadingZeroWidth rest).1 s1 hAllSafe
          (by rw [hs1len]; exact hi0) (by rw [hs1len]; exact hid1), hzt, Option.map_some]
        refine congrArg some ?_
        rcases s3 with ⟨sl3, tl3⟩
        simp only at hs3slots hs3tail
        simp only [remapShape, Shape.mk.injEq]; exact ⟨hs3slots.symm, hs3tail.symm⟩
      have hMapZW : ∀ z ∈ (leadingZeroWidth rest).1.map (remapZeroWidth d),
          isZeroWidth z = true := by
        intro z hz
        obtain ⟨z0, hz0mem, hz0eq⟩ := List.mem_map.mp hz
        subst hz0eq; rw [isZeroWidth_remapZeroWidth]; exact hAllZW z0 hz0mem
      have hLHSlow : Block.lowerBodyFrom? (normalizeBody (Instr.swap d :: rest)) input
          = Block.lowerBodyFrom? (normalizeBody rest') s3 := by
        rw [normalizeBody_fire d rest rest' hTail hSafe]
        exact lowerBodyFrom?_zeroWidth_run ((leadingZeroWidth rest).1.map (remapZeroWidth d))
          (normalizeBody rest') input s3 hMapZW hfoldT
      intro c' o' hEq
      rw [hLHSlow] at hEq
      obtain ⟨ct, hOrigRest', hLen⟩ := ih s3 output hTypeRest' c' o' hEq
      -- original: swap ; zrun ; swap ; rest' — reduces to sc1 ++ sc2 ++ ct
      have hRestLow : Block.lowerBodyFrom? rest s1 = some (sc2 ++ ct, o') := by
        conv_lhs => rw [← happ]
        rw [lowerBodyFrom?_zeroWidth_run (leadingZeroWidth rest).1
          (Instr.swap d :: rest') s1 sInner hAllZW hzt,
          lowerBodyFrom?_cons, hLA2]
        simp only [Option.bind, hOrigRest']
      refine ⟨sc1 ++ sc2 ++ ct, ?_, ?_⟩
      · rw [lowerBodyFrom?_cons, hLA1]
        simp only [Option.bind, hRestLow, List.append_assoc]
      · simp only [List.length_append] at hLen ⊢; omega
  | case3 d rest d' rest' hTail hGuard ih =>
      intro input output hType
      have hunfold : normalizeBody (Instr.swap d :: rest)
          = Instr.swap d :: normalizeBody rest := by
        by_cases hdd : d = d'
        · have hUnsafe : (leadingZeroWidth rest).1.all RemapSafe = false := by
            by_contra hne; simp only [Bool.not_eq_false] at hne
            exact hGuard ⟨hdd, hne⟩
          exact normalizeBody_keep_unsafe d d' rest rest' hTail hUnsafe
        · exact normalizeBody_keep_swap d d' rest rest' hTail hdd
      rw [hunfold, bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨middle, hHeadType, hTailType⟩ := hType
      exact LowerLe.cons hHeadType (ih middle output hTailType)
  | case4 d rest hNoTail ih =>
      intro input output hType
      rw [normalizeBody_keep_noTail d rest (fun d' rest' h => hNoTail d' rest' h),
        bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨middle, hHeadType, hTailType⟩ := hType
      exact LowerLe.cons hHeadType (ih middle output hTailType)
  | case5 instr rest hNotSwap ih =>
      intro input output hType
      rw [normalizeBody_cons_generic instr rest (fun d h => hNotSwap d h),
        bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨middle, hHeadType, hTailType⟩ := hType
      exact LowerLe.cons hHeadType (ih middle output hTailType)

/-- Per-block, the normalization does not increase the compiled fuel budget. -/
theorem compiledBlock_fuelBudget_normalize_le (block : Block)
    (hType : Block.bodyType? block.body block.input = some block.output) :
    InteractionSemantics.CompiledBlock.fuelBudget (normalizeBlock block) ≤
      InteractionSemantics.CompiledBlock.fuelBudget block := by
  unfold InteractionSemantics.CompiledBlock.fuelBudget
  simp only [normalizeBlock_body, normalizeBlock_input, normalizeBlock_output,
    normalizeBlock_term]
  cases hNorm : Block.lowerBodyFrom? (normalizeBody block.body) block.input with
  | none => simp
  | some normPair =>
      obtain ⟨normCode, normOut⟩ := normPair
      obtain ⟨origCode, hOrig, hLen⟩ :=
        lowerBodyFrom?_normalize_le block.body block.input block.output hType
          normCode normOut hNorm
      simp only [hOrig]
      by_cases hOut : normOut = block.output
      · simp only [hOut, if_true]
        cases hTerm : block.term.lowerAt? block.output with
        | none => simp
        | some termCode => simp only [hTerm]; omega
      · simp [hOut]

/-- Whole-block-list fuel-budget monotonicity under the (well-typed) normalize. -/
theorem fuelBudget_blocks_le_normalize {program : Program} :
    ∀ (blocks : List Block), (∀ b ∈ blocks, b.WellTyped program) →
      (blocks.map fun b =>
          InteractionSemantics.CompiledBlock.fuelBudget (normalizeBlock b)).sum ≤
        (blocks.map InteractionSemantics.CompiledBlock.fuelBudget).sum
  | [], _ => by simp
  | b :: bs, hAll => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledBlock_fuelBudget_normalize_le b
          (hAll b (List.mem_cons_self ..)).1)
        (fuelBudget_blocks_le_normalize bs
          (fun b' hb' => hAll b' (List.mem_cons_of_mem _ hb')))

/-- **The normalization does not increase the whole-program fuel budget.** -/
theorem fuelBudget_normalizeProgram_le (program : Program)
    (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget (normalizeProgram program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  rw [normalizeProgram_blocks, List.map_map]
  obtain ⟨_, hBlocks, _, _⟩ := hWT
  unfold Program.AllBlocksTyped at hBlocks
  rw [List.forall_iff_forall_mem] at hBlocks
  have hMain := fuelBudget_blocks_le_normalize program.blocks hBlocks
  simpa [Function.comp] using hMain

end Peephole
end TypedCfg
end EvmCompiler
