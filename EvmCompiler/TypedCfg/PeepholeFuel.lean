import EvmCompiler.TypedCfg.PeepholeSpine

/-!
# Peephole shrinks the compiled fuel budget

Milestone (g): `fuelBudget (peepholeProgram cfg) ≤ fuelBudget cfg`.  This is the
last self-contained lemma the compile-spine splice needs: the peepholed program
emits no more Assembly instructions than the original, so its
`CompiledProgram.fuelBudget` is bounded by the original's.  A future splice that
keeps the conclusion budget at `fuelBudget cfg` can therefore pad the peepholed
program's assembly execution up to the original budget with the existing
`openRunNResult_*_add_executes` / `_follows_of_le_follows` lemmas, changing no
downstream statement.

Core lemma `lowerBodyFrom?_peephole_le`: whenever the peepholed body lowers, the
original body lowers to the SAME output shape with at least as many bytes.  A
`push v ; pop` cancellation removes exactly the two 1-byte fragments
`[.push v]` and `[.prim .pop]`; the intervening shape returns to `input`, so the
rest of the body lowers identically.  The proof mirrors
`peepholeBody_bodyType?` (tail-first, `peepholeBody_cons` split).
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-- `lowerBodyFrom?` on a cons, as an explicit `Option.bind` (so the standard
`Option.bind_eq_some_iff` fires). -/
theorem lowerBodyFrom?_cons (i : Instr) (A : List Instr) (input : Shape) :
    Block.lowerBodyFrom? (i :: A) input =
      (Instr.lowerAt? i input).bind (fun p =>
        (Block.lowerBodyFrom? A p.2).bind (fun q => some (p.1 ++ q.1, q.2))) := by
  simp only [Block.lowerBodyFrom?, Option.bind]
  cases Instr.lowerAt? i input with
  | none => rfl
  | some p => cases Block.lowerBodyFrom? A p.2 <;> rfl

/-- The peepholed lowering (if defined) has the same output shape and no more
bytes than the original lowering. -/
def LowerLe (peep orig : Option (Assembly.Program × Shape)) : Prop :=
  ∀ c' o', peep = some (c', o') →
    ∃ c, orig = some (c, o') ∧ c'.length ≤ c.length

theorem LowerLe.cons {i : Instr} {A B : List Instr}
    (h : ∀ input, LowerLe (Block.lowerBodyFrom? A input)
      (Block.lowerBodyFrom? B input)) (input : Shape) :
    LowerLe (Block.lowerBodyFrom? (i :: A) input)
      (Block.lowerBodyFrom? (i :: B) input) := by
  intro c' o' hEq
  rw [lowerBodyFrom?_cons, Option.bind_eq_some_iff] at hEq
  obtain ⟨⟨head, sh'⟩, hHead, hEq2⟩ := hEq
  rw [Option.bind_eq_some_iff] at hEq2
  obtain ⟨⟨t', o''⟩, hTail, hEq3⟩ := hEq2
  simp only [Option.some.injEq, Prod.mk.injEq] at hEq3
  obtain ⟨hc, ho⟩ := hEq3
  obtain ⟨t, hOrig, hLen⟩ := h sh' t' o'' hTail
  refine ⟨head ++ t, ?_, ?_⟩
  · rw [lowerBodyFrom?_cons, hHead]
    simp only [Option.bind, hOrig, ho]
  · rw [← hc]; simp only [List.length_append]; omega

theorem lowerBodyFrom?_peephole_le :
    ∀ (body : List Instr) (input : Shape),
      LowerLe (Block.lowerBodyFrom? (peepholeBody body) input)
        (Block.lowerBodyFrom? body input)
  | [], input => by
      intro c' o' hEq
      simp only [peepholeBody_nil, Block.lowerBodyFrom?, Option.some.injEq,
        Prod.mk.injEq] at hEq
      obtain ⟨hc, ho⟩ := hEq
      subst hc; subst ho
      exact ⟨[], rfl, le_refl _⟩
  | instr :: rest, input => by
      rw [peepholeBody_cons]
      split
      · -- cancel arm: instr = .push v, peepholeBody rest = .pop :: rest'
        rename_i v rest' hPeep
        intro c' o' hEq
        -- hEq : lowerBodyFrom? rest' input = some (c', o')
        have hPush : Instr.lowerAt? (.push v) input =
            some ([Assembly.Instr.push v],
              { input with slots := .literal v :: input.slots }) := by
          simp [Instr.lowerAt?, Instr.type?, Instr.lower?]
        have hPop : Instr.lowerAt? .pop
            { input with slots := .literal v :: input.slots } =
            some ([Assembly.Instr.prim .pop], input) := by
          simp [Instr.lowerAt?, Instr.type?, Instr.lower?]
        -- lowerBodyFrom? (peepholeBody rest) pushShape = some ([.prim .pop] ++ c', o')
        have hPeepLower :
            Block.lowerBodyFrom? (peepholeBody rest)
                { input with slots := .literal v :: input.slots } =
              some ([Assembly.Instr.prim .pop] ++ c', o') := by
          rw [hPeep, lowerBodyFrom?_cons, hPop]
          simp only [Option.bind, hEq]
        obtain ⟨t, hOrigRest, hLen⟩ :=
          lowerBodyFrom?_peephole_le rest
            { input with slots := .literal v :: input.slots }
            ([Assembly.Instr.prim .pop] ++ c') o' hPeepLower
        refine ⟨[Assembly.Instr.push v] ++ t, ?_, ?_⟩
        · rw [lowerBodyFrom?_cons, hPush]
          simp only [Option.bind, hOrigRest]
        · simp only [List.length_append, List.length_cons,
            List.length_nil] at hLen ⊢
          omega
      · -- keep arm
        exact LowerLe.cons (fun input => lowerBodyFrom?_peephole_le rest input)
          input

/-- Per-block, the peephole does not increase the compiled fuel budget. -/
theorem compiledBlock_fuelBudget_peephole_le (block : Block) :
    InteractionSemantics.CompiledBlock.fuelBudget (peepholeBlock block) ≤
      InteractionSemantics.CompiledBlock.fuelBudget block := by
  unfold InteractionSemantics.CompiledBlock.fuelBudget
  simp only [peepholeBlock_body, peepholeBlock_input, peepholeBlock_output,
    peepholeBlock_term]
  cases hPeep : Block.lowerBodyFrom? (peepholeBody block.body) block.input with
  | none => simp
  | some peepPair =>
      obtain ⟨peepCode, peepOut⟩ := peepPair
      obtain ⟨origCode, hOrig, hLen⟩ :=
        lowerBodyFrom?_peephole_le block.body block.input peepCode peepOut hPeep
      simp only [hOrig]
      by_cases hOut : peepOut = block.output
      · simp only [hOut, if_true]
        cases hTerm : block.term.lowerAt? block.output with
        | none => simp
        | some termCode => simp only [hTerm]; omega
      · simp [hOut]

/-- **The peephole does not increase the whole-program fuel budget.** -/
theorem fuelBudget_peepholeProgram_le (program : Program) :
    InteractionSemantics.CompiledProgram.fuelBudget (peepholeProgram program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  rw [peepholeProgram_blocks, List.map_map]
  induction program.blocks with
  | nil => simp
  | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      exact Nat.add_le_add (compiledBlock_fuelBudget_peephole_le b) ih

end Peephole
end TypedCfg
end EvmCompiler
