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

/-- `LowerLe` is transitive (used by the `push v ; push v → push v ; dup 0`
arm, which factors through the intermediate doubled-push lowering). -/
theorem LowerLe.trans {a b c : Option (Assembly.Program × Shape)}
    (hab : LowerLe a b) (hbc : LowerLe b c) : LowerLe a c := by
  intro c' o' hEq
  obtain ⟨c1, hb, hlen1⟩ := hab c' o' hEq
  obtain ⟨c2, hc, hlen2⟩ := hbc c1 o' hb
  exact ⟨c2, hc, le_trans hlen1 hlen2⟩

/-- Lowering `dup 0` where the original lowered a repeated `push v`: same output
shape, same Assembly-instruction count (one fragment each).  The byte saving —
`DUP1` is 1 byte where `PUSH_n v` is `1 + n` — is invisible to `LowerLe`, which
counts fragments, so this is an equality-length `LowerLe`. -/
theorem lowerBodyFrom?_dup0_push_le (v : Word) (rest' : List Instr)
    (input : Shape) :
    LowerLe
      (Block.lowerBodyFrom? (.dup 0 :: rest')
        { input with slots := .literal v :: input.slots })
      (Block.lowerBodyFrom? (.push v :: rest')
        { input with slots := .literal v :: input.slots }) := by
  intro c' o' hEq
  have hDup : Instr.lowerAt? (.dup 0)
        { input with slots := .literal v :: input.slots } =
      some ([Assembly.Instr.prim .dup1],
        { slots := .literal v :: .literal v :: input.slots,
          tail := input.tail }) := by
    simp [Instr.lowerAt?, Instr.type?, Instr.lower?, Shape.get?]
  have hPush : Instr.lowerAt? (.push v)
        { input with slots := .literal v :: input.slots } =
      some (Assembly.pushCode v,
        { slots := .literal v :: .literal v :: input.slots,
          tail := input.tail }) := by
    simp [Instr.lowerAt?, Instr.type?, Instr.lower?]
  rw [lowerBodyFrom?_cons, hDup] at hEq
  simp only [Option.bind] at hEq
  cases hTail : Block.lowerBodyFrom? rest'
      { slots := .literal v :: .literal v :: input.slots,
        tail := input.tail } with
  | none => rw [hTail] at hEq; simp at hEq
  | some q =>
      obtain ⟨tailCode, tailOut⟩ := q
      rw [hTail] at hEq
      simp only [Option.some.injEq, Prod.mk.injEq] at hEq
      obtain ⟨hc, ho⟩ := hEq
      refine ⟨Assembly.pushCode v ++ tailCode, ?_, ?_⟩
      · rw [lowerBodyFrom?_cons, hPush]
        simp only [Option.bind, hTail, ho]
      · rw [← hc]
        simp only [List.length_append, List.length_singleton]
        have hLen : (Assembly.pushCode v).length ≥ 1 := by
          unfold Assembly.pushCode
          split <;> simp [List.length_append, List.length_singleton] <;> omega
        omega

/-- Head-typed `LowerLe.cons`: a shared leading instruction that types `input`
to `middle` propagates a `LowerLe` established at `middle`.  (Directional/typed,
because the `swap ; swap` arm — unlike `push ; pop` — only lowers when the shape
is deep enough; the head typing supplies exactly that shape.) -/
theorem LowerLe.cons {i : Instr} {A B : List Instr} {input middle : Shape}
    (hHeadType : i.type? input = some middle)
    (h : LowerLe (Block.lowerBodyFrom? A middle)
      (Block.lowerBodyFrom? B middle)) :
    LowerLe (Block.lowerBodyFrom? (i :: A) input)
      (Block.lowerBodyFrom? (i :: B) input) := by
  intro c' o' hEq
  rw [lowerBodyFrom?_cons, Option.bind_eq_some_iff] at hEq
  obtain ⟨⟨head, sh'⟩, hHead, hEq2⟩ := hEq
  have hSh' : sh' = middle := by
    have hT := Preservation.Instr.type?_eq_some_of_lowerAt? hHead
    rw [hHeadType] at hT; exact (Option.some.inj hT).symm
  subst hSh'
  rw [Option.bind_eq_some_iff] at hEq2
  obtain ⟨⟨t', o''⟩, hTail, hEq3⟩ := hEq2
  simp only [Option.some.injEq, Prod.mk.injEq] at hEq3
  obtain ⟨hc, ho⟩ := hEq3
  obtain ⟨t, hOrig, hLen⟩ := h t' o'' hTail
  refine ⟨head ++ t, ?_, ?_⟩
  · rw [lowerBodyFrom?_cons, hHead]
    simp only [Option.bind, hOrig, ho]
  · rw [← hc]; simp only [List.length_append]; omega

/-- A well-typed `swap depth` lowers: `type? = some output` forces `depth < 16`,
so `lower?` yields a (singleton) fragment and `lowerAt?` succeeds with the same
output shape.  (The exact fragment length is irrelevant to `LowerLe`.) -/
theorem lowerAt?_swap_of_type? {depth : Nat} {input output : Shape}
    (hType : Instr.type? (.swap depth) input = some output) :
    ∃ code, Instr.lowerAt? (.swap depth) input = some (code, output) := by
  obtain ⟨hDLt, _, _⟩ := Instr.length_of_type?_swap hType
  unfold Instr.lowerAt?
  rw [hType]
  interval_cases depth <;> exact ⟨_, rfl⟩

theorem lowerBodyFrom?_peephole_le :
    ∀ (body : List Instr) (input output : Shape),
      Block.bodyType? body input = some output →
      LowerLe (Block.lowerBodyFrom? (peepholeBody body) input)
        (Block.lowerBodyFrom? body input)
  | [], input, _output, _hType => by
      intro c' o' hEq
      simp only [peepholeBody_nil, Block.lowerBodyFrom?, Option.some.injEq,
        Prod.mk.injEq] at hEq
      obtain ⟨hc, ho⟩ := hEq
      subst hc; subst ho
      exact ⟨[], rfl, le_refl _⟩
  | instr :: rest, input, output, hType => by
      cases hHeadType : instr.type? input with
      | none => simp [Block.bodyType?, hHeadType] at hType
      | some middle =>
          have hTailType : Block.bodyType? rest middle = some output := by
            simpa [Block.bodyType?, hHeadType] using hType
          rw [peepholeBody_cons]
          split
          · -- push;pop cancel arm: instr = .push v, peepholeBody rest = .pop :: rest'
            rename_i v rest' hPeep
            intro c' o' hEq
            have hMiddle : middle =
                { input with slots := .literal v :: input.slots } := by
              simpa [Instr.type?] using hHeadType.symm
            subst hMiddle
            have hPush : Instr.lowerAt? (.push v) input =
                some (Assembly.pushCode v,
                  { input with slots := .literal v :: input.slots }) := by
              simp [Instr.lowerAt?, Instr.type?, Instr.lower?]
            have hPop : Instr.lowerAt? .pop
                { input with slots := .literal v :: input.slots } =
                some ([Assembly.Instr.prim .pop], input) := by
              simp [Instr.lowerAt?, Instr.type?, Instr.lower?]
            have hPeepLower :
                Block.lowerBodyFrom? (peepholeBody rest)
                    { input with slots := .literal v :: input.slots } =
                  some ([Assembly.Instr.prim .pop] ++ c', o') := by
              rw [hPeep, lowerBodyFrom?_cons, hPop]
              simp only [Option.bind, hEq]
            obtain ⟨t, hOrigRest, hLen⟩ :=
              lowerBodyFrom?_peephole_le rest
                { input with slots := .literal v :: input.slots } output hTailType
                ([Assembly.Instr.prim .pop] ++ c') o' hPeepLower
            refine ⟨Assembly.pushCode v ++ t, ?_, ?_⟩
            · rw [lowerBodyFrom?_cons, hPush]
              simp only [Option.bind, hOrigRest]
            · simp only [List.length_append, List.length_cons,
                List.length_nil] at hLen ⊢
              omega
          · -- swap;swap arm: instr = .swap d, peepholeBody rest = .swap d' :: rest'
            rename_i d d' rest' hEq
            split
            · -- d = d': cancels to rest'.  The two swaps are well-typed
              -- (input→middle and, by involution, middle→input), so both lower;
              -- their codes only ADD bytes to the original, preserving `LowerLe`.
              rename_i hdd
              subst hdd
              intro c' o' hEqLower
              have hInv : Instr.type? (.swap d) middle = some input :=
                Instr.swap_type_involution hHeadType
              obtain ⟨sc1, hLA1⟩ := lowerAt?_swap_of_type? hHeadType
              obtain ⟨sc2, hLA2⟩ := lowerAt?_swap_of_type? hInv
              have hPeepLower :
                  Block.lowerBodyFrom? (peepholeBody rest) middle =
                    some (sc2 ++ c', o') := by
                rw [hEq, lowerBodyFrom?_cons, hLA2]
                simp only [Option.bind, hEqLower]
              obtain ⟨c0, hOrigRest, hLen⟩ :=
                lowerBodyFrom?_peephole_le rest middle output hTailType
                  (sc2 ++ c') o' hPeepLower
              refine ⟨sc1 ++ c0, ?_, ?_⟩
              · rw [lowerBodyFrom?_cons, hLA1]
                simp only [Option.bind, hOrigRest]
              · simp only [List.length_append] at hLen ⊢
                omega
            · -- d ≠ d': keeps both swaps (= .swap d :: peepholeBody rest)
              rw [← hEq]
              exact LowerLe.cons hHeadType
                (lowerBodyFrom?_peephole_le rest middle output hTailType)
          · -- push;push arm: instr = .push v, peepholeBody rest = .push v' :: rest'
            rename_i v v' rest' hEq
            have hMiddle : middle =
                { input with slots := .literal v :: input.slots } := by
              simpa [Instr.type?] using hHeadType.symm
            subst hMiddle
            split
            · -- v = v': the second push becomes `dup 0`; both lower to a single
              -- Assembly instruction with the same output shape, so the
              -- fragment-count bound routes through the doubled-push lowering.
              rename_i hvv
              subst hvv
              refine LowerLe.cons hHeadType ?_
              refine LowerLe.trans (lowerBodyFrom?_dup0_push_le v rest' input) ?_
              have ih := lowerBodyFrom?_peephole_le rest
                { input with slots := .literal v :: input.slots } output hTailType
              rwa [hEq] at ih
            · -- v ≠ v': keeps both pushes (= .push v :: peepholeBody rest)
              rw [← hEq]
              exact LowerLe.cons hHeadType
                (lowerBodyFrom?_peephole_le rest
                  { input with slots := .literal v :: input.slots } output
                  hTailType)
          · -- keep arm
            exact LowerLe.cons hHeadType
              (lowerBodyFrom?_peephole_le rest middle output hTailType)

/-- Per-block, the peephole does not increase the compiled fuel budget.  Needs
the block's body typing so the `swap ; swap` cancellation's guard is available:
without it a shallow shape could make the original body fail to lower while the
cancelled tail lowers, breaking the per-block `LowerLe`. -/
theorem compiledBlock_fuelBudget_peephole_le (block : Block)
    (hType : Block.bodyType? block.body block.input = some block.output) :
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
        lowerBodyFrom?_peephole_le block.body block.input block.output hType
          peepCode peepOut hPeep
      simp only [hOrig]
      by_cases hOut : peepOut = block.output
      · simp only [hOut, if_true]
        cases hTerm : block.term.lowerAt? block.output with
        | none => simp
        | some termCode => simp only [hTerm]; omega
      · simp [hOut]

/-- Whole-block-list fuel-budget monotonicity under the (well-typed) peephole. -/
theorem fuelBudget_blocks_le {program : Program} :
    ∀ (blocks : List Block), (∀ b ∈ blocks, b.WellTyped program) →
      (blocks.map fun b =>
          InteractionSemantics.CompiledBlock.fuelBudget (peepholeBlock b)).sum ≤
        (blocks.map InteractionSemantics.CompiledBlock.fuelBudget).sum
  | [], _ => by simp
  | b :: bs, hAll => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledBlock_fuelBudget_peephole_le b
          (hAll b (List.mem_cons_self ..)).1)
        (fuelBudget_blocks_le bs
          (fun b' hb' => hAll b' (List.mem_cons_of_mem _ hb')))

/-- **The peephole does not increase the whole-program fuel budget** (for a
well-typed program). -/
theorem fuelBudget_peepholeProgram_le (program : Program)
    (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget (peepholeProgram program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  rw [peepholeProgram_blocks, List.map_map]
  obtain ⟨_, hBlocks, _, _⟩ := hWT
  unfold Program.AllBlocksTyped at hBlocks
  rw [List.forall_iff_forall_mem] at hBlocks
  have hMain := fuelBudget_blocks_le program.blocks hBlocks
  simpa [Function.comp] using hMain

end Peephole
end TypedCfg
end EvmCompiler
