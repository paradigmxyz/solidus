import EvmCompiler.TypedCfg.ShuffleCanonChain
import EvmCompiler.Structured.PeepholeSeamCombined

/-!
# Fuel-budget accounting for the cross-block chain canonicaliser

This orphan leaf collects the *fuel-budget* reductions for `chainCanonProgram`
that feed the (still-open) dual-hypothesis global bound

```
fuelBudget (chainCanonProgram program) ≤ fuelBudget program
```

banked green + axiom-clean.  §Session-91 established the bound needs BOTH
`(chainCanonProgram program).lower?.isSome` (F-side non-collapse) and
`program.lower?.isSome` (G-side non-collapse); §Session-92 reduced it — with no
`Nat` subtraction — to a permutation-to-lowering-order rewrite plus a per-chain
`canonSwaps_length_le` inequality (see `PEEPHOLE_PROGRESS.md`, §Session-92).

Nothing here is imported by the `compile_correct` cone: `chainCanonProgram` is
still referenced only inside the `ShuffleCanon*` cluster, so these lemmas cannot
touch the public axiom footprint.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleCanon

open TypedCfg (Instr Shape Terminator Block Program Label)
open InteractionSemantics

/-! ## Lowered-length of chain bodies and the canonical head body -/

/-- A single `swap` whose `lowerAt?` succeeds lowers to exactly one instruction. -/
theorem lowerAt?_swap_length {d : Nat} {input : Shape}
    {code : Assembly.Program} {out : Shape}
    (h : Instr.lowerAt? (.swap d) input = some (code, out)) : code.length = 1 := by
  have hT : (Instr.type? (.swap d) input).isSome := by
    unfold Instr.lowerAt? at h
    rcases hh : Instr.type? (.swap d) input with _ | o
    · rw [hh] at h; simp at h
    · rfl
  rw [Option.isSome_iff_exists] at hT
  obtain ⟨o, ho⟩ := hT
  obtain ⟨hd, _, _⟩ := Instr.length_of_type?_swap ho
  unfold Instr.lowerAt? at h
  rw [ho] at h
  interval_cases d <;>
    · simp only [Instr.lower?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl

/-- A single `bindLocals` whose `lowerAt?` succeeds lowers to zero instructions. -/
theorem lowerAt?_bindLocals_length {off : Nat} {names : List String} {input : Shape}
    {code : Assembly.Program} {out : Shape}
    (h : Instr.lowerAt? (.bindLocals off names) input = some (code, out)) :
    code.length = 0 := by
  have hT : (Instr.type? (.bindLocals off names) input).isSome := by
    unfold Instr.lowerAt? at h
    rcases hh : Instr.type? (.bindLocals off names) input with _ | o
    · rw [hh] at h; simp at h
    · rfl
  rw [Option.isSome_iff_exists] at hT
  obtain ⟨o, ho⟩ := hT
  unfold Instr.lowerAt? at h
  rw [ho] at h
  simp only [Instr.lower?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- If a chain body (`.swap`/`.bindLocals` only) lowers, its lowered length equals
its swap count (`.bindLocals` lowers to `[]`, so it contributes nothing). -/
theorem lowerBodyFrom?_chainBody_length (body : List Instr) {ds : List Nat}
    (hds : chainBodyDepths? body = some ds)
    {input : Shape} {code : Assembly.Program} {out : Shape}
    (hlow : Block.lowerBodyFrom? body input = some (code, out)) :
    code.length = ds.length := by
  induction body generalizing ds input code out with
  | nil =>
      simp only [chainBodyDepths?, Option.some.injEq] at hds
      subst hds
      simp only [Block.lowerBodyFrom?, Option.some.injEq, Prod.mk.injEq] at hlow
      simp [← hlow.1]
  | cons hd tl ih =>
      cases hd
      case swap d =>
          simp only [chainBodyDepths?] at hds
          rcases hh : chainBodyDepths? tl with _ | ds'
          · rw [hh] at hds; simp at hds
          · rw [hh] at hds
            simp only [Option.map_some, Option.some.injEq] at hds
            subst hds
            rw [Peephole.lowerBodyFrom?_cons] at hlow
            rcases hp : Instr.lowerAt? (.swap d) input with _ | ⟨pc, po⟩
            · rw [hp] at hlow; simp at hlow
            · rw [hp, Option.bind_some] at hlow
              rcases hq : Block.lowerBodyFrom? tl po with _ | ⟨qc, qo⟩
              · rw [hq] at hlow; simp at hlow
              · rw [hq, Option.bind_some] at hlow
                simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                obtain ⟨hcode, _⟩ := hlow
                subst hcode
                rw [List.length_append, lowerAt?_swap_length hp, ih hh hq,
                  List.length_cons]
                omega
      case bindLocals off names =>
          simp only [chainBodyDepths?] at hds
          rw [Peephole.lowerBodyFrom?_cons] at hlow
          rcases hp : Instr.lowerAt? (.bindLocals off names) input with _ | ⟨pc, po⟩
          · rw [hp] at hlow; simp at hlow
          · rw [hp, Option.bind_some] at hlow
            rcases hq : Block.lowerBodyFrom? tl po with _ | ⟨qc, qo⟩
            · rw [hq] at hlow; simp at hlow
            · rw [hq, Option.bind_some] at hlow
              simp only [Option.some.injEq, Prod.mk.injEq] at hlow
              obtain ⟨hcode, _⟩ := hlow
              subst hcode
              rw [List.length_append, lowerAt?_bindLocals_length hp, ih hds hq]
              omega
      all_goals (exact absurd hds (by simp [chainBodyDepths?]))

/-- `applyEdit` is the identity on any block whose label is absent from the
edit table, so it leaves the compiled fuel budget unchanged.  This is the
zero-difference contribution of every non-chain block in the global sum. -/
theorem fuelBudget_applyEdit_none {tbl : List (Label × Edit)} {b : Block}
    (h : tbl.lookup b.label = none) :
    CompiledBlock.fuelBudget (applyEdit tbl b) = CompiledBlock.fuelBudget b := by
  unfold applyEdit
  rw [h]

/-- The chain-canonicalised program's fuel budget as an explicit block-indexed
sum over the ORIGINAL block list (same order as `program.blocks`): the transform
only rewrites bodies/shapes via `applyEdit`, never reorders blocks.  Both this
sum and `fuelBudget program` therefore range over the identical list — the
per-chain rebalancing is a redistribution of summands, not a reordering. -/
theorem fuelBudget_chainCanonProgram_eq (program : Program) :
    CompiledProgram.fuelBudget (chainCanonProgram program) =
      (program.blocks.map
        (fun b => CompiledBlock.fuelBudget (applyEdit (editTable program) b))).sum := by
  simp only [CompiledProgram.fuelBudget, chainCanonProgram_blocks, List.map_map,
    Function.comp_def]

/-- Fuel budget is invariant under the lowering-order permutation: it may be
computed over `blocksInLoweringOrder?` instead of `program.blocks`.  This is the
bridge that makes chains **contiguous** (they are runs in the lowering order),
enabling the `scanEdits`-mirrored segment induction for the global bound. -/
theorem fuelBudget_eq_sum_ordered {program : Program} {ordered : List Block}
    (h : program.blocksInLoweringOrder? = some ordered) :
    CompiledProgram.fuelBudget program =
      (ordered.map CompiledBlock.fuelBudget).sum := by
  unfold CompiledProgram.fuelBudget
  exact (Program.blocksInLoweringOrder?_perm h).map CompiledBlock.fuelBudget
    |>.sum_eq

/-- The chain program's fuel budget likewise computed over the lowering order,
applying the SAME edit table `editTable program` (the transform reads the table
by label, which the permutation preserves). -/
theorem fuelBudget_chainCanonProgram_eq_sum_ordered
    {program : Program} {ordered : List Block}
    (h : program.blocksInLoweringOrder? = some ordered) :
    CompiledProgram.fuelBudget (chainCanonProgram program) =
      (ordered.map
        (fun b => CompiledBlock.fuelBudget (applyEdit (editTable program) b))).sum := by
  rw [fuelBudget_chainCanonProgram_eq]
  exact (Program.blocksInLoweringOrder?_perm h).map
    (fun b => CompiledBlock.fuelBudget (applyEdit (editTable program) b)) |>.sum_eq

end ShuffleCanon
end TypedCfg
end EvmCompiler
