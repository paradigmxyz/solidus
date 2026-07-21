import EvmCompiler.TypedCfg.ShuffleCanonChain

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

open TypedCfg (Block Program Label)
open InteractionSemantics

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
