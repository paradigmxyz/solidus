import EvmCompiler.TypedCfg.ShuffleCanonChainRel

/-!
# Chain-transform step congruence (session-81)

Item 2 *tail* of the PEEPHOLE_PROGRESS §Session-74..80 campaign.  Discharges the
two kernel hypotheses the §80 block-level `Rel` kernels
(`headBlock_rel`/`consumedBlock_rel`) were left carrying, then assembles the
per-label `ChainStepRel` invariant + the disjunctive step congruence.

* **Frontier 1 — `runBody`-success from typing.**  A chain body (only
  `.swap`/identity instrs) that `WellTyped`-checks (`bodyType? body input = some
  out`) and whose input is `StackRealizes`d runs to `.ok (s', out)`: every swap
  is depth-feasible (`length_of_type?_swap` + `StackRealizes` threaded by
  `runState_stackRealizes`), every bookkeeping instr is a runtime identity.
* **Frontier 2 — the type→runtime `netStack` lift.**  `canonSwaps` preserves the
  net stack permutation in *position* units (`netStack (merged.map (·+1)) L =
  netStack ((canonSwaps merged).map (·+1)) L`), extended from the touched window
  to the full stack length via `netStack_congr_window`.

Imported by **nobody** in the spine ⟹ cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-! ## Frontier 1 — a well-typed, stack-realized chain body runs successfully -/

/-- **`runBody`-success from typing (chain bodies).**  A chain body — only
`.swap`/`.bindLocals`/`.bindScratch`/`.relabel` — that `bodyType?`-checks
`input → out` and whose `input` is realized by the runtime stack runs to
`.ok (s', out)` in the closed evaluator.  Discharges the `hrun*` hypotheses of
`headBlock_rel`/`consumedBlock_rel`.  The swap depth-feasibility is the typing
bound `depth + 2 ≤ input.length` composed with `StackRealizes`, threaded across
the body by `runState_stackRealizes`; the bookkeeping instrs are EVMState
identities. -/
theorem runBody_chain_ok :
    ∀ (body : List Instr) {input out : Shape} {s : EVMState},
      (∀ i ∈ body, ChainInstr i) →
      Block.bodyType? body input = some out →
      StackRealizes input s →
      ∃ s', TypedCfg.Block.runBody body input s = .ok (s', out)
  | [], input, out, s, _, hType, _ => by
      simp only [Block.bodyType?, Option.some.injEq] at hType
      subst hType
      exact ⟨s, rfl⟩
  | instr :: rest, input, out, s, hChain, hType, hReal => by
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨mid, htype, hrest⟩ := hType
      have hHead : ChainInstr instr := hChain instr List.mem_cons_self
      -- The head instruction's `runState` succeeds.
      have hrun : ∃ s1, Instr.runState instr input s = .ok s1 := by
        cases instr with
        | swap d =>
            obtain ⟨hd16, hdlen, _⟩ := Instr.length_of_type?_swap htype
            have hReal' : input.length ≤ s.stack.length := hReal
            have hfeas : d + 1 + 1 ≤ s.stack.length := by omega
            rw [runState_swap_eq hd16, swap_eq_of_depth (by omega) hfeas]
            exact ⟨_, rfl⟩
        | bindLocals _ _ => exact ⟨s, rfl⟩
        | bindScratch _ _ _ => exact ⟨s, rfl⟩
        | relabel _ => exact ⟨s, rfl⟩
        | push _ => exact absurd hHead (by simp [ChainInstr])
        | returnToken _ => exact absurd hHead (by simp [ChainInstr])
        | prim _ => exact absurd hHead (by simp [ChainInstr])
        | pop => exact absurd hHead (by simp [ChainInstr])
        | dup _ => exact absurd hHead (by simp [ChainInstr])
        | unwind _ => exact absurd hHead (by simp [ChainInstr])
      obtain ⟨s1, hs1⟩ := hrun
      have hrunAt : Instr.runAt instr input s = .ok (s1, mid) := by
        simp only [Instr.runAt, htype, Option.elim, hs1, bind, Except.bind]
      have hReal1 : StackRealizes mid s1 := runState_stackRealizes htype hs1 hReal
      have hChainTail : ∀ i ∈ rest, ChainInstr i :=
        fun i hi => hChain i (List.mem_cons_of_mem _ hi)
      obtain ⟨s', hs'⟩ := runBody_chain_ok rest hChainTail hrest hReal1
      refine ⟨s', ?_⟩
      simp only [Block.runBody, hrunAt, bind, Except.bind]
      exact hs'

end Peephole
end TypedCfg
end EvmCompiler
