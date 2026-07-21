import EvmCompiler.TypedCfg.ShuffleCanonChainRuntime

/-!
# Block-level `PendingPerm` Rel kernels for the chain transform (session-80)

Item 2 *tail* of the PEEPHOLE_PROGRESS §Session-74..79 campaign: lift the banked
runtime foundation (`ShuffleCanonChainRuntime`: `runSwaps_ok`/`_resync`,
`PendingPerm` birth/peel/nil, `runBody_chain_state`) from the closed evaluator up
to the interaction-monad `openRunBody`, giving the three block-level Rel kernels
the step congruence (item 2) is built on:

* **consumed kernel** — the original body run threads `PendingPerm` (peel per
  block); the transformed body is empty.
* **head/birth kernel** — the fired head births `PendingPerm rest`.
* **exit** — `PendingPerm [] ⇒ SameRuntimeData` (`pendingPerm_nil_iff`, banked).

The genuinely-short path is the **non-`.prim` collapse**: a chain block's body
carries only `.swap`/`.bindLocals`/`.bindScratch`/`.relabel` (all non-`.prim`), so
`openRunBody body input s = .done (Block.runBody body input s)`
(`openRunBody_eq_done_of_forall_not_prim`), and `runBody_chain_state` rewrites the
closed `Block.runBody` to `runSwaps (bodyRunPositions body)`.  Every kernel is
therefore "collapse to `.done`, rewrite to `runSwaps`, apply the banked
`PendingPerm` lemma."

Imported by **nobody** in the spine ⟹ cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-! ## Part A — state-level: peel a whole run's worth of residual -/

/-- **Peel a run.**  If the original state is `ps ++ σ` swaps behind the
transformed state, and the original runs the whole `ps` (to `s_o'`), the residual
shrinks to `σ`.  The run-length generalisation of `pendingPerm_peel`. -/
theorem pendingPerm_peel_run {ps σ : List Nat} {s_c s_o s_o' : EVMState}
    (hP : PendingPerm (ps ++ σ) s_c s_o)
    (hrun : runSwaps ps s_o = .ok s_o') :
    PendingPerm σ s_c s_o' := by
  obtain ⟨next, hrunFull, hsrd⟩ := hP
  refine ⟨next, ?_, hsrd⟩
  rw [runSwaps_append ps σ s_o s_o' hrun] at hrunFull
  exact hrunFull

/-! ## Part B — a chain body's `openRunBody` collapses to `runSwaps` on `.done` -/

/-- A `ChainInstr` is never a `.prim`. -/
theorem chainInstr_not_prim {i : Instr} (h : ChainInstr i) : ∀ op, i ≠ .prim op := by
  intro op; cases i <;> simp_all [ChainInstr]

/-- **The chain-body `openRunBody` collapse.**  A chain block's body (only
`.swap`/identity instrs) runs in the *closed* evaluator, embedded as one completed
interaction: `openRunBody body input s = .done (Block.runBody body input s)`. -/
theorem openRunBody_chain_done {body : List Instr} {input : Shape} {s : EVMState}
    (hChain : ∀ i ∈ body, ChainInstr i) :
    InteractionSemantics.Block.openRunBody body input s
      = .done (TypedCfg.Block.runBody body input s) :=
  InteractionSemantics.Block.openRunBody_eq_done_of_forall_not_prim
    (fun i hi op => chainInstr_not_prim (hChain i hi) op)

/-! ## Part C — consumed-block kernel: the original body run threads `PendingPerm` -/

/-- **Consumed-block state kernel.**  A consumed chain member's original body
`body` runs (in the closed evaluator) from `s_o` to `s_o'`, peeling exactly its
own swap positions off the pending residual: from `PendingPerm (bodyRunPositions
body ++ σ)` the residual shrinks to `σ`.  The transformed member's body is empty
(no state motion), so this is the whole per-block thread. -/
theorem consumedBlock_pending {body : List Instr} {input out : Shape} {σ : List Nat}
    {s_c s_o s_o' : EVMState}
    (hChain : ∀ i ∈ body, ChainInstr i)
    (hsw16 : ∀ d, Instr.swap d ∈ body → d < 16)
    (hP : PendingPerm (bodyRunPositions body ++ σ) s_c s_o)
    (hrun : TypedCfg.Block.runBody body input s_o = .ok (s_o', out)) :
    PendingPerm σ s_c s_o' :=
  pendingPerm_peel_run hP (runBody_chain_state body hChain hsw16 hrun)

/-! ## Part D — head-block kernel: the fired head births `PendingPerm rest` -/

/-- **Head-block state kernel (birth).**  Entering the chain from `SameRuntimeData`
entry states, the ORIGINAL side runs the head block's body `headBody` (positions
`bodyRunPositions headBody`) while the TRANSFORMED side runs the whole
canonicalised head body `canonBody` (positions `bodyRunPositions canonBody`).  If
the full concatenation `bodyRunPositions headBody ++ rest` (= the whole chain's
positions) has the same `netStack` as `canonBody`, the residual `rest` is born:
`PendingPerm rest s_c1 s_o1`.  A thin `runBody_chain_state` lift of
`pendingPerm_birth`. -/
theorem headBlock_pending {headBody canonBody : List Instr} {rest : List Nat}
    {hin hout cin cout : Shape} {s_o0 s_c0 s_o1 s_c1 : EVMState}
    (hChainH : ∀ i ∈ headBody, ChainInstr i)
    (hsw16H : ∀ d, Instr.swap d ∈ headBody → d < 16)
    (hChainC : ∀ i ∈ canonBody, ChainInstr i)
    (hsw16C : ∀ d, Instr.swap d ∈ canonBody → d < 16)
    (hSRD : SameRuntimeData s_o0 s_c0)
    (hposM : ∀ p ∈ bodyRunPositions headBody ++ rest, 1 ≤ p)
    (hposC : ∀ p ∈ bodyRunPositions canonBody, 1 ≤ p)
    (hlenM : ∀ p ∈ bodyRunPositions headBody ++ rest, p + 1 ≤ s_o0.stack.length)
    (hlenC : ∀ p ∈ bodyRunPositions canonBody, p + 1 ≤ s_c0.stack.length)
    (hnet : ShuffleCanon.netStack (bodyRunPositions headBody ++ rest) s_o0.stack.length
      = ShuffleCanon.netStack (bodyRunPositions canonBody) s_o0.stack.length)
    (hrunO : TypedCfg.Block.runBody headBody hin s_o0 = .ok (s_o1, hout))
    (hrunC : TypedCfg.Block.runBody canonBody cin s_c0 = .ok (s_c1, cout)) :
    PendingPerm rest s_c1 s_o1 :=
  pendingPerm_birth hSRD hposM hposC hlenM hlenC hnet
    (runBody_chain_state headBody hChainH hsw16H hrunO)
    (runBody_chain_state canonBody hChainC hsw16C hrunC)

/-! ## Part E — `openRunBody`-level Rel kernels (the interaction-monad wrappers)

Both sides collapse to `.done` (chain bodies are non-`.prim`), so the block-body
`Rel` reduces to the state-level `PendingPerm` fact plus reflexive outputs.  The
original-body-success hypotheses (`hrun*`) are discharged from `WellTyped` +
`StackRealizes` at the step-congruence altitude. -/

/-- **Consumed-block `openRunBody` Rel kernel.**  From the pending residual
`bodyRunPositions body ++ σ`, the original consumed body and the transformed empty
body are `Rel`-related with the residual peeled to `σ`. -/
theorem consumedBlock_rel {body : List Instr} {input out finalOut : Shape} {σ : List Nat}
    {s_c s_o s_o' : EVMState}
    (hChain : ∀ i ∈ body, ChainInstr i)
    (hsw16 : ∀ d, Instr.swap d ∈ body → d < 16)
    (hP : PendingPerm (bodyRunPositions body ++ σ) s_c s_o)
    (hrun : TypedCfg.Block.runBody body input s_o = .ok (s_o', out)) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          PendingPerm σ rp.1 lp.1 ∧ lp.2 = out ∧ rp.2 = finalOut))
      (InteractionSemantics.Block.openRunBody body input s_o)
      (InteractionSemantics.Block.openRunBody [] finalOut s_c) := by
  rw [openRunBody_chain_done hChain, hrun,
    openRunBody_chain_done (body := []) (by intro i hi; cases hi)]
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok
      ⟨consumedBlock_pending hChain hsw16 hP hrun, rfl, rfl⟩)

/-- **Head-block `openRunBody` Rel kernel (birth).**  From `SameRuntimeData` entry
states, the original head body and the transformed canonicalised body are
`Rel`-related with the residual `rest` born. -/
theorem headBlock_rel {headBody canonBody : List Instr} {rest : List Nat}
    {hin hout cin cout : Shape} {s_o0 s_c0 s_o1 s_c1 : EVMState}
    (hChainH : ∀ i ∈ headBody, ChainInstr i)
    (hsw16H : ∀ d, Instr.swap d ∈ headBody → d < 16)
    (hChainC : ∀ i ∈ canonBody, ChainInstr i)
    (hsw16C : ∀ d, Instr.swap d ∈ canonBody → d < 16)
    (hSRD : SameRuntimeData s_o0 s_c0)
    (hposM : ∀ p ∈ bodyRunPositions headBody ++ rest, 1 ≤ p)
    (hposC : ∀ p ∈ bodyRunPositions canonBody, 1 ≤ p)
    (hlenM : ∀ p ∈ bodyRunPositions headBody ++ rest, p + 1 ≤ s_o0.stack.length)
    (hlenC : ∀ p ∈ bodyRunPositions canonBody, p + 1 ≤ s_c0.stack.length)
    (hnet : ShuffleCanon.netStack (bodyRunPositions headBody ++ rest) s_o0.stack.length
      = ShuffleCanon.netStack (bodyRunPositions canonBody) s_o0.stack.length)
    (hrunO : TypedCfg.Block.runBody headBody hin s_o0 = .ok (s_o1, hout))
    (hrunC : TypedCfg.Block.runBody canonBody cin s_c0 = .ok (s_c1, cout)) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          PendingPerm rest rp.1 lp.1 ∧ lp.2 = hout ∧ rp.2 = cout))
      (InteractionSemantics.Block.openRunBody headBody hin s_o0)
      (InteractionSemantics.Block.openRunBody canonBody cin s_c0) := by
  rw [openRunBody_chain_done hChainH, hrunO, openRunBody_chain_done hChainC, hrunC]
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok
      ⟨headBlock_pending hChainH hsw16H hChainC hsw16C hSRD hposM hposC hlenM hlenC hnet
        hrunO hrunC, rfl, rfl⟩)

end Peephole
end TypedCfg
end EvmCompiler
