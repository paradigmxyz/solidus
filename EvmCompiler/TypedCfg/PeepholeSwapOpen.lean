import EvmCompiler.TypedCfg.PeepholeOpen
import EvmCompiler.TypedCfg.PeepholeSwapKernel
import EvmCompiler.TypedCfg.PeepholeStackRealizes

/-!
# Depth-guarded `swap n ; swap n → ε` cancellation at the OPEN body level

Step (3) of the swap-arm recipe (`PEEPHOLE_PROGRESS.md`, session-5 note).

This is the swap-arm analogue of the `push v ; pop` cancel branch inside
`Peephole.openRunBody_peephole_congr`, isolated as a standalone lemma so the
landed, green push;pop tower and `peepholeBody` stay untouched.  It proves that
the cancelled body `rest` (run from `state1`) `Rel`-relates to the original body
`swap d ; swap d ; rest` (run from any `SameRuntimeData`-equivalent `state2`),
*provided* the runtime stack at `state2` realizes the current shape
(`StackRealizes input state2`) so the two swaps actually execute.  That depth
guard — absent for `push v ; pop`, which is unconditionally cancellable — is
exactly the extra hypothesis the swap arm carries.

Ingredients (all landed):
* `swap_swap_sameRuntimeData` (kernel) — the two swaps restore all runtime data;
* `swap_type_involution` — the two swaps restore the shape to `input`;
* `StackRealizes` + `Instr.length_of_type?_swap` — turn the shape depth guard
  `d + 2 ≤ input.length` into the runtime guard `d + 2 ≤ state2.stack.length`;
* the pre-existing `InteractionCongruence.Block.openRunBody_runtimeRel` to carry
  the `SameRuntimeData` shift through the shared tail `rest`.

Once `peepholeBody` gains the `swap d :: swap d :: rest → rest` arm (step 5),
this lemma discharges the new arm of `openRunBody_peephole_congr` directly.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-- `Instr.swap depth` dispatches to `EvmYul.swap (depth + 1)` at the runtime
transformer level (the trivial 16-way dispatch, uniform via `interval_cases`). -/
theorem runState_swap_eq {depth : Nat} (hDepth : depth < 16)
    (shape : Shape) (state : EVMState) :
    Instr.runState (.swap depth) shape state = EvmYul.swap (depth + 1) state := by
  interval_cases depth <;> rfl

/-- One `swap depth` step in the open body evaluator, when the swap succeeds. -/
theorem openRunBody_swap_cons_ok
    {depth : Nat} {rest : List Instr} {input middle : Shape}
    {state next : EVMState}
    (hType : Instr.type? (.swap depth) input = some middle)
    (hRun : Instr.runState (.swap depth) input state = .ok next) :
    Block.openRunBody (.swap depth :: rest) input state =
      Block.openRunBody rest middle next := by
  rw [openRunBody_nonprim_cons (by intro op; simp)]
  simp [TypedCfg.Instr.runAt, hType, hRun, Option.elim]

/-- **Depth-guarded open swap-swap cancellation (the swap-arm reduction).**
The cancelled tail `rest` from `state1` `Rel`-relates to the original
`swap d ; swap d ; rest` from a `SameRuntimeData`-equivalent `state2`, up to
runtime data.  The depth guard `StackRealizes input state2` is what lets the two
swaps execute; without it the original side would underflow where the cancelled
side succeeds. -/
theorem openRunBody_swap_swap_congr
    {depth : Nat} {rest : List Instr} {input output : Shape}
    {state1 state2 : EVMState}
    (hType : (Instr.type? (.swap depth) input).isSome)
    (hTailType : Block.bodyType? rest input = some output)
    (hTailPC : rest.Forall Instr.ProgramCounterIndependent)
    (hReal2 : StackRealizes input state2)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
      (Block.openRunBody rest input state1)
      (Block.openRunBody (.swap depth :: .swap depth :: rest) input state2) := by
  -- Recover the head typing and its shape/depth facts.
  obtain ⟨middle, hHeadType⟩ := Option.isSome_iff_exists.mp hType
  obtain ⟨hDepthLt, hShapeDepth, _hLen⟩ := Instr.length_of_type?_swap hHeadType
  -- The involution: the second swap takes `middle` back to `input`.
  have hHeadType2 : Instr.type? (.swap depth) middle = some input :=
    Instr.swap_type_involution hHeadType
  -- Turn the shape depth guard into the runtime depth guard on `state2`.
  have hRuntimeDepth : depth + 1 + 1 ≤ state2.stack.length :=
    le_trans hShapeDepth hReal2
  -- Fire the kernel on `state2` at `n = depth + 1`.
  obtain ⟨s1, s2, hSwap1, hSwap2, hSame⟩ :=
    swap_swap_sameRuntimeData state2 (depth + 1) (by omega) hRuntimeDepth
  -- Bridge `EvmYul.swap` back to `runState`.
  have hRun1 : Instr.runState (.swap depth) input state2 = .ok s1 := by
    rw [runState_swap_eq hDepthLt]; exact hSwap1
  have hRun2 : Instr.runState (.swap depth) middle s1 = .ok s2 := by
    rw [runState_swap_eq hDepthLt]; exact hSwap2
  -- Reduce the two open swap steps.
  rw [openRunBody_swap_cons_ok hHeadType hRun1,
      openRunBody_swap_cons_ok hHeadType2 hRun2]
  -- Now both sides run `rest` from `input`; the states are `SameRuntimeData`.
  have hSame12 : SameRuntimeData state1 s2 :=
    hRel.trans hSame.symm
  exact InteractionCongruence.Block.openRunBody_runtimeRel hTailType hTailPC hSame12

end Peephole
end TypedCfg
end EvmCompiler
