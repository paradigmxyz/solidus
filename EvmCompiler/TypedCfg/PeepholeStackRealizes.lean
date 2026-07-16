import EvmCompiler.TypedCfg.Semantics
import EvmCompiler.TypedCfg.Preservation
import EvmCompiler.Assembly.PrimSemantics
import Mathlib.Tactic.IntervalCases

/-!
# Swap typing involution and the runtime `StackRealizes` invariant

Support lemmas for the `swap n ; swap n → ε` peephole arm (steps (1)–(2) of the
session-5 recipe in `PEEPHOLE_PROGRESS.md`).

Unlike `push v ; pop`, the swap cancellation is only sound when the runtime
stack is deep enough to actually perform the swap (`swap_swap_sameRuntimeData`
in `PeepholeSwapKernel.lean` carries an explicit `n + 1 ≤ stack.length` guard).
That depth fact is not available from `SameRuntimeData` + `bodyType?` alone: the
typing layer bounds the *shape* length, but nothing in the semantic layer ties
shape length to the *runtime* stack depth.  This module supplies the two missing
ingredients:

* `swap_type_involution` — the pure typing fact that `swap depth` is its own
  inverse on shapes (needed to carry the type transition across the cancelled
  pair);
* `StackRealizes` — the runtime invariant `shape.length ≤ state.stack.length`,
  with its single-step (`runAt`) and straight-line (`runBody`) preservation
  proved from the per-instruction stack-length facts already in
  `Assembly.PrimSemantics` / `TypedCfg.Preservation`.
-/

namespace EvmCompiler
namespace TypedCfg

namespace Instr

/-- **Swap typing involution.** `swap depth` is its own inverse at the shape
level: typing it twice returns to the original shape.  This mirrors the runtime
kernel `Peephole.swap_swap_sameRuntimeData` on the typing side, and is what lets
the cancelled `swap ; swap` pair carry `bodyType?` transparently. -/
theorem swap_type_involution {depth : Nat} {input output : Shape}
    (hType : Instr.type? (.swap depth) input = some output) :
    Instr.type? (.swap depth) output = some input := by
  -- Peel the `depth < 16` guard and the two structural matches of `type?`.
  by_cases hDepth : depth < 16
  · cases hSlots : input.slots with
    | nil =>
        simp [Instr.type?, hDepth, Shape.get?, hSlots] at hType
    | cons top rest =>
        cases hGet : input.get? (depth + 1) with
        | none =>
            simp [Instr.type?, hDepth, hSlots, hGet] at hType
        | some slot =>
            -- `output.slots = slot :: rest.set depth top`, `output.tail = input.tail`.
            simp only [Instr.type?, hDepth, if_true, hSlots, hGet] at hType
            -- Recover the shape components.
            have hOut : output = { input with slots := slot :: rest.set depth top } :=
              (Option.some.inj hType).symm
            -- `slot = rest[depth]?` and `depth < rest.length`.
            have hSlotGet : rest[depth]? = some slot := by
              have hEq : input.get? (depth + 1) = rest[depth]? := by
                simp [Shape.get?, hSlots]
              rw [hEq] at hGet; exact hGet
            have hDepthLt : depth < rest.length :=
              (List.getElem?_eq_some_iff.mp hSlotGet).1
            -- Compute `type? (.swap depth) output`.
            have hOutSlots : output.slots = slot :: rest.set depth top := by
              rw [hOut]
            have hOutGet : output.get? (depth + 1) = some top := by
              rw [Shape.get?, hOutSlots]
              rw [List.getElem?_cons_succ, List.getElem?_set]
              simp [hDepthLt]
            -- Now unfold `type? (.swap depth) output`.
            rw [Instr.type?]
            simp only [hDepth, if_true, hOutSlots, hOutGet]
            -- Result slots: `top :: (rest.set depth top).set depth slot`.
            -- `(rest.set depth top).set depth slot = rest.set depth slot = rest`.
            have hGetEq : rest[depth]'hDepthLt = slot := by
              have h := List.getElem?_eq_getElem hDepthLt
              rw [h] at hSlotGet
              exact Option.some.inj hSlotGet
            have hSetSet : (rest.set depth top).set depth slot = rest := by
              rw [List.set_set, ← hGetEq]
              exact List.set_getElem_self hDepthLt
            have hOutTail : output.tail = input.tail := by rw [hOut]
            -- Reassemble to `some input`.
            rw [hSetSet, ← hSlots, hOutTail]
  · simp [Instr.type?, hDepth] at hType

end Instr

/-- **Runtime stack-realization invariant.** The runtime stack is at least as
deep as the current type-state shape.  This is the semantic fact the swap
cancellation needs: from `StackRealizes input state` and the typing
`depth + 2 ≤ input.length` (which `type? (.swap depth)` demands), the kernel's
runtime guard `depth + 2 ≤ state.stack.length` follows. -/
def StackRealizes (shape : Shape) (state : EVMState) : Prop :=
  shape.length ≤ state.stack.length

namespace StackRealizes

theorem of_le {shape : Shape} {state : EVMState}
    (h : shape.length ≤ state.stack.length) : StackRealizes shape state := h

theorem le {shape : Shape} {state : EVMState}
    (h : StackRealizes shape state) : shape.length ≤ state.stack.length := h

end StackRealizes

/-- **Per-instruction `StackRealizes` preservation (`runState` version).**
If the runtime stack realizes the input shape and `instr` types `input` to
`output` and its runtime step succeeds, the resulting stack realizes `output`.
This is the single-step invariant threaded through the peephole body congruence
to discharge the swap-arm depth guard. -/
theorem runState_stackRealizes {instr : Instr} {input output : Shape}
    {state state' : EVMState}
    (hType : instr.type? input = some output)
    (hRunState : instr.runState input state = .ok state')
    (hReal : StackRealizes input state) :
    StackRealizes output state' := by
  unfold StackRealizes at hReal ⊢
  cases instr with
  | push value =>
      simp only [Instr.type?, Option.some.injEq] at hType
      simp only [Instr.runState] at hRunState
      subst hType; cases hRunState
      simp only [Shape.length, List.length_cons,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
        EvmYul.Stack.push, List.length_cons] at *
      omega
  | returnToken value =>
      simp only [Instr.type?, Option.some.injEq] at hType
      simp only [Instr.runState] at hRunState
      subst hType; cases hRunState
      simp only [Shape.length, List.length_cons,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
        EvmYul.Stack.push, List.length_cons] at *
      omega
  | prim op =>
      cases hArity : op.stackArity? with
      | none => simp [Instr.type?, hArity] at hType
      | some arity =>
          rcases arity with ⟨inArity, outArity⟩
          rcases Instr.length_of_type?_prim hArity hType with ⟨hIn, hOutLen⟩
          have hStepLen :=
            Assembly.PrimOp.step_stack_length_of_stackArity hArity
              (by simpa [Instr.runState] using hRunState)
          rw [hOutLen, hStepLen]
          omega
  | pop =>
      rcases Instr.length_of_type?_pop hType with ⟨hIn, hOutLen⟩
      have hStepLen :=
        Assembly.PrimOp.step_stack_length_of_stackArity
          (op := .pop) (by rfl) (by simpa [Instr.runState] using hRunState)
      rw [hOutLen]
      norm_num [EvmYul.EVM.δ, EvmYul.EVM.α, Assembly.PrimOp.toEVM] at hStepLen
      omega
  | dup depth =>
      rcases Instr.length_of_type?_dup hType with ⟨hDepth, hIn, hOutLen⟩
      rw [hOutLen]
      interval_cases depth <;>
        · simp only [Instr.runState] at hRunState
          have hStepLen :=
            Assembly.PrimOp.step_stack_length_of_stackArity (by rfl) hRunState
          norm_num [EvmYul.EVM.δ, EvmYul.EVM.α, Assembly.PrimOp.toEVM] at hStepLen
          omega
  | swap depth =>
      rcases Instr.length_of_type?_swap hType with ⟨hDepth, hIn, hOutLen⟩
      rw [hOutLen]
      interval_cases depth <;>
        · simp only [Instr.runState] at hRunState
          have hStepLen :=
            Assembly.PrimOp.step_stack_length_of_stackArity (by rfl) hRunState
          norm_num [EvmYul.EVM.δ, EvmYul.EVM.α, Assembly.PrimOp.toEVM] at hStepLen
          omega
  | bindLocals offset names =>
      rw [Instr.length_of_type?_bindLocals hType]
      simp only [Instr.runState] at hRunState
      cases hRunState; exact hReal
  | bindScratch baseDepth name slot =>
      rw [Instr.length_of_type?_bindScratch hType]
      simp only [Instr.runState] at hRunState
      cases hRunState; exact hReal
  | relabel target =>
      rw [Instr.length_of_type?_relabel hType]
      simp only [Instr.runState] at hRunState
      cases hRunState; exact hReal
  | unwind target =>
      -- `type? unwind = unwindTo target`, so `output = target`, `target.length ≤ input.length`.
      simp only [Instr.type?] at hType
      unfold Shape.unwindTo at hType
      by_cases hCond :
          target.tail = input.tail ∧ target.length ≤ input.length ∧
            input.slots.drop (input.length - target.length) = target.slots
      · rw [if_pos hCond] at hType
        have hOut : output = target := (Option.some.inj hType).symm
        rw [hOut]
        simp only [Instr.runState] at hRunState
        have hLen := Preservation.runPops_stack_length _ hRunState
        have hLe := hCond.2.1
        omega
      · rw [if_neg hCond] at hType
        exact absurd hType (by simp)

/-- **`StackRealizes` preservation across a single `runAt`.** -/
theorem runAt_stackRealizes {instr : Instr} {input output : Shape}
    {state state' : EVMState}
    (hRun : instr.runAt input state = .ok (state', output))
    (hReal : StackRealizes input state) :
    StackRealizes output state' := by
  unfold Instr.runAt at hRun
  cases hType : instr.type? input with
  | none => simp [hType] at hRun
  | some out =>
      cases hRunState : instr.runState input state with
      | error e => simp [hType, hRunState] at hRun
      | ok st =>
          simp only [hType, Option.elim, hRunState, Bind.bind, Except.bind,
            Except.ok.injEq, Prod.mk.injEq] at hRun
          obtain ⟨rfl, rfl⟩ := hRun
          exact runState_stackRealizes hType hRunState hReal

/-- **`StackRealizes` preservation across a straight-line body (`runBody`).**
The runtime stack realizing the block's input shape at entry is preserved to
realizing the body's output shape at exit. -/
theorem runBody_stackRealizes :
    ∀ (body : List Instr) {input output : Shape} {state state' : EVMState},
      Block.runBody body input state = .ok (state', output) →
      StackRealizes input state →
      StackRealizes output state'
  | [], input, output, state, state', hRun, hReal => by
      simp only [Block.runBody, Except.ok.injEq, Prod.mk.injEq] at hRun
      obtain ⟨rfl, rfl⟩ := hRun
      exact hReal
  | instr :: rest, input, output, state, state', hRun, hReal => by
      simp only [Block.runBody] at hRun
      cases hHead : instr.runAt input state with
      | error e => simp [hHead] at hRun
      | ok pair =>
          rcases pair with ⟨midState, midShape⟩
          simp only [hHead, Bind.bind, Except.bind] at hRun
          have hMidReal : StackRealizes midShape midState :=
            runAt_stackRealizes hHead hReal
          exact runBody_stackRealizes rest hRun hMidReal

end TypedCfg
end EvmCompiler
