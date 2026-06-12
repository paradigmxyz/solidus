import EvmCompiler.Assembly.Assembler
import EvmCompiler.Assembly.StateRelation
import EvmYul.Semantics
import EvmYul.EVM.State
import EvmYul.EVM.StateOps

namespace EvmCompiler
namespace Assembly

/--
Small semantic families for EVM primitives that can be sequenced as ordinary
non-control instructions.

This classifier is deliberately separate from `PrimOp.toEVM`: byte encoding
still records the concrete EVM opcode, while proofs can reason through these
compact public EVMYul helper functions instead of unfolding the full
`EvmYul.step` dispatcher.
-/
inductive PrimStep where
  | bin (f : EvmYul.Primop.Binary)
  | un (f : EvmYul.Primop.Unary)
  | tri (f : EvmYul.Primop.Ternary)
  | executionEnv
      (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
  | unaryExecutionEnv
      (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
  | machineState (f : EvmYul.MachineState → Word)
  | binaryMachineState
      (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
  | binaryMachineStateWithResult
      (f : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState)
  | ternaryMachineState
      (f : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
  | state (f : EvmYul.State EvmYul.OperationType.EVM → Word)
  | unaryState
      (f : EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
  | binaryState
      (f : EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
  | ternaryCopy
      (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → EvmYul.SharedState EvmYul.OperationType.EVM)
  | quaternaryCopy
      (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → Word → EvmYul.SharedState EvmYul.OperationType.EVM)
  | pop
  | mload
  | returndatacopy
  | dup (n : Nat)
  | swap (n : Nat)
  | log0
  | log1
  | log2
  | log3
  | log4
  | invalid

namespace PrimStep

namespace Stack

variable {α : Type}

theorem pop_append_of_some {stack tail rest : EvmYul.Stack α} {a : α}
    (h : EvmYul.Stack.pop stack = some (rest, a)) :
    EvmYul.Stack.pop (stack ++ tail) = some (rest ++ tail, a) := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop] at h
  | cons x xs =>
      simp [EvmYul.Stack.pop] at h ⊢
      rcases h with ⟨hRest, hA⟩
      subst rest
      subst a
      simp

theorem length_of_pop_some {stack rest : EvmYul.Stack α} {a : α}
    (h : EvmYul.Stack.pop stack = some (rest, a)) :
    stack.length = rest.length + 1 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop] at h
  | cons x xs =>
      simp [EvmYul.Stack.pop] at h
      rcases h with ⟨hRest, hA⟩
      subst rest
      simp

theorem pop2_append_of_some {stack tail rest : EvmYul.Stack α}
    {a b : α}
    (h : EvmYul.Stack.pop2 stack = some (rest, a, b)) :
    EvmYul.Stack.pop2 (stack ++ tail) = some (rest ++ tail, a, b) := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop2] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop2] at h
      | cons y ys =>
          simp [EvmYul.Stack.pop2] at h ⊢
          rcases h with ⟨hRest, hA, hB⟩
          subst rest
          subst a
          subst b
          simp

theorem length_of_pop2_some {stack rest : EvmYul.Stack α}
    {a b : α}
    (h : EvmYul.Stack.pop2 stack = some (rest, a, b)) :
    stack.length = rest.length + 2 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop2] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop2] at h
      | cons y ys =>
          simp [EvmYul.Stack.pop2] at h
          rcases h with ⟨hRest, hA, hB⟩
          subst rest
          simp

theorem pop3_append_of_some {stack tail rest : EvmYul.Stack α}
    {a b c : α}
    (h : EvmYul.Stack.pop3 stack = some (rest, a, b, c)) :
    EvmYul.Stack.pop3 (stack ++ tail) = some (rest ++ tail, a, b, c) := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop3] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop3] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop3] at h
          | cons z zs =>
              simp [EvmYul.Stack.pop3] at h ⊢
              rcases h with ⟨hRest, hA, hB, hC⟩
              subst rest
              subst a
              subst b
              subst c
              simp

theorem length_of_pop3_some {stack rest : EvmYul.Stack α}
    {a b c : α}
    (h : EvmYul.Stack.pop3 stack = some (rest, a, b, c)) :
    stack.length = rest.length + 3 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop3] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop3] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop3] at h
          | cons z zs =>
              simp [EvmYul.Stack.pop3] at h
              rcases h with ⟨hRest, hA, hB, hC⟩
              subst rest
              simp

theorem pop4_append_of_some {stack tail rest : EvmYul.Stack α}
    {a b c d : α}
    (h : EvmYul.Stack.pop4 stack = some (rest, a, b, c, d)) :
    EvmYul.Stack.pop4 (stack ++ tail) = some (rest ++ tail, a, b, c, d) := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop4] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop4] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop4] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop4] at h
              | cons w ws =>
                  simp [EvmYul.Stack.pop4] at h ⊢
                  rcases h with ⟨hRest, hA, hB, hC, hD⟩
                  subst rest
                  subst a
                  subst b
                  subst c
                  subst d
                  simp

theorem length_of_pop4_some {stack rest : EvmYul.Stack α}
    {a b c d : α}
    (h : EvmYul.Stack.pop4 stack = some (rest, a, b, c, d)) :
    stack.length = rest.length + 4 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop4] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop4] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop4] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop4] at h
              | cons w ws =>
                  simp [EvmYul.Stack.pop4] at h
                  rcases h with ⟨hRest, hA, hB, hC, hD⟩
                  subst rest
                  simp

theorem pop5_append_of_some {stack tail rest : EvmYul.Stack α}
    {a b c d e : α}
    (h : EvmYul.Stack.pop5 stack = some (rest, a, b, c, d, e)) :
    EvmYul.Stack.pop5 (stack ++ tail) =
      some (rest ++ tail, a, b, c, d, e) := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop5] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop5] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop5] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop5] at h
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop5] at h
                  | cons v vs =>
                      simp [EvmYul.Stack.pop5] at h ⊢
                      rcases h with ⟨hRest, hA, hB, hC, hD, hE⟩
                      subst rest
                      subst a
                      subst b
                      subst c
                      subst d
                      subst e
                      simp

theorem length_of_pop5_some {stack rest : EvmYul.Stack α}
    {a b c d e : α}
    (h : EvmYul.Stack.pop5 stack = some (rest, a, b, c, d, e)) :
    stack.length = rest.length + 5 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop5] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop5] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop5] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop5] at h
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop5] at h
                  | cons v vs =>
                      simp [EvmYul.Stack.pop5] at h
                      rcases h with ⟨hRest, hA, hB, hC, hD, hE⟩
                      subst rest
                      simp

theorem pop6_append_of_some {stack tail rest : EvmYul.Stack α}
    {a b c d e f : α}
    (h : EvmYul.Stack.pop6 stack = some (rest, a, b, c, d, e, f)) :
    EvmYul.Stack.pop6 (stack ++ tail) =
      some (rest ++ tail, a, b, c, d, e, f) := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop6] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop6] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop6] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop6] at h
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop6] at h
                  | cons v vs =>
                      cases vs with
                      | nil => simp [EvmYul.Stack.pop6] at h
                      | cons u us =>
                          simp [EvmYul.Stack.pop6] at h ⊢
                          rcases h with ⟨hRest, hA, hB, hC, hD, hE, hF⟩
                          subst rest
                          subst a
                          subst b
                          subst c
                          subst d
                          subst e
                          subst f
                          simp

theorem length_of_pop6_some {stack rest : EvmYul.Stack α}
    {a b c d e f : α}
    (h : EvmYul.Stack.pop6 stack = some (rest, a, b, c, d, e, f)) :
    stack.length = rest.length + 6 := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop6] at h
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop6] at h
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop6] at h
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop6] at h
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop6] at h
                  | cons v vs =>
                      cases vs with
                      | nil => simp [EvmYul.Stack.pop6] at h
                      | cons u us =>
                          simp [EvmYul.Stack.pop6] at h
                          rcases h with ⟨hRest, hA, hB, hC, hD, hE, hF⟩
                          subst rest
                          simp

theorem exists_pop_of_one_le
    {stack : EvmYul.Stack α} (h : 1 ≤ stack.length) :
    ∃ rest a, EvmYul.Stack.pop stack = some (rest, a) := by
  cases stack with
  | nil => simp at h
  | cons a rest => exact ⟨rest, a, rfl⟩

theorem exists_pop2_of_two_le
    {stack : EvmYul.Stack α} (h : 2 ≤ stack.length) :
    ∃ rest a b, EvmYul.Stack.pop2 stack = some (rest, a, b) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail => exact ⟨tail, a, b, rfl⟩

theorem exists_pop3_of_three_le
    {stack : EvmYul.Stack α} (h : 3 ≤ stack.length) :
    ∃ rest a b c,
      EvmYul.Stack.pop3 stack = some (rest, a, b, c) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail =>
          cases tail with
          | nil => simp at h
          | cons c suffix => exact ⟨suffix, a, b, c, rfl⟩

theorem exists_pop4_of_four_le
    {stack : EvmYul.Stack α} (h : 4 ≤ stack.length) :
    ∃ rest a b c d,
      EvmYul.Stack.pop4 stack = some (rest, a, b, c, d) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail =>
          cases tail with
          | nil => simp at h
          | cons c suffix =>
              cases suffix with
              | nil => simp at h
              | cons d final => exact ⟨final, a, b, c, d, rfl⟩

theorem exists_pop5_of_five_le
    {stack : EvmYul.Stack α} (h : 5 ≤ stack.length) :
    ∃ rest a b c d e,
      EvmYul.Stack.pop5 stack = some (rest, a, b, c, d, e) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail =>
          cases tail with
          | nil => simp at h
          | cons c suffix =>
              cases suffix with
              | nil => simp at h
              | cons d final =>
                  cases final with
                  | nil => simp at h
                  | cons e last => exact ⟨last, a, b, c, d, e, rfl⟩

theorem exists_pop6_of_six_le
    {stack : EvmYul.Stack α} (h : 6 ≤ stack.length) :
    ∃ rest a b c d e f,
      EvmYul.Stack.pop6 stack = some (rest, a, b, c, d, e, f) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail =>
          cases tail with
          | nil => simp at h
          | cons c suffix =>
              cases suffix with
              | nil => simp at h
              | cons d final =>
                  cases final with
                  | nil => simp at h
                  | cons e last =>
                      cases last with
                      | nil => simp at h
                      | cons f remaining =>
                          exact ⟨remaining, a, b, c, d, e, f, rfl⟩

end Stack

def run (step : PrimStep) (state : EvmYul.EVM.State) :
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State :=
  match step with
  | .bin f => EvmYul.EVM.execBinOp f state
  | .un f => EvmYul.EVM.execUnOp f state
  | .tri f => EvmYul.EVM.execTriOp f state
  | .executionEnv f => EvmYul.EVM.executionEnvOp f state
  | .unaryExecutionEnv f => EvmYul.EVM.unaryExecutionEnvOp f state
  | .machineState f => EvmYul.EVM.machineStateOp f state
  | .binaryMachineState f => EvmYul.EVM.binaryMachineStateOp f state
  | .binaryMachineStateWithResult f => EvmYul.EVM.binaryMachineStateOp' f state
  | .ternaryMachineState f => EvmYul.EVM.ternaryMachineStateOp f state
  | .state f => EvmYul.EVM.stateOp f state
  | .unaryState f => EvmYul.EVM.unaryStateOp f state
  | .binaryState f => EvmYul.EVM.binaryStateOp f state
  | .ternaryCopy f => EvmYul.EVM.ternaryCopyOp f state
  | .quaternaryCopy f => EvmYul.EVM.quaternaryCopyOp f state
  | .pop =>
      match state.stack.pop with
      | some ⟨stack, _⟩ => .ok <| state.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .mload =>
      match state.stack.pop with
      | some ⟨stack, μ₀⟩ =>
          let (value, mState') := state.toMachineState.mload μ₀
          let state' := { state with toMachineState := mState' }
          .ok <| state'.replaceStackAndIncrPC (stack.push value)
      | none => .error .StackUnderflow
  | .returndatacopy =>
      match state.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ =>
          if state.returnData.size < μ₁.toNat + μ₂.toNat then
            .error .InvalidMemoryAccess
          else
            let mState' := state.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let state' := { state with toMachineState := mState' }
            .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .dup n => EvmYul.dup n state
  | .swap n => EvmYul.swap n state
  | .log0 =>
      match state.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[] state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log1 =>
      match state.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂] state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log2 =>
      match state.stack.pop4 with
      | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂, μ₃] state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log3 =>
      match state.stack.pop5 with
      | some ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂, μ₃, μ₄]
              state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .log4 =>
      match state.stack.pop6 with
      | some ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ =>
          let sharedState' :=
            EvmYul.SharedState.logOp μ₀ μ₁ #[μ₂, μ₃, μ₄, μ₅]
              state.toSharedState
          let state' := { state with toSharedState := sharedState' }
          .ok <| state'.replaceStackAndIncrPC stack
      | none => .error .StackUnderflow
  | .invalid => .error .InvalidInstruction

theorem run_pc {step : PrimStep}
    {state final : EvmYul.EVM.State}
    (hRun : step.run state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases step <;>
    simp [PrimStep.run, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.machineStateOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun ⊢
  all_goals
    try
      cases hRun
      rfl
  all_goals
    try
      simp [EvmYul.dup, EvmYul.swap,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hRun
    repeat' split at hRun
  all_goals
    try simp_all
  all_goals
    cases hRun
    rfl

abbrev isoState (shared : EvmYul.SharedState .EVM)
    (stack : EvmYul.Stack Word) : EvmYul.EVM.State :=
  { toSharedState := shared,
    pc := EvmYul.UInt256.ofNat 0,
    stack := stack,
    execLength := 0 }

theorem run_suffix_sound_un
    (f : EvmYul.Primop.Unary)
    {shared : EvmYul.SharedState .EVM}
    {stack base : EvmYul.Stack Word}
    {iso' evm evm' : EvmYul.EVM.State}
    (hIso : (PrimStep.un f).run (isoState shared stack) = .ok iso')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = stack ++ base)
    (hRun : (PrimStep.un f).run evm = .ok evm') :
    evm'.toSharedState = iso'.toSharedState ∧
      evm'.stack = iso'.stack ++ base := by
  simp [PrimStep.run, EvmYul.EVM.execUnOp] at hIso hRun
  cases hPop : stack.pop with
  | none => simp [hPop] at hIso
  | some tup =>
      rcases tup with ⟨rest, a⟩
      have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
      rw [hStack, hPopTarget] at hRun
      simp [hPop, hShared, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hIso hRun ⊢
      cases hIso
      cases hRun
      simp [EvmYul.Stack.push]

theorem run_suffix_sound_bin
    (f : EvmYul.Primop.Binary)
    {shared : EvmYul.SharedState .EVM}
    {stack base : EvmYul.Stack Word}
    {iso' evm evm' : EvmYul.EVM.State}
    (hIso : (PrimStep.bin f).run (isoState shared stack) = .ok iso')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = stack ++ base)
    (hRun : (PrimStep.bin f).run evm = .ok evm') :
    evm'.toSharedState = iso'.toSharedState ∧
      evm'.stack = iso'.stack ++ base := by
  simp [PrimStep.run, EvmYul.EVM.execBinOp] at hIso hRun
  cases hPop : stack.pop2 with
  | none => simp [hPop] at hIso
  | some tup =>
      rcases tup with ⟨rest, a, b⟩
      have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
      rw [hStack, hPopTarget] at hRun
      simp [hPop, hShared, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hIso hRun ⊢
      cases hIso
      cases hRun
      simp [EvmYul.Stack.push]

theorem run_suffix_sound_tri
    (f : EvmYul.Primop.Ternary)
    {shared : EvmYul.SharedState .EVM}
    {stack base : EvmYul.Stack Word}
    {iso' evm evm' : EvmYul.EVM.State}
    (hIso : (PrimStep.tri f).run (isoState shared stack) = .ok iso')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = stack ++ base)
    (hRun : (PrimStep.tri f).run evm = .ok evm') :
    evm'.toSharedState = iso'.toSharedState ∧
      evm'.stack = iso'.stack ++ base := by
  simp [PrimStep.run, EvmYul.EVM.execTriOp] at hIso hRun
  cases hPop : stack.pop3 with
  | none => simp [hPop] at hIso
  | some tup =>
      rcases tup with ⟨rest, a, b, c⟩
      have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
      rw [hStack, hPopTarget] at hRun
      simp [hPop, hShared, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hIso hRun ⊢
      cases hIso
      cases hRun
      simp [EvmYul.Stack.push]

def SuffixSafe : PrimStep → Prop
  | .dup _ | .swap _ => False
  | _ => True

def inputArity : PrimStep → Nat
  | .un _ | .unaryExecutionEnv _ | .unaryState _ | .pop | .mload => 1
  | .bin _ | .binaryMachineState _ | .binaryMachineStateWithResult _
  | .binaryState _ | .log0 => 2
  | .tri _ | .ternaryMachineState _ | .ternaryCopy _ | .returndatacopy
  | .log1 => 3
  | .quaternaryCopy _ | .log2 => 4
  | .log3 => 5
  | .log4 => 6
  | .executionEnv _ | .machineState _ | .state _ | .invalid => 0
  | .dup n => n
  | .swap n => n + 1

def outputArity : PrimStep → Nat
  | .un _ | .bin _ | .tri _ | .executionEnv _ | .machineState _
  | .state _ | .unaryExecutionEnv _ | .unaryState _
  | .binaryMachineStateWithResult _ | .mload => 1
  | .dup n => n + 1
  | .swap n => n + 1
  | _ => 0

theorem run_inputArity_le
    {step : Assembly.PrimStep}
    {state evm' : EvmYul.EVM.State}
    (hRun : step.run state = .ok evm') :
    inputArity step ≤ state.stack.length := by
  cases step
  case invalid =>
    simp [PrimStep.run] at hRun
  all_goals
    simp [PrimStep.run, inputArity, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.machineStateOp,
      EvmYul.EVM.stateOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp]
      at hRun ⊢
  case bin f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b⟩
        have hLen := Stack.length_of_pop2_some hPop
        omega
  case un f =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a⟩
        have hLen := Stack.length_of_pop_some hPop
        omega
  case tri f =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c⟩
        have hLen := Stack.length_of_pop3_some hPop
        omega
  case unaryExecutionEnv f =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a⟩
        have hLen := Stack.length_of_pop_some hPop
        omega
  case unaryState f =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a⟩
        have hLen := Stack.length_of_pop_some hPop
        omega
  case binaryMachineState f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b⟩
        have hLen := Stack.length_of_pop2_some hPop
        omega
  case binaryMachineStateWithResult f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b⟩
        have hLen := Stack.length_of_pop2_some hPop
        omega
  case ternaryMachineState f =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c⟩
        have hLen := Stack.length_of_pop3_some hPop
        omega
  case binaryState f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b⟩
        have hLen := Stack.length_of_pop2_some hPop
        omega
  case ternaryCopy f =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c⟩
        have hLen := Stack.length_of_pop3_some hPop
        omega
  case quaternaryCopy f =>
    cases hPop : state.stack.pop4 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c, d⟩
        have hLen := Stack.length_of_pop4_some hPop
        omega
  case pop =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a⟩
        have hLen := Stack.length_of_pop_some hPop
        omega
  case mload =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a⟩
        have hLen := Stack.length_of_pop_some hPop
        omega
  case returndatacopy =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c⟩
        have hLen := Stack.length_of_pop3_some hPop
        omega
  case dup n =>
    by_cases hLen : n ≤ state.stack.length
    · exact hLen
    · simp [EvmYul.dup, hLen] at hRun
  case swap n =>
    by_cases hLen : n + 1 ≤ state.stack.length
    · exact hLen
    · simp [EvmYul.swap, hLen] at hRun
  case log0 =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b⟩
        have hLen := Stack.length_of_pop2_some hPop
        omega
  case log1 =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c⟩
        have hLen := Stack.length_of_pop3_some hPop
        omega
  case log2 =>
    cases hPop : state.stack.pop4 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c, d⟩
        have hLen := Stack.length_of_pop4_some hPop
        omega
  case log3 =>
    cases hPop : state.stack.pop5 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c, d, e⟩
        have hLen := Stack.length_of_pop5_some hPop
        omega
  case log4 =>
    cases hPop : state.stack.pop6 with
    | none => simp [hPop] at hRun
    | some popped =>
        rcases popped with ⟨rest, a, b, c, d, e, f⟩
        have hLen := Stack.length_of_pop6_some hPop
        omega

theorem idRun_eq {α : Type} (value : α) :
    Id.run value = value :=
  rfl

attribute [local simp] idRun_eq in
/--
If a primitive's declared operands fit in the source stack prefix, appending a
hidden suffix cannot turn a failing source primitive into a successful one.
-/
theorem exists_run_of_inputArity_le_of_append_run
    {step : Assembly.PrimStep}
    {state framedFinal : EvmYul.EVM.State}
    {hidden : EvmYul.Stack Word}
    (hBound : inputArity step ≤ state.stack.length)
    (hFramed :
      step.run { state with stack := state.stack ++ hidden } =
        .ok framedFinal) :
    ∃ final, step.run state = .ok final := by
  cases step with
  | bin f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Stack.exists_pop2_of_two_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop]
  | un f =>
      obtain ⟨rest, a, hPop⟩ :=
        Stack.exists_pop_of_one_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop]
  | tri f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Stack.exists_pop3_of_three_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop]
  | executionEnv f =>
      simp [PrimStep.run, EvmYul.EVM.executionEnvOp,
        EvmYul.Stack.push]
  | unaryExecutionEnv f =>
      obtain ⟨rest, a, hPop⟩ :=
        Stack.exists_pop_of_one_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp,
        hPop, EvmYul.Stack.push]
  | machineState f =>
      simp [PrimStep.run, EvmYul.EVM.machineStateOp,
        EvmYul.Stack.push]
  | binaryMachineState f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Stack.exists_pop2_of_two_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp,
        hPop]
  | binaryMachineStateWithResult f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Stack.exists_pop2_of_two_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp',
        hPop, EvmYul.Stack.push]
  | ternaryMachineState f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Stack.exists_pop3_of_three_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp,
        hPop]
  | state f =>
      simp [PrimStep.run, EvmYul.EVM.stateOp,
        EvmYul.Stack.push]
  | unaryState f =>
      obtain ⟨rest, a, hPop⟩ :=
        Stack.exists_pop_of_one_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp,
        hPop, EvmYul.Stack.push]
  | binaryState f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Stack.exists_pop2_of_two_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp,
        hPop]
  | ternaryCopy f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Stack.exists_pop3_of_three_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp,
        hPop]
  | quaternaryCopy f =>
      obtain ⟨rest, a, b, c, d, hPop⟩ :=
        Stack.exists_pop4_of_four_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp,
        hPop]
  | pop =>
      obtain ⟨rest, a, hPop⟩ :=
        Stack.exists_pop_of_one_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | mload =>
      obtain ⟨rest, a, hPop⟩ :=
        Stack.exists_pop_of_one_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop, EvmYul.Stack.push]
  | returndatacopy =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Stack.exists_pop3_of_three_le (by simpa [inputArity] using hBound)
      have hFramedPop :=
        Stack.pop3_append_of_some (tail := hidden) hPop
      by_cases hInvalid :
          state.returnData.size < b.toNat + c.toNat
      · simp [PrimStep.run, hFramedPop, hInvalid] at hFramed
      · simp [PrimStep.run, hPop, hInvalid]
  | dup n =>
      simp only [inputArity] at hBound
      simp [PrimStep.run, EvmYul.dup, List.length_take,
        Nat.min_eq_left hBound, hBound]
  | swap n =>
      simp only [inputArity] at hBound
      simp [PrimStep.run, EvmYul.swap, List.length_take,
        Nat.min_eq_left hBound, hBound]
  | log0 =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Stack.exists_pop2_of_two_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | log1 =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Stack.exists_pop3_of_three_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | log2 =>
      obtain ⟨rest, a, b, c, d, hPop⟩ :=
        Stack.exists_pop4_of_four_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | log3 =>
      obtain ⟨rest, a, b, c, d, e, hPop⟩ :=
        Stack.exists_pop5_of_five_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | log4 =>
      obtain ⟨rest, a, b, c, d, e, f, hPop⟩ :=
        Stack.exists_pop6_of_six_le (by simpa [inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | invalid =>
      simp [PrimStep.run] at hFramed

theorem run_isolated_length_safe
    {step : Assembly.PrimStep}
    {shared : EvmYul.SharedState .EVM}
    {stack : EvmYul.Stack Word} {evm' : EvmYul.EVM.State}
    (hSafe : SuffixSafe step)
    (hLen : stack.length = inputArity step)
    (hRun : step.run (isoState shared stack) = .ok evm') :
    evm'.stack.length = outputArity step := by
  cases step
  case bin f =>
    simp [PrimStep.run, inputArity, outputArity, EvmYul.EVM.execBinOp] at hRun hLen ⊢
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop2_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case un f =>
    simp [PrimStep.run, inputArity, outputArity, EvmYul.EVM.execUnOp] at hRun hLen ⊢
    cases hPop : stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case tri f =>
    simp [PrimStep.run, inputArity, outputArity, EvmYul.EVM.execTriOp] at hRun hLen ⊢
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop3_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case dup n => contradiction
  case swap n => contradiction
  case invalid => simp [PrimStep.run] at hRun
  all_goals
    simp [PrimStep.run, inputArity, outputArity, EvmYul.EVM.executionEnvOp,
      EvmYul.EVM.machineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryExecutionEnvOp, EvmYul.EVM.unaryStateOp,
      EvmYul.EVM.binaryStateOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp', EvmYul.EVM.ternaryMachineStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      EvmYul.Stack.push] at hRun hLen ⊢
  case executionEnv f =>
    cases hRun
    simp [hLen]
  case machineState f =>
    cases hRun
    simp [hLen]
  case state f =>
    cases hRun
    simp [hLen]
  case unaryExecutionEnv f =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case unaryState f =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case pop =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case mload =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case binaryMachineState f =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop2_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case binaryMachineStateWithResult f =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        have hRestLen := Stack.length_of_pop2_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case binaryState f =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop2_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case log0 =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop2_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case ternaryMachineState f =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop3_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case ternaryCopy f =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop3_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case returndatacopy =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        split at hRun
        · simp at hRun
        have hRestLen := Stack.length_of_pop3_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case log1 =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop3_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case quaternaryCopy f =>
    cases hPop : stack.pop4 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop4_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case log2 =>
    cases hPop : stack.pop4 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop4_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case log3 =>
    cases hPop : stack.pop5 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d, e⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop5_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]
  case log4 =>
    cases hPop : stack.pop6 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d, e, f⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        have hRestLen := Stack.length_of_pop6_some hPop
        have hRestZero : rest.length = 0 := by
          rw [hRestLen] at hLen
          omega
        cases hRun
        first
        | exact List.eq_nil_of_length_eq_zero hRestZero
        | simp [hRestZero]

theorem run_stack_length_safe
    {step : Assembly.PrimStep}
    {state evm' : EvmYul.EVM.State}
    (hSafe : SuffixSafe step)
    (hRun : step.run state = .ok evm') :
    evm'.stack.length =
      state.stack.length - inputArity step + outputArity step := by
  cases step
  case dup n => contradiction
  case swap n => contradiction
  case invalid => simp [PrimStep.run] at hRun
  all_goals
    simp [PrimStep.run, inputArity, outputArity, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.machineStateOp,
      EvmYul.EVM.stateOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.ternaryCopyOp,
      EvmYul.EVM.quaternaryCopyOp, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
  case bin f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop2_some hPop
        simp [EvmYul.Stack.push, hLen]
  case un f =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop_some hPop
        simp [EvmYul.Stack.push, hLen]
  case tri f =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop3_some hPop
        simp [EvmYul.Stack.push, hLen]
  case executionEnv f =>
    cases hRun
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  case machineState f =>
    cases hRun
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  case state f =>
    cases hRun
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  case unaryExecutionEnv f =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop_some hPop
        simp [EvmYul.Stack.push, hLen]
  case unaryState f =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop_some hPop
        simp [EvmYul.Stack.push, hLen]
  case pop =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop_some hPop
        simp [hLen]
  case mload =>
    cases hPop : state.stack.pop with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop_some hPop
        simp [EvmYul.Stack.push, hLen]
  case binaryMachineState f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop2_some hPop
        simp [hLen]
  case binaryMachineStateWithResult f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop2_some hPop
        simp [EvmYul.Stack.push, hLen]
  case binaryState f =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop2_some hPop
        simp [hLen]
  case log0 =>
    cases hPop : state.stack.pop2 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop2_some hPop
        simp [hLen]
  case ternaryMachineState f =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop3_some hPop
        simp [hLen]
  case ternaryCopy f =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop3_some hPop
        simp [hLen]
  case returndatacopy =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        split at hRun
        · simp at hRun
        cases hRun
        have hLen := Stack.length_of_pop3_some hPop
        simp [hLen]
  case log1 =>
    cases hPop : state.stack.pop3 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop3_some hPop
        simp [hLen]
  case quaternaryCopy f =>
    cases hPop : state.stack.pop4 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop4_some hPop
        simp [hLen]
  case log2 =>
    cases hPop : state.stack.pop4 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop4_some hPop
        simp [hLen]
  case log3 =>
    cases hPop : state.stack.pop5 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d, e⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop5_some hPop
        simp [hLen]
  case log4 =>
    cases hPop : state.stack.pop6 with
    | none => simp [hPop] at hRun
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d, e, f⟩
        simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hRun ⊢
        cases hRun
        have hLen := Stack.length_of_pop6_some hPop
        simp [hLen]

theorem run_dup_stack_length
    {n : Nat} {state evm' : EvmYul.EVM.State}
    (hRun : (PrimStep.dup n).run state = .ok evm') :
    evm'.stack.length = state.stack.length + 1 := by
  by_cases hLen : n ≤ state.stack.length
  · simp [PrimStep.run, EvmYul.dup, hLen,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun
    cases hRun
    simp
  · simp [PrimStep.run, EvmYul.dup, hLen] at hRun

theorem run_swap_stack_length_of_pos
    {n : Nat} {state evm' : EvmYul.EVM.State}
    (hPos : 1 ≤ n)
    (hRun : (PrimStep.swap n).run state = .ok evm') :
    evm'.stack.length = state.stack.length := by
  by_cases hLen : n + 1 ≤ state.stack.length
  · simp [PrimStep.run, EvmYul.swap, hLen,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun
    cases hRun
    let top := state.stack.take (n + 1)
    let bottom := state.stack.drop (n + 1)
    have hTopLen : top.length = n + 1 := by
      simp [top, hLen]
    have hSplitLen : state.stack.length = top.length + bottom.length := by
      rw [← List.length_append, List.take_append_drop]
    have hPostLen :
        (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom).length =
          top.length + bottom.length := by
      cases hTop : top with
      | nil =>
          simp [hTop] at hTopLen
      | cons head tail =>
          cases hTail : tail with
          | nil =>
              simp [hTop, hTail] at hTopLen
              omega
          | cons next rest =>
              simp [hTop, hTail, List.length_dropLast]
              omega
    have hPost :
        (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom).length =
          state.stack.length := by
      calc
        (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom).length
            = top.length + bottom.length := hPostLen
      _ = state.stack.length := by omega
    simpa [top, bottom] using hPost
  · simp [PrimStep.run, EvmYul.swap, hLen] at hRun

theorem run_stack_le_of_arity_bound
    {step : Assembly.PrimStep}
    {state evm' : EvmYul.EVM.State}
    (hStack : inputArity step ≤ state.stack.length)
    (hBound :
      state.stack.length - inputArity step + outputArity step ≤ 1024)
    (hSwapPos : ∀ n, step = .swap n → 1 ≤ n)
    (hRun : step.run state = .ok evm') :
    evm'.stack.length ≤ 1024 := by
  cases step
  case dup n =>
    have hLen := run_dup_stack_length hRun
    simp [inputArity, outputArity] at hStack hBound
    rw [hLen]
    omega
  case swap n =>
    have hPos : 1 ≤ n := hSwapPos n rfl
    have hLen := run_swap_stack_length_of_pos hPos hRun
    simp [inputArity, outputArity] at hStack hBound
    rw [hLen]
    omega
  case invalid =>
    simp [PrimStep.run] at hRun
  all_goals
    have hLen := run_stack_length_safe (by simp [SuffixSafe]) hRun
    rw [hLen]
    exact hBound

theorem run_suffix_sound_safe
    {step : Assembly.PrimStep}
    {shared : EvmYul.SharedState .EVM}
    {stack base : EvmYul.Stack Word}
    {iso' evm evm' : EvmYul.EVM.State}
    (hSafe : SuffixSafe step)
    (hIso : step.run (isoState shared stack) = .ok iso')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = stack ++ base)
    (hRun : step.run evm = .ok evm') :
    evm'.toSharedState = iso'.toSharedState ∧
      evm'.stack = iso'.stack ++ base := by
  cases step
  case bin f => exact run_suffix_sound_bin f hIso hShared hStack hRun
  case un f => exact run_suffix_sound_un f hIso hShared hStack hRun
  case tri f => exact run_suffix_sound_tri f hIso hShared hStack hRun
  case executionEnv f =>
    simp [PrimStep.run, EvmYul.EVM.executionEnvOp, hShared, hStack,
      EvmYul.Stack.push] at hIso hRun ⊢
    cases hIso
    cases hRun
    simp [isoState, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      hShared]
  case machineState f =>
    simp [PrimStep.run, EvmYul.EVM.machineStateOp, hShared, hStack,
      EvmYul.Stack.push] at hIso hRun ⊢
    cases hIso
    cases hRun
    simp [isoState, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      hShared]
  case state f =>
    simp [PrimStep.run, EvmYul.EVM.stateOp, hShared, hStack,
      EvmYul.Stack.push] at hIso hRun ⊢
    cases hIso
    cases hRun
    simp [isoState, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
      hShared]
  case dup n => contradiction
  case swap n => contradiction
  case invalid => simp [PrimStep.run] at hIso
  all_goals
    simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.ternaryCopyOp,
      EvmYul.EVM.quaternaryCopyOp,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hIso hRun ⊢
  case unaryExecutionEnv f =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a⟩
        have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp [isoState, EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hShared]
  case unaryState f =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a⟩
        have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp [isoState, EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hShared]
  case pop =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a⟩
        have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case mload =>
    cases hPop : stack.pop with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a⟩
        have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp [isoState, EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hShared]
  case binaryMachineState =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case binaryMachineStateWithResult =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp [isoState, EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hShared]
  case binaryState =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case log0 =>
    cases hPop : stack.pop2 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b⟩
        have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case ternaryMachineState =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case ternaryCopy =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case returndatacopy =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        split at hIso
        · simp at hIso
        · simp [*] at hRun
          cases hIso
          cases hRun
          simp
  case log1 =>
    cases hPop : stack.pop3 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c⟩
        have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case quaternaryCopy =>
    cases hPop : stack.pop4 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d⟩
        have hPopTarget := Stack.pop4_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case log2 =>
    cases hPop : stack.pop4 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d⟩
        have hPopTarget := Stack.pop4_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case log3 =>
    cases hPop : stack.pop5 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d, e⟩
        have hPopTarget := Stack.pop5_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp
  case log4 =>
    cases hPop : stack.pop6 with
    | none => simp [hPop] at hIso
    | some tup =>
        rcases tup with ⟨rest, a, b, c, d, e, f⟩
        have hPopTarget := Stack.pop6_append_of_some (tail := base) hPop
        rw [hStack, hPopTarget] at hRun
        simp [hPop, hShared] at hIso hRun
        cases hIso
        cases hRun
        simp

theorem run_suffix_exists_safe
    {step : Assembly.PrimStep}
    {shared : EvmYul.SharedState .EVM}
    {stack base : EvmYul.Stack Word}
    {iso' evm : EvmYul.EVM.State}
    (hSafe : SuffixSafe step)
    (hIso : step.run (isoState shared stack) = .ok iso')
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = stack ++ base) :
    ∃ evm',
      step.run evm = .ok evm' ∧
        evm'.toSharedState = iso'.toSharedState ∧
          evm'.stack = iso'.stack ++ base := by
  cases hRun : step.run evm with
  | ok evm' =>
      exact ⟨evm', rfl,
        run_suffix_sound_safe hSafe hIso hShared hStack hRun⟩
  | error err =>
      exfalso
      cases step
      case dup n => contradiction
      case swap n => contradiction
      case invalid => simp [PrimStep.run] at hIso
      case bin f =>
        simp [PrimStep.run, EvmYul.EVM.execBinOp] at hIso hRun
        cases hPop : stack.pop2 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b⟩
            have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case un f =>
        simp [PrimStep.run, EvmYul.EVM.execUnOp] at hIso hRun
        cases hPop : stack.pop with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a⟩
            have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case tri f =>
        simp [PrimStep.run, EvmYul.EVM.execTriOp] at hIso hRun
        cases hPop : stack.pop3 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c⟩
            have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case executionEnv f =>
        simp [PrimStep.run, EvmYul.EVM.executionEnvOp, hShared, hStack,
          EvmYul.Stack.push] at hIso hRun
        cases hRun
      case machineState f =>
        simp [PrimStep.run, EvmYul.EVM.machineStateOp, hShared, hStack,
          EvmYul.Stack.push] at hIso hRun
        cases hRun
      case state f =>
        simp [PrimStep.run, EvmYul.EVM.stateOp, hShared, hStack,
          EvmYul.Stack.push] at hIso hRun
        cases hRun
      all_goals
        simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp,
          EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
          EvmYul.EVM.binaryMachineStateOp,
          EvmYul.EVM.binaryMachineStateOp',
          EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.ternaryCopyOp,
          EvmYul.EVM.quaternaryCopyOp,
          EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] at hIso hRun
      case unaryExecutionEnv f =>
        cases hPop : stack.pop with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a⟩
            have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case unaryState f =>
        cases hPop : stack.pop with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a⟩
            have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case pop =>
        cases hPop : stack.pop with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a⟩
            have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
      case mload =>
        cases hPop : stack.pop with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a⟩
            have hPopTarget := Stack.pop_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
      case binaryMachineState =>
        cases hPop : stack.pop2 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b⟩
            have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case binaryMachineStateWithResult =>
        cases hPop : stack.pop2 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b⟩
            have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case binaryState =>
        cases hPop : stack.pop2 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b⟩
            have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case log0 =>
        cases hPop : stack.pop2 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b⟩
            have hPopTarget := Stack.pop2_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
      case ternaryMachineState =>
        cases hPop : stack.pop3 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c⟩
            have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case ternaryCopy =>
        cases hPop : stack.pop3 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c⟩
            have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case returndatacopy =>
        cases hPop : stack.pop3 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c⟩
            have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            split at hIso
            · simp at hIso
            · simp [*] at hRun
      case log1 =>
        cases hPop : stack.pop3 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c⟩
            have hPopTarget := Stack.pop3_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
      case quaternaryCopy =>
        cases hPop : stack.pop4 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c, d⟩
            have hPopTarget := Stack.pop4_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
            cases hRun
      case log2 =>
        cases hPop : stack.pop4 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c, d⟩
            have hPopTarget := Stack.pop4_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
      case log3 =>
        cases hPop : stack.pop5 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c, d, e⟩
            have hPopTarget := Stack.pop5_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun
      case log4 =>
        cases hPop : stack.pop6 with
        | none => simp [hPop] at hIso
        | some tup =>
            rcases tup with ⟨rest, a, b, c, d, e, f⟩
            have hPopTarget := Stack.pop6_append_of_some (tail := base) hPop
            rw [hStack, hPopTarget] at hRun
            simp [hPop, hShared] at hIso hRun

attribute [local simp] idRun_eq

/--
Continuing primitive semantics are congruent modulo compiler-owned control
counters. This lower-layer theorem is shared by Structured and observer-aware
TypedCfg semantics.
-/
theorem run_map_eraseRuntimeControl
    {step : PrimStep} {target source : EvmYul.EVM.State}
    (hRel : SameRuntimeData target source) :
    (step.run target).map eraseRuntimeControl =
      (step.run source).map eraseRuntimeControl := by
  cases target with
  | mk targetShared targetPc targetStack targetExec =>
      cases source with
      | mk sourceShared sourcePc sourceStack sourceExec =>
          simp [SameRuntimeData, eraseRuntimeControl] at hRel
          rcases hRel with ⟨rfl, rfl⟩
          cases step with
          | bin f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.execBinOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | un f =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.execUnOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | tri f =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.execTriOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | executionEnv f =>
              simp [Except.map, PrimStep.run,
                EvmYul.EVM.executionEnvOp,
                eraseRuntimeControl,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          | unaryExecutionEnv f =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.unaryExecutionEnvOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | machineState f =>
              simp [Except.map, PrimStep.run,
                EvmYul.EVM.machineStateOp,
                eraseRuntimeControl,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          | binaryMachineState f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.binaryMachineStateOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | binaryMachineStateWithResult f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.binaryMachineStateOp', hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | ternaryMachineState f =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.ternaryMachineStateOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | state f =>
              simp [Except.map, PrimStep.run, EvmYul.EVM.stateOp,
                eraseRuntimeControl,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          | unaryState f =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.unaryStateOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | binaryState f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.binaryStateOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | ternaryCopy f =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.ternaryCopyOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | quaternaryCopy f =>
              cases hPop : targetStack.pop4 <;>
                simp [Except.map, PrimStep.run,
                  EvmYul.EVM.quaternaryCopyOp, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | pop =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | mload =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | returndatacopy =>
              cases hPop : targetStack.pop3 with
              | none =>
                  simp [Except.map, PrimStep.run, hPop,
                    eraseRuntimeControl]
              | some values =>
                  by_cases hBounds :
                      targetShared.returnData.size <
                        values.2.2.1.toNat + values.2.2.2.toNat <;>
                    simp [Except.map, PrimStep.run, hPop,
                      hBounds, eraseRuntimeControl,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
          | dup n =>
              by_cases hLength : n ≤ targetStack.length <;>
                simp [Except.map, PrimStep.run, EvmYul.dup,
                  hLength, eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | swap n =>
              by_cases hLength : n + 1 ≤ targetStack.length <;>
                simp [Except.map, PrimStep.run, EvmYul.swap,
                  hLength, eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log0 =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log1 =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log2 =>
              cases hPop : targetStack.pop4 <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log3 =>
              cases hPop : targetStack.pop5 <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log4 =>
              cases hPop : targetStack.pop6 <;>
                simp [Except.map, PrimStep.run, hPop,
                  eraseRuntimeControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | invalid =>
              rfl

/--
Successful primitive execution preserves a hidden stack suffix modulo the
compiler-owned PC and execution-length counters, provided every operand lies
in the visible source prefix.
-/
theorem run_append_stack_rel_of_inputArity_le
    {step : PrimStep} {state final framedFinal : EvmYul.EVM.State}
    {hidden : EvmYul.Stack Word}
    (hBound : inputArity step ≤ state.stack.length)
    (hRun : step.run state = .ok final)
    (hFramed :
      step.run { state with stack := state.stack ++ hidden } =
        .ok framedFinal) :
    SameRuntimeData
      framedFinal
      { final with stack := final.stack ++ hidden } := by
  by_cases hSafe : SuffixSafe step
  · let isolated := isoState state.toSharedState state.stack
    have hInitialRel : SameRuntimeData isolated state := by
      cases state
      rfl
    have hCongruence :=
      run_map_eraseRuntimeControl
        (step := step) hInitialRel
    rw [hRun] at hCongruence
    cases hIsolated : step.run isolated with
    | error err =>
        simp [hIsolated, Except.map] at hCongruence
    | ok isolatedFinal =>
        simp [hIsolated, Except.map] at hCongruence
        have hSuffix :=
          run_suffix_sound_safe
            (step := step) (stack := state.stack)
            (base := hidden)
            (evm :=
              { state with stack := state.stack ++ hidden })
            hSafe hIsolated rfl rfl hFramed
        have hFramedRel :
            SameRuntimeData
              framedFinal
              { isolatedFinal with
                stack := isolatedFinal.stack ++ hidden } := by
          rcases hSuffix with ⟨hShared, hStack⟩
          cases framedFinal
          cases isolatedFinal
          simpa [SameRuntimeData, eraseRuntimeControl] using
            And.intro hShared hStack
        have hFinalStack :
            isolatedFinal.stack = final.stack :=
          SameRuntimeData.stack_eq hCongruence
        have hFinalRel :
            SameRuntimeData
              { isolatedFinal with
                stack := isolatedFinal.stack ++ hidden }
              { final with stack := final.stack ++ hidden } :=
          SameRuntimeData.replaceStack hCongruence
            (congrArg (· ++ hidden) hFinalStack)
        exact SameRuntimeData.trans hFramedRel hFinalRel
  · cases step <;> simp [SuffixSafe] at hSafe
    case neg.dup n =>
      simp only [inputArity] at hBound
      have hFramedBound :
          n ≤ (state.stack ++ hidden).length := by
        simp
        omega
      simp [PrimStep.run, EvmYul.dup,
        List.length_take, Nat.min_eq_left hBound,
        Nat.min_eq_left hFramedBound,
        List.take_append_of_le_length hBound] at hRun hFramed
      subst final
      subst framedFinal
      simp [SameRuntimeData, eraseRuntimeControl,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC,
        List.take_append_of_le_length hBound]
    case neg.swap n =>
      simp only [inputArity] at hBound
      have hFramedBound :
          n + 1 ≤ (state.stack ++ hidden).length := by
        simp
        omega
      simp [PrimStep.run, EvmYul.swap,
        List.length_take, Nat.min_eq_left hBound,
        Nat.min_eq_left hFramedBound,
        List.take_append_of_le_length hBound,
        List.drop_append_of_le_length hBound] at hRun hFramed
      subst final
      subst framedFinal
      simp [SameRuntimeData, eraseRuntimeControl,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC,
        List.take_append_of_le_length hBound,
        List.drop_append_of_le_length hBound,
        List.append_assoc]

end PrimStep

namespace PrimOp

/--
The stack transition of any nonterminal primitive.

This is deliberately broader than `continuingStep?`: the latter is the
historical closed-world proof whitelist and excludes resource observers,
PC-dependent instructions, and call/create operations. Typed CFG validation
only needs the EVM stack contract, so those effects remain admissible while
terminal instructions must be represented by CFG terminators.
-/
def stackArity? (op : PrimOp) : Option (Nat × Nat) :=
  match op with
  | .stop | .return | .revert | .selfdestruct | .invalid => none
  | _ =>
      some
        ((EvmYul.EVM.δ op.toEVM).getD 0,
          (EvmYul.EVM.α op.toEVM).getD 0)

/--
Continuing primitives admitted by structured control as ordinary statements.

Excluded here: `STOP`, `RETURN`, `REVERT`, `SELFDESTRUCT`, the call/create
family, `PC`, and `GAS`. Those are control-boundary, PC-dependent, or
gas-accounting opcodes and are not ordinary source/compiler-tower statements.
-/
def continuingStep? : PrimOp → Option PrimStep
  | .add => some (.bin EvmYul.UInt256.add)
  | .mul => some (.bin EvmYul.UInt256.mul)
  | .sub => some (.bin EvmYul.UInt256.sub)
  | .div => some (.bin EvmYul.UInt256.div)
  | .sdiv => some (.bin EvmYul.UInt256.sdiv)
  | .mod => some (.bin EvmYul.UInt256.mod)
  | .smod => some (.bin EvmYul.UInt256.smod)
  | .addmod => some (.tri EvmYul.UInt256.addMod)
  | .mulmod => some (.tri EvmYul.UInt256.mulMod)
  | .exp => some (.bin EvmYul.UInt256.exp)
  | .signextend => some (.bin EvmYul.UInt256.signextend)
  | .lt => some (.bin EvmYul.UInt256.lt)
  | .gt => some (.bin EvmYul.UInt256.gt)
  | .slt => some (.bin EvmYul.UInt256.slt)
  | .sgt => some (.bin EvmYul.UInt256.sgt)
  | .eq => some (.bin EvmYul.UInt256.eq)
  | .iszero => some (.un EvmYul.UInt256.isZero)
  | .and => some (.bin EvmYul.UInt256.land)
  | .or => some (.bin EvmYul.UInt256.lor)
  | .xor => some (.bin EvmYul.UInt256.xor)
  | .not => some (.un EvmYul.UInt256.lnot)
  | .byte => some (.bin EvmYul.UInt256.byteAt)
  | .shl => some (.bin (flip EvmYul.UInt256.shiftLeft))
  | .shr => some (.bin (flip EvmYul.UInt256.shiftRight))
  | .sar => some (.bin EvmYul.UInt256.sar)
  | .address =>
      some (.executionEnv
        (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner))
  | .balance => some (.unaryState EvmYul.State.balance)
  | .origin =>
      some (.executionEnv
        (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender))
  | .caller =>
      some (.executionEnv
        (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source))
  | .callvalue => some (.executionEnv EvmYul.ExecutionEnv.weiValue)
  | .calldataload =>
      some (.unaryState (fun s v => (s, EvmYul.State.calldataload s v)))
  | .calldatasize =>
      some (.executionEnv
        (.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.calldata))
  | .calldatacopy =>
      some (.ternaryCopy EvmYul.SharedState.calldatacopy)
  | .codesize =>
      some (.executionEnv
        (.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.code))
  | .codecopy => some (.ternaryCopy EvmYul.SharedState.codeCopy)
  | .gasprice =>
      some (.executionEnv (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice))
  | .extcodesize => some (.unaryState EvmYul.State.extCodeSize)
  | .extcodecopy =>
      some (.quaternaryCopy EvmYul.SharedState.extCodeCopy')
  | .returndatasize =>
      some (.machineState EvmYul.MachineState.returndatasize)
  | .returndatacopy => some .returndatacopy
  | .extcodehash => some (.unaryState EvmYul.State.extCodeHash)
  | .blockhash =>
      some (.unaryState (fun s v => (s, EvmYul.State.blockHash s v)))
  | .coinbase =>
      some (.state (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase))
  | .timestamp => some (.state EvmYul.State.timeStamp)
  | .number => some (.state EvmYul.State.number)
  | .prevrandao => some (.executionEnv EvmYul.prevRandao)
  | .gaslimit => some (.state EvmYul.State.gasLimit)
  | .chainid => some (.state EvmYul.State.chainId)
  | .selfbalance => some (.state EvmYul.State.selfbalance)
  | .basefee => some (.executionEnv EvmYul.basefee)
  | .blobhash => some (.unaryExecutionEnv EvmYul.blobhash)
  | .blobbasefee =>
      some (.executionEnv EvmYul.ExecutionEnv.getBlobGasprice)
  | .pop => some .pop
  | .mload => some .mload
  | .mstore => some (.binaryMachineState EvmYul.MachineState.mstore)
  | .sload => some (.unaryState EvmYul.State.sload)
  | .sstore => some (.binaryState EvmYul.State.sstore)
  | .mstore8 => some (.binaryMachineState EvmYul.MachineState.mstore8)
  | .msize => some (.machineState EvmYul.MachineState.msize)
  | .tload => some (.unaryState EvmYul.State.tload)
  | .tstore => some (.binaryState EvmYul.State.tstore)
  | .mcopy => some (.ternaryMachineState EvmYul.MachineState.mcopy)
  | .keccak256 =>
      some (.binaryMachineStateWithResult EvmYul.MachineState.keccak256)
  | .dup1 => some (.dup 1)
  | .dup2 => some (.dup 2)
  | .dup3 => some (.dup 3)
  | .dup4 => some (.dup 4)
  | .dup5 => some (.dup 5)
  | .dup6 => some (.dup 6)
  | .dup7 => some (.dup 7)
  | .dup8 => some (.dup 8)
  | .dup9 => some (.dup 9)
  | .dup10 => some (.dup 10)
  | .dup11 => some (.dup 11)
  | .dup12 => some (.dup 12)
  | .dup13 => some (.dup 13)
  | .dup14 => some (.dup 14)
  | .dup15 => some (.dup 15)
  | .dup16 => some (.dup 16)
  | .swap1 => some (.swap 1)
  | .swap2 => some (.swap 2)
  | .swap3 => some (.swap 3)
  | .swap4 => some (.swap 4)
  | .swap5 => some (.swap 5)
  | .swap6 => some (.swap 6)
  | .swap7 => some (.swap 7)
  | .swap8 => some (.swap 8)
  | .swap9 => some (.swap 9)
  | .swap10 => some (.swap 10)
  | .swap11 => some (.swap 11)
  | .swap12 => some (.swap 12)
  | .swap13 => some (.swap 13)
  | .swap14 => some (.swap 14)
  | .swap15 => some (.swap 15)
  | .swap16 => some (.swap 16)
  | .log0 => some .log0
  | .log1 => some .log1
  | .log2 => some .log2
  | .log3 => some .log3
  | .log4 => some .log4
  | .invalid => some .invalid
  | .stop | .pc | .gas | .create | .call | .callcode | .return | .delegatecall
  | .create2 | .staticcall | .revert | .selfdestruct =>
      none

theorem continuingStep?_delta_alpha
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    (EvmYul.EVM.δ (PrimOp.toEVM op)).getD 0 =
        PrimStep.inputArity step ∧
      (EvmYul.EVM.α (PrimOp.toEVM op)).getD 0 =
        PrimStep.outputArity step := by
  cases op <;>
    simp [continuingStep?, PrimOp.toEVM, PrimStep.inputArity,
      PrimStep.outputArity, EvmYul.EVM.δ, EvmYul.EVM.α] at hStep ⊢
  all_goals
    cases hStep
    simp [PrimStep.inputArity, PrimStep.outputArity]

theorem continuingStep?_swap_pos
    {op : PrimOp} {n : Nat}
    (hStep : op.continuingStep? = some (.swap n)) :
    1 ≤ n := by
  cases op <;> simp [continuingStep?] at hStep
  all_goals omega

def step (op : PrimOp) (state : EvmYul.EVM.State) :
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State :=
  match op.continuingStep? with
  | some step => step.run state
  | none =>
      match op with
      | .create | .call | .callcode | .delegatecall | .create2
      | .staticcall =>
          .error .InvalidInstruction
      | _ =>
          EvmYul.step op.toEVM none state

theorem step_eq_continuingStep_run {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) (state : EvmYul.EVM.State) :
    op.step state = step.run state := by
  unfold PrimOp.step
  simp [hStep]

theorem step_eq_evm_step_of_not_continuing {op : PrimOp}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    (state : EvmYul.EVM.State) :
    op.step state = EvmYul.step op.toEVM none state := by
  cases op <;>
    simp [PrimOp.step, PrimOp.continuingStep?,
      PrimOp.isCallCreate] at hStep hNoCallCreate ⊢

/--
Every nonterminal primitive admitted by the checked no-external-effects
boundary is congruent modulo compiler-owned control counters. This includes
`gas`, whose value is runtime data retained by `SameRuntimeData`.
-/
theorem step_map_eraseRuntimeControl
    {op : PrimOp} {target source : EVMState}
    (hArity : ∃ arity, op.stackArity? = some arity)
    (hNoPc : op ≠ .pc)
    (hNoCall : op.isExternalCallCreate = false)
    (hRel : SameRuntimeData target source) :
    (op.step target).map eraseRuntimeControl =
      (op.step source).map eraseRuntimeControl := by
  cases hStep : op.continuingStep? with
  | some step =>
      rw [step_eq_continuingStep_run hStep target,
        step_eq_continuingStep_run hStep source]
      exact PrimStep.run_map_eraseRuntimeControl hRel
  | none =>
      rcases hArity with ⟨arity, hArity⟩
      have hGas : op = .gas := by
        cases op <;>
          simp [PrimOp.stackArity?, PrimOp.continuingStep?,
            PrimOp.isExternalCallCreate] at hArity hNoPc hNoCall hStep ⊢
      subst op
      change
        (EvmYul.EVM.machineStateOp EvmYul.MachineState.gas target).map
            eraseRuntimeControl =
          (EvmYul.EVM.machineStateOp EvmYul.MachineState.gas source).map
            eraseRuntimeControl
      exact
        PrimStep.run_map_eraseRuntimeControl
          (step := .machineState EvmYul.MachineState.gas) hRel

theorem step_pc_of_stackArity
    {op : PrimOp} {input output : Nat}
    {state final : EvmYul.EVM.State}
    (hArity : op.stackArity? = some (input, output))
    (hRun : op.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases hCont : op.continuingStep? with
  | some step =>
      rw [step_eq_continuingStep_run hCont] at hRun
      exact PrimStep.run_pc hRun
  | none =>
      cases op <;>
        simp [PrimOp.continuingStep?] at hCont
      case stop | «return» | revert | selfdestruct =>
        simp [PrimOp.stackArity?] at hArity
      case pc =>
        change
          Except.ok
              (state.replaceStackAndIncrPC
                (state.stack.push state.pc)) =
            Except.ok final at hRun
        cases hRun
        rfl
      case gas =>
        change
          Except.ok
              (state.replaceStackAndIncrPC
                (state.stack.push state.gasAvailable)) =
            Except.ok final at hRun
        cases hRun
        rfl
      case create | call | callcode | delegatecall | create2 | staticcall =>
        change
          (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
            Except EvmYul.EVM.ExecutionException EvmYul.EVM.State) =
            Except.ok final at hRun
        cases hRun

/--
Successful `stackArity?` lookup exposes the EVM delta/alpha pair used to define
the declaration.
-/
theorem stackArity_values
    {op : PrimOp} {input output : Nat}
    (hArity : op.stackArity? = some (input, output)) :
    input = (EvmYul.EVM.δ op.toEVM).getD 0 ∧
      output = (EvmYul.EVM.α op.toEVM).getD 0 := by
  cases op <;>
    simp [PrimOp.stackArity?, PrimOp.toEVM,
      EvmYul.EVM.δ, EvmYul.EVM.α] at hArity ⊢ <;>
    omega

/--
A primitive whose declared operands fit in the visible prefix cannot succeed
only because compiler-owned stack data was appended.
-/
theorem exists_step_of_stackArity_le_of_append_step
    {op : PrimOp} {input output : Nat}
    {state framedFinal : EvmYul.EVM.State}
    {hidden : EvmYul.Stack Word}
    (hArity : op.stackArity? = some (input, output))
    (hBound : input ≤ state.stack.length)
    (hFramed :
      op.step { state with stack := state.stack ++ hidden } =
        .ok framedFinal) :
    ∃ final, op.step state = .ok final := by
  cases hCont : op.continuingStep? with
  | some step =>
      have hInput :
          input = PrimStep.inputArity step := by
        rcases stackArity_values hArity with ⟨hDeclared, _⟩
        rcases continuingStep?_delta_alpha hCont with
          ⟨hStep, _⟩
        exact hDeclared.trans hStep
      rw [step_eq_continuingStep_run hCont] at hFramed ⊢
      exact
        PrimStep.exists_run_of_inputArity_le_of_append_run
          (step := step) (hidden := hidden)
          (by simpa [← hInput] using hBound) hFramed
  | none =>
      cases op <;>
        simp [PrimOp.step, continuingStep?, PrimOp.stackArity?,
          PrimOp.toEVM, EvmYul.EVM.δ, EvmYul.EVM.α]
          at hCont hArity hFramed ⊢
      case none.pc =>
        exact ⟨_, rfl⟩
      case none.gas =>
        exact ⟨_, rfl⟩

/--
Successful primitive execution preserves an appended compiler-owned suffix
modulo control counters whenever the declared operands fit in the visible
prefix.
-/
theorem step_append_stack_rel_of_stackArity_le
    {op : PrimOp} {input output : Nat}
    {state final framedFinal : EvmYul.EVM.State}
    {hidden : EvmYul.Stack Word}
    (hArity : op.stackArity? = some (input, output))
    (hBound : input ≤ state.stack.length)
    (hRun : op.step state = .ok final)
    (hFramed :
      op.step { state with stack := state.stack ++ hidden } =
        .ok framedFinal) :
    SameRuntimeData
      framedFinal
      { final with stack := final.stack ++ hidden } := by
  cases hCont : op.continuingStep? with
  | some step =>
      have hInput :
          input = PrimStep.inputArity step := by
        rcases stackArity_values hArity with ⟨hDeclared, _⟩
        rcases continuingStep?_delta_alpha hCont with
          ⟨hStep, _⟩
        exact hDeclared.trans hStep
      apply
        PrimStep.run_append_stack_rel_of_inputArity_le
          (step := step)
      · simpa [← hInput] using hBound
      · simpa [step_eq_continuingStep_run hCont] using hRun
      · simpa [step_eq_continuingStep_run hCont] using hFramed
  | none =>
      cases op <;>
        simp [PrimOp.step, continuingStep?, PrimOp.stackArity?,
          PrimOp.toEVM, EvmYul.EVM.δ, EvmYul.EVM.α,
          SameRuntimeData, eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
          at hCont hArity hRun hFramed ⊢
      case none.pc =>
        cases hRun
        cases hFramed
        simp [SameRuntimeData, eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      case none.gas =>
        cases hRun
        cases hFramed
        simp [SameRuntimeData, eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]

/--
Every successful nonterminal primitive realizes its declared symbolic stack
transition on the concrete EVM stack.
-/
theorem step_stack_length_of_stackArity
    {op : PrimOp} {input output : Nat}
    {state final : EvmYul.EVM.State}
    (hArity : op.stackArity? = some (input, output))
    (hRun : op.step state = .ok final) :
    final.stack.length =
      state.stack.length - input + output := by
  cases hCont : op.continuingStep? with
  | some step =>
      rcases stackArity_values hArity with
        ⟨hInput, hOutput⟩
      rcases continuingStep?_delta_alpha hCont with
        ⟨hStepInput, hStepOutput⟩
      rw [hInput, hOutput, hStepInput, hStepOutput]
      rw [step_eq_continuingStep_run hCont] at hRun
      cases step with
      | dup depth =>
          have hLength := PrimStep.run_dup_stack_length hRun
          have hBound := PrimStep.run_inputArity_le hRun
          simp [PrimStep.inputArity, PrimStep.outputArity] at hLength ⊢
          simp [PrimStep.inputArity] at hBound
          omega
      | swap depth =>
          have hPos : 1 ≤ depth :=
            continuingStep?_swap_pos hCont
          have hLength :=
            PrimStep.run_swap_stack_length_of_pos hPos hRun
          have hBound := PrimStep.run_inputArity_le hRun
          simp [PrimStep.inputArity, PrimStep.outputArity] at hLength ⊢
          simp [PrimStep.inputArity] at hBound
          omega
      | invalid =>
          simp [PrimStep.run] at hRun
      | bin f | un f | tri f | executionEnv f | machineState f
      | state f | unaryExecutionEnv f | unaryState f
      | binaryMachineState f | binaryMachineStateWithResult f
      | ternaryMachineState f | binaryState f | ternaryCopy f
      | quaternaryCopy f | pop | mload | returndatacopy
      | log0 | log1 | log2 | log3 | log4 =>
          exact
            PrimStep.run_stack_length_safe
              (by simp [PrimStep.SuffixSafe]) hRun
  | none =>
      cases op <;>
        simp [PrimOp.continuingStep?] at hCont
      case stop | «return» | revert | selfdestruct =>
        simp [PrimOp.stackArity?] at hArity
      case pc =>
        change
          Except.ok
              (state.replaceStackAndIncrPC
                (state.stack.push state.pc)) =
            Except.ok final at hRun
        cases hRun
        have hValues := stackArity_values hArity
        have hInput : input = 0 := by simpa using hValues.1
        have hOutput : output = 1 := by simpa using hValues.2
        subst input
        subst output
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      case gas =>
        change
          Except.ok
              (state.replaceStackAndIncrPC
                (state.stack.push state.gasAvailable)) =
            Except.ok final at hRun
        cases hRun
        have hValues := stackArity_values hArity
        have hInput : input = 0 := by simpa using hValues.1
        have hOutput : output = 1 := by simpa using hValues.2
        subst input
        subst output
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      case create | call | callcode | delegatecall | create2 | staticcall =>
        change
          (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
            Except EvmYul.EVM.ExecutionException EvmYul.EVM.State) =
            Except.ok final at hRun
        cases hRun

end PrimOp

end Assembly
end EvmCompiler
