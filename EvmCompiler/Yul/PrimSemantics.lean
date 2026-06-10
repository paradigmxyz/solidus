import EvmCompiler.Yul.Syntax
import EvmCompiler.Structured.Semantics
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul

namespace PrimSemantics

theorem ok_store_eq_of_state_eq
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    (h :
      (.Ok sharedAfter storeAfter : EvmYul.Yul.State) =
        .Ok shared store) :
    storeAfter = store := by
  cases h
  rfl

theorem setSharedState_eq_self_of_nonOk
    {state : EvmYul.Yul.State} {shared : EvmYul.SharedState .Yul}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State)) :
    EvmYul.Yul.State.setSharedState shared state = state := by
  cases state with
  | Ok oldShared store =>
      exact False.elim (hNonOk oldShared store rfl)
  | OutOfFuel =>
      rfl
  | Checkpoint jump =>
      rfl

theorem setMachineState_eq_self_of_nonOk
    {state : EvmYul.Yul.State} {machineState : EvmYul.MachineState}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State)) :
    EvmYul.Yul.State.setMachineState machineState state = state := by
  cases state with
  | Ok shared store =>
      exact False.elim (hNonOk shared store rfl)
  | OutOfFuel =>
      rfl
  | Checkpoint jump =>
      rfl

theorem setState_eq_self_of_nonOk
    {state : EvmYul.Yul.State} {evmState : EvmYul.State .Yul}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State)) :
    EvmYul.Yul.State.setState evmState state = state := by
  cases state with
  | Ok shared store =>
      exact False.elim (hNonOk shared store rfl)
  | OutOfFuel =>
      rfl
  | Checkpoint jump =>
      rfl

theorem wrapped_execUnOp_state_eq_of_ok
    {f : EvmYul.Primop.Unary}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.execUnOp f state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.execUnOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.execUnOp] at h
          exact h.1.symm
      | cons b restTail =>
          simp [EvmYul.Yul.execUnOp] at h

theorem wrapped_execBinOp_state_eq_of_ok
    {f : EvmYul.Primop.Binary}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.execBinOp f state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.execBinOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.execBinOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.execBinOp] at h
              exact h.1.symm
          | cons c restRest =>
              simp [EvmYul.Yul.execBinOp] at h

theorem wrapped_execTriOp_state_eq_of_ok
    {f : EvmYul.Primop.Ternary}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.execTriOp f state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.execTriOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.execTriOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.execTriOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.execTriOp] at h
                  exact h.1.symm
              | cons d restFinal =>
                  simp [EvmYul.Yul.execTriOp] at h

theorem wrapped_execQuadOp_state_eq_of_ok
    {f : EvmYul.Primop.Quaternary}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.execQuadOp f state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.execQuadOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.execQuadOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.execQuadOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.execQuadOp] at h
              | cons d restFinal =>
                  cases restFinal with
                  | nil =>
                      simp [EvmYul.Yul.execQuadOp] at h
                      exact h.1.symm
                  | cons e restExtra =>
                      simp [EvmYul.Yul.execQuadOp] at h

theorem wrapped_executionEnvOp_state_eq_of_ok
    {op : EvmYul.ExecutionEnv .Yul → Word}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.executionEnvOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  simp [EvmYul.Yul.executionEnvOp] at h
  exact h.1.symm

theorem wrapped_unaryExecutionEnvOp_state_eq_of_ok
    {op : EvmYul.ExecutionEnv .Yul → Word → Word}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.unaryExecutionEnvOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.unaryExecutionEnvOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.unaryExecutionEnvOp] at h
          exact h.1.symm
      | cons b restTail =>
          simp [EvmYul.Yul.unaryExecutionEnvOp] at h

theorem wrapped_machineStateOp_state_eq_of_ok
    {op : EvmYul.MachineState → Word}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.machineStateOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  simp [EvmYul.Yul.machineStateOp] at h
  exact h.1.symm

theorem wrapped_stateOp_state_eq_of_ok
    {op : EvmYul.State .Yul → Word}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      (match EvmYul.Yul.stateOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  simp [EvmYul.Yul.stateOp] at h
  exact h.1.symm

theorem wrapped_binaryMachineStateOp_state_eq_of_ok_of_nonOk
    {op : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.binaryMachineStateOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp,
                setMachineState_eq_self_of_nonOk hNonOk] at h
              exact h.1.symm
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp] at h

theorem wrapped_binaryMachineStateOp'_state_eq_of_ok_of_nonOk
    {op : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.binaryMachineStateOp' op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp'] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp'] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp',
                setMachineState_eq_self_of_nonOk hNonOk] at h
              exact h.1.symm
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at h

theorem wrapped_ternaryMachineStateOp_state_eq_of_ok_of_nonOk
    {op : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.ternaryMachineStateOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryMachineStateOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp,
                    setMachineState_eq_self_of_nonOk hNonOk] at h
                  exact h.1.symm
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at h

theorem wrapped_unaryStateOp_state_eq_of_ok_of_nonOk
    {op : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.unaryStateOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.unaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp,
            setSharedState_eq_self_of_nonOk hNonOk] at h
          exact h.1.symm
      | cons b restTail =>
          simp [EvmYul.Yul.unaryStateOp] at h

theorem wrapped_binaryStateOp_state_eq_of_ok_of_nonOk
    {op : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.binaryStateOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryStateOp,
                setState_eq_self_of_nonOk hNonOk] at h
              exact h.1.symm
          | cons c restRest =>
              simp [EvmYul.Yul.binaryStateOp] at h

theorem wrapped_binaryStateOp_store_eq_of_ok
    {op : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryStateOp,
                EvmYul.Yul.State.setState] at h
              exact h.1.2.symm
          | cons c restRest =>
              simp [EvmYul.Yul.binaryStateOp] at h

theorem wrapped_executionEnvOp_store_eq_of_ok
    {op : EvmYul.ExecutionEnv .Yul → Word}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.executionEnvOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store :=
  ok_store_eq_of_state_eq
    (wrapped_executionEnvOp_state_eq_of_ok (args := args) h)

theorem wrapped_unaryExecutionEnvOp_store_eq_of_ok
    {op : EvmYul.ExecutionEnv .Yul → Word → Word}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.unaryExecutionEnvOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store :=
  ok_store_eq_of_state_eq
    (wrapped_unaryExecutionEnvOp_state_eq_of_ok (args := args) h)

theorem wrapped_unaryStateOp_store_eq_of_ok
    {op : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.unaryStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.unaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp,
            EvmYul.Yul.State.setSharedState] at h
          exact h.1.2.symm
      | cons b restTail =>
          simp [EvmYul.Yul.unaryStateOp] at h

theorem wrapped_stateOp_store_eq_of_ok
    {op : EvmYul.State .Yul → Word}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.stateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store :=
  ok_store_eq_of_state_eq
    (wrapped_stateOp_state_eq_of_ok (args := args) h)

theorem wrapped_machineStateOp_store_eq_of_ok
    {op : EvmYul.MachineState → Word}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.machineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  simp [EvmYul.Yul.machineStateOp] at h
  exact h.1.2.symm

theorem wrapped_binaryMachineStateOp_store_eq_of_ok
    {op : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryMachineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp,
                EvmYul.Yul.State.setMachineState] at h
              exact h.1.2.symm
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp] at h

theorem wrapped_ternaryMachineStateOp_store_eq_of_ok
    {op : EvmYul.MachineState → Word → Word → Word →
      EvmYul.MachineState}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.ternaryMachineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryMachineStateOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp,
                    EvmYul.Yul.State.setMachineState] at h
                  exact h.1.2.symm
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at h

theorem wrapped_binaryMachineStateOp'_store_eq_of_ok
    {op : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryMachineStateOp' op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp'] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp'] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp',
                EvmYul.Yul.State.setMachineState] at h
              exact h.1.2.symm
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at h

theorem wrapped_ternaryCopyOp_store_eq_of_ok
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.ternaryCopyOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryCopyOp,
                    EvmYul.Yul.State.setSharedState] at h
                  exact h.1.2.symm
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryCopyOp] at h

theorem wrapped_ternaryCopyOp_state_eq_of_ok_of_nonOk
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.ternaryCopyOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryCopyOp,
                    setSharedState_eq_self_of_nonOk hNonOk] at h
                  exact h.1.symm
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryCopyOp] at h

theorem wrapped_quaternaryCopyOp_store_eq_of_ok
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      (match EvmYul.Yul.quaternaryCopyOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.quaternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.quaternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.quaternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.quaternaryCopyOp] at h
              | cons d restFinal =>
                  cases restFinal with
                  | nil =>
                      simp [EvmYul.Yul.quaternaryCopyOp,
                        EvmYul.Yul.State.setSharedState] at h
                      exact h.1.2.symm
                  | cons e restExtra =>
                      simp [EvmYul.Yul.quaternaryCopyOp] at h

theorem wrapped_quaternaryCopyOp_state_eq_of_ok_of_nonOk
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      (match EvmYul.Yul.quaternaryCopyOp op state args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (outState, values)) :
    outState = state := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.quaternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.quaternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.quaternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.quaternaryCopyOp] at h
              | cons d restFinal =>
                  cases restFinal with
                  | nil =>
                      simp [EvmYul.Yul.quaternaryCopyOp,
                        setSharedState_eq_self_of_nonOk hNonOk] at h
                      exact h.1.symm
                  | cons e restExtra =>
                      simp [EvmYul.Yul.quaternaryCopyOp] at h

theorem wrapped_binaryMachineStateOp_not_checkpoint_of_ok
    {op : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryMachineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp,
                EvmYul.Yul.State.setMachineState] at h
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp] at h

theorem wrapped_binaryMachineStateOp'_not_checkpoint_of_ok
    {op : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryMachineStateOp' op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp'] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp'] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp',
                EvmYul.Yul.State.setMachineState] at h
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at h

theorem wrapped_ternaryMachineStateOp_not_checkpoint_of_ok
    {op : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.ternaryMachineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryMachineStateOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp,
                    EvmYul.Yul.State.setMachineState] at h
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at h

theorem wrapped_unaryStateOp_not_checkpoint_of_ok
    {op : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.unaryStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.unaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp,
            EvmYul.Yul.State.setSharedState] at h
      | cons b restTail =>
          simp [EvmYul.Yul.unaryStateOp] at h

theorem wrapped_binaryStateOp_not_checkpoint_of_ok
    {op : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryStateOp,
                EvmYul.Yul.State.setState] at h
          | cons c restRest =>
              simp [EvmYul.Yul.binaryStateOp] at h

theorem wrapped_ternaryCopyOp_not_checkpoint_of_ok
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.ternaryCopyOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryCopyOp,
                    EvmYul.Yul.State.setSharedState] at h
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryCopyOp] at h

theorem wrapped_quaternaryCopyOp_not_checkpoint_of_ok
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      (match EvmYul.Yul.quaternaryCopyOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.Checkpoint jump, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.quaternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.quaternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.quaternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.quaternaryCopyOp] at h
              | cons d restFinal =>
                  cases restFinal with
                  | nil =>
                      simp [EvmYul.Yul.quaternaryCopyOp,
                        EvmYul.Yul.State.setSharedState] at h
                  | cons e restExtra =>
                      simp [EvmYul.Yul.quaternaryCopyOp] at h

theorem wrapped_execUnOp_not_outOfFuel_of_ok
    {f : EvmYul.Primop.Unary}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.execUnOp f (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_execUnOp_state_eq_of_ok h
  cases hEq

theorem wrapped_execBinOp_not_outOfFuel_of_ok
    {f : EvmYul.Primop.Binary}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.execBinOp f (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_execBinOp_state_eq_of_ok h
  cases hEq

theorem wrapped_execTriOp_not_outOfFuel_of_ok
    {f : EvmYul.Primop.Ternary}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.execTriOp f (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_execTriOp_state_eq_of_ok h
  cases hEq

theorem wrapped_execQuadOp_not_outOfFuel_of_ok
    {f : EvmYul.Primop.Quaternary}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.execQuadOp f (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_execQuadOp_state_eq_of_ok h
  cases hEq

theorem wrapped_executionEnvOp_not_outOfFuel_of_ok
    {op : EvmYul.ExecutionEnv .Yul → Word}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.executionEnvOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_executionEnvOp_state_eq_of_ok (args := args) h
  cases hEq

theorem wrapped_unaryExecutionEnvOp_not_outOfFuel_of_ok
    {op : EvmYul.ExecutionEnv .Yul → Word → Word}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.unaryExecutionEnvOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_unaryExecutionEnvOp_state_eq_of_ok h
  cases hEq

theorem wrapped_machineStateOp_not_outOfFuel_of_ok
    {op : EvmYul.MachineState → Word}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.machineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_machineStateOp_state_eq_of_ok (args := args) h
  cases hEq

theorem wrapped_stateOp_not_outOfFuel_of_ok
    {op : EvmYul.State .Yul → Word}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.stateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
  cases hEq

theorem wrapped_binaryMachineStateOp_not_outOfFuel_of_ok
    {op : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryMachineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp,
                EvmYul.Yul.State.setMachineState] at h
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp] at h

theorem wrapped_binaryMachineStateOp'_not_outOfFuel_of_ok
    {op : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryMachineStateOp' op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryMachineStateOp'] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp'] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp',
                EvmYul.Yul.State.setMachineState] at h
          | cons c restRest =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at h

theorem wrapped_ternaryMachineStateOp_not_outOfFuel_of_ok
    {op : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.ternaryMachineStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryMachineStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryMachineStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryMachineStateOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp,
                    EvmYul.Yul.State.setMachineState] at h
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at h

theorem wrapped_unaryStateOp_not_outOfFuel_of_ok
    {op : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.unaryStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.unaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp,
            EvmYul.Yul.State.setSharedState] at h
      | cons b restTail =>
          simp [EvmYul.Yul.unaryStateOp] at h

theorem wrapped_binaryStateOp_not_outOfFuel_of_ok
    {op : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.binaryStateOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.binaryStateOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.binaryStateOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.binaryStateOp,
                EvmYul.Yul.State.setState] at h
          | cons c restRest =>
              simp [EvmYul.Yul.binaryStateOp] at h

theorem wrapped_ternaryCopyOp_not_outOfFuel_of_ok
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.ternaryCopyOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.ternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.ternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.ternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.ternaryCopyOp,
                    EvmYul.Yul.State.setSharedState] at h
              | cons d restFinal =>
                  simp [EvmYul.Yul.ternaryCopyOp] at h

theorem wrapped_quaternaryCopyOp_not_outOfFuel_of_ok
    {op :
      EvmYul.SharedState .Yul → Word → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      (match EvmYul.Yul.quaternaryCopyOp op (.Ok shared store) args with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok (.OutOfFuel, values)) :
    False := by
  cases args with
  | nil =>
      simp [EvmYul.Yul.quaternaryCopyOp] at h
  | cons a rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.quaternaryCopyOp] at h
      | cons b restTail =>
          cases restTail with
          | nil =>
              simp [EvmYul.Yul.quaternaryCopyOp] at h
          | cons c restRest =>
              cases restRest with
              | nil =>
                  simp [EvmYul.Yul.quaternaryCopyOp] at h
              | cons d restFinal =>
                  cases restFinal with
                  | nil =>
                      simp [EvmYul.Yul.quaternaryCopyOp,
                        EvmYul.Yul.State.setSharedState] at h
                  | cons e restExtra =>
                      simp [EvmYul.Yul.quaternaryCopyOp] at h

theorem primCall_keccak256_state_eq_of_ok_of_nonOk
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Keccak .KECCAK256 : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      have hStep :
          EvmYul.step ((.Keccak .KECCAK256 : EvmYul.Operation .Yul)) none =
            EvmYul.Yul.binaryMachineStateOp'
              EvmYul.MachineState.keccak256 := by
        rfl
      simp [EvmYul.Yul.primCall] at h
      rw [hStep] at h
      exact
        wrapped_binaryMachineStateOp'_state_eq_of_ok_of_nonOk hNonOk h

theorem primCall_stopArith_state_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.SAOp .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel state
          ((.StopArith op : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | STOP =>
          simp [EvmYul.Yul.primCall] at h
          unfold EvmYul.step at h
          change
            (match
              (Except.error
                (EvmYul.Yul.Exception.YulHalt
                  (state.setMachineState
                    (state.toMachineState.setHReturn ByteArray.empty))
                  ⟨0⟩) :
                Except EvmYul.Yul.Exception
                  (EvmYul.Yul.State × Option Word)) with
            | Except.ok (s, lit) => Except.ok (s, lit.toList)
            | Except.error e => Except.error e) =
              Except.ok (outState, values) at h
          simp at h
      | ADD =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | MUL =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SUB =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | DIV =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SDIV =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | MOD =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SMOD =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | ADDMOD =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execTriOp_state_eq_of_ok h
      | MULMOD =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execTriOp_state_eq_of_ok h
      | EXP =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SIGNEXTEND =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h

theorem primCall_compBit_state_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.CBLOp .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel state
          ((.CompBit op : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | LT =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | GT =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SLT =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SGT =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | EQ =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | ISZERO =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execUnOp_state_eq_of_ok h
      | AND =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | OR =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | XOR =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | NOT =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execUnOp_state_eq_of_ok h
      | BYTE =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SHL =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SHR =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h
      | SAR =>
          simp [EvmYul.Yul.primCall] at h
          exact wrapped_execBinOp_state_eq_of_ok h

theorem primCall_stopArith_store_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.SAOp .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StopArith op : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store :=
  ok_store_eq_of_state_eq (primCall_stopArith_state_eq_of_ok h)

theorem primCall_compBit_store_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.CBLOp .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.CompBit op : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store :=
  ok_store_eq_of_state_eq (primCall_compBit_state_eq_of_ok h)

theorem primCall_keccak_store_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.KOp .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Keccak op : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | KECCAK256 =>
          have hStep :
              EvmYul.step
                  ((.Keccak .KECCAK256 : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp'
                  EvmYul.MachineState.keccak256 := by
            rfl
          simp [EvmYul.Yul.primCall] at h
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp'_store_eq_of_ok h

theorem primCall_block_state_eq_of_ok_of_nonOk
    {fuel : Nat} {op : EvmYul.Operation.BOp .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Block op : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | BLOCKHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOCKHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.blockHash s v)) := by
            rfl
          rw [hStep] at h
          exact
            wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | COINBASE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .COINBASE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_state_eq_of_ok (args := args) h
      | TIMESTAMP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .TIMESTAMP : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.timeStamp := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_state_eq_of_ok (args := args) h
      | NUMBER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .NUMBER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.number := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_state_eq_of_ok (args := args) h
      | PREVRANDAO =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .PREVRANDAO : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.prevRandao := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | GASLIMIT =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .GASLIMIT : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.gasLimit := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_state_eq_of_ok (args := args) h
      | CHAINID =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .CHAINID : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.chainId := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_state_eq_of_ok (args := args) h
      | SELFBALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .SELFBALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.selfbalance := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_state_eq_of_ok (args := args) h
      | BASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.basefee := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | BLOBHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryExecutionEnvOp EvmYul.blobhash := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryExecutionEnvOp_state_eq_of_ok h
      | BLOBBASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBBASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  EvmYul.ExecutionEnv.getBlobGasprice := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h

theorem primCall_block_store_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.BOp .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Block op : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | BLOCKHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOCKHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.blockHash s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_store_eq_of_ok h
      | COINBASE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .COINBASE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_store_eq_of_ok (args := args) h
      | TIMESTAMP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .TIMESTAMP : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.timeStamp := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_store_eq_of_ok (args := args) h
      | NUMBER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .NUMBER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.number := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_store_eq_of_ok (args := args) h
      | PREVRANDAO =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .PREVRANDAO : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.prevRandao := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | GASLIMIT =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .GASLIMIT : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.gasLimit := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_store_eq_of_ok (args := args) h
      | CHAINID =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .CHAINID : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.chainId := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_store_eq_of_ok (args := args) h
      | SELFBALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .SELFBALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.selfbalance := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_store_eq_of_ok (args := args) h
      | BASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.basefee := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | BLOBHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryExecutionEnvOp EvmYul.blobhash := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryExecutionEnvOp_store_eq_of_ok h
      | BLOBBASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBBASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  EvmYul.ExecutionEnv.getBlobGasprice := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h

theorem primCall_block_not_checkpoint_of_ok
    {fuel : Nat} {op : EvmYul.Operation.BOp .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Block op : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | BLOCKHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOCKHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.blockHash s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_checkpoint_of_ok h
      | COINBASE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .COINBASE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
          cases hEq
      | TIMESTAMP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .TIMESTAMP : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.timeStamp := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
          cases hEq
      | NUMBER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .NUMBER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.number := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
          cases hEq
      | PREVRANDAO =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .PREVRANDAO : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.prevRandao := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | GASLIMIT =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .GASLIMIT : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.gasLimit := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
          cases hEq
      | CHAINID =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .CHAINID : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.chainId := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
          cases hEq
      | SELFBALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .SELFBALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.selfbalance := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_stateOp_state_eq_of_ok (args := args) h
          cases hEq
      | BASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.basefee := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | BLOBHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryExecutionEnvOp EvmYul.blobhash := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_unaryExecutionEnvOp_state_eq_of_ok h
          cases hEq
      | BLOBBASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBBASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  EvmYul.ExecutionEnv.getBlobGasprice := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq

theorem primCall_block_not_outOfFuel_of_ok
    {fuel : Nat} {op : EvmYul.Operation.BOp .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Block op : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | BLOCKHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOCKHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.blockHash s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_outOfFuel_of_ok h
      | COINBASE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .COINBASE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_not_outOfFuel_of_ok (args := args) h
      | TIMESTAMP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .TIMESTAMP : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.timeStamp := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_not_outOfFuel_of_ok (args := args) h
      | NUMBER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .NUMBER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.number := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_not_outOfFuel_of_ok (args := args) h
      | PREVRANDAO =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .PREVRANDAO : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.prevRandao := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | GASLIMIT =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .GASLIMIT : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.gasLimit := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_not_outOfFuel_of_ok (args := args) h
      | CHAINID =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .CHAINID : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.chainId := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_not_outOfFuel_of_ok (args := args) h
      | SELFBALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .SELFBALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.stateOp EvmYul.State.selfbalance := by
            rfl
          rw [hStep] at h
          exact wrapped_stateOp_not_outOfFuel_of_ok (args := args) h
      | BASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.basefee := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | BLOBHASH =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBHASH : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryExecutionEnvOp EvmYul.blobhash := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryExecutionEnvOp_not_outOfFuel_of_ok h
      | BLOBBASEFEE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Block .BLOBBASEFEE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  EvmYul.ExecutionEnv.getBlobGasprice := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h

theorem primCall_returndatacopy_state_eq_of_ok_of_nonOk
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
                match lits with
                | [a, b, c] =>
                    if
                        yulState.toSharedState.returnData.size <
                          b.toNat + c.toNat then
                      .error .InvalidMemoryAccess
                    else
                      let mState' :=
                        yulState.toSharedState.toMachineState.returndatacopy
                          a b c
                      .ok (yulState.setMachineState mState', .none)
                | _ => .error .InvalidArguments) := by
          rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp at h
          | cons b restTail =>
              cases restTail with
              | nil =>
                  simp at h
              | cons c restRest =>
                    cases restRest with
                    | nil =>
                        by_cases hBounds :
                            state.toSharedState.returnData.size <
                              b.toNat + c.toNat
                        · simp [hBounds] at h
                        · simp [hBounds,
                            setMachineState_eq_self_of_nonOk hNonOk] at h
                          exact h.1.symm
                    | cons d restFinal =>
                        simp at h

theorem primCall_returndatacopy_store_eq_of_ok
    {fuel : Nat} {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
                match lits with
                | [a, b, c] =>
                    if
                        yulState.toSharedState.returnData.size <
                          b.toNat + c.toNat then
                      .error .InvalidMemoryAccess
                    else
                      let mState' :=
                        yulState.toSharedState.toMachineState.returndatacopy
                          a b c
                      .ok (yulState.setMachineState mState', .none)
                | _ => .error .InvalidArguments) := by
          rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp at h
          | cons b restTail =>
              cases restTail with
              | nil =>
                  simp at h
              | cons c restRest =>
                    cases restRest with
                    | nil =>
                        by_cases hBounds :
                            shared.returnData.size < b.toNat + c.toNat
                        · simp [EvmYul.Yul.State.toSharedState, hBounds] at h
                        · simp [EvmYul.Yul.State.toSharedState,
                            EvmYul.Yul.State.setMachineState, hBounds] at h
                          exact h.1.2.symm
                    | cons d restFinal =>
                        simp at h

theorem primCall_returndatacopy_not_checkpoint_of_ok
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {jump : EvmYul.Yul.Jump}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
                match lits with
                | [a, b, c] =>
                    if
                        yulState.toSharedState.returnData.size <
                          b.toNat + c.toNat then
                      .error .InvalidMemoryAccess
                    else
                      let mState' :=
                        yulState.toSharedState.toMachineState.returndatacopy
                          a b c
                      .ok (yulState.setMachineState mState', .none)
                | _ => .error .InvalidArguments) := by
          rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp at h
          | cons b restTail =>
              cases restTail with
              | nil =>
                  simp at h
              | cons c restRest =>
                    cases restRest with
                    | nil =>
                        by_cases hBounds :
                            shared.returnData.size < b.toNat + c.toNat
                        · simp [EvmYul.Yul.State.toSharedState, hBounds] at h
                        · simp [EvmYul.Yul.State.toSharedState,
                            EvmYul.Yul.State.setMachineState, hBounds] at h
                    | cons d restFinal =>
                        simp at h

theorem primCall_returndatacopy_not_outOfFuel_of_ok
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
                match lits with
                | [a, b, c] =>
                    if
                        yulState.toSharedState.returnData.size <
                          b.toNat + c.toNat then
                      .error .InvalidMemoryAccess
                    else
                      let mState' :=
                        yulState.toSharedState.toMachineState.returndatacopy
                          a b c
                      .ok (yulState.setMachineState mState', .none)
                | _ => .error .InvalidArguments) := by
          rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp at h
          | cons b restTail =>
              cases restTail with
              | nil =>
                  simp at h
              | cons c restRest =>
                    cases restRest with
                    | nil =>
                        by_cases hBounds :
                            shared.returnData.size < b.toNat + c.toNat
                        · simp [EvmYul.Yul.State.toSharedState, hBounds] at h
                        · simp [EvmYul.Yul.State.toSharedState,
                            EvmYul.Yul.State.setMachineState, hBounds] at h
                    | cons d restFinal =>
                        simp at h

def EnvCheckpointSafe : EvmYul.Operation.EOp .Yul → Prop
  | _ => True

theorem primCall_env_state_eq_of_ok_of_nonOk
    {fuel : Nat} {op : EvmYul.Operation.EOp .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hSupported : EnvCheckpointSafe op)
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Env op : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | ADDRESS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ADDRESS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | BALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .BALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.balance := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | ORIGIN =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ORIGIN : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | CALLER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | CALLVALUE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLVALUE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.ExecutionEnv.weiValue := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | CALLDATALOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATALOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.calldataload s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | CALLDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.calldata) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | CALLDATACOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATACOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.calldatacopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_state_eq_of_ok_of_nonOk hNonOk h
      | GASPRICE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .GASPRICE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
      | CODESIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CODESIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.codeBytes) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_state_eq_of_ok (args := args) h
        | CODECOPY =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .CODECOPY : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.ternaryCopyOp
                    EvmYul.SharedState.codeBytesCopy := by
              rfl
            rw [hStep] at h
            exact wrapped_ternaryCopyOp_state_eq_of_ok_of_nonOk hNonOk h
        | EXTCODESIZE =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODESIZE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeSize := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
        | EXTCODECOPY =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODECOPY : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.quaternaryCopyOp
                    EvmYul.SharedState.extCodeCopy' := by
              rfl
            rw [hStep] at h
            exact wrapped_quaternaryCopyOp_state_eq_of_ok_of_nonOk
              hNonOk h
      | RETURNDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .RETURNDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp
                  EvmYul.MachineState.returndatasize := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_state_eq_of_ok (args := args) h
        | RETURNDATACOPY =>
            exact primCall_returndatacopy_state_eq_of_ok_of_nonOk
              hNonOk h
        | EXTCODEHASH =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODEHASH : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeHash := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h

theorem primCall_env_store_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.EOp .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (hSupported : EnvCheckpointSafe op)
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Env op : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | ADDRESS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ADDRESS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | BALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .BALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.balance := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_store_eq_of_ok h
      | ORIGIN =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ORIGIN : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | CALLER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | CALLVALUE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLVALUE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.ExecutionEnv.weiValue := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | CALLDATALOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATALOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.calldataload s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_store_eq_of_ok h
      | CALLDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.calldata) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | CALLDATACOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATACOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.calldatacopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_store_eq_of_ok h
      | GASPRICE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .GASPRICE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | CODESIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CODESIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.codeBytes) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_store_eq_of_ok (args := args) h
      | CODECOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CODECOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.codeBytesCopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_store_eq_of_ok h
        | EXTCODESIZE =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODESIZE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeSize := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_store_eq_of_ok h
        | EXTCODECOPY =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODECOPY : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.quaternaryCopyOp
                    EvmYul.SharedState.extCodeCopy' := by
              rfl
            rw [hStep] at h
            exact wrapped_quaternaryCopyOp_store_eq_of_ok h
      | RETURNDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .RETURNDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp
                  EvmYul.MachineState.returndatasize := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_store_eq_of_ok (args := args) h
      | RETURNDATACOPY =>
          exact primCall_returndatacopy_store_eq_of_ok h
        | EXTCODEHASH =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODEHASH : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeHash := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_store_eq_of_ok h

theorem primCall_env_not_checkpoint_of_ok
    {fuel : Nat} {op : EvmYul.Operation.EOp .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (hSupported : EnvCheckpointSafe op)
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Env op : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | ADDRESS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ADDRESS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | BALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .BALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.balance := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_checkpoint_of_ok h
      | ORIGIN =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ORIGIN : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | CALLER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | CALLVALUE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLVALUE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.ExecutionEnv.weiValue := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | CALLDATALOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATALOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.calldataload s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_checkpoint_of_ok h
      | CALLDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.calldata) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | CALLDATACOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATACOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.calldatacopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_not_checkpoint_of_ok h
      | GASPRICE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .GASPRICE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | CODESIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CODESIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.codeBytes) := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_executionEnvOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | CODECOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CODECOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.codeBytesCopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_not_checkpoint_of_ok h
        | EXTCODESIZE =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODESIZE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeSize := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_not_checkpoint_of_ok h
        | EXTCODECOPY =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODECOPY : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.quaternaryCopyOp
                    EvmYul.SharedState.extCodeCopy' := by
              rfl
            rw [hStep] at h
            exact wrapped_quaternaryCopyOp_not_checkpoint_of_ok h
      | RETURNDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .RETURNDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp
                  EvmYul.MachineState.returndatasize := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_machineStateOp_state_eq_of_ok
            (args := args) h
          cases hEq
      | RETURNDATACOPY =>
          exact primCall_returndatacopy_not_checkpoint_of_ok h
        | EXTCODEHASH =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODEHASH : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeHash := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_not_checkpoint_of_ok h

theorem primCall_env_not_outOfFuel_of_ok
    {fuel : Nat} {op : EvmYul.Operation.EOp .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (hSupported : EnvCheckpointSafe op)
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Env op : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | ADDRESS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .ADDRESS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | BALANCE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .BALANCE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.balance := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_outOfFuel_of_ok h
      | ORIGIN =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step ((.Env .ORIGIN : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | CALLER =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step ((.Env .CALLER : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | CALLVALUE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLVALUE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp EvmYul.ExecutionEnv.weiValue := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | CALLDATALOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATALOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp
                  (fun s v => (s, EvmYul.State.calldataload s v)) := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_outOfFuel_of_ok h
      | CALLDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.calldata) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | CALLDATACOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .CALLDATACOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.calldatacopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_not_outOfFuel_of_ok h
      | GASPRICE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step ((.Env .GASPRICE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | CODESIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step ((.Env .CODESIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.executionEnvOp
                  (.ofNat ∘ ByteArray.size ∘
                    EvmYul.ExecutionEnv.codeBytes) := by
            rfl
          rw [hStep] at h
          exact wrapped_executionEnvOp_not_outOfFuel_of_ok (args := args) h
      | CODECOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step ((.Env .CODECOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.codeBytesCopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryCopyOp_not_outOfFuel_of_ok h
        | EXTCODESIZE =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODESIZE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeSize := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_not_outOfFuel_of_ok h
        | EXTCODECOPY =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODECOPY : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.quaternaryCopyOp
                    EvmYul.SharedState.extCodeCopy' := by
              rfl
            rw [hStep] at h
            exact wrapped_quaternaryCopyOp_not_outOfFuel_of_ok h
      | RETURNDATASIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.Env .RETURNDATASIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp
                  EvmYul.MachineState.returndatasize := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_not_outOfFuel_of_ok (args := args) h
      | RETURNDATACOPY =>
          exact primCall_returndatacopy_not_outOfFuel_of_ok h
        | EXTCODEHASH =>
            simp [EvmYul.Yul.primCall] at h
            have hStep :
                EvmYul.step
                    ((.Env .EXTCODEHASH : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeHash := by
              rfl
            rw [hStep] at h
            exact wrapped_unaryStateOp_not_outOfFuel_of_ok h

def StackMemFlowCheckpointSafe : EvmYul.Operation.SMSFOp .Yul → Prop
  | _ => True

theorem primCall_mload_not_checkpoint_of_ok
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {jump : EvmYul.Yul.Jump}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
              match lits with
              | [a] =>
                  let (v, mState') :=
                    yulState.toSharedState.toMachineState.mload a
                  let yulState' := yulState.setMachineState mState'
                  .ok (yulState', some v)
              | _ => .error .InvalidArguments) := by
        rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.State.setMachineState] at h
          | cons b restTail =>
              simp at h

theorem primCall_mload_not_outOfFuel_of_ok
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
              match lits with
              | [a] =>
                  let (v, mState') :=
                    yulState.toSharedState.toMachineState.mload a
                  let yulState' := yulState.setMachineState mState'
                  .ok (yulState', some v)
              | _ => .error .InvalidArguments) := by
        rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.State.setMachineState] at h
          | cons b restTail =>
              simp at h

theorem primCall_stackMemFlow_not_checkpoint_of_ok
    {fuel : Nat} {op : EvmYul.Operation.SMSFOp .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {jump : EvmYul.Yul.Jump} {args values : List Word}
    (hSupported : StackMemFlowCheckpointSafe op)
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow op : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | POP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .POP : EvmYul.Operation .Yul)) none =
                (fun yulState _ => .ok (yulState, .none)) := by
            rfl
          rw [hStep] at h
          simp at h
      | MLOAD =>
          exact primCall_mload_not_checkpoint_of_ok h
      | MSTORE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore := by
            rfl
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp_not_checkpoint_of_ok h
      | SLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .SLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.sload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_checkpoint_of_ok h
      | SSTORE =>
          cases hPerm : shared.executionEnv.perm
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm, MonadExcept.throw, instMonadExceptOfExcept,
              Except.instMonad, Except.bind] at h
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm] at h
            have hStep :
                EvmYul.step
                    ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.binaryStateOp EvmYul.State.sstore := by
              rfl
            rw [hStep] at h
            exact wrapped_binaryStateOp_not_checkpoint_of_ok h
      | MSTORE8 =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE8 : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore8 := by
            rfl
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp_not_checkpoint_of_ok h
      | MSIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.msize := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_machineStateOp_state_eq_of_ok (args := args) h
          cases hEq
      | GAS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.gas := by
            rfl
          rw [hStep] at h
          have hEq := wrapped_machineStateOp_state_eq_of_ok (args := args) h
          cases hEq
      | TLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .TLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.tload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_checkpoint_of_ok h
      | TSTORE =>
          cases hPerm : shared.executionEnv.perm
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm, MonadExcept.throw, instMonadExceptOfExcept,
              Except.instMonad, Except.bind] at h
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm] at h
            have hStep :
                EvmYul.step
                    ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.binaryStateOp EvmYul.State.tstore := by
              rfl
            rw [hStep] at h
            exact wrapped_binaryStateOp_not_checkpoint_of_ok h
      | MCOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MCOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryMachineStateOp
                  EvmYul.MachineState.mcopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryMachineStateOp_not_checkpoint_of_ok h

theorem primCall_stackMemFlow_not_outOfFuel_of_ok
    {fuel : Nat} {op : EvmYul.Operation.SMSFOp .Yul}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (hSupported : StackMemFlowCheckpointSafe op)
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow op : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | POP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .POP : EvmYul.Operation .Yul)) none =
                (fun yulState _ => .ok (yulState, .none)) := by
            rfl
          rw [hStep] at h
          simp at h
      | MLOAD =>
          exact primCall_mload_not_outOfFuel_of_ok h
      | MSTORE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore := by
            rfl
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp_not_outOfFuel_of_ok h
      | SLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .SLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.sload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_outOfFuel_of_ok h
      | SSTORE =>
          cases hPerm : shared.executionEnv.perm
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm, MonadExcept.throw, instMonadExceptOfExcept,
              Except.instMonad, Except.bind] at h
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm] at h
            have hStep :
                EvmYul.step
                    ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.binaryStateOp EvmYul.State.sstore := by
              rfl
            rw [hStep] at h
            exact wrapped_binaryStateOp_not_outOfFuel_of_ok h
      | MSTORE8 =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE8 : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore8 := by
            rfl
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp_not_outOfFuel_of_ok h
      | MSIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.msize := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_not_outOfFuel_of_ok (args := args) h
      | GAS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.gas := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_not_outOfFuel_of_ok (args := args) h
      | TLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .TLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.tload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_not_outOfFuel_of_ok h
      | TSTORE =>
          cases hPerm : shared.executionEnv.perm
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm, MonadExcept.throw, instMonadExceptOfExcept,
              Except.instMonad, Except.bind] at h
          · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hPerm] at h
            have hStep :
                EvmYul.step
                    ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.binaryStateOp EvmYul.State.tstore := by
              rfl
            rw [hStep] at h
            exact wrapped_binaryStateOp_not_outOfFuel_of_ok h
      | MCOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MCOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryMachineStateOp
                  EvmYul.MachineState.mcopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryMachineStateOp_not_outOfFuel_of_ok h

theorem primCall_mload_state_eq_of_ok_of_nonOk
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
              match lits with
              | [a] =>
                  let (v, mState') :=
                    yulState.toSharedState.toMachineState.mload a
                  let yulState' := yulState.setMachineState mState'
                  .ok (yulState', some v)
              | _ => .error .InvalidArguments) := by
        rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp [setMachineState_eq_self_of_nonOk hNonOk] at h
              exact h.1.symm
          | cons b restTail =>
              simp at h

theorem primCall_stackMemFlow_state_eq_of_ok_of_nonOk
    {fuel : Nat} {op : EvmYul.Operation.SMSFOp .Yul}
    {state outState : EvmYul.Yul.State} {args values : List Word}
    (hSupported : StackMemFlowCheckpointSafe op)
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.StackMemFlow op : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    outState = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | POP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .POP : EvmYul.Operation .Yul)) none =
                (fun yulState _ => .ok (yulState, .none)) := by
            rfl
          rw [hStep] at h
          simp at h
          exact h.1.symm
      | MLOAD =>
          exact primCall_mload_state_eq_of_ok_of_nonOk hNonOk h
      | MSTORE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore := by
            rfl
          rw [hStep] at h
          exact
            wrapped_binaryMachineStateOp_state_eq_of_ok_of_nonOk
              hNonOk h
      | SLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .SLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.sload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | SSTORE =>
          cases hPerm : state.executionEnv.perm
          · exfalso
            simp [EvmYul.Yul.primCall, hPerm, MonadExcept.throw,
              instMonadExceptOfExcept, Except.instMonad, Except.bind] at h
          · simp [EvmYul.Yul.primCall, hPerm] at h
            have hStep :
                EvmYul.step
                    ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.binaryStateOp EvmYul.State.sstore := by
              rfl
            rw [hStep] at h
            exact wrapped_binaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | MSTORE8 =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE8 : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore8 := by
            rfl
          rw [hStep] at h
          exact
            wrapped_binaryMachineStateOp_state_eq_of_ok_of_nonOk
              hNonOk h
      | MSIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.msize := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_state_eq_of_ok (args := args) h
      | GAS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.gas := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_state_eq_of_ok (args := args) h
      | TLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .TLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.tload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | TSTORE =>
          cases hPerm : state.executionEnv.perm
          · exfalso
            simp [EvmYul.Yul.primCall, hPerm, MonadExcept.throw,
              instMonadExceptOfExcept, Except.instMonad, Except.bind] at h
          · simp [EvmYul.Yul.primCall, hPerm] at h
            have hStep :
                EvmYul.step
                    ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.binaryStateOp EvmYul.State.tstore := by
              rfl
            rw [hStep] at h
            exact wrapped_binaryStateOp_state_eq_of_ok_of_nonOk hNonOk h
      | MCOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MCOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryMachineStateOp
                  EvmYul.MachineState.mcopy := by
            rfl
          rw [hStep] at h
          exact
            wrapped_ternaryMachineStateOp_state_eq_of_ok_of_nonOk
              hNonOk h

def SystemCheckpointSafe : EvmYul.Operation.SOp .Yul → Prop
  | .CREATE => False
  | .CALL => False
  | .CALLCODE => False
  | .DELEGATECALL => False
  | .CREATE2 => False
  | .STATICCALL => False
  | .SELFDESTRUCT => False
  | _ => True

def selfdestructState
    (state : EvmYul.Yul.State) (recipient : Word) :
    EvmYul.Yul.State :=
  EvmYul.Yul.selfdestructState state recipient

theorem step_selfdestruct_nil_eq (state : EvmYul.Yul.State) :
    EvmYul.step
        (EvmYul.Operation.SELFDESTRUCT : EvmYul.Operation .Yul) none
        state [] =
      .error .InvalidArguments := by
  rfl

theorem step_selfdestruct_lit_eq
    (state : EvmYul.Yul.State) (recipient : Word) :
    EvmYul.step
        (EvmYul.Operation.SELFDESTRUCT : EvmYul.Operation .Yul) none
        state [recipient] =
      .error (.YulHalt (selfdestructState state recipient)
        (EvmYul.UInt256.ofNat 0)) := by
  rfl

theorem step_selfdestruct_cons_cons_eq
    (state : EvmYul.Yul.State) (a b : Word) (rest : List Word) :
    EvmYul.step
        (EvmYul.Operation.SELFDESTRUCT : EvmYul.Operation .Yul) none
        state (a :: b :: rest) =
      .error .InvalidArguments := by
  rfl

/--
`STOP` ignores its argument list and halts with the zero return value.
-/
theorem primCall_stop_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (args : List Word) :
    EvmYul.Yul.primCall fuel.succ state
        ((.StopArith .STOP : EvmYul.Operation .Yul)) args =
      .error
        (.YulHalt
          (state.setMachineState
            (state.toMachineState.setHReturn ByteArray.empty))
          (EvmYul.UInt256.ofNat 0)) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

theorem primCall_return_nil_eq
    (fuel : Nat) (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .RETURN : EvmYul.Operation .Yul)) [] =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .RETURN : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmReturn yulState lits with
          | .error e => .error e
          | .ok (s, v) =>
              .error (EvmYul.Yul.Exception.YulHalt s (v.getD ⟨1⟩))) := by
    rfl
  rw [hStep]
  simp [EvmYul.Yul.binaryMachineStateOp]

theorem primCall_return_singleton_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (arg : Word) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .RETURN : EvmYul.Operation .Yul)) [arg] =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .RETURN : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmReturn yulState lits with
          | .error e => .error e
          | .ok (s, v) =>
              .error (EvmYul.Yul.Exception.YulHalt s (v.getD ⟨1⟩))) := by
    rfl
  rw [hStep]
  simp [EvmYul.Yul.binaryMachineStateOp]

theorem primCall_return_cons_cons_cons_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (arg₁ arg₂ arg₃ : Word)
    (rest : List Word) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .RETURN : EvmYul.Operation .Yul))
        (arg₁ :: arg₂ :: arg₃ :: rest) =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .RETURN : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmReturn yulState lits with
          | .error e => .error e
          | .ok (s, v) =>
              .error (EvmYul.Yul.Exception.YulHalt s (v.getD ⟨1⟩))) := by
    rfl
  rw [hStep]
  simp [EvmYul.Yul.binaryMachineStateOp]

/--
`RETURN [offset, size]` halts. `binaryMachineStateOp evmReturn` is total on
a two-element list (it pattern-matches `[a, b]` and returns `.ok` with no
failure path).
-/
theorem primCall_return_lit_lit_yul_halt
    (fuel : Nat) (state : EvmYul.Yul.State) (offset size : Word) :
    ∃ haltState value,
      EvmYul.Yul.primCall fuel.succ state
          ((.System .RETURN : EvmYul.Operation .Yul)) [offset, size] =
        .error (.YulHalt haltState value) := by
  refine
    ⟨state.setMachineState
        (EvmYul.MachineState.evmReturn state.toMachineState offset size),
      (Option.none : Option Word).getD ⟨1⟩, ?_⟩
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .RETURN : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmReturn yulState lits with
          | .error e => .error e
          | .ok (s, v) =>
              .error (EvmYul.Yul.Exception.YulHalt s (v.getD ⟨1⟩))) := by
    rfl
  rw [hStep]
  rfl

theorem primCall_revert_nil_eq
    (fuel : Nat) (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .REVERT : EvmYul.Operation .Yul)) [] =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .REVERT : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmRevert yulState lits with
          | .error e => .error e
          | .ok (s, _) => .error (EvmYul.Yul.Exception.Revert s)) := by
    rfl
  rw [hStep]
  simp [EvmYul.Yul.binaryMachineStateOp]

theorem primCall_revert_singleton_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (arg : Word) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .REVERT : EvmYul.Operation .Yul)) [arg] =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .REVERT : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmRevert yulState lits with
          | .error e => .error e
          | .ok (s, _) => .error (EvmYul.Yul.Exception.Revert s)) := by
    rfl
  rw [hStep]
  simp [EvmYul.Yul.binaryMachineStateOp]

theorem primCall_revert_cons_cons_cons_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (arg₁ arg₂ arg₃ : Word)
    (rest : List Word) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .REVERT : EvmYul.Operation .Yul))
        (arg₁ :: arg₂ :: arg₃ :: rest) =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .REVERT : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmRevert yulState lits with
          | .error e => .error e
          | .ok (s, _) => .error (EvmYul.Yul.Exception.Revert s)) := by
    rfl
  rw [hStep]
  simp [EvmYul.Yul.binaryMachineStateOp]

/--
`REVERT [offset, size]` reverts. `binaryMachineStateOp evmRevert` is total on
a two-element list.
-/
theorem primCall_revert_lit_lit_revert
    (fuel : Nat) (state : EvmYul.Yul.State) (offset size : Word) :
    ∃ revertState,
      EvmYul.Yul.primCall fuel.succ state
          ((.System .REVERT : EvmYul.Operation .Yul)) [offset, size] =
        .error (.Revert revertState) := by
  refine
    ⟨state.setMachineState
        (EvmYul.MachineState.evmRevert state.toMachineState offset size), ?_⟩
  simp [EvmYul.Yul.primCall]
  have hStep :
      EvmYul.step
          ((.System .REVERT : EvmYul.Operation .Yul)) none =
        (fun yulState lits =>
          match
            EvmYul.Yul.binaryMachineStateOp
              EvmYul.MachineState.evmRevert yulState lits with
          | .error e => .error e
          | .ok (s, _) => .error (EvmYul.Yul.Exception.Revert s)) := by
    rfl
  rw [hStep]
  rfl

theorem primCall_selfdestruct_static_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (args : List Word)
    (hStatic : state.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)) args =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, hStatic]
  rfl

theorem primCall_selfdestruct_nil_eq
    (fuel : Nat) (state : EvmYul.Yul.State)
    (hStatic : ¬ state.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)) [] =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall, hStatic, step_selfdestruct_nil_eq]

theorem primCall_selfdestruct_cons_cons_eq
    (fuel : Nat) (state : EvmYul.Yul.State) (arg₁ arg₂ : Word)
    (rest : List Word)
    (hStatic : ¬ state.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ state
        ((.System .SELFDESTRUCT : EvmYul.Operation .Yul))
        (arg₁ :: arg₂ :: rest) =
      .error .InvalidArguments := by
  simp [EvmYul.Yul.primCall, hStatic, step_selfdestruct_cons_cons_eq]

theorem primCall_return_impossible_of_ok
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel state
          ((.System .RETURN : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.System .RETURN : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
              match
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.evmReturn yulState lits with
              | .error e => .error e
              | .ok (s, v) =>
                  .error (EvmYul.Yul.Exception.YulHalt s (v.getD ⟨1⟩))) := by
        rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp] at h
          | cons b restTail =>
              cases restTail with
              | nil =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at h
              | cons c restRest =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at h

theorem primCall_revert_impossible_of_ok
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel state
          ((.System .REVERT : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.System .REVERT : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
              match
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.evmRevert yulState lits with
              | .error e => .error e
              | .ok (s, _) => .error (EvmYul.Yul.Exception.Revert s)) := by
        rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp] at h
          | cons b restTail =>
              cases restTail with
              | nil =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at h
              | cons c restRest =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at h

theorem primCall_invalid_impossible_of_ok
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel state
          ((.System .INVALID : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      unfold EvmYul.step at h
      change
        (match
          (Except.error EvmYul.Yul.Exception.InvalidInstruction :
            Except EvmYul.Yul.Exception
              (EvmYul.Yul.State × Option Word)) with
        | Except.ok (s, lit) => Except.ok (s, lit.toList)
        | Except.error e => Except.error e) =
          Except.ok (outState, values) at h
      simp at h

theorem primCall_selfdestruct_impossible_of_ok
    {fuel : Nat} {state outState : EvmYul.Yul.State}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel state
          ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)) args =
        .ok (outState, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      by_cases hStatic : state.executionEnv.perm = false
      · simp [hStatic] at h
        change
          (Except.error EvmYul.Yul.Exception.StaticModeViolation :
            Except EvmYul.Yul.Exception
              (EvmYul.Yul.State × List Word)) =
            Except.ok (outState, values) at h
        simp at h
      · simp [hStatic] at h
        cases args with
        | nil =>
            simp [step_selfdestruct_nil_eq] at h
        | cons a rest =>
            cases rest with
            | nil =>
                simp [step_selfdestruct_lit_eq] at h
            | cons b restTail =>
                simp [step_selfdestruct_cons_cons_eq] at h

/--
Imported-Yul primitive semantics for the currently checked pure unary
primitive cases. These facts are deliberately below `Yul.Reference`: they know
about `primCall`, but not about source blocks, layouts, compiler-generated
locals, or bridge relations.
-/
theorem primCall_iszero_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (value : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .ISZERO : EvmYul.Operation .Yul)) [value] =
      .ok (.Ok shared store, [EvmYul.UInt256.isZero value]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execUnOp EvmYul.UInt256.isZero
        (.Ok shared store) [value] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.isZero value])
  simp [EvmYul.Yul.execUnOp]

theorem primCall_not_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (value : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .NOT : EvmYul.Operation .Yul)) [value] =
      .ok (.Ok shared store, [EvmYul.UInt256.lnot value]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execUnOp EvmYul.UInt256.lnot
        (.Ok shared store) [value] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.lnot value])
  simp [EvmYul.Yul.execUnOp]

theorem primCall_add_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .ADD : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.add left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.add
        (.Ok shared store) [left, right] with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.add left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_mul_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .MUL : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.mul left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.mul
        (.Ok shared store) [left, right] with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.mul left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_sub_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .SUB : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.sub left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.sub
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.sub left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_div_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .DIV : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.div left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.div
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.div left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_sdiv_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .SDIV : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.sdiv left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.sdiv
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.sdiv left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_mod_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .MOD : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.mod left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.mod
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.mod left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_smod_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .SMOD : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.smod left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.smod
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.smod left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_addmod_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left middle right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .ADDMOD : EvmYul.Operation .Yul))
        [left, middle, right] =
      .ok (.Ok shared store,
        [EvmYul.UInt256.addMod left middle right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execTriOp EvmYul.UInt256.addMod
        (.Ok shared store) [left, middle, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.addMod left middle right])
  simp [EvmYul.Yul.execTriOp]

theorem primCall_mulmod_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left middle right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .MULMOD : EvmYul.Operation .Yul))
        [left, middle, right] =
      .ok (.Ok shared store,
        [EvmYul.UInt256.mulMod left middle right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execTriOp EvmYul.UInt256.mulMod
        (.Ok shared store) [left, middle, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.mulMod left middle right])
  simp [EvmYul.Yul.execTriOp]

theorem primCall_keccak256_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (start size : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Keccak .KECCAK256 : EvmYul.Operation .Yul)) [start, size] =
      .ok
        (.Ok
          { shared with
            toMachineState :=
              (EvmYul.MachineState.keccak256 shared.toMachineState
                start size).2 }
          store,
        [(EvmYul.MachineState.keccak256 shared.toMachineState
          start size).1]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.binaryMachineStateOp',
    EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.setMachineState]
  rfl

theorem primCall_exp_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .EXP : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.exp left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.exp
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.exp left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_signextend_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .SIGNEXTEND : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.signextend left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.signextend
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.signextend left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_lt_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .LT : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.lt left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.lt
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.lt left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_gt_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .GT : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.gt left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.gt
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.gt left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_slt_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .SLT : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.slt left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.slt
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.slt left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_sgt_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .SGT : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.sgt left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.sgt
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.sgt left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_eq_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .EQ : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.eq left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.eq
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.eq left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_and_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .AND : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.land left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.land
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.land left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_or_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .OR : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.lor left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.lor
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.lor left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_xor_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .XOR : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.xor left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.xor
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.xor left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_byte_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .BYTE : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.byteAt left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.byteAt
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.byteAt left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_shl_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .SHL : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [(flip EvmYul.UInt256.shiftLeft) left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp (flip EvmYul.UInt256.shiftLeft)
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [(flip EvmYul.UInt256.shiftLeft) left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_shr_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .SHR : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [(flip EvmYul.UInt256.shiftRight) left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp (flip EvmYul.UInt256.shiftRight)
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [(flip EvmYul.UInt256.shiftRight) left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_sar_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.CompBit .SAR : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.sar left right]) := by
  simp [EvmYul.Yul.primCall]
  change
    (match
      EvmYul.Yul.execBinOp EvmYul.UInt256.sar
        (.Ok shared store) [left, right] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.UInt256.sar left right])
  simp [EvmYul.Yul.execBinOp]

theorem primCall_address_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .ADDRESS : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner)
          shared.executionEnv)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp
        ((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat ↑shared.executionEnv.codeOwner])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_balance_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (address : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .BALANCE : EvmYul.Operation .Yul)) [address] =
      .ok
        (.Ok { shared with
          toState := (EvmYul.State.balance shared.toState address).1 } store,
        [(EvmYul.State.balance shared.toState address).2]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp EvmYul.State.balance
        (.Ok shared store) [address] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := (EvmYul.State.balance shared.toState address).1 } store,
        [(EvmYul.State.balance shared.toState address).2])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_sload_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .SLOAD : EvmYul.Operation .Yul)) [slot] =
      .ok
        (.Ok { shared with
          toState := (EvmYul.State.sload shared.toState slot).1 } store,
        [(EvmYul.State.sload shared.toState slot).2]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp EvmYul.State.sload
        (.Ok shared store) [slot] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := (EvmYul.State.sload shared.toState slot).1 } store,
        [(EvmYul.State.sload shared.toState slot).2])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_sstore_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot value : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) [slot, value] =
      .ok
        (.Ok { shared with
          toState := EvmYul.State.sstore shared.toState slot value } store,
        []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.binaryStateOp EvmYul.State.sstore
        (.Ok shared store) [slot, value] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := EvmYul.State.sstore shared.toState slot value } store,
        [])
  simp [EvmYul.Yul.binaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.setState]

theorem primCall_sstore_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot value : Word)
    (hStatic : shared.executionEnv.perm = false) :
  EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) [slot, value] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_sstore_store_eq_of_ok
    {fuel : Nat} {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases hPerm : shared.executionEnv.perm
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hPerm, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hPerm] at h
        have hStep :
            EvmYul.step
                ((.StackMemFlow .SSTORE : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.binaryStateOp EvmYul.State.sstore := by
          rfl
        rw [hStep] at h
        exact wrapped_binaryStateOp_store_eq_of_ok h

theorem primCall_tload_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .TLOAD : EvmYul.Operation .Yul)) [slot] =
      .ok
        (.Ok { shared with
          toState := (EvmYul.State.tload shared.toState slot).1 } store,
        [(EvmYul.State.tload shared.toState slot).2]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp EvmYul.State.tload
        (.Ok shared store) [slot] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := (EvmYul.State.tload shared.toState slot).1 } store,
        [(EvmYul.State.tload shared.toState slot).2])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_tstore_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot value : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) [slot, value] =
      .ok
        (.Ok { shared with
          toState := EvmYul.State.tstore shared.toState slot value } store,
        []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.binaryStateOp EvmYul.State.tstore
        (.Ok shared store) [slot, value] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := EvmYul.State.tstore shared.toState slot value } store,
        [])
  simp [EvmYul.Yul.binaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.setState]

theorem primCall_tstore_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot value : Word)
    (hStatic : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) [slot, value] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_tstore_store_eq_of_ok
    {fuel : Nat} {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases hPerm : shared.executionEnv.perm
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hPerm, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hPerm] at h
        have hStep :
            EvmYul.step
                ((.StackMemFlow .TSTORE : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.binaryStateOp EvmYul.State.tstore := by
          rfl
        rw [hStep] at h
        exact wrapped_binaryStateOp_store_eq_of_ok h

theorem primCall_mload_store_eq_of_ok
    {fuel : Nat} {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at h
      have hStep :
          EvmYul.step
              ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) none =
            (fun yulState lits =>
              match lits with
              | [a] =>
                  let (v, mState') :=
                    yulState.toSharedState.toMachineState.mload a
                  let yulState' := yulState.setMachineState mState'
                  .ok <| (yulState', some v)
              | _ => .error .InvalidArguments) := by
        rfl
      rw [hStep] at h
      cases args with
      | nil =>
          simp at h
      | cons a rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.State.setMachineState] at h
              exact h.1.2.symm
          | cons b restTail =>
              simp at h

theorem primCall_stackMemFlow_store_eq_of_ok
    {fuel : Nat} {op : EvmYul.Operation.SMSFOp .Yul}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore} {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.StackMemFlow op : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases op with
      | POP =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .POP : EvmYul.Operation .Yul)) none =
                (fun yulState _ => .ok (yulState, .none)) := by
            rfl
          rw [hStep] at h
          simp at h
          exact h.1.2.symm
      | MLOAD =>
          exact primCall_mload_store_eq_of_ok h
      | MSTORE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore := by
            rfl
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp_store_eq_of_ok h
      | SLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .SLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.sload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_store_eq_of_ok h
      | SSTORE =>
          exact primCall_sstore_store_eq_of_ok h
      | MSTORE8 =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSTORE8 : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.binaryMachineStateOp
                  EvmYul.MachineState.mstore8 := by
            rfl
          rw [hStep] at h
          exact wrapped_binaryMachineStateOp_store_eq_of_ok h
      | MSIZE =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.msize := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_store_eq_of_ok (args := args) h
      | GAS =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.machineStateOp EvmYul.MachineState.gas := by
            rfl
          rw [hStep] at h
          exact wrapped_machineStateOp_store_eq_of_ok (args := args) h
      | TLOAD =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .TLOAD : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.unaryStateOp EvmYul.State.tload := by
            rfl
          rw [hStep] at h
          exact wrapped_unaryStateOp_store_eq_of_ok h
      | TSTORE =>
          exact primCall_tstore_store_eq_of_ok h
      | MCOPY =>
          simp [EvmYul.Yul.primCall] at h
          have hStep :
              EvmYul.step
                  ((.StackMemFlow .MCOPY : EvmYul.Operation .Yul)) none =
                EvmYul.Yul.ternaryMachineStateOp
                  EvmYul.MachineState.mcopy := by
            rfl
          rw [hStep] at h
          exact wrapped_ternaryMachineStateOp_store_eq_of_ok h

theorem primCall_log0_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG0 : EvmYul.Operation .Yul)) [offset, size] =
      .ok
        (.Ok (EvmYul.SharedState.logOp offset size #[] shared) store, []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.log0Op (.Ok shared store) [offset, size] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.logOp offset size #[] shared) store, [])
  simp [EvmYul.Yul.log0Op]
  constructor <;> rfl

theorem primCall_log0_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size : Word)
    (hStatic : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG0 : EvmYul.Operation .Yul)) [offset, size] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_log1_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size topic : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG1 : EvmYul.Operation .Yul)) [offset, size, topic] =
      .ok
        (.Ok (EvmYul.SharedState.logOp offset size #[topic] shared) store,
          []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.log1Op (.Ok shared store) [offset, size, topic] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.logOp offset size #[topic] shared) store, [])
  simp [EvmYul.Yul.log1Op]
  constructor <;> rfl

theorem primCall_log1_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size topic : Word)
    (hStatic : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG1 : EvmYul.Operation .Yul)) [offset, size, topic] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_log2_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size topic0 topic1 : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG2 : EvmYul.Operation .Yul))
        [offset, size, topic0, topic1] =
      .ok
        (.Ok
          (EvmYul.SharedState.logOp offset size #[topic0, topic1] shared)
          store,
        []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.log2Op (.Ok shared store)
        [offset, size, topic0, topic1] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.logOp offset size #[topic0, topic1] shared)
          store,
        [])
  simp [EvmYul.Yul.log2Op]
  constructor <;> rfl

theorem primCall_log2_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size topic0 topic1 : Word)
    (hStatic : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG2 : EvmYul.Operation .Yul))
        [offset, size, topic0, topic1] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_log3_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size topic0 topic1 topic2 : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG3 : EvmYul.Operation .Yul))
        [offset, size, topic0, topic1, topic2] =
      .ok
        (.Ok
          (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
            shared)
          store,
        []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.log3Op (.Ok shared store)
        [offset, size, topic0, topic1, topic2] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
            shared)
          store,
        [])
  simp [EvmYul.Yul.log3Op]
  constructor <;> rfl

theorem primCall_log3_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset size topic0 topic1 topic2 : Word)
    (hStatic : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG3 : EvmYul.Operation .Yul))
        [offset, size, topic0, topic1, topic2] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_log4_ok_of_writable
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (offset size topic0 topic1 topic2 topic3 : Word)
    (hWritable : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG4 : EvmYul.Operation .Yul))
        [offset, size, topic0, topic1, topic2, topic3] =
      .ok
        (.Ok
          (EvmYul.SharedState.logOp offset size
            #[topic0, topic1, topic2, topic3] shared)
          store,
        []) := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hWritable]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.log4Op (.Ok shared store)
        [offset, size, topic0, topic1, topic2, topic3] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.logOp offset size
            #[topic0, topic1, topic2, topic3] shared)
          store,
        [])
  simp [EvmYul.Yul.log4Op]
  constructor <;> rfl

theorem primCall_log4_static_error
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (offset size topic0 topic1 topic2 topic3 : Word)
    (hStatic : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Log .LOG4 : EvmYul.Operation .Yul))
        [offset, size, topic0, topic1, topic2, topic3] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hStatic]
  change Except.error EvmYul.Yul.Exception.StaticModeViolation =
    Except.error EvmYul.Yul.Exception.StaticModeViolation
  rfl

theorem primCall_log0_store_eq_of_ok
    {fuel : Nat}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG0 : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        revert h
        cases args with
        | nil =>
            intro h
            have hStep :
                EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.log0Op := by
              rfl
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log0Op] at h
            rcases h with ⟨hState, _hValues⟩
            exact hState.2.symm
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                have hStep :
                    EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul))
                        none =
                      EvmYul.Yul.log0Op := by
                  rfl
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log0Op] at h
                rcases h with ⟨hState, _hValues⟩
                exact hState.2.symm
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    have hStep :
                        EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul))
                            none =
                          EvmYul.Yul.log0Op := by
                      rfl
                    rw [primCall_log0_ok_of_writable fuel shared store
                      offset size hWritable] at h
                    cases h
                    rfl
                | cons extra rest =>
                    intro h
                    have hStep :
                        EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul))
                            none =
                          EvmYul.Yul.log0Op := by
                      rfl
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log0Op] at h
                    rcases h with ⟨hState, _hValues⟩
                    exact hState.2.symm

theorem primCall_log0_state_eq_of_ok_of_nonOk
    {fuel : Nat}
    {state stateAfter : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Log .LOG0 : EvmYul.Operation .Yul)) args =
        .ok (stateAfter, values)) :
    stateAfter = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases state with
      | Ok shared store =>
          exact False.elim (hNonOk shared store rfl)
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log0Op, EvmYul.Yul.State.setSharedState] at h
          cases h
      | Checkpoint jump =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log0Op, EvmYul.Yul.State.setSharedState] at h
          cases h

theorem primCall_log0_not_checkpoint_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word} {jump : EvmYul.Yul.Jump}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG0 : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        revert h
        cases args with
        | nil =>
            intro h
            have hStep :
                EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul)) none =
                  EvmYul.Yul.log0Op := by
              rfl
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log0Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                have hStep :
                    EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul))
                        none =
                      EvmYul.Yul.log0Op := by
                  rfl
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log0Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    have hStep :
                        EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul))
                            none =
                          EvmYul.Yul.log0Op := by
                      rfl
                    rw [primCall_log0_ok_of_writable fuel shared store
                      offset size hWritable] at h
                    cases h
                | cons extra rest =>
                    intro h
                    have hStep :
                        EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul))
                            none =
                          EvmYul.Yul.log0Op := by
                      rfl
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log0Op] at h

theorem primCall_log1_store_eq_of_ok
    {fuel : Nat}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG1 : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG1 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log1Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log1Op] at h
            rcases h with ⟨hState, _hValues⟩
            exact hState.2.symm
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log1Op] at h
                rcases h with ⟨hState, _hValues⟩
                exact hState.2.symm
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log1Op] at h
                    rcases h with ⟨hState, _hValues⟩
                    exact hState.2.symm
                | cons topic rest =>
                    cases rest with
                    | nil =>
                        intro h
                        rw [primCall_log1_ok_of_writable fuel shared store
                          offset size topic hWritable] at h
                        cases h
                        rfl
                    | cons extra rest =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log1Op] at h
                        rcases h with ⟨hState, _hValues⟩
                        exact hState.2.symm

theorem primCall_log1_state_eq_of_ok_of_nonOk
    {fuel : Nat}
    {state stateAfter : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Log .LOG1 : EvmYul.Operation .Yul)) args =
        .ok (stateAfter, values)) :
    stateAfter = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases state with
      | Ok shared store =>
          exact False.elim (hNonOk shared store rfl)
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log1Op, EvmYul.Yul.State.setSharedState] at h
          cases h
      | Checkpoint jump =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log1Op, EvmYul.Yul.State.setSharedState] at h
          cases h

theorem primCall_log1_not_checkpoint_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word} {jump : EvmYul.Yul.Jump}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG1 : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG1 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log1Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log1Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log1Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log1Op] at h
                | cons topic rest =>
                    cases rest with
                    | nil =>
                        intro h
                        rw [primCall_log1_ok_of_writable fuel shared store
                          offset size topic hWritable] at h
                        cases h
                    | cons extra rest =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log1Op] at h

theorem primCall_log2_store_eq_of_ok
    {fuel : Nat}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG2 : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG2 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log2Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log2Op] at h
            rcases h with ⟨hState, _hValues⟩
            exact hState.2.symm
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log2Op] at h
                rcases h with ⟨hState, _hValues⟩
                exact hState.2.symm
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log2Op] at h
                    rcases h with ⟨hState, _hValues⟩
                    exact hState.2.symm
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log2Op] at h
                        rcases h with ⟨hState, _hValues⟩
                        exact hState.2.symm
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            rw [primCall_log2_ok_of_writable fuel shared store
                              offset size topic0 topic1 hWritable] at h
                            cases h
                            rfl
                        | cons extra rest =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log2Op] at h
                            rcases h with ⟨hState, _hValues⟩
                            exact hState.2.symm

theorem primCall_log2_state_eq_of_ok_of_nonOk
    {fuel : Nat}
    {state stateAfter : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Log .LOG2 : EvmYul.Operation .Yul)) args =
        .ok (stateAfter, values)) :
    stateAfter = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases state with
      | Ok shared store =>
          exact False.elim (hNonOk shared store rfl)
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log2Op, EvmYul.Yul.State.setSharedState] at h
          cases h
      | Checkpoint jump =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log2Op, EvmYul.Yul.State.setSharedState] at h
          cases h

theorem primCall_log2_not_checkpoint_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word} {jump : EvmYul.Yul.Jump}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG2 : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG2 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log2Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log2Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log2Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log2Op] at h
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log2Op] at h
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            rw [primCall_log2_ok_of_writable fuel shared store
                              offset size topic0 topic1 hWritable] at h
                            cases h
                        | cons extra rest =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log2Op] at h

theorem primCall_log3_store_eq_of_ok
    {fuel : Nat}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG3 : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG3 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log3Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log3Op] at h
            rcases h with ⟨hState, _hValues⟩
            exact hState.2.symm
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log3Op] at h
                rcases h with ⟨hState, _hValues⟩
                exact hState.2.symm
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log3Op] at h
                    rcases h with ⟨hState, _hValues⟩
                    exact hState.2.symm
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log3Op] at h
                        rcases h with ⟨hState, _hValues⟩
                        exact hState.2.symm
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log3Op] at h
                            rcases h with ⟨hState, _hValues⟩
                            exact hState.2.symm
                        | cons topic2 rest =>
                            cases rest with
                            | nil =>
                                intro h
                                rw [primCall_log3_ok_of_writable fuel shared
                                  store offset size topic0 topic1 topic2
                                  hWritable] at h
                                cases h
                                rfl
                            | cons extra rest =>
                                intro h
                                simp [EvmYul.Yul.primCall,
                                  EvmYul.Yul.State.executionEnv, hWritable] at h
                                rw [hStep] at h
                                simp [EvmYul.Yul.log3Op] at h
                                rcases h with ⟨hState, _hValues⟩
                                exact hState.2.symm

theorem primCall_log3_state_eq_of_ok_of_nonOk
    {fuel : Nat}
    {state stateAfter : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Log .LOG3 : EvmYul.Operation .Yul)) args =
        .ok (stateAfter, values)) :
    stateAfter = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases state with
      | Ok shared store =>
          exact False.elim (hNonOk shared store rfl)
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log3Op, EvmYul.Yul.State.setSharedState] at h
          cases h
      | Checkpoint jump =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log3Op, EvmYul.Yul.State.setSharedState] at h
          cases h

theorem primCall_log3_not_checkpoint_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word} {jump : EvmYul.Yul.Jump}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG3 : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG3 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log3Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log3Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log3Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log3Op] at h
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log3Op] at h
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log3Op] at h
                        | cons topic2 rest =>
                            cases rest with
                            | nil =>
                                intro h
                                rw [primCall_log3_ok_of_writable fuel shared
                                  store offset size topic0 topic1 topic2
                                  hWritable] at h
                                cases h
                            | cons extra rest =>
                                intro h
                                simp [EvmYul.Yul.primCall,
                                  EvmYul.Yul.State.executionEnv, hWritable] at h
                                rw [hStep] at h
                                simp [EvmYul.Yul.log3Op] at h

theorem primCall_log4_store_eq_of_ok
    {fuel : Nat}
    {shared sharedAfter : EvmYul.SharedState .Yul}
    {store storeAfter : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG4 : EvmYul.Operation .Yul)) args =
        .ok (.Ok sharedAfter storeAfter, values)) :
    storeAfter = store := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG4 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log4Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log4Op] at h
            rcases h with ⟨hState, _hValues⟩
            exact hState.2.symm
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log4Op] at h
                rcases h with ⟨hState, _hValues⟩
                exact hState.2.symm
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log4Op] at h
                    rcases h with ⟨hState, _hValues⟩
                    exact hState.2.symm
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log4Op] at h
                        rcases h with ⟨hState, _hValues⟩
                        exact hState.2.symm
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log4Op] at h
                            rcases h with ⟨hState, _hValues⟩
                            exact hState.2.symm
                        | cons topic2 rest =>
                            cases rest with
                            | nil =>
                                intro h
                                simp [EvmYul.Yul.primCall,
                                  EvmYul.Yul.State.executionEnv, hWritable] at h
                                rw [hStep] at h
                                simp [EvmYul.Yul.log4Op] at h
                                rcases h with ⟨hState, _hValues⟩
                                exact hState.2.symm
                            | cons topic3 rest =>
                                cases rest with
                                | nil =>
                                    intro h
                                    rw [primCall_log4_ok_of_writable fuel
                                      shared store offset size topic0 topic1
                                      topic2 topic3 hWritable] at h
                                    cases h
                                    rfl
                                | cons extra rest =>
                                    intro h
                                    simp [EvmYul.Yul.primCall,
                                      EvmYul.Yul.State.executionEnv,
                                      hWritable] at h
                                    rw [hStep] at h
                                    simp [EvmYul.Yul.log4Op] at h
                                    rcases h with ⟨hState, _hValues⟩
                                    exact hState.2.symm

theorem primCall_log4_state_eq_of_ok_of_nonOk
    {fuel : Nat}
    {state stateAfter : EvmYul.Yul.State}
    {args values : List Word}
    (hNonOk :
      ∀ shared store, state ≠ (.Ok shared store : EvmYul.Yul.State))
    (h :
      EvmYul.Yul.primCall fuel state
          ((.Log .LOG4 : EvmYul.Operation .Yul)) args =
        .ok (stateAfter, values)) :
    stateAfter = state := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      cases state with
      | Ok shared store =>
          exact False.elim (hNonOk shared store rfl)
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log4Op, EvmYul.Yul.State.setSharedState] at h
          cases h
      | Checkpoint jump =>
          simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.log4Op, EvmYul.Yul.State.setSharedState] at h
          cases h

theorem primCall_log4_not_checkpoint_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word} {jump : EvmYul.Yul.Jump}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG4 : EvmYul.Operation .Yul)) args =
        .ok (.Checkpoint jump, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic] at h
        cases h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG4 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log4Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log4Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log4Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log4Op] at h
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log4Op] at h
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log4Op] at h
                        | cons topic2 rest =>
                            cases rest with
                            | nil =>
                                intro h
                                simp [EvmYul.Yul.primCall,
                                  EvmYul.Yul.State.executionEnv, hWritable] at h
                                rw [hStep] at h
                                simp [EvmYul.Yul.log4Op] at h
                            | cons topic3 rest =>
                                cases rest with
                                | nil =>
                                    intro h
                                    rw [primCall_log4_ok_of_writable fuel
                                      shared store offset size topic0 topic1
                                      topic2 topic3 hWritable] at h
                                    cases h
                                | cons extra rest =>
                                    intro h
                                    simp [EvmYul.Yul.primCall,
                                      EvmYul.Yul.State.executionEnv,
                                      hWritable] at h
                                    rw [hStep] at h
                                    simp [EvmYul.Yul.log4Op] at h

theorem primCall_log0_not_outOfFuel_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG0 : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG0 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log0Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log0Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log0Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    rw [primCall_log0_ok_of_writable fuel shared store
                      offset size hWritable] at h
                    cases h
                | cons extra rest =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log0Op] at h

theorem primCall_log1_not_outOfFuel_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG1 : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG1 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log1Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log1Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log1Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log1Op] at h
                | cons topic rest =>
                    cases rest with
                    | nil =>
                        intro h
                        rw [primCall_log1_ok_of_writable fuel shared store
                          offset size topic hWritable] at h
                        cases h
                    | cons extra rest =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log1Op] at h

theorem primCall_log2_not_outOfFuel_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG2 : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG2 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log2Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log2Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log2Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log2Op] at h
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log2Op] at h
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            rw [primCall_log2_ok_of_writable fuel shared store
                              offset size topic0 topic1 hWritable] at h
                            cases h
                        | cons extra rest =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log2Op] at h

theorem primCall_log3_not_outOfFuel_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG3 : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG3 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log3Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log3Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log3Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log3Op] at h
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log3Op] at h
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log3Op] at h
                        | cons topic2 rest =>
                            cases rest with
                            | nil =>
                                intro h
                                rw [primCall_log3_ok_of_writable fuel shared
                                  store offset size topic0 topic1 topic2
                                  hWritable] at h
                                cases h
                            | cons extra rest =>
                                intro h
                                simp [EvmYul.Yul.primCall,
                                  EvmYul.Yul.State.executionEnv, hWritable] at h
                                rw [hStep] at h
                                simp [EvmYul.Yul.log3Op] at h

theorem primCall_log4_not_outOfFuel_of_ok
    {fuel : Nat}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    {args values : List Word}
    (h :
      EvmYul.Yul.primCall fuel (.Ok shared store)
          ((.Log .LOG4 : EvmYul.Operation .Yul)) args =
        .ok (.OutOfFuel, values)) :
    False := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at h
  | succ fuel =>
      by_cases hStatic : shared.executionEnv.perm = false
      · simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
          hStatic, MonadExcept.throw, instMonadExceptOfExcept,
          Except.instMonad, Except.bind] at h
      · have hWritable : shared.executionEnv.perm = true := by
          cases hPerm : shared.executionEnv.perm <;> simp [hPerm] at hStatic ⊢
        have hStep :
            EvmYul.step ((.Log .LOG4 : EvmYul.Operation .Yul)) none =
              EvmYul.Yul.log4Op := by
          rfl
        revert h
        cases args with
        | nil =>
            intro h
            simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
              hWritable] at h
            rw [hStep] at h
            simp [EvmYul.Yul.log4Op] at h
        | cons offset rest =>
            cases rest with
            | nil =>
                intro h
                simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
                  hWritable] at h
                rw [hStep] at h
                simp [EvmYul.Yul.log4Op] at h
            | cons size rest =>
                cases rest with
                | nil =>
                    intro h
                    simp [EvmYul.Yul.primCall,
                      EvmYul.Yul.State.executionEnv, hWritable] at h
                    rw [hStep] at h
                    simp [EvmYul.Yul.log4Op] at h
                | cons topic0 rest =>
                    cases rest with
                    | nil =>
                        intro h
                        simp [EvmYul.Yul.primCall,
                          EvmYul.Yul.State.executionEnv, hWritable] at h
                        rw [hStep] at h
                        simp [EvmYul.Yul.log4Op] at h
                    | cons topic1 rest =>
                        cases rest with
                        | nil =>
                            intro h
                            simp [EvmYul.Yul.primCall,
                              EvmYul.Yul.State.executionEnv, hWritable] at h
                            rw [hStep] at h
                            simp [EvmYul.Yul.log4Op] at h
                        | cons topic2 rest =>
                            cases rest with
                            | nil =>
                                intro h
                                simp [EvmYul.Yul.primCall,
                                  EvmYul.Yul.State.executionEnv, hWritable] at h
                                rw [hStep] at h
                                simp [EvmYul.Yul.log4Op] at h
                            | cons topic3 rest =>
                                cases rest with
                                | nil =>
                                    intro h
                                    rw [primCall_log4_ok_of_writable fuel
                                      shared store offset size topic0 topic1
                                      topic2 topic3 hWritable] at h
                                    cases h
                                | cons extra rest =>
                                    intro h
                                    simp [EvmYul.Yul.primCall,
                                      EvmYul.Yul.State.executionEnv,
                                      hWritable] at h
                                    rw [hStep] at h
                                    simp [EvmYul.Yul.log4Op] at h

theorem primCall_mload_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .MLOAD : EvmYul.Operation .Yul)) [slot] =
      .ok
        (.Ok
          { shared with
            toMachineState :=
              (EvmYul.MachineState.mload shared.toMachineState slot).2 }
          store,
        [(EvmYul.MachineState.mload shared.toMachineState slot).1]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.setMachineState]
  rfl

theorem primCall_pop_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (value : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .POP : EvmYul.Operation .Yul)) [value] =
      .ok (.Ok shared store, []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp
  rfl

theorem primCall_mstore_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot value : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)) [slot, value] =
      .ok
        (.Ok
          { shared with
            toMachineState :=
              EvmYul.MachineState.mstore shared.toMachineState slot value }
          store,
        []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.setMachineState]
  rfl

theorem primCall_mstore8_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (slot value : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .MSTORE8 : EvmYul.Operation .Yul)) [slot, value] =
      .ok
        (.Ok
          { shared with
            toMachineState :=
              EvmYul.MachineState.mstore8 shared.toMachineState slot value }
          store,
        []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.setMachineState]
  rfl

theorem primCall_mcopy_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (writeStart readStart size : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .MCOPY : EvmYul.Operation .Yul))
          [writeStart, readStart, size] =
      .ok
        (.Ok
          { shared with
            toMachineState :=
              EvmYul.MachineState.mcopy shared.toMachineState
                writeStart readStart size }
          store,
        []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.ternaryMachineStateOp,
    EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.setMachineState]
  rfl

theorem primCall_origin_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .ORIGIN : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender)
          shared.executionEnv)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp
        ((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat ↑shared.executionEnv.sender])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_caller_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CALLER : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source)
          shared.executionEnv)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp
        ((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat ↑shared.executionEnv.source])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_callvalue_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CALLVALUE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.ExecutionEnv.weiValue shared.executionEnv]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp EvmYul.ExecutionEnv.weiValue
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.ExecutionEnv.weiValue shared.executionEnv])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_calldataload_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (offset : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CALLDATALOAD : EvmYul.Operation .Yul)) [offset] =
      .ok (.Ok shared store,
        [EvmYul.State.calldataload shared.toState offset]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp
        (fun s v => (s, EvmYul.State.calldataload s v))
        (.Ok shared store) [offset] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.calldataload shared.toState offset])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_calldatasize_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CALLDATASIZE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.calldata)
          shared.executionEnv)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp
        ((.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.calldata))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat shared.executionEnv.calldata.size])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_codesize_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CODESIZE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.codeBytes)
          shared.executionEnv)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp
        ((.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.codeBytes))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat shared.executionEnv.codeBytes.size])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_extcodesize_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (address : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .EXTCODESIZE : EvmYul.Operation .Yul)) [address] =
      .ok
        (.Ok { shared with
          toState := (EvmYul.State.extCodeSize shared.toState address).1 } store,
        [(EvmYul.State.extCodeSize shared.toState address).2]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp EvmYul.State.extCodeSize
        (.Ok shared store) [address] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := (EvmYul.State.extCodeSize shared.toState address).1 } store,
        [(EvmYul.State.extCodeSize shared.toState address).2])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_calldatacopy_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (memStart dataStart size : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CALLDATACOPY : EvmYul.Operation .Yul))
          [memStart, dataStart, size] =
      .ok
        (.Ok
          (EvmYul.SharedState.calldatacopy shared memStart dataStart size)
          store,
        []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.ternaryCopyOp, EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.setSharedState]
  rfl

theorem primCall_codecopy_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (memStart codeStart size : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .CODECOPY : EvmYul.Operation .Yul))
          [memStart, codeStart, size] =
      .ok
        (.Ok
          (EvmYul.SharedState.codeBytesCopy shared memStart codeStart size)
          store,
        []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.ternaryCopyOp, EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.setSharedState]
  rfl

theorem primCall_extcodecopy_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (address memStart codeStart size : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .EXTCODECOPY : EvmYul.Operation .Yul))
          [address, memStart, codeStart, size] =
      .ok
        (.Ok
          (EvmYul.SharedState.extCodeCopy' shared address memStart codeStart
            size)
          store,
        []) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  simp [EvmYul.Yul.quaternaryCopyOp, EvmYul.Yul.State.toSharedState,
    EvmYul.Yul.State.setSharedState]
  rfl

theorem primCall_extcodehash_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (address : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .EXTCODEHASH : EvmYul.Operation .Yul)) [address] =
      .ok
        (.Ok { shared with
          toState := (EvmYul.State.extCodeHash shared.toState address).1 } store,
        [(EvmYul.State.extCodeHash shared.toState address).2]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp EvmYul.State.extCodeHash
        (.Ok shared store) [address] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok
        (.Ok { shared with
          toState := (EvmYul.State.extCodeHash shared.toState address).1 } store,
        [(EvmYul.State.extCodeHash shared.toState address).2])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_returndatacopy_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (memStart dataStart size : Word)
    (hBounds : dataStart.toNat + size.toNat ≤ shared.returnData.size) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .RETURNDATACOPY : EvmYul.Operation .Yul))
          [memStart, dataStart, size] =
      .ok
        (.Ok
          { shared with
            toMachineState :=
              EvmYul.MachineState.returndatacopy shared.toMachineState
                memStart dataStart size }
          store,
        []) := by
    have hNotBounds :
        ¬ shared.returnData.size < dataStart.toNat + size.toNat := by
      omega
    simp [EvmYul.Yul.primCall]
    unfold EvmYul.step
    change
      (match
        (if shared.returnData.size < dataStart.toNat + size.toNat then
          Except.error EvmYul.Yul.Exception.InvalidMemoryAccess
        else
          Except.ok
            (EvmYul.Yul.State.Ok
              { shared with
                toMachineState :=
                  EvmYul.MachineState.returndatacopy shared.toMachineState
                    memStart dataStart size }
              store,
            (none : Option Word))) with
      | Except.ok (s, lit) => Except.ok (s, lit.toList)
      | Except.error e => Except.error e) =
        Except.ok
          (EvmYul.Yul.State.Ok
            { shared with
              toMachineState :=
                EvmYul.MachineState.returndatacopy shared.toMachineState
                  memStart dataStart size }
            store,
          [])
    simp [hNotBounds]

theorem primCall_gasprice_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .GASPRICE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ EvmYul.ExecutionEnv.gasPrice)
          shared.executionEnv)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp
        ((.ofNat ∘ EvmYul.ExecutionEnv.gasPrice))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat shared.executionEnv.gasPrice])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_prevrandao_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .PREVRANDAO : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store, [EvmYul.prevRandao shared.executionEnv]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp EvmYul.prevRandao
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.prevRandao shared.executionEnv])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_basefee_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .BASEFEE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store, [EvmYul.basefee shared.executionEnv]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp EvmYul.basefee
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store, [EvmYul.basefee shared.executionEnv])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_blobbasefee_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .BLOBBASEFEE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.ExecutionEnv.getBlobGasprice shared.executionEnv]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.executionEnvOp EvmYul.ExecutionEnv.getBlobGasprice
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.ExecutionEnv.getBlobGasprice shared.executionEnv])
  simp [EvmYul.Yul.executionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_coinbase_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .COINBASE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [((.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
          shared.toState)]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.stateOp
        ((.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase))
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.UInt256.ofNat ↑shared.toState.coinBase])
  simp [EvmYul.Yul.stateOp, EvmYul.Yul.State.toState]

theorem primCall_timestamp_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .TIMESTAMP : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.State.timeStamp shared.toState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.stateOp EvmYul.State.timeStamp
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.timeStamp shared.toState])
  simp [EvmYul.Yul.stateOp, EvmYul.Yul.State.toState]

theorem primCall_number_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .NUMBER : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.State.number shared.toState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.stateOp EvmYul.State.number
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.number shared.toState])
  simp [EvmYul.Yul.stateOp, EvmYul.Yul.State.toState]

theorem primCall_gaslimit_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .GASLIMIT : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.State.gasLimit shared.toState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.stateOp EvmYul.State.gasLimit
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.gasLimit shared.toState])
  simp [EvmYul.Yul.stateOp, EvmYul.Yul.State.toState]

theorem primCall_chainid_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .CHAINID : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.State.chainId shared.toState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.stateOp EvmYul.State.chainId
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.chainId shared.toState])
  simp [EvmYul.Yul.stateOp, EvmYul.Yul.State.toState]

theorem primCall_blockhash_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (blockNumber : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .BLOCKHASH : EvmYul.Operation .Yul)) [blockNumber] =
      .ok (.Ok shared store,
        [EvmYul.State.blockHash shared.toState blockNumber]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryStateOp
        (fun s v => (s, EvmYul.State.blockHash s v))
        (.Ok shared store) [blockNumber] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.blockHash shared.toState blockNumber])
  simp [EvmYul.Yul.unaryStateOp, EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

theorem primCall_selfbalance_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .SELFBALANCE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.State.selfbalance shared.toState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.stateOp EvmYul.State.selfbalance
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.State.selfbalance shared.toState])
  simp [EvmYul.Yul.stateOp, EvmYul.Yul.State.toState]

theorem primCall_blobhash_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (index : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Block .BLOBHASH : EvmYul.Operation .Yul)) [index] =
      .ok (.Ok shared store,
        [EvmYul.blobhash shared.executionEnv index]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.unaryExecutionEnvOp EvmYul.blobhash
        (.Ok shared store) [index] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.blobhash shared.executionEnv index])
  simp [EvmYul.Yul.unaryExecutionEnvOp, EvmYul.Yul.State.executionEnv]

theorem primCall_returndatasize_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.Env .RETURNDATASIZE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store,
        [EvmYul.MachineState.returndatasize shared.toMachineState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.machineStateOp EvmYul.MachineState.returndatasize
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.MachineState.returndatasize shared.toMachineState])
  simp [EvmYul.Yul.machineStateOp, EvmYul.Yul.State.toMachineState]

theorem primCall_msize_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store, [EvmYul.MachineState.msize shared.toMachineState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.machineStateOp EvmYul.MachineState.msize
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.MachineState.msize shared.toMachineState])
  simp [EvmYul.Yul.machineStateOp, EvmYul.Yul.State.toMachineState]

theorem primCall_gas_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) [] =
      .ok (.Ok shared store, [EvmYul.MachineState.gas shared.toMachineState]) := by
  simp [EvmYul.Yul.primCall]
  unfold EvmYul.step
  change
    (match
      EvmYul.Yul.machineStateOp EvmYul.MachineState.gas
        (.Ok shared store) [] with
    | Except.ok (s, lit) => Except.ok (s, lit.toList)
    | Except.error e => Except.error e) =
      Except.ok (.Ok shared store,
        [EvmYul.MachineState.gas shared.toMachineState])
  simp [EvmYul.Yul.machineStateOp, EvmYul.Yul.State.toMachineState]

/--
Target structured primitive semantics for the corresponding pure operations.
These are target-only stack facts, kept below the imported-reference bridge.
-/
theorem basicOp_step_iszero_of_stack
    (state : EVMState) (value : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = value :: stack) :
    Structured.BasicOp.step .iszero state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.isZero value :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execUnOp, EvmYul.Stack.pop, EvmYul.Stack.push, Id.run]

theorem basicOp_step_not_of_stack
    (state : EVMState) (value : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = value :: stack) :
    Structured.BasicOp.step .not state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.lnot value :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execUnOp, EvmYul.Stack.pop, EvmYul.Stack.push, Id.run]

theorem basicOp_step_add_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .add state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.add left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_mul_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .mul state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.mul left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_sub_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .sub state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.sub left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_div_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .div state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.div left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_sdiv_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .sdiv state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.sdiv left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_mod_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .mod state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.mod left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_smod_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .smod state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.smod left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_addmod_of_stack
    (state : EVMState) (left middle right : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: middle :: right :: stack) :
    Structured.BasicOp.step .addmod state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.addMod left middle right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execTriOp, EvmYul.Stack.pop3, EvmYul.Stack.push, Id.run]

theorem basicOp_step_mulmod_of_stack
    (state : EVMState) (left middle right : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: middle :: right :: stack) :
    Structured.BasicOp.step .mulmod state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.mulMod left middle right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execTriOp, EvmYul.Stack.pop3, EvmYul.Stack.push, Id.run]

theorem basicOp_step_exp_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .exp state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.exp left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_signextend_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .signextend state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.signextend left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_lt_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .lt state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.lt left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_gt_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .gt state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.gt left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_slt_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .slt state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.slt left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_sgt_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .sgt state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.sgt left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_eq_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .eq state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.eq left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_and_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .and state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.land left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_or_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .or state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.lor left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_xor_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .xor state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.xor left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_byte_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .byte state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.byteAt left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_shl_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .shl state =
      .ok (state.replaceStackAndIncrPC
        ((flip EvmYul.UInt256.shiftLeft) left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_shr_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .shr state =
      .ok (state.replaceStackAndIncrPC
        ((flip EvmYul.UInt256.shiftRight) left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_sar_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .sar state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.sar left right :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
        Assembly.Target.stepInstr, Assembly.PrimOp.step,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run]

theorem basicOp_step_address_of_stack
    (state : EVMState) (stack : EvmYul.Stack Word)
    (hStack : state.stack = stack) :
    Structured.BasicOp.step .address state =
      .ok (state.replaceStackAndIncrPC
        (((.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner)
          state.executionEnv) :: stack)) := by
  subst hStack
  simp [Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
    Assembly.Target.stepInstr, Assembly.PrimOp.step,
    Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
    EvmYul.EVM.executionEnvOp, EvmYul.Stack.push]
  rfl

theorem basicOp_step_executionEnv_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.ExecutionEnv .EVM → Word)
    (hStep : op.toPrimOp.continuingStep? =
      some (.executionEnv f))
    (state : EVMState) (stack : EvmYul.Stack Word)
    (hStack : state.stack = stack) :
    Structured.BasicOp.step op state =
      .ok (state.replaceStackAndIncrPC (f state.executionEnv :: stack)) := by
  subst hStack
  simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
    Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
    EvmYul.EVM.executionEnvOp, EvmYul.Stack.push]
  rfl

theorem basicOp_step_unaryExecutionEnv_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.ExecutionEnv .EVM → Word → Word)
    (hStep : op.toPrimOp.continuingStep? = some (.unaryExecutionEnv f))
    (state : EVMState) (value : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = value :: stack) :
    Structured.BasicOp.step op state =
      .ok (state.replaceStackAndIncrPC
        (f state.executionEnv value :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
        EvmYul.EVM.unaryExecutionEnvOp, EvmYul.Stack.pop,
        EvmYul.Stack.push]
      rfl

theorem basicOp_step_unaryState_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word)
    (hStep : op.toPrimOp.continuingStep? = some (.unaryState f))
    (state : EVMState) (value : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = value :: stack) :
    Structured.BasicOp.step op state =
      .ok
        ({ state with toState := (f state.toState value).1 }
          |>.replaceStackAndIncrPC ((f state.toState value).2 :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
        EvmYul.EVM.unaryStateOp, EvmYul.Stack.pop,
        EvmYul.Stack.push]
      rfl

theorem basicOp_step_pop_of_stack
    (state : EVMState) (value : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = value :: stack) :
    Structured.BasicOp.step .pop state =
      .ok (state.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run, EvmYul.Stack.pop]
      rfl

theorem basicOp_step_mload_of_stack
    (state : EVMState) (slot : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = slot :: stack) :
    Structured.BasicOp.step .mload state =
      .ok
        ({ state with
          toMachineState :=
            (EvmYul.MachineState.mload state.toMachineState slot).2 }
          |>.replaceStackAndIncrPC
            ((EvmYul.MachineState.mload state.toMachineState slot).1 ::
              stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run,
        EvmYul.Stack.pop, EvmYul.Stack.push]
      rfl

theorem basicOp_step_mstore_of_stack
    (state : EVMState) (slot value : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = slot :: value :: stack) :
    Structured.BasicOp.step .mstore state =
      .ok
        ({ state with
          toMachineState :=
            EvmYul.MachineState.mstore state.toMachineState slot value }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run, EvmYul.Stack.pop2]
      rfl

theorem basicOp_step_binaryState_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.State .EVM → Word → Word → EvmYul.State .EVM)
    (hStep : op.toPrimOp.continuingStep? = some (.binaryState f))
    (state : EVMState) (left right : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step op state =
      .ok
        ({ state with toState := f state.toState left right }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
        EvmYul.EVM.binaryStateOp, EvmYul.Stack.pop2]
      rfl

theorem basicOp_step_sstore_of_stack
    (state : EVMState) (slot value : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = slot :: value :: stack) :
    Structured.BasicOp.step .sstore state =
      .ok
        ({ state with
          toState :=
            EvmYul.State.sstore state.toState slot value }
          |>.replaceStackAndIncrPC stack) := by
  exact
    basicOp_step_binaryState_of_stack
      .sstore EvmYul.State.sstore
      (by simp [Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?])
      state slot value stack hStack

theorem basicOp_step_tstore_of_stack
    (state : EVMState) (slot value : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = slot :: value :: stack) :
    Structured.BasicOp.step .tstore state =
      .ok
        ({ state with
          toState :=
            EvmYul.State.tstore state.toState slot value }
          |>.replaceStackAndIncrPC stack) := by
  exact
    basicOp_step_binaryState_of_stack
      .tstore EvmYul.State.tstore
      (by simp [Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?])
      state slot value stack hStack

theorem basicOp_step_log0_of_stack
    (state : EVMState) (offset size : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = offset :: size :: stack) :
    Structured.BasicOp.step .log0 state =
      .ok
        ({ state with
          toSharedState :=
            EvmYul.SharedState.logOp offset size #[]
              state.toSharedState }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run,
        EvmYul.Stack.pop2]
      rfl

theorem basicOp_step_log1_of_stack
    (state : EVMState) (offset size topic : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = offset :: size :: topic :: stack) :
    Structured.BasicOp.step .log1 state =
      .ok
        ({ state with
          toSharedState :=
            EvmYul.SharedState.logOp offset size #[topic]
              state.toSharedState }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run,
        EvmYul.Stack.pop3]
      rfl

theorem basicOp_step_log2_of_stack
    (state : EVMState) (offset size topic0 topic1 : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = offset :: size :: topic0 :: topic1 :: stack) :
    Structured.BasicOp.step .log2 state =
      .ok
        ({ state with
          toSharedState :=
            EvmYul.SharedState.logOp offset size #[topic0, topic1]
              state.toSharedState }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run,
        EvmYul.Stack.pop4]
      rfl

theorem basicOp_step_mstore8_of_stack
    (state : EVMState) (slot value : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = slot :: value :: stack) :
    Structured.BasicOp.step .mstore8 state =
      .ok
        ({ state with
          toMachineState :=
            EvmYul.MachineState.mstore8 state.toMachineState slot value }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run, EvmYul.Stack.pop2]
      rfl

theorem basicOp_step_keccak256_of_stack
    (state : EVMState) (start size : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = start :: size :: stack) :
    Structured.BasicOp.step .keccak256 state =
      .ok
        ({ state with
          toMachineState :=
            (EvmYul.MachineState.keccak256 state.toMachineState
              start size).2 }
          |>.replaceStackAndIncrPC
            ((EvmYul.MachineState.keccak256 state.toMachineState
              start size).1 :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, Assembly.PrimStep.run,
        EvmYul.EVM.binaryMachineStateOp',
        EvmYul.Stack.pop2, EvmYul.Stack.push]
      rfl

theorem basicOp_step_ternaryCopy_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.SharedState .EVM → Word → Word → Word →
      EvmYul.SharedState .EVM)
    (hStep : op.toPrimOp.continuingStep? = some (.ternaryCopy f))
    (state : EVMState) (left middle right : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: middle :: right :: stack) :
    Structured.BasicOp.step op state =
      .ok
        ({ state with
          toSharedState :=
            f state.toSharedState left middle right }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
        EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3]
      rfl

theorem basicOp_step_ternaryMachineState_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.MachineState → Word → Word → Word →
      EvmYul.MachineState)
    (hStep : op.toPrimOp.continuingStep? = some (.ternaryMachineState f))
    (state : EVMState) (left middle right : Word)
    (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: middle :: right :: stack) :
    Structured.BasicOp.step op state =
      .ok
        ({ state with
          toMachineState :=
            f state.toMachineState left middle right }
          |>.replaceStackAndIncrPC stack) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
        EvmYul.EVM.ternaryMachineStateOp, EvmYul.Stack.pop3]
      rfl

theorem basicOp_step_returndatacopy_of_stack
      (state : EVMState) (memStart dataStart size : Word)
      (stack : EvmYul.Stack Word)
      (hStack : state.stack = memStart :: dataStart :: size :: stack)
      (hBounds : dataStart.toNat + size.toNat ≤ state.returnData.size) :
      Structured.BasicOp.step .returndatacopy state =
      .ok
        ({ state with
          toMachineState :=
            EvmYul.MachineState.returndatacopy state.toMachineState
              memStart dataStart size }
          |>.replaceStackAndIncrPC stack) := by
    cases state with
    | mk shared pc stack0 execLength =>
        simp at hStack hBounds
        subst stack0
        have hNotBounds :
            ¬ shared.returnData.size < dataStart.toNat + size.toNat := by
          omega
        simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
          Assembly.PrimOp.step, Assembly.PrimStep.run, EvmYul.Stack.pop3,
          hNotBounds]
        rfl

theorem basicOp_step_state_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.State .EVM → Word)
    (hStep : op.toPrimOp.continuingStep? = some (.state f))
    (state : EVMState) (stack : EvmYul.Stack Word)
    (hStack : state.stack = stack) :
    Structured.BasicOp.step op state =
      .ok (state.replaceStackAndIncrPC (f state.toState :: stack)) := by
  subst hStack
  simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
    Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
    EvmYul.EVM.stateOp, EvmYul.Stack.push]
  rfl

theorem basicOp_step_machineState_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.MachineState → Word)
    (hStep : op.toPrimOp.continuingStep? = some (.machineState f))
    (state : EVMState) (stack : EvmYul.Stack Word)
    (hStack : state.stack = stack) :
    Structured.BasicOp.step op state =
      .ok (state.replaceStackAndIncrPC (f state.toMachineState :: stack)) := by
  subst hStack
  simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
    Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
    EvmYul.EVM.machineStateOp, EvmYul.Stack.push]
  rfl

theorem basicOp_step_unaryState_same_of_stack
    (op : Structured.BasicOp)
    (f : EvmYul.State .EVM → Word → Word)
    (hStep :
      op.toPrimOp.continuingStep? =
        some (.unaryState (fun state value => (state, f state value))))
    (state : EVMState) (value : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = value :: stack) :
    Structured.BasicOp.step op state =
      .ok (state.replaceStackAndIncrPC (f state.toState value :: stack)) := by
  cases state with
  | mk shared pc stack0 execLength =>
      simp at hStack
      subst stack0
      simp [Structured.BasicOp.step, Assembly.Target.stepInstr,
        Assembly.PrimOp.step, hStep, Assembly.PrimStep.run,
        EvmYul.EVM.unaryStateOp, EvmYul.Stack.pop,
        EvmYul.Stack.push]
      rfl

end PrimSemantics

end Yul
end EvmCompiler
