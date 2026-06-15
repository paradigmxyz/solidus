import EvmCompiler.Yul.EffectSemanticsOwner
import EvmCompiler.Yul.Primitive
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul
namespace Prim

/-!
Active-owner preservation for ordinary compiler-selected Yul primitives.
External call/create operations are excluded by the same classifier used by
the compiler and memory-safety contract.
-/

private theorem wrappedStep_preserves
    {result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × Option Assembly.Word)}
    {initial final : EvmYul.Yul.State}
    {values : List Assembly.Word}
    (hPreserves :
      ∀ {resultState : EvmYul.Yul.State}
        {value : Option Assembly.Word},
        result = Except.ok (resultState, value) →
        Source.Effectful.ActiveOwnerAvailable initial →
        Source.Effectful.ActiveOwnerAvailable resultState)
    (hOwner : Source.Effectful.ActiveOwnerAvailable initial)
    (hRun :
      (match result with
        | Except.ok (state, value) =>
            Except.ok (state, value.toList)
        | Except.error err => Except.error err) =
          Except.ok (final, values)) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases hResult : result with
  | error err =>
      simp [hResult] at hRun
  | ok result =>
      rcases result with ⟨resultState, value⟩
      simp [hResult] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hPreserves hResult hOwner

private theorem execUnOp_preserves
    (op : EvmYul.Primop.Unary)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.execUnOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.execUnOp] at hRun
  | cons first rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.execUnOp] at hRun
          exact hRun.1 ▸ hOwner
      | cons second rest => simp [EvmYul.Yul.execUnOp] at hRun

private theorem execBinOp_preserves
    (op : EvmYul.Primop.Binary)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.execBinOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.execBinOp] at hRun
  | cons first rest =>
      cases rest with
      | nil => simp [EvmYul.Yul.execBinOp] at hRun
      | cons second rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.execBinOp] at hRun
              exact hRun.1 ▸ hOwner
          | cons third rest => simp [EvmYul.Yul.execBinOp] at hRun

private theorem execTriOp_preserves
    (op : EvmYul.Primop.Ternary)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.execTriOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.execTriOp] at hRun
  | cons first rest =>
      cases rest with
      | nil => simp [EvmYul.Yul.execTriOp] at hRun
      | cons second rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.execTriOp] at hRun
          | cons third rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.execTriOp] at hRun
                  exact hRun.1 ▸ hOwner
              | cons fourth rest => simp [EvmYul.Yul.execTriOp] at hRun

private theorem executionEnvOp_preserves
    (op : EvmYul.ExecutionEnv .Yul → EvmYul.UInt256)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.executionEnvOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  simp [EvmYul.Yul.executionEnvOp] at hRun
  exact hRun.1 ▸ hOwner

private theorem unaryExecutionEnvOp_preserves
    (op : EvmYul.ExecutionEnv .Yul → EvmYul.UInt256 → EvmYul.UInt256)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.unaryExecutionEnvOp op state args =
        .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
  | cons first rest =>
      cases rest with
      | nil =>
          simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
          exact hRun.1 ▸ hOwner
      | cons second rest =>
          simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun

private theorem machineStateOp_preserves
    (op : EvmYul.MachineState → EvmYul.UInt256)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.machineStateOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  simp [EvmYul.Yul.machineStateOp] at hRun
  exact hRun.1 ▸ hOwner

private theorem stateOp_preserves
    (op : EvmYul.State .Yul → EvmYul.UInt256)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.stateOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  simp [EvmYul.Yul.stateOp] at hRun
  exact hRun.1 ▸ hOwner

private theorem binaryMachineStateOp_preserves
    (op :
      EvmYul.MachineState → EvmYul.UInt256 → EvmYul.UInt256 →
        EvmYul.MachineState)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.binaryMachineStateOp op state args =
        .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.binaryMachineStateOp] at hRun
  | cons first rest =>
      cases rest with
      | nil => simp [EvmYul.Yul.binaryMachineStateOp] at hRun
      | cons second rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp] at hRun
              rw [← hRun.1]
              simpa using hOwner
          | cons third rest =>
              simp [EvmYul.Yul.binaryMachineStateOp] at hRun

private theorem ternaryMachineStateOp_preserves
    (op :
      EvmYul.MachineState → EvmYul.UInt256 → EvmYul.UInt256 →
        EvmYul.UInt256 → EvmYul.MachineState)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.ternaryMachineStateOp op state args =
        .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
  | cons first rest =>
      cases rest with
      | nil => simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
      | cons second rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
          | cons third rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
                  rw [← hRun.1]
                  simpa using hOwner
              | cons fourth rest =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at hRun

private def StateHasOwner (state : EvmYul.State .Yul) : Prop :=
  ∃ account,
    state.accountMap.find? state.executionEnv.codeOwner = some account

private def SharedHasOwner (state : EvmYul.SharedState .Yul) : Prop :=
  ∃ account,
    state.accountMap.find? state.executionEnv.codeOwner = some account

private theorem activeOwnerAvailable_ok_iff
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    Source.Effectful.ActiveOwnerAvailable (.Ok shared store) ↔
      SharedHasOwner shared := by
  simp [Source.Effectful.ActiveOwnerAvailable,
    Source.Effectful.activeShared?, SharedHasOwner]

private theorem sharedHasOwner_iff_stateHasOwner
    (shared : EvmYul.SharedState .Yul) :
    SharedHasOwner shared ↔ StateHasOwner shared.toState := by
  rfl

private theorem binaryMachineStateOp'_preserves
    (op :
      EvmYul.MachineState → EvmYul.UInt256 → EvmYul.UInt256 →
        EvmYul.UInt256 × EvmYul.MachineState)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.binaryMachineStateOp' op state args =
        .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases args with
  | nil => simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
  | cons first rest =>
      cases rest with
      | nil => simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
      | cons second rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
              rw [← hRun.1]
              simpa using hOwner
          | cons third rest =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at hRun

private theorem unaryStateOp_preserves
    (op :
      EvmYul.State .Yul → EvmYul.UInt256 →
        EvmYul.State .Yul × EvmYul.UInt256)
    (hOp :
      ∀ world value,
        StateHasOwner world → StateHasOwner (op world value).1)
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.unaryStateOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases state with
  | OutOfFuel =>
      simp [Source.Effectful.ActiveOwnerAvailable,
        Source.Effectful.activeShared?] at hOwner
  | Checkpoint jump =>
      cases args with
      | nil => simp [EvmYul.Yul.unaryStateOp] at hRun
      | cons first rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.unaryStateOp] at hRun
              exact hRun.1 ▸ hOwner
          | cons second rest => simp [EvmYul.Yul.unaryStateOp] at hRun
  | Ok shared store =>
      cases args with
      | nil => simp [EvmYul.Yul.unaryStateOp] at hRun
      | cons first rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.unaryStateOp] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              have hStateOwner :
                  StateHasOwner shared.toState :=
                (sharedHasOwner_iff_stateHasOwner shared).mp
                  ((activeOwnerAvailable_ok_iff shared store).mp hOwner)
              have hResultOwner :=
                hOp shared.toState first hStateOwner
              rcases hResultOwner with ⟨account, hLookup⟩
              exact
                ⟨{ shared with
                    toState := (op shared.toState first).1 },
                  account, rfl, hLookup⟩
          | cons second rest => simp [EvmYul.Yul.unaryStateOp] at hRun

private theorem binaryStateOp_preserves
    (op :
      EvmYul.State .Yul → EvmYul.UInt256 → EvmYul.UInt256 →
        EvmYul.State .Yul)
    (hOp :
      ∀ world left right,
        StateHasOwner world → StateHasOwner (op world left right))
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.binaryStateOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases state with
  | OutOfFuel =>
      simp [Source.Effectful.ActiveOwnerAvailable,
        Source.Effectful.activeShared?] at hOwner
  | Checkpoint jump =>
      cases args with
      | nil => simp [EvmYul.Yul.binaryStateOp] at hRun
      | cons first rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.binaryStateOp] at hRun
          | cons second rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.binaryStateOp] at hRun
                  exact hRun.1 ▸ hOwner
              | cons third rest =>
                  simp [EvmYul.Yul.binaryStateOp] at hRun
  | Ok shared store =>
      cases args with
      | nil => simp [EvmYul.Yul.binaryStateOp] at hRun
      | cons first rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.binaryStateOp] at hRun
          | cons second rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.binaryStateOp] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hStateOwner :
                      StateHasOwner shared.toState :=
                    (sharedHasOwner_iff_stateHasOwner shared).mp
                      ((activeOwnerAvailable_ok_iff shared store).mp hOwner)
                  have hResultOwner :=
                    hOp shared.toState first second hStateOwner
                  rcases hResultOwner with ⟨account, hLookup⟩
                  exact
                    ⟨{ shared with
                        toState := op shared.toState first second },
                      account, rfl, hLookup⟩
              | cons third rest =>
                  simp [EvmYul.Yul.binaryStateOp] at hRun

private theorem ternaryCopyOp_preserves
    (op :
      EvmYul.SharedState .Yul → EvmYul.UInt256 → EvmYul.UInt256 →
        EvmYul.UInt256 → EvmYul.SharedState .Yul)
    (hOp :
      ∀ shared first second third,
        SharedHasOwner shared →
          SharedHasOwner (op shared first second third))
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.ternaryCopyOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases state with
  | OutOfFuel =>
      simp [Source.Effectful.ActiveOwnerAvailable,
        Source.Effectful.activeShared?] at hOwner
  | Checkpoint jump =>
      cases args with
      | nil => simp [EvmYul.Yul.ternaryCopyOp] at hRun
      | cons first rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.ternaryCopyOp] at hRun
          | cons second rest =>
              cases rest with
              | nil => simp [EvmYul.Yul.ternaryCopyOp] at hRun
              | cons third rest =>
                  cases rest with
                  | nil =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hRun
                      exact hRun.1 ▸ hOwner
                  | cons fourth rest =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hRun
  | Ok shared store =>
      cases args with
      | nil => simp [EvmYul.Yul.ternaryCopyOp] at hRun
      | cons first rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.ternaryCopyOp] at hRun
          | cons second rest =>
              cases rest with
              | nil => simp [EvmYul.Yul.ternaryCopyOp] at hRun
              | cons third rest =>
                  cases rest with
                  | nil =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      have hSharedOwner : SharedHasOwner shared :=
                        (activeOwnerAvailable_ok_iff shared store).mp hOwner
                      have hResultOwner :=
                        hOp shared first second third hSharedOwner
                      rcases hResultOwner with ⟨account, hLookup⟩
                      exact
                        ⟨op shared first second third, account, rfl,
                          hLookup⟩
                  | cons fourth rest =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hRun

private theorem quaternaryCopyOp_preserves
    (op :
      EvmYul.SharedState .Yul → EvmYul.UInt256 → EvmYul.UInt256 →
        EvmYul.UInt256 → EvmYul.UInt256 → EvmYul.SharedState .Yul)
    (hOp :
      ∀ shared first second third fourth,
        SharedHasOwner shared →
          SharedHasOwner (op shared first second third fourth))
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun :
      EvmYul.Yul.quaternaryCopyOp op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  cases state with
  | OutOfFuel =>
      simp [Source.Effectful.ActiveOwnerAvailable,
        Source.Effectful.activeShared?] at hOwner
  | Checkpoint jump =>
      cases args with
      | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
      | cons first rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
          | cons second rest =>
              cases rest with
              | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
              | cons third rest =>
                  cases rest with
                  | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
                  | cons fourth rest =>
                      cases rest with
                      | nil =>
                          simp [EvmYul.Yul.quaternaryCopyOp] at hRun
                          exact hRun.1 ▸ hOwner
                      | cons fifth rest =>
                          simp [EvmYul.Yul.quaternaryCopyOp] at hRun
  | Ok shared store =>
      cases args with
      | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
      | cons first rest =>
          cases rest with
          | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
          | cons second rest =>
              cases rest with
              | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
              | cons third rest =>
                  cases rest with
                  | nil => simp [EvmYul.Yul.quaternaryCopyOp] at hRun
                  | cons fourth rest =>
                      cases rest with
                      | nil =>
                          simp [EvmYul.Yul.quaternaryCopyOp] at hRun
                          rcases hRun with ⟨rfl, rfl⟩
                          have hSharedOwner : SharedHasOwner shared :=
                            (activeOwnerAvailable_ok_iff shared store).mp hOwner
                          have hResultOwner :=
                            hOp shared first second third fourth hSharedOwner
                          rcases hResultOwner with ⟨account, hLookup⟩
                          exact
                            ⟨op shared first second third fourth, account,
                              rfl, hLookup⟩
                      | cons fifth rest =>
                          simp [EvmYul.Yul.quaternaryCopyOp] at hRun

private theorem sharedCopy_preserves_owner
    (op :
      EvmYul.SharedState .Yul → EvmYul.SharedState .Yul)
    (hAccountMap : ∀ shared, (op shared).accountMap = shared.accountMap)
    (hCodeOwner :
      ∀ shared,
        (op shared).executionEnv.codeOwner =
          shared.executionEnv.codeOwner)
    (shared : EvmYul.SharedState .Yul) :
    SharedHasOwner shared → SharedHasOwner (op shared) := by
  rintro ⟨account, hLookup⟩
  exact ⟨account, by simpa [hAccountMap shared, hCodeOwner shared]⟩

private theorem stateRead_preserves_owner
    (op : EvmYul.State .Yul → EvmYul.State .Yul)
    (hAccountMap : ∀ world, (op world).accountMap = world.accountMap)
    (hCodeOwner :
      ∀ world,
        (op world).executionEnv.codeOwner =
          world.executionEnv.codeOwner)
    (world : EvmYul.State .Yul) :
    StateHasOwner world → StateHasOwner (op world) := by
  rintro ⟨account, hLookup⟩
  exact ⟨account, by simpa [hAccountMap world, hCodeOwner world]⟩

private theorem tstore_preserves_owner
    (world : EvmYul.State .Yul) (position value : EvmYul.UInt256) :
    StateHasOwner world →
      StateHasOwner (world.tstore position value) := by
  rintro ⟨account, hLookup⟩
  refine ⟨account.updateTransientStorage position value, ?_⟩
  simp [EvmYul.State.tstore, EvmYul.State.lookupAccount, hLookup,
    Option.option, EvmYul.State.updateAccount,
    Batteries.RBMap.find?_insert]

private theorem sstore_preserves_owner
    (world : EvmYul.State .Yul) (position value : EvmYul.UInt256) :
    StateHasOwner world →
      StateHasOwner (world.sstore position value) := by
  rintro ⟨account, hLookup⟩
  unfold EvmYul.State.sstore
  simp [EvmYul.State.lookupAccount, hLookup, Option.option,
    Batteries.RBMap.find!,
    EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
    Batteries.RBMap.find?_insert, StateHasOwner]

private theorem balance_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world → StateHasOwner (world.balance value).1 := by
  apply stateRead_preserves_owner
    (fun current => (current.balance value).1)
  · intro current
    rfl
  · intro current
    rfl

private theorem calldataload_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world →
      StateHasOwner (world, world.calldataload value).1 :=
  id

private theorem extCodeSize_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world → StateHasOwner (world.extCodeSize value).1 := by
  apply stateRead_preserves_owner
    (fun current => (current.extCodeSize value).1)
  · intro current
    rfl
  · intro current
    rfl

private theorem extCodeHash_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world → StateHasOwner (world.extCodeHash value).1 := by
  apply stateRead_preserves_owner
    (fun current => (current.extCodeHash value).1)
  · intro current
    simp only [EvmYul.State.extCodeHash]
    split <;> rfl
  · intro current
    simp only [EvmYul.State.extCodeHash]
    split <;> rfl

private theorem blockHash_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world →
      StateHasOwner (world, world.blockHash value).1 :=
  id

private theorem sload_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world → StateHasOwner (world.sload value).1 := by
  apply stateRead_preserves_owner
    (fun current => (current.sload value).1)
  · intro current
    rfl
  · intro current
    rfl

private theorem tload_preserves_owner
    (world : EvmYul.State .Yul) (value : EvmYul.UInt256) :
    StateHasOwner world → StateHasOwner (world.tload value).1 :=
  id

private theorem calldatacopy_preserves_owner
    (shared : EvmYul.SharedState .Yul)
    (first second third : EvmYul.UInt256) :
    SharedHasOwner shared →
      SharedHasOwner (shared.calldatacopy first second third) := by
  apply sharedCopy_preserves_owner
    (fun current => current.calldatacopy first second third)
  · intro current
    rfl
  · intro current
    rfl

private theorem codeBytesCopy_preserves_owner
    (shared : EvmYul.SharedState .Yul)
    (first second third : EvmYul.UInt256) :
    SharedHasOwner shared →
      SharedHasOwner (shared.codeBytesCopy first second third) := by
  apply sharedCopy_preserves_owner
    (fun current => current.codeBytesCopy first second third)
  · intro current
    rfl
  · intro current
    rfl

private theorem extCodeCopy_preserves_owner
    (shared : EvmYul.SharedState .Yul)
    (first second third fourth : EvmYul.UInt256) :
    SharedHasOwner shared →
      SharedHasOwner (shared.extCodeCopy' first second third fourth) := by
  apply sharedCopy_preserves_owner
    (fun current => current.extCodeCopy' first second third fourth)
  · intro current
    rfl
  · intro current
    rfl

private theorem logUpdate_preserves_owner
    (state : EvmYul.Yul.State) (start size : EvmYul.UInt256)
    (topics : Array EvmYul.UInt256) :
    Source.Effectful.ActiveOwnerAvailable state →
      Source.Effectful.ActiveOwnerAvailable
        (state.setSharedState
          (EvmYul.SharedState.logOp start size topics
            state.toSharedState)) := by
  intro hOwner
  cases state with
  | OutOfFuel =>
      simpa [Source.Effectful.ActiveOwnerAvailable,
        Source.Effectful.activeShared?] using hOwner
  | Checkpoint jump =>
      simpa [EvmYul.Yul.State.setSharedState] using hOwner
  | Ok shared store =>
      rcases (activeOwnerAvailable_ok_iff shared store).mp hOwner with
        ⟨account, hLookup⟩
      exact
        ⟨EvmYul.SharedState.logOp start size topics shared, account,
          rfl, by
            simpa [EvmYul.SharedState.logOp] using hLookup⟩

private theorem log0Op_preserves
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.log0Op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  unfold EvmYul.Yul.log0Op at hRun
  split at hRun
  · rename_i lits first second
    simp at hRun
    change
      (state.setSharedState
          (EvmYul.SharedState.logOp first second #[] state.toSharedState),
        none) =
        (final, value) at hRun
    have hFinal :
        state.setSharedState
            (EvmYul.SharedState.logOp first second #[] state.toSharedState) =
          final := by
      simpa using congrArg Prod.fst hRun
    rw [← hFinal]
    exact logUpdate_preserves_owner state first second #[] hOwner
  · simp at hRun
    exact hRun.1 ▸ hOwner

private theorem log1Op_preserves
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.log1Op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  unfold EvmYul.Yul.log1Op at hRun
  split at hRun
  · rename_i lits first second topic
    simp at hRun
    change
      (state.setSharedState
          (EvmYul.SharedState.logOp first second #[topic]
            state.toSharedState), none) =
        (final, value) at hRun
    have hFinal :
        state.setSharedState
            (EvmYul.SharedState.logOp first second #[topic]
              state.toSharedState) =
          final := by
      simpa using congrArg Prod.fst hRun
    rw [← hFinal]
    exact logUpdate_preserves_owner state first second #[topic] hOwner
  · simp at hRun
    exact hRun.1 ▸ hOwner

private theorem log2Op_preserves
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.log2Op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  unfold EvmYul.Yul.log2Op at hRun
  split at hRun
  · rename_i lits first second topic₁ topic₂
    simp at hRun
    change
      (state.setSharedState
          (EvmYul.SharedState.logOp first second #[topic₁, topic₂]
            state.toSharedState), none) =
        (final, value) at hRun
    have hFinal :
        state.setSharedState
            (EvmYul.SharedState.logOp first second #[topic₁, topic₂]
              state.toSharedState) =
          final := by
      simpa using congrArg Prod.fst hRun
    rw [← hFinal]
    exact
      logUpdate_preserves_owner state first second #[topic₁, topic₂]
        hOwner
  · simp at hRun
    exact hRun.1 ▸ hOwner

private theorem log3Op_preserves
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.log3Op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  unfold EvmYul.Yul.log3Op at hRun
  split at hRun
  · rename_i lits first second topic₁ topic₂ topic₃
    simp at hRun
    change
      (state.setSharedState
          (EvmYul.SharedState.logOp first second
            #[topic₁, topic₂, topic₃] state.toSharedState), none) =
        (final, value) at hRun
    have hFinal :
        state.setSharedState
            (EvmYul.SharedState.logOp first second
              #[topic₁, topic₂, topic₃]
              state.toSharedState) =
          final := by
      simpa using congrArg Prod.fst hRun
    rw [← hFinal]
    exact
      logUpdate_preserves_owner state first second
        #[topic₁, topic₂, topic₃] hOwner
  · simp at hRun
    exact hRun.1 ▸ hOwner

private theorem log4Op_preserves
    {state final : EvmYul.Yul.State}
    {args : List Assembly.Word} {value : Option Assembly.Word}
    (hRun : EvmYul.Yul.log4Op state args = .ok (final, value))
    (hOwner : Source.Effectful.ActiveOwnerAvailable state) :
    Source.Effectful.ActiveOwnerAvailable final := by
  unfold EvmYul.Yul.log4Op at hRun
  split at hRun
  · rename_i lits first second topic₁ topic₂ topic₃ topic₄
    simp at hRun
    change
      (state.setSharedState
          (EvmYul.SharedState.logOp first second
            #[topic₁, topic₂, topic₃, topic₄] state.toSharedState), none) =
        (final, value) at hRun
    have hFinal :
        state.setSharedState
            (EvmYul.SharedState.logOp first second
              #[topic₁, topic₂, topic₃, topic₄] state.toSharedState) =
          final := by
      simpa using congrArg Prod.fst hRun
    rw [← hFinal]
    exact
      logUpdate_preserves_owner state first second
        #[topic₁, topic₂, topic₃, topic₄] hOwner
  · simp at hRun
    exact hRun.1 ▸ hOwner

theorem primCall_preserves_activeOwner_of_nonExternal
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hOp : toUncheckedBasicOp? prim = some op)
    (hNonExternal : op.toPrimOp.isExternalCallCreate = false)
    {fuel : Nat} {state final : EvmYul.Yul.State}
    {args values : List Assembly.Word}
    (hOwner : Source.Effectful.ActiveOwnerAvailable state)
    (hRun :
      EvmYul.Yul.primCall fuel state prim args = .ok (final, values)) :
    Source.Effectful.ActiveOwnerAvailable final := by
  by_cases hStatic :
      ¬state.executionEnv.perm ∧
        prim ∈
          [(.System .CREATE : EvmYul.Operation .Yul),
            .System .CREATE2, .StackMemFlow .SSTORE,
            .System .SELFDESTRUCT, .Log .LOG0, .Log .LOG1, .Log .LOG2,
            .Log .LOG3, .Log .LOG4, .StackMemFlow .TSTORE]
  · cases fuel with
    | zero =>
        simp [EvmYul.Yul.primCall] at hRun
    | succ fuel =>
        unfold EvmYul.Yul.primCall at hRun
        rw [if_pos hStatic] at hRun
        change
          (Except.error EvmYul.Yul.Exception.StaticModeViolation :
              Except EvmYul.Yul.Exception
                (EvmYul.Yul.State × List Assembly.Word)) =
            Except.ok (final, values) at hRun
        contradiction
  · cases prim <;> rename_i primitive <;> cases primitive
    all_goals
      simp [toUncheckedBasicOp?, toBasicOp?] at hOp
    all_goals
      subst op
    all_goals
      simp [Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.isExternalCallCreate] at hNonExternal
    all_goals
      cases fuel with
      | zero =>
          simp only [EvmYul.Yul.primCall] at hRun
          contradiction
      | succ fuel =>
          unfold EvmYul.Yul.primCall at hRun
          rw [if_neg hStatic] at hRun
          unfold EvmYul.step at hRun
          simp only [Id.run] at hRun
          simp only [pure_bind] at hRun
          first
          | change
              (match EvmYul.Yul.execUnOp _ state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves (execUnOp_preserves _) hOwner hRun
          | change
              (match EvmYul.Yul.execBinOp _ state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves (execBinOp_preserves _) hOwner hRun
          | change
              (match EvmYul.Yul.execTriOp _ state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves (execTriOp_preserves _) hOwner hRun
          | change
              (match
                  EvmYul.Yul.executionEnvOp (fun env => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            simp [EvmYul.Yul.executionEnvOp] at hRun
            exact hRun.1 ▸ hOwner
          | change
              (match
                  EvmYul.Yul.unaryExecutionEnvOp
                    (fun env value => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            cases args with
            | nil => simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
            | cons first rest =>
                cases rest with
                | nil =>
                    simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
                    exact hRun.1 ▸ hOwner
                | cons second rest =>
                    simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
          | change
              (match
                  EvmYul.Yul.machineStateOp (fun machine => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            simp [EvmYul.Yul.machineStateOp] at hRun
            exact hRun.1 ▸ hOwner
          | change
              (match EvmYul.Yul.stateOp (fun world => _) state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            simp [EvmYul.Yul.stateOp] at hRun
            exact hRun.1 ▸ hOwner
          | change
              (match
                  EvmYul.Yul.binaryMachineStateOp
                    (fun machine left right => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves (binaryMachineStateOp_preserves _) hOwner
                hRun
          | change
              (match
                  EvmYul.Yul.binaryMachineStateOp'
                    (fun machine left right => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.binaryMachineStateOp'
                    (fun machine left right => _) state args)
                (binaryMachineStateOp'_preserves _) hOwner hRun
          | change
              (match
                  EvmYul.Yul.unaryStateOp
                    (fun world value => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            apply
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp
                    (fun world value => _) state args)
                ?_ hOwner hRun
            apply unaryStateOp_preserves _ ?_
            intro world value hWorld
            rcases hWorld with ⟨account, hLookup⟩
            refine ⟨account, ?_⟩
            simpa [EvmYul.State.balance, EvmYul.State.extCodeSize,
              EvmYul.State.extCodeHash, EvmYul.State.sload,
              EvmYul.State.tload, EvmYul.State.addAccessedAccount,
              EvmYul.State.addAccessedStorageKey] using hLookup
          | change
              (match
                  EvmYul.Yul.binaryStateOp
                    (fun world left right => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            apply
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.binaryStateOp
                    (fun world left right => _) state args)
                ?_ hOwner hRun
            apply binaryStateOp_preserves _ ?_
            intro world left right
            first
            | exact sstore_preserves_owner world left right
            | exact tstore_preserves_owner world left right
          | change
              (match
                  EvmYul.Yul.ternaryCopyOp
                    (fun shared first second third => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            apply
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.ternaryCopyOp
                    (fun shared first second third => _) state args)
                ?_ hOwner hRun
            apply ternaryCopyOp_preserves _ ?_
            intro shared first second third hShared
            rcases hShared with ⟨account, hLookup⟩
            exact
              ⟨account, by
                simpa [EvmYul.SharedState.calldatacopy,
                  EvmYul.SharedState.codeBytesCopy] using hLookup⟩
          | change
              (match
                  EvmYul.Yul.quaternaryCopyOp
                    (fun shared first second third fourth => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            apply
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.quaternaryCopyOp
                    (fun shared first second third fourth => _) state args)
                ?_ hOwner hRun
            apply quaternaryCopyOp_preserves _ ?_
            intro shared first second third fourth hShared
            rcases hShared with ⟨account, hLookup⟩
            exact
              ⟨account, by
                simpa [EvmYul.SharedState.extCodeCopy'] using hLookup⟩
          | change
              (match
                  EvmYul.Yul.binaryMachineStateOp'
                    EvmYul.MachineState.keccak256 state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.binaryMachineStateOp'
                    EvmYul.MachineState.keccak256 state args)
                (binaryMachineStateOp'_preserves
                  EvmYul.MachineState.keccak256) hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  EvmYul.State.balance state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp EvmYul.State.balance state args)
                (unaryStateOp_preserves EvmYul.State.balance
                  balance_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  (fun world value =>
                    (world, world.calldataload value)) state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp
                    (fun world value =>
                      (world, world.calldataload value)) state args)
                (unaryStateOp_preserves _ calldataload_preserves_owner)
                hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  EvmYul.State.extCodeSize state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeSize
                    state args)
                (unaryStateOp_preserves EvmYul.State.extCodeSize
                  extCodeSize_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  EvmYul.State.extCodeHash state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp EvmYul.State.extCodeHash
                    state args)
                (unaryStateOp_preserves EvmYul.State.extCodeHash
                  extCodeHash_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  (fun world value =>
                    (world, world.blockHash value)) state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp
                    (fun world value =>
                      (world, world.blockHash value)) state args)
                (unaryStateOp_preserves _ blockHash_preserves_owner)
                hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  EvmYul.State.sload state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp EvmYul.State.sload state args)
                (unaryStateOp_preserves EvmYul.State.sload
                  sload_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.unaryStateOp
                  EvmYul.State.tload state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.unaryStateOp EvmYul.State.tload state args)
                (unaryStateOp_preserves EvmYul.State.tload
                  tload_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.binaryStateOp
                  EvmYul.State.sstore state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.binaryStateOp EvmYul.State.sstore state args)
                (binaryStateOp_preserves EvmYul.State.sstore
                  sstore_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.binaryStateOp
                  EvmYul.State.tstore state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.binaryStateOp EvmYul.State.tstore state args)
                (binaryStateOp_preserves EvmYul.State.tstore
                  tstore_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.calldatacopy state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.ternaryCopyOp
                    EvmYul.SharedState.calldatacopy state args)
                (ternaryCopyOp_preserves EvmYul.SharedState.calldatacopy
                  calldatacopy_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.ternaryCopyOp
                  EvmYul.SharedState.codeBytesCopy state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.ternaryCopyOp
                    EvmYul.SharedState.codeBytesCopy state args)
                (ternaryCopyOp_preserves EvmYul.SharedState.codeBytesCopy
                  codeBytesCopy_preserves_owner) hOwner hRun
          | change
              (match EvmYul.Yul.quaternaryCopyOp
                  EvmYul.SharedState.extCodeCopy' state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result :=
                  EvmYul.Yul.quaternaryCopyOp
                    EvmYul.SharedState.extCodeCopy' state args)
                (quaternaryCopyOp_preserves
                  EvmYul.SharedState.extCodeCopy'
                  extCodeCopy_preserves_owner) hOwner hRun
          | change
              (match
                  (match args with
                    | [first, second, third] =>
                        if state.toSharedState.returnData.size <
                            second.toNat + third.toNat then
                          Except.error
                            EvmYul.Yul.Exception.InvalidMemoryAccess
                        else
                          Except.ok
                            (state.setMachineState
                              (state.toSharedState.returndatacopy
                                first second third), none)
                    | _ =>
                        Except.error
                          EvmYul.Yul.Exception.InvalidArguments)
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            cases args with
            | nil => simp at hRun
            | cons first rest =>
                cases rest with
                | nil => simp at hRun
                | cons second rest =>
                    cases rest with
                    | nil => simp at hRun
                    | cons third rest =>
                        cases rest with
                        | cons fourth rest => simp at hRun
                        | nil =>
                            by_cases hBounds :
                                state.toSharedState.returnData.size <
                                  second.toNat + third.toNat
                            · simp [hBounds] at hRun
                            · simp [hBounds] at hRun
                              rw [← hRun.1]
                              simpa using hOwner
          | change
              Except.ok (state, none.toList) =
                Except.ok (final, values) at hRun
            simp at hRun
            exact hRun.1 ▸ hOwner
          | change
              (match
                  (match args with
                    | [address] =>
                        Except.ok
                          (state.setMachineState
                            (state.toSharedState.mload address).2,
                            some (state.toSharedState.mload address).1)
                    | _ =>
                        Except.error
                          EvmYul.Yul.Exception.InvalidArguments)
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            cases args with
            | nil => simp at hRun
            | cons first rest =>
                cases rest with
                | cons second rest => simp at hRun
                | nil =>
                    simp at hRun
                    rw [← hRun.1]
                    simpa using hOwner
          | change
              (match EvmYul.Yul.log0Op state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result := EvmYul.Yul.log0Op state args)
                log0Op_preserves hOwner hRun
          | change
              (match EvmYul.Yul.log1Op state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result := EvmYul.Yul.log1Op state args)
                log1Op_preserves hOwner hRun
          | change
              (match EvmYul.Yul.log2Op state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result := EvmYul.Yul.log2Op state args)
                log2Op_preserves hOwner hRun
          | change
              (match EvmYul.Yul.log3Op state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result := EvmYul.Yul.log3Op state args)
                log3Op_preserves hOwner hRun
          | change
              (match EvmYul.Yul.log4Op state args with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves
                (result := EvmYul.Yul.log4Op state args)
                log4Op_preserves hOwner hRun
          | change
              (match
                  (Except.error EvmYul.Yul.Exception.InvalidInstruction :
                    Except EvmYul.Yul.Exception
                      (EvmYul.Yul.State × Option Assembly.Word))
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            simp at hRun
          | change
              (match
                  EvmYul.Yul.ternaryMachineStateOp
                    (fun machine first second third => _) state args
                with
                | Except.ok (result, value) =>
                    Except.ok (result, value.toList)
                | Except.error err => Except.error err) =
                  Except.ok (final, values) at hRun
            exact
              wrappedStep_preserves (ternaryMachineStateOp_preserves _) hOwner
                hRun

end Prim
end Yul
end EvmCompiler
