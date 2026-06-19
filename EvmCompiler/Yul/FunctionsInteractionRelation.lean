import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Yul.InteractionSemantics
import EvmCompiler.Yul.VarStoreRestriction

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRelation

abbrev SourceState := Yul.InteractionSemantics.State
abbrev TargetState := Functions.InteractionSemantics.State

/-- Protected active-frame data. External account implementation code is
intentionally absent; only the active byte image remains observable. -/
structure ExecutionEnvRel
    (source : EvmYul.ExecutionEnv .Yul)
    (target : EvmYul.ExecutionEnv .EVM) : Prop where
  codeOwner : source.codeOwner = target.codeOwner
  sender : source.sender = target.sender
  sourceAddress : source.source = target.source
  weiValue : source.weiValue = target.weiValue
  calldata : source.calldata = target.calldata
  gasPrice : source.gasPrice = target.gasPrice
  header : source.header = target.header
  depth : source.depth = target.depth
  permission : source.perm = target.perm
  blobVersionedHashes :
    source.blobVersionedHashes = target.blobVersionedHashes
  codeImage : source.codeBytes = target.code
  codeBytes : source.codeBytes = target.codeBytes

/-- The code-erased part of a Yul/EVM world relation. This is the owner-facing
interface for closed world operations; active machine state and source locals
remain at the enclosing `SharedRel`/`StateRel` layers. -/
structure WorldRel
    (source : EvmYul.State .Yul)
    (target : EvmYul.State .EVM) : Prop where
  openWorld :
    Simulation.OpenWorld.ofYulState source =
      Simulation.OpenWorld.ofEVMState target
  initialAccounts : source.σ₀ = target.σ₀
  totalGasUsedInBlock :
    source.totalGasUsedInBlock = target.totalGasUsedInBlock
  transactionReceipts :
    source.transactionReceipts = target.transactionReceipts
  executionEnv : ExecutionEnvRel source.executionEnv target.executionEnv
  blocks : source.blocks = target.blocks
  genesisBlockHeader :
    source.genesisBlockHeader = target.genesisBlockHeader

/-- Code-erased shared-state relation for the adjacent Yul-to-Functions pass. -/
structure SharedRel
    (source : EvmYul.SharedState .Yul)
    (target : EvmYul.SharedState .EVM) : Prop where
  openWorld :
    Simulation.OpenWorld.ofYulShared source =
      Simulation.OpenWorld.ofEVMShared target
  machine : source.toMachineState = target.toMachineState
  initialAccounts : source.σ₀ = target.σ₀
  totalGasUsedInBlock :
    source.totalGasUsedInBlock = target.totalGasUsedInBlock
  transactionReceipts :
    source.transactionReceipts = target.transactionReceipts
  executionEnv : ExecutionEnvRel source.executionEnv target.executionEnv
  blocks : source.blocks = target.blocks
  genesisBlockHeader :
    source.genesisBlockHeader = target.genesisBlockHeader

/-- Machine observations retained after terminal control. Return-data scratch
bookkeeping is intentionally absent: STOP clears it on EVM but not in imported
Yul, and no continuation can observe it after a halt. -/
structure TerminalMachineRel
    (source target : EvmYul.MachineState) : Prop where
  gasAvailable : source.gasAvailable = target.gasAvailable
  activeWords : source.activeWords = target.activeWords
  memory : source.memory = target.memory
  output : source.H_return = target.H_return

structure TerminalSharedRel
    (source : EvmYul.SharedState .Yul)
    (target : EvmYul.SharedState .EVM) : Prop where
  openWorld :
    Simulation.OpenWorld.ofYulShared source =
      Simulation.OpenWorld.ofEVMShared target
  machine : TerminalMachineRel source.toMachineState target.toMachineState
  initialAccounts : source.σ₀ = target.σ₀
  totalGasUsedInBlock :
    source.totalGasUsedInBlock = target.totalGasUsedInBlock
  transactionReceipts :
    source.transactionReceipts = target.transactionReceipts
  executionEnv : ExecutionEnvRel source.executionEnv target.executionEnv
  blocks : source.blocks = target.blocks
  genesisBlockHeader :
    source.genesisBlockHeader = target.genesisBlockHeader

def VarsRel (source : EvmYul.Yul.VarStore)
    (target : Locals.Source.Store) : Prop :=
  ∀ name value, source.lookup name = some value →
    target name = some value

/-- Regular Yul states correspond to the stack-free Functions source state.
Compiler-private target locals may extend the source-visible store. -/
def StateRel (source : SourceState) (target : TargetState) : Prop :=
  ∃ sourceShared sourceVars,
    source = .Ok sourceShared sourceVars ∧
      SharedRel sourceShared target.shared ∧
      VarsRel sourceVars target.vars

def TerminalStateRel (source : SourceState) (target : TargetState) : Prop :=
  ∃ sourceShared sourceVars,
    source = .Ok sourceShared sourceVars ∧
      TerminalSharedRel sourceShared target.shared ∧
      VarsRel sourceVars target.vars

namespace ExecutionEnvRel

theorem externalFrame_eq
    {source : EvmYul.ExecutionEnv .Yul}
    {target : EvmYul.ExecutionEnv .EVM}
    (hRel : ExecutionEnvRel source target)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    Simulation.ExternalFrame.mk sourceMachine source.codeOwner source.source
        source.weiValue source.perm =
      Simulation.ExternalFrame.mk targetMachine target.codeOwner target.source
        target.weiValue target.perm := by
  rcases hRel with
    ⟨hOwner, _hSender, hSource, hValue, _hCalldata, _hGasPrice,
      _hHeader, _hDepth, hPermission, _hBlobHashes, _hCodeImage,
      _hCodeBytes⟩
  simp [hMachine, hOwner, hSource, hValue, hPermission]

end ExecutionEnvRel

namespace WorldRel

theorem accounts
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) :
    (Simulation.OpenWorld.ofYulState source).accounts =
      (Simulation.OpenWorld.ofEVMState target).accounts :=
  congrArg Simulation.OpenWorld.accounts hRel.openWorld

theorem substate
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) :
    source.substate = target.substate := by
  exact congrArg Simulation.OpenWorld.substate hRel.openWorld

theorem createdAccounts
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) :
    source.createdAccounts = target.createdAccounts := by
  exact congrArg Simulation.OpenWorld.createdAccounts hRel.openWorld

theorem accountViews
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target)
    (address : EvmYul.AccountAddress) :
    (source.accountMap.find? address).map Simulation.OpenAccount.ofYul =
      (target.accountMap.find? address).map Simulation.OpenAccount.ofEVM := by
  have hAccounts :=
    congrArg Simulation.OpenWorld.accounts hRel.openWorld
  have hLookup := congrArg (fun accounts => accounts.find? address) hAccounts
  simpa [Simulation.OpenWorld.ofYulState,
    Simulation.OpenWorld.ofEVMState,
    Simulation.OpenWorld.find?_mapVal_const] using hLookup

theorem accountValueEq
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target)
    (address : EvmYul.AccountAddress)
    {α : Type} (defaultValue : α)
    (value : Simulation.OpenAccount → α) :
    (source.accountMap.find? address).option defaultValue
        (fun account => value (Simulation.OpenAccount.ofYul account)) =
      (target.accountMap.find? address).option defaultValue
        (fun account => value (Simulation.OpenAccount.ofEVM account)) := by
  have hViews := hRel.accountViews address
  cases hSource : source.accountMap.find? address with
  | none =>
      rw [hSource] at hViews
      cases hTarget : target.accountMap.find? address with
      | none => rfl
      | some targetAccount => simp [hTarget] at hViews
  | some sourceAccount =>
      rw [hSource] at hViews
      cases hTarget : target.accountMap.find? address with
      | none => simp [hTarget] at hViews
      | some targetAccount =>
          rw [hTarget] at hViews
          have hAccount :
              Simulation.OpenAccount.ofYul sourceAccount =
                Simulation.OpenAccount.ofEVM targetAccount := by
            simpa using Option.some.inj hViews
          simpa [hSource, hTarget] using congrArg value hAccount

theorem accountElimValueEq
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target)
    (address : EvmYul.AccountAddress)
    {α : Type} (defaultValue : α)
    (value : Simulation.OpenAccount → α) :
    (source.accountMap.find? address).elim defaultValue
        (fun account => value (Simulation.OpenAccount.ofYul account)) =
      (target.accountMap.find? address).elim defaultValue
        (fun account => value (Simulation.OpenAccount.ofEVM account)) := by
  have hViews := hRel.accountViews address
  cases hSource : source.accountMap.find? address with
  | none =>
      rw [hSource] at hViews
      cases hTarget : target.accountMap.find? address with
      | none => rfl
      | some targetAccount => simp [hTarget] at hViews
  | some sourceAccount =>
      rw [hSource] at hViews
      cases hTarget : target.accountMap.find? address with
      | none => simp [hTarget] at hViews
      | some targetAccount =>
          rw [hTarget] at hViews
          have hAccount :
              Simulation.OpenAccount.ofYul sourceAccount =
                Simulation.OpenAccount.ofEVM targetAccount := by
            simpa using Option.some.inj hViews
          simpa [hSource, hTarget] using congrArg value hAccount

theorem addAccessedAccount
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target)
    (address : EvmYul.AccountAddress) :
    WorldRel
      (source.addAccessedAccount address)
      (target.addAccessedAccount address) := by
  exact
    { openWorld := by
        apply Simulation.OpenWorld.ext_of_fields
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.addAccessedAccount] using hRel.accounts
        · simp [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.addAccessedAccount, hRel.substate]
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.addAccessedAccount] using hRel.createdAccounts
      initialAccounts := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.executionEnv
      blocks := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.genesisBlockHeader }

theorem addAccessedStorageKey
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target)
    (storageKey : EvmYul.AccountAddress × EvmYul.UInt256) :
    WorldRel
      (source.addAccessedStorageKey storageKey)
      (target.addAccessedStorageKey storageKey) := by
  exact
    { openWorld := by
        apply Simulation.OpenWorld.ext_of_fields
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.addAccessedStorageKey] using hRel.accounts
        · simp [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.addAccessedStorageKey, hRel.substate]
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.addAccessedStorageKey] using hRel.createdAccounts
      initialAccounts := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.executionEnv
      blocks := by
        simpa [EvmYul.State.addAccessedStorageKey] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.genesisBlockHeader }

theorem updateAccount
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target)
    (address : EvmYul.AccountAddress)
    (sourceAccount : EvmYul.Account .Yul)
    (targetAccount : EvmYul.Account .EVM)
    (hAccount :
      Simulation.OpenAccount.ofYul sourceAccount =
        Simulation.OpenAccount.ofEVM targetAccount) :
    WorldRel
      (source.updateAccount address sourceAccount)
      (target.updateAccount address targetAccount) := by
  exact
    { openWorld := by
        apply Simulation.OpenWorld.ext_of_fields
        · change
            ((source.accountMap.insert address sourceAccount).mapVal
                fun _ account => Simulation.OpenAccount.ofYul account) =
              ((target.accountMap.insert address targetAccount).mapVal
                fun _ account => Simulation.OpenAccount.ofEVM account)
          rw [Simulation.OpenWorld.mapVal_insert,
            Simulation.OpenWorld.mapVal_insert]
          have hAccounts := hRel.accounts
          change
            (source.accountMap.mapVal
                fun _ account => Simulation.OpenAccount.ofYul account) =
              (target.accountMap.mapVal
                fun _ account => Simulation.OpenAccount.ofEVM account)
            at hAccounts
          rw [hAccounts, hAccount]
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.updateAccount] using hRel.substate
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.State.updateAccount] using hRel.createdAccounts
      initialAccounts := by
        simpa [EvmYul.State.updateAccount] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.updateAccount] using
          hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.updateAccount] using
          hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.State.updateAccount] using hRel.executionEnv
      blocks := by
        simpa [EvmYul.State.updateAccount] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.updateAccount] using hRel.genesisBlockHeader }

theorem withRefundBalance
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) (refundBalance : EvmYul.UInt256) :
    WorldRel
      { source with substate.refundBalance := refundBalance }
      { target with substate.refundBalance := refundBalance } := by
  exact
    { openWorld := by
        apply Simulation.OpenWorld.ext_of_fields
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState] using hRel.accounts
        · simp [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState, hRel.substate]
        · simpa [Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState] using hRel.createdAccounts
      initialAccounts := by simpa using hRel.initialAccounts
      totalGasUsedInBlock := by simpa using hRel.totalGasUsedInBlock
      transactionReceipts := by simpa using hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := by simpa using hRel.blocks
      genesisBlockHeader := by simpa using hRel.genesisBlockHeader }

theorem updateStorageAccount
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hAccount :
      Simulation.OpenAccount.ofYul source =
        Simulation.OpenAccount.ofEVM target)
    (key value : EvmYul.UInt256) :
    Simulation.OpenAccount.ofYul (source.updateStorage key value) =
      Simulation.OpenAccount.ofEVM (target.updateStorage key value) := by
  rw [← Simulation.OpenAccount.ofAccount_yul,
    ← Simulation.OpenAccount.ofAccount_evm,
    Simulation.OpenAccount.ofAccount_updateStorage,
    Simulation.OpenAccount.ofAccount_updateStorage]
  rw [Simulation.OpenAccount.ofAccount_yul,
    Simulation.OpenAccount.ofAccount_evm, hAccount]
  have hStorage := congrArg Simulation.OpenAccount.storage hAccount
  change source.storage = target.storage at hStorage
  simp [hStorage]

theorem updateTransientStorageAccount
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hAccount :
      Simulation.OpenAccount.ofYul source =
        Simulation.OpenAccount.ofEVM target)
    (key value : EvmYul.UInt256) :
    Simulation.OpenAccount.ofYul
        (source.updateTransientStorage key value) =
      Simulation.OpenAccount.ofEVM
        (target.updateTransientStorage key value) := by
  rw [← Simulation.OpenAccount.ofAccount_yul,
    ← Simulation.OpenAccount.ofAccount_evm,
    Simulation.OpenAccount.ofAccount_updateTransientStorage,
    Simulation.OpenAccount.ofAccount_updateTransientStorage]
  rw [Simulation.OpenAccount.ofAccount_yul,
    Simulation.OpenAccount.ofAccount_evm, hAccount]
  have hStorage :=
    congrArg Simulation.OpenAccount.transientStorage hAccount
  change source.tstorage = target.tstorage at hStorage
  simp [hStorage]

theorem tstore
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) (key value : EvmYul.UInt256) :
    WorldRel (source.tstore key value) (target.tstore key value) := by
  let owner := source.executionEnv.codeOwner
  have hTargetOwner : target.executionEnv.codeOwner = owner := by
    simpa [owner] using hRel.executionEnv.codeOwner.symm
  unfold EvmYul.State.tstore
  dsimp only
  rw [hTargetOwner]
  have hLookup := hRel.accountViews owner
  cases hSource : source.lookupAccount owner with
  | none =>
      change source.accountMap.find? owner = none at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none => simpa [hSource, hTarget] using hRel
      | some targetAccount =>
          change target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          simp at hLookup
  | some sourceAccount =>
      change source.accountMap.find? owner = some sourceAccount at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none =>
          change target.accountMap.find? owner = none at hTarget
          rw [hTarget] at hLookup
          simp at hLookup
      | some targetAccount =>
          change target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          have hAccount :
              Simulation.OpenAccount.ofYul sourceAccount =
                Simulation.OpenAccount.ofEVM targetAccount := by
            simpa using Option.some.inj hLookup
          simpa [hSource, hTarget] using
            hRel.updateAccount owner
              (sourceAccount.updateTransientStorage key value)
              (targetAccount.updateTransientStorage key value)
              (updateTransientStorageAccount hAccount key value)

theorem sstore
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) (key value : EvmYul.UInt256) :
    WorldRel (source.sstore key value) (target.sstore key value) := by
  let owner := source.executionEnv.codeOwner
  have hTargetOwner : target.executionEnv.codeOwner = owner := by
    simpa [owner] using hRel.executionEnv.codeOwner.symm
  have hCurrent :
      Simulation.CodeErasedState.currentStorageValue source owner key =
        Simulation.CodeErasedState.currentStorageValue target owner key := by
    have hLookup := hRel.accountViews owner
    cases hSource : source.accountMap.find? owner with
    | none =>
        rw [hSource] at hLookup
        cases hTarget : target.accountMap.find? owner with
        | none =>
            simp [Simulation.CodeErasedState.currentStorageValue,
              Batteries.RBMap.find!, hSource, hTarget]
            rfl
        | some targetAccount => simp [hTarget] at hLookup
    | some sourceAccount =>
        rw [hSource] at hLookup
        cases hTarget : target.accountMap.find? owner with
        | none => simp [hTarget] at hLookup
        | some targetAccount =>
            rw [hTarget] at hLookup
            have hAccount :
                Simulation.OpenAccount.ofYul sourceAccount =
                  Simulation.OpenAccount.ofEVM targetAccount := by
              simpa using Option.some.inj hLookup
            have hStorage :=
              congrArg Simulation.OpenAccount.storage hAccount
            change sourceAccount.storage = targetAccount.storage at hStorage
            simp [Simulation.CodeErasedState.currentStorageValue,
              Batteries.RBMap.find!, hSource, hTarget, hStorage]
  have hInitial :
      Simulation.CodeErasedState.initialStorageValue source owner key =
        Simulation.CodeErasedState.initialStorageValue target owner key := by
    simp [Simulation.CodeErasedState.initialStorageValue,
      hRel.initialAccounts]
  have hRefund :
      source.substate.refundBalance = target.substate.refundBalance := by
    simpa using congrArg EvmYul.Substate.refundBalance hRel.substate
  rw [Simulation.CodeErasedState.sstore_eq,
    Simulation.CodeErasedState.sstore_eq, hTargetOwner]
  let newRefund : EvmYul.UInt256 :=
    Simulation.CodeErasedState.sstoreRefundBalance
      (Simulation.CodeErasedState.initialStorageValue source owner key)
      (Simulation.CodeErasedState.currentStorageValue source owner key)
      value source.substate.refundBalance
  have hNewRefund :
      newRefund =
        Simulation.CodeErasedState.sstoreRefundBalance
          (Simulation.CodeErasedState.initialStorageValue target owner key)
          (Simulation.CodeErasedState.currentStorageValue target owner key)
          value target.substate.refundBalance := by
    simp [newRefund, hInitial, hCurrent, hRefund]
  change
    WorldRel
      ((source.lookupAccount owner).option source
        (fun account =>
          { (source.setAccount owner
                (account.updateStorage key value)
              |>.addAccessedStorageKey (owner, key)) with
            substate.refundBalance := newRefund }))
      ((target.lookupAccount owner).option target
        (fun account =>
          { (target.setAccount owner
                (account.updateStorage key value)
              |>.addAccessedStorageKey (owner, key)) with
            substate.refundBalance :=
              Simulation.CodeErasedState.sstoreRefundBalance
                (Simulation.CodeErasedState.initialStorageValue
                  target owner key)
                (Simulation.CodeErasedState.currentStorageValue
                  target owner key)
                value target.substate.refundBalance }))
  rw [← hNewRefund]
  have hLookup := hRel.accountViews owner
  cases hSource : source.lookupAccount owner with
  | none =>
      change source.accountMap.find? owner = none at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none => simpa [hSource, hTarget] using hRel
      | some targetAccount =>
          change target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          simp at hLookup
  | some sourceAccount =>
      change source.accountMap.find? owner = some sourceAccount at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none =>
          change target.accountMap.find? owner = none at hTarget
          rw [hTarget] at hLookup
          simp at hLookup
      | some targetAccount =>
          change target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          have hAccount :
              Simulation.OpenAccount.ofYul sourceAccount =
                Simulation.OpenAccount.ofEVM targetAccount := by
            simpa using Option.some.inj hLookup
          have hUpdated :=
            hRel.updateAccount owner
              (sourceAccount.updateStorage key value)
              (targetAccount.updateStorage key value)
              (updateStorageAccount hAccount key value)
          have hAccessed := hUpdated.addAccessedStorageKey (owner, key)
          simpa [hSource, hTarget, EvmYul.State.setAccount] using
            hAccessed.withRefundBalance newRefund

theorem codeErasedExtCodeHash
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : WorldRel source target) (value : EvmYul.UInt256) :
    WorldRel
        (Simulation.CodeErasedState.extCodeHash source value).1
        (Simulation.CodeErasedState.extCodeHash target value).1 ∧
      (Simulation.CodeErasedState.extCodeHash source value).2 =
        (Simulation.CodeErasedState.extCodeHash target value).2 := by
  let address := EvmYul.AccountAddress.ofUInt256 value
  have hDead :
      Simulation.CodeErasedState.dead source.accountMap address =
        Simulation.CodeErasedState.dead target.accountMap address := by
    simpa [Simulation.CodeErasedState.dead,
      Simulation.CodeErasedState.emptyAccount,
      Simulation.OpenAccount.ofAccount_yul,
      Simulation.OpenAccount.ofAccount_evm] using
      hRel.accountValueEq address true Simulation.OpenAccount.empty
  have hHash :
      (source.lookupAccount address).option ⟨0⟩
          (fun account =>
            EvmYul.UInt256.ofNat <|
              EvmYul.fromByteArrayBigEndian
                (ffi.KEC (EvmYul.State.accountCodeImage account))) =
        (target.lookupAccount address).option ⟨0⟩
          (fun account =>
            EvmYul.UInt256.ofNat <|
              EvmYul.fromByteArrayBigEndian
                (ffi.KEC (EvmYul.State.accountCodeImage account))) := by
    simpa [EvmYul.State.lookupAccount,
      Simulation.OpenAccount.ofYul,
      Simulation.OpenAccount.ofEVM,
      EvmYul.State.accountCodeImage] using
      hRel.accountValueEq address (⟨0⟩ : EvmYul.UInt256)
        (fun account =>
          EvmYul.UInt256.ofNat <|
            EvmYul.fromByteArrayBigEndian (ffi.KEC account.codeBytes))
  cases hTargetDead :
      Simulation.CodeErasedState.dead target.accountMap address with
  | false =>
      constructor
      · simpa [Simulation.CodeErasedState.extCodeHash, address,
          hDead, hTargetDead] using hRel.addAccessedAccount address
      · simpa [Simulation.CodeErasedState.extCodeHash, address,
          hDead, hTargetDead] using hHash
  | true =>
      constructor
      · simpa [Simulation.CodeErasedState.extCodeHash, address,
          hDead, hTargetDead] using hRel.addAccessedAccount address
      · simp [Simulation.CodeErasedState.extCodeHash, address,
          hDead, hTargetDead]

end WorldRel

namespace SharedRel

theorem world
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) :
    WorldRel source.toState target.toState := by
  exact
    { openWorld := hRel.openWorld
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

/-- Replace only the code-erased world component while retaining the active
machine relation. -/
theorem withWorldState
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (sourceWorld : EvmYul.State .Yul)
    (targetWorld : EvmYul.State .EVM)
    (hWorld : WorldRel sourceWorld targetWorld) :
    SharedRel
      { source with toState := sourceWorld }
      { target with toState := targetWorld } := by
  exact
    { openWorld := hWorld.openWorld
      machine := hRel.machine
      initialAccounts := hWorld.initialAccounts
      totalGasUsedInBlock := hWorld.totalGasUsedInBlock
      transactionReceipts := hWorld.transactionReceipts
      executionEnv := hWorld.executionEnv
      blocks := hWorld.blocks
      genesisBlockHeader := hWorld.genesisBlockHeader }

/-- Replace only the active machine while retaining the exact code-erased
world relation. -/
theorem withMachine
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    SharedRel
      { source with toMachineState := sourceMachine }
      { target with toMachineState := targetMachine } := by
  exact
    { openWorld := by simpa using hRel.openWorld
      machine := hMachine
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

theorem extCodeCopy
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (account destination readStart size : EvmYul.UInt256) :
    SharedRel
      (EvmYul.SharedState.extCodeCopy'
        source account destination readStart size)
      (EvmYul.SharedState.extCodeCopy'
        target account destination readStart size) := by
  let address := EvmYul.AccountAddress.ofUInt256 account
  have hCode :
      (source.lookupAccount address).option ByteArray.empty
          EvmYul.State.accountCodeImage =
        (target.lookupAccount address).option ByteArray.empty
          EvmYul.State.accountCodeImage := by
    simpa [EvmYul.State.lookupAccount,
      Simulation.OpenAccount.ofYul,
      Simulation.OpenAccount.ofEVM,
      EvmYul.State.accountCodeImage] using
      hRel.world.accountValueEq address ByteArray.empty
        Simulation.OpenAccount.codeBytes
  have hWorld := hRel.world.addAccessedAccount address
  exact
    { openWorld := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using hWorld.openWorld
      machine := by
        simp [EvmYul.SharedState.extCodeCopy', address,
          hRel.machine, hCode]
      initialAccounts := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using
          hWorld.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using
          hWorld.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using
          hWorld.transactionReceipts
      executionEnv := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using hWorld.executionEnv
      blocks := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using hWorld.blocks
      genesisBlockHeader := by
        simpa [EvmYul.SharedState.extCodeCopy',
          EvmYul.State.addAccessedAccount, address] using
          hWorld.genesisBlockHeader }

theorem logOp
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (offset size : EvmYul.UInt256) (topics : Array EvmYul.UInt256) :
    SharedRel
      (EvmYul.SharedState.logOp offset size topics source)
      (EvmYul.SharedState.logOp offset size topics target) := by
  exact
    { openWorld := by
        apply Simulation.OpenWorld.ext_of_fields
        · simpa [Simulation.OpenWorld.ofYulShared,
            Simulation.OpenWorld.ofEVMShared,
            EvmYul.SharedState.logOp] using hRel.world.accounts
        · simp [Simulation.OpenWorld.ofYulShared,
            Simulation.OpenWorld.ofEVMShared,
            Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.SharedState.logOp, hRel.world.substate,
            hRel.executionEnv.codeOwner, hRel.machine]
        · simpa [Simulation.OpenWorld.ofYulShared,
            Simulation.OpenWorld.ofEVMShared,
            EvmYul.SharedState.logOp] using hRel.world.createdAccounts
      machine := by
        simp [EvmYul.SharedState.logOp, hRel.machine]
      initialAccounts := by
        simpa [EvmYul.SharedState.logOp] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.SharedState.logOp] using hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.SharedState.logOp] using hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.SharedState.logOp] using hRel.executionEnv
      blocks := by simpa [EvmYul.SharedState.logOp] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.SharedState.logOp] using hRel.genesisBlockHeader }

end SharedRel

namespace TerminalMachineRel

theorem of_eq {source target : EvmYul.MachineState}
    (hEq : source = target) : TerminalMachineRel source target := by
  subst target
  exact ⟨rfl, rfl, rfl, rfl⟩

end TerminalMachineRel

namespace TerminalSharedRel

theorem of_shared
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) :
    TerminalSharedRel source target :=
  { openWorld := hRel.openWorld
    machine := TerminalMachineRel.of_eq hRel.machine
    initialAccounts := hRel.initialAccounts
    totalGasUsedInBlock := hRel.totalGasUsedInBlock
    transactionReceipts := hRel.transactionReceipts
    executionEnv := hRel.executionEnv
    blocks := hRel.blocks
    genesisBlockHeader := hRel.genesisBlockHeader }

theorem stop
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) :
    TerminalSharedRel
      { source with H_return := ByteArray.empty }
      { target with
          returnData := ByteArray.empty
          H_return := ByteArray.empty } := by
  exact
    { openWorld := by simpa using hRel.openWorld
      machine :=
        { gasAvailable := by
            simpa using congrArg (·.gasAvailable) hRel.machine
          activeWords := by
            simpa using congrArg (·.activeWords) hRel.machine
          memory := by simpa using congrArg (·.memory) hRel.machine
          output := rfl }
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

theorem evmReturn
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) (address size : Word) :
    TerminalSharedRel
      { source with
          toMachineState := source.toMachineState.evmReturn address size }
      { target with
          toMachineState := target.toMachineState.evmReturn address size } := by
  exact
    { openWorld := by simpa using hRel.openWorld
      machine := TerminalMachineRel.of_eq
        (congrArg (fun machine => machine.evmReturn address size)
          hRel.machine)
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

theorem evmRevert
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) (address size : Word) :
    TerminalSharedRel
      { source with
          toMachineState := source.toMachineState.evmRevert address size }
      { target with
          toMachineState := target.toMachineState.evmRevert address size } := by
  exact
    { openWorld := by simpa using hRel.openWorld
      machine := TerminalMachineRel.of_eq
        (congrArg (fun machine => machine.evmRevert address size)
          hRel.machine)
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

theorem accounts_selfdestructAccountMap
    {τ : EvmYul.OperationType} (accounts : EvmYul.AccountMap τ)
    (source target : EvmYul.AccountAddress) (created : Bool) :
    (EvmYul.selfdestructAccountMap accounts source target created).mapVal
        (fun _ account => Simulation.OpenAccount.ofAccount account) =
      Simulation.OpenWorld.selfdestructAccounts
        (accounts.mapVal fun _ account =>
          Simulation.OpenAccount.ofAccount account)
        source target created := by
  unfold EvmYul.selfdestructAccountMap
    Simulation.OpenWorld.selfdestructAccounts
  rw [Simulation.OpenWorld.find?_mapVal_const]
  cases hSource : accounts.find? source with
  | none => simp [hSource, dbgTrace]
  | some sourceAccount =>
      simp only [hSource, Option.map_some]
      rw [Simulation.OpenWorld.find?_mapVal_const]
      cases hTarget : accounts.find? target with
      | none =>
          simp only [hTarget, Option.map_none]
          by_cases hZero :
              (sourceAccount.balance == (⟨0⟩ : EvmYul.UInt256)) = true
          ·
            have hZeroErased :
                ((Simulation.OpenAccount.ofAccount sourceAccount).balance ==
                    (EvmYul.UInt256.ofNat 0)) = true := by
              simpa [EvmYul.UInt256.ofNat] using hZero
            rw [if_pos hZero, if_pos hZeroErased]
          ·
            have hZeroErased :
                ¬(((Simulation.OpenAccount.ofAccount sourceAccount).balance ==
                    (EvmYul.UInt256.ofNat 0)) = true) := by
              simpa [EvmYul.UInt256.ofNat] using hZero
            rw [if_neg hZero, if_neg hZeroErased,
              Simulation.OpenWorld.mapVal_insert,
              Simulation.OpenWorld.mapVal_insert]
            simp [EvmYul.UInt256.ofNat, Id.run]
      | some targetAccount =>
          simp only [hTarget, Option.map_some]
          by_cases hDistinct : target ≠ source
          · rw [if_pos hDistinct, if_pos hDistinct,
              Simulation.OpenWorld.mapVal_insert,
              Simulation.OpenWorld.mapVal_insert]
            simp [EvmYul.UInt256.ofNat, Id.run]
          · rw [if_neg hDistinct, if_neg hDistinct]
            cases created <;>
              simp [Simulation.OpenWorld.mapVal_insert,
                EvmYul.UInt256.ofNat, Id.run]

theorem selfdestruct
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (vars : EvmYul.Yul.VarStore) (recipient : Word) :
    TerminalSharedRel
      (EvmYul.Yul.selfdestructState
        (.Ok source vars) recipient).sharedState
      (EvmYul.EVM.selfdestructState
        { toSharedState := target
          pc := EvmYul.UInt256.ofNat 0
          stack := [recipient]
          execLength := 0 }
        recipient []).toSharedState := by
  let sourceOwner := source.executionEnv.codeOwner
  let targetOwner := target.executionEnv.codeOwner
  let recipientAddress := EvmYul.AccountAddress.ofUInt256 recipient
  have hOwner : sourceOwner = targetOwner :=
    hRel.executionEnv.codeOwner
  have hOwnerDirect :
      source.executionEnv.codeOwner = target.executionEnv.codeOwner :=
    hRel.executionEnv.codeOwner
  have hAccounts :
      (source.accountMap.mapVal fun _ account =>
          Simulation.OpenAccount.ofAccount account) =
        (target.accountMap.mapVal fun _ account =>
          Simulation.OpenAccount.ofAccount account) := by
    simpa [Simulation.OpenWorld.ofYulShared,
      Simulation.OpenWorld.ofEVMShared,
      Simulation.OpenWorld.ofYulState,
      Simulation.OpenWorld.ofEVMState] using
        congrArg Simulation.OpenWorld.accounts hRel.openWorld
  have hSubstate : source.substate = target.substate := by
    simpa [Simulation.OpenWorld.ofYulShared,
      Simulation.OpenWorld.ofEVMShared,
      Simulation.OpenWorld.ofYulState,
      Simulation.OpenWorld.ofEVMState] using
        congrArg Simulation.OpenWorld.substate hRel.openWorld
  have hCreated : source.createdAccounts = target.createdAccounts := by
    simpa [Simulation.OpenWorld.ofYulShared,
      Simulation.OpenWorld.ofEVMShared,
      Simulation.OpenWorld.ofYulState,
      Simulation.OpenWorld.ofEVMState] using
        congrArg Simulation.OpenWorld.createdAccounts hRel.openWorld
  have hCreatedContains :
      source.createdAccounts.contains sourceOwner =
        target.createdAccounts.contains targetOwner := by
    rw [hOwner, hCreated]
  exact
    { openWorld := by
        apply Simulation.OpenWorld.ext_of_fields
        · simp only [Simulation.OpenWorld.ofYulShared,
            Simulation.OpenWorld.ofEVMShared,
            Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.Yul.selfdestructState,
            EvmYul.EVM.selfdestructState,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.toState,
            EvmYul.Yul.State.setState,
            EvmYul.Yul.State.setMachineState,
            EvmYul.Yul.State.sharedState,
            EvmYul.Yul.State.toMachineState,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            sourceOwner, targetOwner, recipientAddress]
          change
            (EvmYul.selfdestructAccountMap source.accountMap
                source.executionEnv.codeOwner
                (EvmYul.AccountAddress.ofUInt256 recipient)
                (source.createdAccounts.contains
                  source.executionEnv.codeOwner)).mapVal
                  (fun _ account =>
                    Simulation.OpenAccount.ofAccount account) =
              (EvmYul.selfdestructAccountMap target.accountMap
                target.executionEnv.codeOwner
                (EvmYul.AccountAddress.ofUInt256 recipient)
                (target.createdAccounts.contains
                  target.executionEnv.codeOwner)).mapVal
                  (fun _ account =>
                    Simulation.OpenAccount.ofAccount account)
          rw [accounts_selfdestructAccountMap,
            accounts_selfdestructAccountMap, hOwnerDirect,
            hCreated, hAccounts]
        · simp [Simulation.OpenWorld.ofYulShared,
            Simulation.OpenWorld.ofEVMShared,
            Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.Yul.selfdestructState,
            EvmYul.EVM.selfdestructState,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.toState,
            EvmYul.Yul.State.setState,
            EvmYul.Yul.State.setMachineState,
            EvmYul.Yul.State.sharedState,
            EvmYul.Yul.State.toMachineState,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            sourceOwner, targetOwner, recipientAddress,
            hOwner, hCreated, hCreatedContains, hSubstate]
        · simpa [Simulation.OpenWorld.ofYulShared,
            Simulation.OpenWorld.ofEVMShared,
            Simulation.OpenWorld.ofYulState,
            Simulation.OpenWorld.ofEVMState,
            EvmYul.Yul.selfdestructState,
            EvmYul.EVM.selfdestructState,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.toState,
            EvmYul.Yul.State.setState,
            EvmYul.Yul.State.setMachineState,
            EvmYul.Yul.State.sharedState,
            EvmYul.Yul.State.toMachineState,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hCreated
      machine :=
        { gasAvailable := by
            simpa [EvmYul.Yul.selfdestructState,
              EvmYul.EVM.selfdestructState,
              EvmYul.Yul.State.setState,
              EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.sharedState,
              EvmYul.Yul.State.toMachineState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn] using
                congrArg (·.gasAvailable) hRel.machine
          activeWords := by
            simpa [EvmYul.Yul.selfdestructState,
              EvmYul.EVM.selfdestructState,
              EvmYul.Yul.State.setState,
              EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.sharedState,
              EvmYul.Yul.State.toMachineState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn] using
                congrArg (·.activeWords) hRel.machine
          memory := by
            simpa [EvmYul.Yul.selfdestructState,
              EvmYul.EVM.selfdestructState,
              EvmYul.Yul.State.setState,
              EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.sharedState,
              EvmYul.Yul.State.toMachineState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn] using
                congrArg (·.memory) hRel.machine
          output := by
            simp [EvmYul.Yul.selfdestructState,
              EvmYul.EVM.selfdestructState,
              EvmYul.Yul.State.setState,
              EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.sharedState,
              EvmYul.Yul.State.toMachineState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn] }
      initialAccounts := by
        simpa [EvmYul.Yul.selfdestructState,
          EvmYul.EVM.selfdestructState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
          EvmYul.Yul.State.sharedState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.Yul.selfdestructState,
          EvmYul.EVM.selfdestructState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
          EvmYul.Yul.State.sharedState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.Yul.selfdestructState,
          EvmYul.EVM.selfdestructState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
          EvmYul.Yul.State.sharedState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.Yul.selfdestructState,
          EvmYul.EVM.selfdestructState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
          EvmYul.Yul.State.sharedState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.executionEnv
      blocks := by
        simpa [EvmYul.Yul.selfdestructState,
          EvmYul.EVM.selfdestructState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
          EvmYul.Yul.State.sharedState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.Yul.selfdestructState,
          EvmYul.EVM.selfdestructState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.setMachineState,
          EvmYul.Yul.State.sharedState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.genesisBlockHeader }

end TerminalSharedRel

namespace SharedRel

theorem externalFrame_eq
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) :
    Simulation.ExternalFrame.ofShared source =
      Simulation.ExternalFrame.ofShared target := by
  exact hRel.executionEnv.externalFrame_eq _ _ hRel.machine

/-- Installing one exact arbitrary response world and one related local
machine transition preserves the adjacent relation. -/
theorem withWorldAndMachine
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (world : Simulation.OpenWorld)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    SharedRel
      { Simulation.OpenWorld.installYulShared source world with
        toMachineState := sourceMachine }
      { Simulation.OpenWorld.installEVMShared target world with
        toMachineState := targetMachine } := by
  refine
    { openWorld := by
        change
          Simulation.OpenWorld.ofYulShared
              (Simulation.OpenWorld.installYulShared source world) =
            Simulation.OpenWorld.ofEVMShared
              (Simulation.OpenWorld.installEVMShared target world)
        simp
      machine := hMachine
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

end SharedRel

namespace VarsRel

theorem empty :
    VarsRel (default : EvmYul.Yul.VarStore)
      Locals.Source.Store.empty := by
  intro name value hLookup
  change (none : Option Word) = some value at hLookup
  contradiction

theorem insert
    {source : EvmYul.Yul.VarStore} {target : Locals.Source.Store}
    (hRel : VarsRel source target) (name : EvmYul.Identifier)
    (value : Word) :
    VarsRel (source.insert name value)
      (Locals.Source.Store.insert target name value) := by
  intro key result hLookup
  by_cases hKey : key = name
  · subst key
    simp at hLookup
    rcases hLookup with ⟨rfl⟩
    simp [Locals.Source.Store.insert]
  · rw [Finmap.lookup_insert_of_ne source hKey] at hLookup
    rw [Locals.Source.Store.insert_of_ne hKey]
    exact hRel key result hLookup

end VarsRel

/-- Every target local is tracked by the compiler freshness state. -/
def TargetDomainWithin (used : List Functions.Name)
    (target : Locals.Source.Store) : Prop :=
  ∀ name value, target name = some value → name ∈ used

/-- Later generated code preserves every target local already allocated. -/
def TargetExtends (before after : Locals.Source.Store) : Prop :=
  ∀ name value, before name = some value → after name = some value

namespace TargetDomainWithin

theorem mono
    {before after : List Functions.Name}
    {target : Locals.Source.Store}
    (hDomain : TargetDomainWithin before target)
    (hSubset : ∀ name, name ∈ before → name ∈ after) :
    TargetDomainWithin after target := by
  intro name value hLookup
  exact hSubset name (hDomain name value hLookup)

theorem lookup_none
    {used : List Functions.Name} {target : Locals.Source.Store}
    (hDomain : TargetDomainWithin used target)
    {name : Functions.Name} (hFresh : name ∉ used) :
    target name = none := by
  cases hLookup : target name with
  | none => rfl
  | some value =>
      exact False.elim (hFresh (hDomain name value hLookup))

theorem insert
    {used : List Functions.Name} {target : Locals.Source.Store}
    (hDomain : TargetDomainWithin used target)
    {name : Functions.Name} {value : Word}
    (hFresh : name ∉ used) :
    TargetDomainWithin (name :: used)
      (Locals.Source.Store.insert target name value) := by
  intro key result hLookup
  by_cases hEq : key = name
  · subst key
    exact List.mem_cons_self
  · rw [Locals.Source.Store.insert_of_ne hEq] at hLookup
    exact List.mem_cons_of_mem name (hDomain key result hLookup)

theorem insert_used
    {used : List Functions.Name} {target : Locals.Source.Store}
    (hDomain : TargetDomainWithin used target)
    {name : Functions.Name} (hUsed : name ∈ used) (value : Word) :
    TargetDomainWithin used
      (Locals.Source.Store.insert target name value) := by
  intro key result hLookup
  by_cases hEq : key = name
  · subst key
    exact hUsed
  · rw [Locals.Source.Store.insert_of_ne hEq] at hLookup
    exact hDomain key result hLookup

theorem insertMany_used :
    ∀ {names : List Functions.Name} {values : List Word}
      {used : List Functions.Name} {target final : Locals.Source.Store},
      TargetDomainWithin used target →
      (∀ name, name ∈ names → name ∈ used) →
      Functions.Source.Store.insertMany names values target = some final →
      TargetDomainWithin used final
  | [], [], _used, _target, final, hDomain, _hUsed, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
      subst final
      exact hDomain
  | [], _value :: _values, _used, _target, _final,
      _hDomain, _hUsed, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | _name :: _names, [], _used, _target, _final,
      _hDomain, _hUsed, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | name :: names, value :: values, used, target, final,
      hDomain, hUsed, hInsert => by
      have hHead := hDomain.insert_used (hUsed name (by simp)) value
      have hTailUsed : ∀ candidate, candidate ∈ names → candidate ∈ used := by
        intro candidate hMem
        exact hUsed candidate (by simp [hMem])
      change
        Functions.Source.Store.insertMany names values
            (Locals.Source.Store.insert target name value) = some final
        at hInsert
      exact insertMany_used hHead hTailUsed hInsert

theorem restrictTo
    {used scope : List Functions.Name}
    {target : Functions.InteractionSemantics.State}
    (hDomain : TargetDomainWithin used target.vars) :
    TargetDomainWithin used (target.restrictTo scope).vars := by
  intro name value hLookup
  by_cases hMem : name ∈ scope
  · apply hDomain name value
    simpa [Locals.Source.State.restrictTo,
      Locals.Source.Store.restrictTo, hMem] using hLookup
  · simp [Locals.Source.State.restrictTo,
      Locals.Source.Store.restrictTo, hMem] at hLookup

end TargetDomainWithin

namespace TargetExtends

theorem refl (target : Locals.Source.Store) :
    TargetExtends target target := by
  intro name value hLookup
  exact hLookup

theorem trans
    {first second third : Locals.Source.Store}
    (hFirst : TargetExtends first second)
    (hSecond : TargetExtends second third) :
    TargetExtends first third := by
  intro name value hLookup
  exact hSecond name value (hFirst name value hLookup)

theorem insert_fresh
    {target : Locals.Source.Store} {name : Functions.Name} {value : Word}
    (hFresh : target name = none) :
    TargetExtends target (Locals.Source.Store.insert target name value) := by
  intro key result hLookup
  have hNe : key ≠ name := by
    intro hEq
    subst key
    rw [hFresh] at hLookup
    contradiction
  simpa [Locals.Source.Store.insert_of_ne hNe] using hLookup

end TargetExtends

namespace StateRel

theorem lookup
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    {name : EvmYul.Identifier} {value : Word}
    (hLookup : source.lookup? name = some value) :
    target.vars name = some value := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  rw [hSource] at hLookup
  exact hVars name value (by simpa [EvmYul.Yul.State.lookup?] using hLookup)

theorem shared
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    SharedRel source.sharedState target.shared := by
  rcases hRel with ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  simpa [hSource] using hShared

theorem externalFrame_eq
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    Simulation.ExternalFrame.ofShared source.sharedState =
      Simulation.ExternalFrame.ofShared target.shared :=
  (shared hRel).externalFrame_eq

theorem openWorld_eq
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    Simulation.OpenWorld.ofYulShared source.sharedState =
      Simulation.OpenWorld.ofEVMShared target.shared :=
  (shared hRel).openWorld

/-- Arbitrary external post-worlds preserve source-visible locals and the
protected frame while installing exactly the same world on both sides. -/
theorem withWorldAndMachine
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    (world : Simulation.OpenWorld)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    StateRel
      (Yul.InteractionSemantics.State.withWorldAndMachine
        source world sourceMachine)
      (target.withShared
        { Simulation.OpenWorld.installEVMShared target.shared world with
          toMachineState := targetMachine }) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  refine ⟨_, sourceVars, rfl, ?_, hVars⟩
  exact hShared.withWorldAndMachine world sourceMachine targetMachine hMachine

/-- A closed primitive may update only the active machine while retaining the
exact current world. -/
theorem withMachine
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    StateRel
      (source.setMachineState sourceMachine)
      (target.withShared
        { target.shared with toMachineState := targetMachine }) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  let sourceFinal : EvmYul.SharedState .Yul :=
    { sourceShared with toMachineState := sourceMachine }
  let targetFinal : EvmYul.SharedState .EVM :=
    { target.shared with toMachineState := targetMachine }
  refine ⟨sourceFinal, sourceVars, ?_, ?_, ?_⟩
  · simp [sourceFinal, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.setSharedState]
  · exact
      { openWorld := by simpa using hShared.openWorld
        machine := hMachine
        initialAccounts := hShared.initialAccounts
        totalGasUsedInBlock := hShared.totalGasUsedInBlock
        transactionReceipts := hShared.transactionReceipts
        executionEnv := by simpa using hShared.executionEnv
        blocks := hShared.blocks
        genesisBlockHeader := hShared.genesisBlockHeader }
  · simpa [targetFinal, Locals.Source.State.withShared] using hVars

/-- A closed primitive may replace the complete related shared-state pair
while retaining source-visible locals. -/
theorem withSharedState
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    (sourceShared : EvmYul.SharedState .Yul)
    (targetShared : EvmYul.SharedState .EVM)
    (hShared : SharedRel sourceShared targetShared) :
    StateRel
      (source.setSharedState sourceShared)
      (target.withShared targetShared) := by
  rcases hRel with
    ⟨oldSourceShared, sourceVars, hSource, _hOldShared, hVars⟩
  subst source
  refine ⟨sourceShared, sourceVars, ?_, hShared, ?_⟩
  · simp [EvmYul.Yul.State.setSharedState]
  · simpa [Locals.Source.State.withShared] using hVars

/-- A closed world operation may replace the state component on both sides
while preserving the active machine and source-visible locals. -/
theorem withWorldState
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    (sourceWorld : EvmYul.State .Yul)
    (targetWorld : EvmYul.State .EVM)
    (hWorld : WorldRel sourceWorld targetWorld) :
    StateRel
      (source.setState sourceWorld)
      (target.withShared { target.shared with toState := targetWorld }) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  refine
    ⟨{ sourceShared with toState := sourceWorld }, sourceVars,
      ?_, hShared.withWorldState sourceWorld targetWorld hWorld, ?_⟩
  · simp [EvmYul.Yul.State.setState]
  · simpa [Locals.Source.State.withShared] using hVars

theorem multifill_single
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    (name : EvmYul.Identifier) (value : Word) :
    StateRel (source.multifill [name] [value])
      (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  refine
    ⟨sourceShared, sourceVars.insert name value, ?_, hShared,
      VarsRel.insert hVars name value⟩
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

end StateRel

/-- Reviving an abrupt Yul checkpoint exposes the same local lookup payload. -/
theorem lookupBang_reviveJump
    (source : SourceState) (name : Functions.Name) :
    source.reviveJump.lookup! name = source.lookup! name := by
  cases source with
  | Ok shared vars => rfl
  | OutOfFuel => rfl
  | Checkpoint jump => cases jump <;> rfl

def VarsDomainWithin (layout : List Functions.Name)
    (source : EvmYul.Yul.VarStore) : Prop :=
  ∀ name value, source.lookup name = some value → name ∈ layout

def VarsDefinedOn (layout : List Functions.Name)
    (source : EvmYul.Yul.VarStore) : Prop :=
  ∀ name, name ∈ layout → ∃ value, source.lookup name = some value

/-- Regular adjacent relation plus the exact source lexical domain. Target
locals may still extend this domain with compiler-private names. -/
structure ScopedStateRel (layout : List Functions.Name)
    (source : SourceState) (target : TargetState) : Prop where
  state : StateRel source target
  domain :
    ∀ sourceShared sourceVars,
      source = .Ok sourceShared sourceVars →
        VarsDomainWithin layout sourceVars
  defined :
    ∀ sourceShared sourceVars,
      source = .Ok sourceShared sourceVars →
        VarsDefinedOn layout sourceVars

namespace ScopedStateRel

/-- The scoped relation depends only on the set of visible names, not their
list order. This is useful at call entry, where Yul and Functions initialize
returns and parameters in opposite traversal orders. -/
theorem relayout
    {left right : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel left source target)
    (hNames : ∀ name, name ∈ left ↔ name ∈ right) :
    ScopedStateRel right source target := by
  refine ⟨hRel.state, ?_, ?_⟩
  · intro sourceShared sourceVars hSource name value hLookup
    exact (hNames name).mp
      (hRel.domain sourceShared sourceVars hSource name value hLookup)
  · intro sourceShared sourceVars hSource name hName
    exact hRel.defined sourceShared sourceVars hSource name
      ((hNames name).mpr hName)

theorem restrictTarget
    {layout scope : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope) :
    StateRel source (target.restrictTo scope) := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  refine ⟨sourceShared, sourceVars, hSource, by simpa, ?_⟩
  intro name value hLookup
  have hLayout : name ∈ layout :=
    hRel.domain sourceShared sourceVars hSource name value hLookup
  have hScope : name ∈ scope := hSubset name hLayout
  simpa [Locals.Source.State.restrictTo,
    Locals.Source.Store.restrictTo, hScope] using
    hVars name value hLookup

/-- Restrict both sides to corresponding source and target control scopes.
The source scope store contributes only its domain; values are retained from
the current source state, exactly as Yul lexical restriction specifies. -/
theorem restrictBoth
    {current retained targetScope : List Functions.Name}
    {sourceScope : EvmYul.Yul.VarStore}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel current source target)
    (hScopeDomain : VarsDomainWithin retained sourceScope)
    (hScopeDefined : VarsDefinedOn retained sourceScope)
    (hRetained : ∀ name, name ∈ retained → name ∈ current)
    (hTargetScope : ∀ name, name ∈ retained → name ∈ targetScope) :
    ScopedStateRel retained
      (source.restrictStoreTo sourceScope)
      (target.restrictTo targetScope) := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  let restrictedSource :=
    EvmYul.Yul.State.restrictVarStore sourceVars sourceScope
  refine
    { state := ?_
      domain := ?_
      defined := ?_ }
  · refine ⟨sourceShared, restrictedSource, rfl, ?_, ?_⟩
    · simpa [Locals.Source.State.restrictTo] using hShared
    · intro name value hLookup
      cases hScopeLookup : sourceScope.lookup name with
      | none =>
          have hNone := VarStoreRestriction.lookup_restrict_of_none
            sourceVars sourceScope name hScopeLookup
          change restrictedSource.lookup name = some value at hLookup
          simp [restrictedSource, hNone] at hLookup
      | some scopeValue =>
          have hSourceLookup := VarStoreRestriction.lookup_restrict_of_some
            sourceVars sourceScope name hScopeLookup
          have hRetainedName : name ∈ retained :=
            hScopeDomain name scopeValue hScopeLookup
          have hTargetName : name ∈ targetScope :=
            hTargetScope name hRetainedName
          change restrictedSource.lookup name = some value at hLookup
          change
            (EvmYul.Yul.State.restrictVarStore
              sourceVars sourceScope).lookup name = some value at hLookup
          rw [hSourceLookup] at hLookup
          simpa [Locals.Source.State.restrictTo,
            Locals.Source.Store.restrictTo, hTargetName] using
            hVars name value hLookup
  · intro finalShared finalVars hFinal name value hLookup
    cases hFinal
    cases hScopeLookup : sourceScope.lookup name with
    | none =>
        have hNone := VarStoreRestriction.lookup_restrict_of_none
          sourceVars sourceScope name hScopeLookup
        simp [restrictedSource, hNone] at hLookup
    | some scopeValue =>
        exact hScopeDomain name scopeValue hScopeLookup
  · intro finalShared finalVars hFinal name hName
    cases hFinal
    obtain ⟨scopeValue, hScopeLookup⟩ := hScopeDefined name hName
    obtain ⟨sourceValue, hSourceLookup⟩ :=
      hRel.defined sourceShared sourceVars rfl name (hRetained name hName)
    refine ⟨sourceValue, ?_⟩
    change restrictedSource.lookup name = some sourceValue
    change
      (EvmYul.Yul.State.restrictVarStore
        sourceVars sourceScope).lookup name = some sourceValue
    rw [VarStoreRestriction.lookup_restrict_of_some
        sourceVars sourceScope name hScopeLookup]
    exact hSourceLookup

theorem of_state_store_eq
    {layout : List Functions.Name}
    {entry finalSource : SourceState}
    {entryTarget finalTarget : TargetState}
    (hEntry : ScopedStateRel layout entry entryTarget)
    (hFinal : StateRel finalSource finalTarget)
    (hStore : finalSource.store = entry.store) :
    ScopedStateRel layout finalSource finalTarget := by
  refine ⟨hFinal, ?_, ?_⟩
  · intro finalShared finalVars hFinalSource
    rcases hEntry.state with
      ⟨entryShared, entryVars, hEntrySource, _hShared, _hVars⟩
    have hVarsEq : finalVars = entryVars := by
      simpa [hFinalSource, hEntrySource] using hStore
    simpa [hVarsEq] using
      hEntry.domain entryShared entryVars hEntrySource
  · intro finalShared finalVars hFinalSource
    rcases hEntry.state with
      ⟨entryShared, entryVars, hEntrySource, _hShared, _hVars⟩
    have hVarsEq : finalVars = entryVars := by
      simpa [hFinalSource, hEntrySource] using hStore
    simpa [hVarsEq] using
      hEntry.defined entryShared entryVars hEntrySource

theorem declarationCheck
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    {name : EvmYul.Identifier} (hFresh : name ∉ layout) :
    EvmYul.Yul.checkDeclaration source [name] = .ok () := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
  subst source
  have hLookup : sourceVars.lookup name = none := by
    cases hValue : sourceVars.lookup name with
    | none => rfl
    | some value =>
        exact False.elim
          (hFresh (hRel.domain sourceShared sourceVars rfl
            name value hValue))
  simp [EvmYul.Yul.checkDeclaration, EvmYul.Yul.firstDuplicate?,
    EvmYul.Yul.firstDeclared?, EvmYul.Yul.State.lookup?, hLookup]

private theorem firstDuplicate?_none_of_nodup
    (names : List Functions.Name) (hNoDup : names.Nodup) :
    EvmYul.Yul.firstDuplicate? names = none := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      have hParts := List.nodup_cons.mp hNoDup
      simp [EvmYul.Yul.firstDuplicate?, hParts.1, ih hParts.2]

theorem declarationCheck_many
    {layout names : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    (hNoDup : names.Nodup)
    (hFresh : ∀ name, name ∈ names → name ∉ layout) :
    EvmYul.Yul.checkDeclaration source names = .ok () := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
  subst source
  have hDeclared :
      EvmYul.Yul.firstDeclared? (.Ok sourceShared sourceVars) names = none := by
    unfold EvmYul.Yul.firstDeclared?
    apply List.find?_eq_none.mpr
    intro name hMem
    have hLookup : sourceVars.lookup name = none := by
      cases hValue : sourceVars.lookup name with
      | none => rfl
      | some value =>
          exact False.elim
            (hFresh name hMem
              (hRel.domain sourceShared sourceVars rfl
                name value hValue))
    simp [EvmYul.Yul.State.lookup?, hLookup]
  simp [EvmYul.Yul.checkDeclaration,
    firstDuplicate?_none_of_nodup names hNoDup, hDeclared]

theorem assignmentCheck
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    {name : EvmYul.Identifier} (hName : name ∈ layout) :
    EvmYul.Yul.checkAssignment source [name] = .ok () := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
  subst source
  obtain ⟨value, hLookup⟩ :=
    hRel.defined sourceShared sourceVars rfl name hName
  simp [EvmYul.Yul.checkAssignment, EvmYul.Yul.firstDuplicate?,
    EvmYul.Yul.firstUndeclared?, EvmYul.Yul.State.lookup?, hLookup]

theorem assignmentCheck_many
    {layout names : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    (hNoDup : names.Nodup)
    (hVisible : ∀ name, name ∈ names → name ∈ layout) :
    EvmYul.Yul.checkAssignment source names = .ok () := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
  subst source
  have hUndeclared :
      EvmYul.Yul.firstUndeclared? (.Ok sourceShared sourceVars) names = none := by
    unfold EvmYul.Yul.firstUndeclared?
    apply List.find?_eq_none.mpr
    intro name hMem
    obtain ⟨value, hLookup⟩ :=
      hRel.defined sourceShared sourceVars rfl name
        (hVisible name hMem)
    simp [EvmYul.Yul.State.lookup?, hLookup]
  simp [EvmYul.Yul.checkAssignment,
    firstDuplicate?_none_of_nodup names hNoDup, hUndeclared]

theorem targetContains
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    {name : Functions.Name} (hName : name ∈ layout) :
    target.vars.contains name = true := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, hVars⟩
  obtain ⟨value, hLookup⟩ :=
    hRel.defined sourceShared sourceVars hSource name hName
  have hTarget : target.vars name = some value := hVars name value hLookup
  simp [Locals.Source.Store.contains, hTarget]

/-- Inserting a compiler-private target local preserves the source-visible
scoped relation when freshness excludes every source variable in the layout. -/
theorem insert_private
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    {name : Functions.Name} (hFresh : name ∉ layout)
    (value : Word) :
    ScopedStateRel layout source (target.insert name value) := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  refine
    { state := ⟨sourceShared, sourceVars, hSource, ?_, ?_⟩
      domain := hRel.domain
      defined := hRel.defined }
  · simpa [Locals.Source.State.insert] using hShared
  · intro key result hLookup
    have hKey : key ≠ name := by
      intro hEq
      subst key
      exact hFresh
        (hRel.domain sourceShared sourceVars hSource name result hLookup)
    simpa [Locals.Source.State.insert,
      Locals.Source.Store.insert_of_ne hKey] using hVars key result hLookup

theorem insertMany_private :
    ∀ {names : List Functions.Name} {values : List Word}
      {layout : List Functions.Name}
      {source : SourceState} {target : TargetState}
      {finalVars : Locals.Source.Store},
      ScopedStateRel layout source target →
      (∀ name, name ∈ names → name ∉ layout) →
      Functions.Source.Store.insertMany names values target.vars =
        some finalVars →
      ScopedStateRel layout source
        { shared := target.shared, vars := finalVars }
  | [], [], _layout, _source, _target, finalVars,
      hRel, _hFresh, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
      subst finalVars
      exact hRel
  | [], _value :: _values, _layout, _source, _target, _finalVars,
      _hRel, _hFresh, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | _name :: _names, [], _layout, _source, _target, _finalVars,
      _hRel, _hFresh, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | name :: names, value :: values, layout, source, target, finalVars,
      hRel, hFresh, hInsert => by
      have hHeadFresh : name ∉ layout := hFresh name (by simp)
      have hTailFresh : ∀ candidate, candidate ∈ names →
          candidate ∉ layout := by
        intro candidate hMem
        exact hFresh candidate (by simp [hMem])
      have hHead := hRel.insert_private hHeadFresh value
      change
        Functions.Source.Store.insertMany names values
            (Locals.Source.Store.insert target.vars name value) =
          some finalVars at hInsert
      exact ScopedStateRel.insertMany_private
        (target := target.insert name value)
        hHead hTailFresh hInsert

theorem multifill_single_cons
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    (name : EvmYul.Identifier) (value : Word) :
    ScopedStateRel (name :: layout)
      (source.multifill [name] [value])
      (target.insert name value) := by
  refine ⟨StateRel.multifill_single hRel.state name value, ?_, ?_⟩
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  intro finalShared finalVars hFinal
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert] at hFinal
  rcases hFinal with ⟨rfl, rfl⟩
  intro key result hLookup
  by_cases hKey : key = name
  · subst key
    exact List.mem_cons_self
  · rw [Finmap.lookup_insert_of_ne sourceVars hKey] at hLookup
    exact List.mem_cons_of_mem name
      (hRel.domain sourceShared sourceVars rfl key result hLookup)
  · rcases hRel.state with
      ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
    subst source
    intro finalShared finalVars hFinal
    simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert] at hFinal
    rcases hFinal with ⟨rfl, rfl⟩
    intro key hKey
    by_cases hName : key = name
    · subst key
      exact ⟨value, by simp⟩
    · have hOld : key ∈ layout := by simpa [hName] using hKey
      obtain ⟨result, hLookup⟩ :=
        hRel.defined sourceShared sourceVars rfl key hOld
      exact ⟨result, by simpa [Finmap.lookup_insert_of_ne sourceVars hName]⟩

theorem multifill_single_visible
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    {name : EvmYul.Identifier} (hName : name ∈ layout)
    (value : Word) :
    ScopedStateRel layout
      (source.multifill [name] [value])
      (target.insert name value) := by
  refine ⟨StateRel.multifill_single hRel.state name value, ?_, ?_⟩
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  intro finalShared finalVars hFinal
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert] at hFinal
  rcases hFinal with ⟨rfl, rfl⟩
  intro key result hLookup
  by_cases hKey : key = name
  · simpa [hKey] using hName
  · rw [Finmap.lookup_insert_of_ne sourceVars hKey] at hLookup
    exact hRel.domain sourceShared sourceVars rfl key result hLookup
  · rcases hRel.state with
      ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
    subst source
    intro finalShared finalVars hFinal
    simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert] at hFinal
    rcases hFinal with ⟨rfl, rfl⟩
    intro key hKey
    by_cases hNameEq : key = name
    · subst key
      exact ⟨value, by simp⟩
    · obtain ⟨result, hLookup⟩ :=
        hRel.defined sourceShared sourceVars rfl key hKey
      exact
        ⟨result, by
          simpa [Finmap.lookup_insert_of_ne sourceVars hNameEq] using hLookup⟩

/-- A fresh, duplicate-free source multifill agrees with the ordinary
Functions `insertMany`, despite their opposite insertion traversals. -/
theorem multifill_insertMany :
    ∀ {names : List Functions.Name} {values : List Word}
      {layout : List Functions.Name}
      {source : SourceState} {target : TargetState}
      {finalVars : Locals.Source.Store},
      ScopedStateRel layout source target →
      names.Nodup →
      (∀ name, name ∈ names → name ∉ layout) →
      Functions.Source.Store.insertMany names values target.vars =
        some finalVars →
      ScopedStateRel (names ++ layout)
        (source.multifill names values)
        { shared := target.shared, vars := finalVars }
  | [], [], layout, source, target, finalVars,
      hRel, _hNodup, _hFresh, hInsert => by
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      simp [Functions.Source.Store.insertMany] at hInsert
      subst finalVars
      simpa [EvmYul.Yul.State.multifill] using hRel
  | [], _value :: _values, _layout, _source, _target, _finalVars,
      _hRel, _hNodup, _hFresh, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | _name :: _names, [], _layout, _source, _target, _finalVars,
      _hRel, _hNodup, _hFresh, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | name :: names, value :: values, layout, source, target, finalVars,
      hRel, hNodup, hFresh, hInsert => by
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hParts := List.nodup_cons.mp hNodup
      have hLength : values.length = names.length := by
        have hAllLength :=
          Functions.Source.Store.insertMany_length hInsert
        simpa using hAllLength
      obtain ⟨tailVars, hTailInsert⟩ :=
        Functions.Source.Store.insertMany_exists_of_length
          (store := target.vars) hLength
      have hTailFresh :
          ∀ candidate, candidate ∈ names → candidate ∉ layout := by
        intro candidate hMem
        exact hFresh candidate (by simp [hMem])
      have hTailRel :=
        multifill_insertMany hRel hParts.2 hTailFresh hTailInsert
      have hTargetInsert :
          Functions.Source.Store.insertMany names values
              (Locals.Source.Store.insert target.vars name value) =
            some (Locals.Source.Store.insert tailVars name value) :=
        Functions.Source.Store.insertMany_commute_insert_of_not_mem
          hTailInsert hParts.1
      have hTargetEq :
          finalVars = Locals.Source.Store.insert tailVars name value := by
        change
          Functions.Source.Store.insertMany names values
              (Locals.Source.Store.insert target.vars name value) =
            some finalVars at hInsert
        rw [hTargetInsert] at hInsert
        exact Option.some.inj hInsert.symm
      subst finalVars
      have hHeadRel :=
        hTailRel.multifill_single_cons name value
      have hSourceEq :
          (EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
              (name :: names) (value :: values) =
            ((EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
                names values).multifill [name] [value] := by
        rcases hTailRel.state with
          ⟨tailShared, tailSourceVars, hTailSource, _hShared, _hVars⟩
        change
          ((EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
              names values).insert name value =
            ((EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
              names values).multifill [name] [value]
        rw [hTailSource]
        rfl
      rw [hSourceEq]
      simpa [List.cons_append, Locals.Source.State.insert,
        Locals.Source.Store.insert] using hHeadRel

/-- Updating duplicate-free source-visible names agrees with ordinary
Functions insertion while preserving the same lexical domain. -/
theorem multifill_insertMany_visible :
    ∀ {names : List Functions.Name} {values : List Word}
      {layout : List Functions.Name}
      {source : SourceState} {target : TargetState}
      {finalVars : Locals.Source.Store},
      ScopedStateRel layout source target →
      names.Nodup →
      (∀ name, name ∈ names → name ∈ layout) →
      Functions.Source.Store.insertMany names values target.vars =
        some finalVars →
      ScopedStateRel layout
        (source.multifill names values)
        { shared := target.shared, vars := finalVars }
  | [], [], layout, source, target, finalVars,
      hRel, _hNodup, _hVisible, hInsert => by
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      simp [Functions.Source.Store.insertMany] at hInsert
      subst finalVars
      simpa [EvmYul.Yul.State.multifill] using hRel
  | [], _value :: _values, _layout, _source, _target, _finalVars,
      _hRel, _hNodup, _hVisible, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | _name :: _names, [], _layout, _source, _target, _finalVars,
      _hRel, _hNodup, _hVisible, hInsert => by
      simp [Functions.Source.Store.insertMany] at hInsert
  | name :: names, value :: values, layout, source, target, finalVars,
      hRel, hNodup, hVisible, hInsert => by
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hParts := List.nodup_cons.mp hNodup
      have hLength : values.length = names.length := by
        have hAllLength :=
          Functions.Source.Store.insertMany_length hInsert
        simpa using hAllLength
      obtain ⟨tailVars, hTailInsert⟩ :=
        Functions.Source.Store.insertMany_exists_of_length
          (store := target.vars) hLength
      have hTailVisible :
          ∀ candidate, candidate ∈ names → candidate ∈ layout := by
        intro candidate hMem
        exact hVisible candidate (by simp [hMem])
      have hTailRel :=
        multifill_insertMany_visible hRel hParts.2 hTailVisible hTailInsert
      have hTargetInsert :
          Functions.Source.Store.insertMany names values
              (Locals.Source.Store.insert target.vars name value) =
            some (Locals.Source.Store.insert tailVars name value) :=
        Functions.Source.Store.insertMany_commute_insert_of_not_mem
          hTailInsert hParts.1
      have hTargetEq :
          finalVars = Locals.Source.Store.insert tailVars name value := by
        change
          Functions.Source.Store.insertMany names values
              (Locals.Source.Store.insert target.vars name value) =
            some finalVars at hInsert
        rw [hTargetInsert] at hInsert
        exact Option.some.inj hInsert.symm
      subst finalVars
      have hHeadRel := hTailRel.multifill_single_visible
        (hVisible name (by simp)) value
      have hSourceEq :
          (EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
              (name :: names) (value :: values) =
            ((EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
                names values).multifill [name] [value] := by
        rcases hTailRel.state with
          ⟨tailShared, tailSourceVars, hTailSource, _hShared, _hVars⟩
        change
          ((EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
              names values).insert name value =
            ((EvmYul.Yul.State.Ok sourceShared sourceVars).multifill
              names values).multifill [name] [value]
        rw [hTailSource]
        rfl
      rw [hSourceEq]
      simpa [Locals.Source.State.insert,
        Locals.Source.Store.insert] using hHeadRel

theorem zeroFill_insertMany
    {layout names : List Functions.Name}
    {source : SourceState} {target : TargetState}
    {finalVars : Locals.Source.Store}
    (hRel : ScopedStateRel layout source target)
    (hNoDup : names.Nodup)
    (hFresh : ∀ name, name ∈ names → name ∉ layout)
    (hInsert :
      Functions.Source.Store.insertMany names
          (names.map fun _name => Functions.Source.zero)
          target.vars = some finalVars) :
    ScopedStateRel (names ++ layout)
      (source.zeroFill names)
      { shared := target.shared, vars := finalVars } := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  rw [Yul.InteractionSemantics.State.zeroFill_eq_multifill_zero]
  exact multifill_insertMany hRel hNoDup hFresh hInsert

/-- Canonical Yul and Functions call-frame initialization agree for a
duplicate-free function signature. -/
theorem initcall
    {source : SourceState} {target : TargetState}
    {params returns : List Functions.Name} {args : List Word}
    {paramStore : Locals.Source.Store}
    (hRel : StateRel source target)
    (hSignature : (returns ++ params).Nodup)
    (hParams :
      Functions.Source.Store.insertMany params args
          Locals.Source.Store.empty = some paramStore) :
    ScopedStateRel (returns ++ params)
      (EvmYul.Yul.State.mkOk (source.initcall params returns args))
      { shared := target.shared
        vars := Functions.Source.Store.initReturns returns paramStore } := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, _hVars⟩
  subst source
  have hSignatureParts := List.nodup_append.mp hSignature
  have hReturnsNodup : returns.Nodup := hSignatureParts.1
  have hParamsNodup : params.Nodup := hSignatureParts.2.1
  have hParamsFresh :
      ∀ name, name ∈ params → name ∉ returns := by
    intro name hParam hReturn
    exact hSignatureParts.2.2 name hReturn name hParam rfl
  let sourceEmpty : SourceState := .Ok sourceShared default
  let targetEmpty : TargetState :=
    { shared := target.shared, vars := Locals.Source.Store.empty }
  have hEmpty : ScopedStateRel [] sourceEmpty targetEmpty := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨sourceShared, default, rfl, by simpa [targetEmpty], VarsRel.empty⟩
    · intro shared vars hState name value hLookup
      simp [sourceEmpty] at hState
      rcases hState with ⟨rfl, rfl⟩
      change (none : Option Word) = some value at hLookup
      contradiction
    · intro shared vars hState name hName
      simp at hName
  have hReturnsInsert :
      Functions.Source.Store.insertMany returns
          (returns.map fun _name => Functions.Source.zero)
          targetEmpty.vars =
        some (Functions.Source.Store.initReturns returns
          Locals.Source.Store.empty) := by
    simpa [targetEmpty] using
      (Functions.Source.Store.insertMany_zero_eq_initReturns
        returns Locals.Source.Store.empty)
  have hReturns := hEmpty.zeroFill_insertMany hReturnsNodup
    (by simp) hReturnsInsert
  have hParamsAfterReturns :
      Functions.Source.Store.insertMany params args
          (Functions.Source.Store.initReturns returns
            Locals.Source.Store.empty) =
        some (Functions.Source.Store.initReturns returns paramStore) :=
    Functions.Source.Store.insertMany_initReturns_commute
      hParams (by
        intro name hReturn hParam
        exact hSignatureParts.2.2 name hReturn name hParam rfl)
  have hFrame := hReturns.multifill_insertMany hParamsNodup
    (by
      intro name hMem
      simpa using hParamsFresh name hMem)
    hParamsAfterReturns
  have hFrame' := hFrame.relayout (right := returns ++ params) (by
    intro name
    simp [or_comm])
  have hMkOk :
      EvmYul.Yul.State.mkOk
          (((.Ok sourceShared default : SourceState).zeroFill returns).multifill
            params args) =
        ((.Ok sourceShared default : SourceState).zeroFill returns).multifill
          params args := by
    rcases hFrame'.state with
      ⟨frameShared, frameVars, hFrameSource, _hShared, _hVars⟩
    simp [sourceEmpty] at hFrameSource
    rw [hFrameSource]
    rfl
  simpa [sourceEmpty, targetEmpty, EvmYul.Yul.State.initcall,
    EvmYul.Yul.State.setStore, hMkOk] using hFrame'

/-- Return locals can be read in source order from a related function frame. -/
theorem lookupMany
    {layout names : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    (hSubset : ∀ name, name ∈ names → name ∈ layout) :
    Functions.Source.Store.lookupMany names target.vars =
      some (names.map source.lookup!) := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, hVars⟩
  subst source
  induction names with
  | nil => rfl
  | cons name rest ih =>
      obtain ⟨value, hLookup⟩ :=
        hRel.defined sourceShared sourceVars rfl name
          (hSubset name (by simp))
      have hTarget : target.vars name = some value :=
        hVars name value hLookup
      have hTail := ih (fun candidate hMem =>
        hSubset candidate (by simp [hMem]))
      simp [Functions.Source.Store.lookupMany, hTarget, hTail,
        EvmYul.Yul.State.lookup!, EvmYul.Yul.State.lookup?, hLookup]

/-- Restore caller locals after a returned function body while retaining the
body's shared-state effects. -/
theorem restore_call_state
    {layout : List Functions.Name}
    {callerSource bodySource : SourceState}
    {callerTarget bodyTarget : TargetState}
    (hCaller : StateRel callerSource callerTarget)
    (hBody : ScopedStateRel layout bodySource.reviveJump bodyTarget) :
    StateRel
      ((bodySource.reviveJump.overwrite? callerSource).setStore callerSource)
      { shared := bodyTarget.shared, vars := callerTarget.vars } := by
  rcases hCaller with
    ⟨callerShared, callerVars, hCallerSource,
      _hCallerShared, hCallerVars⟩
  rcases hBody.state with
    ⟨bodyShared, bodyVars, hBodySource, hBodyShared,
      _hBodyVars⟩
  subst callerSource
  refine ⟨bodyShared, callerVars, ?_, hBodyShared, hCallerVars⟩
  simp [hBodySource, EvmYul.Yul.State.overwrite?,
    EvmYul.Yul.State.setStore]

/-- Scoped caller restoration preserves the caller's exact visible domain. -/
theorem restore_call
    {callerLayout bodyLayout : List Functions.Name}
    {callerSource bodySource : SourceState}
    {callerTarget bodyTarget : TargetState}
    (hCaller : ScopedStateRel callerLayout callerSource callerTarget)
    (hBody : ScopedStateRel bodyLayout bodySource.reviveJump bodyTarget) :
    ScopedStateRel callerLayout
      ((bodySource.reviveJump.overwrite? callerSource).setStore callerSource)
      { shared := bodyTarget.shared, vars := callerTarget.vars } := by
  refine ⟨restore_call_state hCaller.state hBody, ?_, ?_⟩
  · rcases hCaller.state with
      ⟨callerShared, callerVars, hCallerSource,
        _hCallerShared, _hCallerVars⟩
    rcases hBody.state with
      ⟨bodyShared, bodyVars, hBodySource,
        _hBodyShared, _hBodyVars⟩
    subst callerSource
    intro finalShared finalVars hFinal
    simp [hBodySource, EvmYul.Yul.State.overwrite?,
      EvmYul.Yul.State.setStore] at hFinal
    rcases hFinal with ⟨rfl, rfl⟩
    exact hCaller.domain callerShared callerVars rfl
  · rcases hCaller.state with
      ⟨callerShared, callerVars, hCallerSource,
        _hCallerShared, _hCallerVars⟩
    rcases hBody.state with
      ⟨bodyShared, bodyVars, hBodySource,
        _hBodyShared, _hBodyVars⟩
    subst callerSource
    intro finalShared finalVars hFinal
    simp [hBodySource, EvmYul.Yul.State.overwrite?,
      EvmYul.Yul.State.setStore] at hFinal
    rcases hFinal with ⟨rfl, rfl⟩
    exact hCaller.defined callerShared callerVars rfl

end ScopedStateRel

/-- Agreement between imported Yul checkpoints and canonical Functions
control outcomes. Yul's historical `OutOfFuel` state is not a terminal
control outcome and therefore relates to no Functions mode. -/
def ModeRel (source : SourceState)
    (target : Functions.InteractionSemantics.Outcome) : Prop :=
  match source, target.mode with
  | .Ok _ _, .regular => True
  | .Checkpoint (.Break _ _), .brk => True
  | .Checkpoint (.Continue _ _), .cont => True
  | .Checkpoint (.Leave _ _), .leave => True
  | _, _ => False

namespace ModeRel

theorem target_nonregular_source_checkpoint
    {source : SourceState}
    {target : Functions.InteractionSemantics.Outcome}
    (hMode : ModeRel source target)
    (hNonregular : target.mode ≠ .regular) :
    ∃ jump, source = .Checkpoint jump := by
  cases source with
  | Ok shared vars =>
      cases hTarget : target.mode <;>
        simp [ModeRel, hTarget] at hMode hNonregular
  | OutOfFuel =>
      cases hTarget : target.mode <;>
        simp [ModeRel, hTarget] at hMode
  | Checkpoint jump => exact ⟨jump, rfl⟩

end ModeRel

/-- Outcome-indexed adjacent state relation. Checkpoint payloads are revived
only for relating their shared state and visible locals; `ModeRel` retains
the exact control destination. -/
structure OutcomeRel (source : SourceState)
    (target : Functions.InteractionSemantics.Outcome) : Prop where
  mode : ModeRel source target
  state : StateRel source.reviveJump target.state

namespace OutcomeRel

theorem regular
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    OutcomeRel source
      (Functions.Source.Effectful.Outcome.regular target) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  exact ⟨trivial, ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩⟩

theorem brk
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : StateRel (.Ok sourceShared sourceVars) target) :
    OutcomeRel (.Checkpoint (.Break sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.brk target) :=
  ⟨trivial, hRel⟩

theorem cont
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : StateRel (.Ok sourceShared sourceVars) target) :
    OutcomeRel (.Checkpoint (.Continue sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.cont target) :=
  ⟨trivial, hRel⟩

theorem leave
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : StateRel (.Ok sourceShared sourceVars) target) :
    OutcomeRel (.Checkpoint (.Leave sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.leave target) :=
  ⟨trivial, hRel⟩

end OutcomeRel

/-- Outcome relation retaining the source-only lexical domain required by the
next adjacent statement. -/
structure ScopedOutcomeRel (layout : List Functions.Name)
    (source : SourceState)
    (target : Functions.InteractionSemantics.Outcome) : Prop where
  outcome : OutcomeRel source target
  domain :
    ∀ sourceShared sourceVars,
      source.reviveJump = .Ok sourceShared sourceVars →
        VarsDomainWithin layout sourceVars
  defined :
    ∀ sourceShared sourceVars,
      source.reviveJump = .Ok sourceShared sourceVars →
        VarsDefinedOn layout sourceVars

namespace ScopedOutcomeRel

/-- Forget the control tag while retaining the exact revived function-frame
state and lexical domain. -/
theorem revived_state
    {layout : List Functions.Name}
    {source : SourceState}
    {target : Functions.InteractionSemantics.Outcome}
    (hRel : ScopedOutcomeRel layout source target) :
    ScopedStateRel layout source.reviveJump target.state :=
  ⟨hRel.outcome.state, hRel.domain, hRel.defined⟩

/-- A related regular Functions outcome exposes the scoped Yul state needed
by the next statement in a source block. -/
theorem of_regular_target
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedOutcomeRel layout source
      (Functions.Source.Effectful.Outcome.regular target)) :
    ScopedStateRel layout source target := by
  cases source with
  | Ok sourceShared sourceVars =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using hRel.outcome.state
      · intro finalShared finalVars hSource
        cases hSource
        exact hRel.domain sourceShared sourceVars rfl
      · intro finalShared finalVars hSource
        cases hSource
        exact hRel.defined sourceShared sourceVars rfl
  | OutOfFuel =>
      have hImpossible := hRel.outcome.mode
      simp [ModeRel] at hImpossible
  | Checkpoint checkpoint =>
      cases checkpoint <;>
        have hImpossible := hRel.outcome.mode <;>
        simp [ModeRel] at hImpossible

theorem regular
    {layout : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target) :
    ScopedOutcomeRel layout source
      (Functions.Source.Effectful.Outcome.regular target) := by
  refine ⟨OutcomeRel.regular hRel.state, ?_, ?_⟩
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  intro finalShared finalVars hFinal
  cases hFinal
  exact hRel.domain sourceShared sourceVars rfl
  · rcases hRel.state with
      ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
    subst source
    intro finalShared finalVars hFinal
    cases hFinal
    exact hRel.defined sourceShared sourceVars rfl

theorem brk_restrict
    {layout scope : List Functions.Name}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : ScopedStateRel layout (.Ok sourceShared sourceVars) target)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope) :
    ScopedOutcomeRel layout (.Checkpoint (.Break sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.brk
        (target.restrictTo scope)) := by
  refine
    ⟨OutcomeRel.brk (ScopedStateRel.restrictTarget hRel hSubset), ?_, ?_⟩
  intro finalShared finalVars hFinal
  cases hFinal
  exact hRel.domain sourceShared sourceVars rfl
  · intro finalShared finalVars hFinal
    cases hFinal
    exact hRel.defined sourceShared sourceVars rfl

theorem cont_restrict
    {layout scope : List Functions.Name}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : ScopedStateRel layout (.Ok sourceShared sourceVars) target)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope) :
    ScopedOutcomeRel layout
      (.Checkpoint (.Continue sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.cont
        (target.restrictTo scope)) := by
  refine
    ⟨OutcomeRel.cont (ScopedStateRel.restrictTarget hRel hSubset), ?_, ?_⟩
  intro finalShared finalVars hFinal
  cases hFinal
  exact hRel.domain sourceShared sourceVars rfl
  · intro finalShared finalVars hFinal
    cases hFinal
    exact hRel.defined sourceShared sourceVars rfl

theorem leave_restrict
    {layout scope : List Functions.Name}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : ScopedStateRel layout (.Ok sourceShared sourceVars) target)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope) :
    ScopedOutcomeRel layout (.Checkpoint (.Leave sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.leave
        (target.restrictTo scope)) := by
  refine
    ⟨OutcomeRel.leave (ScopedStateRel.restrictTarget hRel hSubset), ?_, ?_⟩
  intro finalShared finalVars hFinal
  cases hFinal
  exact hRel.domain sourceShared sourceVars rfl
  · intro finalShared finalVars hFinal
    cases hFinal
    exact hRel.defined sourceShared sourceVars rfl

end ScopedOutcomeRel

/-- Yul exposes terminal control as a distinguished failure, while Functions
keeps it as an outcome. The terminal syntax theorem chooses the exact
non-revert halt kind; this relation preserves the terminal state and permits
that representation change without treating runtime errors as outcomes. -/
inductive TerminalFailureRel :
    Yul.InteractionSemantics.Failure →
      Functions.InteractionSemantics.Outcome → Prop where
  | stop
      {source : SourceState} {value : Word} {target : TargetState}
      (state : TerminalStateRel source target) :
      TerminalFailureRel
        { exception := .YulHalt source value, state := source }
        (Functions.Source.Effectful.Outcome.halt .stop target)
  | return_
      {source : SourceState} {value : Word} {target : TargetState}
      (state : TerminalStateRel source target) :
      TerminalFailureRel
        { exception := .YulHalt source value, state := source }
        (Functions.Source.Effectful.Outcome.halt .return target)
  | selfdestruct
      {source : SourceState} {value : Word} {target : TargetState}
      (state : TerminalStateRel source target) :
      TerminalFailureRel
        { exception := .YulHalt source value, state := source }
        (Functions.Source.Effectful.Outcome.halt .selfdestruct target)
  | revert
      {source : SourceState} {target : TargetState}
      (state : TerminalStateRel source target) :
      TerminalFailureRel
        { exception := .Revert source, state := source }
        (Functions.Source.Effectful.Outcome.halt .revert target)

end FunctionsInteractionRelation
end Yul
end EvmCompiler
