import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Yul.InteractionSemantics

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

end FunctionsInteractionRelation
end Yul
end EvmCompiler
