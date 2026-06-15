import EvmCompiler.Locals.SourceSemantics
import EvmCompiler.Simulation.ResourceReplay
import EvmYul.Yul.Interpreter
import EvmYul.Yul.StateOps

namespace EvmCompiler
namespace Yul
namespace StateRelation

abbrev Name := EvmYul.Identifier

abbrev CodeRel :=
  EvmYul.Yul.Ast.YulContract → ByteArray → Prop

def OptionRel {α β : Type} (rel : α → β → Prop) :
    Option α → Option β → Prop
  | none, none => True
  | some left, some right => rel left right
  | _, _ => False

namespace OptionRel

theorem elim_eq
    {α β γ : Type} {rel : α → β → Prop}
    {left : Option α} {right : Option β}
    (hRel : OptionRel rel left right)
    (defaultValue : γ)
    (leftValue : α → γ) (rightValue : β → γ)
    (hValue :
      ∀ {leftValue' rightValue'},
        rel leftValue' rightValue' →
          leftValue leftValue' = rightValue rightValue') :
    left.elim defaultValue leftValue =
      right.elim defaultValue rightValue := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightValue' =>
          simp [StateRelation.OptionRel] at hRel
  | some leftValue' =>
      cases right with
      | none =>
          simp [StateRelation.OptionRel] at hRel
      | some rightValue' =>
          exact hValue hRel

theorem option_eq
    {α β γ : Type} {rel : α → β → Prop}
    {left : Option α} {right : Option β}
    (hRel : OptionRel rel left right)
    (defaultValue : γ)
    (leftValue : α → γ) (rightValue : β → γ)
    (hValue :
      ∀ {leftValue' rightValue'},
        rel leftValue' rightValue' →
          leftValue leftValue' = rightValue rightValue') :
    left.option defaultValue leftValue =
      right.option defaultValue rightValue := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightValue' =>
          simp [StateRelation.OptionRel] at hRel
  | some leftValue' =>
      cases right with
      | none =>
          simp [StateRelation.OptionRel] at hRel
      | some rightValue' =>
          exact hValue hRel

end OptionRel

namespace ExecutionEnv

structure Rel (codeRel : CodeRel)
    (source : EvmYul.ExecutionEnv .Yul)
    (target : EvmYul.ExecutionEnv .EVM) : Prop where
  codeOwner : source.codeOwner = target.codeOwner
  sender : source.sender = target.sender
  sourceAddress : source.source = target.source
  weiValue : source.weiValue = target.weiValue
  calldata : source.calldata = target.calldata
  code : codeRel source.code target.code
  gasPrice : source.gasPrice = target.gasPrice
  header : source.header = target.header
  depth : source.depth = target.depth
  permission : source.perm = target.perm
  blobVersionedHashes :
    source.blobVersionedHashes = target.blobVersionedHashes
  codeImage : source.codeBytes = target.code
  codeBytes : source.codeBytes = target.codeBytes

end ExecutionEnv

namespace Account

structure Rel (codeRel : CodeRel)
    (source : EvmYul.Account .Yul)
    (target : EvmYul.Account .EVM) : Prop where
  nonce : source.nonce = target.nonce
  balance : source.balance = target.balance
  storage : source.storage = target.storage
  code : codeRel source.code target.code
  codeImage : source.codeBytes = target.code
  codeBytes : source.codeBytes = target.codeBytes
  transientStorage : source.tstorage = target.tstorage
  emptyAccount :
    source.emptyAccount = target.emptyAccount

theorem codeImage_eq
    {codeRel : CodeRel}
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hRel : Rel codeRel source target) :
    EvmYul.State.accountCodeImage source =
      EvmYul.State.accountCodeImage target := by
  simpa [EvmYul.State.accountCodeImage] using hRel.codeImage

theorem storageValue_eq
    {codeRel : CodeRel}
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hRel : Rel codeRel source target)
    (key : EvmYul.UInt256) :
    source.lookupStorage key = target.lookupStorage key := by
  simp [EvmYul.Account.lookupStorage, hRel.storage]

theorem transientStorageValue_eq
    {codeRel : CodeRel}
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hRel : Rel codeRel source target)
    (key : EvmYul.UInt256) :
    source.lookupTransientStorage key =
      target.lookupTransientStorage key := by
  simp [EvmYul.Account.lookupTransientStorage,
    hRel.transientStorage]

theorem updateStorage
    {codeRel : CodeRel}
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hRel : Rel codeRel source target)
    (key value : EvmYul.UInt256) :
    Rel codeRel
      (source.updateStorage key value)
      (target.updateStorage key value) := by
  by_cases hZero : value == (default : EvmYul.UInt256)
  all_goals
    exact
      { nonce := by
          simpa [EvmYul.Account.updateStorage, hZero] using
            hRel.nonce
        balance := by
          simpa [EvmYul.Account.updateStorage, hZero] using
            hRel.balance
        storage := by
          simp [EvmYul.Account.updateStorage, hZero, hRel.storage]
        code := by
          simpa [EvmYul.Account.updateStorage, hZero] using
            hRel.code
        codeImage := by
          simpa [EvmYul.Account.updateStorage, hZero] using
            hRel.codeImage
        codeBytes := by
          simpa [EvmYul.Account.updateStorage, hZero] using
            hRel.codeBytes
        transientStorage := by
          simpa [EvmYul.Account.updateStorage, hZero] using
            hRel.transientStorage
        emptyAccount := by
          simpa [EvmYul.Account.updateStorage, hZero,
            EvmYul.Account.emptyAccount] using hRel.emptyAccount }

theorem updateTransientStorage
    {codeRel : CodeRel}
    {source : EvmYul.Account .Yul}
    {target : EvmYul.Account .EVM}
    (hRel : Rel codeRel source target)
    (key value : EvmYul.UInt256) :
    Rel codeRel
      (source.updateTransientStorage key value)
      (target.updateTransientStorage key value) := by
  by_cases hZero : value == (default : EvmYul.UInt256)
  all_goals
    exact
      { nonce := by
          simpa [EvmYul.Account.updateTransientStorage, hZero] using
            hRel.nonce
        balance := by
          simpa [EvmYul.Account.updateTransientStorage, hZero] using
            hRel.balance
        storage := by
          simpa [EvmYul.Account.updateTransientStorage, hZero] using
            hRel.storage
        code := by
          simpa [EvmYul.Account.updateTransientStorage, hZero] using
            hRel.code
        codeImage := by
          simpa [EvmYul.Account.updateTransientStorage, hZero] using
            hRel.codeImage
        codeBytes := by
          simpa [EvmYul.Account.updateTransientStorage, hZero] using
            hRel.codeBytes
        transientStorage := by
          simp [EvmYul.Account.updateTransientStorage, hZero,
            hRel.transientStorage]
        emptyAccount := by
          simpa [EvmYul.Account.updateTransientStorage, hZero,
            EvmYul.Account.emptyAccount] using hRel.emptyAccount }

end Account

namespace AccountMap

def Rel (codeRel : CodeRel)
    (source : EvmYul.AccountMap .Yul)
    (target : EvmYul.AccountMap .EVM) : Prop :=
  ∀ address,
    OptionRel (Account.Rel codeRel)
      (source.find? address) (target.find? address)

theorem balance_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress) :
    (source.find? address).elim ⟨0⟩ (·.balance) =
      (target.find? address).elim ⟨0⟩ (·.balance) := by
  apply OptionRel.elim_eq (hRel address)
  intro sourceAccount targetAccount hAccount
  exact hAccount.balance

theorem codeImage_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress) :
    (source.find? address).option ByteArray.empty
        EvmYul.State.accountCodeImage =
      (target.find? address).option ByteArray.empty
        EvmYul.State.accountCodeImage := by
  have hLookup := hRel address
  cases hSource : source.find? address with
  | none =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          rfl
      | some targetAccount =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
  | some sourceAccount =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
      | some targetAccount =>
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          change
            EvmYul.State.accountCodeImage sourceAccount =
              EvmYul.State.accountCodeImage targetAccount
          exact Account.codeImage_eq hAccount

theorem codeSize_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress) :
    (source.find? address).option ⟨0⟩
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.State.accountCodeImage) =
      (target.find? address).option ⟨0⟩
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.State.accountCodeImage) := by
  have hLookup := hRel address
  cases hSource : source.find? address with
  | none =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          rfl
      | some targetAccount =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
  | some sourceAccount =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
      | some targetAccount =>
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          change
            EvmYul.UInt256.ofNat
                (EvmYul.State.accountCodeImage sourceAccount).size =
              EvmYul.UInt256.ofNat
                (EvmYul.State.accountCodeImage targetAccount).size
          rw [Account.codeImage_eq hAccount]

theorem dead_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress) :
    EvmYul.State.dead source address =
      EvmYul.State.dead target address := by
  unfold EvmYul.State.dead
  apply OptionRel.option_eq (hRel address)
  intro sourceAccount targetAccount hAccount
  exact hAccount.emptyAccount

theorem codeHash_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress) :
    (source.find? address).option ⟨0⟩
        (fun account =>
          EvmYul.UInt256.ofNat <|
            EvmYul.fromByteArrayBigEndian
              (ffi.KEC
                (EvmYul.State.accountCodeImage account))) =
      (target.find? address).option ⟨0⟩
        (fun account =>
          EvmYul.UInt256.ofNat <|
            EvmYul.fromByteArrayBigEndian
              (ffi.KEC
                (EvmYul.State.accountCodeImage account))) := by
  apply OptionRel.option_eq (hRel address)
  intro sourceAccount targetAccount hAccount
  rw [Account.codeImage_eq hAccount]

theorem storageValue_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) :
    (source.find? address).option ⟨0⟩
        (EvmYul.Account.lookupStorage (k := key)) =
      (target.find? address).option ⟨0⟩
        (EvmYul.Account.lookupStorage (k := key)) := by
  have hLookup := hRel address
  cases hSource : source.find? address with
  | none =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none => rfl
      | some targetAccount =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
  | some sourceAccount =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
      | some targetAccount =>
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          change
            sourceAccount.lookupStorage key =
              targetAccount.lookupStorage key
          exact Account.storageValue_eq hAccount key

theorem transientStorageValue_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) :
    (source.find? address).option ⟨0⟩
        (EvmYul.Account.lookupTransientStorage (k := key)) =
      (target.find? address).option ⟨0⟩
        (EvmYul.Account.lookupTransientStorage (k := key)) := by
  have hLookup := hRel address
  cases hSource : source.find? address with
  | none =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none => rfl
      | some targetAccount =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
  | some sourceAccount =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
      | some targetAccount =>
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          change
            sourceAccount.lookupTransientStorage key =
              targetAccount.lookupTransientStorage key
          exact Account.transientStorageValue_eq hAccount key

theorem findStorageValue_eq
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) :
    (source.find! address).storage.findD key ⟨0⟩ =
      (target.find! address).storage.findD key ⟨0⟩ := by
  have hLookup := hRel address
  cases hSource : source.find? address with
  | none =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          simp [Batteries.RBMap.find!, hSource, hTarget]
          rfl
      | some targetAccount =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
  | some sourceAccount =>
      rw [hSource] at hLookup
      cases hTarget : target.find? address with
      | none =>
          simp [StateRelation.OptionRel, hTarget] at hLookup
      | some targetAccount =>
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          simpa [Batteries.RBMap.find!, hSource, hTarget,
            EvmYul.Account.lookupStorage] using
            Account.storageValue_eq hAccount key

theorem insert
    {codeRel : CodeRel}
    {source : EvmYul.AccountMap .Yul}
    {target : EvmYul.AccountMap .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress)
    {sourceAccount : EvmYul.Account .Yul}
    {targetAccount : EvmYul.Account .EVM}
    (hAccount : Account.Rel codeRel sourceAccount targetAccount) :
    Rel codeRel
      (source.insert address sourceAccount)
      (target.insert address targetAccount) := by
  intro query
  by_cases hEq : query = address
  · subst query
    simp [Batteries.RBMap.find?_insert]
    exact hAccount
  · simp [Batteries.RBMap.find?_insert, hEq, hRel query]

end AccountMap

namespace World

structure Rel (codeRel : CodeRel)
    (source : EvmYul.State .Yul)
    (target : EvmYul.State .EVM) : Prop where
  accounts : AccountMap.Rel codeRel source.accountMap target.accountMap
  initialAccounts : source.σ₀ = target.σ₀
  totalGasUsedInBlock :
    source.totalGasUsedInBlock = target.totalGasUsedInBlock
  transactionReceipts :
    source.transactionReceipts = target.transactionReceipts
  substate : source.substate = target.substate
  executionEnv :
    ExecutionEnv.Rel codeRel source.executionEnv target.executionEnv
  blocks : source.blocks = target.blocks
  genesisBlockHeader :
    source.genesisBlockHeader = target.genesisBlockHeader
  createdAccounts : source.createdAccounts = target.createdAccounts

theorem addAccessedAccount
    {codeRel : CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress) :
    Rel codeRel
      (source.addAccessedAccount address)
      (target.addAccessedAccount address) := by
  exact
    { accounts := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.accounts
      initialAccounts := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.transactionReceipts
      substate := by
        simp [EvmYul.State.addAccessedAccount, hRel.substate]
      executionEnv := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.executionEnv
      blocks := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.genesisBlockHeader
      createdAccounts := by
        simpa [EvmYul.State.addAccessedAccount] using
          hRel.createdAccounts }

theorem addAccessedStorageKey
    {codeRel : CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : Rel codeRel source target)
    (storageKey : EvmYul.AccountAddress × EvmYul.UInt256) :
    Rel codeRel
      (source.addAccessedStorageKey storageKey)
      (target.addAccessedStorageKey storageKey) := by
  exact
    { accounts := by
        simpa [EvmYul.State.addAccessedStorageKey] using hRel.accounts
      initialAccounts := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.transactionReceipts
      substate := by
        simp [EvmYul.State.addAccessedStorageKey, hRel.substate]
      executionEnv := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.executionEnv
      blocks := by
        simpa [EvmYul.State.addAccessedStorageKey] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.genesisBlockHeader
      createdAccounts := by
        simpa [EvmYul.State.addAccessedStorageKey] using
          hRel.createdAccounts }

theorem updateAccount
    {codeRel : CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : Rel codeRel source target)
    (address : EvmYul.AccountAddress)
    {sourceAccount : EvmYul.Account .Yul}
    {targetAccount : EvmYul.Account .EVM}
    (hAccount : Account.Rel codeRel sourceAccount targetAccount) :
    Rel codeRel
      (source.updateAccount address sourceAccount)
      (target.updateAccount address targetAccount) := by
  exact
    { accounts := by
        simpa [EvmYul.State.updateAccount] using
          AccountMap.insert hRel.accounts address hAccount
      initialAccounts := by
        simpa [EvmYul.State.updateAccount] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.updateAccount] using
          hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.updateAccount] using
          hRel.transactionReceipts
      substate := by
        simpa [EvmYul.State.updateAccount] using hRel.substate
      executionEnv := by
        simpa [EvmYul.State.updateAccount] using hRel.executionEnv
      blocks := by
        simpa [EvmYul.State.updateAccount] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.updateAccount] using
          hRel.genesisBlockHeader
      createdAccounts := by
        simpa [EvmYul.State.updateAccount] using
          hRel.createdAccounts }

theorem withRefundBalance
    {codeRel : CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : Rel codeRel source target)
    (refundBalance : EvmYul.UInt256) :
    Rel codeRel
      { source with substate.refundBalance := refundBalance }
      { target with substate.refundBalance := refundBalance } := by
  exact
    { accounts := by simpa using hRel.accounts
      initialAccounts := by simpa using hRel.initialAccounts
      totalGasUsedInBlock := by simpa using hRel.totalGasUsedInBlock
      transactionReceipts := by simpa using hRel.transactionReceipts
      substate := by simp [hRel.substate]
      executionEnv := by simpa using hRel.executionEnv
      blocks := by simpa using hRel.blocks
      genesisBlockHeader := by simpa using hRel.genesisBlockHeader
      createdAccounts := by simpa using hRel.createdAccounts }

private def currentStorageValue {τ}
    (state : EvmYul.State τ)
    (owner : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) : EvmYul.UInt256 :=
  (state.accountMap.find! owner).1.storage.findD key ⟨0⟩

private def initialStorageValue {τ}
    (state : EvmYul.State τ)
    (owner : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) : EvmYul.UInt256 :=
  (state.σ₀.find? owner).option ⟨0⟩
    (fun account => account.storage.findD key ⟨0⟩)

private def sstoreRefundBalance
    (initial current new refundBalance : EvmYul.UInt256) :
    EvmYul.UInt256 :=
  let dirtyClear : ℤ :=
    if initial ≠ .ofNat 0 && current = .ofNat 0 then
      -GasConstants.Rsclear
    else if initial ≠ .ofNat 0 && new = .ofNat 0 then
      GasConstants.Rsclear
    else 0
  let dirtyReset : ℤ :=
    if initial = new && initial = .ofNat 0 then
      GasConstants.Gsset - GasConstants.Gwarmaccess
    else if initial = new && initial ≠ .ofNat 0 then
      GasConstants.Gsreset - GasConstants.Gwarmaccess
    else 0
  let refundDelta : ℤ :=
    if current ≠ new && initial = current && new = .ofNat 0 then
      GasConstants.Rsclear
    else if current ≠ new && initial ≠ current then
      dirtyClear + dirtyReset
    else 0
  match refundDelta with
  | .ofNat n => refundBalance + .ofNat n
  | .negSucc n => refundBalance - .ofNat n - ⟨1⟩

private theorem sstore_eq {τ}
    (state : EvmYul.State τ)
    (key value : EvmYul.UInt256) :
    state.sstore key value =
      let owner := state.executionEnv.codeOwner
      state.lookupAccount owner |>.option state fun account =>
        let state' :=
          state.setAccount owner (account.updateStorage key value)
            |>.addAccessedStorageKey (owner, key)
        { state' with
          substate.refundBalance :=
            sstoreRefundBalance
              (initialStorageValue state owner key)
              (currentStorageValue state owner key)
              value state.substate.refundBalance } := by
  unfold EvmYul.State.sstore
  dsimp only
  congr 1
  funext account
  congr 1
  simp [sstoreRefundBalance, initialStorageValue,
    currentStorageValue]
  have hStorage :
      (state.accountMap.find!
          state.executionEnv.codeOwner).1.storage =
        (state.accountMap.find!
          state.executionEnv.codeOwner).storage := by
    rfl
  rw [hStorage]
  cases hInitial :
      state.σ₀.find? state.executionEnv.codeOwner <;>
    simp [hInitial, Option.option] <;>
    rfl

theorem sstore
    {codeRel : CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : Rel codeRel source target)
    (key value : EvmYul.UInt256) :
    Rel codeRel
      (source.sstore key value)
      (target.sstore key value) := by
  let owner := source.executionEnv.codeOwner
  have hTargetOwner :
      target.executionEnv.codeOwner = owner := by
    simpa [owner] using hRel.executionEnv.codeOwner.symm
  have hCurrent :
      currentStorageValue source owner key =
        currentStorageValue target owner key := by
    simpa [currentStorageValue] using
      AccountMap.findStorageValue_eq hRel.accounts owner key
  have hInitial :
      initialStorageValue source owner key =
        initialStorageValue target owner key := by
    simp [initialStorageValue, hRel.initialAccounts]
  have hRefund :
      source.substate.refundBalance =
        target.substate.refundBalance := by
    simpa using congrArg EvmYul.Substate.refundBalance hRel.substate
  rw [sstore_eq, sstore_eq]
  rw [hTargetOwner]
  let newRefund : EvmYul.UInt256 :=
    sstoreRefundBalance
      (initialStorageValue source owner key)
      (currentStorageValue source owner key)
      value source.substate.refundBalance
  have hNewRefund :
      newRefund =
        sstoreRefundBalance
          (initialStorageValue target owner key)
          (currentStorageValue target owner key)
          value target.substate.refundBalance := by
    simp [newRefund, hInitial, hCurrent, hRefund]
  change
    Rel codeRel
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
              sstoreRefundBalance
                (initialStorageValue target owner key)
                (currentStorageValue target owner key)
                value target.substate.refundBalance }))
  rw [← hNewRefund]
  have hLookup := hRel.accounts owner
  cases hSource : source.lookupAccount owner with
  | none =>
      change source.accountMap.find? owner = none at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none =>
          simpa [hSource, hTarget] using hRel
      | some targetAccount =>
          change
            target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          simp [StateRelation.OptionRel] at hLookup
  | some sourceAccount =>
      change
        source.accountMap.find? owner = some sourceAccount at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none =>
          change target.accountMap.find? owner = none at hTarget
          rw [hTarget] at hLookup
          simp [StateRelation.OptionRel] at hLookup
      | some targetAccount =>
          change
            target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          simpa [hSource, hTarget, EvmYul.State.setAccount] using
            withRefundBalance
              (addAccessedStorageKey
                (updateAccount hRel owner
                  (Account.updateStorage hAccount key value))
                (owner, key))
              newRefund

theorem tstore
    {codeRel : CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : Rel codeRel source target)
    (key value : EvmYul.UInt256) :
    Rel codeRel
      (source.tstore key value)
      (target.tstore key value) := by
  let owner := source.executionEnv.codeOwner
  have hTargetOwner :
      target.executionEnv.codeOwner = owner := by
    simpa [owner] using hRel.executionEnv.codeOwner.symm
  unfold EvmYul.State.tstore
  dsimp only
  rw [hTargetOwner]
  change
    Rel codeRel
      ((source.lookupAccount owner).option source
        (fun account =>
          source.updateAccount owner
            (account.updateTransientStorage key value)))
      ((target.lookupAccount owner).option target
        (fun account =>
          target.updateAccount owner
            (account.updateTransientStorage key value)))
  have hLookup := hRel.accounts owner
  cases hSource : source.lookupAccount owner with
  | none =>
      change source.accountMap.find? owner = none at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none =>
          simpa [hSource, hTarget] using hRel
      | some targetAccount =>
          change
            target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          simp [StateRelation.OptionRel] at hLookup
  | some sourceAccount =>
      change
        source.accountMap.find? owner = some sourceAccount at hSource
      rw [hSource] at hLookup
      cases hTarget : target.lookupAccount owner with
      | none =>
          change target.accountMap.find? owner = none at hTarget
          rw [hTarget] at hLookup
          simp [StateRelation.OptionRel] at hLookup
      | some targetAccount =>
          change
            target.accountMap.find? owner = some targetAccount at hTarget
          rw [hTarget] at hLookup
          have hAccount :
              Account.Rel codeRel sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hLookup
          simpa [hSource, hTarget] using
            updateAccount hRel owner
              (Account.updateTransientStorage hAccount key value)

end World

namespace Shared

structure Rel (codeRel : CodeRel)
    (source : EvmYul.SharedState .Yul)
    (target : EvmYul.SharedState .EVM) : Prop where
  world : World.Rel codeRel source.toState target.toState
  machine : source.toMachineState = target.toMachineState

theorem withMachine
    {codeRel : CodeRel}
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : Rel codeRel source target)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    Rel codeRel
      { source with toMachineState := sourceMachine }
      { target with toMachineState := targetMachine } := by
  exact
    { world := by simpa using hRel.world
      machine := by simpa using hMachine }

theorem logOp
    {codeRel : CodeRel}
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : Rel codeRel source target)
    (address size : EvmYul.UInt256)
    (topics : Array EvmYul.UInt256) :
    Rel codeRel
      (EvmYul.SharedState.logOp address size topics source)
      (EvmYul.SharedState.logOp address size topics target) := by
  constructor
  · exact
      { accounts := by
          simpa [EvmYul.SharedState.logOp] using hRel.world.accounts
        initialAccounts := by
          simpa [EvmYul.SharedState.logOp] using
            hRel.world.initialAccounts
        totalGasUsedInBlock := by
          simpa [EvmYul.SharedState.logOp] using
            hRel.world.totalGasUsedInBlock
        transactionReceipts := by
          simpa [EvmYul.SharedState.logOp] using
            hRel.world.transactionReceipts
        substate := by
          simp [EvmYul.SharedState.logOp, hRel.world.substate,
            hRel.world.executionEnv.codeOwner, hRel.machine]
        executionEnv := by
          simpa [EvmYul.SharedState.logOp] using
            hRel.world.executionEnv
        blocks := by
          simpa [EvmYul.SharedState.logOp] using hRel.world.blocks
        genesisBlockHeader := by
          simpa [EvmYul.SharedState.logOp] using
            hRel.world.genesisBlockHeader
        createdAccounts := by
          simpa [EvmYul.SharedState.logOp] using
            hRel.world.createdAccounts }
  · simp [EvmYul.SharedState.logOp, hRel.machine]

end Shared

namespace VarStore

private theorem lookup_fold_erase_preserve_of_notMem
    (key : Name) :
    ∀ (entries : List (Sigma (fun _ : Name => Assembly.Word)))
      (store : EvmYul.Yul.VarStore),
      key ∉ entries.keys →
        (List.foldl
            (fun (store : EvmYul.Yul.VarStore)
                (entry : Sigma (fun _ : Name => Assembly.Word)) =>
              Finmap.erase entry.1 store)
            store entries).lookup key =
          store.lookup key
  | [], store, _hNotMem => rfl
  | Sigma.mk head value :: rest, store, hNotMem => by
      have hRest : key ∉ rest.keys := by
        intro hMem
        exact hNotMem (by simp [hMem])
      have hNe : key ≠ head := by
        intro hEq
        exact hNotMem (by simp [hEq])
      simp only [List.foldl_cons]
      rw [lookup_fold_erase_preserve_of_notMem key rest
        (Finmap.erase head store) hRest]
      rw [Finmap.lookup_erase_ne hNe]

private theorem lookup_fold_erase_none_of_initial_none
    (key : Name) :
    ∀ (entries : List (Sigma (fun _ : Name => Assembly.Word)))
      (store : EvmYul.Yul.VarStore),
      store.lookup key = none →
        (List.foldl
            (fun (store : EvmYul.Yul.VarStore)
                (entry : Sigma (fun _ : Name => Assembly.Word)) =>
              Finmap.erase entry.1 store)
            store entries).lookup key =
          none
  | [], _store, hNone => hNone
  | Sigma.mk head value :: rest, store, hNone => by
      simp only [List.foldl_cons]
      apply lookup_fold_erase_none_of_initial_none key rest
      by_cases hEq : key = head
      · subst key
        simp
      · rw [Finmap.lookup_erase_ne hEq]
        exact hNone

private theorem lookup_fold_erase_none_of_mem
    (key : Name) :
    ∀ (entries : List (Sigma (fun _ : Name => Assembly.Word)))
      (store : EvmYul.Yul.VarStore),
      key ∈ entries.keys →
        (List.foldl
            (fun (store : EvmYul.Yul.VarStore)
                (entry : Sigma (fun _ : Name => Assembly.Word)) =>
              Finmap.erase entry.1 store)
            store entries).lookup key =
          none
  | [], _store, hMem => by
      simp at hMem
  | Sigma.mk head value :: rest, store, hMem => by
      simp only [List.foldl_cons]
      by_cases hEq : key = head
      · subst key
        apply lookup_fold_erase_none_of_initial_none head rest
        simp
      · have hRest : key ∈ rest.keys := by
          simpa [hEq] using hMem
        exact lookup_fold_erase_none_of_mem key rest
          (Finmap.erase head store) hRest

private theorem lookup_sdiff_of_lookup_none
    (store scope : EvmYul.Yul.VarStore) (key : Name)
    (hScope : scope.lookup key = none) :
    (store.sdiff scope).lookup key = store.lookup key := by
  induction scope using Finmap.induction_on with
  | H alist =>
      rw [Finmap.sdiff, Finmap.foldl]
      apply lookup_fold_erase_preserve_of_notMem
      have hNotMem : key ∉ alist := by
        rw [← AList.lookup_eq_none]
        simpa using hScope
      simpa [AList.mem_keys, AList.keys] using hNotMem

private theorem lookup_sdiff_of_lookup_some
    (store scope : EvmYul.Yul.VarStore) (key : Name)
    {value : Assembly.Word}
    (hScope : scope.lookup key = some value) :
    (store.sdiff scope).lookup key = none := by
  induction scope using Finmap.induction_on with
  | H alist =>
      rw [Finmap.sdiff, Finmap.foldl]
      apply lookup_fold_erase_none_of_mem
      have hMem : key ∈ alist := by
        have hLookup : AList.lookup key alist = some value := by
          simpa using hScope
        have hSome : (AList.lookup key alist).isSome := by
          simp [hLookup]
        exact AList.lookup_isSome.mp hSome
      simpa [AList.mem_keys, AList.keys] using hMem

theorem lookup_restrict_of_some
    (store scope : EvmYul.Yul.VarStore) (key : Name)
    {value : Assembly.Word}
    (hScope : scope.lookup key = some value) :
    (EvmYul.Yul.State.restrictVarStore store scope).lookup key =
      store.lookup key := by
  unfold EvmYul.Yul.State.restrictVarStore
  have hInner :
      (store.sdiff scope).lookup key = none :=
    lookup_sdiff_of_lookup_some store scope key hScope
  exact lookup_sdiff_of_lookup_none store (store.sdiff scope) key hInner

theorem lookup_restrict_of_none
    (store scope : EvmYul.Yul.VarStore) (key : Name)
    (hScope : scope.lookup key = none) :
    (EvmYul.Yul.State.restrictVarStore store scope).lookup key = none := by
  unfold EvmYul.Yul.State.restrictVarStore
  have hInner :
      (store.sdiff scope).lookup key = store.lookup key :=
    lookup_sdiff_of_lookup_none store scope key hScope
  cases hStore : store.lookup key with
  | none =>
      simpa [hInner, hStore] using
        lookup_sdiff_of_lookup_none store (store.sdiff scope) key (by
          simpa [hInner, hStore])
  | some value =>
      have hInnerSome :
          (store.sdiff scope).lookup key = some value := by
        simpa [hStore] using hInner
      simpa using
        lookup_sdiff_of_lookup_some store (store.sdiff scope) key hInnerSome

end VarStore

namespace Vars

def Rel (source : EvmYul.Yul.VarStore)
    (target : Locals.Source.Store) : Prop :=
  ∀ name value, source.lookup name = some value →
    target name = some value

/-!
`Rel` preserves every source-visible binding while permitting
compiler-private target temporaries. `DomainExact` remains source-only: it is
the fact needed to justify imported Yul declaration and assignment checks and
to prove that a fresh compiler name is hidden from the source.
-/

def ScopedRel (layout : List Name) (source : EvmYul.Yul.VarStore)
    (target : Locals.Source.Store) : Prop :=
  ∀ name, name ∈ layout → source.lookup name = target name

def DomainExact (layout : List Name)
    (source : EvmYul.Yul.VarStore) : Prop :=
  ∀ name, (source.lookup name).isSome = true ↔ name ∈ layout

theorem empty :
    Rel (default : EvmYul.Yul.VarStore) Locals.Source.Store.empty := by
  intro name value hLookup
  change (none : Option Assembly.Word) = some value at hLookup
  cases hLookup

theorem scoped_of_rel {layout : List Name}
    {source : EvmYul.Yul.VarStore} {target : Locals.Source.Store}
    (hRel : Rel source target)
    (hDomain : DomainExact layout source) :
    ScopedRel layout source target := by
  intro name hMem
  have hSome : (source.lookup name).isSome = true :=
    (hDomain name).mpr hMem
  cases hLookup : source.lookup name with
  | none =>
      simp [hLookup] at hSome
  | some value =>
      exact (hRel name value hLookup).symm

theorem scoped_of_subset
    {outer inner : List Name}
    {source : EvmYul.Yul.VarStore} {target : Locals.Source.Store}
    (hRel : ScopedRel outer source target)
    (hSubset : ∀ name, name ∈ inner → name ∈ outer) :
    ScopedRel inner source target := by
  intro name hMem
  exact hRel name (hSubset name hMem)

theorem scoped_empty :
    ScopedRel [] (default : EvmYul.Yul.VarStore)
      Locals.Source.Store.empty := by
  intro name hMem
  simp at hMem

theorem domainExact_empty :
    DomainExact [] (default : EvmYul.Yul.VarStore) := by
  intro name
  change
    (Finmap.lookup name (∅ : EvmYul.Yul.VarStore)).isSome = true ↔
      name ∈ ([] : List Name)
  simp

theorem insert
    {source : EvmYul.Yul.VarStore} {target : Locals.Source.Store}
    (hRel : Rel source target) (name : EvmYul.Identifier)
    (value : Assembly.Word) :
    Rel (source.insert name value)
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

theorem insert_target_hidden
    {source : EvmYul.Yul.VarStore} {target : Locals.Source.Store}
    (hRel : Rel source target) {name : Name} {value : Assembly.Word}
    (hHidden : source.lookup name = none) :
    Rel source (Locals.Source.Store.insert target name value) := by
  intro key result hLookup
  have hNe : key ≠ name := by
    intro hEq
    subst key
    rw [hHidden] at hLookup
    contradiction
  rw [Locals.Source.Store.insert_of_ne hNe]
  exact hRel key result hLookup

theorem scoped_insert_hidden
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {target : Locals.Source.Store} {name : Name} {value : Assembly.Word}
    (hRel : ScopedRel layout source target)
    (hHidden : name ∉ layout) :
    ScopedRel layout source
      (Locals.Source.Store.insert target name value) := by
  intro key hKey
  have hNe : key ≠ name := by
    intro hEq
    exact hHidden (by simpa [hEq] using hKey)
  rw [Locals.Source.Store.insert_of_ne hNe]
  exact hRel key hKey

theorem scoped_cons_insert
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {target : Locals.Source.Store} {name : Name} {value : Assembly.Word}
    (hRel : ScopedRel layout source target)
    (hFresh : name ∉ layout) :
    ScopedRel (name :: layout) (source.insert name value)
      (Locals.Source.Store.insert target name value) := by
  intro key hKey
  simp only [List.mem_cons] at hKey
  rcases hKey with hEq | hMem
  · subst key
    simp
  · have hNe : key ≠ name := by
      intro hEq
      exact hFresh (by simpa [hEq] using hMem)
    rw [Finmap.lookup_insert_of_ne source hNe]
    rw [Locals.Source.Store.insert_of_ne hNe]
    exact hRel key hMem

theorem scoped_insert_visible
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {target : Locals.Source.Store} {name : Name} {value : Assembly.Word}
    (hRel : ScopedRel layout source target) :
    ScopedRel layout (source.insert name value)
      (Locals.Source.Store.insert target name value) := by
  intro key hKey
  by_cases hEq : key = name
  · subst key
    simp
  · rw [Finmap.lookup_insert_of_ne source hEq]
    rw [Locals.Source.Store.insert_of_ne hEq]
    exact hRel key hKey

theorem scoped_restrict_target
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {target : Locals.Source.Store}
    (hRel : ScopedRel layout source target) :
    ScopedRel layout source
      (Locals.Source.Store.restrictTo layout target) := by
  intro name hMem
  rw [Locals.Source.Store.restrictTo_mem hMem]
  exact hRel name hMem

theorem scoped_restrict
    {layout : List Name} {source scope : EvmYul.Yul.VarStore}
    {target : Locals.Source.Store}
    (hRel : ScopedRel layout source target)
    (hScope : DomainExact layout scope) :
    ScopedRel layout
      (EvmYul.Yul.State.restrictVarStore source scope)
      (Locals.Source.Store.restrictTo layout target) := by
  intro name hMem
  have hScopeSome : (scope.lookup name).isSome = true :=
    (hScope name).mpr hMem
  cases hLookup : scope.lookup name with
  | none =>
      simp [hLookup] at hScopeSome
  | some value =>
      rw [VarStore.lookup_restrict_of_some source scope name hLookup]
      rw [Locals.Source.Store.restrictTo_mem hMem]
      exact hRel name hMem

theorem domainExact_insert
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {name : Name} {value : Assembly.Word}
    (hDomain : DomainExact layout source) :
    DomainExact (name :: layout) (source.insert name value) := by
  intro key
  by_cases hEq : key = name
  · subst key
    simp
  · rw [Finmap.lookup_insert_of_ne source hEq]
    constructor
    · intro hSome
      exact List.mem_cons_of_mem name ((hDomain key).mp hSome)
    · intro hMem
      exact (hDomain key).mpr (by simpa [hEq] using hMem)

theorem domainExact_insert_visible
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {name : Name} {value : Assembly.Word}
    (hDomain : DomainExact layout source)
    (hMem : name ∈ layout) :
    DomainExact layout (source.insert name value) := by
  intro key
  by_cases hEq : key = name
  · subst key
    simp [hMem]
  · rw [Finmap.lookup_insert_of_ne source hEq]
    exact hDomain key

theorem domainExact_isSome_of_mem
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    (hDomain : DomainExact layout source)
    {name : Name} (hMem : name ∈ layout) :
    (source.lookup name).isSome = true :=
  (hDomain name).mpr hMem

theorem domainExact_isNone_of_not_mem
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    (hDomain : DomainExact layout source)
    {name : Name} (hNotMem : name ∉ layout) :
    source.lookup name = none := by
  cases hLookup : source.lookup name with
  | none =>
      rfl
  | some value =>
      have hSome : (source.lookup name).isSome = true := by
        simp [hLookup]
      exact False.elim (hNotMem ((hDomain name).mp hSome))

theorem domainExact_restrict
    {retained current : List Name}
    {source scope : EvmYul.Yul.VarStore}
    (hSource : DomainExact current source)
    (hScope : DomainExact retained scope)
    (hSubset : ∀ name, name ∈ retained → name ∈ current) :
    DomainExact retained
      (EvmYul.Yul.State.restrictVarStore source scope) := by
  intro name
  constructor
  · intro hSome
    by_contra hNotMem
    have hScopeNone : scope.lookup name = none :=
      domainExact_isNone_of_not_mem hScope hNotMem
    rw [VarStore.lookup_restrict_of_none source scope name hScopeNone] at hSome
    simp at hSome
  · intro hMem
    have hSourceSome : (source.lookup name).isSome = true :=
      (hSource name).mpr (hSubset name hMem)
    have hScopeSome : (scope.lookup name).isSome = true :=
      (hScope name).mpr hMem
    cases hScopeLookup : scope.lookup name with
    | none =>
        simp [hScopeLookup] at hScopeSome
    | some scopeValue =>
        rw [VarStore.lookup_restrict_of_some source scope name hScopeLookup]
        exact hSourceSome

theorem firstDuplicate?_none_of_nodup
    (names : List Name) (hNoDup : names.Nodup) :
    EvmYul.Yul.firstDuplicate? names = none := by
  induction names with
  | nil =>
      rfl
  | cons name rest ih =>
      have hParts := List.nodup_cons.mp hNoDup
      simp [EvmYul.Yul.firstDuplicate?, hParts.1, ih hParts.2]

theorem firstDeclared?_none
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {shared : EvmYul.SharedState .Yul} {names : List Name}
    (hDomain : DomainExact layout source)
    (hFresh : ∀ name, name ∈ names → name ∉ layout) :
    EvmYul.Yul.firstDeclared? (.Ok shared source) names = none := by
  unfold EvmYul.Yul.firstDeclared?
  apply List.find?_eq_none.mpr
  intro name hMem
  have hNone : source.lookup name = none :=
    domainExact_isNone_of_not_mem hDomain (hFresh name hMem)
  simp [EvmYul.Yul.State.lookup?, hNone]

theorem checkDeclaration_ok
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {shared : EvmYul.SharedState .Yul} {names : List Name}
    (hDomain : DomainExact layout source)
    (hNoDup : names.Nodup)
    (hFresh : ∀ name, name ∈ names → name ∉ layout) :
    EvmYul.Yul.checkDeclaration (.Ok shared source) names = .ok () := by
  simp [EvmYul.Yul.checkDeclaration,
    firstDuplicate?_none_of_nodup names hNoDup,
    firstDeclared?_none hDomain hFresh]

theorem firstUndeclared?_none
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {shared : EvmYul.SharedState .Yul} {names : List Name}
    (hDomain : DomainExact layout source)
    (hDeclared : ∀ name, name ∈ names → name ∈ layout) :
    EvmYul.Yul.firstUndeclared? (.Ok shared source) names = none := by
  unfold EvmYul.Yul.firstUndeclared?
  apply List.find?_eq_none.mpr
  intro name hMem
  have hSome :
      (source.lookup name).isSome = true :=
    domainExact_isSome_of_mem hDomain (hDeclared name hMem)
  cases hLookup : source.lookup name with
  | none =>
      simp [hLookup] at hSome
  | some value =>
      simp [EvmYul.Yul.State.lookup?, hLookup]

theorem checkAssignment_ok
    {layout : List Name} {source : EvmYul.Yul.VarStore}
    {shared : EvmYul.SharedState .Yul} {names : List Name}
    (hDomain : DomainExact layout source)
    (hNoDup : names.Nodup)
    (hDeclared : ∀ name, name ∈ names → name ∈ layout) :
    EvmYul.Yul.checkAssignment (.Ok shared source) names = .ok () := by
  simp [EvmYul.Yul.checkAssignment,
    firstDuplicate?_none_of_nodup names hNoDup,
    firstUndeclared?_none hDomain hDeclared]

end Vars

namespace Regular

def Rel (codeRel : CodeRel)
    (source : EvmYul.Yul.State)
    (target : Locals.Source.State) : Prop :=
  ∃ sourceShared : EvmYul.SharedState .Yul,
    ∃ sourceVars : EvmYul.Yul.VarStore,
      source = .Ok sourceShared sourceVars ∧
        Shared.Rel codeRel sourceShared target.shared ∧
        Vars.Rel sourceVars target.vars

theorem machine_eq
    {codeRel : CodeRel} {source : EvmYul.Yul.State}
    {target : Locals.Source.State}
    (hRel : Rel codeRel source target) :
    source.sharedState.toMachineState =
      target.shared.toMachineState := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, _hVars⟩
  simpa only [hSource, EvmYul.Yul.State.sharedState] using
    hShared.machine

theorem multifill_single
    {codeRel : CodeRel} {source : EvmYul.Yul.State}
    {target : Locals.Source.State}
    (hRel : Rel codeRel source target)
    (name : EvmYul.Identifier) (value : Assembly.Word) :
    Rel codeRel (source.multifill [name] [value])
      (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  refine
    ⟨sourceShared, sourceVars.insert name value, ?_, hShared,
      Vars.insert hVars name value⟩
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

theorem insert_target_hidden
    {codeRel : CodeRel} {source : EvmYul.Yul.State}
    {target : Locals.Source.State}
    (hRel : Rel codeRel source target)
    {name : Name} {value : Assembly.Word}
    (hHidden : source.lookup? name = none) :
    Rel codeRel source (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  exact
    ⟨sourceShared, sourceVars, rfl, hShared,
      Vars.insert_target_hidden hVars (by simpa using hHidden)⟩

def ScopedExactRel (codeRel : CodeRel) (layout : List Name)
    (source : EvmYul.Yul.State)
    (target : Locals.Source.State) : Prop :=
  ∃ sourceShared : EvmYul.SharedState .Yul,
    ∃ sourceVars : EvmYul.Yul.VarStore,
      source = .Ok sourceShared sourceVars ∧
        Shared.Rel codeRel sourceShared target.shared ∧
        Vars.ScopedRel layout sourceVars target.vars ∧
        Vars.DomainExact layout sourceVars

theorem scopedExact_of_rel
    {codeRel : CodeRel} {layout : List Name}
    {source : EvmYul.Yul.State} {target : Locals.Source.State}
    (hRel : Rel codeRel source target)
    (hDomain :
      ∀ sourceShared sourceVars,
        source = .Ok sourceShared sourceVars →
          Vars.DomainExact layout sourceVars) :
    ScopedExactRel codeRel layout source target := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  have hSourceDomain :=
    hDomain sourceShared sourceVars hSource
  exact
    ⟨sourceShared, sourceVars, hSource, hShared,
      Vars.scoped_of_rel hVars hSourceDomain, hSourceDomain⟩

theorem scopedExact_insert_hidden
    {codeRel : CodeRel} {layout : List Name}
    {source : EvmYul.Yul.State} {target : Locals.Source.State}
    (hRel : ScopedExactRel codeRel layout source target)
    {name : Name} {value : Assembly.Word}
    (hHidden : name ∉ layout) :
    ScopedExactRel codeRel layout source (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars, hDomain⟩
  exact
    ⟨sourceShared, sourceVars, hSource, hShared,
      Vars.scoped_insert_hidden hVars hHidden, hDomain⟩

theorem scopedExact_multifill_single_fresh
    {codeRel : CodeRel} {layout : List Name}
    {source : EvmYul.Yul.State} {target : Locals.Source.State}
    (hRel : ScopedExactRel codeRel layout source target)
    (name : EvmYul.Identifier) (value : Assembly.Word)
    (hFresh : name ∉ layout) :
    ScopedExactRel codeRel (name :: layout)
      (source.multifill [name] [value])
      (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars, hDomain⟩
  subst source
  refine
    ⟨sourceShared, sourceVars.insert name value, ?_, hShared,
      Vars.scoped_cons_insert hVars hFresh,
      Vars.domainExact_insert hDomain⟩
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

theorem scopedExact_multifill_single_visible
    {codeRel : CodeRel} {layout : List Name}
    {source : EvmYul.Yul.State} {target : Locals.Source.State}
    (hRel : ScopedExactRel codeRel layout source target)
    (name : EvmYul.Identifier) (value : Assembly.Word)
    (hMem : name ∈ layout) :
    ScopedExactRel codeRel layout
      (source.multifill [name] [value])
      (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars, hDomain⟩
  subst source
  refine
    ⟨sourceShared, sourceVars.insert name value, ?_, hShared,
      Vars.scoped_insert_visible hVars,
      Vars.domainExact_insert_visible hDomain hMem⟩
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

theorem scopedExact_restrict
    {codeRel : CodeRel} {retained current : List Name}
    {shared : EvmYul.SharedState .Yul}
    {sourceVars scopeVars : EvmYul.Yul.VarStore}
    {target : Locals.Source.State}
    (hRel :
      ScopedExactRel codeRel current (.Ok shared sourceVars) target)
    (hScope : Vars.DomainExact retained scopeVars)
    (hSubset : ∀ name, name ∈ retained → name ∈ current) :
    ScopedExactRel codeRel retained
      (.Ok shared
        (EvmYul.Yul.State.restrictVarStore sourceVars scopeVars))
      (target.restrictTo retained) := by
  rcases hRel with
    ⟨sourceShared, relatedVars, hSource, hShared, hVars, hDomain⟩
  cases hSource
  exact
    ⟨shared, EvmYul.Yul.State.restrictVarStore sourceVars scopeVars,
      rfl, hShared,
      Vars.scoped_restrict (Vars.scoped_of_subset hVars hSubset) hScope,
      Vars.domainExact_restrict hDomain hScope hSubset⟩

end Regular

namespace Replay

def Rel {transcript : Assembly.ResourceTrace} (codeRel : CodeRel)
    (source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript)
    (target :
      Simulation.ResourceReplay.State Locals.Source.State transcript) : Prop :=
  source.cursor = target.cursor ∧
    Regular.Rel codeRel source.source target.source

theorem machine_eq
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.source.sharedState.toMachineState =
      target.source.shared.toMachineState :=
  Regular.machine_eq hRel.2

theorem consumedExactly_iff
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.ConsumedExactly ↔ target.ConsumedExactly := by
  change source.cursor = transcript.length ↔
    target.cursor = transcript.length
  rw [hRel.1]

theorem observed_eq
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.observed = target.observed := by
  simp only [Simulation.ResourceReplay.State.observed]
  rw [hRel.1]

theorem remaining_eq
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.remaining = target.remaining := by
  simp only [Simulation.ResourceReplay.State.remaining]
  rw [hRel.1]

theorem multifill_single
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target)
    (name : EvmYul.Identifier) (value : Assembly.Word) :
    Rel codeRel
      (source.withSource (source.source.multifill [name] [value]))
      (target.withSource (target.source.insert name value)) := by
  exact
    ⟨hRel.1, Regular.multifill_single hRel.2 name value⟩

theorem insert_target_hidden
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target)
    {name : Name} {value : Assembly.Word}
    (hHidden : source.source.lookup? name = none) :
    Rel codeRel source
      (target.withSource (target.source.insert name value)) := by
  exact
    ⟨hRel.1, Regular.insert_target_hidden hRel.2 hHidden⟩

def ScopedExactRel {transcript : Assembly.ResourceTrace}
    (codeRel : CodeRel) (layout : List Name)
    (source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript)
    (target :
      Simulation.ResourceReplay.State Locals.Source.State transcript) : Prop :=
  source.cursor = target.cursor ∧
    Regular.ScopedExactRel codeRel layout source.source target.source

theorem scopedExact_consumedExactly_iff
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {layout : List Name}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : ScopedExactRel codeRel layout source target) :
    source.ConsumedExactly ↔ target.ConsumedExactly := by
  change source.cursor = transcript.length ↔
    target.cursor = transcript.length
  rw [hRel.1]

theorem scopedExact_insert_hidden
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {layout : List Name}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : ScopedExactRel codeRel layout source target)
    {name : Name} {value : Assembly.Word}
    (hHidden : name ∉ layout) :
    ScopedExactRel codeRel layout source
      (target.withSource (target.source.insert name value)) := by
  exact
    ⟨hRel.1, Regular.scopedExact_insert_hidden hRel.2 hHidden⟩

theorem scopedExact_multifill_single_fresh
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {layout : List Name}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : ScopedExactRel codeRel layout source target)
    (name : EvmYul.Identifier) (value : Assembly.Word)
    (hFresh : name ∉ layout) :
    ScopedExactRel codeRel (name :: layout)
      (source.withSource (source.source.multifill [name] [value]))
      (target.withSource (target.source.insert name value)) := by
  exact
    ⟨hRel.1,
      Regular.scopedExact_multifill_single_fresh hRel.2 name value hFresh⟩

theorem scopedExact_multifill_single_visible
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {layout : List Name}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : ScopedExactRel codeRel layout source target)
    (name : EvmYul.Identifier) (value : Assembly.Word)
    (hMem : name ∈ layout) :
    ScopedExactRel codeRel layout
      (source.withSource (source.source.multifill [name] [value]))
      (target.withSource (target.source.insert name value)) := by
  exact
    ⟨hRel.1,
      Regular.scopedExact_multifill_single_visible hRel.2 name value hMem⟩

theorem scopedExact_restrict
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {retained current : List Name}
    {shared : EvmYul.SharedState .Yul}
    {sourceVars scopeVars : EvmYul.Yul.VarStore}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hSource : source.source = .Ok shared sourceVars)
    (hRel : ScopedExactRel codeRel current source target)
    (hScope : Vars.DomainExact retained scopeVars)
    (hSubset : ∀ name, name ∈ retained → name ∈ current) :
    ScopedExactRel codeRel retained
      (source.withSource
        (.Ok shared
          (EvmYul.Yul.State.restrictVarStore sourceVars scopeVars)))
      (target.withSource (target.source.restrictTo retained)) := by
  refine ⟨hRel.1, ?_⟩
  exact
    Regular.scopedExact_restrict
      (hRel := by simpa [hSource] using hRel.2)
      hScope hSubset

end Replay

end StateRelation
end Yul
end EvmCompiler
