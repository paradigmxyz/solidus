import EvmYul.SharedState
import EvmYul.StateOps

namespace EvmCompiler
namespace Simulation

abbrev OpenWord := EvmYul.UInt256
abbrev OpenAddress := EvmYul.AccountAddress

/--
The account data observable across the compiler's open external boundary.

External code is deliberately represented only by bytes. In particular, an
external account does not carry a Yul AST or any compiler provenance.
-/
structure OpenAccount where
  nonce : OpenWord
  balance : OpenWord
  storage : EvmYul.Storage
  transientStorage : EvmYul.Storage
  codeBytes : ByteArray
  deriving Inhabited

namespace OpenAccount

def ofAccount {τ : EvmYul.OperationType}
    (account : EvmYul.Account τ) : OpenAccount where
  nonce := account.nonce
  balance := account.balance
  storage := account.storage
  transientStorage := account.tstorage
  codeBytes := EvmYul.State.accountCodeImage account

def empty (account : OpenAccount) : Bool :=
  account.codeBytes.isEmpty &&
    (decide (account.nonce = ⟨0⟩) &&
      decide (account.balance = ⟨0⟩))

def ofYul (account : EvmYul.Account .Yul) : OpenAccount where
  nonce := account.nonce
  balance := account.balance
  storage := account.storage
  transientStorage := account.tstorage
  codeBytes := account.codeBytes

def ofEVM (account : EvmYul.Account .EVM) : OpenAccount where
  nonce := account.nonce
  balance := account.balance
  storage := account.storage
  transientStorage := account.tstorage
  codeBytes := account.code

@[simp] theorem ofAccount_yul (account : EvmYul.Account .Yul) :
    ofAccount account = ofYul account := rfl

@[simp] theorem ofAccount_evm (account : EvmYul.Account .EVM) :
    ofAccount account = ofEVM account := rfl

@[simp] theorem ofAccount_default {τ : EvmYul.OperationType} :
    ofAccount (default : EvmYul.Account τ) = (default : OpenAccount) := by
  cases τ <;> rfl

@[simp] theorem ofAccount_balance {τ : EvmYul.OperationType}
    (account : EvmYul.Account τ) :
    (ofAccount account).balance = account.balance := rfl

@[simp] theorem ofAccount_withBalance {τ : EvmYul.OperationType}
    (account : EvmYul.Account τ) (balance : OpenWord) :
    ofAccount { account with balance := balance } =
      { ofAccount account with balance := balance } := by
  cases τ <;> rfl

@[simp] theorem ofAccount_defaultWithBalance
    {τ : EvmYul.OperationType} (balance : OpenWord) :
    ofAccount ({ (default : EvmYul.Account τ) with balance := balance }) =
      { (default : OpenAccount) with balance := balance } := by
  cases τ <;> rfl

theorem ofAccount_updateStorage {τ : EvmYul.OperationType}
    (account : EvmYul.Account τ) (key value : EvmYul.UInt256) :
    ofAccount (account.updateStorage key value) =
      { ofAccount account with
        storage :=
          if value == (default : EvmYul.UInt256) then
            account.storage.erase key
          else account.storage.insert key value } := by
  cases τ <;>
    by_cases hZero : value == (default : EvmYul.UInt256) <;>
    simp [EvmYul.Account.updateStorage, hZero, ofAccount,
      EvmYul.State.accountCodeImage]

theorem ofAccount_updateTransientStorage {τ : EvmYul.OperationType}
    (account : EvmYul.Account τ) (key value : EvmYul.UInt256) :
    ofAccount (account.updateTransientStorage key value) =
      { ofAccount account with
        transientStorage :=
          if value == (default : EvmYul.UInt256) then
            account.tstorage.erase key
          else account.tstorage.insert key value } := by
  cases τ <;>
    by_cases hZero : value == (default : EvmYul.UInt256) <;>
    simp [EvmYul.Account.updateTransientStorage, hZero, ofAccount,
      EvmYul.State.accountCodeImage]

/--
Install code-erased account data into a legacy Yul account while retaining an
explicit compatibility AST. Canonical open semantics must not inspect that AST.
-/
def toYul (account : OpenAccount)
    (compatibilityCode : EvmYul.Yul.Ast.YulContract) :
    EvmYul.Account .Yul where
  nonce := account.nonce
  balance := account.balance
  storage := account.storage
  code := compatibilityCode
  codeBytes := account.codeBytes
  tstorage := account.transientStorage

def toEVM (account : OpenAccount) : EvmYul.Account .EVM where
  nonce := account.nonce
  balance := account.balance
  storage := account.storage
  code := account.codeBytes
  codeBytes := account.codeBytes
  tstorage := account.transientStorage

@[simp] theorem ofYul_toYul (account : OpenAccount)
    (compatibilityCode : EvmYul.Yul.Ast.YulContract) :
    ofYul (account.toYul compatibilityCode) = account := by
  cases account
  rfl

@[simp] theorem ofEVM_toEVM (account : OpenAccount) :
    ofEVM account.toEVM = account := by
  cases account
  rfl

end OpenAccount

namespace CodeErasedState

/-- Account emptiness observable through the open-world boundary. Unlike the
legacy Yul predicate, this inspects the executable byte image, not a retained
compatibility AST. -/
def emptyAccount {τ : EvmYul.OperationType}
    (account : EvmYul.Account τ) : Bool :=
  (OpenAccount.ofAccount account).empty

def dead {τ : EvmYul.OperationType}
    (accounts : EvmYul.AccountMap τ)
    (address : EvmYul.AccountAddress) : Bool :=
  (accounts.find? address).option true emptyAccount

/-- `EXTCODEHASH` over the code-erased account view shared by Yul and EVM. -/
def extCodeHash {τ : EvmYul.OperationType}
    (state : EvmYul.State τ) (value : EvmYul.UInt256) :
    EvmYul.State τ × EvmYul.UInt256 :=
  let address := EvmYul.AccountAddress.ofUInt256 value
  let next := state.addAccessedAccount address
  if dead state.accountMap address then
    (next, ⟨0⟩)
  else
    let result :=
      state.lookupAccount address |>.option ⟨0⟩
        (fun account =>
          .ofNat <| EvmYul.fromByteArrayBigEndian
            (ffi.KEC (EvmYul.State.accountCodeImage account)))
    (next, result)

theorem extCodeHash_evm (state : EvmYul.State .EVM) (value : EvmYul.UInt256) :
    extCodeHash state value = EvmYul.State.extCodeHash state value := by
  have hEmpty :
      (fun account : EvmYul.Account .EVM => emptyAccount account) =
        EvmYul.Account.emptyAccount := by
    funext account
    simp [emptyAccount, EvmYul.Account.emptyAccount,
      EvmYul.State.accountCodeImage, OpenAccount.empty,
      OpenAccount.ofEVM]
  simp [extCodeHash, dead, EvmYul.State.extCodeHash,
    EvmYul.State.dead, hEmpty]

def currentStorageValue {τ : EvmYul.OperationType}
    (state : EvmYul.State τ) (owner : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) : EvmYul.UInt256 :=
  (state.accountMap.find! owner).1.storage.findD key ⟨0⟩

def initialStorageValue {τ : EvmYul.OperationType}
    (state : EvmYul.State τ) (owner : EvmYul.AccountAddress)
    (key : EvmYul.UInt256) : EvmYul.UInt256 :=
  (state.σ₀.find? owner).option ⟨0⟩
    (fun account => account.storage.findD key ⟨0⟩)

def sstoreRefundBalance
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

theorem sstore_eq {τ : EvmYul.OperationType}
    (state : EvmYul.State τ) (key value : EvmYul.UInt256) :
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
      (state.accountMap.find! state.executionEnv.codeOwner).1.storage =
        (state.accountMap.find! state.executionEnv.codeOwner).storage := by
    rfl
  rw [hStorage]
  cases hInitial : state.σ₀.find? state.executionEnv.codeOwner <;>
    simp [hInitial, Option.option] <;> rfl

end CodeErasedState

/--
The mutable, code-erased world shared exactly by source and target semantics.

Transaction snapshots, block history, active code, frame-local data, and gas
counters are intentionally excluded.
-/
structure OpenWorld where
  accounts : EvmYul.AddrMap OpenAccount
  substate : EvmYul.Substate
  createdAccounts : Batteries.RBSet OpenAddress compare
  deriving Inhabited

namespace OpenWorld

theorem ext_of_fields
    {left right : OpenWorld}
    (hAccounts : left.accounts = right.accounts)
    (hSubstate : left.substate = right.substate)
    (hCreated : left.createdAccounts = right.createdAccounts) :
    left = right := by
  cases left
  cases right
  simp_all

theorem find?_mapVal_const
    {α β γ : Type} {cmp : α → α → Ordering}
    (map : Batteries.RBMap α β cmp) (f : β → γ) (key : α) :
    (map.mapVal fun _ value => f value).find? key =
      (map.find? key).map f := by
  rcases map with ⟨tree, hTree⟩
  change
    Option.map Prod.snd
        (Batteries.RBNode.find? (fun entry => cmp key entry.1)
          (tree.map (Batteries.RBMap.Imp.mapSnd fun _ value => f value))) =
      Option.map f
        (Option.map Prod.snd
          (Batteries.RBNode.find? (fun entry => cmp key entry.1) tree))
  clear hTree
  induction tree with
  | nil => rfl
  | node color left entry right leftIH rightIH =>
      cases hCompare : cmp key entry.1 <;>
        simp [Batteries.RBNode.map, Batteries.RBNode.find?,
          Batteries.RBMap.Imp.mapSnd, hCompare, leftIH, rightIH,
          Function.comp_def]

private theorem mapSnd_setBlack
    {α β γ : Type} (f : α → β → γ)
    (tree : Batteries.RBNode (α × β)) :
    (tree.setBlack.map (Batteries.RBMap.Imp.mapSnd f)) =
      (tree.map (Batteries.RBMap.Imp.mapSnd f)).setBlack := by
  cases tree <;> rfl

private theorem mapSnd_balance1
    {α β γ : Type} (f : α → β → γ)
    (left : Batteries.RBNode (α × β)) (value : α × β)
    (right : Batteries.RBNode (α × β)) :
    (Batteries.RBNode.balance1 left value right).map
        (Batteries.RBMap.Imp.mapSnd f) =
      Batteries.RBNode.balance1
        (left.map (Batteries.RBMap.Imp.mapSnd f))
        (Batteries.RBMap.Imp.mapSnd f value)
        (right.map (Batteries.RBMap.Imp.mapSnd f)) := by
  cases left with
  | nil => rfl
  | node color leftLeft leftValue leftRight =>
      cases color with
      | black => rfl
      | red =>
          cases leftLeft with
          | nil =>
              cases leftRight with
              | nil => rfl
              | node rightColor rightLeft rightValue rightRight =>
                  cases rightColor <;> rfl
          | node leftColor farLeft pivot nearLeft =>
              cases leftColor with
              | red => rfl
              | black =>
                  cases leftRight with
                  | nil => rfl
                  | node rightColor rightLeft rightValue rightRight =>
                      cases rightColor <;> rfl

private theorem mapSnd_balance2
    {α β γ : Type} (f : α → β → γ)
    (left : Batteries.RBNode (α × β)) (value : α × β)
    (right : Batteries.RBNode (α × β)) :
    (Batteries.RBNode.balance2 left value right).map
        (Batteries.RBMap.Imp.mapSnd f) =
      Batteries.RBNode.balance2
        (left.map (Batteries.RBMap.Imp.mapSnd f))
        (Batteries.RBMap.Imp.mapSnd f value)
        (right.map (Batteries.RBMap.Imp.mapSnd f)) := by
  cases right with
  | nil => rfl
  | node color rightLeft rightValue rightRight =>
      cases color with
      | black => rfl
      | red =>
          cases rightRight with
          | nil =>
              cases rightLeft with
              | nil => rfl
              | node leftColor leftLeft leftValue leftRight =>
                  cases leftColor <;> rfl
          | node rightColor nearRight pivot farRight =>
              cases rightColor with
              | red => rfl
              | black =>
                  cases rightLeft with
                  | nil => rfl
                  | node leftColor leftLeft leftValue leftRight =>
                      cases leftColor <;> rfl

private theorem mapSnd_ins
    {α β γ : Type} {cmp : α → α → Ordering}
    (f : α → β → γ) (key : α) (value : β)
    (tree : Batteries.RBNode (α × β)) :
    (tree.ins (Ordering.byKey Prod.fst cmp) (key, value)).map
        (Batteries.RBMap.Imp.mapSnd f) =
      (tree.map (Batteries.RBMap.Imp.mapSnd f)).ins
        (Ordering.byKey Prod.fst cmp) (key, f key value) := by
  induction tree with
  | nil => rfl
  | node color left entry right leftIH rightIH =>
      cases color with
      | red =>
          cases hCompare : cmp key entry.1 <;>
            simp [Batteries.RBNode.ins, Batteries.RBNode.map,
              Batteries.RBMap.Imp.mapSnd, Ordering.byKey,
              hCompare, leftIH, rightIH]
      | black =>
          cases hCompare : cmp key entry.1 with
          | lt =>
              simp only [Batteries.RBNode.ins, Batteries.RBNode.map,
                Batteries.RBMap.Imp.mapSnd, Ordering.byKey, hCompare]
              rw [mapSnd_balance1, leftIH]
              simp [Batteries.RBMap.Imp.mapSnd]
          | gt =>
              simp only [Batteries.RBNode.ins, Batteries.RBNode.map,
                Batteries.RBMap.Imp.mapSnd, Ordering.byKey, hCompare]
              rw [mapSnd_balance2, rightIH]
              simp [Batteries.RBMap.Imp.mapSnd]
          | eq =>
              simp [Batteries.RBNode.ins, Batteries.RBNode.map,
                Batteries.RBMap.Imp.mapSnd, Ordering.byKey, hCompare]

private theorem mapSnd_insert
    {α β γ : Type} {cmp : α → α → Ordering}
    (f : α → β → γ) (key : α) (value : β)
    (tree : Batteries.RBNode (α × β)) :
    (tree.insert (Ordering.byKey Prod.fst cmp) (key, value)).map
        (Batteries.RBMap.Imp.mapSnd f) =
      (tree.map (Batteries.RBMap.Imp.mapSnd f)).insert
        (Ordering.byKey Prod.fst cmp) (key, f key value) := by
  unfold Batteries.RBNode.insert
  have hColor :
      (tree.map (Batteries.RBMap.Imp.mapSnd f)).isRed = tree.isRed := by
    cases tree <;> rfl
  rw [hColor]
  cases tree.isRed <;>
    simp [mapSnd_ins, mapSnd_setBlack]

theorem mapVal_insert
    {α β γ : Type} {cmp : α → α → Ordering}
    (map : Batteries.RBMap α β cmp) (f : α → β → γ)
    (key : α) (value : β) :
    (map.insert key value).mapVal f =
      (map.mapVal f).insert key (f key value) := by
  apply Subtype.ext
  exact mapSnd_insert f key value map.1

def selfdestructAccounts (accounts : EvmYul.AddrMap OpenAccount)
    (source target : OpenAddress) (created : Bool) :
    EvmYul.AddrMap OpenAccount :=
  match accounts.find? source with
  | none => accounts
  | some sourceAccount =>
      match accounts.find? target with
      | none =>
          if sourceAccount.balance == (EvmYul.UInt256.ofNat 0) then
            accounts
          else
            accounts.insert target
                { (default : OpenAccount) with
                  balance := sourceAccount.balance }
              |>.insert source
                { sourceAccount with
                  balance := EvmYul.UInt256.ofNat 0 }
      | some targetAccount =>
          if target ≠ source then
            accounts.insert target
                { targetAccount with
                  balance := targetAccount.balance + sourceAccount.balance }
              |>.insert source
                { sourceAccount with
                  balance := EvmYul.UInt256.ofNat 0 }
          else if created then
            accounts.insert target
                { targetAccount with balance := EvmYul.UInt256.ofNat 0 }
              |>.insert source
                { sourceAccount with balance := EvmYul.UInt256.ofNat 0 }
          else accounts

private theorem mapVal_leftInverse
    {α β γ : Type} {cmp : α → α → Ordering}
    (f : α → β → γ) (g : α → γ → β)
    (h : ∀ key value, g key (f key value) = value)
    (map : Batteries.RBMap α β cmp) :
    (map.mapVal f).mapVal g = map := by
  apply Subtype.ext
  change Batteries.RBNode.map (Batteries.RBMap.Imp.mapSnd g)
      (Batteries.RBNode.map (Batteries.RBMap.Imp.mapSnd f) map.1) = map.1
  induction map.1 with
  | nil => rfl
  | node color left value right leftIH rightIH =>
      simp [Batteries.RBNode.map, leftIH, rightIH,
        Batteries.RBMap.Imp.mapSnd, h]

def ofYulState (state : EvmYul.State .Yul) : OpenWorld where
  accounts := state.accountMap.mapVal fun _ account => OpenAccount.ofYul account
  substate := state.substate
  createdAccounts := state.createdAccounts

def ofEVMState (state : EvmYul.State .EVM) : OpenWorld where
  accounts := state.accountMap.mapVal fun _ account => OpenAccount.ofEVM account
  substate := state.substate
  createdAccounts := state.createdAccounts

def ofYulShared (state : EvmYul.SharedState .Yul) : OpenWorld :=
  ofYulState state.toState

def ofEVMShared (state : EvmYul.SharedState .EVM) : OpenWorld :=
  ofEVMState state.toState

def installYulAccounts
    (base : EvmYul.AccountMap .Yul)
    (accounts : EvmYul.AddrMap OpenAccount) :
    EvmYul.AccountMap .Yul :=
  accounts.mapVal fun address account =>
    let compatibilityCode :=
      match base.find? address with
      | some existing => existing.code
      | none => default
    account.toYul compatibilityCode

def installEVMAccounts
    (accounts : EvmYul.AddrMap OpenAccount) :
    EvmYul.AccountMap .EVM :=
  accounts.mapVal fun _ account => account.toEVM

/--
Install an open world into a legacy source state. All transaction, block, and
protected execution-frame fields are preserved from `base`.
-/
def installYul (base : EvmYul.State .Yul) (world : OpenWorld) :
    EvmYul.State .Yul :=
  { base with
    accountMap := installYulAccounts base.accountMap world.accounts
    substate := world.substate
    createdAccounts := world.createdAccounts }

/--
Install an open world into a legacy target state. Active bytecode remains in
the protected execution environment, not in this world replacement.
-/
def installEVM (base : EvmYul.State .EVM) (world : OpenWorld) :
    EvmYul.State .EVM :=
  { base with
    accountMap := installEVMAccounts world.accounts
    substate := world.substate
    createdAccounts := world.createdAccounts }

def installYulShared
    (base : EvmYul.SharedState .Yul) (world : OpenWorld) :
    EvmYul.SharedState .Yul :=
  { base with toState := installYul base.toState world }

def installEVMShared
    (base : EvmYul.SharedState .EVM) (world : OpenWorld) :
    EvmYul.SharedState .EVM :=
  { base with toState := installEVM base.toState world }

@[simp] theorem ofYulState_installYul
    (base : EvmYul.State .Yul) (world : OpenWorld) :
    ofYulState (installYul base world) = world := by
  cases world with
  | mk accounts substate createdAccounts =>
      change OpenWorld.mk
          ((accounts.mapVal fun address account =>
              let compatibilityCode :=
                match base.accountMap.find? address with
                | some existing => existing.code
                | none => default
              account.toYul compatibilityCode).mapVal
            fun _ account => OpenAccount.ofYul account)
          substate createdAccounts =
        OpenWorld.mk accounts substate createdAccounts
      rw [mapVal_leftInverse
          (fun address account =>
            let compatibilityCode :=
              match base.accountMap.find? address with
              | some existing => existing.code
              | none => default
            account.toYul compatibilityCode)
          (fun _ account => OpenAccount.ofYul account)
          (by intro address account; simp)
          accounts]

@[simp] theorem ofEVMState_installEVM
    (base : EvmYul.State .EVM) (world : OpenWorld) :
    ofEVMState (installEVM base world) = world := by
  cases world with
  | mk accounts substate createdAccounts =>
      change OpenWorld.mk
          ((accounts.mapVal fun _ account => account.toEVM).mapVal
            fun _ account => OpenAccount.ofEVM account)
          substate createdAccounts =
        OpenWorld.mk accounts substate createdAccounts
      rw [mapVal_leftInverse
          (fun _ account => account.toEVM)
          (fun _ account => OpenAccount.ofEVM account)
          (by intro address account; simp)
          accounts]

@[simp] theorem ofYulShared_installYulShared
    (base : EvmYul.SharedState .Yul) (world : OpenWorld) :
    ofYulShared (installYulShared base world) = world := by
  exact ofYulState_installYul base.toState world

@[simp] theorem ofEVMShared_installEVMShared
    (base : EvmYul.SharedState .EVM) (world : OpenWorld) :
    ofEVMShared (installEVMShared base world) = world := by
  exact ofEVMState_installEVM base.toState world

@[simp] theorem installYul_executionEnv
    (base : EvmYul.State .Yul) (world : OpenWorld) :
    (installYul base world).executionEnv = base.executionEnv := rfl

@[simp] theorem installEVM_executionEnv
    (base : EvmYul.State .EVM) (world : OpenWorld) :
    (installEVM base world).executionEnv = base.executionEnv := rfl

@[simp] theorem installYul_substate
    (base : EvmYul.State .Yul) (world : OpenWorld) :
    (installYul base world).substate = world.substate := rfl

@[simp] theorem installEVM_substate
    (base : EvmYul.State .EVM) (world : OpenWorld) :
    (installEVM base world).substate = world.substate := rfl

@[simp] theorem installYul_createdAccounts
    (base : EvmYul.State .Yul) (world : OpenWorld) :
    (installYul base world).createdAccounts = world.createdAccounts := rfl

@[simp] theorem installEVM_createdAccounts
    (base : EvmYul.State .EVM) (world : OpenWorld) :
    (installEVM base world).createdAccounts = world.createdAccounts := rfl

@[simp] theorem installYulShared_machine
    (base : EvmYul.SharedState .Yul) (world : OpenWorld) :
    (installYulShared base world).toMachineState =
      base.toMachineState := rfl

@[simp] theorem installEVMShared_machine
    (base : EvmYul.SharedState .EVM) (world : OpenWorld) :
    (installEVMShared base world).toMachineState =
      base.toMachineState := rfl

end OpenWorld

end Simulation
end EvmCompiler
