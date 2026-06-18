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
  (EvmYul.State.accountCodeImage account).isEmpty &&
    (decide (account.nonce = ⟨0⟩) &&
      decide (account.balance = ⟨0⟩))

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
      EvmYul.State.accountCodeImage]
  simp [extCodeHash, dead, EvmYul.State.extCodeHash,
    EvmYul.State.dead, hEmpty]

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
