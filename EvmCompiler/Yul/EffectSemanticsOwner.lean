import EvmCompiler.Yul.EffectSemantics

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

/-!
Active-code-owner availability for the canonical parameterized Yul semantics.

The predicate follows checkpoint states as well as ordinary states because
`break`, `continue`, and `leave` retain the active world inside the checkpoint.
This is a source semantic invariant, not compiler evidence.
-/

def activeShared? :
    EvmYul.Yul.State → Option (EvmYul.SharedState .Yul)
  | .Ok shared _ => some shared
  | .OutOfFuel => none
  | .Checkpoint (.Continue shared _) => some shared
  | .Checkpoint (.Break shared _) => some shared
  | .Checkpoint (.Leave shared _) => some shared

def ActiveOwnerAvailable (state : EvmYul.Yul.State) : Prop :=
  ∃ shared account,
    activeShared? state = some shared ∧
      shared.accountMap.find? shared.executionEnv.codeOwner = some account

def OwnerAvailable {σ : Type} (model : StateModel σ) (state : σ) : Prop :=
  ActiveOwnerAvailable (model.source state)

namespace StateModel

structure Lawful {σ : Type} (model : StateModel σ) : Prop where
  source_withSource :
    ∀ state source, model.source (model.withSource state source) = source

end StateModel

namespace PrimitiveSemantics

structure PreservesOwner {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) : Prop where
  eval :
    ∀ {fuel : Nat} {state final : σ}
      {op : EvmYul.Operation .Yul} {args values : List Word},
      OwnerAvailable model state →
      prim.eval fuel state op args = .ok (final, values) →
      OwnerAvailable model final

end PrimitiveSemantics

@[simp] theorem activeShared?_insert
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier) (value : Word) :
    activeShared? (state.insert name value) = activeShared? state := by
  cases state <;> rfl

private theorem activeShared?_foldr_insert
    (entries : List (EvmYul.Identifier × Word))
    (state : EvmYul.Yul.State) :
    activeShared?
        (entries.foldr
          (fun entry result => result.insert entry.1 entry.2) state) =
      activeShared? state := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldr_cons, activeShared?_insert, ih]

@[simp] theorem activeShared?_multifill
    (state : EvmYul.Yul.State)
    (names : List EvmYul.Identifier) (values : List Word) :
    activeShared? (state.multifill names values) = activeShared? state := by
  cases state with
  | Ok shared store =>
      exact activeShared?_foldr_insert (List.zip names values) (.Ok shared store)
  | OutOfFuel => rfl
  | Checkpoint jump => rfl

@[simp] theorem activeShared?_zeroFill
    (state : EvmYul.Yul.State) (names : List EvmYul.Identifier) :
    activeShared? (state.zeroFill names) = activeShared? state := by
  induction names generalizing state with
  | nil => rfl
  | cons name names ih =>
      simp only [EvmYul.Yul.State.zeroFill, List.foldr_cons,
        activeShared?_insert]
      simpa [EvmYul.Yul.State.zeroFill] using ih state

@[simp] theorem activeShared?_restrictStoreTo
    (state : EvmYul.Yul.State) (store : EvmYul.Yul.VarStore) :
    activeShared? (state.restrictStoreTo store) = activeShared? state := by
  cases state with
  | Ok shared vars => rfl
  | OutOfFuel => rfl
  | Checkpoint jump =>
      cases jump <;> rfl

@[simp] theorem activeShared?_setStore
    (state restore : EvmYul.Yul.State) :
    activeShared? (state.setStore restore) = activeShared? state := by
  cases state <;> cases restore <;> rfl

@[simp] theorem activeOwnerAvailable_setMachineState
    (state : EvmYul.Yul.State) (machine : EvmYul.MachineState) :
    ActiveOwnerAvailable (state.setMachineState machine) ↔
      ActiveOwnerAvailable state := by
  cases state with
  | Ok shared store =>
      simp [ActiveOwnerAvailable, activeShared?,
        EvmYul.Yul.State.setMachineState]
  | OutOfFuel =>
      simp [ActiveOwnerAvailable, activeShared?,
        EvmYul.Yul.State.setMachineState]
  | Checkpoint jump =>
      cases jump <;>
        simp [ActiveOwnerAvailable, activeShared?,
          EvmYul.Yul.State.setMachineState]

@[simp] theorem activeShared?_setContinue
    (state : EvmYul.Yul.State) :
    activeShared? state.setContinue = activeShared? state := by
  cases state <;> rfl

@[simp] theorem activeShared?_setBreak
    (state : EvmYul.Yul.State) :
    activeShared? state.setBreak = activeShared? state := by
  cases state <;> rfl

@[simp] theorem activeShared?_setLeave
    (state : EvmYul.Yul.State) :
    activeShared? state.setLeave = activeShared? state := by
  cases state <;> rfl

@[simp] theorem activeShared?_initcall
    (state : EvmYul.Yul.State)
    (params returns : List EvmYul.Identifier) (args : List Word) :
    activeShared? (state.initcall params returns args) = activeShared? state := by
  cases state <;> simp [EvmYul.Yul.State.initcall]

@[simp] theorem activeShared?_reviveJump
    (state : EvmYul.Yul.State) :
    activeShared? state.reviveJump = activeShared? state := by
  cases state with
  | Ok shared vars => rfl
  | OutOfFuel => rfl
  | Checkpoint jump =>
      cases jump <;> rfl

theorem activeOwnerAvailable_of_activeShared?_eq
    {left right : EvmYul.Yul.State}
    (hShared : activeShared? left = activeShared? right)
    (hOwner : ActiveOwnerAvailable right) :
    ActiveOwnerAvailable left := by
  rcases hOwner with ⟨shared, account, hActive, hLookup⟩
  exact ⟨shared, account, hShared.trans hActive, hLookup⟩

@[simp] theorem activeOwnerAvailable_multifill
    (state : EvmYul.Yul.State)
    (names : List EvmYul.Identifier) (values : List Word) :
    ActiveOwnerAvailable (state.multifill names values) ↔
      ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_multifill]

@[simp] theorem activeOwnerAvailable_zeroFill
    (state : EvmYul.Yul.State) (names : List EvmYul.Identifier) :
    ActiveOwnerAvailable (state.zeroFill names) ↔
      ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_zeroFill]

@[simp] theorem activeOwnerAvailable_restrictStoreTo
    (state : EvmYul.Yul.State) (store : EvmYul.Yul.VarStore) :
    ActiveOwnerAvailable (state.restrictStoreTo store) ↔
      ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_restrictStoreTo]

@[simp] theorem activeOwnerAvailable_setStore
    (state restore : EvmYul.Yul.State) :
    ActiveOwnerAvailable (state.setStore restore) ↔
      ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_setStore]

@[simp] theorem activeOwnerAvailable_setContinue
    (state : EvmYul.Yul.State) :
    ActiveOwnerAvailable state.setContinue ↔ ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_setContinue]

@[simp] theorem activeOwnerAvailable_setBreak
    (state : EvmYul.Yul.State) :
    ActiveOwnerAvailable state.setBreak ↔ ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_setBreak]

@[simp] theorem activeOwnerAvailable_setLeave
    (state : EvmYul.Yul.State) :
    ActiveOwnerAvailable state.setLeave ↔ ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_setLeave]

@[simp] theorem activeOwnerAvailable_initcall
    (state : EvmYul.Yul.State)
    (params returns : List EvmYul.Identifier) (args : List Word) :
    ActiveOwnerAvailable (state.initcall params returns args) ↔
      ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_initcall]

@[simp] theorem activeOwnerAvailable_reviveJump
    (state : EvmYul.Yul.State) :
    ActiveOwnerAvailable state.reviveJump ↔ ActiveOwnerAvailable state := by
  simp only [ActiveOwnerAvailable, activeShared?_reviveJump]

end Effectful
end Source
end Yul
end EvmCompiler
