import EvmCompiler.Functions.Syntax
import EvmCompiler.Locals.SourceSemantics

namespace EvmCompiler
namespace Functions

/-
Stack-free source semantics for the function abstraction.

`Functions.Direct` is still the lowering target into the locals/procedure
backend.  This namespace is the source contract that higher layers should see:
function calls evaluate arguments to values, execute a fresh function-local
environment with parameter and return variables, and assign returned values back
to named caller targets.  It deliberately does not mention stack frames, return
tokens, layout depths, cleanup code, or procedure return machinery.
-/
namespace Source

abbrev Store := Locals.Source.Store
abbrev State := Locals.Source.State
abbrev PrimitiveSemantics := Locals.Source.PrimitiveSemantics
abbrev Mode := Locals.Source.Mode
abbrev Outcome := Locals.Source.Outcome

abbrev invalid {α : Type} : Except EVMException α :=
  Structured.invalid

namespace Outcome

abbrev regular := Locals.Source.Outcome.regular
abbrev brk := Locals.Source.Outcome.brk
abbrev cont := Locals.Source.Outcome.cont
abbrev leave := Locals.Source.Outcome.leave
abbrev halt := Locals.Source.Outcome.halt

end Outcome

def zero : Word :=
  EvmYul.UInt256.ofNat 0

structure Ctx where
  scope : List Name := []
  breakScope? : Option (List Name) := none
  continueScope? : Option (List Name) := none
  leaveScope? : Option (List Name) := none

namespace Ctx

def initial : Ctx := {}

def withoutLoopControl (ctx : Ctx) : Ctx :=
  { ctx with breakScope? := none, continueScope? := none }

def withLoopControl (ctx : Ctx) (breakScope continueScope : List Name) :
    Ctx :=
  { scope := ctx.scope,
    breakScope? := some breakScope,
    continueScope? := some continueScope,
    leaveScope? := ctx.leaveScope? }

def withLeaveScope (ctx : Ctx) (leaveScope : List Name) : Ctx :=
  { ctx with leaveScope? := some leaveScope }

end Ctx

namespace Expr

abbrev eval {results : Nat} (prim : PrimitiveSemantics)
    (expr : Expr results) (state : State) :
    Except EVMException (State × List Word) :=
  Locals.Source.Expr.eval prim expr state

abbrev evalOne {results : Nat} (prim : PrimitiveSemantics)
    (expr : Expr results) (state : State) :
    Except EVMException (State × Word) :=
  Locals.Source.Expr.evalOne prim expr state

abbrev evalCondition (prim : PrimitiveSemantics) (expr : Expr 1)
    (state : State) :
    Except EVMException (State × Bool) :=
  Locals.Source.Expr.evalCondition prim expr state

end Expr

namespace ArgList

def eval (prim : PrimitiveSemantics) : List (Expr 1) → State →
    Except EVMException (State × List Word)
  | [], state => .ok (state, [])
  | arg :: rest, state => do
      let (stateAfterArg, value) ← Expr.evalOne prim arg state
      let (stateAfterRest, values) ← eval prim rest stateAfterArg
      .ok (stateAfterRest, value :: values)

theorem eval_length (prim : PrimitiveSemantics) :
    ∀ {args : List (Expr 1)} {state state' : State} {values : List Word},
      eval prim args state = .ok (state', values) →
        values.length = args.length
  | [], _state, _state', _values, hEval => by
      cases hEval
      rfl
  | arg :: rest, state, state', values, hEval => by
      unfold eval at hEval
      cases hArg : Expr.evalOne prim arg state with
      | error err =>
          simp [hArg] at hEval
      | ok argResult =>
          rcases argResult with ⟨stateAfterArg, value⟩
          simp [hArg] at hEval
          cases hRest : eval prim rest stateAfterArg with
          | error err =>
              simp [hRest] at hEval
          | ok restResult =>
              rcases restResult with ⟨stateAfterRest, restValues⟩
              simp [hRest] at hEval
              rcases hEval with ⟨_hStateEq, hValuesEq⟩
              have hTail :=
                eval_length prim
                  (args := rest) (state := stateAfterArg)
                  (state' := stateAfterRest) (values := restValues) hRest
              rw [← hValuesEq]
              simp [hTail]

theorem eval_single_lit (prim : PrimitiveSemantics)
    (value : Word) (state : State) :
    eval prim [.lit value] state = .ok (state, [value]) := by
  simp [eval, Expr.evalOne, Locals.Source.Expr.evalOne,
    Locals.Source.Expr.eval]

end ArgList

namespace Store

def insertMany : List Name → List Word → Store → Option Store
  | [], [], store => some store
  | name :: names, value :: values, store =>
      insertMany names values (Locals.Source.Store.insert store name value)
  | _, _, _ => none

def initReturns : List Name → Store → Store
  | [], store => store
  | name :: rest, store =>
      initReturns rest (Locals.Source.Store.insert store name zero)

def lookupMany : List Name → Store → Option (List Word)
  | [], _store => some []
  | name :: rest, store => do
      let value ← store name
      let values ← lookupMany rest store
      some (value :: values)

def assignMany : List Name → List Word → Store → Option Store
  | [], [], store => some store
  | name :: names, value :: values, store =>
      if store.contains name then
        assignMany names values (Locals.Source.Store.insert store name value)
      else
        none
  | _, _, _ => none

theorem insertMany_length :
    ∀ {names : List Name} {values : List Word} {store store' : Store},
      insertMany names values store = some store' →
        values.length = names.length
  | [], [], _store, _store', hInsert => by
      simp [insertMany] at hInsert
      cases hInsert
      simp
  | [], _value :: _values, _store, _store', hInsert => by
      simp [insertMany] at hInsert
  | _name :: _names, [], _store, _store', hInsert => by
      simp [insertMany] at hInsert
  | name :: names, value :: values, store, store', hInsert => by
      unfold insertMany at hInsert
      have hTail :=
        insertMany_length
          (names := names) (values := values)
          (store := Locals.Source.Store.insert store name value)
          (store' := store') hInsert
      simp [hTail]

theorem insertMany_apply_of_not_mem :
    ∀ {names : List Name} {values : List Word}
      {store store' : Store} {key : Name},
      insertMany names values store = some store' →
      key ∉ names →
      store' key = store key
  | [], [], _store, _store', _key, hInsert, _hNotMem => by
      simp [insertMany] at hInsert
      cases hInsert
      rfl
  | [], _value :: _values, _store, _store', _key, hInsert, _hNotMem => by
      simp [insertMany] at hInsert
  | _name :: _names, [], _store, _store', _key, hInsert, _hNotMem => by
      simp [insertMany] at hInsert
  | name :: names, value :: values, store, store', key,
      hInsert, hNotMem => by
      have hHead : key ≠ name := by
        intro hEq
        subst key
        exact hNotMem (by simp)
      have hTail : key ∉ names := by
        intro hMem
        exact hNotMem (by simp [hMem])
      calc
        store' key =
            (Locals.Source.Store.insert store name value) key :=
          insertMany_apply_of_not_mem hInsert hTail
        _ = store key :=
          Locals.Source.Store.insert_of_ne hHead

theorem lookupMany_insertMany_self :
    ∀ {names : List Name} {values : List Word}
      {store store' : Store},
      names.Nodup →
      insertMany names values store = some store' →
      lookupMany names store' = some values
  | [], [], _store, _store', _hNodup, hInsert => by
      simp [insertMany] at hInsert
      cases hInsert
      rfl
  | [], _value :: _values, _store, _store', _hNodup, hInsert => by
      simp [insertMany] at hInsert
  | _name :: _names, [], _store, _store', _hNodup, hInsert => by
      simp [insertMany] at hInsert
  | name :: names, value :: values, store, store', hNodup, hInsert => by
      change
        insertMany names values
            (Locals.Source.Store.insert store name value) =
          some store' at hInsert
      have hName :
          store' name = some value := by
        have hPreserved :=
          insertMany_apply_of_not_mem hInsert
            (List.nodup_cons.mp hNodup).1
        simpa using hPreserved
      have hTail :
          lookupMany names store' = some values :=
        lookupMany_insertMany_self
          (List.nodup_cons.mp hNodup).2 hInsert
      unfold lookupMany
      rw [hName]
      simp only [Bind.bind, Option.bind]
      rw [hTail]

theorem initReturns_apply_of_not_mem :
    ∀ {returns : List Name} {store : Store} {key : Name},
      key ∉ returns →
      initReturns returns store key = store key
  | [], _store, _key, _hNotMem => by
      rfl
  | name :: returns, store, key, hNotMem => by
      have hHead : key ≠ name := by
        intro hEq
        subst key
        exact hNotMem (by simp)
      have hTail : key ∉ returns := by
        intro hMem
        exact hNotMem (by simp [hMem])
      calc
        initReturns (name :: returns) store key =
            initReturns returns
              (Locals.Source.Store.insert store name zero) key := rfl
        _ = (Locals.Source.Store.insert store name zero) key :=
          initReturns_apply_of_not_mem hTail
        _ = store key :=
          Locals.Source.Store.insert_of_ne hHead

/--
Every name initialized by `initReturns` maps to the canonical zero word.
-/
theorem initReturns_apply_of_mem :
    ∀ {returns : List Name} {store : Store} {key : Name},
      returns.Nodup →
      key ∈ returns →
      initReturns returns store key = some zero
  | [], _store, _key, _hNodup, hMem => by
      simp at hMem
  | name :: returns, store, key, hNodup, hMem => by
      rcases List.mem_cons.mp hMem with hKey | hTail
      · subst key
        have hFresh := (List.nodup_cons.mp hNodup).1
        change
          initReturns returns
              (Locals.Source.Store.insert store name zero) name =
            some zero
        rw [initReturns_apply_of_not_mem hFresh]
        exact Locals.Source.Store.insert_self store name zero
      · exact
          initReturns_apply_of_mem
            (returns := returns)
            (store := Locals.Source.Store.insert store name zero)
            (key := key)
            (List.nodup_cons.mp hNodup).2 hTail

theorem lookupMany_initReturns_self :
    ∀ {returns : List Name} {store : Store},
      returns.Nodup →
      lookupMany returns (initReturns returns store) =
        some (returns.map fun _name => zero)
  | [], _store, _hNodup => by
      rfl
  | name :: returns, store, hNodup => by
      have hName :
          initReturns returns
              (Locals.Source.Store.insert store name zero) name =
            some zero := by
        have hPreserved :=
          initReturns_apply_of_not_mem
            (returns := returns)
            (store := Locals.Source.Store.insert store name zero)
            (key := name)
            (List.nodup_cons.mp hNodup).1
        simpa using hPreserved
      have hTail :
          lookupMany returns
              (initReturns returns
                (Locals.Source.Store.insert store name zero)) =
            some (returns.map fun _name => zero) :=
        lookupMany_initReturns_self
          (returns := returns)
          (store := Locals.Source.Store.insert store name zero)
          (List.nodup_cons.mp hNodup).2
      change
        (do
          let value ←
            initReturns returns
              (Locals.Source.Store.insert store name zero) name
          let values ←
            lookupMany returns
              (initReturns returns
                (Locals.Source.Store.insert store name zero))
          some (value :: values)) =
        some (zero :: returns.map fun _name => zero)
      rw [hName]
      simp only [Bind.bind, Option.bind]
      rw [hTail]

theorem lookupMany_congr
    {names : List Name} {left right : Store}
    (hEq : ∀ name, name ∈ names → left name = right name) :
    lookupMany names left = lookupMany names right := by
  induction names with
  | nil =>
      rfl
  | cons name rest ih =>
      have hHead := hEq name (by simp)
      have hTail :
          ∀ candidate, candidate ∈ rest →
            left candidate = right candidate := by
        intro candidate hMem
        exact hEq candidate (by simp [hMem])
      simp [lookupMany, hHead, ih hTail]

theorem lookupMany_initReturns_of_disjoint
    {returns params : List Name} {store : Store}
    (hDisjoint :
      ∀ name, name ∈ params → name ∉ returns) :
    lookupMany params (initReturns returns store) =
      lookupMany params store := by
  apply lookupMany_congr
  intro name hParam
  exact initReturns_apply_of_not_mem (hDisjoint name hParam)

/--
The store constructed at function entry realizes the argument list at
parameters and zero at named returns.
-/
theorem initializedStore_lookupMany
    {params returns : List Name} {args : List Word}
    {paramStore : Store}
    (hSignature : (returns ++ params).Nodup)
    (hInsert :
      insertMany params args Locals.Source.Store.empty =
        some paramStore) :
    lookupMany params (initReturns returns paramStore) = some args ∧
    lookupMany returns (initReturns returns paramStore) =
      some (returns.map fun _name => zero) := by
  have hParts := List.nodup_append.mp hSignature
  have hDisjoint :
      ∀ name, name ∈ params → name ∉ returns := by
    intro name hParam hReturn
    exact hParts.2.2 name hReturn name hParam rfl
  constructor
  · rw [lookupMany_initReturns_of_disjoint hDisjoint]
    exact lookupMany_insertMany_self hParts.2.1 hInsert
  · exact lookupMany_initReturns_self hParts.1

theorem lookupMany_forall₂ :
    ∀ {names : List Name} {store : Store} {values : List Word},
      lookupMany names store = some values →
      List.Forall₂ (fun name value => store name = some value)
        names values
  | [], _store, values, hLookup => by
      simp [lookupMany] at hLookup
      subst values
      exact .nil
  | name :: names, store, values, hLookup => by
      cases hValue : store name with
      | none =>
          simp [lookupMany, hValue] at hLookup
      | some value =>
          cases hTail : lookupMany names store with
          | none =>
              simp [lookupMany, hValue, hTail] at hLookup
          | some tail =>
              simp [lookupMany, hValue, hTail] at hLookup
              subst values
              exact .cons hValue (lookupMany_forall₂ hTail)

theorem lookupMany_getElem
    {names : List Name} {store : Store} {values : List Word}
    {index : Nat} {name : Name}
    (hLookup : lookupMany names store = some values)
    (hName : names[index]? = some name) :
    ∃ value,
      values[index]? = some value ∧
        store name = some value := by
  have hPairs := lookupMany_forall₂ hLookup
  clear hLookup
  induction hPairs generalizing index name with
  | nil =>
      simp at hName
  | @cons headName headValue tailNames tailValues hHead _hTail ih =>
      cases index with
      | zero =>
          simp at hName
          subst name
          exact ⟨headValue, by simp, hHead⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at hName
          obtain ⟨value, hValue, hStore⟩ := ih hName
          exact
            ⟨value,
              by simpa only [List.getElem?_cons_succ] using hValue,
              hStore⟩

theorem lookupMany_cons_parts
    {name : Name} {names : List Name} {store : Store}
    {values : List Word}
    (hLookup : lookupMany (name :: names) store = some values) :
    ∃ value tail,
      store name = some value ∧
        lookupMany names store = some tail ∧
        values = value :: tail := by
  cases hValue : store name with
  | none =>
      simp [lookupMany, hValue] at hLookup
  | some value =>
      cases hTail : lookupMany names store with
      | none =>
          simp [lookupMany, hValue, hTail] at hLookup
      | some tail =>
          simp [lookupMany, hValue, hTail] at hLookup
          subst values
          exact ⟨value, tail, rfl, rfl, rfl⟩

private theorem forall₂_append
    {α β : Type} {relation : α → β → Prop}
    {leftNames rightNames : List α}
    {leftValues rightValues : List β}
    (hLeft : List.Forall₂ relation leftNames leftValues)
    (hRight : List.Forall₂ relation rightNames rightValues) :
    List.Forall₂ relation
      (leftNames ++ rightNames) (leftValues ++ rightValues) := by
  induction hLeft with
  | nil =>
      simpa using hRight
  | cons hHead _hTail ih =>
      exact .cons hHead ih

private theorem forall₂_reverse
    {α β : Type} {relation : α → β → Prop}
    {names : List α} {values : List β}
    (hPairs : List.Forall₂ relation names values) :
    List.Forall₂ relation names.reverse values.reverse := by
  induction hPairs with
  | nil =>
      exact .nil
  | @cons name value names values hHead _hTail ih =>
      simpa using
        forall₂_append ih
          (List.Forall₂.cons hHead List.Forall₂.nil)

theorem lookupMany_of_forall₂
    {names : List Name} {store : Store} {values : List Word}
    (hPairs :
      List.Forall₂ (fun name value => store name = some value)
        names values) :
    lookupMany names store = some values := by
  induction hPairs with
  | nil =>
      rfl
  | cons hHead _hTail ih =>
      unfold lookupMany
      rw [hHead]
      simp only [Bind.bind, Option.bind]
      rw [ih]

theorem lookupMany_reverse
    {names : List Name} {store : Store} {values : List Word}
    (hLookup : lookupMany names store = some values) :
    lookupMany names.reverse store = some values.reverse :=
  lookupMany_of_forall₂
    (forall₂_reverse (lookupMany_forall₂ hLookup))

theorem lookupMany_length :
    ∀ {names : List Name} {store : Store} {values : List Word},
      lookupMany names store = some values →
        values.length = names.length
  | [], _store, _values, hLookup => by
      simp [lookupMany] at hLookup
      cases hLookup
      simp
  | name :: names, store, values, hLookup => by
      unfold lookupMany at hLookup
      cases hName : store name with
      | none =>
          simp [hName] at hLookup
      | some value =>
          simp [hName] at hLookup
          cases hTail : lookupMany names store with
          | none =>
              simp [hTail] at hLookup
          | some tailValues =>
              simp [hTail] at hLookup
              cases hLookup
              have hTailLength :=
                lookupMany_length
                  (names := names) (store := store)
                  (values := tailValues) hTail
              simp [hTailLength]

theorem lookupMany_restrictTo_of_mem :
    ∀ {names scope : List Name} {store : Store} {values : List Word},
      (∀ name, name ∈ names → name ∈ scope) →
      lookupMany names store = some values →
        lookupMany names (Locals.Source.Store.restrictTo scope store) =
          some values
  | [], _scope, _store, _values, _hMem, hLookup => by
      simp [lookupMany] at hLookup ⊢
      cases hLookup
      rfl
  | name :: rest, scope, store, values, hMem, hLookup => by
      unfold lookupMany at hLookup
      have hNameMem : name ∈ scope :=
        hMem name (by simp)
      have hRestrictedName :
          Locals.Source.Store.restrictTo scope store name = store name :=
        Locals.Source.Store.restrictTo_mem hNameMem
      cases hName : store name with
      | none =>
          simp [hName] at hLookup
      | some value =>
          simp [hName] at hLookup
          cases hTail : lookupMany rest store with
          | none =>
              simp [hTail] at hLookup
          | some tailValues =>
              simp [hTail] at hLookup
              cases hLookup
              have hRestMem :
                  ∀ restName, restName ∈ rest → restName ∈ scope := by
                intro restName hRestName
                exact hMem restName (by simp [hRestName])
              have hTailRestrict :=
                lookupMany_restrictTo_of_mem
                  (names := rest) (scope := scope) (store := store)
                  (values := tailValues) hRestMem hTail
              simp [lookupMany, hRestrictedName, hName, hTailRestrict]

theorem assignMany_length :
    ∀ {names : List Name} {values : List Word} {store store' : Store},
      assignMany names values store = some store' →
        values.length = names.length
  | [], [], _store, _store', hAssign => by
      simp [assignMany] at hAssign
      cases hAssign
      simp
  | [], _value :: _values, _store, _store', hAssign => by
      simp [assignMany] at hAssign
  | _name :: _names, [], _store, _store', hAssign => by
      simp [assignMany] at hAssign
  | name :: names, value :: values, store, store', hAssign => by
      unfold assignMany at hAssign
      by_cases hContains : store.contains name
      · simp [hContains] at hAssign
        have hTail :=
          assignMany_length
            (names := names) (values := values)
            (store := Locals.Source.Store.insert store name value)
            (store' := store') hAssign
        simp [hTail]
      · simp [hContains] at hAssign

theorem assignMany_append :
    ∀ {names suffixNames : List Name}
      {wordValues suffixWordValues : List Word} {store : Store},
      wordValues.length = names.length →
        assignMany (names ++ suffixNames) (wordValues ++ suffixWordValues)
            store =
          match assignMany names wordValues store with
          | some store' => assignMany suffixNames suffixWordValues store'
          | none => none
  | [], suffixNames, [], suffixWordValues, store, _hLen => by
      simp [assignMany]
  | [], suffixNames, _value :: _values, suffixWordValues, store, hLen => by
      simp at hLen
  | _name :: _names, suffixNames, [], suffixWordValues, store, hLen => by
      simp at hLen
  | name :: names, suffixNames, value :: wordValues, suffixWordValues, store,
      hLen => by
      simp at hLen
      unfold assignMany
      by_cases hContains : store.contains name
      · simp [hContains]
        cases suffixNames with
        | nil =>
            cases suffixWordValues with
            | nil =>
                simpa [assignMany] using
                  (assignMany_append
                    (names := names) (wordValues := wordValues)
                    (suffixNames := [])
                    (suffixWordValues := [])
                    (store := Locals.Source.Store.insert store name value)
                    hLen)
            | cons suffixValue suffixValues =>
                simpa [assignMany] using
                  (assignMany_append
                    (names := names) (wordValues := wordValues)
                    (suffixNames := [])
                    (suffixWordValues := suffixValue :: suffixValues)
                    (store := Locals.Source.Store.insert store name value)
                    hLen)
        | cons suffixName suffixNames =>
            cases suffixWordValues with
            | nil =>
                simpa [assignMany] using
                  (assignMany_append
                    (names := names) (wordValues := wordValues)
                    (suffixNames := suffixName :: suffixNames)
                    (suffixWordValues := [])
                    (store := Locals.Source.Store.insert store name value)
                    hLen)
            | cons suffixValue suffixValues =>
                simpa [assignMany] using
                  (assignMany_append
                    (names := names) (wordValues := wordValues)
                    (suffixNames := suffixName :: suffixNames)
                    (suffixWordValues := suffixValue :: suffixValues)
                    (store := Locals.Source.Store.insert store name value)
                    hLen)
      · simp [hContains]

theorem contains_insert_of_ne {store : Store} {name other : Name}
    {value : Word}
    (hNe : name ≠ other) :
    (Locals.Source.Store.insert store other value).contains name =
      store.contains name := by
  simp [Locals.Source.Store.contains, Locals.Source.Store.insert, hNe]

theorem assignMany_preserves_contains_of_not_mem :
    ∀ {names : List Name} {values : List Word} {store store' : Store}
      {name : Name},
      assignMany names values store = some store' →
        name ∉ names →
          store'.contains name = store.contains name
  | [], [], store, store', name, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
      cases hAssign
      rfl
  | [], _value :: _values, store, store', name, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
  | _head :: _tail, [], store, store', name, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
  | head :: tail, value :: values, store, store', name, hAssign, hNotMem => by
      unfold assignMany at hAssign
      by_cases hContains : store.contains head
      · simp [hContains] at hAssign
        have hNameNe : name ≠ head := by
          intro hEq
          subst head
          exact hNotMem (by simp)
        have hTailNotMem : name ∉ tail := by
          intro hMem
          exact hNotMem (by simp [hMem])
        have hTail :=
          assignMany_preserves_contains_of_not_mem
            (names := tail) (values := values)
            (store := Locals.Source.Store.insert store head value)
            (store' := store') (name := name) hAssign hTailNotMem
        calc
          store'.contains name =
              (Locals.Source.Store.insert store head value).contains name :=
            hTail
          _ = store.contains name :=
            contains_insert_of_ne hNameNe
      · simp [hContains] at hAssign

theorem assignMany_snoc_of_run {names : List Name} {values : List Word}
    {store store' : Store} {name : Name} {value : Word}
    (hAssign : assignMany names values store = some store')
    (hLen : values.length = names.length)
    (hNotMem : name ∉ names)
    (hContains : store.contains name = true) :
    assignMany (names ++ [name]) (values ++ [value]) store =
      some (Locals.Source.Store.insert store' name value) := by
  rw [assignMany_append (names := names) (wordValues := values)
    (suffixNames := [name]) (suffixWordValues := [value]) hLen]
  simp [hAssign]
  have hContains' :=
    assignMany_preserves_contains_of_not_mem
      (names := names) (values := values) (store := store)
      (store' := store') (name := name) hAssign hNotMem
  have hContainsStore' : store'.contains name = true :=
    hContains'.trans hContains
  simp [assignMany, hContainsStore']

theorem insert_comm_of_ne {store : Store} {left right : Name}
    {leftValue rightValue : Word}
    (hNe : left ≠ right) :
    Locals.Source.Store.insert
        (Locals.Source.Store.insert store left leftValue) right rightValue =
      Locals.Source.Store.insert
        (Locals.Source.Store.insert store right rightValue) left leftValue := by
  funext key
  by_cases hRight : key = right
  · subst key
    have hRightLeft : right ≠ left := hNe.symm
    simp [Locals.Source.Store.insert, hNe, hRightLeft]
  · by_cases hLeft : key = left
    · subst key
      simp [Locals.Source.Store.insert, hRight]
    · simp [Locals.Source.Store.insert, hLeft, hRight]

theorem assignMany_commute_insert_of_not_mem :
    ∀ {names : List Name} {values : List Word} {store store' : Store}
      {protectedName : Name} {protectedValue : Word},
      assignMany names values store = some store' →
        protectedName ∉ names →
          assignMany names values
              (Locals.Source.Store.insert store protectedName protectedValue) =
            some
              (Locals.Source.Store.insert store' protectedName
                protectedValue)
  | [], [], store, store', protectedName, protectedValue, hAssign,
      _hNotMem => by
      simp [assignMany] at hAssign
      cases hAssign
      simp [assignMany]
  | [], _value :: _values, _store, _store', _protectedName,
      _protectedValue, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
  | _head :: _tail, [], _store, _store', _protectedName,
      _protectedValue, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
  | head :: tail, value :: values, store, store', protectedName,
      protectedValue, hAssign, hNotMem => by
      unfold assignMany at hAssign ⊢
      by_cases hContains : store.contains head
      · simp [hContains] at hAssign
        have hHeadNe : head ≠ protectedName := by
          intro hEq
          subst protectedName
          exact hNotMem (by simp)
        have hTailNotMem : protectedName ∉ tail := by
          intro hMem
          exact hNotMem (by simp [hMem])
        have hContainsInserted :
            Locals.Source.Store.contains
                (Locals.Source.Store.insert store protectedName
                  protectedValue) head = true := by
          have hPreserve :=
            contains_insert_of_ne (store := store) (name := head)
              (other := protectedName) (value := protectedValue) hHeadNe
          simpa [hContains] using hPreserve
        rw [hContainsInserted]
        simp
        have hComm :
            Locals.Source.Store.insert
                (Locals.Source.Store.insert store protectedName
                  protectedValue) head value =
              Locals.Source.Store.insert
                (Locals.Source.Store.insert store head value)
                protectedName protectedValue :=
          insert_comm_of_ne (store := store) (left := protectedName)
            (right := head) (leftValue := protectedValue)
            (rightValue := value) hHeadNe.symm
        rw [hComm]
        exact assignMany_commute_insert_of_not_mem hAssign hTailNotMem
      · simp [hContains] at hAssign

theorem assignMany_remove_insert_of_not_mem :
    ∀ {names : List Name} {values : List Word} {store store' : Store}
      {protectedName : Name} {protectedValue : Word},
      assignMany names values
          (Locals.Source.Store.insert store protectedName protectedValue) =
          some store' →
        protectedName ∉ names →
          ∃ base,
            assignMany names values store = some base ∧
              store' =
                Locals.Source.Store.insert base protectedName protectedValue
  | [], [], store, store', protectedName, protectedValue, hAssign,
      _hNotMem => by
      simp [assignMany] at hAssign
      cases hAssign
      exact ⟨store, by simp [assignMany], rfl⟩
  | [], _value :: _values, _store, _store', _protectedName,
      _protectedValue, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
  | _head :: _tail, [], _store, _store', _protectedName,
      _protectedValue, hAssign, _hNotMem => by
      simp [assignMany] at hAssign
  | head :: tail, value :: values, store, store', protectedName,
      protectedValue, hAssign, hNotMem => by
      unfold assignMany at hAssign
      have hHeadNe : head ≠ protectedName := by
        intro hEq
        subst protectedName
        exact hNotMem (by simp)
      have hContainsInserted :
          Locals.Source.Store.contains
              (Locals.Source.Store.insert store protectedName protectedValue)
              head = store.contains head := by
        exact
          contains_insert_of_ne (store := store) (name := head)
            (other := protectedName) (value := protectedValue) hHeadNe
      rw [hContainsInserted] at hAssign
      by_cases hContains : store.contains head
      · simp [hContains] at hAssign
        have hTailNotMem : protectedName ∉ tail := by
          intro hMem
          exact hNotMem (by simp [hMem])
        have hComm :
            Locals.Source.Store.insert
                (Locals.Source.Store.insert store protectedName
                  protectedValue) head value =
              Locals.Source.Store.insert
                (Locals.Source.Store.insert store head value)
                protectedName protectedValue :=
          insert_comm_of_ne (store := store) (left := protectedName)
            (right := head) (leftValue := protectedValue)
            (rightValue := value) hHeadNe.symm
        rw [hComm] at hAssign
        rcases assignMany_remove_insert_of_not_mem hAssign hTailNotMem with
          ⟨base, hBase, hStore'⟩
        refine ⟨base, ?hOriginal, hStore'⟩
        unfold assignMany
        simp [hContains, hBase]
      · simp [hContains] at hAssign

theorem assignMany_reverse_of_run :
    ∀ {names : List Name} {values : List Word} {store store' : Store},
      assignMany names values store = some store' →
        names.Nodup →
          assignMany names.reverse values.reverse store = some store'
  | [], [], _store, _store', hAssign, _hNoDup => by
      simp [assignMany] at hAssign
      cases hAssign
      simp [assignMany]
  | [], _value :: _values, _store, _store', hAssign, _hNoDup => by
      simp [assignMany] at hAssign
  | _name :: _names, [], _store, _store', hAssign, _hNoDup => by
      simp [assignMany] at hAssign
  | name :: names, value :: values, store, store', hAssign, hNoDup => by
      unfold assignMany at hAssign
      by_cases hContains : store.contains name
      · simp [hContains] at hAssign
        cases hNoDup with
        | cons hNameNotMem hNamesNoDup =>
            have hNameNotMem' : name ∉ names := by
              intro hMem
              exact hNameNotMem name hMem rfl
            rcases assignMany_remove_insert_of_not_mem hAssign
                hNameNotMem' with
              ⟨base, hBase, hStore'⟩
            have hReverseBase :=
              assignMany_reverse_of_run hBase hNamesNoDup
            have hLen : values.reverse.length = names.reverse.length := by
              have hBaseLen := assignMany_length hBase
              simp [hBaseLen]
            have hNameNotMemReverse : name ∉ names.reverse := by
              intro hMem
              exact hNameNotMem' (by simpa using hMem)
            have hSnoc :=
              assignMany_snoc_of_run
                (names := names.reverse) (values := values.reverse)
                (store := store) (store' := base) (name := name)
                (value := value) hReverseBase hLen hNameNotMemReverse
                hContains
            simpa [List.reverse_cons, hStore'] using hSnoc
      · simp [hContains] at hAssign

end Store

inductive CallResult where
  | returned (shared : EvmYul.SharedState .EVM) (values : List Word)
  | halted (kind : Assembly.HaltKind) (state : State)

namespace Switch

def select (scrutinee : Word) :
    List (Word × Block) → Option Block → Option Block
  | [], defaultBody => defaultBody
  | (value, body) :: rest, defaultBody =>
      if value = scrutinee then
        some body
      else
        select scrutinee rest defaultBody

end Switch

namespace FunList

def find? (name : Name) : List FunDef → Option FunDef
  | [] => none
  | fn :: rest =>
      if fn.name = name then
        some fn
      else
        find? name rest

theorem mem_of_find?_eq_some
    {name : Name} {functions : List FunDef} {fn : FunDef}
    (hFind : find? name functions = some fn) :
    fn ∈ functions := by
  induction functions with
  | nil =>
      simp [find?] at hFind
  | cons head rest ih =>
      by_cases hName : head.name = name
      · simp [find?, hName] at hFind
        subst fn
        simp
      · have hTail : find? name rest = some fn := by
          simpa [find?, hName] using hFind
        exact List.mem_cons_of_mem head (ih hTail)

end FunList

mutual
  def Block.runOpen (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) : Nat → Block → State →
      Except EVMException (Outcome × Ctx)
    | 0, _block, _state =>
        invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ← Stmt.run prim program ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen prim program ctx' fuel { stmts := rest }
              outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) (block : Block) (fuel : Nat) (state : State) :
      Except EVMException Outcome := do
    let (outcome, _) ← Block.runOpen prim program ctx fuel block state
    match outcome.mode with
    | .regular =>
        .ok (Outcome.regular (outcome.state.restrictTo ctx.scope))
    | .brk | .cont | .leave | .halt _ =>
        .ok outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def FunDef.runBody (prim : PrimitiveSemantics) (program : Program)
      (fn : FunDef) (args : List Word) :
      Nat → EvmYul.SharedState .EVM →
      Except EVMException CallResult
    | 0, _shared =>
        invalid
    | fuel + 1, shared => do
        let paramStore ←
          (Store.insertMany fn.params args Locals.Source.Store.empty).elim
            invalid pure
        let initialStore := Store.initReturns fn.returns paramStore
        let initialState : State := { shared := shared, vars := initialStore }
        let functionScope := fn.returns ++ fn.params
        let bodyCtx := (Ctx.initial.withLeaveScope functionScope)
        let bodyCtx := { bodyCtx with scope := functionScope }
        let (bodyOutcome, _bodyFinalCtx) ←
          Block.runOpen prim program bodyCtx fuel fn.body initialState
        match bodyOutcome.mode with
        | .regular | .leave =>
            let values ←
              (Store.lookupMany fn.returns bodyOutcome.state.vars).elim
                invalid pure
            .ok (.returned bodyOutcome.state.shared values)
        | .brk | .cont =>
            invalid
        | .halt kind =>
            .ok (.halted kind bodyOutcome.state)
  termination_by fuel _shared => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runForLoop (prim : PrimitiveSemantics) (program : Program)
      (loopCtx : Ctx) (cond : Expr 1) (postBase : Ctx) (post : Block)
      (bodyBase : Ctx) (body : Block) :
      Nat → State → Except EVMException Outcome
    | 0, _state =>
        invalid
    | fuel + 1, state =>
        match Expr.evalCondition prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.runScoped prim program bodyBase body fuel
                  stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.runScoped prim program postBase post fuel
                          bodyOutcome.state with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop prim program loopCtx cond
                                postBase post bodyBase body fuel
                                postOutcome.state
                          | .brk | .cont =>
                              invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Outcome.regular (stateAfterCond.restrictTo loopCtx.scope))
  termination_by fuel _state => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run (prim : PrimitiveSemantics) (program : Program)
      (ctx : Ctx) : Nat → Stmt → State →
      Except EVMException (Outcome × Ctx)
    | _fuel, .expr expr, state => do
        let (state', _values) ← Expr.eval prim expr state
        .ok (Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let (stateAfterValue, value') ← Expr.evalOne prim value state
        .ok (Outcome.regular
          (stateAfterValue.insert name value'),
          { ctx with scope := name :: ctx.scope })
    | _fuel, .assign name value, state => do
        if state.vars.contains name then
          let (stateAfterValue, value') ← Expr.evalOne prim value state
          .ok (Outcome.regular
            (stateAfterValue.withVars
              (Locals.Source.Store.insert stateAfterValue.vars name value')),
            ctx)
        else
          invalid
    | fuel, .block body, state => do
        let outcome ← Block.runScoped prim program ctx body fuel state
        .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        invalid
    | fuel + 1, .if_ cond body, state =>
        match Expr.evalCondition prim cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then do
              let outcome ← Block.runScoped prim program ctx body fuel
                stateAfterCond
              .ok (outcome, ctx)
            else
              .ok (Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let (stateAfterScrutinee, value) ← Expr.evalOne prim scrutinee state
        match Switch.select value cases defaultBody with
        | none => .ok (Outcome.regular stateAfterScrutinee, ctx)
        | some body =>
            let outcome ← Block.runScoped prim program ctx body fuel
              stateAfterScrutinee
            .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx) ←
          Block.runOpen prim program initBase fuel init state
        match initOutcome.mode with
        | .regular =>
            let loopCtx := initCtx
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.scope initCtx.scope
            let loopOutcome ←
              Stmt.runForLoop prim program loopCtx cond postBase post
                bodyBase body fuel initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                .ok (Outcome.regular (loopOutcome.state.restrictTo ctx.scope),
                  ctx)
            | .brk | .cont =>
                invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx)
        | .brk | .cont =>
            invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx)
    | _fuel, .brk, state =>
        match ctx.breakScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.brk (state.restrictTo scope), ctx)
    | _fuel, .cont, state =>
        match ctx.continueScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.cont (state.restrictTo scope), ctx)
    | _fuel, .leave, state =>
        match ctx.leaveScope? with
        | none => invalid
        | some scope =>
            .ok (Outcome.leave (state.restrictTo scope), ctx)
    | 0, .call _targets _functionName _args, _state =>
        invalid
    | fuel + 1, .call targets functionName args, state => do
        if targets.Nodup then
          let (stateAfterArgs, argValues) ← ArgList.eval prim args state
          let fn ← (FunList.find? functionName program.functions).elim
            invalid pure
          let callResult ←
            FunDef.runBody prim program fn argValues fuel stateAfterArgs.shared
          match callResult with
          | .returned sharedAfterCall returnValues =>
              let returnStore ←
                (Store.assignMany targets returnValues stateAfterArgs.vars).elim
                  invalid pure
              .ok (Outcome.regular
                { shared := sharedAfterCall, vars := returnStore }, ctx)
          | .halted kind haltedState =>
              .ok (Outcome.halt kind haltedState, ctx)
        else
          invalid
    | _fuel, .terminal kind, state => do
        let shared ← prim.terminal kind state.shared []
        .ok (Outcome.halt kind (state.withShared shared), ctx)
    | _fuel, .terminalArgs kind args, state => do
        let (stateAfterArgs, values) ←
          Locals.Source.Expr.ExprSeq.eval prim args state
        let shared ← prim.terminal kind stateAfterArgs.shared values
        .ok (Outcome.halt kind (stateAfterArgs.withShared shared), ctx)
  termination_by fuel stmt _state => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Stmt

theorem run_nonregular_ctx {prim : PrimitiveSemantics} {program : Program}
    {ctx runCtx : Ctx} {fuel : Nat} {stmt : Stmt} {state : State}
    {outcome : Outcome}
    (hRun :
      Stmt.run prim program ctx fuel stmt state = .ok (outcome, runCtx))
    (hNonregular : outcome.mode ≠ .regular) :
    runCtx = ctx := by
  cases stmt with
  | expr expr =>
      unfold Stmt.run at hRun
      cases hEval : Expr.eval prim expr state with
      | error err =>
          simp [hEval] at hRun
      | ok result =>
          rcases result with ⟨stateAfter, values⟩
          simp [hEval] at hRun
          cases hRun.1
          exact False.elim (hNonregular rfl)
  | let_ name value =>
      unfold Stmt.run at hRun
      cases hEval : Expr.evalOne prim value state with
      | error err =>
          simp [hEval] at hRun
      | ok result =>
          rcases result with ⟨stateAfter, value'⟩
          simp [hEval] at hRun
          cases hRun.1
          exact False.elim (hNonregular rfl)
  | assign name value =>
      unfold Stmt.run at hRun
      cases hContains : state.vars.contains name with
      | false =>
          simp [hContains, invalid, Structured.invalid] at hRun
      | true =>
          cases hEval : Expr.evalOne prim value state with
          | error err =>
              simp [hContains, hEval] at hRun
          | ok result =>
              rcases result with ⟨stateAfter, value'⟩
              simp [hContains, hEval] at hRun
              cases hRun.1
              exact False.elim (hNonregular rfl)
  | block body =>
      unfold Stmt.run at hRun
      cases hScoped : Block.runScoped prim program ctx body fuel state with
      | error err =>
          simp [hScoped] at hRun
      | ok bodyOutcome =>
          simp [hScoped] at hRun
          exact hRun.2.symm
  | if_ cond body =>
      cases fuel with
      | zero =>
          simp [Stmt.run, invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          cases hCond : Expr.evalCondition prim cond state with
          | error err =>
              simp [hCond] at hRun
          | ok condResult =>
              rcases condResult with ⟨stateAfterCond, condTrue⟩
              cases condTrue
              · simp [hCond] at hRun
                exact hRun.2.symm
              · cases hScoped :
                    Block.runScoped prim program ctx body fuel stateAfterCond with
                | error err =>
                    simp [hCond, hScoped] at hRun
                | ok bodyOutcome =>
                    simp [hCond, hScoped] at hRun
                    exact hRun.2.symm
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          simp [Stmt.run, invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          cases hScrutinee : Expr.evalOne prim scrutinee state with
          | error err =>
              simp [hScrutinee] at hRun
          | ok scrutineeResult =>
              rcases scrutineeResult with ⟨stateAfterScrutinee, value⟩
              cases hSelect : Switch.select value cases defaultBody with
              | none =>
                  simp [hScrutinee, hSelect] at hRun
                  exact hRun.2.symm
              | some body =>
                  cases hScoped :
                      Block.runScoped prim program ctx body fuel
                        stateAfterScrutinee with
                  | error err =>
                      simp [hScrutinee, hSelect, hScoped] at hRun
                  | ok bodyOutcome =>
                      simp [hScrutinee, hSelect, hScoped] at hRun
                      exact hRun.2.symm
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          simp [Stmt.run, invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          cases hInit :
              Block.runOpen prim program ctx.withoutLoopControl fuel init
                state with
          | error err =>
              simp [hInit] at hRun
          | ok initResult =>
              rcases initResult with ⟨initOutcome, initCtx⟩
              cases hInitMode : initOutcome.mode with
              | regular =>
                  cases hLoop :
                      runForLoop prim program initCtx cond
                        initCtx.withoutLoopControl post
                        (initCtx.withLoopControl initCtx.scope initCtx.scope)
                        body fuel initOutcome.state with
                  | error err =>
                      simp [hInit, hInitMode, hLoop] at hRun
                  | ok loopOutcome =>
                      cases hLoopMode : loopOutcome.mode with
                      | regular =>
                          simp [hInit, hInitMode, hLoop, hLoopMode] at hRun
                          exact hRun.2.symm
                      | brk =>
                          simp [hInit, hInitMode, hLoop, hLoopMode, invalid,
                            Structured.invalid] at hRun
                      | cont =>
                          simp [hInit, hInitMode, hLoop, hLoopMode, invalid,
                            Structured.invalid] at hRun
                      | leave =>
                          simp [hInit, hInitMode, hLoop, hLoopMode] at hRun
                          exact hRun.2.symm
                      | halt kind =>
                          simp [hInit, hInitMode, hLoop, hLoopMode] at hRun
                          exact hRun.2.symm
              | brk =>
                  simp [hInit, hInitMode, invalid, Structured.invalid] at hRun
              | cont =>
                  simp [hInit, hInitMode, invalid, Structured.invalid] at hRun
              | leave =>
                  simp [hInit, hInitMode] at hRun
                  exact hRun.2.symm
              | halt kind =>
                  simp [hInit, hInitMode] at hRun
                  exact hRun.2.symm
  | brk =>
      unfold Stmt.run at hRun
      cases hBreak : ctx.breakScope? with
      | none =>
          simp [hBreak, invalid, Structured.invalid] at hRun
      | some scope =>
          simp [hBreak] at hRun
          exact hRun.2.symm
  | cont =>
      unfold Stmt.run at hRun
      cases hContinue : ctx.continueScope? with
      | none =>
          simp [hContinue, invalid, Structured.invalid] at hRun
      | some scope =>
          simp [hContinue] at hRun
          exact hRun.2.symm
  | leave =>
      unfold Stmt.run at hRun
      cases hLeave : ctx.leaveScope? with
      | none =>
          simp [hLeave, invalid, Structured.invalid] at hRun
      | some scope =>
          simp [hLeave] at hRun
          exact hRun.2.symm
  | call targets functionName args =>
      cases fuel with
      | zero =>
          simp [Stmt.run, invalid, Structured.invalid] at hRun
      | succ fuel =>
          unfold Stmt.run at hRun
          by_cases hTargets : targets.Nodup
          ·
              cases hArgs : ArgList.eval prim args state with
              | error err =>
                  simp [hTargets, hArgs] at hRun
              | ok argResult =>
                  rcases argResult with ⟨stateAfterArgs, argValues⟩
                  cases hFind : FunList.find? functionName program.functions with
                  | none =>
                      simp [hTargets, hArgs, hFind, invalid,
                        Structured.invalid] at hRun
                  | some fn =>
                      cases hBody :
                          FunDef.runBody prim program fn argValues fuel
                            stateAfterArgs.shared with
                      | error err =>
                          simp [hTargets, hArgs, hFind, hBody] at hRun
                      | ok callResult =>
                          cases callResult with
                          | returned sharedAfterCall returnValues =>
                              cases hAssign :
                                  Store.assignMany targets returnValues
                                    stateAfterArgs.vars with
                              | none =>
                                  simp [hTargets, hArgs, hFind, hBody, hAssign,
                                    invalid, Structured.invalid] at hRun
                              | some returnStore =>
                                  simp [hTargets, hArgs, hFind, hBody, hAssign]
                                    at hRun
                                  cases hRun.1
                                  exact False.elim (hNonregular rfl)
                          | halted kind haltedState =>
                              simp [hTargets, hArgs, hFind, hBody] at hRun
                              exact hRun.2.symm
          · simp [hTargets, invalid, Structured.invalid] at hRun
  | terminal kind =>
      unfold Stmt.run at hRun
      cases hTerminal : prim.terminal kind state.shared [] with
      | error err =>
          simp [hTerminal] at hRun
      | ok shared =>
          simp [hTerminal] at hRun
          exact hRun.2.symm
  | terminalArgs kind args =>
      unfold Stmt.run at hRun
      cases hArgs : Locals.Source.Expr.ExprSeq.eval prim args state with
      | error err =>
          simp [hArgs] at hRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, values⟩
          cases hTerminal : prim.terminal kind stateAfterArgs.shared values with
          | error err =>
              simp [hArgs, hTerminal] at hRun
          | ok shared =>
              simp [hArgs, hTerminal] at hRun
              exact hRun.2.symm

end Stmt

set_option maxHeartbeats 1000000 in
mutual
  theorem Block.runOpen_mono (prim : PrimitiveSemantics)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Block}
        {state : State} {outcome : Outcome} {runCtx : Ctx},
        fuel ≤ fuel' →
        Block.runOpen prim program ctx fuel block state =
          .ok (outcome, runCtx) →
        Block.runOpen prim program ctx fuel' block state =
          .ok (outcome, runCtx) := by
    intro fuel fuel' ctx block state outcome runCtx hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.runOpen, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            cases block with
            | mk stmts =>
                cases stmts with
                | nil =>
                    simpa [Block.runOpen] using hRun
                | cons stmt rest =>
                    cases hStmt :
                        Stmt.run prim program ctx fuel stmt state with
                    | error err =>
                        simp [Block.runOpen, hStmt] at hRun
                    | ok stmtResult =>
                        rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
                        have hStmt' :
                            Stmt.run prim program ctx fuel' stmt state =
                              .ok (stmtOutcome, stmtCtx) :=
                          Stmt.run_mono prim program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact
                              Block.runOpen_mono prim program hFuelLe hRun
                        | brk =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Block.runOpen, hStmt, hStmt', hMode]
                              at hRun ⊢
                            exact hRun
  termination_by
    fuel _fuel' _ctx block _state _outcome _runCtx _hLe _hRun =>
      (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_mono (prim : PrimitiveSemantics)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {block : Block}
        {state : State} {outcome : Outcome},
        fuel ≤ fuel' →
        Block.runScoped prim program ctx block fuel state = .ok outcome →
        Block.runScoped prim program ctx block fuel' state = .ok outcome := by
    intro fuel fuel' ctx block state outcome hLe hRun
    unfold Block.runScoped at hRun ⊢
    cases hOpen : Block.runOpen prim program ctx fuel block state with
    | error err =>
        simp [hOpen] at hRun
    | ok openResult =>
        rcases openResult with ⟨openOutcome, finalCtx⟩
        have hOpen' :
            Block.runOpen prim program ctx fuel' block state =
              .ok (openOutcome, finalCtx) :=
          Block.runOpen_mono prim program hLe hOpen
        cases hMode : openOutcome.mode with
        | regular =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | brk =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | cont =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | leave =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
        | halt kind =>
            simp [hOpen, hOpen', hMode] at hRun ⊢
            exact hRun
  termination_by
    fuel _fuel' _ctx block _state _outcome _hLe _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem FunDef.runBody_mono (prim : PrimitiveSemantics)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {fn : FunDef} {args : List Word}
        {shared : EvmYul.SharedState .EVM} {result : CallResult},
        fuel ≤ fuel' →
        FunDef.runBody prim program fn args fuel shared = .ok result →
        FunDef.runBody prim program fn args fuel' shared = .ok result := by
    intro fuel fuel' fn args shared result hLe hRun
    cases fuel with
    | zero =>
        simp [FunDef.runBody, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            cases hParams :
                Store.insertMany fn.params args Locals.Source.Store.empty with
            | none =>
                simp [FunDef.runBody, hParams, invalid, Structured.invalid]
                  at hRun
            | some paramStore =>
                cases hBody :
                    Block.runOpen prim program
                      { (Ctx.initial.withLeaveScope
                          (fn.returns ++ fn.params)) with
                        scope := fn.returns ++ fn.params }
                      fuel fn.body
                      { shared := shared,
                        vars := Store.initReturns fn.returns paramStore } with
                | error err =>
                    simp [FunDef.runBody, hParams, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with ⟨bodyOutcome, bodyFinalCtx⟩
                    have hBody' :
                        Block.runOpen prim program
                            { (Ctx.initial.withLeaveScope
                                (fn.returns ++ fn.params)) with
                              scope := fn.returns ++ fn.params }
                            fuel' fn.body
                            { shared := shared,
                              vars :=
                                Store.initReturns fn.returns paramStore } =
                          .ok (bodyOutcome, bodyFinalCtx) :=
                      Block.runOpen_mono prim program hFuelLe hBody
                    cases hMode : bodyOutcome.mode with
                    | regular =>
                        simp [FunDef.runBody, hParams, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
                    | brk =>
                        simp [FunDef.runBody, hParams, hBody, hBody', hMode,
                          invalid, Structured.invalid] at hRun
                    | cont =>
                        simp [FunDef.runBody, hParams, hBody, hBody', hMode,
                          invalid, Structured.invalid] at hRun
                    | leave =>
                        simp [FunDef.runBody, hParams, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [FunDef.runBody, hParams, hBody, hBody', hMode]
                          at hRun ⊢
                        exact hRun
  termination_by
    fuel _fuel' fn _args _shared _result _hLe _hRun =>
      (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.runForLoop_mono (prim : PrimitiveSemantics)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {loopCtx : Ctx}
        {cond : Expr 1} {postBase : Ctx} {post : Block}
        {bodyBase : Ctx} {body : Block} {state : State}
        {outcome : Outcome},
        fuel ≤ fuel' →
        Stmt.runForLoop prim program loopCtx cond postBase post bodyBase body
          fuel state = .ok outcome →
        Stmt.runForLoop prim program loopCtx cond postBase post bodyBase body
          fuel' state = .ok outcome := by
    intro fuel fuel' loopCtx cond postBase post bodyBase body state outcome
      hLe hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Stmt.runForLoop at hRun ⊢
            cases hCond : Expr.evalCondition prim cond state with
            | error err =>
                simp [hCond] at hRun ⊢
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                cases condTrue with
                | false =>
                    simp [hCond] at hRun ⊢
                    exact hRun
                | true =>
                    simp [hCond] at hRun ⊢
                    cases hBody :
                        Block.runScoped prim program bodyBase body fuel
                          stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Block.runScoped prim program bodyBase body fuel'
                              stateAfterCond = .ok bodyOutcome :=
                          Block.runScoped_mono prim program hFuelLe hBody
                        cases hBodyMode : bodyOutcome.mode with
                        | brk =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | regular =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScoped prim program postBase post fuel
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped prim program postBase post
                                      fuel' bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.runScoped_mono prim program hFuelLe
                                    hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono prim program
                                        hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | cont =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.runScoped prim program postBase post fuel
                                  bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.runScoped prim program postBase post
                                      fuel' bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.runScoped_mono prim program hFuelLe
                                    hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono prim program
                                        hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | leave =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
  termination_by
    fuel _fuel' _loopCtx _cond _postBase _post _bodyBase _body _state
      _outcome _hLe _hRun => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_mono (prim : PrimitiveSemantics)
      (program : Program) :
      ∀ {fuel fuel' : Nat} {ctx : Ctx} {stmt : Stmt} {state : State}
        {outcome : Outcome} {runCtx : Ctx},
        fuel ≤ fuel' →
        Stmt.run prim program ctx fuel stmt state =
          .ok (outcome, runCtx) →
        Stmt.run prim program ctx fuel' stmt state =
          .ok (outcome, runCtx) := by
    intro fuel fuel' ctx stmt state outcome runCtx hLe hRun
    cases stmt with
    | expr expr =>
        simpa [Stmt.run] using hRun
    | let_ name value =>
        simpa [Stmt.run] using hRun
    | assign name value =>
        simpa [Stmt.run] using hRun
    | block body =>
        unfold Stmt.run at hRun ⊢
        cases hBody : Block.runScoped prim program ctx body fuel state with
        | error err =>
            simp [hBody] at hRun
        | ok bodyOutcome =>
            have hBody' :
                Block.runScoped prim program ctx body fuel' state =
                  .ok bodyOutcome :=
              Block.runScoped_mono prim program hLe hBody
            simp [hBody, hBody'] at hRun ⊢
            exact hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hCond : Expr.evalCondition prim cond state with
                | error err =>
                    simp [hCond] at hRun ⊢
                | ok condResult =>
                    rcases condResult with ⟨stateAfterCond, condTrue⟩
                    cases condTrue with
                    | false =>
                        simp [hCond] at hRun ⊢
                        exact hRun
                    | true =>
                        simp [hCond] at hRun ⊢
                        cases hBody :
                            Block.runScoped prim program ctx body fuel
                              stateAfterCond with
                        | error err =>
                            simp [hBody] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped prim program ctx body fuel'
                                  stateAfterCond = .ok bodyOutcome :=
                              Block.runScoped_mono prim program hFuelLe hBody
                            simp [hBody, hBody'] at hRun ⊢
                            exact hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hScrutinee : Expr.evalOne prim scrutinee state with
                | error err =>
                    simp [hScrutinee] at hRun ⊢
                | ok scrutineeResult =>
                    rcases scrutineeResult with ⟨stateAfterScrutinee, value⟩
                    cases hSelected :
                        Switch.select value cases defaultBody with
                    | none =>
                        simp [hScrutinee, hSelected] at hRun ⊢
                        exact hRun
                    | some selected =>
                        simp [hScrutinee, hSelected] at hRun ⊢
                        cases hBody :
                            Block.runScoped prim program ctx selected fuel
                              stateAfterScrutinee with
                        | error err =>
                            simpa [hBody] using hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.runScoped prim program ctx selected
                                    fuel' stateAfterScrutinee =
                                  .ok bodyOutcome :=
                              Block.runScoped_mono prim program hFuelLe hBody
                            simpa [hBody, hBody'] using hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                let initBase := ctx.withoutLoopControl
                cases hInit :
                    Block.runOpen prim program initBase fuel init state with
                | error err =>
                    simp [initBase, hInit] at hRun
                | ok initResult =>
                    rcases initResult with ⟨initOutcome, initCtx⟩
                    have hInit' :
                        Block.runOpen prim program initBase fuel' init state =
                          .ok (initOutcome, initCtx) :=
                      Block.runOpen_mono prim program hFuelLe hInit
                    cases hInitMode : initOutcome.mode with
                    | regular =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        let loopCtx := initCtx
                        let postBase := initCtx.withoutLoopControl
                        let bodyBase :=
                          initCtx.withLoopControl initCtx.scope initCtx.scope
                        cases hLoop :
                            Stmt.runForLoop prim program loopCtx cond postBase
                              post bodyBase body fuel initOutcome.state with
                        | error err =>
                            simp [loopCtx, postBase, bodyBase, hLoop] at hRun
                        | ok loopOutcome =>
                            have hLoop' :
                                Stmt.runForLoop prim program loopCtx cond
                                  postBase post bodyBase body fuel'
                                  initOutcome.state =
                                  .ok loopOutcome :=
                              Stmt.runForLoop_mono prim program hFuelLe hLoop
                            cases hLoopMode : loopOutcome.mode with
                            | regular =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode] at hRun ⊢
                                exact hRun
                            | brk =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode, invalid,
                                  Structured.invalid] at hRun
                            | cont =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode, invalid,
                                  Structured.invalid] at hRun
                            | leave =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode] at hRun ⊢
                                exact hRun
                            | halt kind =>
                                simp [loopCtx, postBase, bodyBase, hLoop,
                                  hLoop', hLoopMode] at hRun ⊢
                                exact hRun
                    | brk =>
                        simp [initBase, hInit, hInit', hInitMode, invalid,
                          Structured.invalid] at hRun
                    | cont =>
                        simp [initBase, hInit, hInit', hInitMode, invalid,
                          Structured.invalid] at hRun
                    | leave =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [initBase, hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
    | brk =>
        simpa [Stmt.run] using hRun
    | cont =>
        simpa [Stmt.run] using hRun
    | leave =>
        simpa [Stmt.run] using hRun
    | call targets functionName args =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                by_cases hTargets : targets.Nodup
                · simp [hTargets] at hRun ⊢
                  cases hArgs : ArgList.eval prim args state with
                  | error err =>
                      simp [hArgs] at hRun ⊢
                  | ok argResult =>
                      rcases argResult with ⟨stateAfterArgs, argValues⟩
                      cases hLookup :
                          FunList.find? functionName program.functions with
                      | none =>
                          simp [hArgs, hLookup, invalid, Structured.invalid]
                            at hRun
                      | some fn =>
                          cases hBody :
                              FunDef.runBody prim program fn argValues fuel
                                stateAfterArgs.shared with
                          | error err =>
                              simp [hArgs, hLookup, hBody] at hRun
                          | ok callResult =>
                              have hBody' :
                                  FunDef.runBody prim program fn argValues
                                      fuel' stateAfterArgs.shared =
                                    .ok callResult :=
                                FunDef.runBody_mono prim program hFuelLe hBody
                              cases callResult with
                              | returned sharedAfterCall returnValues =>
                                  simp [hArgs, hLookup, hBody, hBody'] at hRun ⊢
                                  exact hRun
                              | halted kind haltedState =>
                                  simp [hArgs, hLookup, hBody, hBody'] at hRun ⊢
                                  exact hRun
                · simp [hTargets, invalid, Structured.invalid] at hRun
    | terminal kind =>
        simpa [Stmt.run] using hRun
    | terminalArgs kind args =>
        simpa [Stmt.run] using hRun
  termination_by
    fuel _fuel' _ctx stmt _state _outcome _runCtx _hLe _hRun =>
      (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Block

theorem runOpen_nil_ok {prim : PrimitiveSemantics} {program : Program}
    {ctx : Ctx} {fuel : Nat} {state : State} {outcome : Outcome}
    {runCtx : Ctx}
    (hRun : Block.runOpen prim program ctx fuel { stmts := [] } state =
      .ok (outcome, runCtx)) :
    outcome = Outcome.regular state ∧ runCtx = ctx := by
  cases fuel with
  | zero =>
      simp [Block.runOpen, invalid, Structured.invalid] at hRun
  | succ fuel =>
      have hPair :
          (Outcome.regular state, ctx) = (outcome, runCtx) := by
        simpa [Block.runOpen] using hRun
      injection hPair with hOutcome hCtx
      exact ⟨hOutcome.symm, hCtx.symm⟩

theorem runOpen_append_regular_exists
    (prim : PrimitiveSemantics) (program : Program) :
    ∀ (left right : List Stmt) (ctx midCtx : Ctx)
      (state mid : State) (outcome : Outcome) (runCtx : Ctx),
      (∃ fuel, Block.runOpen prim program ctx fuel { stmts := left } state =
        .ok (Outcome.regular mid, midCtx)) →
      (∃ fuel, Block.runOpen prim program midCtx fuel { stmts := right } mid =
        .ok (outcome, runCtx)) →
      ∃ fuel, Block.runOpen prim program ctx fuel { stmts := left ++ right }
        state = .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx midCtx state mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpen_nil_ok hLeft with ⟨hOutcome, hCtx⟩
      cases hOutcome
      cases hCtx
      simpa using hRight
  | cons stmt rest ih =>
      intro right ctx midCtx state mid outcome runCtx hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpen, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt : Stmt.run prim program ctx fuelLeft stmt state with
          | error err =>
              simp [Block.runOpen, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
              cases hMode : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpen, hStmt, hMode] at hLeft
                  have hRest :
                      ∃ fuel,
                        Block.runOpen prim program stmtCtx fuel
                          { stmts := rest } stmtOutcome.state =
                          .ok (Outcome.regular mid, midCtx) :=
                    ⟨fuelLeft, hLeft⟩
                  rcases ih right stmtCtx midCtx stmtOutcome.state mid outcome
                      runCtx hRest hRight with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run prim program ctx (Nat.max fuelLeft fuelRest)
                          stmt state =
                        .ok (stmtOutcome, stmtCtx) :=
                    Stmt.run_mono prim program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.runOpen prim program stmtCtx
                          (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok (outcome, runCtx) :=
                    Block.runOpen_mono prim program (Nat.le_max_right _ _)
                      hRestAppend
                  simp [fuel, Block.runOpen, hStmt', hMode, hRestAppend']
              | brk =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Outcome.regular, Locals.Source.Outcome.regular]
                    at hMode
              | cont =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Outcome.regular, Locals.Source.Outcome.regular]
                    at hMode
              | leave =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Outcome.regular, Locals.Source.Outcome.regular]
                    at hMode
              | halt kind =>
                  have hPair :
                      (stmtOutcome, ctx) =
                        (Outcome.regular mid, midCtx) := by
                    simpa [Block.runOpen, hStmt, hMode] using hLeft
                  injection hPair with hOutcome _hCtx
                  rw [hOutcome] at hMode
                  simp [Outcome.regular, Locals.Source.Outcome.regular]
                    at hMode

theorem runOpen_append_nonregular_exists
    (prim : PrimitiveSemantics) (program : Program) :
    ∀ (left right : List Stmt) (ctx : Ctx) (state : State)
      (outcome : Outcome) (runCtx : Ctx),
      (∃ fuel, Block.runOpen prim program ctx fuel { stmts := left } state =
        .ok (outcome, runCtx)) →
      outcome.mode ≠ .regular →
      ∃ fuel, Block.runOpen prim program ctx fuel { stmts := left ++ right }
        state = .ok (outcome, runCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx state outcome runCtx hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      rcases runOpen_nil_ok hLeft with ⟨hOutcome, _hCtx⟩
      cases hOutcome
      simp [Outcome.regular, Locals.Source.Outcome.regular] at hMode
  | cons stmt rest ih =>
      intro right ctx state outcome runCtx hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.runOpen, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt : Stmt.run prim program ctx fuelLeft stmt state with
          | error err =>
              simp [Block.runOpen, hStmt] at hLeft
          | ok stmtResult =>
              rcases stmtResult with ⟨stmtOutcome, stmtCtx⟩
              cases hModeStmt : stmtOutcome.mode with
              | regular =>
                  simp [Block.runOpen, hStmt, hModeStmt] at hLeft
                  rcases ih right stmtCtx stmtOutcome.state outcome runCtx
                      ⟨fuelLeft, hLeft⟩ hMode with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run prim program ctx
                          (Nat.max fuelLeft fuelRest) stmt state =
                        .ok (stmtOutcome, stmtCtx) :=
                    Stmt.run_mono prim program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.runOpen prim program stmtCtx
                          (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok (outcome, runCtx) :=
                    Block.runOpen_mono prim program (Nat.le_max_right _ _)
                      hRestAppend
                  simp [fuel, Block.runOpen, hStmt', hModeStmt, hRestAppend']
              | brk =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1, by
                    rw [← hOutcome, ← hCtx]
                    simp [Block.runOpen, hStmt, hModeStmt]⟩
              | cont =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1, by
                    rw [← hOutcome, ← hCtx]
                    simp [Block.runOpen, hStmt, hModeStmt]⟩
              | leave =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1, by
                    rw [← hOutcome, ← hCtx]
                    simp [Block.runOpen, hStmt, hModeStmt]⟩
              | halt kind =>
                  have hPair :
                      (stmtOutcome, ctx) = (outcome, runCtx) := by
                    simpa [Block.runOpen, hStmt, hModeStmt] using hLeft
                  injection hPair with hOutcome hCtx
                  exact ⟨fuelLeft + 1, by
                    rw [← hOutcome, ← hCtx]
                    simp [Block.runOpen, hStmt, hModeStmt]⟩

theorem runScoped_regular_eq_restrict {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {block : Block} {fuel : Nat}
    {state out : State}
    (hRun :
      Block.runScoped prim program ctx block fuel state =
        .ok (Outcome.regular out)) :
    ∃ inner finalCtx,
      Block.runOpen prim program ctx fuel block state =
        .ok (Outcome.regular inner, finalCtx) ∧
        out = inner.restrictTo ctx.scope := by
  unfold Block.runScoped at hRun
  cases hOpen : Block.runOpen prim program ctx fuel block state with
  | error err =>
      simp [hOpen] at hRun
  | ok result =>
      rcases result with ⟨outcome, finalCtx⟩
      cases outcome with
      | mk outcomeState mode =>
          cases mode
          · simp [hOpen, Outcome.regular, Locals.Source.Outcome.regular] at hRun
            cases hRun
            refine ⟨outcomeState, finalCtx, ?_, rfl⟩
            simpa [Outcome.regular, Locals.Source.Outcome.regular] using hOpen
          · simp [hOpen, Outcome.regular, Locals.Source.Outcome.regular,
              Outcome.brk, Locals.Source.Outcome.brk] at hRun
          · simp [hOpen, Outcome.regular, Locals.Source.Outcome.regular,
              Outcome.cont, Locals.Source.Outcome.cont] at hRun
          · simp [hOpen, Outcome.regular, Locals.Source.Outcome.regular,
              Outcome.leave, Locals.Source.Outcome.leave] at hRun
          · simp [hOpen, Outcome.regular, Locals.Source.Outcome.regular,
              Outcome.halt, Locals.Source.Outcome.halt] at hRun

theorem runScoped_regular_drops_not_mem {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {block : Block} {fuel : Nat}
    {state out : State} {name : Name}
    (hRun :
      Block.runScoped prim program ctx block fuel state =
        .ok (Outcome.regular out))
    (hNotMem : name ∉ ctx.scope) :
    out.vars name = none := by
  rcases runScoped_regular_eq_restrict hRun with
    ⟨inner, _finalCtx, _hOpen, hOut⟩
  rw [hOut]
  exact Locals.Source.Store.restrictTo_not_mem hNotMem

end Block

namespace FunDef

def bodyCtx (fn : FunDef) : Ctx :=
  let functionScope := fn.returns ++ fn.params
  { Ctx.initial.withLeaveScope functionScope with
    scope := functionScope }

theorem runBody_returned_parts {prim : PrimitiveSemantics}
    {program : Program} {fn : FunDef} {args : List Word}
    {fuel : Nat} {shared shared' : EvmYul.SharedState .EVM}
    {returnValues : List Word}
    (hRun :
      FunDef.runBody prim program fn args (fuel + 1) shared =
        .ok (CallResult.returned shared' returnValues)) :
    ∃ paramStore bodyOutcome bodyCtx',
      Store.insertMany fn.params args Locals.Source.Store.empty =
        some paramStore ∧
      Block.runOpen prim program (bodyCtx fn) fuel fn.body
          { shared := shared,
            vars := Store.initReturns fn.returns paramStore } =
        .ok (bodyOutcome, bodyCtx') ∧
      (bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave) ∧
      Store.lookupMany fn.returns bodyOutcome.state.vars =
        some returnValues ∧
      bodyOutcome.state.shared = shared' := by
  unfold FunDef.runBody at hRun
  cases hParams :
      Store.insertMany fn.params args Locals.Source.Store.empty with
  | none =>
      simp [hParams, invalid, Structured.invalid] at hRun
  | some paramStore =>
      simp [hParams] at hRun
      cases hBody :
          Block.runOpen prim program
            { Source.Ctx.withLeaveScope Source.Ctx.initial
                (fn.returns ++ fn.params) with
              scope := fn.returns ++ fn.params }
            fuel fn.body
            { shared := shared,
              vars := Store.initReturns fn.returns paramStore } with
      | error err =>
          simp [hBody] at hRun
      | ok bodyResult =>
          rcases bodyResult with ⟨bodyOutcome, bodyCtx'⟩
          simp [hBody] at hRun
          cases hMode : bodyOutcome.mode with
          | regular =>
              simp [hMode] at hRun
              cases hLookup :
                  Store.lookupMany fn.returns bodyOutcome.state.vars with
              | none =>
                  simp [hLookup, invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
                  rcases hRun with ⟨hShared, hValues⟩
                  subst values
                  exact
                    ⟨paramStore, bodyOutcome, bodyCtx', rfl,
                      by simpa [bodyCtx] using hBody,
                      Or.inl hMode, hLookup, hShared⟩
          | leave =>
              simp [hMode] at hRun
              cases hLookup :
                  Store.lookupMany fn.returns bodyOutcome.state.vars with
              | none =>
                  simp [hLookup, invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
                  rcases hRun with ⟨hShared, hValues⟩
                  subst values
                  exact
                    ⟨paramStore, bodyOutcome, bodyCtx', rfl,
                      by simpa [bodyCtx] using hBody,
                      Or.inr hMode, hLookup, hShared⟩
          | brk =>
              simp [hMode, invalid, Structured.invalid] at hRun
          | cont =>
              simp [hMode, invalid, Structured.invalid] at hRun
          | halt kind =>
              simp [hMode] at hRun

theorem runBody_halted_parts {prim : PrimitiveSemantics}
    {program : Program} {fn : FunDef} {args : List Word}
    {fuel : Nat} {shared : EvmYul.SharedState .EVM}
    {kind : Assembly.HaltKind} {haltedState : State}
    (hRun :
      FunDef.runBody prim program fn args (fuel + 1) shared =
        .ok (CallResult.halted kind haltedState)) :
    ∃ paramStore bodyCtx',
      Store.insertMany fn.params args Locals.Source.Store.empty =
        some paramStore ∧
      Block.runOpen prim program (bodyCtx fn) fuel fn.body
          { shared := shared,
            vars := Store.initReturns fn.returns paramStore } =
        .ok (Outcome.halt kind haltedState, bodyCtx') := by
  unfold FunDef.runBody at hRun
  cases hParams :
      Store.insertMany fn.params args Locals.Source.Store.empty with
  | none =>
      simp [hParams, invalid, Structured.invalid] at hRun
  | some paramStore =>
      simp [hParams] at hRun
      cases hBody :
          Block.runOpen prim program
            { Source.Ctx.withLeaveScope Source.Ctx.initial
                (fn.returns ++ fn.params) with
              scope := fn.returns ++ fn.params }
            fuel fn.body
            { shared := shared,
              vars := Store.initReturns fn.returns paramStore } with
      | error err =>
          simp [hBody] at hRun
      | ok bodyResult =>
          rcases bodyResult with ⟨bodyOutcome, bodyCtx'⟩
          simp [hBody] at hRun
          cases hMode : bodyOutcome.mode with
          | regular =>
              simp [hMode] at hRun
              cases hLookup :
                  Store.lookupMany fn.returns bodyOutcome.state.vars with
              | none =>
                  simp [hLookup, invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
          | leave =>
              simp [hMode] at hRun
              cases hLookup :
                  Store.lookupMany fn.returns bodyOutcome.state.vars with
              | none =>
                  simp [hLookup, invalid, Structured.invalid] at hRun
              | some values =>
                  simp [hLookup] at hRun
          | brk =>
              simp [hMode, invalid, Structured.invalid] at hRun
          | cont =>
              simp [hMode, invalid, Structured.invalid] at hRun
          | halt actualKind =>
              rcases bodyOutcome with ⟨bodyState, bodyMode⟩
              simp at hMode
              subst bodyMode
              simp at hRun
              rcases hRun with ⟨hKind, hState⟩
              subst actualKind
              subst haltedState
              exact ⟨paramStore, bodyCtx', rfl,
                by simpa [bodyCtx, Outcome.halt] using hBody⟩

theorem runBody_args_length {prim : PrimitiveSemantics}
    {program : Program} {fn : FunDef} {args : List Word}
    {fuel : Nat} {shared : EvmYul.SharedState .EVM}
    {result : CallResult}
    (hRun :
      FunDef.runBody prim program fn args fuel shared = .ok result) :
    args.length = fn.params.length := by
  cases fuel with
  | zero =>
      simp [FunDef.runBody, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold FunDef.runBody at hRun
      cases hParams :
          Store.insertMany fn.params args Locals.Source.Store.empty with
      | none =>
          simp [hParams, invalid, Structured.invalid] at hRun
      | some paramStore =>
          exact Store.insertMany_length hParams

theorem runBody_returned_length {prim : PrimitiveSemantics}
    {program : Program} {fn : FunDef} {args : List Word}
    {fuel : Nat} {shared shared' : EvmYul.SharedState .EVM}
    {values : List Word}
    (hRun :
      FunDef.runBody prim program fn args fuel shared =
        .ok (CallResult.returned shared' values)) :
    values.length = fn.returns.length := by
  cases fuel with
  | zero =>
      simp [FunDef.runBody, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold FunDef.runBody at hRun
      cases hParams :
          Store.insertMany fn.params args Locals.Source.Store.empty with
      | none =>
          simp [hParams, invalid, Structured.invalid] at hRun
      | some paramStore =>
          simp [hParams] at hRun
          cases hBody :
              Block.runOpen prim program
                { Source.Ctx.withLeaveScope Source.Ctx.initial
                    (fn.returns ++ fn.params) with
                  scope := fn.returns ++ fn.params }
                fuel fn.body
                { shared := shared,
                  vars := Store.initReturns fn.returns paramStore } with
          | error err =>
              simp [hBody] at hRun
          | ok bodyResult =>
              rcases bodyResult with ⟨bodyOutcome, bodyCtx⟩
              simp [hBody] at hRun
              cases hMode : bodyOutcome.mode with
              | regular =>
                  simp [hMode] at hRun
                  cases hLookup :
                      Store.lookupMany fn.returns bodyOutcome.state.vars with
                  | none =>
                      simp [hLookup, invalid, Structured.invalid] at hRun
                  | some returnValues =>
                      simp [hLookup] at hRun
                      rcases hRun with ⟨_hSharedEq, hValuesEq⟩
                      rw [← hValuesEq]
                      exact Store.lookupMany_length hLookup
              | leave =>
                  simp [hMode] at hRun
                  cases hLookup :
                      Store.lookupMany fn.returns bodyOutcome.state.vars with
                  | none =>
                      simp [hLookup, invalid, Structured.invalid] at hRun
                  | some returnValues =>
                      simp [hLookup] at hRun
                      rcases hRun with ⟨_hSharedEq, hValuesEq⟩
                      rw [← hValuesEq]
                      exact Store.lookupMany_length hLookup
              | brk =>
                  simp [hMode, invalid, Structured.invalid] at hRun
              | cont =>
                  simp [hMode, invalid, Structured.invalid] at hRun
              | halt kind =>
                  simp [hMode] at hRun

end FunDef

namespace Stmt

theorem call_regular_parts {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source sourceAfter : State}
    (hRun :
      Stmt.run prim program ctx (fuel + 1)
          (.call targets functionName args) source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    ∃ stateAfterArgs argValues fn sharedAfterCall returnValues returnStore,
      targets.Nodup ∧
        ArgList.eval prim args source = .ok (stateAfterArgs, argValues) ∧
        FunList.find? functionName program.functions = some fn ∧
        FunDef.runBody prim program fn argValues fuel
            stateAfterArgs.shared =
          .ok (CallResult.returned sharedAfterCall returnValues) ∧
        Store.assignMany targets returnValues stateAfterArgs.vars =
          some returnStore ∧
        sourceAfter = { shared := sharedAfterCall, vars := returnStore } := by
  unfold Stmt.run at hRun
  by_cases hTargets : targets.Nodup
  · simp [hTargets] at hRun
    cases hArgs : ArgList.eval prim args source with
    | error err =>
        simp [hArgs] at hRun
    | ok argResult =>
        rcases argResult with ⟨stateAfterArgs, argValues⟩
        simp [hArgs] at hRun
        cases hFind :
            FunList.find? functionName program.functions with
        | none =>
            simp [hFind, invalid, Structured.invalid] at hRun
        | some fn =>
            simp [hFind] at hRun
            cases hBody :
                FunDef.runBody prim program fn argValues fuel
                  stateAfterArgs.shared with
            | error err =>
                simp [hBody] at hRun
            | ok callResult =>
                cases callResult with
                | returned sharedAfterCall returnValues =>
                    simp [hBody] at hRun
                    cases hAssign :
                        Store.assignMany targets returnValues
                          stateAfterArgs.vars with
                    | none =>
                        simp [hAssign, invalid, Structured.invalid] at hRun
                    | some returnStore =>
                        simp [hAssign] at hRun
                        cases hRun
                        exact
                          ⟨stateAfterArgs, argValues, fn, sharedAfterCall,
                            returnValues, returnStore, hTargets,
                            by simpa [hArgs],
                            by simpa [hFind],
                            by simpa [hBody],
                            by simpa [hAssign],
                            rfl⟩
                | halted kind haltedState =>
                    simp [hBody, Outcome.regular, Outcome.halt] at hRun
                    cases hRun
  · simp [hTargets, invalid, Structured.invalid] at hRun

theorem call_halted_parts {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source haltedState : State} {kind : Assembly.HaltKind}
    (hRun :
      Stmt.run prim program ctx (fuel + 1)
          (.call targets functionName args) source =
        .ok (Outcome.halt kind haltedState, ctx)) :
    ∃ stateAfterArgs argValues fn,
      targets.Nodup ∧
        ArgList.eval prim args source = .ok (stateAfterArgs, argValues) ∧
        FunList.find? functionName program.functions = some fn ∧
        FunDef.runBody prim program fn argValues fuel
            stateAfterArgs.shared =
          .ok (CallResult.halted kind haltedState) := by
  unfold Stmt.run at hRun
  by_cases hTargets : targets.Nodup
  · simp [hTargets] at hRun
    cases hArgs : ArgList.eval prim args source with
    | error err =>
        simp [hArgs] at hRun
    | ok argResult =>
        rcases argResult with ⟨stateAfterArgs, argValues⟩
        simp [hArgs] at hRun
        cases hFind :
            FunList.find? functionName program.functions with
        | none =>
            simp [hFind, invalid, Structured.invalid] at hRun
        | some fn =>
            simp [hFind] at hRun
            cases hBody :
                FunDef.runBody prim program fn argValues fuel
                  stateAfterArgs.shared with
            | error err =>
                simp [hBody] at hRun
            | ok callResult =>
                cases callResult with
                | returned sharedAfterCall returnValues =>
                    simp [hBody] at hRun
                    cases hAssign :
                        Store.assignMany targets returnValues
                          stateAfterArgs.vars with
                    | none =>
                        simp [hAssign, invalid, Structured.invalid] at hRun
                    | some returnStore =>
                        simp [hAssign, Outcome.regular, Outcome.halt] at hRun
                        cases hRun
                | halted actualKind actualState =>
                    simp [hBody, Outcome.halt] at hRun
                    cases hRun
                    exact
                      ⟨stateAfterArgs, argValues, fn, hTargets,
                        by simpa [hArgs],
                        by simpa [hFind],
                        by simpa [hBody]⟩
  · simp [hTargets, invalid, Structured.invalid] at hRun

theorem call_ok_parts {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source : State} {outcome : Outcome}
    (hRun :
      Stmt.run prim program ctx (fuel + 1)
          (.call targets functionName args) source =
        .ok (outcome, ctx)) :
    ∃ stateAfterArgs argValues fn callResult,
      targets.Nodup ∧
        ArgList.eval prim args source = .ok (stateAfterArgs, argValues) ∧
        FunList.find? functionName program.functions = some fn ∧
        FunDef.runBody prim program fn argValues fuel
            stateAfterArgs.shared =
          .ok callResult ∧
        ((∃ sharedAfterCall returnValues returnStore,
          callResult = CallResult.returned sharedAfterCall returnValues ∧
            Store.assignMany targets returnValues stateAfterArgs.vars =
              some returnStore ∧
            outcome =
              Outcome.regular
                { shared := sharedAfterCall, vars := returnStore }) ∨
          ∃ kind haltedState,
            callResult = CallResult.halted kind haltedState ∧
              outcome = Outcome.halt kind haltedState) := by
  unfold Stmt.run at hRun
  by_cases hTargets : targets.Nodup
  · simp [hTargets] at hRun
    cases hArgs : ArgList.eval prim args source with
    | error err =>
        simp [hArgs] at hRun
    | ok argResult =>
        rcases argResult with ⟨stateAfterArgs, argValues⟩
        simp [hArgs] at hRun
        cases hFind :
            FunList.find? functionName program.functions with
        | none =>
            simp [hFind, invalid, Structured.invalid] at hRun
        | some fn =>
            simp [hFind] at hRun
            cases hBody :
                FunDef.runBody prim program fn argValues fuel
                  stateAfterArgs.shared with
            | error err =>
                simp [hBody] at hRun
            | ok callResult =>
                cases callResult with
                | returned sharedAfterCall returnValues =>
                    simp [hBody] at hRun
                    cases hAssign :
                        Store.assignMany targets returnValues
                          stateAfterArgs.vars with
                    | none =>
                        simp [hAssign, invalid, Structured.invalid] at hRun
                    | some returnStore =>
                        simp [hAssign] at hRun
                        cases hRun
                        exact
                          ⟨stateAfterArgs, argValues, fn,
                            CallResult.returned sharedAfterCall returnValues,
                            hTargets, by simpa [hArgs],
                            by simpa [hFind], by simpa [hBody],
                            Or.inl
                              ⟨sharedAfterCall, returnValues, returnStore,
                                rfl, by simpa [hAssign], rfl⟩⟩
                | halted kind haltedState =>
                    simp [hBody] at hRun
                    cases hRun
                    exact
                      ⟨stateAfterArgs, argValues, fn,
                        CallResult.halted kind haltedState, hTargets,
                        by simpa [hArgs], by simpa [hFind],
                        by simpa [hBody],
                        Or.inr ⟨kind, haltedState, rfl, rfl⟩⟩
  · simp [hTargets, invalid, Structured.invalid] at hRun

theorem call_regular_targets_nodup {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source sourceAfter : State}
    (hRun :
      Stmt.run prim program ctx fuel (.call targets functionName args)
          source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    targets.Nodup := by
  cases fuel with
  | zero =>
      simp [Stmt.run, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold Stmt.run at hRun
      by_contra hTargets
      simp [hTargets, invalid, Structured.invalid] at hRun

theorem call_halt_targets_nodup {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source haltedState : State} {kind : Assembly.HaltKind}
    (hRun :
      Stmt.run prim program ctx fuel (.call targets functionName args)
          source =
        .ok (Outcome.halt kind haltedState, ctx)) :
    targets.Nodup := by
  cases fuel with
  | zero =>
      simp [Stmt.run, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold Stmt.run at hRun
      by_contra hTargets
      simp [hTargets, invalid, Structured.invalid] at hRun

theorem call_regular_args_length {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source sourceAfter : State} {fn : FunDef}
    (hLookup : FunList.find? functionName program.functions = some fn)
    (hRun :
      Stmt.run prim program ctx fuel (.call targets functionName args)
          source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    args.length = fn.params.length := by
  cases fuel with
  | zero =>
      simp [Stmt.run, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold Stmt.run at hRun
      have hTargets : targets.Nodup := by
        by_contra hTargets
        simp [hTargets, invalid, Structured.invalid] at hRun
      simp [hTargets] at hRun
      cases hArgs : ArgList.eval prim args source with
      | error err =>
          simp [hArgs] at hRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, argValues⟩
          simp [hArgs, hLookup] at hRun
          cases hBody :
              FunDef.runBody prim program fn argValues fuel
                stateAfterArgs.shared with
          | error err =>
              simp [hBody] at hRun
          | ok callResult =>
              have hArgLen : argValues.length = args.length :=
                ArgList.eval_length prim hArgs
              have hParamLen : argValues.length = fn.params.length :=
                FunDef.runBody_args_length hBody
              omega

theorem call_regular_targets_length {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source sourceAfter : State} {fn : FunDef}
    (hLookup : FunList.find? functionName program.functions = some fn)
    (hRun :
      Stmt.run prim program ctx fuel (.call targets functionName args)
          source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    targets.length = fn.returns.length := by
  cases fuel with
  | zero =>
      simp [Stmt.run, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold Stmt.run at hRun
      have hTargets : targets.Nodup := by
        by_contra hTargets
        simp [hTargets, invalid, Structured.invalid] at hRun
      simp [hTargets] at hRun
      cases hArgs : ArgList.eval prim args source with
      | error err =>
          simp [hArgs] at hRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, argValues⟩
          simp [hArgs, hLookup] at hRun
          cases hBody :
              FunDef.runBody prim program fn argValues fuel
                stateAfterArgs.shared with
          | error err =>
              simp [hBody] at hRun
          | ok callResult =>
              cases callResult with
              | returned sharedAfterCall returnValues =>
                  simp [hBody] at hRun
                  cases hAssign :
                      Store.assignMany targets returnValues
                        stateAfterArgs.vars with
                  | none =>
                      simp [hAssign, invalid, Structured.invalid] at hRun
                  | some returnStore =>
                      have hAssignLen :
                          returnValues.length = targets.length :=
                        Store.assignMany_length hAssign
                      have hReturnLen :
                          returnValues.length = fn.returns.length :=
                        FunDef.runBody_returned_length hBody
                      omega
              | halted kind haltedState =>
                  simp [hBody, Outcome.regular, Outcome.halt] at hRun
                  cases hRun

theorem call_regular_arities {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source sourceAfter : State} {fn : FunDef}
    (hLookup : FunList.find? functionName program.functions = some fn)
    (hRun :
      Stmt.run prim program ctx fuel (.call targets functionName args)
          source =
        .ok (Outcome.regular sourceAfter, ctx)) :
    args.length = fn.params.length ∧
      targets.length = fn.returns.length := by
  exact
    ⟨call_regular_args_length hLookup hRun,
      call_regular_targets_length hLookup hRun⟩

theorem call_halt_args_length {prim : PrimitiveSemantics}
    {program : Program} {ctx : Ctx} {fuel : Nat}
    {targets : List Name} {functionName : Name} {args : List (Expr 1)}
    {source haltedState : State} {fn : FunDef} {kind : Assembly.HaltKind}
    (hLookup : FunList.find? functionName program.functions = some fn)
    (hRun :
      Stmt.run prim program ctx fuel (.call targets functionName args)
          source =
        .ok (Outcome.halt kind haltedState, ctx)) :
    args.length = fn.params.length := by
  cases fuel with
  | zero =>
      simp [Stmt.run, invalid, Structured.invalid] at hRun
  | succ fuel =>
      unfold Stmt.run at hRun
      have hTargets : targets.Nodup := by
        by_contra hTargets
        simp [hTargets, invalid, Structured.invalid] at hRun
      simp [hTargets] at hRun
      cases hArgs : ArgList.eval prim args source with
      | error err =>
          simp [hArgs] at hRun
      | ok argResult =>
          rcases argResult with ⟨stateAfterArgs, argValues⟩
          simp [hArgs, hLookup] at hRun
          cases hBody :
              FunDef.runBody prim program fn argValues fuel
                stateAfterArgs.shared with
          | error err =>
              simp [hBody] at hRun
          | ok callResult =>
              have hArgLen : argValues.length = args.length :=
                ArgList.eval_length prim hArgs
              have hParamLen : argValues.length = fn.params.length :=
                FunDef.runBody_args_length hBody
              omega

end Stmt

namespace Program

def initialState (shared : EvmYul.SharedState .EVM) : State :=
  { shared := shared, vars := Locals.Source.Store.empty }

def runState (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : State) : Except EVMException Outcome :=
  Block.runScoped prim program Ctx.initial program.body fuel state

def run (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : EVMState) : Except EVMException Outcome :=
  runState prim fuel program (initialState state.toSharedState)

inductive Eval (prim : PrimitiveSemantics) :
    Nat → Program → State → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : State}
      {outcome : Outcome}
      (hRun : runState prim fuel program initial = .ok outcome) :
      Eval prim fuel program initial outcome

theorem eval_of_run {prim : PrimitiveSemantics} {fuel : Nat}
    {program : Program} {initial : State} {outcome : Outcome}
    (hRun : runState prim fuel program initial = .ok outcome) :
    Eval prim fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

end Source

end Functions
end EvmCompiler
