import EvmCompiler.Functions.StackSchedule
import EvmCompiler.Functions.SourceSemantics
import EvmCompiler.Locals.InteractionPreservation

/-!
Dynamic-layout relation for stack-scheduled Functions allocation.

Unlike the lexical Locals relation, this relation permits dead source bindings
to be absent from the target layout.  It owns only the current live stack
prefix and an abstract dormant caller suffix.
-/

namespace EvmCompiler
namespace Functions
namespace StackRelation

abbrev Word := Assembly.Word

def values (source : Locals.Source.State)
    (layout : Locals.Layout) : List Word :=
  layout.map fun name => (source.vars name).getD (EvmYul.UInt256.ofNat 0)

theorem values_eq_of_lookupMany
    {source : Locals.Source.State} {names : Locals.Layout}
    {result : List Word}
    (hLookup : Functions.Source.Store.lookupMany names source.vars =
      some result) :
    values source names = result := by
  have hPairs := Functions.Source.Store.lookupMany_forall₂ hLookup
  clear hLookup
  induction hPairs with
  | nil => rfl
  | cons hValue _hTail ih =>
      unfold values
      simp only [List.map_cons, hValue, Option.getD_some]
      congr

structure StateRel (layout : Locals.Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State) (target : Structured.RunState) : Prop where
  shared : target.evm.toSharedState = source.shared
  returns : target.returns = returns
  stack : target.evm.stack = values source layout ++ suffix
  defined :
    ∀ {name : Name}, name ∈ layout → ∃ value, source.vars name = some value

theorem list_eq_take_cons_drop_of_getElem?_eq_some
    {α : Type} {items : List α} {index : Nat} {value : α}
    (hAt : items[index]? = some value) :
    items = items.take index ++ value :: items.drop (index + 1) := by
  induction items generalizing index with
  | nil => simp at hAt
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hAt
          subst head
          simp
      | succ index =>
          simp only [List.getElem?_cons_succ] at hAt
          have hTail := ih hAt
          change
            head :: tail =
              head ::
                (tail.take index ++ value :: tail.drop (index + 1))
          exact congrArg (List.cons head) hTail

theorem values_getElem?_eq_some
    {source : Locals.Source.State} {layout : Locals.Layout}
    {index : Nat} {name : Name}
    (hAt : layout[index]? = some name) :
    (values source layout)[index]? =
      some ((source.vars name).getD (EvmYul.UInt256.ofNat 0)) := by
  simp [values, List.getElem?_map, hAt]

theorem values_promoteAt
    {source : Locals.Source.State} {layout : Locals.Layout}
    {index : Nat} {name : Name}
    (hAt : layout[index]? = some name) :
    values source (Locals.Layout.promoteAt index layout) =
      (source.vars name).getD (EvmYul.UInt256.ofNat 0) ::
        (values source layout).take index ++
          (values source layout).drop (index + 1) := by
  simp [values, Locals.Layout.promoteAt, hAt, List.map_take,
    List.map_drop]

theorem values_insert_fresh
    {source : Locals.Source.State} {layout : Locals.Layout}
    {name : Name} {value : Word}
    (hFresh : name ∉ layout) :
    values (source.insert name value) (name :: layout) =
      value :: values source layout := by
  unfold values
  simp only [List.map_cons, Locals.Source.State.insert,
    Locals.Source.Store.insert_self, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro candidate hCandidate
  have hNe : candidate ≠ name := by
    intro hEq
    subst candidate
    exact hFresh hCandidate
  simp [Locals.Source.State.insert, Locals.Source.Store.insert, hNe]

theorem values_insert_existing
    {source : Locals.Source.State} {layout : Locals.Layout}
    {name : Name} {depth : Nat} {value : Word}
    (hNodup : layout.Nodup)
    (hAt : layout[depth]? = some name) :
    values (source.insert name value) layout =
      (values source layout).set depth value := by
  induction layout generalizing depth with
  | nil => simp at hAt
  | cons head tail ih =>
      cases depth with
      | zero =>
          simp only [List.getElem?_cons_zero] at hAt
          cases hAt
          have hNotMem : name ∉ tail := List.nodup_cons.mp hNodup |>.1
          unfold values
          simp only [List.map_cons, List.set_cons_zero,
            Locals.Source.State.insert,
            Locals.Source.Store.insert_self, Option.getD_some]
          congr 1
          apply List.map_congr_left
          intro candidate hCandidate
          have hNe : candidate ≠ name := by
            intro hEq
            subst candidate
            exact hNotMem hCandidate
          simp [Locals.Source.Store.insert, hNe]
      | succ depth =>
          simp only [List.getElem?_cons_succ] at hAt
          have hParts := List.nodup_cons.mp hNodup
          have hHeadNe : head ≠ name := by
            intro hEq
            subst head
            exact hParts.1 (List.mem_of_getElem? hAt)
          unfold values
          simp only [List.map_cons, List.set_cons_succ,
            Locals.Source.State.insert]
          rw [show
            Locals.Source.Store.insert source.vars name value head =
              source.vars head by
            simp [Locals.Source.Store.insert, hHeadNe]]
          exact congrArg (List.cons ((source.vars head).getD
            (EvmYul.UInt256.ofNat 0))) (ih hParts.2 hAt)

theorem mem_of_mem_promoteAt
    {layout : Locals.Layout} {index : Nat} {name candidate : Name}
    (hAt : layout[index]? = some name)
    (hMem : candidate ∈ Locals.Layout.promoteAt index layout) :
    candidate ∈ layout := by
  unfold Locals.Layout.promoteAt at hMem
  rw [hAt] at hMem
  rcases List.mem_cons.mp hMem with hName | hRest
  · rw [hName]
    exact List.mem_of_getElem? hAt
  · rcases List.mem_append.mp hRest with hTake | hDrop
    · exact List.mem_of_mem_take hTake
    · exact List.mem_of_mem_drop hDrop

namespace StateRel

theorem of_lookupMany
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    {result : List Word}
    (hShared : target.evm.toSharedState = source.shared)
    (hReturns : target.returns = returns)
    (hLookup :
      Functions.Source.Store.lookupMany layout source.vars = some result)
    (hStack : target.evm.stack = result ++ suffix) :
    StateRel layout suffix returns source target := by
  refine ⟨hShared, hReturns, ?_, ?_⟩
  · rw [values_eq_of_lookupMany hLookup]
    exact hStack
  · intro name hName
    have hContains :=
      Functions.Source.Store.lookupMany_contains_of_mem hLookup hName
    cases hValue : source.vars name with
    | none => simp [Locals.Source.Store.contains, hValue] at hContains
    | some value => exact ⟨value, rfl⟩

theorem lookupMany_of_subset
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hRel : StateRel layout suffix returns source target)
    {names : List Name}
    (hSubset : ∀ name, name ∈ names → name ∈ layout) :
    ∃ result,
      Functions.Source.Store.lookupMany names source.vars = some result := by
  induction names with
  | nil => exact ⟨[], rfl⟩
  | cons name names ih =>
      obtain ⟨value, hValue⟩ := hRel.defined (hSubset name (by simp))
      obtain ⟨result, hResult⟩ :=
        ih (fun other hOther => hSubset other (by simp [hOther]))
      exact
        ⟨value :: result, by
          simp [Functions.Source.Store.lookupMany, hValue, hResult]⟩

theorem restrictTo
    {layout scope : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hRel : StateRel layout suffix returns source target)
    (hScope : ∀ {name : Name}, name ∈ layout → name ∈ scope) :
    StateRel layout suffix returns (source.restrictTo scope) target := by
  have hValues :
      values (source.restrictTo scope) layout = values source layout := by
    unfold values
    apply List.map_congr_left
    intro name hName
    simp only [Locals.Source.State.restrictTo]
    rw [Locals.Source.Store.restrictTo_mem (hScope hName)]
  constructor
  · simpa using hRel.shared
  · exact hRel.returns
  · rw [hRel.stack, hValues]
  · intro name hName
    obtain ⟨value, hValue⟩ := hRel.defined hName
    refine ⟨value, ?_⟩
    simpa [Locals.Source.State.restrictTo] using
      (Locals.Source.Store.restrictTo_mem
        (scope := scope) (store := source.vars) (hScope hName)).trans hValue

theorem expr
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hRel : StateRel layout suffix returns source target) :
    Locals.InteractionPreservation.Expr.StateRel layout 0 source target := by
  constructor
  · exact hRel.shared
  · intro name depth hDepth
    have hAt : layout[depth]? = some name :=
      Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
    obtain ⟨value, hValue⟩ :=
      hRel.defined (List.mem_of_getElem? hAt)
    refine ⟨value, hValue, ?_⟩
    rw [hRel.stack]
    have hValuesAt : (values source layout)[depth]? = some value := by
      simp [values, List.getElem?_map, hAt, hValue]
    have hDepthBound : depth < (values source layout).length :=
      (List.getElem?_eq_some_iff.mp hValuesAt).1
    simp only [Nat.zero_add]
    rw [List.getElem?_append_left hDepthBound]
    simpa using hValuesAt

theorem ofExprResultZero
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {initialSource finalSource : Locals.Source.State}
    {resultValues : List Word}
    {initialTarget finalTarget : Structured.RunState}
    (hInitial :
      StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Locals.InteractionPreservation.Expr.ResultRel 0
        initialSource initialTarget (finalSource, resultValues) finalTarget) :
    StateRel layout suffix returns finalSource finalTarget := by
  have hValues : resultValues = [] := by
    simpa using hResult.length
  subst resultValues
  constructor
  · exact hResult.shared
  · exact hResult.returns.trans hInitial.returns
  · rw [hResult.stack]
    simp only [List.reverse_nil, List.nil_append]
    rw [hInitial.stack]
    unfold values
    rw [hResult.vars]
  · intro name hName
    obtain ⟨value, hValue⟩ := hInitial.defined hName
    refine ⟨value, ?_⟩
    rw [hResult.vars]
    exact hValue

theorem ofExprResultOneInsert
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {initialSource finalSource : Locals.Source.State}
    {value : Word} {initialTarget finalTarget : Structured.RunState}
    {name : Name}
    (hFresh : name ∉ layout)
    (hInitial :
      StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Locals.InteractionPreservation.Expr.ResultRel 1
        initialSource initialTarget (finalSource, [value]) finalTarget) :
    StateRel (name :: layout) suffix returns
      (finalSource.insert name value) finalTarget := by
  constructor
  · exact hResult.shared
  · exact hResult.returns.trans hInitial.returns
  · rw [hResult.stack, hInitial.stack,
      values_insert_fresh hFresh]
    unfold values
    rw [hResult.vars]
    simp [List.append_assoc]
  · intro candidate hCandidate
    rcases List.mem_cons.mp hCandidate with hName | hTail
    · subst candidate
      exact ⟨value, Locals.Source.Store.insert_self _ _ _⟩
    · obtain ⟨oldValue, hOldValue⟩ := hInitial.defined hTail
      have hNe : candidate ≠ name := by
        intro hEq
        subst candidate
        exact hFresh hTail
      refine ⟨oldValue, ?_⟩
      simp [Locals.Source.State.insert,
        Locals.Source.Store.insert, hNe]
      rw [hResult.vars]
      exact hOldValue

/-- A compiler-owned push may expose an already-defined source binding as a
fresh symbolic stack slot without changing the source state. -/
theorem afterPushExisting
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    {name : Name} {value : Word}
    (hFresh : name ∉ layout)
    (hValue : source.vars name = some value)
    (hInitial : StateRel layout suffix returns source target) :
    StateRel (name :: layout) suffix returns source
      (target.withEVM
        (target.evm.replaceStackAndIncrPC
          (value :: target.evm.stack) (pcΔ := 33))) := by
  constructor
  · simpa using hInitial.shared
  · exact hInitial.returns
  · rw [hInitial.stack]
    unfold values
    simp only [List.map_cons, hValue, Option.getD_some]
    simp [Structured.RunState.withEVM,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · intro candidate hCandidate
    rcases List.mem_cons.mp hCandidate with hName | hTail
    · subst candidate
      exact ⟨value, hValue⟩
    · exact hInitial.defined hTail

theorem ofExprResultOnePop
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {initialSource finalSource : Locals.Source.State}
    {value : Word} {initialTarget targetAfterExpr : Structured.RunState}
    (hInitial :
      StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Locals.InteractionPreservation.Expr.ResultRel 1
        initialSource initialTarget (finalSource, [value]) targetAfterExpr) :
    StateRel layout suffix returns finalSource
      (targetAfterExpr.withEVM
        { targetAfterExpr.evm with stack := initialTarget.evm.stack }) := by
  have hValues : values finalSource layout = values initialSource layout := by
    unfold values
    rw [hResult.vars]
  constructor
  · simpa using hResult.shared
  · exact hResult.returns.trans hInitial.returns
  · simpa [hValues] using hInitial.stack
  · intro name hName
    obtain ⟨oldValue, hOldValue⟩ := hInitial.defined hName
    refine ⟨oldValue, ?_⟩
    rw [hResult.vars]
    exact hOldValue

theorem ofExprResultOneAssign
    {layout : Locals.Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {name : Name} {depth : Nat} {value : Word}
    {initialSource finalSource : Locals.Source.State}
    {initialTarget targetAfterValue finalTarget : Structured.RunState}
    (hNodup : layout.Nodup)
    (hDepth :
      Locals.Layout.lookupDepth? name layout = some (depth + 1))
    (hInitial :
      StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Locals.InteractionPreservation.Expr.ResultRel 1
        initialSource initialTarget (finalSource, [value]) targetAfterValue)
    (hFinalShared :
      finalTarget.evm.toSharedState =
        targetAfterValue.evm.toSharedState)
    (hFinalReturns :
      finalTarget.returns = targetAfterValue.returns)
    (hFinalStack :
      finalTarget.evm.stack =
        initialTarget.evm.stack.set depth value) :
    StateRel layout suffix returns
      (finalSource.insert name value) finalTarget := by
  have hAt : layout[depth]? = some name :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hDepthBound : depth < (values initialSource layout).length := by
    unfold values
    simpa using (List.getElem?_eq_some_iff.mp hAt).1
  constructor
  · rw [hFinalShared]
    simpa [Locals.Source.State.insert] using hResult.shared
  · exact hFinalReturns.trans (hResult.returns.trans hInitial.returns)
  · rw [hFinalStack, hInitial.stack,
      List.set_append_left depth value hDepthBound,
      ← values_insert_existing hNodup hAt]
    unfold values
    simp only [Locals.Source.State.insert]
    rw [hResult.vars]
  · intro candidate hCandidate
    by_cases hName : candidate = name
    · subst candidate
      exact ⟨value, Locals.Source.Store.insert_self _ _ _⟩
    · obtain ⟨oldValue, hOldValue⟩ := hInitial.defined hCandidate
      refine ⟨oldValue, ?_⟩
      simp [Locals.Source.State.insert,
        Locals.Source.Store.insert, hName]
      rw [hResult.vars]
      exact hOldValue

end StateRel

end StackRelation
end Functions
end EvmCompiler
