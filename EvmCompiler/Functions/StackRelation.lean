import EvmCompiler.Functions.StackSchedule
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

end StackRelation
end Functions
end EvmCompiler
