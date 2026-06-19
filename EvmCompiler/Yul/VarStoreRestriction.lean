import EvmCompiler.Functions.SourceSemantics
import EvmYul.Yul.StateOps

namespace EvmCompiler
namespace Yul
namespace VarStoreRestriction

abbrev Name := EvmYul.Identifier

private theorem lookup_fold_erase_preserve_of_notMem
    (key : Name) :
    ∀ (entries : List (Sigma (fun _ : Name => Assembly.Word)))
      (store : EvmYul.Yul.VarStore),
      key ∉ entries.keys →
        (List.foldl
            (fun (store : EvmYul.Yul.VarStore)
                (entry : Sigma (fun _ : Name => Assembly.Word)) =>
              Finmap.erase entry.1 store)
            store entries).lookup key = store.lookup key
  | [], _store, _hNotMem => rfl
  | Sigma.mk head _value :: rest, store, hNotMem => by
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
            store entries).lookup key = none
  | [], _store, hNone => hNone
  | Sigma.mk head _value :: rest, store, hNone => by
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
            store entries).lookup key = none
  | [], _store, hMem => by simp at hMem
  | Sigma.mk head _value :: rest, store, hMem => by
      simp only [List.foldl_cons]
      by_cases hEq : key = head
      · subst key
        apply lookup_fold_erase_none_of_initial_none head rest
        simp
      · have hRest : key ∈ rest.keys := by simpa [hEq] using hMem
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
      have hLookup : AList.lookup key alist = some value := by
        simpa using hScope
      have hSome : (AList.lookup key alist).isSome := by simp [hLookup]
      simpa [AList.mem_keys, AList.keys] using AList.lookup_isSome.mp hSome

theorem lookup_restrict_of_some
    (store scope : EvmYul.Yul.VarStore) (key : Name)
    {value : Assembly.Word}
    (hScope : scope.lookup key = some value) :
    (EvmYul.Yul.State.restrictVarStore store scope).lookup key =
      store.lookup key := by
  unfold EvmYul.Yul.State.restrictVarStore
  have hInner : (store.sdiff scope).lookup key = none :=
    lookup_sdiff_of_lookup_some store scope key hScope
  exact lookup_sdiff_of_lookup_none store (store.sdiff scope) key hInner

theorem lookup_restrict_of_none
    (store scope : EvmYul.Yul.VarStore) (key : Name)
    (hScope : scope.lookup key = none) :
    (EvmYul.Yul.State.restrictVarStore store scope).lookup key = none := by
  unfold EvmYul.Yul.State.restrictVarStore
  have hInner : (store.sdiff scope).lookup key = store.lookup key :=
    lookup_sdiff_of_lookup_none store scope key hScope
  cases hStore : store.lookup key with
  | none =>
      simpa [hInner, hStore] using
        lookup_sdiff_of_lookup_none store (store.sdiff scope) key (by
          simpa [hInner, hStore])
  | some value =>
      have hInnerSome : (store.sdiff scope).lookup key = some value := by
        simpa [hStore] using hInner
      simpa using
        lookup_sdiff_of_lookup_some store (store.sdiff scope) key hInnerSome

end VarStoreRestriction
end Yul
end EvmCompiler
