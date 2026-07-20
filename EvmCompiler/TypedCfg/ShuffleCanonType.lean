import EvmCompiler.TypedCfg.ShuffleCanon

/-!
# Shuffle-window canonicalisation — the permutation-algebra type-preservation core
(session-75, Route 2 first milestone)

`ShuffleCanon.lean` (§74) banks the transform (`canonSwaps`/`canonBody`/
`canonBlock`/`shuffleCanonProgram`) and its *structural* preservation
(label/entry/`findBlock?`/uniqueness).  Its **type-preservation** was only
empirical ("`wellTyped?`/`lower?` preservation empirically confirmed").

This module banks the reusable *type-preservation core*: the exact
correspondence between the typed `Shape` transition of a `.swap` run and the
`applySwap`/`netStack` permutation algebra of `ShuffleCanon`.  It is the crux
that BOTH the single-block `shuffleCanonProgram` and the Route-2 chain transform
need, and it reduces the whole WellTyped/`lower?` preservation of `canonBlock`
to two clean pure-permutation facts (stated at the end as the documented
frontier):

* **(P1) selection-sort realisability**: `netStack (starDecompose t) t.length = t`;
* **(P2) permutation-action naturality**: two transposition lists with equal
  `netStack` act identically on any list (`applySwaps` depends only on the net
  permutation).

Everything BELOW those two facts — the `type?`/`bodyType?` ⇔ `applySwap`/
`applySwaps` dictionary — is proved green here.  This leaf is imported by nobody
in the certified spine, so it cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleCanon

open EvmCompiler.TypedCfg

/-! ## `applySwaps`: fold `applySwap` over a position list (the shape action) -/

/-- Apply a list of `(0,k)`-transpositions left-to-right to `xs`.  `netStack ps m
= applySwaps ps (List.range m)`. -/
def applySwaps {α : Type _} (ps : List Nat) (xs : List α) : List α :=
  ps.foldl (fun acc k => applySwap k acc) xs

@[simp] theorem applySwaps_nil {α : Type _} (xs : List α) :
    applySwaps [] xs = xs := rfl

@[simp] theorem applySwaps_cons {α : Type _} (k : Nat) (ps : List Nat)
    (xs : List α) :
    applySwaps (k :: ps) xs = applySwaps ps (applySwap k xs) := rfl

theorem applySwaps_append {α : Type _} (ps qs : List Nat) (xs : List α) :
    applySwaps (ps ++ qs) xs = applySwaps qs (applySwaps ps xs) := by
  unfold applySwaps; rw [List.foldl_append]

/-- `netStack` is `applySwaps` on the identity window. -/
theorem netStack_eq_applySwaps (ps : List Nat) (m : Nat) :
    netStack ps m = applySwaps ps (List.range m) := rfl

/-- `applySwap` preserves length (it is a transposition or the identity). -/
@[simp] theorem length_applySwap {α : Type _} (k : Nat) (xs : List α) :
    (applySwap k xs).length = xs.length := by
  unfold applySwap
  cases h0 : xs[0]? with
  | none => simp [h0]
  | some a =>
      cases hk : xs[k]? with
      | none => simp [h0, hk]
      | some b => simp [h0, hk, List.length_set]

/-- `applySwaps` preserves length. -/
@[simp] theorem length_applySwaps {α : Type _} (ps : List Nat) (xs : List α) :
    (applySwaps ps xs).length = xs.length := by
  induction ps generalizing xs with
  | nil => rfl
  | cons k ps ih => rw [applySwaps_cons, ih, length_applySwap]

/-! ## Single `.swap` ⇔ `applySwap` -/

/-- `applySwap (d+1)` on a cons whose `(d+1)`-th element exists is exactly the
`type?`-shape transposition `slot :: rest.set d top`. -/
theorem applySwap_succ_cons
    {α : Type _} {d : Nat} {top slot : α} {rest : List α}
    (hGet : (top :: rest)[d + 1]? = some slot) :
    applySwap (d + 1) (top :: rest) = slot :: rest.set d top := by
  unfold applySwap
  simp only [List.getElem?_cons_zero, hGet]
  -- (xs.set 0 slot).set (d+1) top with xs = top :: rest
  rw [List.set_cons_zero]
  rw [List.set_cons_succ]

/-- **The swap-typing dictionary.**  `type? (.swap d)` succeeds exactly when
`d < 16` and the `(d+1)`-th slot exists, and then transposes the slots by
`applySwap (d+1)` while leaving the frame `tail` untouched. -/
theorem type?_swap_eq_applySwap
    {d : Nat} {input output : Shape}
    (hType : Instr.type? (.swap d) input = some output) :
    d < 16 ∧ d + 1 < input.slots.length ∧
      output = { slots := applySwap (d + 1) input.slots, tail := input.tail } := by
  unfold Instr.type? at hType
  by_cases hDepth : d < 16
  · simp [hDepth] at hType
    cases hSlots : input.slots with
    | nil => simp [Shape.get?, hSlots] at hType
    | cons top rest =>
        cases hGet : input.get? (d + 1) with
        | none => simp [hSlots, hGet] at hType
        | some slot =>
            simp [hSlots, hGet] at hType
            have hGet' : (top :: rest)[d + 1]? = some slot := by
              have h : input.slots[d + 1]? = some slot := hGet
              rw [hSlots] at h; exact h
            have hIndex : d + 1 < (top :: rest).length :=
              List.getElem?_eq_some_iff.mp hGet' |>.1
            refine ⟨hDepth, hIndex, ?_⟩
            rw [← hType, applySwap_succ_cons hGet']
  · simp [hDepth] at hType

/-- Converse definedness: if `d < 16` and the `(d+1)`-th slot exists, `type? (.swap
d)` succeeds with the `applySwap` transposition. -/
theorem type?_swap_of_lt
    {d : Nat} {input : Shape}
    (hDepth : d < 16) (hLen : d + 1 < input.slots.length) :
    Instr.type? (.swap d) input =
      some { slots := applySwap (d + 1) input.slots, tail := input.tail } := by
  obtain ⟨top, rest, hSlots⟩ : ∃ top rest, input.slots = top :: rest := by
    cases h : input.slots with
    | nil => rw [h] at hLen; exact absurd hLen (by simp)
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨slot, hGet'⟩ : ∃ slot, (top :: rest)[d + 1]? = some slot :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hSlots]; exact hLen)⟩
  have hget : input.get? (d + 1) = some slot := by
    unfold Shape.get?; rw [hSlots]; exact hGet'
  unfold Instr.type?
  simp only [hDepth, if_true, hSlots, hget]
  rw [applySwap_succ_cons hGet']

/-! ## A `.swap` run ⇔ `applySwaps` on `bodyType?` -/

/-- Shape equality reduces to slots + tail equality. -/
theorem Shape.ext_slots_tail {s t : Shape}
    (hs : s.slots = t.slots) (ht : s.tail = t.tail) : s = t := by
  cases s; cases t; simp_all

/-- **Forward threading.**  A `.swap` run that types from `input` threads the
slots by `applySwaps` on the depth-shifted positions and leaves the frame `tail`
fixed. -/
theorem bodyType?_map_swap_eq
    (ds : List Nat) (input out : Shape)
    (hType : Block.bodyType? (ds.map Instr.swap) input = some out) :
    out = { slots := applySwaps (ds.map (· + 1)) input.slots, tail := input.tail } := by
  induction ds generalizing input with
  | nil =>
      simp only [List.map_nil, Block.bodyType?, Option.some.injEq] at hType
      subst hType
      exact Shape.ext_slots_tail (by simp [applySwaps]) rfl
  | cons d ds ih =>
      simp only [List.map_cons, Block.bodyType?] at hType
      cases hMid : Instr.type? (.swap d) input with
      | none => rw [hMid] at hType; simp at hType
      | some mid =>
          rw [hMid] at hType
          have hType' : Block.bodyType? (ds.map Instr.swap) mid = some out := hType
          obtain ⟨_hd, _hlen, hmidEq⟩ := type?_swap_eq_applySwap hMid
          have hout := ih mid hType'
          rw [hout, hmidEq]
          exact Shape.ext_slots_tail (by simp only [List.map_cons, applySwaps_cons]) rfl

/-- **Definedness.**  If every depth is `< 16` and its target slot is present (a
uniform bound that swaps preserve, since they keep length), the run types with
the `applySwaps` result. -/
theorem bodyType?_map_swap_of
    (ds : List Nat) (input : Shape)
    (hBound : ∀ d ∈ ds, d < 16 ∧ d + 1 < input.slots.length) :
    Block.bodyType? (ds.map Instr.swap) input =
      some { slots := applySwaps (ds.map (· + 1)) input.slots, tail := input.tail } := by
  induction ds generalizing input with
  | nil =>
      simp only [List.map_nil, Block.bodyType?, applySwaps_nil]
  | cons d ds ih =>
      obtain ⟨hd, hlen⟩ := hBound d (by simp)
      have hBound' : ∀ e ∈ ds, e < 16 ∧
          e + 1 < (applySwap (d + 1) input.slots).length := by
        intro e he
        obtain ⟨he16, helen⟩ := hBound e (by simp [he])
        exact ⟨he16, by rw [length_applySwap]; exact helen⟩
      simp only [List.map_cons, Block.bodyType?, applySwaps_cons]
      rw [type?_swap_of_lt hd hlen]
      show Block.bodyType? (ds.map Instr.swap)
          { slots := applySwap (d + 1) input.slots, tail := input.tail } = _
      rw [ih _ hBound']

/-! ## (P2) Permutation-action naturality: `applySwaps` depends only on `netStack`

The action of a transposition list on a list factors through its net window
permutation.  Hence two position lists with equal `netStack` act identically on
any list — the second of the two pure-permutation facts the `canonBody`
preservation reduces to. -/

/-- `applySwap` is natural under `List.map`: permuting then relabelling equals
relabelling then permuting. -/
theorem applySwap_map {α β : Type _} (f : α → β) (k : Nat) (l : List α) :
    applySwap k (l.map f) = (applySwap k l).map f := by
  unfold applySwap
  rw [List.getElem?_map, List.getElem?_map]
  cases h0 : l[0]? with
  | none => simp [h0]
  | some a =>
      cases hk : l[k]? with
      | none => simp [h0, hk]
      | some b =>
          simp only [h0, hk, Option.map_some]
          rw [List.map_set, List.map_set]

/-- `applySwaps` is natural under `List.map`. -/
theorem applySwaps_map {α β : Type _} (f : α → β) (ps : List Nat) (l : List α) :
    applySwaps ps (l.map f) = (applySwaps ps l).map f := by
  induction ps generalizing l with
  | nil => rfl
  | cons k ps ih => rw [applySwaps_cons, applySwaps_cons, applySwap_map, ih]

/-- Reconstruct a list from its length window by gathering. -/
theorem range_map_getElem! {α : Type _} [Inhabited α] (xs : List α) :
    (List.range xs.length).map (fun j => xs[j]!) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    have hi : i < xs.length := by simpa using h1
    rw [getElem!_pos xs i hi]

/-- **The factoring.**  `applySwaps ps xs` is the net window permutation
`netStack ps xs.length` used to gather from `xs`. -/
theorem applySwaps_eq_gather {α : Type _} [Inhabited α] (ps : List Nat)
    (xs : List α) :
    applySwaps ps xs = (netStack ps xs.length).map (fun j => xs[j]!) := by
  conv_lhs => rw [← range_map_getElem! xs]
  rw [applySwaps_map]
  rfl

/-- **(P2) naturality.**  Equal `netStack` (over the shared length window) ⟹
equal `applySwaps` on any list. -/
theorem applySwaps_congr_of_netStack {α : Type _} [Inhabited α]
    (ps qs : List Nat) (xs : List α)
    (h : netStack ps xs.length = netStack qs xs.length) :
    applySwaps ps xs = applySwaps qs xs := by
  rw [applySwaps_eq_gather ps xs, applySwaps_eq_gather qs xs, h]

/-! ## The per-run type-preservation reduction

Combining the dictionary (forward + definedness) with (P2) naturality reduces the
`bodyType?`-preservation of `canonSwaps` on a single swap run to the two
pure-permutation facts, stated here as explicit hypotheses:

* `hNet` — `canonSwaps` preserves the net window permutation.  In the unfired
  branch this is `rfl`; in the fired branch it is exactly **(P1)** selection-sort
  realisability (`netStack (starDecompose t) t.length = t`) transported from the
  decomposition window `maxDepth+1` up to the slot window (both agree because all
  positions stay below `maxDepth+1 ≤ input.slots.length`).
* `hBound` — every canonical depth is `< 16` and lands in range (its position
  never exceeds the original run's deepest, which the typing bound already caps).

Both are `ShuffleCanon`-internal permutation facts, independent of the typed
`Shape` layer; discharging them (the §Session-75 frontier) upgrades this to an
unconditional `canonBody`/`canonBlock` WellTyped/`lower?` preservation. -/

/-- A default `Slot` for the gather reconstruction (local; this leaf is imported
by nobody). -/
private instance : Inhabited Slot := ⟨Slot.word⟩

/-- **Per-run type-preservation (reduction).**  If a swap run types from `input`,
and `canonSwaps` preserves both the net permutation (`hNet`) and the in-range
bound (`hBound`), then the canonicalised run types from `input` to the SAME
output — the crux `canonBody` preservation modulo the two pure-permutation
facts. -/
theorem canonSwaps_bodyType?_preserve
    (r : List Nat) (input out : Shape)
    (hType : Block.bodyType? (r.map Instr.swap) input = some out)
    (hBound : ∀ e ∈ canonSwaps r, e < 16 ∧ e + 1 < input.slots.length)
    (hNet : netStack ((canonSwaps r).map (· + 1)) input.slots.length
          = netStack (r.map (· + 1)) input.slots.length) :
    Block.bodyType? ((canonSwaps r).map Instr.swap) input = some out := by
  have hout : out =
      { slots := applySwaps (r.map (· + 1)) input.slots, tail := input.tail } :=
    bodyType?_map_swap_eq r input out hType
  rw [bodyType?_map_swap_of (canonSwaps r) input hBound, hout]
  apply congrArg some
  refine Shape.ext_slots_tail ?_ rfl
  exact applySwaps_congr_of_netStack _ _ input.slots hNet

end ShuffleCanon
end TypedCfg
end EvmCompiler
