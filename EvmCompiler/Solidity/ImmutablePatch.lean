import EvmCompiler.Solidity.VerifiedStackObjectArtifact

/-!
# Deploy-time immutable patching, verified

Contracts with `immutable` variables compile through a marker scheme: the
checked pipeline compiles the code twice — once with the caller-supplied
(`zero`) immutable values and once with distinguished marker values — pins the
push sites where the two compiles differ (`Assembly.Compact.differingPushPcs?`)
so both compiles share one instruction layout, and exports the marker byte
offsets as `immutableReferences`.  External tools patch actual values into the
emitted bytes at deploy time.

This module gives that patching step a semantics:

* `Frontend.patchImmutables` is the byte-level patcher (the Lean model of what
  deploy-time tooling does with `image.immutableReferences`).
* `Frontend.Bytecode.ByteDiffAt` is a window decomposition relating two byte
  images that agree everywhere except on 32-byte push payload windows.
* `Assembly.Compact` level: two `compile?` runs over shape-identical programs
  with the same pin set produce `ByteDiffAt`-related bytes whose windows sit
  exactly at the pinned push payloads
  (`compile?_byteDiff_of_differingPushPcs`).
* Frontend level: a successful `compileVerifiedStackCodeArtifactIn?` yields
  `ByteDiffAt 0 artifact.bytes artifact.immutableMarkerBytes ws`
  (`compileVerifiedStackCodeArtifactIn?_byteDiff`), and patching the compiled
  bytes at the exported references with the marker values reproduces the
  marker compile exactly (`patchImmutables_markerBytes_of_byteDiff`), while
  patching with actual values reproduces the actual-value compile
  (`patchImmutables_compileWithImmutableValues?`).
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

namespace Bytecode

/-! ## The patcher

`patchImmutableReferences` and `patchImmutables` live in `Frontend.lean`'s
`Bytecode` namespace so the checked pipeline can gate on them at compile
time; this module carries their semantics. -/

/-! ## Pointwise characterisation of `patchBytesAt` -/

theorem patchBytesAt_length {start : Nat} {replacement bytes : List UInt8}
    (hIn : start + replacement.length ≤ bytes.length) :
    (patchBytesAt start replacement bytes).length = bytes.length := by
  simp [patchBytesAt]
  omega

theorem patchBytesAt_getElem?_left {start : Nat}
    {replacement bytes : List UInt8} {p : Nat}
    (hIn : start + replacement.length ≤ bytes.length)
    (hLt : p < start) :
    (patchBytesAt start replacement bytes)[p]? = bytes[p]? := by
  have hTakeLen : (bytes.take start).length = start := by
    simp; omega
  rw [patchBytesAt, List.append_assoc,
    List.getElem?_append_left (by omega), List.getElem?_take, if_pos hLt]

theorem patchBytesAt_getElem?_inside {start : Nat}
    {replacement bytes : List UInt8} {p : Nat}
    (hIn : start + replacement.length ≤ bytes.length)
    (hGe : start ≤ p) (hLt : p < start + replacement.length) :
    (patchBytesAt start replacement bytes)[p]? = replacement[p - start]? := by
  have hTakeLen : (bytes.take start).length = start := by
    simp; omega
  rw [patchBytesAt, List.append_assoc,
    List.getElem?_append_right (by omega), hTakeLen,
    List.getElem?_append_left (by omega)]

theorem patchBytesAt_getElem?_right {start : Nat}
    {replacement bytes : List UInt8} {p : Nat}
    (hIn : start + replacement.length ≤ bytes.length)
    (hGe : start + replacement.length ≤ p) :
    (patchBytesAt start replacement bytes)[p]? = bytes[p]? := by
  have hTakeLen : (bytes.take start).length = start := by
    simp; omega
  rw [patchBytesAt, List.append_assoc,
    List.getElem?_append_right (by omega), hTakeLen,
    List.getElem?_append_right (by omega), List.getElem?_drop]
  congr 1
  omega

/-- Reading a byte inside a window whose content is a known prefix of the
target at that offset. -/
theorem getElem?_of_startsWithAt {needle bytes : List UInt8} {start p : Nat}
    (hStarts : startsWithAt needle bytes start = true)
    (hGe : start ≤ p) (hLt : p < start + needle.length) :
    bytes[p]? = needle[p - start]? := by
  unfold startsWithAt at hStarts
  have hTake : ((bytes.drop start).take needle.length) = needle := by
    simpa using hStarts
  have hDrop : (bytes.drop start)[p - start]? = needle[p - start]? := by
    rw [← hTake, List.getElem?_take_of_lt (by omega)]
  rw [List.getElem?_drop] at hDrop
  rw [← hDrop]
  congr 1
  omega

theorem length_le_of_startsWithAt {needle bytes : List UInt8} {start : Nat}
    (hNeedle : 0 < needle.length)
    (hStarts : startsWithAt needle bytes start = true) :
    start + needle.length ≤ bytes.length := by
  unfold startsWithAt at hStarts
  have hTake : ((bytes.drop start).take needle.length) = needle := by
    simpa using hStarts
  have hLen : ((bytes.drop start).take needle.length).length = needle.length := by
    rw [hTake]
  simp at hLen
  omega

/-! ## Patch-to-target: pointwise reconstruction -/

/-- `p` lies inside one of the exported 32-byte reference windows. -/
def CoveredByReferences (references : List ImmutableReference) (p : Nat) :
    Prop :=
  ∃ r ∈ references, r.start ≤ p ∧ p < r.start + 32

/-- `p` lies inside one of the exported windows of any name group. -/
def CoveredByRefs (refs : List (Name × List ImmutableReference)) (p : Nat) :
    Prop :=
  ∃ entry ∈ refs, CoveredByReferences entry.snd p

/-- Every reference window of every group carries, in `target`, exactly the
encoded word assigned to the group's name by `values`. -/
def RefsMatchTarget (target : List UInt8)
    (refs : List (Name × List ImmutableReference))
    (values : List (Name × Word)) : Prop :=
  ∀ entry ∈ refs, ∃ value,
    values.find? (fun e => e.fst == entry.fst) = some value ∧
      ∀ r ∈ entry.snd,
        startsWithAt (Assembly.Bytecode.encodeWord32 value.snd) target
          r.start = true

private theorem patchBytesAt_toTarget_spec
    {bytes target replacement : List UInt8} {start : Nat}
    (hLen : bytes.length = target.length)
    (hRepl : 0 < replacement.length)
    (hStarts : startsWithAt replacement target start = true) :
    (patchBytesAt start replacement bytes).length = target.length ∧
      (∀ p, ¬ (start ≤ p ∧ p < start + replacement.length) →
        (patchBytesAt start replacement bytes)[p]? = bytes[p]?) ∧
      (∀ p, start ≤ p → p < start + replacement.length →
        (patchBytesAt start replacement bytes)[p]? = target[p]?) := by
  have hIn : start + replacement.length ≤ target.length :=
    length_le_of_startsWithAt hRepl hStarts
  have hIn' : start + replacement.length ≤ bytes.length := by omega
  refine ⟨by rw [patchBytesAt_length hIn', hLen], ?_, ?_⟩
  · intro p hOut
    rcases Nat.lt_or_ge p start with hLt | hGe
    · exact patchBytesAt_getElem?_left hIn' hLt
    · exact patchBytesAt_getElem?_right hIn' (by omega)
  · intro p hGe hLt
    rw [patchBytesAt_getElem?_inside hIn' hGe hLt,
      getElem?_of_startsWithAt hStarts hGe hLt]

private theorem patchImmutableReferences_toTarget_spec
    {value : Word} {target : List UInt8} :
    ∀ {references : List ImmutableReference} {bytes : List UInt8},
      bytes.length = target.length →
      (∀ r ∈ references,
        startsWithAt (Assembly.Bytecode.encodeWord32 value) target
          r.start = true) →
      (patchImmutableReferences value bytes references).length =
          target.length ∧
        (∀ p, ¬ CoveredByReferences references p →
          (patchImmutableReferences value bytes references)[p]? =
            bytes[p]?) ∧
        (∀ p, CoveredByReferences references p →
          (patchImmutableReferences value bytes references)[p]? =
            target[p]?)
  | [], bytes, hLen, _hContent => by
      refine ⟨hLen, fun p _ => rfl, fun p hCov => ?_⟩
      rcases hCov with ⟨r, hr, _⟩
      simp at hr
  | reference :: rest, bytes, hLen, hContent => by
      have hHead := hContent reference (List.mem_cons_self ..)
      have hEnc : 0 < (Assembly.Bytecode.encodeWord32 value).length := by
        rw [Assembly.Bytecode.encodeWord32_length]; omega
      obtain ⟨hLen', hOut', hIn'⟩ :=
        patchBytesAt_toTarget_spec (start := reference.start) hLen hEnc hHead
      have hRest := patchImmutableReferences_toTarget_spec
        (references := rest)
        (bytes := patchBytesAt reference.start
          (Assembly.Bytecode.encodeWord32 value) bytes)
        hLen' (fun r hr => hContent r (List.mem_cons_of_mem _ hr))
      obtain ⟨hLenR, hOutR, hInR⟩ := hRest
      have hEncLen : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
        Assembly.Bytecode.encodeWord32_length value
      refine ⟨hLenR, ?_, ?_⟩
      · intro p hNCov
        have hNHead : ¬ (reference.start ≤ p ∧ p < reference.start + 32) :=
          fun h => hNCov ⟨reference, List.mem_cons_self .., h⟩
        have hNRest : ¬ CoveredByReferences rest p := by
          rintro ⟨r, hr, hw⟩
          exact hNCov ⟨r, List.mem_cons_of_mem _ hr, hw⟩
        rw [patchImmutableReferences, hOutR p hNRest]
        exact hOut' p (by rw [hEncLen]; exact hNHead)
      · intro p hCov
        rw [patchImmutableReferences]
        by_cases hRestCov : CoveredByReferences rest p
        · exact hInR p hRestCov
        · have hHeadCov : reference.start ≤ p ∧ p < reference.start + 32 := by
            rcases hCov with ⟨r, hr, hw⟩
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hw
            · exact absurd ⟨r, hr', hw⟩ hRestCov
          rw [hOutR p hRestCov]
          exact hIn' p hHeadCov.1 (by rw [hEncLen]; exact hHeadCov.2)

private theorem patchImmutables_toTarget_spec
    {target : List UInt8} {values : List (Name × Word)} :
    ∀ {refs : List (Name × List ImmutableReference)} {bytes : List UInt8},
      bytes.length = target.length →
      RefsMatchTarget target refs values →
      (patchImmutables bytes refs values).length = target.length ∧
        (∀ p, ¬ CoveredByRefs refs p →
          (patchImmutables bytes refs values)[p]? = bytes[p]?) ∧
        (∀ p, CoveredByRefs refs p →
          (patchImmutables bytes refs values)[p]? = target[p]?)
  | [], bytes, hLen, _hMatch => by
      refine ⟨hLen, fun p _ => rfl, fun p hCov => ?_⟩
      rcases hCov with ⟨entry, hEntry, _⟩
      simp at hEntry
  | (name, references) :: rest, bytes, hLen, hMatch => by
      obtain ⟨value, hFind, hContent⟩ :=
        hMatch (name, references) (List.mem_cons_self ..)
      obtain ⟨hLen', hOut', hIn'⟩ :=
        patchImmutableReferences_toTarget_spec (value := value.snd)
          (references := references) (bytes := bytes) hLen hContent
      have hRest := patchImmutables_toTarget_spec
        (refs := rest)
        (bytes := patchImmutableReferences value.snd bytes references)
        hLen' (fun entry hEntry => hMatch entry (List.mem_cons_of_mem _ hEntry))
      obtain ⟨hLenR, hOutR, hInR⟩ := hRest
      refine ⟨?_, ?_, ?_⟩
      · rw [patchImmutables, hFind]; exact hLenR
      · intro p hNCov
        have hNHead : ¬ CoveredByReferences references p :=
          fun h => hNCov ⟨(name, references), List.mem_cons_self .., h⟩
        have hNRest : ¬ CoveredByRefs rest p := by
          rintro ⟨entry, hEntry, hw⟩
          exact hNCov ⟨entry, List.mem_cons_of_mem _ hEntry, hw⟩
        rw [patchImmutables, hFind, hOutR p hNRest]
        exact hOut' p hNHead
      · intro p hCov
        rw [patchImmutables, hFind]
        by_cases hRestCov : CoveredByRefs rest p
        · exact hInR p hRestCov
        · have hHeadCov : CoveredByReferences references p := by
            rcases hCov with ⟨entry, hEntry, hw⟩
            rcases List.mem_cons.mp hEntry with rfl | hEntry'
            · exact hw
            · exact absurd ⟨entry, hEntry', hw⟩ hRestCov
          rw [hOutR p hRestCov]
          exact hIn' p hHeadCov

/-- **Patch reconstruction.**  If every exported window carries in `target`
exactly the encoded assigned value, and `bytes` already agrees with `target`
everywhere outside the exported windows, then patching recovers `target`
exactly. -/
theorem patchImmutables_eq_target
    {bytes target : List UInt8}
    {refs : List (Name × List ImmutableReference)}
    {values : List (Name × Word)}
    (hLen : bytes.length = target.length)
    (hMatch : RefsMatchTarget target refs values)
    (hAgree : ∀ p, bytes[p]? = target[p]? ∨ CoveredByRefs refs p) :
    patchImmutables bytes refs values = target := by
  obtain ⟨hLenP, hOut, hIn⟩ :=
    patchImmutables_toTarget_spec (refs := refs) (bytes := bytes) hLen hMatch
  apply List.ext_getElem?
  intro p
  rcases Classical.em (CoveredByRefs refs p) with hCov | hNCov
  · exact hIn p hCov
  · rcases hAgree p with hEq | hCov
    · rw [hOut p hNCov, hEq]
    · exact absurd hCov hNCov

/-! ## `findOccurrences` specification -/

private theorem mem_acc_findOccurrencesAux {needle bytes : List UInt8} :
    ∀ {fuel start : Nat} {acc : List Nat} {q : Nat}, q ∈ acc →
      q ∈ findOccurrencesAux needle bytes start fuel acc
  | 0, _start, acc, q, hq => by
      simpa [findOccurrencesAux] using hq
  | fuel + 1, start, acc, q, hq => by
      rw [findOccurrencesAux]
      by_cases hHit : startsWithAt needle bytes start
      · exact mem_acc_findOccurrencesAux (by simp [hHit, List.mem_cons, hq])
      · exact mem_acc_findOccurrencesAux (by simp [hHit, hq])

private theorem mem_findOccurrencesAux_of_startsWithAt
    {needle bytes : List UInt8} :
    ∀ {fuel start : Nat} {acc : List Nat} {p : Nat},
      startsWithAt needle bytes p = true → start ≤ p → p < start + fuel →
      p ∈ findOccurrencesAux needle bytes start fuel acc
  | 0, start, _acc, p, _hStarts, hGe, hLt => by omega
  | fuel + 1, start, acc, p, hStarts, hGe, hLt => by
      rw [findOccurrencesAux]
      rcases Nat.eq_or_lt_of_le hGe with rfl | hGt
      · exact mem_acc_findOccurrencesAux (by simp [hStarts])
      · by_cases hHit : startsWithAt needle bytes start <;>
          exact mem_findOccurrencesAux_of_startsWithAt hStarts
            (by omega) (by omega)

private theorem startsWithAt_of_mem_findOccurrencesAux
    {needle bytes : List UInt8} :
    ∀ {fuel start : Nat} {acc : List Nat} {p : Nat},
      p ∈ findOccurrencesAux needle bytes start fuel acc →
      p ∈ acc ∨ (startsWithAt needle bytes p = true ∧ p < start + fuel)
  | 0, _start, acc, p, hMem => by
      rw [findOccurrencesAux] at hMem
      exact .inl (by simpa using hMem)
  | fuel + 1, start, acc, p, hMem => by
      rw [findOccurrencesAux] at hMem
      by_cases hHit : startsWithAt needle bytes start
      · simp only [hHit, if_pos] at hMem
        rcases startsWithAt_of_mem_findOccurrencesAux hMem with hAcc | hHit'
        · rcases List.mem_cons.mp hAcc with rfl | hAcc'
          · exact .inr ⟨hHit, by omega⟩
          · exact .inl hAcc'
        · exact .inr ⟨hHit'.1, by omega⟩
      · simp only [hHit, if_neg, Bool.false_eq_true, not_false_iff] at hMem
        rcases startsWithAt_of_mem_findOccurrencesAux hMem with hAcc | hHit'
        · exact .inl hAcc
        · exact .inr ⟨hHit'.1, by omega⟩

theorem mem_findOccurrences_iff {needle bytes : List UInt8} {p : Nat}
    (hNeedle : needle ≠ []) (hBound : p ≤ bytes.length) :
    p ∈ findOccurrences needle bytes ↔
      startsWithAt needle bytes p = true := by
  cases needle with
  | nil => exact absurd rfl hNeedle
  | cons b tail =>
      rw [findOccurrences]
      constructor
      · intro hMem
        rcases startsWithAt_of_mem_findOccurrencesAux hMem with hAcc | hHit
        · simp at hAcc
        · exact hHit.1
      · intro hStarts
        exact mem_findOccurrencesAux_of_startsWithAt hStarts
          (Nat.zero_le _) (by omega)

/-! ## Export lemmas for `immutableReferenceEntriesFromCodes` -/

theorem mem_immutableReferencesForMarkerFromCodes_facts
    {zeroBytes markerBytes : List UInt8} {value : Word}
    {r : ImmutableReference}
    (hMem : r ∈ immutableReferencesForMarkerFromCodes zeroBytes markerBytes
      value) :
    startsWithAt (Assembly.Bytecode.encodeWord32 value) markerBytes
        r.start = true ∧
      startsWithAt zeroWord32 zeroBytes r.start = true ∧
      r.length = ImmutableReference.patchLength := by
  unfold immutableReferencesForMarkerFromCodes at hMem
  rcases List.mem_map.mp hMem with ⟨start, hStart, rfl⟩
  rcases List.mem_filter.mp hStart with ⟨hFind, hZero⟩
  have hLen : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
    Assembly.Bytecode.encodeWord32_length value
  have hNeedle : Assembly.Bytecode.encodeWord32 value ≠ [] := by
    intro h
    rw [h] at hLen
    simp at hLen
  have hStarts : startsWithAt (Assembly.Bytecode.encodeWord32 value)
      markerBytes start = true := by
    cases hEnc : Assembly.Bytecode.encodeWord32 value with
    | nil => exact absurd hEnc hNeedle
    | cons b tail =>
        rw [hEnc, findOccurrences] at hFind
        rcases startsWithAt_of_mem_findOccurrencesAux hFind with hAcc | hHit
        · simp at hAcc
        · exact hEnc ▸ hHit.1
  exact ⟨hStarts, hZero, rfl⟩

theorem mem_immutableReferencesForMarkerFromCodes_of_startsWithAt
    {zeroBytes markerBytes : List UInt8} {value : Word} {p : Nat}
    (hMarker : startsWithAt (Assembly.Bytecode.encodeWord32 value)
      markerBytes p = true)
    (hZero : startsWithAt zeroWord32 zeroBytes p = true) :
    ({ start := p, length := ImmutableReference.patchLength } :
        ImmutableReference) ∈
      immutableReferencesForMarkerFromCodes zeroBytes markerBytes value := by
  have hLen : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
    Assembly.Bytecode.encodeWord32_length value
  have hNeedle : Assembly.Bytecode.encodeWord32 value ≠ [] := by
    intro h
    rw [h] at hLen
    simp at hLen
  have hBound : p ≤ markerBytes.length := by
    have := length_le_of_startsWithAt (by omega) hMarker
    omega
  unfold immutableReferencesForMarkerFromCodes
  refine List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨?_, hZero⟩, rfl⟩
  exact (mem_findOccurrences_iff hNeedle hBound).mpr hMarker

theorem mem_immutableReferenceEntriesFromCodes
    {zeroBytes markerBytes : List UInt8} :
    ∀ {entries : List (Name × Word)} {e : Name × Word}, e ∈ entries →
      (e.fst,
        immutableReferencesForMarkerFromCodes zeroBytes markerBytes e.snd) ∈
        immutableReferenceEntriesFromCodes zeroBytes markerBytes entries
  | [], e, hMem => by simp at hMem
  | (name, value) :: rest, e, hMem => by
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _
          (mem_immutableReferenceEntriesFromCodes hMem')

theorem mem_immutableReferenceEntriesFromCodes_elim
    {zeroBytes markerBytes : List UInt8} :
    ∀ {entries : List (Name × Word)}
      {bucket : Name × List ImmutableReference},
      bucket ∈ immutableReferenceEntriesFromCodes zeroBytes markerBytes
        entries →
      ∃ value, (bucket.fst, value) ∈ entries ∧
        bucket.snd =
          immutableReferencesForMarkerFromCodes zeroBytes markerBytes value
  | [], bucket, hMem => by simp [immutableReferenceEntriesFromCodes] at hMem
  | (name, value) :: rest, bucket, hMem => by
      rw [immutableReferenceEntriesFromCodes] at hMem
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · exact ⟨value, List.mem_cons_self .., rfl⟩
      · obtain ⟨v, hv, hEq⟩ :=
          mem_immutableReferenceEntriesFromCodes_elim hMem'
        exact ⟨v, List.mem_cons_of_mem _ hv, hEq⟩

/-! ## Window decompositions between two compiled images -/

/-- `ByteDiffAt off base target ws` decomposes two byte images that share one
instruction layout: they agree byte for byte except on the listed 32-byte
windows, where `base` carries `encodeWord32 va` and `target` carries
`encodeWord32 vb`.  The `Nat` in each window is its absolute start offset
(`off` is the absolute offset of the head of the lists). -/
inductive ByteDiffAt :
    Nat → List UInt8 → List UInt8 → List (Nat × Word × Word) → Prop where
  | nil (off : Nat) : ByteDiffAt off [] [] []
  | same {off : Nat} (c : UInt8) {base target : List UInt8}
      {ws : List (Nat × Word × Word)}
      (rest : ByteDiffAt (off + 1) base target ws) :
      ByteDiffAt off (c :: base) (c :: target) ws
  | window {off : Nat} (va vb : Word) {base target : List UInt8}
      {ws : List (Nat × Word × Word)}
      (rest : ByteDiffAt (off + 32) base target ws) :
      ByteDiffAt off (Assembly.Bytecode.encodeWord32 va ++ base)
        (Assembly.Bytecode.encodeWord32 vb ++ target) ((off, va, vb) :: ws)

namespace ByteDiffAt

theorem refl : ∀ (bytes : List UInt8) (off : Nat), ByteDiffAt off bytes bytes []
  | [], off => .nil off
  | c :: rest, off => .same c (refl rest (off + 1))

theorem append_same {off : Nat} :
    ∀ {prefixBytes base target : List UInt8} {ws : List (Nat × Word × Word)},
      ByteDiffAt (off + prefixBytes.length) base target ws →
      ByteDiffAt off (prefixBytes ++ base) (prefixBytes ++ target) ws := by
  intro prefixBytes
  induction prefixBytes generalizing off with
  | nil => intro base target ws h; simpa using h
  | cons c rest ih =>
      intro base target ws h
      refine .same c (ih ?_)
      have : off + (c :: rest).length = off + 1 + rest.length := by
        simp; omega
      rwa [this] at h

theorem append_suffix {suffix : List UInt8} :
    ∀ {off : Nat} {base target : List UInt8} {ws : List (Nat × Word × Word)},
      ByteDiffAt off base target ws →
      ByteDiffAt off (base ++ suffix) (target ++ suffix) ws := by
  intro off base target ws h
  induction h with
  | nil off => simpa using refl suffix off
  | same c _ ih => exact .same c ih
  | window va vb _ ih =>
      simpa [List.append_assoc] using
        ByteDiffAt.window (off := _) va vb ih

theorem length_eq {off : Nat} {base target : List UInt8}
    {ws : List (Nat × Word × Word)}
    (h : ByteDiffAt off base target ws) : base.length = target.length := by
  induction h with
  | nil => rfl
  | same c _ ih => simpa using ih
  | window va vb _ ih =>
      simp [Assembly.Bytecode.encodeWord32_length, ih]

/-- Bytes agree at every position not covered by a window. -/
theorem agree_outside {off : Nat} {base target : List UInt8}
    {ws : List (Nat × Word × Word)}
    (h : ByteDiffAt off base target ws) :
    ∀ q, (∀ w ∈ ws, ¬ (w.1 ≤ off + q ∧ off + q < w.1 + 32)) →
      base[q]? = target[q]? := by
  induction h with
  | nil => intro q _; rfl
  | same c rest ih =>
      intro q hOut
      cases q with
      | zero => rfl
      | succ q' =>
          simp only [List.getElem?_cons_succ]
          refine ih q' fun w hw => ?_
          have := hOut w hw
          omega
  | window va vb rest ih =>
      rename_i off' base' target' ws'
      intro q hOut
      have hHead := hOut (off', va, vb) (List.mem_cons_self ..)
      simp only at hHead
      have hEnc : (Assembly.Bytecode.encodeWord32 va).length = 32 :=
        Assembly.Bytecode.encodeWord32_length va
      have hEnc' : (Assembly.Bytecode.encodeWord32 vb).length = 32 :=
        Assembly.Bytecode.encodeWord32_length vb
      have hGe : 32 ≤ q := by omega
      rw [List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega), hEnc, hEnc']
      refine ih (q - 32) fun w hw => ?_
      have := hOut w (List.mem_cons_of_mem _ hw)
      omega

/-- Every window start carries the decoded contents in both images. -/
theorem window_facts {off : Nat} {base target : List UInt8}
    {ws : List (Nat × Word × Word)}
    (h : ByteDiffAt off base target ws) :
    ∀ w ∈ ws, off ≤ w.1 ∧
      startsWithAt (Assembly.Bytecode.encodeWord32 w.2.1) base
        (w.1 - off) = true ∧
      startsWithAt (Assembly.Bytecode.encodeWord32 w.2.2) target
        (w.1 - off) = true := by
  induction h with
  | nil => intro w hw; simp at hw
  | same c rest ih =>
      rename_i off' base' target' ws'
      intro w hw
      obtain ⟨hGe, hBase, hTarget⟩ := ih w hw
      have hShift : ∀ (needle tail : List UInt8) (b : UInt8) (s : Nat),
          startsWithAt needle tail s = true →
          startsWithAt needle (b :: tail) (s + 1) = true := by
        intro needle tail b s hs
        unfold startsWithAt at hs ⊢
        simpa using hs
      have hIdx : w.1 - off' = (w.1 - (off' + 1)) + 1 := by omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [hIdx]; exact hShift _ _ _ _ hBase
      · rw [hIdx]; exact hShift _ _ _ _ hTarget
  | window va vb rest ih =>
      rename_i off' base' target' ws'
      intro w hw
      have hStartsPrefix : ∀ (l tail : List UInt8),
          l.length = 32 → startsWithAt l (l ++ tail) 0 = true := by
        intro l tail _
        unfold startsWithAt
        simp
      have hShift32 : ∀ (needle l tail : List UInt8) (s : Nat),
          l.length = 32 → startsWithAt needle tail s = true →
          startsWithAt needle (l ++ tail) (s + 32) = true := by
        intro needle l tail s hl hs
        unfold startsWithAt at hs ⊢
        rw [List.drop_append]
        have hNil : l.drop (s + 32) = [] :=
          List.drop_eq_nil_of_le (by omega)
        rw [hNil, hl, show s + 32 - 32 = s by omega]
        simpa using hs
      rcases List.mem_cons.mp hw with rfl | hw'
      · refine ⟨Nat.le_refl _, ?_, ?_⟩
        · simpa using hStartsPrefix _ base'
            (Assembly.Bytecode.encodeWord32_length va)
        · simpa using hStartsPrefix _ target'
            (Assembly.Bytecode.encodeWord32_length vb)
      · obtain ⟨hGe, hBase, hTarget⟩ := ih w hw'
        have hIdx : w.1 - off' = (w.1 - (off' + 32)) + 32 := by omega
        refine ⟨by omega, ?_, ?_⟩
        · rw [hIdx]
          exact hShift32 _ _ _ _ (Assembly.Bytecode.encodeWord32_length va)
            hBase
        · rw [hIdx]
          exact hShift32 _ _ _ _ (Assembly.Bytecode.encodeWord32_length vb)
            hTarget

end ByteDiffAt

/-! ## Patching recovers the marker-value compile -/

private theorem find?_entries_of_nodup :
    ∀ {entries : List (Name × Word)} {n : Name} {v : Word},
      (entries.map Prod.fst).Nodup → (n, v) ∈ entries →
      entries.find? (fun e => e.fst == n) = some (n, v)
  | [], _, _, _, hMem => by simp at hMem
  | (m, u) :: rest, n, v, hNodup, hMem => by
      rcases List.mem_cons.mp hMem with hEq | hMem'
      · cases hEq
        simp [List.find?]
      · simp only [List.map_cons, List.nodup_cons, List.mem_map] at hNodup
        have hNe : (m == n) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro hEq
          subst hEq
          exact hNodup.1 ⟨(m, v), hMem', rfl⟩
        rw [List.find?, hNe]
        exact find?_entries_of_nodup hNodup.2 hMem'

/-- **Marker-compile reconstruction, byte level.**  Given a window
decomposition between the compiled bytes and the marker-compile bytes whose
windows carry the zero word on the compiled side and one of the exported
marker values on the marker side, patching the compiled bytes at the exported
`immutableReferences` with the marker values reproduces the marker compile
exactly. -/
theorem patchImmutables_markerBytes_of_byteDiff
    {zeroBytes markerBytes : List UInt8} {ws : List (Nat × Word × Word)}
    {entries : List (Name × Word)}
    (hDiff : ByteDiffAt 0 zeroBytes markerBytes ws)
    (hNodup : (entries.map Prod.fst).Nodup)
    (hSites : ∀ w ∈ ws, w.2.1 = EvmYul.UInt256.ofNat 0 ∧
      ∃ e ∈ entries, w.2.2 = e.snd) :
    patchImmutables zeroBytes
      (immutableReferenceEntriesFromCodes zeroBytes markerBytes entries)
      entries = markerBytes := by
  have hLen : zeroBytes.length = markerBytes.length := hDiff.length_eq
  refine patchImmutables_eq_target hLen ?_ ?_
  · intro bucket hBucket
    obtain ⟨value, hEntry, hRefs⟩ :=
      mem_immutableReferenceEntriesFromCodes_elim hBucket
    refine ⟨(bucket.fst, value), find?_entries_of_nodup hNodup hEntry, ?_⟩
    intro r hr
    rw [hRefs] at hr
    exact (mem_immutableReferencesForMarkerFromCodes_facts hr).1
  · intro p
    rcases Classical.em (∃ w ∈ ws, w.1 ≤ p ∧ p < w.1 + 32) with hCov | hNCov
    · right
      obtain ⟨w, hw, hRange⟩ := hCov
      obtain ⟨hZeroVal, e, hEntry, hMarkerVal⟩ := hSites w hw
      obtain ⟨_hGe, hBase, hTarget⟩ := hDiff.window_facts w hw
      rw [Nat.sub_zero] at hBase hTarget
      have hZeroStarts : startsWithAt zeroWord32 zeroBytes w.1 = true := by
        rw [hZeroVal] at hBase
        exact hBase
      have hMarkerStarts :
          startsWithAt (Assembly.Bytecode.encodeWord32 e.snd) markerBytes
            w.1 = true := by
        rw [hMarkerVal] at hTarget
        exact hTarget
      have hRefMem :=
        mem_immutableReferencesForMarkerFromCodes_of_startsWithAt
          (zeroBytes := zeroBytes) hMarkerStarts hZeroStarts
      refine ⟨(e.fst, immutableReferencesForMarkerFromCodes zeroBytes
          markerBytes e.snd),
        mem_immutableReferenceEntriesFromCodes hEntry,
        ⟨{ start := w.1, length := ImmutableReference.patchLength },
          hRefMem, ?_⟩⟩
      exact hRange
    · left
      refine hDiff.agree_outside p fun w hw => ?_
      intro hRange
      exact hNCov ⟨w, hw, by omega⟩

end Bytecode

/-! ## Two `Assembly.Compact.compile?` runs with shared pins differ only at
pinned push payloads -/

/-- Structural alignment of two assembly programs with identical instruction
shape: they agree instruction for instruction except that push values may
differ, and every (source-pc, actual-value, marker-value) site is recorded.
This is the relational content of `Assembly.Compact.differingPushPcsFrom?`. -/
inductive PushDiffSites :
    Assembly.Program → Assembly.Program → Nat →
      List (Nat × Word × Word) → Prop where
  | nil (spc : Nat) : PushDiffSites [] [] spc []
  | push {a b : Assembly.Program} {spc : Nat}
      {sites : List (Nat × Word × Word)} (va vb : Word)
      (rest : PushDiffSites a b (spc + (Assembly.Instr.push va).byteSize)
        sites) :
      PushDiffSites (.push va :: a) (.push vb :: b) spc
        ((spc, va, vb) :: sites)
  | keep {a b : Assembly.Program} {spc : Nat}
      {sites : List (Nat × Word × Word)} (instr : Assembly.Instr)
      (rest : PushDiffSites a b (spc + instr.byteSize) sites) :
      PushDiffSites (instr :: a) (instr :: b) spc sites

theorem pushDiffSites_of_differingPushPcsFrom?
    {a b : Assembly.Program} {spc : Nat} {pcs : List Nat}
    (hDiff : Assembly.Compact.differingPushPcsFrom? a b spc = some pcs) :
    ∃ sites, PushDiffSites a b spc sites ∧ sites.map Prod.fst = pcs := by
  fun_induction Assembly.Compact.differingPushPcsFrom? a b spc
    generalizing pcs with
  | case1 spc =>
      simp only [Option.some.injEq] at hDiff
      exact ⟨[], hDiff ▸ ⟨.nil spc, rfl⟩⟩
  | case2 actual aRest marker bRest spc ih =>
      cases hRest : Assembly.Compact.differingPushPcsFrom? aRest bRest
          (spc + (Assembly.Instr.push actual).byteSize) with
      | none => rw [hRest] at hDiff; simp at hDiff
      | some rest =>
          rw [hRest] at hDiff
          obtain ⟨sites, hSites, hMap⟩ := ih hRest
          by_cases hEq : actual = marker
          · subst hEq
            simp at hDiff
            exact ⟨sites, hDiff ▸ ⟨.keep (.push actual) hSites, hMap⟩⟩
          · simp [hEq] at hDiff
            refine ⟨(spc, actual, marker) :: sites, ?_, ?_⟩
            · exact .push actual marker hSites
            · rw [List.map_cons, hMap, hDiff]
  | case3 aRest instr bRest spc hNotPush ih =>
      obtain ⟨sites, hSites, hMap⟩ := ih hDiff
      exact ⟨sites, .keep instr hSites, hMap⟩
  | case4 => exact absurd hDiff (by simp)
  | case5 => exact absurd hDiff (by simp)

private theorem layoutRev?_eq_of_pushDiffSites
    {pins : List Nat} {bw : Assembly.Compact.BranchWidths}
    {a b : Assembly.Program} {spc : Nat} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b spc sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    ∀ (cpc : Nat) (acc : Assembly.Compact.LabelTable),
      Assembly.Compact.layoutRev? pins bw b spc cpc acc =
        Assembly.Compact.layoutRev? pins bw a spc cpc acc := by
  induction h with
  | nil spc => intro cpc acc; rfl
  | push va vb rest ih =>
      rename_i a' b' spc' sites'
      intro cpc acc
      have hMem : spc' ∈ pins := by
        simpa using hPins (spc', va, vb) (List.mem_cons_self ..)
      have hPins' : ∀ s ∈ sites', s.1 ∈ pins := fun s hs =>
        hPins s (List.mem_cons_of_mem _ hs)
      simp only [Assembly.Compact.layoutRev?,
        Assembly.Compact.sourceInstrSizeAt?, Assembly.Compact.pushWidthAt?,
        hMem, if_pos, Option.bind_some, List.contains_eq_mem, decide_true,
        Assembly.Instr.byteSize]
      exact ih hPins' _ _
  | keep instr rest ih =>
      rename_i a' b' spc' sites'
      intro cpc acc
      cases hSize : Assembly.Compact.sourceInstrSizeAt? pins bw spc' instr with
      | none =>
          simp [Assembly.Compact.layoutRev?, hSize]
      | some size =>
          simp only [Assembly.Compact.layoutRev?, hSize, Option.bind_some]
          exact ih hPins _ _

private theorem layout?_eq_of_pushDiffSites
    {pins : List Nat} {bw : Assembly.Compact.BranchWidths}
    {a b : Assembly.Program} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b 0 sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    Assembly.Compact.layout? pins b bw = Assembly.Compact.layout? pins a bw :=
  layoutRev?_eq_of_pushDiffSites h hPins 0 []

private theorem PushDiffSites.length_eq
    {a b : Assembly.Program} {spc : Nat}
    {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b spc sites) :
    b.length = a.length := by
  induction h <;> simp_all

private theorem initialBranchWidthsRev_eq_of_pushDiffSites
    {a b : Assembly.Program} {spc : Nat}
    {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b spc sites) :
    ∀ acc,
      Assembly.Compact.initialBranchWidthsRev b spc acc =
        Assembly.Compact.initialBranchWidthsRev a spc acc := by
  induction h with
  | nil => intro acc; rfl
  | push va vb rest ih =>
      intro acc
      exact ih acc
  | keep instr rest ih =>
      intro acc
      cases instr <;> exact ih _

private theorem branchWidthsForLabelsRev?_eq_of_pushDiffSites
    {labels : Assembly.Compact.LabelTable}
    {a b : Assembly.Program} {spc : Nat}
    {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b spc sites) :
    ∀ acc,
      Assembly.Compact.branchWidthsForLabelsRev? labels b spc acc =
        Assembly.Compact.branchWidthsForLabelsRev? labels a spc acc := by
  induction h with
  | nil => intro acc; rfl
  | push va vb rest ih =>
      intro acc
      exact ih acc
  | keep instr rest ih =>
      rename_i a' b' spc' sites'
      intro acc
      cases instr with
      | label | prim | push | pushLabel | jumpDynamic =>
          exact ih acc
      | jump target | jumpi target =>
          simp only [Assembly.Compact.branchWidthsForLabelsRev?]
          cases hDest : Assembly.Compact.lookupLabel? labels target with
          | none => simp [hDest]
          | some dest =>
              cases hWidth : Assembly.Compact.widthForNat? dest with
              | none => simp [hWidth]
              | some width =>
                  simpa [hWidth] using ih ((spc', width) :: acc)

private theorem relocateBranchesLoop?_eq_of_pushDiffSites
    {pins : List Nat}
    {a b : Assembly.Program} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b 0 sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    ∀ fuel widths,
      Assembly.Compact.relocateBranchesLoop? pins b fuel widths =
        Assembly.Compact.relocateBranchesLoop? pins a fuel widths := by
  intro fuel
  induction fuel with
  | zero =>
      intro widths
      rfl
  | succ fuel ih =>
      intro widths
      unfold Assembly.Compact.relocateBranchesLoop?
      rw [layout?_eq_of_pushDiffSites h hPins]
      cases hLayout : Assembly.Compact.layout? pins a widths with
      | none => simp [hLayout]
      | some layoutResult =>
          rcases layoutResult with ⟨labels, codeLength⟩
          simp [hLayout, Assembly.Compact.branchWidthsForLabels?,
            branchWidthsForLabelsRev?_eq_of_pushDiffSites h, ih]

private theorem relocateBranches?_eq_of_pushDiffSites
    {pins : List Nat}
    {a b : Assembly.Program} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b 0 sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    Assembly.Compact.relocateBranches? pins b =
      Assembly.Compact.relocateBranches? pins a := by
  unfold Assembly.Compact.relocateBranches?
  rw [h.length_eq]
  unfold Assembly.Compact.initialBranchWidths
  rw [initialBranchWidthsRev_eq_of_pushDiffSites h []]
  exact relocateBranchesLoop?_eq_of_pushDiffSites h hPins _ _

/-- Flattened bytes of the emitted source blocks. -/
private def blockBytes (blocks : List Assembly.Compact.SourceBlock) :
    List UInt8 :=
  (Assembly.Compact.blocksCode blocks).flatMap Assembly.Compact.encodeLocated

private theorem blockBytes_nil : blockBytes [] = [] := rfl

private theorem blockBytes_cons (block : Assembly.Compact.SourceBlock)
    (rest : List Assembly.Compact.SourceBlock) :
    blockBytes (block :: rest) =
      block.code.flatMap Assembly.Compact.encodeLocated ++ blockBytes rest := by
  simp [blockBytes, Assembly.Compact.blocksCode]

private theorem emitBlocksFrom?_byteDiff
    {pins : List Nat} {bw : Assembly.Compact.BranchWidths}
    {table : Assembly.Compact.LabelTable}
    {a b : Assembly.Program} {spc : Nat} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b spc sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    ∀ {cpc : Nat} {blocksA blocksB : List Assembly.Compact.SourceBlock},
      Assembly.Compact.emitBlocksFrom? pins bw table a spc cpc =
        some blocksA →
      Assembly.Compact.emitBlocksFrom? pins bw table b spc cpc =
        some blocksB →
      ∃ ws, Bytecode.ByteDiffAt cpc (blockBytes blocksA)
          (blockBytes blocksB) ws ∧
        ws.map (fun w => w.2) = sites.map (fun s => s.2) := by
  induction h with
  | nil spc =>
      intro cpc blocksA blocksB hA hB
      simp only [Assembly.Compact.emitBlocksFrom?, Option.some.injEq]
        at hA hB
      subst hA; subst hB
      exact ⟨[], .nil cpc, rfl⟩
  | push va vb rest ih =>
      rename_i a' b' spc' sites'
      intro cpc blocksA blocksB hA hB
      have hMem : spc' ∈ pins := by
        simpa using hPins (spc', va, vb) (List.mem_cons_self ..)
      have hPins' : ∀ s ∈ sites', s.1 ∈ pins := fun s hs =>
        hPins s (List.mem_cons_of_mem _ hs)
      have hSizeA : Assembly.Compact.sourceInstrSizeAt? pins bw spc'
          (.push va) = some 33 := by
        simp [Assembly.Compact.sourceInstrSizeAt?,
          Assembly.Compact.pushWidthAt?, hMem]
      have hSizeB : Assembly.Compact.sourceInstrSizeAt? pins bw spc'
          (.push vb) = some 33 := by
        simp [Assembly.Compact.sourceInstrSizeAt?,
          Assembly.Compact.pushWidthAt?, hMem]
      have hCodeA : Assembly.Compact.emitSourceBlock? pins bw spc' cpc table
          (.push va) = some [{ pc := cpc, instr := .push 32 va }] := by
        simp [Assembly.Compact.emitSourceBlock?,
          Assembly.Compact.emitInstrRev?, Assembly.Compact.pushWidthAt?,
          Assembly.Compact.pushInstrOfWidth, hMem]
      have hCodeB : Assembly.Compact.emitSourceBlock? pins bw spc' cpc table
          (.push vb) = some [{ pc := cpc, instr := .push 32 vb }] := by
        simp [Assembly.Compact.emitSourceBlock?,
          Assembly.Compact.emitInstrRev?, Assembly.Compact.pushWidthAt?,
          Assembly.Compact.pushInstrOfWidth, hMem]
      rw [Assembly.Compact.emitBlocksFrom?, hSizeA, hCodeA] at hA
      rw [Assembly.Compact.emitBlocksFrom?, hSizeB, hCodeB] at hB
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Assembly.Instr.byteSize, Assembly.Instr.push32Size] at hA hB
      simp only [Assembly.Instr.byteSize, Assembly.Instr.push32Size] at ih
      cases hRA : Assembly.Compact.emitBlocksFrom? pins bw table a'
          (spc' + 33) (cpc + 33) with
      | none => rw [hRA] at hA; simp at hA
      | some restA =>
          cases hRB : Assembly.Compact.emitBlocksFrom? pins bw table b'
              (spc' + 33) (cpc + 33) with
          | none => rw [hRB] at hB; simp at hB
          | some restB =>
              rw [hRA] at hA
              rw [hRB] at hB
              simp only [Option.bind_eq_bind, Option.bind_some,
                Option.some.injEq] at hA hB
              subst hA; subst hB
              obtain ⟨ws, hWs, hMap⟩ := ih hPins' hRA hRB
              refine ⟨(cpc + 1, va, vb) :: ws, ?_, by simpa using hMap⟩
              rw [blockBytes_cons, blockBytes_cons]
              have hEncA :
                  [({ pc := cpc, instr := .push 32 va } :
                    Assembly.Compact.Located)].flatMap
                      Assembly.Compact.encodeLocated =
                  UInt8.ofNat (0x5f + 32) ::
                    Assembly.Bytecode.encodeWord32 va := by
                simp [Assembly.Compact.encodeLocated,
                  Assembly.Compact.encodeInstr, Assembly.Compact.encodePush,
                  Assembly.Bytecode.encodeWord32]
              have hEncB :
                  [({ pc := cpc, instr := .push 32 vb } :
                    Assembly.Compact.Located)].flatMap
                      Assembly.Compact.encodeLocated =
                  UInt8.ofNat (0x5f + 32) ::
                    Assembly.Bytecode.encodeWord32 vb := by
                simp [Assembly.Compact.encodeLocated,
                  Assembly.Compact.encodeInstr, Assembly.Compact.encodePush,
                  Assembly.Bytecode.encodeWord32]
              rw [hEncA, hEncB, List.cons_append, List.cons_append]
              have hWs' : Bytecode.ByteDiffAt (cpc + 1 + 32)
                  (blockBytes restA) (blockBytes restB) ws := by
                rw [show cpc + 1 + 32 = cpc + 33 from by omega]
                exact hWs
              exact Bytecode.ByteDiffAt.same _
                (Bytecode.ByteDiffAt.window va vb hWs')
  | keep instr rest ih =>
      rename_i a' b' spc' sites'
      intro cpc blocksA blocksB hA hB
      cases hSize : Assembly.Compact.sourceInstrSizeAt? pins bw spc'
          instr with
      | none =>
          rw [Assembly.Compact.emitBlocksFrom?, hSize] at hA
          simp at hA
      | some size =>
          cases hCode : Assembly.Compact.emitSourceBlock? pins bw spc' cpc
              table instr with
          | none =>
              rw [Assembly.Compact.emitBlocksFrom?, hSize, hCode] at hA
              simp at hA
          | some code =>
              rw [Assembly.Compact.emitBlocksFrom?, hSize, hCode] at hA hB
              simp only [Option.pure_def, Option.bind_eq_bind,
                Option.bind_some] at hA hB
              cases hRA : Assembly.Compact.emitBlocksFrom? pins bw table a'
                  (spc' + instr.byteSize) (cpc + size) with
              | none => rw [hRA] at hA; simp at hA
              | some restA =>
                  cases hRB : Assembly.Compact.emitBlocksFrom? pins bw table
                      b' (spc' + instr.byteSize) (cpc + size) with
                  | none => rw [hRB] at hB; simp at hB
                  | some restB =>
                      rw [hRA] at hA
                      rw [hRB] at hB
                      simp only [Option.bind_eq_bind, Option.bind_some,
                        Option.some.injEq] at hA hB
                      subst hA; subst hB
                      obtain ⟨ws, hWs, hMap⟩ := ih hPins hRA hRB
                      refine ⟨ws, ?_, hMap⟩
                      rw [blockBytes_cons, blockBytes_cons]
                      have hLen : (code.flatMap
                          Assembly.Compact.encodeLocated).length = size := by
                        rw [Assembly.Compact.flatMap_encodeLocated_length]
                        exact Assembly.Compact.emitSourceBlock?_codeByteLength
                          hSize hCode
                      refine Bytecode.ByteDiffAt.append_same ?_
                      rw [hLen]
                      exact hWs

private theorem compile?_pinnedPushPcs
    {source : Assembly.Program} {pins : List Nat}
    {artifact : Assembly.Compact.Artifact}
    (hCompile : Assembly.Compact.compile? source pins = some artifact) :
    artifact.pinnedPushPcs = pins := by
  unfold Assembly.Compact.compile? at hCompile
  by_cases hFits : source.PCFits
  · simp [hFits] at hCompile
    cases hPreparation : Assembly.Compact.alignPreparation? source
        (Assembly.Compact.prepare source) with
    | none => simp [hPreparation] at hCompile
    | some preparation =>
        simp [hPreparation] at hCompile
        by_cases hSafe : Assembly.Compact.preparationSafeIndexed? source
            (Assembly.Compact.prepare source) preparation = true
        · simp [hSafe] at hCompile
          cases hRelocate : Assembly.Compact.relocateBranches? pins
              (Assembly.Compact.prepare source) with
          | none => simp [hRelocate] at hCompile
          | some relocation =>
              rcases relocation with ⟨branchWidths, labels, codeLength⟩
              simp [hRelocate] at hCompile
              cases hEmit : Assembly.Compact.emit? pins
                          (Assembly.Compact.prepare source) branchWidths labels with
                      | none => simp [hEmit] at hCompile
                      | some program =>
                          simp [hEmit] at hCompile
                          cases hBlocks : Assembly.Compact.emitBlocks? pins
                              (Assembly.Compact.prepare source) branchWidths labels with
                          | none => simp [hBlocks] at hCompile
                          | some blocks =>
                              simp [hBlocks] at hCompile
                              by_cases hCodeCheck :
                                  Assembly.Compact.blocksCodeMatches? blocks
                                    program.code = true
                              · simp [hCodeCheck] at hCompile
                                by_cases hLabels :
                                    Assembly.Compact.labelsConsistent? blocks
                                      labels = true
                                · simp [hLabels] at hCompile
                                  by_cases hWellFormed :
                                      program.wellFormed? = true
                                  · simp [hWellFormed] at hCompile
                                    by_cases hSentinel :
                                        Assembly.Compact.Program.codeByteLength
                                            program.code + 1 <
                                          18446744073709551616
                                    · simp [hSentinel] at hCompile
                                      cases hCompile
                                      rfl
                                    · simp [hSentinel] at hCompile
                                  · simp [hWellFormed] at hCompile
                                · simp [hLabels] at hCompile
                              · simp [hCodeCheck] at hCompile
        · simp [hSafe] at hCompile
  · simp [hFits] at hCompile

/-- **Compile-level window decomposition.**  Two `Assembly.Compact.compile?`
runs over programs whose prepared forms share one instruction shape
(`differingPushPcs?` succeeded) and whose differing push sites are all pinned
produce byte images that agree everywhere except on the 32-byte payloads of
the pinned differing pushes, whose values are exactly the source push
values. -/
theorem compile?_byteDiff_of_differingPushPcs
    {sourceA sourceB : Assembly.Program} {pins pcs : List Nat}
    {ca cb : Assembly.Compact.Artifact}
    (hDiff : Assembly.Compact.differingPushPcs? sourceA sourceB = some pcs)
    (hPins : ∀ p ∈ pcs, p ∈ pins)
    (hA : Assembly.Compact.compile? sourceA pins = some ca)
    (hB : Assembly.Compact.compile? sourceB pins = some cb) :
    ∃ sites ws,
      PushDiffSites (Assembly.Compact.prepare sourceA)
        (Assembly.Compact.prepare sourceB) 0 sites ∧
      sites.map Prod.fst = pcs ∧
      Bytecode.ByteDiffAt 0 ca.bytes.toList cb.bytes.toList ws ∧
      ws.map (fun w => w.2) = sites.map (fun s => s.2) := by
  obtain ⟨sites, hSites, hMap⟩ := pushDiffSites_of_differingPushPcsFrom? hDiff
  have hPinsSites : ∀ s ∈ sites, s.1 ∈ pins := by
    intro s hs
    exact hPins s.1 (hMap ▸ List.mem_map.mpr ⟨s, hs, rfl⟩)
  have hValidA := Assembly.Compact.compile?_valid hA
  have hValidB := Assembly.Compact.compile?_valid hB
  have hPinsA : ca.pinnedPushPcs = pins := compile?_pinnedPushPcs hA
  have hPinsB : cb.pinnedPushPcs = pins := compile?_pinnedPushPcs hB
  -- Both compiles produce the same relocation plan.
  have hRelocateA := hValidA.relocated
  have hRelocateB := hValidB.relocated
  rw [hPinsA, hValidA.physicalSource] at hRelocateA
  rw [hPinsB, hValidB.physicalSource] at hRelocateB
  rw [relocateBranches?_eq_of_pushDiffSites hSites hPinsSites,
    hRelocateA] at hRelocateB
  have hRelocation := Option.some.inj hRelocateB
  have hWidthsEq : cb.branchWidths = ca.branchWidths := by
    exact (congrArg Prod.fst hRelocation).symm
  have hLabelsEq : cb.labels = ca.labels := by
    exact (congrArg (fun result => result.2.1) hRelocation).symm
  -- Compare the emitted blocks.
  have hBlocksA := hValidA.blocks
  have hBlocksB := hValidB.blocks
  rw [hPinsA, hValidA.physicalSource] at hBlocksA
  rw [hPinsB, hValidB.physicalSource, hWidthsEq, hLabelsEq] at hBlocksB
  rw [Assembly.Compact.emitBlocks?] at hBlocksA hBlocksB
  obtain ⟨ws, hWs, hWsMap⟩ :=
    emitBlocksFrom?_byteDiff hSites hPinsSites hBlocksA hBlocksB
  refine ⟨sites, ws, hSites, hMap, ?_, hWsMap⟩
  have hBytesA : ca.bytes.toList = blockBytes ca.blocks := by
    rw [hValidA.bytes, Assembly.Compact.encode, ← hValidA.blockCode]
    simp [Assembly.Bytecode.ofList, blockBytes]
  have hBytesB : cb.bytes.toList = blockBytes cb.blocks := by
    rw [hValidB.bytes, Assembly.Compact.encode, ← hValidB.blockCode]
    simp [Assembly.Bytecode.ofList, blockBytes]
  rw [hBytesA, hBytesB]
  exact hWs

/-! ## Pipeline glue: a verified code artifact always admits a window
decomposition against its marker compile -/

private theorem immutablePushPlanFor?_markerTarget
    {object : Object} {context : ObjectBuiltinContext}
    {actual : Assembly.Program} {plan : Object.ImmutablePushPlan}
    {markerTarget : Assembly.Program}
    (hPlan : object.immutablePushPlanFor? context actual = some plan)
    (hTarget : plan.markerTarget? = some markerTarget) :
    Assembly.Compact.differingPushPcs? actual markerTarget =
      some plan.pinnedPushPcs := by
  unfold Object.immutablePushPlanFor? at hPlan
  dsimp only [] at hPlan
  split at hPlan
  · simp only [Option.some.injEq] at hPlan
    rw [← hPlan] at hTarget
    simp at hTarget
  · split at hPlan
    · simp only [Option.some.injEq] at hPlan
      rw [← hPlan] at hTarget
      simp at hTarget
    · simp only [Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at hPlan
      obtain ⟨resolved, hResolved, hPlan⟩ := hPlan
      obtain ⟨ordered, hOrdered, hPlan⟩ := hPlan
      obtain ⟨lower, hLower, hPlan⟩ := hPlan
      obtain ⟨compiled, hCompiled, hPlan⟩ := hPlan
      obtain ⟨pins, hPins, hPlan⟩ := hPlan
      simp only [Option.some.injEq] at hPlan
      rw [← hPlan] at hTarget ⊢
      simp only [Option.some.injEq] at hTarget
      rw [← hTarget]
      exact hPins

private theorem compileImmutableMarkerBytes?_elim
    {plan : Object.ImmutablePushPlan} {compact : Assembly.Compact.Artifact}
    {markerBytes : List UInt8}
    (hMarker : Object.compileImmutableMarkerBytes? plan compact = some markerBytes) :
    (plan.markerTarget? = none ∧
        markerBytes = compact.bytes.toList ++ Object.verifiedCodeSentinel) ∨
      ∃ markerTarget markerCompact,
        plan.markerTarget? = some markerTarget ∧
        Assembly.Compact.compile? markerTarget plan.pinnedPushPcs =
          some markerCompact ∧
        markerBytes = markerCompact.bytes.toList ++ Object.verifiedCodeSentinel := by
  unfold Object.compileImmutableMarkerBytes? at hMarker
  split at hMarker
  · rename_i hTarget
    exact .inl ⟨hTarget, (Option.some.inj hMarker).symm⟩
  · rename_i markerTarget hTarget
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
      at hMarker
    obtain ⟨markerCompact, hCompact, hMarker⟩ := hMarker
    exact .inr ⟨markerTarget, markerCompact, hTarget, hCompact,
      (Option.some.inj hMarker).symm⟩

/-- **Window decomposition for every verified code artifact.**  A successful
`compileVerifiedStackCodeArtifactIn?` run always yields a `ByteDiffAt`
decomposition between the compiled bytes and the marker compile bytes: they
share one instruction layout and differ only on 32-byte pinned push payload
windows. -/
theorem Object.compileVerifiedStackCodeArtifactIn?_byteDiff
    {object : Object} {context : ObjectBuiltinContext}
    {artifact : VerifiedStackCodeArtifact}
    (hCompile : object.compileVerifiedStackCodeArtifactIn? context =
      some artifact) :
    ∃ ws, Bytecode.ByteDiffAt 0 artifact.bytes artifact.immutableMarkerBytes
      ws := by
  obtain ⟨_hResolved, _hOrdered, _hLower, _hCompiled, pushPlan, hPlan,
      hCompact, hBytes, hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCompile
  rcases compileImmutableMarkerBytes?_elim hMarker with
    ⟨_hNone, hMarkerBytes⟩ | ⟨markerTarget, markerCompact, hTarget,
      hMarkerCompact, hMarkerBytes⟩
  · refine ⟨[], ?_⟩
    rw [hBytes, hMarkerBytes]
    exact Bytecode.ByteDiffAt.refl _ 0
  · have hPins := immutablePushPlanFor?_markerTarget hPlan hTarget
    obtain ⟨sites, ws, _hSites, _hMap, hWs, _hWsMap⟩ :=
      compile?_byteDiff_of_differingPushPcs hPins (fun p hp => hp)
        hCompact hMarkerCompact
    refine ⟨ws, ?_⟩
    rw [hBytes, hMarkerBytes]
    exact Bytecode.ByteDiffAt.append_suffix hWs

/-! ## Patching to an arbitrary value compile -/

namespace Bytecode

/-- **Value-compile reconstruction, byte level.**  Suppose the base compile
and a value compile each carry a window decomposition against one shared
marker-compile image.  If every base window carries the zero word and one of
the exported marker values (so it is exported as an `immutableReference`),
every value-compile window starts at an exported reference
(`hCoverValue`), and the value compile carries the encoded assigned value at
every exported site (`hMatch`), then patching the base bytes at the exported
references with the assigned values reproduces the value compile exactly. -/
theorem patchImmutables_valueBytes_of_byteDiffs
    {baseBytes markerBytes valueBytes : List UInt8}
    {wsBase wsValue : List (Nat × Word × Word)}
    {entries values : List (Name × Word)}
    (hDiffBase : ByteDiffAt 0 baseBytes markerBytes wsBase)
    (hDiffValue : ByteDiffAt 0 valueBytes markerBytes wsValue)
    (hSitesBase : ∀ w ∈ wsBase, w.2.1 = EvmYul.UInt256.ofNat 0 ∧
      ∃ e ∈ entries, w.2.2 = e.snd)
    (hMatch : RefsMatchTarget valueBytes
      (immutableReferenceEntriesFromCodes baseBytes markerBytes entries)
      values)
    (hCoverValue : ∀ w ∈ wsValue, ∃ e ∈ entries,
      ∃ r ∈ immutableReferencesForMarkerFromCodes baseBytes markerBytes
        e.snd, r.start = w.1) :
    patchImmutables baseBytes
      (immutableReferenceEntriesFromCodes baseBytes markerBytes entries)
      values = valueBytes := by
  have hLen : baseBytes.length = valueBytes.length := by
    rw [hDiffBase.length_eq, hDiffValue.length_eq]
  refine patchImmutables_eq_target hLen hMatch ?_
  intro p
  rcases Classical.em
      (CoveredByRefs
        (immutableReferenceEntriesFromCodes baseBytes markerBytes entries)
        p) with
    hCov | hNCov
  · exact .inr hCov
  · left
    have hBaseAgree : baseBytes[p]? = markerBytes[p]? := by
      refine hDiffBase.agree_outside p fun w hw => ?_
      intro hRange
      obtain ⟨hZeroVal, e, hEntry, hMarkerVal⟩ := hSitesBase w hw
      obtain ⟨_hGe, hBase, hTarget⟩ := hDiffBase.window_facts w hw
      rw [Nat.sub_zero] at hBase hTarget
      have hZeroStarts : startsWithAt zeroWord32 baseBytes w.1 = true := by
        rw [hZeroVal] at hBase
        exact hBase
      have hMarkerStarts :
          startsWithAt (Assembly.Bytecode.encodeWord32 e.snd) markerBytes
            w.1 = true := by
        rw [hMarkerVal] at hTarget
        exact hTarget
      exact hNCov
        ⟨(e.fst, immutableReferencesForMarkerFromCodes baseBytes markerBytes
            e.snd),
          mem_immutableReferenceEntriesFromCodes hEntry,
          ⟨{ start := w.1, length := ImmutableReference.patchLength },
            mem_immutableReferencesForMarkerFromCodes_of_startsWithAt
              hMarkerStarts hZeroStarts,
            (by omega : w.1 ≤ p ∧ p < w.1 + 32)⟩⟩
    have hValueAgree : valueBytes[p]? = markerBytes[p]? := by
      refine hDiffValue.agree_outside p fun w hw => ?_
      intro hRange
      obtain ⟨e, hEntry, r, hRef, hStart⟩ := hCoverValue w hw
      exact hNCov
        ⟨(e.fst, immutableReferencesForMarkerFromCodes baseBytes markerBytes
            e.snd),
          mem_immutableReferenceEntriesFromCodes hEntry,
          ⟨r, hRef, by omega⟩⟩
    rw [hBaseAgree, hValueAgree]

end Bytecode

/-- Compile the object with `loadimmutable` resolved to the supplied deploy
values instead of the context's own immutable values.  This is a thin wrapper
over the one supported pipeline — same resolution, lowering, stack allocation
and compact assembly — so every end-to-end theorem about
`compileVerifiedStackCodeArtifactIn?` applies to it directly. -/
def Object.compileVerifiedStackCodeArtifactWithImmutableValues?
    (object : Object) (context : ObjectBuiltinContext)
    (values : List (Name × Word)) : Option VerifiedStackCodeArtifact :=
  object.compileVerifiedStackCodeArtifactIn?
    { context with immutableValues := values }

/-- **Deploy-time patching is the value compile.**  Patching the base
artifact's bytes at its exported immutable references with the deploy values
yields exactly the bytes the verified pipeline itself emits when compiled
with those values resolved. -/
theorem Object.patchImmutables_compileWithImmutableValues?
    {object : Object} {context : ObjectBuiltinContext}
    {values entries : List (Name × Word)}
    {base withValues : VerifiedStackCodeArtifact}
    {wsBase wsValue : List (Nat × Word × Word)}
    (_hBase : object.compileVerifiedStackCodeArtifactIn? context = some base)
    (_hValues : object.compileVerifiedStackCodeArtifactWithImmutableValues?
      context values = some withValues)
    (hMarkerEq : withValues.immutableMarkerBytes =
      base.immutableMarkerBytes)
    (hDiffBase : Bytecode.ByteDiffAt 0 base.bytes base.immutableMarkerBytes
      wsBase)
    (hDiffValue : Bytecode.ByteDiffAt 0 withValues.bytes
      withValues.immutableMarkerBytes wsValue)
    (hSitesBase : ∀ w ∈ wsBase, w.2.1 = EvmYul.UInt256.ofNat 0 ∧
      ∃ e ∈ entries, w.2.2 = e.snd)
    (hMatch : Bytecode.RefsMatchTarget withValues.bytes
      (Bytecode.immutableReferenceEntriesFromCodes base.bytes
        base.immutableMarkerBytes entries) values)
    (hCoverValue : ∀ w ∈ wsValue, ∃ e ∈ entries,
      ∃ r ∈ Bytecode.immutableReferencesForMarkerFromCodes base.bytes
        base.immutableMarkerBytes e.snd, r.start = w.1) :
    Bytecode.patchImmutables base.bytes
      (Bytecode.immutableReferenceEntriesFromCodes base.bytes
        base.immutableMarkerBytes entries) values = withValues.bytes := by
  rw [hMarkerEq] at hDiffValue
  exact Bytecode.patchImmutables_valueBytes_of_byteDiffs hDiffBase hDiffValue
    hSitesBase hMatch hCoverValue

/-! ## Compile-gate semantics: unconditional deploy-time patching

`Object.immutablePatchChecked?` runs inside every successful
`compileVerifiedStackCodeArtifactIn?`.  The lemmas below extract its Boolean
facts into the hypotheses the patch reconstruction needs, so the headline
theorem `Object.patchImmutables_compileWithImmutableValues?_ofCompile` takes
only the two compile-success hypotheses. -/

namespace Bytecode

/-! ### Length and outside-window preservation for the patcher -/

theorem patchImmutableReferences_length {value : Word} :
    ∀ {references : List ImmutableReference} {bytes : List UInt8},
      (∀ r ∈ references, r.start + 32 ≤ bytes.length) →
      (patchImmutableReferences value bytes references).length = bytes.length
  | [], _bytes, _hIn => rfl
  | reference :: rest, bytes, hIn => by
      have hHead : reference.start + 32 ≤ bytes.length :=
        hIn reference (List.mem_cons_self ..)
      have hEnc : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
        Assembly.Bytecode.encodeWord32_length value
      have hLen : (patchBytesAt reference.start
          (Assembly.Bytecode.encodeWord32 value) bytes).length =
            bytes.length :=
        patchBytesAt_length (by rw [hEnc]; omega)
      rw [patchImmutableReferences,
        patchImmutableReferences_length (fun r hr => by
          rw [hLen]; exact hIn r (List.mem_cons_of_mem _ hr)), hLen]

theorem patchImmutables_length {values : List (Name × Word)} :
    ∀ {refs : List (Name × List ImmutableReference)} {bytes : List UInt8},
      (∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ bytes.length) →
      (patchImmutables bytes refs values).length = bytes.length
  | [], _bytes, _hIn => rfl
  | (name, references) :: rest, bytes, hIn => by
      have hHead : ∀ r ∈ references, r.start + 32 ≤ bytes.length :=
        hIn (name, references) (List.mem_cons_self ..)
      cases hFind : values.find? (fun entry => entry.fst == name) with
      | none =>
          rw [patchImmutables, hFind]
          exact patchImmutables_length
            (fun e he => hIn e (List.mem_cons_of_mem _ he))
      | some entry =>
          have hLen := patchImmutableReferences_length (value := entry.snd)
            (references := references) (bytes := bytes) hHead
          rw [patchImmutables, hFind,
            patchImmutables_length (fun e he r hr => by
              rw [hLen]; exact hIn e (List.mem_cons_of_mem _ he) r hr), hLen]

theorem patchImmutableReferences_getElem?_notCovered {value : Word} :
    ∀ {references : List ImmutableReference} {bytes : List UInt8} {p : Nat},
      (∀ r ∈ references, r.start + 32 ≤ bytes.length) →
      ¬ CoveredByReferences references p →
      (patchImmutableReferences value bytes references)[p]? = bytes[p]?
  | [], _bytes, _p, _hIn, _hNCov => rfl
  | reference :: rest, bytes, p, hIn, hNCov => by
      have hHead : reference.start + 32 ≤ bytes.length :=
        hIn reference (List.mem_cons_self ..)
      have hEnc : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
        Assembly.Bytecode.encodeWord32_length value
      have hIn' : reference.start +
          (Assembly.Bytecode.encodeWord32 value).length ≤ bytes.length := by
        rw [hEnc]; omega
      have hLen := patchBytesAt_length hIn'
      have hNHead : ¬ (reference.start ≤ p ∧ p < reference.start + 32) :=
        fun h => hNCov ⟨reference, List.mem_cons_self .., h⟩
      have hNRest : ¬ CoveredByReferences rest p := by
        rintro ⟨r, hr, hw⟩
        exact hNCov ⟨r, List.mem_cons_of_mem _ hr, hw⟩
      rw [patchImmutableReferences,
        patchImmutableReferences_getElem?_notCovered
          (fun r hr => by rw [hLen]; exact hIn r (List.mem_cons_of_mem _ hr))
          hNRest]
      rcases Nat.lt_or_ge p reference.start with hLt | hGe
      · exact patchBytesAt_getElem?_left hIn' hLt
      · have hGe32 : reference.start +
            (Assembly.Bytecode.encodeWord32 value).length ≤ p := by
          rw [hEnc]
          by_contra h
          exact hNHead ⟨hGe, by omega⟩
        exact patchBytesAt_getElem?_right hIn' hGe32

theorem patchImmutables_getElem?_notCovered {values : List (Name × Word)} :
    ∀ {refs : List (Name × List ImmutableReference)} {bytes : List UInt8}
      {p : Nat},
      (∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ bytes.length) →
      ¬ CoveredByRefs refs p →
      (patchImmutables bytes refs values)[p]? = bytes[p]?
  | [], _bytes, _p, _hIn, _hNCov => rfl
  | (name, references) :: rest, bytes, p, hIn, hNCov => by
      have hHead : ∀ r ∈ references, r.start + 32 ≤ bytes.length :=
        hIn (name, references) (List.mem_cons_self ..)
      have hNHead : ¬ CoveredByReferences references p :=
        fun h => hNCov ⟨(name, references), List.mem_cons_self .., h⟩
      have hNRest : ¬ CoveredByRefs rest p := by
        rintro ⟨e, he, hw⟩
        exact hNCov ⟨e, List.mem_cons_of_mem _ he, hw⟩
      cases hFind : values.find? (fun entry => entry.fst == name) with
      | none =>
          rw [patchImmutables, hFind]
          exact patchImmutables_getElem?_notCovered
            (fun e he => hIn e (List.mem_cons_of_mem _ he)) hNRest
      | some entry =>
          have hLen := patchImmutableReferences_length (value := entry.snd)
            (references := references) (bytes := bytes) hHead
          rw [patchImmutables, hFind,
            patchImmutables_getElem?_notCovered (fun e he r hr => by
              rw [hLen]; exact hIn e (List.mem_cons_of_mem _ he) r hr)
              hNRest]
          exact patchImmutableReferences_getElem?_notCovered hHead hNHead

/-! ### The zero word is thirty-two zero bytes -/

private theorem toBytesLE_zero :
    ∀ width, Assembly.Bytecode.toBytesLE width 0 = List.replicate width 0
  | 0 => rfl
  | width + 1 => by
      simp [Assembly.Bytecode.toBytesLE, toBytesLE_zero width,
        List.replicate_succ]

theorem zeroWord32_eq_replicate : zeroWord32 = List.replicate 32 0 := by
  have h0 : (EvmYul.UInt256.ofNat 0).toNat = 0 := rfl
  rw [zeroWord32, Assembly.Bytecode.encodeWord32, h0, toBytesLE_zero]
  simp

/-! ### Patching all-zero values fills every covered position with zero -/

private theorem patchImmutableReferences_getElem?_zero :
    ∀ {references : List ImmutableReference} {bytes : List UInt8} {p : Nat},
      (∀ r ∈ references, r.start + 32 ≤ bytes.length) →
      (CoveredByReferences references p ∨ bytes[p]? = some 0) →
      (patchImmutableReferences (EvmYul.UInt256.ofNat 0) bytes
        references)[p]? = some 0
  | [], _bytes, _p, _hIn, hCov => by
      rcases hCov with hCov | hEq
      · rcases hCov with ⟨r, hr, _⟩; simp at hr
      · simpa using hEq
  | reference :: rest, bytes, p, hIn, hCov => by
      have hHead : reference.start + 32 ≤ bytes.length :=
        hIn reference (List.mem_cons_self ..)
      have hEnc : (Assembly.Bytecode.encodeWord32
          (EvmYul.UInt256.ofNat 0)).length = 32 :=
        Assembly.Bytecode.encodeWord32_length _
      have hIn' : reference.start + (Assembly.Bytecode.encodeWord32
          (EvmYul.UInt256.ofNat 0)).length ≤ bytes.length := by
        rw [hEnc]; omega
      have hLen := patchBytesAt_length hIn'
      rw [patchImmutableReferences]
      refine patchImmutableReferences_getElem?_zero
        (fun r hr => by rw [hLen]; exact hIn r (List.mem_cons_of_mem _ hr))
        ?_
      by_cases hWin : reference.start ≤ p ∧ p < reference.start + 32
      · right
        rw [patchBytesAt_getElem?_inside hIn' hWin.1
          (by rw [hEnc]; exact hWin.2)]
        have hRepl : Assembly.Bytecode.encodeWord32
            (EvmYul.UInt256.ofNat 0) = List.replicate 32 0 :=
          zeroWord32_eq_replicate
        rw [hRepl, List.getElem?_replicate, if_pos (by omega)]
      · rcases hCov with hCovRefs | hZero
        · rcases hCovRefs with ⟨r, hr, hw⟩
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact absurd hw hWin
          · exact Or.inl ⟨r, hr', hw⟩
        · right
          rcases Nat.lt_or_ge p reference.start with hLt | hGe
          · rw [patchBytesAt_getElem?_left hIn' hLt]; exact hZero
          · have hGe32 : reference.start + (Assembly.Bytecode.encodeWord32
                (EvmYul.UInt256.ofNat 0)).length ≤ p := by
              rw [hEnc]
              by_contra h
              exact hWin ⟨hGe, by omega⟩
            rw [patchBytesAt_getElem?_right hIn' hGe32]; exact hZero

theorem patchImmutables_getElem?_zero
    {values : List (Name × Word)}
    (hValsZero : ∀ e ∈ values, e.snd = EvmYul.UInt256.ofNat 0) :
    ∀ {refs : List (Name × List ImmutableReference)} {bytes : List UInt8}
      {p : Nat},
      (∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ bytes.length) →
      (∀ e ∈ refs, (values.find? (fun v => v.fst == e.fst)).isSome) →
      (CoveredByRefs refs p ∨ bytes[p]? = some 0) →
      (patchImmutables bytes refs values)[p]? = some 0
  | [], _bytes, _p, _hIn, _hBound, hCov => by
      rcases hCov with hCov | hEq
      · rcases hCov with ⟨e, he, _⟩; simp at he
      · simpa using hEq
  | (name, references) :: rest, bytes, p, hIn, hBound, hCov => by
      have hSome := hBound (name, references) (List.mem_cons_self ..)
      cases hFind : values.find? (fun entry => entry.fst == name) with
      | none => rw [hFind] at hSome; simp at hSome
      | some entry =>
          have hEntryMem : entry ∈ values := List.mem_of_find?_eq_some hFind
          have hZero : entry.snd = EvmYul.UInt256.ofNat 0 :=
            hValsZero entry hEntryMem
          have hHead : ∀ r ∈ references, r.start + 32 ≤ bytes.length :=
            hIn (name, references) (List.mem_cons_self ..)
          have hLen := patchImmutableReferences_length (value := entry.snd)
            (references := references) (bytes := bytes) hHead
          rw [patchImmutables, hFind]
          refine patchImmutables_getElem?_zero hValsZero
            (fun e he r hr => by
              rw [hLen]; exact hIn e (List.mem_cons_of_mem _ he) r hr)
            (fun e he => hBound e (List.mem_cons_of_mem _ he))
            ?_
          rcases hCov with hCovRefs | hZeroByte
          · rcases hCovRefs with ⟨e, he, hw⟩
            rcases List.mem_cons.mp he with rfl | he'
            · right
              rw [hZero]
              exact patchImmutableReferences_getElem?_zero hHead (Or.inl hw)
            · exact Or.inl ⟨e, he', hw⟩
          · right
            rw [hZero]
            exact patchImmutableReferences_getElem?_zero hHead
              (Or.inr hZeroByte)

/-! ### Patching is input-congruent outside the written windows -/

private theorem patchImmutableReferences_getElem?_congr {value : Word} :
    ∀ {references : List ImmutableReference} {X Y : List UInt8} {p : Nat},
      X.length = Y.length →
      (∀ r ∈ references, r.start + 32 ≤ X.length) →
      (X[p]? = Y[p]? ∨ CoveredByReferences references p) →
      (patchImmutableReferences value X references)[p]? =
        (patchImmutableReferences value Y references)[p]?
  | [], _X, _Y, _p, _hLen, _hIn, hAgree => by
      rcases hAgree with hEq | hCov
      · exact hEq
      · rcases hCov with ⟨r, hr, _⟩; simp at hr
  | reference :: rest, X, Y, p, hLen, hIn, hAgree => by
      have hHead : reference.start + 32 ≤ X.length :=
        hIn reference (List.mem_cons_self ..)
      have hEnc : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
        Assembly.Bytecode.encodeWord32_length value
      have hInX : reference.start +
          (Assembly.Bytecode.encodeWord32 value).length ≤ X.length := by
        rw [hEnc]; omega
      have hInY : reference.start +
          (Assembly.Bytecode.encodeWord32 value).length ≤ Y.length := by
        rw [hEnc]; omega
      have hLenX := patchBytesAt_length (bytes := X)
        (start := reference.start) hInX
      have hLenY := patchBytesAt_length (bytes := Y)
        (start := reference.start) hInY
      simp only [patchImmutableReferences]
      refine patchImmutableReferences_getElem?_congr
        (by rw [hLenX, hLenY, hLen])
        (fun r hr => by rw [hLenX]; exact hIn r (List.mem_cons_of_mem _ hr))
        ?_
      by_cases hWin : reference.start ≤ p ∧ p < reference.start + 32
      · left
        rw [patchBytesAt_getElem?_inside hInX hWin.1
            (by rw [hEnc]; exact hWin.2),
          patchBytesAt_getElem?_inside hInY hWin.1
            (by rw [hEnc]; exact hWin.2)]
      · rcases hAgree with hEq | hCov
        · left
          rcases Nat.lt_or_ge p reference.start with hLt | hGe
          · rw [patchBytesAt_getElem?_left hInX hLt,
              patchBytesAt_getElem?_left hInY hLt]
            exact hEq
          · have hGe32 : reference.start +
                (Assembly.Bytecode.encodeWord32 value).length ≤ p := by
              rw [hEnc]
              by_contra h
              exact hWin ⟨hGe, by omega⟩
            rw [patchBytesAt_getElem?_right hInX hGe32,
              patchBytesAt_getElem?_right hInY hGe32]
            exact hEq
        · rcases hCov with ⟨r, hr, hw⟩
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact absurd hw hWin
          · exact Or.inr ⟨r, hr', hw⟩

theorem patchImmutables_getElem?_congr {values : List (Name × Word)} :
    ∀ {refs : List (Name × List ImmutableReference)} {X Y : List UInt8}
      {p : Nat},
      X.length = Y.length →
      (∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ X.length) →
      (∀ e ∈ refs, (values.find? (fun v => v.fst == e.fst)).isSome) →
      (X[p]? = Y[p]? ∨ CoveredByRefs refs p) →
      (patchImmutables X refs values)[p]? =
        (patchImmutables Y refs values)[p]?
  | [], _X, _Y, _p, _hLen, _hIn, _hBound, hAgree => by
      rcases hAgree with hEq | hCov
      · exact hEq
      · rcases hCov with ⟨e, he, _⟩; simp at he
  | (name, references) :: rest, X, Y, p, hLen, hIn, hBound, hAgree => by
      have hSome := hBound (name, references) (List.mem_cons_self ..)
      cases hFind : values.find? (fun entry => entry.fst == name) with
      | none => rw [hFind] at hSome; simp at hSome
      | some entry =>
          have hHead : ∀ r ∈ references, r.start + 32 ≤ X.length :=
            hIn (name, references) (List.mem_cons_self ..)
          have hLenX := patchImmutableReferences_length (value := entry.snd)
            (references := references) (bytes := X) hHead
          have hLenY := patchImmutableReferences_length (value := entry.snd)
            (references := references) (bytes := Y)
            (fun r hr => by rw [← hLen]; exact hHead r hr)
          simp only [patchImmutables, hFind]
          refine patchImmutables_getElem?_congr
            (by rw [hLenX, hLenY, hLen])
            (fun e he r hr => by
              rw [hLenX]; exact hIn e (List.mem_cons_of_mem _ he) r hr)
            (fun e he => hBound e (List.mem_cons_of_mem _ he))
            ?_
          rcases hAgree with hEq | hCov
          · left
            exact patchImmutableReferences_getElem?_congr hLen hHead
              (Or.inl hEq)
          · rcases hCov with ⟨e, he, hw⟩
            rcases List.mem_cons.mp he with rfl | he'
            · left
              exact patchImmutableReferences_getElem?_congr hLen hHead
                (Or.inr hw)
            · exact Or.inr ⟨e, he', hw⟩

theorem patchImmutables_congr {values : List (Name × Word)}
    {refs : List (Name × List ImmutableReference)} {X Y : List UInt8}
    (hLen : X.length = Y.length)
    (hIn : ∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ X.length)
    (hBound : ∀ e ∈ refs, (values.find? (fun v => v.fst == e.fst)).isSome)
    (hAgree : ∀ p, X[p]? = Y[p]? ∨ CoveredByRefs refs p) :
    patchImmutables X refs values = patchImmutables Y refs values :=
  List.ext_getElem? fun p =>
    patchImmutables_getElem?_congr hLen hIn hBound (hAgree p)

/-! ### Marker-only reference exports -/

theorem mem_immutableReferencesForMarker_startsWithAt
    {bytes : List UInt8} {value : Word} {r : ImmutableReference}
    (hMem : r ∈ immutableReferencesForMarker bytes value) :
    startsWithAt (Assembly.Bytecode.encodeWord32 value) bytes r.start =
      true := by
  unfold immutableReferencesForMarker at hMem
  rcases List.mem_map.mp hMem with ⟨start, hStart, rfl⟩
  have hLen : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
    Assembly.Bytecode.encodeWord32_length value
  cases hEnc : Assembly.Bytecode.encodeWord32 value with
  | nil => rw [hEnc] at hLen; simp at hLen
  | cons b tail =>
      rw [hEnc, findOccurrences] at hStart
      rcases startsWithAt_of_mem_findOccurrencesAux hStart with hAcc | hHit
      · simp at hAcc
      · exact hEnc ▸ hHit.1

theorem mem_immutableReferenceEntries {markerBytes : List UInt8} :
    ∀ {entries : List (Name × Word)} {e : Name × Word}, e ∈ entries →
      (e.fst, immutableReferencesForMarker markerBytes e.snd) ∈
        immutableReferenceEntries markerBytes entries
  | [], e, hMem => by simp at hMem
  | (name, value) :: rest, e, hMem => by
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_immutableReferenceEntries hMem')

theorem mem_immutableReferenceEntries_elim {markerBytes : List UInt8} :
    ∀ {entries : List (Name × Word)}
      {bucket : Name × List ImmutableReference},
      bucket ∈ immutableReferenceEntries markerBytes entries →
      ∃ value, (bucket.fst, value) ∈ entries ∧
        bucket.snd = immutableReferencesForMarker markerBytes value
  | [], bucket, hMem => by simp [immutableReferenceEntries] at hMem
  | (name, value) :: rest, bucket, hMem => by
      rw [immutableReferenceEntries] at hMem
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · exact ⟨value, List.mem_cons_self .., rfl⟩
      · obtain ⟨v, hv, hEq⟩ := mem_immutableReferenceEntries_elim hMem'
        exact ⟨v, List.mem_cons_of_mem _ hv, hEq⟩

theorem immutableReferenceEntries_inBounds {markerBytes : List UInt8}
    {entries : List (Name × Word)} :
    ∀ e ∈ immutableReferenceEntries markerBytes entries, ∀ r ∈ e.snd,
      r.start + 32 ≤ markerBytes.length := by
  intro e he r hr
  obtain ⟨value, _hVal, hRefs⟩ := mem_immutableReferenceEntries_elim he
  rw [hRefs] at hr
  have hStarts := mem_immutableReferencesForMarker_startsWithAt hr
  have hLen := length_le_of_startsWithAt
    (by rw [Assembly.Bytecode.encodeWord32_length]; omega) hStarts
  rw [Assembly.Bytecode.encodeWord32_length] at hLen
  exact hLen

/-- When the zero-window filter passes at every marker occurrence, the
zero-filtered export equals the marker-only export. -/
theorem immutableReferenceEntriesFromCodes_eq_of_zeroBase
    {zeroBytes markerBytes : List UInt8} :
    ∀ {entries : List (Name × Word)},
      (∀ e ∈ entries, ∀ p ∈ findOccurrences
          (Assembly.Bytecode.encodeWord32 e.snd) markerBytes,
        startsWithAt zeroWord32 zeroBytes p = true) →
      immutableReferenceEntriesFromCodes zeroBytes markerBytes entries =
        immutableReferenceEntries markerBytes entries
  | [], _hZero => rfl
  | (name, value) :: rest, hZero => by
      rw [immutableReferenceEntriesFromCodes, immutableReferenceEntries,
        immutableReferenceEntriesFromCodes_eq_of_zeroBase
          (fun e he => hZero e (List.mem_cons_of_mem _ he))]
      unfold immutableReferencesForMarkerFromCodes
        immutableReferencesForMarker
      rw [List.filter_eq_self.mpr
        (fun p hp => hZero (name, value) (List.mem_cons_self ..) p hp)]

theorem startsWithAt_zeroWord32_of_all_zero {bytes : List UInt8}
    {start : Nat} (hLen : start + 32 ≤ bytes.length)
    (hZero : ∀ p, start ≤ p → p < start + 32 → bytes[p]? = some 0) :
    startsWithAt zeroWord32 bytes start = true := by
  have hZLen : zeroWord32.length = 32 := by
    rw [zeroWord32_eq_replicate]; simp
  suffices h : (bytes.drop start).take zeroWord32.length = zeroWord32 by
    unfold startsWithAt
    rw [h]
    simp
  rw [hZLen, zeroWord32_eq_replicate]
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 32
  · rw [List.getElem?_take_of_lt hk, List.getElem?_drop,
      hZero (start + k) (by omega) (by omega),
      List.getElem?_replicate, if_pos hk]
  · have hLeft : ((bytes.drop start).take 32)[k]? = none := by
      apply List.getElem?_eq_none
      simp
      omega
    have hRight : (List.replicate 32 (0 : UInt8))[k]? = none := by
      apply List.getElem?_eq_none
      simp
      omega
    rw [hLeft, hRight]

/-! ### Patching a code prefix commutes with payload suffixes -/

theorem patchBytesAt_append {start : Nat}
    {replacement bytes suffix : List UInt8}
    (hIn : start + replacement.length ≤ bytes.length) :
    patchBytesAt start replacement (bytes ++ suffix) =
      patchBytesAt start replacement bytes ++ suffix := by
  unfold patchBytesAt
  rw [List.take_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega)]
  simp [List.append_assoc]

theorem patchImmutableReferences_append {value : Word} :
    ∀ {references : List ImmutableReference} {bytes suffix : List UInt8},
      (∀ r ∈ references, r.start + 32 ≤ bytes.length) →
      patchImmutableReferences value (bytes ++ suffix) references =
        patchImmutableReferences value bytes references ++ suffix
  | [], _bytes, _suffix, _hIn => rfl
  | reference :: rest, bytes, suffix, hIn => by
      have hHead : reference.start + 32 ≤ bytes.length :=
        hIn reference (List.mem_cons_self ..)
      have hEnc : (Assembly.Bytecode.encodeWord32 value).length = 32 :=
        Assembly.Bytecode.encodeWord32_length value
      have hIn' : reference.start +
          (Assembly.Bytecode.encodeWord32 value).length ≤ bytes.length := by
        rw [hEnc]; omega
      have hLen := patchBytesAt_length hIn'
      rw [patchImmutableReferences, patchBytesAt_append hIn',
        patchImmutableReferences_append (fun r hr => by
          rw [hLen]; exact hIn r (List.mem_cons_of_mem _ hr)),
        patchImmutableReferences]

theorem patchImmutables_append {values : List (Name × Word)} :
    ∀ {refs : List (Name × List ImmutableReference)}
      {bytes suffix : List UInt8},
      (∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ bytes.length) →
      patchImmutables (bytes ++ suffix) refs values =
        patchImmutables bytes refs values ++ suffix
  | [], _bytes, _suffix, _hIn => rfl
  | (name, references) :: rest, bytes, suffix, hIn => by
      have hHead : ∀ r ∈ references, r.start + 32 ≤ bytes.length :=
        hIn (name, references) (List.mem_cons_self ..)
      cases hFind : values.find? (fun entry => entry.fst == name) with
      | none =>
          rw [patchImmutables, hFind, patchImmutables_append
            (fun e he => hIn e (List.mem_cons_of_mem _ he)), patchImmutables,
            hFind]
      | some entry =>
          have hLen := patchImmutableReferences_length (value := entry.snd)
            (references := references) (bytes := bytes) hHead
          simp only [patchImmutables, hFind]
          rw [patchImmutableReferences_append hHead,
            patchImmutables_append (fun e he r hr => by
              rw [hLen]; exact hIn e (List.mem_cons_of_mem _ he) r hr)]

/-- Exported reference windows are in bounds of the zero-compile bytes. -/
theorem immutableReferenceEntriesFromCodes_inBounds_zero
    {zeroBytes markerBytes : List UInt8} {entries : List (Name × Word)} :
    ∀ e ∈ immutableReferenceEntriesFromCodes zeroBytes markerBytes entries,
      ∀ r ∈ e.snd, r.start + 32 ≤ zeroBytes.length := by
  intro e he r hr
  obtain ⟨value, _hv, hRefs⟩ :=
    mem_immutableReferenceEntriesFromCodes_elim he
  rw [hRefs] at hr
  obtain ⟨_hMarker, hZero, _hLen⟩ :=
    mem_immutableReferencesForMarkerFromCodes_facts hr
  have hzl : zeroWord32.length = 32 := by
    rw [zeroWord32_eq_replicate]; simp
  have hBound := length_le_of_startsWithAt (by rw [hzl]; omega) hZero
  rw [hzl] at hBound
  exact hBound

end Bytecode

/-! ### Marker and zero entry plumbing -/

theorem ImmutableReference.markerEntriesFromNat_map_fst :
    ∀ (index : Nat) (names : List Name),
      (ImmutableReference.markerEntriesFromNat index names).map Prod.fst =
        names
  | _index, [] => rfl
  | index, _name :: rest => by
      simp [ImmutableReference.markerEntriesFromNat,
        ImmutableReference.markerEntriesFromNat_map_fst (index + 1) rest]

theorem ImmutableReference.zeroEntries_snd :
    ∀ {names : List Name} {e : Name × Word},
      e ∈ ImmutableReference.zeroEntries names →
      e.snd = EvmYul.UInt256.ofNat 0
  | [], _e, hMem => by simp [ImmutableReference.zeroEntries] at hMem
  | _name :: rest, e, hMem => by
      rw [ImmutableReference.zeroEntries] at hMem
      rcases List.mem_cons.mp hMem with rfl | hMem'
      · rfl
      · exact ImmutableReference.zeroEntries_snd hMem'

theorem ImmutableReference.zeroEntries_find?_isSome :
    ∀ {names : List Name} {name : Name}, name ∈ names →
      ((ImmutableReference.zeroEntries names).find?
        (fun e => e.fst == name)).isSome
  | [], _name, hMem => by simp at hMem
  | n :: rest, name, hMem => by
      rw [ImmutableReference.zeroEntries]
      by_cases hEq : (n == name) = true
      · simp [List.find?_cons, hEq]
      · rcases List.mem_cons.mp hMem with rfl | hMem'
        · simp at hEq
        · simp only [List.find?_cons, hEq]
          exact ImmutableReference.zeroEntries_find?_isSome hMem'

/-! ### Gate extraction -/

theorem Object.immutablePatchChecked?_none_elim
    {object : Object} {context : ObjectBuiltinContext}
    {plan : Object.ImmutablePushPlan} {bytes markerBytes : List UInt8}
    (hTarget : plan.markerTarget? = none)
    (hGate : object.immutablePatchChecked? context plan bytes markerBytes =
      true) :
    object.loadImmutableNames = [] ∧ context.immutableValues = [] := by
  unfold Object.immutablePatchChecked? at hGate
  rw [hTarget] at hGate
  simpa using hGate

theorem Object.immutablePatchChecked?_some_elim
    {object : Object} {context : ObjectBuiltinContext}
    {plan : Object.ImmutablePushPlan} {bytes markerBytes : List UInt8}
    {markerTarget : Assembly.Program}
    (hTarget : plan.markerTarget? = some markerTarget)
    (hGate : object.immutablePatchChecked? context plan bytes markerBytes =
      true) :
    plan.pinnedPushPcs =
      Object.markerPushPcs
        ((ImmutableReference.markerEntriesFromNat 0
          object.loadImmutableNames).map Prod.snd) markerTarget ∧
    (∀ name ∈ object.loadImmutableNames,
      (context.immutableValues.find? fun entry =>
        entry.fst == name).isSome = true) ∧
    Bytecode.patchImmutables markerBytes
        (Bytecode.immutableReferenceEntries markerBytes
          (ImmutableReference.markerEntriesFromNat 0
            object.loadImmutableNames))
        context.immutableValues = bytes := by
  unfold Object.immutablePatchChecked? at hGate
  rw [hTarget] at hGate
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hGate
  exact ⟨hGate.1.1, fun name h => hGate.1.2 name h, hGate.2⟩

/-! ### Push-plan extraction -/

private theorem immutablePushPlanFor?_nilNames
    {object : Object} {context : ObjectBuiltinContext}
    {actual : Assembly.Program} {plan : Object.ImmutablePushPlan}
    (hNames : object.loadImmutableNames = [])
    (hPlan : object.immutablePushPlanFor? context actual = some plan) :
    plan = { pinnedPushPcs := [], markerTarget? := none } := by
  unfold Object.immutablePushPlanFor? at hPlan
  rw [hNames] at hPlan
  simp only [Option.some.injEq] at hPlan
  exact hPlan.symm

private theorem immutablePushPlanFor?_marker_chain
    {object : Object} {context : ObjectBuiltinContext}
    {actual : Assembly.Program} {plan : Object.ImmutablePushPlan}
    {markerTarget : Assembly.Program}
    (hPlan : object.immutablePushPlanFor? context actual = some plan)
    (hTarget : plan.markerTarget? = some markerTarget) :
    Assembly.Compact.differingPushPcs? actual markerTarget =
        some plan.pinnedPushPcs ∧
      ∃ resolved ordered lower compiledMarker,
        object.resolveObjectBuiltinsIn?
            { context with
              immutableValues :=
                ImmutableReference.markerEntriesFromNat 0
                  object.loadImmutableNames } = some resolved ∧
        resolved.toSolcYulOrderedProgram? = some ordered ∧
        ordered.toObjects? = some lower ∧
        Compiler.StackArtifact.compile? lower.toFunctions =
          some compiledMarker ∧
        markerTarget =
          Assembly.MachineBlockDedup.fixedPointOptimize
            compiledMarker.certified.metadata.entry
            compiledMarker.certified.target := by
  unfold Object.immutablePushPlanFor? at hPlan
  dsimp only [] at hPlan
  split at hPlan
  · simp only [Option.some.injEq] at hPlan
    rw [← hPlan] at hTarget
    simp at hTarget
  · split at hPlan
    · simp only [Option.some.injEq] at hPlan
      rw [← hPlan] at hTarget
      simp at hTarget
    · simp only [Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at hPlan
      obtain ⟨resolved, hResolved, hPlan⟩ := hPlan
      obtain ⟨ordered, hOrdered, hPlan⟩ := hPlan
      obtain ⟨lower, hLower, hPlan⟩ := hPlan
      obtain ⟨compiled, hCompiled, hPlan⟩ := hPlan
      obtain ⟨pins, hPins, hPlan⟩ := hPlan
      simp only [Option.some.injEq] at hPlan
      rw [← hPlan] at hTarget ⊢
      simp only [Option.some.injEq] at hTarget
      subst hTarget
      exact ⟨hPins, resolved, ordered, lower, compiled, hResolved,
        hOrdered, hLower, hCompiled, rfl⟩

/-! ### The unconditional endpoint -/

/-- **Deploy-time patching is the value compile, unconditionally.**  Given
only two compile-success hypotheses — the base compile with the zero
immutable values (exactly what the checked object pipeline runs) and a
compile with arbitrary deploy `values` — patching the base bytes at the
exported immutable references with `values` reproduces the value compile's
bytes exactly.  Every other hypothesis of
`Object.patchImmutables_compileWithImmutableValues?` is discharged by the
`immutablePatchChecked?` compile gate. -/
theorem Object.patchImmutables_compileWithImmutableValues?_ofCompile
    {object : Object} {context : ObjectBuiltinContext}
    {values : List (Name × Word)}
    {base withValues : VerifiedStackCodeArtifact}
    (hBase : object.compileVerifiedStackCodeArtifactWithImmutableValues?
      context (ImmutableReference.zeroEntries object.loadImmutableNames) =
        some base)
    (hValues : object.compileVerifiedStackCodeArtifactWithImmutableValues?
      context values = some withValues) :
    Bytecode.patchImmutables base.bytes
      (Bytecode.immutableReferenceEntriesFromCodes base.bytes
        base.immutableMarkerBytes
        (ImmutableReference.markerEntriesFromNat 0
          object.loadImmutableNames))
      values = withValues.bytes := by
  unfold Object.compileVerifiedStackCodeArtifactWithImmutableValues?
    at hBase hValues
  obtain ⟨_, _, _, _, planB, hPlanB, _, _, hMarkerB, hGateB⟩ :=
    compileVerifiedStackCodeArtifactIn?_partsChecked hBase
  obtain ⟨_, _, _, _, planV, hPlanV, _, _, hMarkerV, hGateV⟩ :=
    compileVerifiedStackCodeArtifactIn?_partsChecked hValues
  by_cases hNs : object.loadImmutableNames = []
  · have hPlanVNil := immutablePushPlanFor?_nilNames hNs hPlanV
    have hNoneV : planV.markerTarget? = none := by
      rw [hPlanVNil]
    have hVEmpty :=
      (Object.immutablePatchChecked?_none_elim hNoneV hGateV).2
    dsimp only at hVEmpty
    have hCtxEq :
        ({ context with
            immutableValues :=
              ImmutableReference.zeroEntries object.loadImmutableNames } :
          ObjectBuiltinContext) =
        { context with immutableValues := values } := by
      rw [hNs, hVEmpty]
      rfl
    rw [hCtxEq] at hBase
    have hSame : base = withValues :=
      Option.some.inj (hBase.symm.trans hValues)
    rw [hNs]
    simp [ImmutableReference.markerEntriesFromNat,
      Bytecode.immutableReferenceEntriesFromCodes,
      Bytecode.patchImmutables, hSame]
  · have hNsNe : object.loadImmutableNames ≠ [] := hNs
    cases hTgtB : planB.markerTarget? with
      | none =>
          exact absurd
            (Object.immutablePatchChecked?_none_elim hTgtB hGateB).1 hNsNe
      | some mtB =>
      cases hTgtV : planV.markerTarget? with
      | none =>
          exact absurd
            (Object.immutablePatchChecked?_none_elim hTgtV hGateV).1 hNsNe
      | some mtV =>
      obtain ⟨_hDiffB, resolvedB, orderedB, lowerB, compiledMB,
          hResB, hOrdB, hLowB, hCompB, hMtB⟩ :=
        immutablePushPlanFor?_marker_chain hPlanB hTgtB
      obtain ⟨_hDiffV, resolvedV, orderedV, lowerV, compiledMV,
          hResV, hOrdV, hLowV, hCompV, hMtV⟩ :=
        immutablePushPlanFor?_marker_chain hPlanV hTgtV
      -- Both marker contexts are the same record, so the marker chains agree.
      have hCtxMarker :
          ({ { context with
                immutableValues :=
                  ImmutableReference.zeroEntries object.loadImmutableNames }
              with
              immutableValues :=
                ImmutableReference.markerEntriesFromNat 0
                  object.loadImmutableNames } : ObjectBuiltinContext) =
          { { context with immutableValues := values } with
              immutableValues :=
                ImmutableReference.markerEntriesFromNat 0
                  object.loadImmutableNames } := rfl
      rw [hCtxMarker] at hResB
      have hResEq : resolvedB = resolvedV :=
        Option.some.inj (hResB.symm.trans hResV)
      subst hResEq
      have hOrdEq : orderedB = orderedV :=
        Option.some.inj (hOrdB.symm.trans hOrdV)
      subst hOrdEq
      have hLowEq : lowerB = lowerV :=
        Option.some.inj (hLowB.symm.trans hLowV)
      subst hLowEq
      have hCompEq : compiledMB = compiledMV :=
        Option.some.inj (hCompB.symm.trans hCompV)
      subst hCompEq
      have hMtEq : mtB = mtV := by
        rw [hMtB, hMtV]
      -- Gate facts for both compiles.
      obtain ⟨hPinsB, _hBoundB, hPatchB⟩ :=
        Object.immutablePatchChecked?_some_elim hTgtB hGateB
      obtain ⟨hPinsV, hBoundV, hPatchV⟩ :=
        Object.immutablePatchChecked?_some_elim hTgtV hGateV
      dsimp only at hPatchB hPatchV hBoundV
      have hPinsEq : planB.pinnedPushPcs = planV.pinnedPushPcs := by
        rw [hPinsB, hPinsV, hMtEq]
      -- The two marker compiles coincide.
      rcases compileImmutableMarkerBytes?_elim hMarkerB with
        ⟨hNoneB, _⟩ | ⟨mtB', mcB, hTgtB', hCompactMB, hBytesMB⟩
      · rw [hNoneB] at hTgtB
        cases hTgtB
      rcases compileImmutableMarkerBytes?_elim hMarkerV with
        ⟨hNoneV, _⟩ | ⟨mtV', mcV, hTgtV', hCompactMV, hBytesMV⟩
      · rw [hNoneV] at hTgtV
        cases hTgtV
      have hMtB' : mtB' = mtB :=
        Option.some.inj (hTgtB'.symm.trans hTgtB)
      have hMtV' : mtV' = mtV :=
        Option.some.inj (hTgtV'.symm.trans hTgtV)
      rw [hMtB', hMtEq] at hCompactMB
      rw [hMtV'] at hCompactMV
      rw [hPinsEq] at hCompactMB
      have hMcEq : mcB = mcV :=
        Option.some.inj (hCompactMB.symm.trans hCompactMV)
      have hMEq : withValues.immutableMarkerBytes =
          base.immutableMarkerBytes := by
        rw [hBytesMV, hBytesMB, hMcEq]
      rw [hMEq] at hPatchV
      -- Abbreviations.
      set M := base.immutableMarkerBytes with hM
      set entries := ImmutableReference.markerEntriesFromNat 0
        object.loadImmutableNames with hEntries
      set refsM := Bytecode.immutableReferenceEntries M entries with hRefsM
      -- Window bounds and lengths.
      have hInM : ∀ e ∈ refsM, ∀ r ∈ e.snd, r.start + 32 ≤ M.length :=
        Bytecode.immutableReferenceEntries_inBounds
      have hLenBase : base.bytes.length = M.length := by
        rw [← hPatchB]
        exact Bytecode.patchImmutables_length hInM
      -- Every reference-group name is an immutable name.
      have hFstMem : ∀ e ∈ refsM, e.fst ∈ object.loadImmutableNames := by
        intro e he
        obtain ⟨v, hv, _⟩ := Bytecode.mem_immutableReferenceEntries_elim he
        have hMem : e.fst ∈ entries.map Prod.fst :=
          List.mem_map.mpr ⟨(e.fst, v), hv, rfl⟩
        rwa [hEntries, ImmutableReference.markerEntriesFromNat_map_fst]
          at hMem
      have hBoundZero : ∀ e ∈ refsM,
          ((ImmutableReference.zeroEntries object.loadImmutableNames).find?
            (fun v => v.fst == e.fst)).isSome :=
        fun e he => ImmutableReference.zeroEntries_find?_isSome (hFstMem e he)
      have hBoundVals : ∀ e ∈ refsM,
          (values.find? (fun v => v.fst == e.fst)).isSome :=
        fun e he => hBoundV e.fst (hFstMem e he)
      -- The compiled base agrees with the marker compile outside the windows.
      have hAgree : ∀ p, base.bytes[p]? = M[p]? ∨
          Bytecode.CoveredByRefs refsM p := by
        intro p
        by_cases hCov : Bytecode.CoveredByRefs refsM p
        · exact Or.inr hCov
        · left
          rw [← hPatchB]
          exact Bytecode.patchImmutables_getElem?_notCovered hInM hCov
      -- The base carries the zero word at every exported window, so the
      -- zero-filtered export equals the marker-only export.
      have hZeroSites : ∀ e ∈ entries, ∀ p ∈ Bytecode.findOccurrences
          (Assembly.Bytecode.encodeWord32 e.snd) M,
          Bytecode.startsWithAt Bytecode.zeroWord32 base.bytes p = true := by
        intro e he p hp
        have hRef :
            (⟨p, ImmutableReference.patchLength⟩ : ImmutableReference) ∈
              Bytecode.immutableReferencesForMarker M e.snd :=
          List.mem_map.mpr ⟨p, hp, rfl⟩
        have hBucket := Bytecode.mem_immutableReferenceEntries
          (markerBytes := M) he
        have hStarts :=
          Bytecode.mem_immutableReferencesForMarker_startsWithAt hRef
        have hpLen : p + 32 ≤ M.length := by
          have := Bytecode.length_le_of_startsWithAt
            (by rw [Assembly.Bytecode.encodeWord32_length]; omega) hStarts
          rw [Assembly.Bytecode.encodeWord32_length] at this
          exact this
        apply Bytecode.startsWithAt_zeroWord32_of_all_zero
          (by rw [hLenBase]; exact hpLen)
        intro q hq1 hq2
        rw [← hPatchB]
        apply Bytecode.patchImmutables_getElem?_zero
          (fun e' he' => ImmutableReference.zeroEntries_snd he')
          hInM hBoundZero
        left
        exact ⟨(e.fst, Bytecode.immutableReferencesForMarker M e.snd),
          hBucket,
          ⟨⟨p, ImmutableReference.patchLength⟩, hRef,
            by constructor <;> omega⟩⟩
      have hRefsEq : Bytecode.immutableReferenceEntriesFromCodes base.bytes
          M entries = refsM :=
        Bytecode.immutableReferenceEntriesFromCodes_eq_of_zeroBase hZeroSites
      -- Assemble.
      calc
        Bytecode.patchImmutables base.bytes
            (Bytecode.immutableReferenceEntriesFromCodes base.bytes M
              entries) values
            = Bytecode.patchImmutables base.bytes refsM values := by
              rw [hRefsEq]
        _ = Bytecode.patchImmutables M refsM values :=
              Bytecode.patchImmutables_congr hLenBase
                (fun e he r hr => by
                  rw [hLenBase]; exact hInM e he r hr)
                hBoundVals hAgree
        _ = withValues.bytes := hPatchV

/-! ### Image-level lift -/

private theorem stabilizeObjectCodeBaseArtifact?_context_immutableValues
    {α : Type}
    {object : Object} {linkerSymbols : List (Name × Word)}
    {childImages : List ObjectImage}
    {childImmutableReferences : List (Name × List ImmutableReference)}
    {immutableValues dataSizes : List (Name × Word)}
    {items : List ObjectItemRef} {payload : List UInt8}
    {compileArtifactIn? : ObjectBuiltinContext → Option α}
    {artifactBytes : α → List UInt8}
    {fuel candidate : Nat} {plan : Object.ObjectCodeBasePlan} {artifact : α}
    (hStabilize :
      Object.stabilizeObjectCodeBaseArtifact? object linkerSymbols
        childImages childImmutableReferences immutableValues dataSizes items
        payload compileArtifactIn? artifactBytes fuel candidate =
          some (plan, artifact)) :
    plan.context.immutableValues = immutableValues := by
  induction fuel generalizing candidate with
  | zero =>
      unfold Object.stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, _hLayout, hAfterLayout⟩ :=
        Option.bind_eq_some_iff.mp hStabilize
      obtain ⟨dataOffsets, _hOffsets, hAfterOffsets⟩ :=
        Option.bind_eq_some_iff.mp hAfterLayout
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      change (if (!context.objectDataNamesUnique?) = true then none else
        (compileArtifactIn? context).bind fun compiled =>
          if ((artifactBytes compiled).length == candidate) = true then
            some
              ({ codeBase := candidate, layout, dataOffsets, context },
                compiled)
          else none) = some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, _hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context },
                  compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          rfl
        · simp [hLength] at hAfterCompiled
      · simp [hUnique] at hAfterOffsets
  | succ fuel ih =>
      unfold Object.stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, _hLayout, hAfterLayout⟩ :=
        Option.bind_eq_some_iff.mp hStabilize
      obtain ⟨dataOffsets, _hOffsets, hAfterOffsets⟩ :=
        Option.bind_eq_some_iff.mp hAfterLayout
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      change (if (!context.objectDataNamesUnique?) = true then none else
        (compileArtifactIn? context).bind fun compiled =>
          if ((artifactBytes compiled).length == candidate) = true then
            some
              ({ codeBase := candidate, layout, dataOffsets, context },
                compiled)
          else
            Object.stabilizeObjectCodeBaseArtifact? object linkerSymbols
              childImages childImmutableReferences immutableValues dataSizes
              items payload compileArtifactIn? artifactBytes fuel
                (artifactBytes compiled).length) =
          some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, _hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context },
                  compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          rfl
        · simp [hLength] at hAfterCompiled
          exact ih hAfterCompiled
      · simp [hUnique] at hAfterOffsets

private theorem planObjectArtifactFromChildImagesArtifactWith?_context_immutableValues
    {α : Type}
    {object : Object} {linkerSymbols : List (Name × Word)}
    {childImages : List ObjectImage}
    {compileArtifactIn? : ObjectBuiltinContext → Option α}
    {artifactBytes : α → List UInt8}
    {plan : Object.ObjectArtifactPlan} {artifact : α}
    (hPlan :
      Object.planObjectArtifactFromChildImagesArtifactWith? object
        linkerSymbols childImages compileArtifactIn? artifactBytes =
          some (plan, artifact)) :
    plan.context.immutableValues =
      ImmutableReference.zeroEntries object.loadImmutableNames := by
  unfold Object.planObjectArtifactFromChildImagesArtifactWith? at hPlan
  obtain ⟨items, _hItems, hAfterItems⟩ :=
    Option.bind_eq_some_iff.mp hPlan
  obtain ⟨dataSizes, _hDataSizes, hAfterDataSizes⟩ :=
    Option.bind_eq_some_iff.mp hAfterItems
  obtain ⟨payload, _hPayload, hAfterPayload⟩ :=
    Option.bind_eq_some_iff.mp hAfterDataSizes
  obtain ⟨stabilizedArtifact, hStabilized, hAfterStabilized⟩ :=
    Option.bind_eq_some_iff.mp hAfterPayload
  rcases stabilizedArtifact with ⟨stabilized, compiled⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hAfterStabilized
  rcases hAfterStabilized with ⟨hPlanEq, hArtifactEq⟩
  subst plan
  subst artifact
  exact stabilizeObjectCodeBaseArtifact?_context_immutableValues hStabilized

/-- **Deploy-time patching at image level, unconditionally.**  For any
successful object-artifact compile (the exported pipeline itself) and any
successful code compile with deploy `values` in the artifact's own context,
patching the exported image bytes at the artifact's own immutable references
yields the value compile's code bytes followed by the unchanged payload. -/
theorem Object.patchImmutables_image_compileWithImmutableValues?_ofCompile
    {object : Object} {linkerSymbols values : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {withValues : VerifiedStackCodeArtifact}
    (hArtifact : object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
      linkerSymbols = some artifact)
    (hValues : object.compileVerifiedStackCodeArtifactWithImmutableValues?
      artifact.computed.context values = some withValues) :
    Bytecode.patchImmutables artifact.image.bytes
      (Bytecode.immutableReferenceEntriesFromCodes
        artifact.codeArtifact.bytes
        artifact.codeArtifact.immutableMarkerBytes
        (ImmutableReference.markerEntriesFromNat 0
          object.loadImmutableNames))
      values = withValues.bytes ++ artifact.computed.payload := by
  obtain ⟨childArtifacts, plan, codeArtifact, _hChildren, hPlan, _hFinish,
      hCode, _hChildrenEq, hContextEq, _hChildImages, hPayloadEq, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hArtifact
  have hPlanIv : plan.context.immutableValues =
      ImmutableReference.zeroEntries object.loadImmutableNames := by
    unfold Object.planVerifiedStackObjectArtifactFromChildren? at hPlan
    exact
      planObjectArtifactFromChildImagesArtifactWith?_context_immutableValues
        hPlan
  have hCtx : ({ plan.context with
      immutableValues :=
        ImmutableReference.zeroEntries object.loadImmutableNames } :
        ObjectBuiltinContext) = plan.context := by
    rw [← hPlanIv]
  have hBase : object.compileVerifiedStackCodeArtifactWithImmutableValues?
      plan.context
      (ImmutableReference.zeroEntries object.loadImmutableNames) =
      some artifact.codeArtifact := by
    unfold Object.compileVerifiedStackCodeArtifactWithImmutableValues?
    rw [hCtx]
    exact hCode
  rw [hContextEq] at hValues
  have hPatchCode :=
    Object.patchImmutables_compileWithImmutableValues?_ofCompile hBase
      hValues
  have hInCode := Bytecode.immutableReferenceEntriesFromCodes_inBounds_zero
    (zeroBytes := artifact.codeArtifact.bytes)
    (markerBytes := artifact.codeArtifact.immutableMarkerBytes)
    (entries := ImmutableReference.markerEntriesFromNat 0
      object.loadImmutableNames)
  rw [hImage, hPayloadEq, Bytecode.patchImmutables_append hInCode,
    hPatchCode]

end Frontend
end Solidity
end EvmCompiler

-- Sanity: proof-hole-free; #print axioms stays within [propext, Classical.choice, Quot.sound].
#print axioms
  EvmCompiler.Solidity.Frontend.Bytecode.patchImmutables_eq_target
#print axioms
  EvmCompiler.Solidity.Frontend.Bytecode.patchImmutables_markerBytes_of_byteDiff
#print axioms
  EvmCompiler.Solidity.Frontend.compile?_byteDiff_of_differingPushPcs
#print axioms
  EvmCompiler.Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_byteDiff
#print axioms
  EvmCompiler.Solidity.Frontend.Bytecode.patchImmutables_valueBytes_of_byteDiffs
#print axioms
  EvmCompiler.Solidity.Frontend.Object.patchImmutables_compileWithImmutableValues?
#print axioms
  EvmCompiler.Solidity.Frontend.Object.patchImmutables_compileWithImmutableValues?_ofCompile
#print axioms
  EvmCompiler.Solidity.Frontend.Object.patchImmutables_image_compileWithImmutableValues?_ofCompile
