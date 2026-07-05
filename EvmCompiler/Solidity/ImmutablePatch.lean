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

/-! ## The patcher -/

/-- Patch one immutable value into every exported reference site. -/
def patchImmutableReferences (value : Word) :
    List UInt8 → List ImmutableReference → List UInt8
  | bytes, [] => bytes
  | bytes, reference :: rest =>
      patchImmutableReferences value
        (patchBytesAt reference.start (Assembly.Bytecode.encodeWord32 value)
          bytes) rest

/-- Patch deploy-time immutable `values` into `bytes` at the exported
`refs` (the shape of `ObjectImage.immutableReferences`).  Mirrors
`zeroImmutableReferenceEntries`, writing the value assigned to each name
instead of the zero word.  Reference groups whose name carries no assigned
value are left untouched. -/
def patchImmutables (bytes : List UInt8)
    (refs : List (Name × List ImmutableReference))
    (values : List (Name × Word)) : List UInt8 :=
  match refs with
  | [] => bytes
  | (name, references) :: rest =>
      match values.find? (fun entry => entry.fst == name) with
      | some entry =>
          patchImmutables (patchImmutableReferences entry.snd bytes references)
            rest values
      | none => patchImmutables bytes rest values

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
    {pins : List Nat} {bw : Nat}
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

private theorem branchWidthFor?_eq_of_pushDiffSites
    {pins : List Nat}
    {a b : Assembly.Program} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b 0 sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    Assembly.Compact.branchWidthFor? pins b =
      Assembly.Compact.branchWidthFor? pins a := by
  unfold Assembly.Compact.branchWidthFor?
  have hFits : (fun width => Assembly.Compact.branchWidthFits? pins b width) =
      (fun width => Assembly.Compact.branchWidthFits? pins a width) := by
    funext width
    unfold Assembly.Compact.branchWidthFits? Assembly.Compact.layout?
    rw [layoutRev?_eq_of_pushDiffSites h hPins 0 []]
  rw [hFits]

private theorem layout?_eq_of_pushDiffSites
    {pins : List Nat} {bw : Nat}
    {a b : Assembly.Program} {sites : List (Nat × Word × Word)}
    (h : PushDiffSites a b 0 sites)
    (hPins : ∀ s ∈ sites, s.1 ∈ pins) :
    Assembly.Compact.layout? pins b bw = Assembly.Compact.layout? pins a bw :=
  layoutRev?_eq_of_pushDiffSites h hPins 0 []

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
    {pins : List Nat} {bw : Nat} {table : Assembly.Compact.LabelTable}
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
          hMem]
      have hCodeB : Assembly.Compact.emitSourceBlock? pins bw spc' cpc table
          (.push vb) = some [{ pc := cpc, instr := .push 32 vb }] := by
        simp [Assembly.Compact.emitSourceBlock?,
          Assembly.Compact.emitInstrRev?, Assembly.Compact.pushWidthAt?,
          hMem]
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
          cases hWidth : Assembly.Compact.branchWidthFor? pins
              (Assembly.Compact.prepare source) with
          | none => simp [hWidth] at hCompile
          | some branchWidth =>
              simp [hWidth] at hCompile
              cases hLayout : Assembly.Compact.layout? pins
                  (Assembly.Compact.prepare source) branchWidth with
              | none => simp [hLayout] at hCompile
              | some layoutResult =>
                  cases layoutResult with
                  | mk labels codeLength =>
                      simp [hLayout] at hCompile
                      cases hEmit : Assembly.Compact.emit? pins
                          (Assembly.Compact.prepare source) branchWidth
                          labels with
                      | none => simp [hEmit] at hCompile
                      | some program =>
                          simp [hEmit] at hCompile
                          cases hBlocks : Assembly.Compact.emitBlocks? pins
                              (Assembly.Compact.prepare source) branchWidth
                              labels with
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
  -- Both compiles select the same branch width.
  have hWidthA := hValidA.selectedBranchWidth
  have hWidthB := hValidB.selectedBranchWidth
  rw [hPinsA, hValidA.physicalSource] at hWidthA
  rw [hPinsB, hValidB.physicalSource] at hWidthB
  have hWidthEq : Assembly.Compact.branchWidthFor? pins
      (Assembly.Compact.prepare sourceB) =
      Assembly.Compact.branchWidthFor? pins
        (Assembly.Compact.prepare sourceA) :=
    branchWidthFor?_eq_of_pushDiffSites hSites hPinsSites
  have hSameWidth : cb.branchWidth = ca.branchWidth := by
    rw [hWidthEq, hWidthA] at hWidthB
    exact (Option.some.inj hWidthB).symm
  -- Both compiles produce the same label table.
  have hLayoutA := hValidA.layout
  have hLayoutB := hValidB.layout
  rw [hPinsA, hValidA.physicalSource] at hLayoutA
  rw [hPinsB, hValidB.physicalSource, hSameWidth] at hLayoutB
  rw [layout?_eq_of_pushDiffSites hSites hPinsSites, hLayoutA] at hLayoutB
  have hLabelsEq : cb.labels = ca.labels := by
    have hPair := Option.some.inj hLayoutB
    exact (congrArg Prod.fst hPair).symm
  -- Compare the emitted blocks.
  have hBlocksA := hValidA.blocks
  have hBlocksB := hValidB.blocks
  rw [hPinsA, hValidA.physicalSource] at hBlocksA
  rw [hPinsB, hValidB.physicalSource, hSameWidth, hLabelsEq] at hBlocksB
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
