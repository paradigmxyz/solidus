import EvmCompiler.Solidity.VerifiedStackObjectArtifact

/-!
# Creation → runtime image embedding

The supported entry point
`Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?` compiles child
objects recursively and appends their verified images verbatim into the parent
payload (`finishVerifiedStackObjectArtifact?` proves
`artifact.image.bytes = codeArtifact.bytes ++ plan.payload`).  This file turns
that structural fact into a single named public theorem:

* `Object.compileVerifiedStackObjectArtifact_child_image_embedded` — for every
  child object of a compiled object there is a child artifact that (a) is
  itself the result of the same verified compile entry point (so every
  end-to-end theorem instantiates for it), and (b) whose verified image bytes
  appear verbatim inside the parent image at exactly the offset/size the
  object-builtin resolution context records for the child's name.  The
  offset/size are tied to the resolution plan: the same
  `artifact.computed.context` in which the creation code was compiled resolves
  `datasize("<child>")` to the child's image length
  (`ObjectBuiltinContext.size?`, consulted by
  `Expr.resolveObjectBuiltinsIn?` for `datasize`), and its layout witness
  resolves `dataoffset("<child>")` to the embedding offset
  (`ObjectBuiltinContext.offset?` falls through to `layout.offset?` for
  child-object names; see `Frontend.lean`).

* `Object.creationImage_embeds_deployedRuntimeImage` — the specialization to
  the solc shape where the creation object carries the deployed runtime object
  (`<C>` wrapping `<C>_deployed`) as its only child: the deployed runtime
  object's verified image sits verbatim inside the creation image at the
  offset/size that `dataoffset`/`datasize` resolved to, i.e. exactly the bytes
  the constructor's `codecopy`/`return` sequence deploys.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

/-! ## Generic list helpers (self-contained) -/

private theorem take_append_self {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).take l₁.length = l₁ := by
  induction l₁ with
  | nil => simp
  | cons a rest ih => simp [ih]

private theorem drop_append_add {α : Type} (l₁ l₂ : List α) (k : Nat) :
    (l₁ ++ l₂).drop (l₁.length + k) = l₂.drop k := by
  induction l₁ with
  | nil => simp
  | cons a rest ih =>
      simp only [List.cons_append, List.length_cons]
      have hArith : rest.length + 1 + k = (rest.length + k) + 1 := by omega
      rw [hArith, List.drop_succ_cons]
      exact ih

private theorem nodup_append_left {α : Type} :
    ∀ {l₁ l₂ : List α}, (l₁ ++ l₂).Nodup → l₁.Nodup
  | [], _, _ => List.nodup_nil
  | a :: l₁, l₂, h => by
      rw [List.cons_append, List.nodup_cons] at h
      rw [List.nodup_cons]
      exact
        ⟨fun hMem => h.1 (List.mem_append_left _ hMem),
          nodup_append_left h.2⟩

private theorem nodup_append_not_mem {α : Type} :
    ∀ {l₁ l₂ : List α} {a : α}, (l₁ ++ l₂).Nodup → a ∈ l₁ → a ∉ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ a _ hMem; cases hMem
  | cons b l₁ ih =>
      intro l₂ a h hMem
      rw [List.cons_append, List.nodup_cons] at h
      rcases List.mem_cons.mp hMem with hEq | hMemRest
      · subst hEq
        exact fun hRight => h.1 (List.mem_append_right _ hRight)
      · exact ih h.2 hMemRest

private theorem find?_entry_of_nodup :
    ∀ {entries : List ObjectLayout.Entry} {entry : ObjectLayout.Entry},
      (entries.map (fun e => e.name)).Nodup → entry ∈ entries →
      entries.find? (fun e => e.name == entry.name) = some entry := by
  intro entries
  induction entries with
  | nil => intro entry _ hMem; cases hMem
  | cons e rest ih =>
      intro entry hNodup hMem
      rw [List.map_cons, List.nodup_cons] at hNodup
      rcases List.mem_cons.mp hMem with hEq | hMemRest
      · subst hEq
        rw [List.find?_cons_of_pos (by simp)]
      · have hNameMem : entry.name ∈ rest.map (fun e => e.name) :=
          List.mem_map.mpr ⟨entry, hMemRest, rfl⟩
        have hNe : e.name ≠ entry.name := fun hEqName =>
          hNodup.1 (hEqName ▸ hNameMem)
        rw [List.find?_cons_of_neg (by simp [hNe])]
        exact ih hNodup.2 hMemRest

/-! ## `ObjectItemRef` boolean-membership helpers -/

namespace ObjectItemRef

theorem eq_of_beq_true : ∀ {a b : ObjectItemRef}, (a == b) = true → a = b := by
  intro a b h
  cases a <;> cases b <;>
    simp [BEq.beq, instBEqObjectItemRef.beq] at h <;>
    simp [h]

theorem mem_of_contains {x : ObjectItemRef} :
    ∀ {l : List ObjectItemRef}, l.contains x = true → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact Bool.noConfusion h
  | cons a rest ih =>
      intro h
      rw [List.contains_cons] at h
      rcases Bool.or_eq_true_iff.mp h with hHead | hTail
      · exact (eq_of_beq_true hHead) ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hTail)

/-- `payloadBytes?` and `payloadSize?` agree: the recorded item size is the
length of the payload bytes contributed by the item. -/
theorem payloadBytes?_payloadSize?
    {dataSections : List DataSection} {objectImages : List ObjectImage}
    {item : ObjectItemRef} {bytes : List UInt8}
    (hBytes : item.payloadBytes? dataSections objectImages = some bytes) :
    item.payloadSize? dataSections objectImages = some bytes.length := by
  cases item with
  | data index =>
      simp only [payloadBytes?] at hBytes
      cases hSection : dataSections[index]? with
      | none => rw [hSection] at hBytes; simp at hBytes
      | some dataSection =>
          rw [hSection] at hBytes
          obtain ⟨section', hSection', hBytesEq⟩ :=
            Option.bind_eq_some_iff.mp hBytes
          obtain rfl := Option.some.inj hSection'
          obtain rfl := Option.some.inj hBytesEq
          simp [payloadSize?, hSection]
  | object index =>
      simp only [payloadBytes?] at hBytes
      cases hImage : objectImages[index]? with
      | none => rw [hImage] at hBytes; simp at hBytes
      | some image =>
          rw [hImage] at hBytes
          obtain ⟨image', hImage', hBytesEq⟩ :=
            Option.bind_eq_some_iff.mp hBytes
          obtain rfl := Option.some.inj hImage'
          obtain rfl := Option.some.inj hBytesEq
          simp [payloadSize?, hImage, ObjectImage.size]

namespace List

/-- Joint payload/layout walk: an `.object i` item's image bytes appear
verbatim in the payload at some offset `k`, and (for path-component names)
the generated layout carries exactly the entry
`{ name := image.name, offset := base + k, size := image.size }`. -/
theorem payloadBytes?_object_embedded
    {dataSections : List DataSection} {objectImages : List ObjectImage}
    {i : Nat} {image : ObjectImage}
    (hImage : objectImages[i]? = some image) :
    ∀ {items : List ObjectItemRef} {base : Nat} {payload : List UInt8}
      {layout : List ObjectLayout.Entry},
      ObjectItemRef.List.payloadBytes? dataSections objectImages items =
        some payload →
      ObjectItemRef.List.objectLayoutEntriesFromNat? dataSections objectImages
        base items = some layout →
      ObjectItemRef.object i ∈ items →
      ∃ k,
        (payload.drop k).take image.bytes.length = image.bytes ∧
        (Name.objectPathComponent? image.name = true →
          image.layoutEntryFromNat (base + k) ∈ layout) := by
  intro items
  induction items with
  | nil =>
      intro base payload layout _ _ hMem
      cases hMem
  | cons item rest ih =>
      intro base payload layout hPayload hLayout hMem
      simp only [ObjectItemRef.List.payloadBytes?] at hPayload
      obtain ⟨head, hHead, hPayload⟩ := Option.bind_eq_some_iff.mp hPayload
      obtain ⟨tailBytes, hTail, hPayload⟩ :=
        Option.bind_eq_some_iff.mp hPayload
      have hPayloadEq : head ++ tailBytes = payload := by
        simpa using hPayload
      subst hPayloadEq
      simp only [ObjectItemRef.List.objectLayoutEntriesFromNat?] at hLayout
      obtain ⟨itemSize, hSize, hLayout⟩ := Option.bind_eq_some_iff.mp hLayout
      obtain ⟨tailLayout, hTailLayout, hLayout⟩ :=
        Option.bind_eq_some_iff.mp hLayout
      rcases List.mem_cons.mp hMem with hEq | hMemRest
      · -- The head item is our object: it sits at offset 0 of this payload.
        subst hEq
        simp only [ObjectItemRef.payloadBytes?] at hHead
        obtain ⟨imageAt, hImageAt, hHeadEq⟩ :=
          Option.bind_eq_some_iff.mp hHead
        rw [hImage] at hImageAt
        obtain rfl := Option.some.inj hImageAt
        obtain rfl := Option.some.inj hHeadEq
        obtain ⟨imageAt', hImageAt', hLayoutEq⟩ :=
          Option.bind_eq_some_iff.mp hLayout
        rw [hImage] at hImageAt'
        obtain rfl := Option.some.inj hImageAt'
        obtain rfl := Option.some.inj hLayoutEq
        refine ⟨0, ?_, ?_⟩
        · simp [take_append_self image.bytes tailBytes]
        · intro hPath
          rw [Nat.add_zero]
          exact List.mem_append_left _
            (by simp [ObjectImage.layoutEntriesFromNatForPath, hPath,
              List.mem_cons])
      · -- The object sits in the tail; shift by the head item's size.
        have hLen : itemSize = head.length := by
          have hSizeLen := payloadBytes?_payloadSize? hHead
          rw [hSizeLen] at hSize
          exact (Option.some.inj hSize).symm
        obtain ⟨k, hTake, hEntry⟩ := ih hTail hTailLayout hMemRest
        refine ⟨head.length + k, ?_, ?_⟩
        · rw [drop_append_add]
          exact hTake
        · intro hPath
          have hMemTail := hEntry hPath
          have hArith : base + (head.length + k) = base + itemSize + k := by
            omega
          rw [hArith]
          cases item with
          | data index =>
              simp only [Option.some.injEq] at hLayout
              subst hLayout
              exact hMemTail
          | object index =>
              obtain ⟨imageAt, _hImageAt, hLayout⟩ :=
                Option.bind_eq_some_iff.mp hLayout
              simp only [Option.some.injEq] at hLayout
              subst hLayout
              exact List.mem_append_right _ hMemTail

end List

end ObjectItemRef

namespace Object

private theorem mem_objectsFromNat :
    ∀ {objects : List Object} (start i : Nat), i < objects.length →
      ObjectItemRef.object (start + i) ∈ ItemRef.objectsFromNat start objects
  | [], _, i, h => absurd h (by simp)
  | _object :: rest, start, 0, _h => by
      rw [ItemRef.objectsFromNat]
      exact Nat.add_zero start ▸ List.mem_cons_self ..
  | _object :: rest, start, i + 1, h => by
      rw [ItemRef.objectsFromNat]
      have hTail :=
        mem_objectsFromNat (objects := rest) (start + 1) i (by simpa using h)
      have hArith : start + 1 + i = start + (i + 1) := by omega
      exact List.mem_cons_of_mem _ (hArith ▸ hTail)

/-- Every child object index survives into the planned payload item list. -/
theorem payloadItems?_object_mem
    {object : Object} {objectImages : List ObjectImage}
    {items : List ObjectItemRef} {i : Nat}
    (hItems : object.payloadItems? objectImages = some items)
    (hLt : i < object.objects.length) :
    ObjectItemRef.object i ∈ items := by
  unfold payloadItems? at hItems
  by_cases hValid :
      ObjectItemRef.List.validFor? object.defaultItems object.effectiveItems
  · simp only [hValid, if_true, Option.some.injEq] at hItems
    subst hItems
    have hMemDefault : ObjectItemRef.object i ∈ object.defaultItems := by
      have hMem := mem_objectsFromNat 0 i hLt
      rw [Nat.zero_add] at hMem
      exact List.mem_append_left _ hMem
    have hSame :
        ObjectItemRef.List.sameMembers?
          object.defaultItems object.effectiveItems = true := by
      unfold ObjectItemRef.List.validFor? at hValid
      exact (Bool.and_eq_true_iff.mp hValid).2
    have hContains :
        object.effectiveItems.contains (ObjectItemRef.object i) = true := by
      unfold ObjectItemRef.List.sameMembers? at hSame
      have hAll := (Bool.and_eq_true_iff.mp hSame).1
      exact (List.all_eq_true.mp hAll) _ hMemDefault
    have hMemEffective : ObjectItemRef.object i ∈ object.effectiveItems :=
      ObjectItemRef.mem_of_contains hContains
    unfold ObjectItemRef.List.dropUnnamedData
      ObjectItemRef.List.moveMetadataLast
    -- `dropUnnamedData` filters on `isUnnamedData?`, which is `false` on every
    -- `.object` item by definition, so object indices survive the filter.
    exact List.mem_filter.mpr
      ⟨List.mem_append_left _
          (List.mem_filter.mpr
            ⟨hMemEffective, by simp [ObjectItemRef.isMetadata?]⟩),
        by simp [ObjectItemRef.isUnnamedData?]⟩
  · simp [hValid] at hItems

/-- The stabilized code-base plan records the layout generated at the final
code base, exposes it as the resolution context's layout witness, and passed
the object-data-name uniqueness gate. -/
theorem stabilizeObjectCodeBaseArtifact?_layout {α : Type}
    (object : Object) (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (childImmutableReferences : List (Name × List ImmutableReference))
    (immutableValues : List (Name × Word))
    (dataSizes : List (Name × Word)) (items : List ObjectItemRef)
    (payload : List UInt8)
    (compileArtifactIn? : ObjectBuiltinContext → Option α)
    (artifactBytes : α → List UInt8)
    {fuel candidate : Nat} {plan : ObjectCodeBasePlan} {artifact : α}
    (hStabilize :
      stabilizeObjectCodeBaseArtifact? object linkerSymbols childImages
        childImmutableReferences immutableValues dataSizes items payload
        compileArtifactIn? artifactBytes fuel candidate =
          some (plan, artifact)) :
    ObjectItemRef.List.objectLayoutEntriesFromNat?
        object.data childImages plan.codeBase items = some plan.layout ∧
      plan.context.layout = { entries := plan.layout } ∧
      plan.context.objectDataNamesUnique? = true := by
  induction fuel generalizing candidate with
  | zero =>
      unfold stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, hLayout, hAfterLayout⟩ :=
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
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled)
          else none) = some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, _hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          exact ⟨hLayout, rfl, hUnique⟩
        · simp [hLength] at hAfterCompiled
      · simp [hUnique] at hAfterOffsets
  | succ fuel ih =>
      unfold stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, hLayout, hAfterLayout⟩ :=
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
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled)
          else
            stabilizeObjectCodeBaseArtifact? object linkerSymbols childImages
              childImmutableReferences immutableValues dataSizes items payload
              compileArtifactIn? artifactBytes fuel
                (artifactBytes compiled).length) =
          some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, _hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context }, compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          exact ⟨hLayout, rfl, hUnique⟩
        · simp [hLength] at hAfterCompiled
          exact ih hAfterCompiled
      · simp [hUnique] at hAfterOffsets

/-- Structural facts recorded by the artifact planner: the plan's item list,
payload bytes, and layout are exactly the ones generated from the child
images, and the resolution context exposes the plan layout. -/
theorem planObjectArtifactFromChildImagesArtifactWith?_layout {α : Type}
    (object : Object) (linkerSymbols : List (Name × Word))
    (childImages : List ObjectImage)
    (compileArtifactIn? : ObjectBuiltinContext → Option α)
    (artifactBytes : α → List UInt8)
    {plan : ObjectArtifactPlan} {artifact : α}
    (hPlan :
      planObjectArtifactFromChildImagesArtifactWith? object linkerSymbols
        childImages compileArtifactIn? artifactBytes = some (plan, artifact)) :
    plan.childImages = childImages ∧
      object.payloadItems? childImages = some plan.items ∧
      ObjectItemRef.List.payloadBytes? object.data childImages plan.items =
        some plan.payload ∧
      ObjectItemRef.List.objectLayoutEntriesFromNat? object.data childImages
        plan.codeBase plan.items = some plan.layout ∧
      plan.context.layout = { entries := plan.layout } ∧
      plan.context.objectDataNamesUnique? = true := by
  unfold planObjectArtifactFromChildImagesArtifactWith? at hPlan
  obtain ⟨items, hItems, hAfterItems⟩ :=
    Option.bind_eq_some_iff.mp hPlan
  obtain ⟨dataSizes, _hDataSizes, hAfterDataSizes⟩ :=
    Option.bind_eq_some_iff.mp hAfterItems
  obtain ⟨payload, hPayload, hAfterPayload⟩ :=
    Option.bind_eq_some_iff.mp hAfterDataSizes
  obtain ⟨stabilizedArtifact, hStabilized, hAfterStabilized⟩ :=
    Option.bind_eq_some_iff.mp hAfterPayload
  rcases stabilizedArtifact with ⟨stabilized, compiled⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hAfterStabilized
  rcases hAfterStabilized with ⟨hPlanEq, hArtifactEq⟩
  subst plan
  subst artifact
  have hStabilizedParts :=
    stabilizeObjectCodeBaseArtifact?_layout object linkerSymbols childImages
      (ObjectImage.immutableReferenceEntries childImages)
      (ImmutableReference.zeroEntries object.loadImmutableNames)
      dataSizes items payload compileArtifactIn? artifactBytes hStabilized
  exact
    ⟨rfl, hItems, hPayload, hStabilizedParts.1, hStabilizedParts.2.1,
      hStabilizedParts.2.2⟩

/-- Image-level facts recorded by `finishVerifiedStackObjectArtifact?`:
the image is named after the object, its bytes are code followed by payload,
the code occupies exactly `plan.codeBase` bytes, and the image publishes the
plan layout. -/
theorem finishVerifiedStackObjectArtifact?_image_parts
    {object : Object} {plan : ObjectArtifactPlan}
    {childArtifacts : List VerifiedStackObjectArtifact}
    {codeArtifact : VerifiedStackCodeArtifact}
    {artifact : VerifiedStackObjectArtifact}
    (hFinish :
      object.finishVerifiedStackObjectArtifact? childArtifacts plan
          codeArtifact =
        some artifact) :
    artifact.image.name = object.name ∧
      artifact.image.bytes = codeArtifact.bytes ++ plan.payload ∧
      artifact.image.layoutEntries = plan.layout ∧
      codeArtifact.bytes.length = plan.codeBase ∧
      artifact.children = childArtifacts := by
  unfold finishVerifiedStackObjectArtifact? at hFinish
  cases hCodeLength : codeArtifact.bytes.length == plan.codeBase with
  | false =>
      have hCodeNe : codeArtifact.bytes.length ≠ plan.codeBase := by
        simpa using hCodeLength
      simp [hCodeNe] at hFinish
  | true =>
      have hCodeEq : codeArtifact.bytes.length = plan.codeBase := by
        simpa using hCodeLength
      cases hMarkerLength :
          codeArtifact.immutableMarkerBytes.length == plan.codeBase with
      | false =>
          have hMarkerNe :
              codeArtifact.immutableMarkerBytes.length ≠ plan.codeBase := by
            simpa using hMarkerLength
          simp [hCodeEq, hMarkerNe] at hFinish
      | true =>
          have hMarkerEq :
              codeArtifact.immutableMarkerBytes.length = plan.codeBase := by
            simpa using hMarkerLength
          cases hPayloadReferences :
              ObjectItemRef.List.immutableReferenceEntriesFromNat?
                object.data plan.childImages plan.codeBase plan.items with
          | none =>
              simp [hCodeEq, hMarkerEq, hPayloadReferences] at hFinish
          | some payloadReferences =>
              simp [hCodeEq, hMarkerEq, hPayloadReferences] at hFinish
              subst artifact
              exact ⟨rfl, rfl, rfl, hCodeEq, rfl⟩

/-- Recursive child compiles are recorded index-by-index. -/
theorem List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?_getElem?
    {objects : List Object} {linkerSymbols : List (Name × Word)}
    {artifacts : List VerifiedStackObjectArtifact} {i : Nat}
    {childObject : Object}
    (hCompile :
      List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
          objects linkerSymbols =
        some artifacts)
    (hChild : objects[i]? = some childObject) :
    ∃ childArtifact,
      artifacts[i]? = some childArtifact ∧
      childObject.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols =
        some childArtifact := by
  induction objects generalizing artifacts i with
  | nil => simp at hChild
  | cons object rest ih =>
      unfold List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
        at hCompile
      cases hHead :
          object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
            linkerSymbols with
      | none => simp [hHead] at hCompile
      | some headArtifact =>
          cases hTail :
              List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
                rest linkerSymbols with
          | none => simp [hHead, hTail] at hCompile
          | some tailArtifacts =>
              simp [hHead, hTail] at hCompile
              subst hCompile
              cases i with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq]
                    at hChild
                  subst hChild
                  exact ⟨headArtifact, rfl, hHead⟩
              | succ i =>
                  simpa using ih hTail (by simpa using hChild)

/-- A verified object artifact's image is named after its source object. -/
theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_imageName
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols =
        some artifact) :
    artifact.image.name = object.name := by
  obtain ⟨_childArtifacts, _plan, _codeArtifact, _hChildren, _hPlan, hFinish,
      _hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  exact (finishVerifiedStackObjectArtifact?_image_parts hFinish).1

/-- **Creation image embeds every verified child image.**

If `object` compiles through the supported verified entry point and its
`i`-th child object has a dot-free (path-component) name, then:

* the child compiles through the same entry point to a verified child
  artifact recorded at index `i` of `artifact.children` (so every end-to-end
  theorem about the entry point instantiates for the child), and
* there is an `offset` such that the resolution context recorded in the
  artifact — the very context in which the creation code was compiled, and
  the one `datasize`/`dataoffset` literals were resolved against — maps the
  child's name to exactly this `offset` and to the child image's size, and
* the parent image bytes at `[offset, offset + size)` are verbatim the
  child's verified image bytes. -/
theorem compileVerifiedStackObjectArtifact_child_image_embedded
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact} {i : Nat} {childObject : Object}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols =
        some artifact)
    (hChild : object.objects[i]? = some childObject)
    (hName : Name.objectPathComponent? childObject.name = true) :
    ∃ (childArtifact : VerifiedStackObjectArtifact) (offset : Nat),
      childObject.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols =
        some childArtifact ∧
      artifact.children[i]? = some childArtifact ∧
      childArtifact.image.name = childObject.name ∧
      object.compileVerifiedStackCodeArtifactIn? artifact.computed.context =
        some artifact.codeArtifact ∧
      artifact.computed.context.layout.findEntry? childObject.name =
        some (childArtifact.image.layoutEntryFromNat offset) ∧
      artifact.computed.context.layout.offset? childObject.name =
        some (EvmYul.UInt256.ofNat offset) ∧
      artifact.computed.context.size? childObject.name =
        some (EvmYul.UInt256.ofNat childArtifact.image.size) ∧
      childArtifact.image.layoutEntryFromNat offset ∈
        artifact.image.layoutEntries ∧
      (artifact.image.bytes.drop offset).take
          childArtifact.image.bytes.length =
        childArtifact.image.bytes := by
  obtain ⟨childArtifacts, plan, codeArtifact, hChildren, hPlan, hFinish,
      hCode, hArtifactChildren, hContext, _hChildImages, _hPayloadComputed,
      _hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  -- The child compiles through the same verified entry point.
  obtain ⟨childArtifact, hChildAt, hChildCompile⟩ :=
    List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?_getElem?
      hChildren hChild
  have hChildName : childArtifact.image.name = childObject.name :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_imageName
      hChildCompile
  -- Plan-level structural facts.
  unfold planVerifiedStackObjectArtifactFromChildren? at hPlan
  obtain ⟨hChildImages, hItems, hPayloadGen, hLayoutGen, hCtxLayout, hUnique⟩ :=
    planObjectArtifactFromChildImagesArtifactWith?_layout object linkerSymbols
      (childArtifacts.map VerifiedStackObjectArtifact.image)
      object.compileVerifiedStackCodeArtifactIn? (·.bytes) hPlan
  -- Image-level facts from the finisher.
  obtain ⟨_hImageName, hImageBytes, hLayoutEntries, hCodeLen, _hChildrenEq⟩ :=
    finishVerifiedStackObjectArtifact?_image_parts hFinish
  -- Locate the child image inside the payload/layout walk.
  have hImageAt :
      (childArtifacts.map VerifiedStackObjectArtifact.image)[i]? =
        some childArtifact.image := by
    rw [List.getElem?_map, hChildAt]
    rfl
  have hLt : i < object.objects.length := by
    rcases List.getElem?_eq_some_iff.mp hChild with ⟨hLt, _⟩
    exact hLt
  have hMemItems : ObjectItemRef.object i ∈ plan.items :=
    payloadItems?_object_mem hItems hLt
  obtain ⟨k, hTake, hEntryCond⟩ :=
    ObjectItemRef.List.payloadBytes?_object_embedded hImageAt
      hPayloadGen hLayoutGen hMemItems
  have hPathImage : Name.objectPathComponent? childArtifact.image.name = true := by
    rw [hChildName]
    exact hName
  have hEntryMem :
      childArtifact.image.layoutEntryFromNat (plan.codeBase + k) ∈
        plan.layout :=
    hEntryCond hPathImage
  -- Uniqueness of object/data names gives find?-level resolution.
  have hNodupAll :
      (ObjectBuiltinContext.objectDataNames plan.context).Nodup := by
    exact of_decide_eq_true hUnique
  rw [ObjectBuiltinContext.objectDataNames, hCtxLayout] at hNodupAll
  have hNameMemLayout :
      childObject.name ∈
        ({ entries := plan.layout } : ObjectLayout).entries.map
          (fun entry => entry.name) := by
    exact List.mem_map.mpr ⟨_, hEntryMem, hChildName⟩
  have hNodupLayoutNames :
      (({ entries := plan.layout } : ObjectLayout).entries.map
        (fun entry => entry.name)).Nodup :=
    nodup_append_left (nodup_append_left hNodupAll)
  have hNotMemDataSizes :
      childObject.name ∉ plan.context.dataSizes.map Prod.fst :=
    nodup_append_not_mem (nodup_append_left hNodupAll) hNameMemLayout
  have hNotMemSelf :
      childObject.name ∉
        (match plan.context.selfSize? with
          | some (selfName, _size) =>
              if Name.objectPathComponent? selfName then [selfName] else []
          | none => []) :=
    nodup_append_not_mem hNodupAll (List.mem_append_left _ hNameMemLayout)
  have hFind :
      plan.layout.find?
          (fun entry => entry.name == childObject.name) =
        some (childArtifact.image.layoutEntryFromNat (plan.codeBase + k)) := by
    have hFound := find?_entry_of_nodup hNodupLayoutNames hEntryMem
    have hEntryName :
        (childArtifact.image.layoutEntryFromNat (plan.codeBase + k)).name =
          childObject.name := hChildName
    rw [hEntryName] at hFound
    exact hFound
  have hFindEntry :
      plan.context.layout.findEntry? childObject.name =
        some (childArtifact.image.layoutEntryFromNat (plan.codeBase + k)) := by
    rw [hCtxLayout]
    exact hFind
  -- `datasize` resolution: no data-section or self-size entry shadows the
  -- child name, so the context resolves it through the layout witness.
  have hDataSizeNone :
      plan.context.findDataSize? childObject.name = none := by
    unfold ObjectBuiltinContext.findDataSize?
    have hFindNone :
        plan.context.dataSizes.find?
            (fun entry => entry.fst == childObject.name) =
          none := by
      rw [List.find?_eq_none]
      intro entry hMemEntry hBeq
      exact hNotMemDataSizes
        (List.mem_map.mpr ⟨entry, hMemEntry, eq_of_beq hBeq⟩)
    rw [hFindNone]
    rfl
  have hSelfSizeNone :
      plan.context.findSelfSize? childObject.name = none := by
    unfold ObjectBuiltinContext.findSelfSize?
    cases hSelf : plan.context.selfSize? with
    | none => rfl
    | some selfEntry =>
        rcases selfEntry with ⟨selfName, selfSize⟩
        rw [hSelf] at hNotMemSelf
        by_cases hPathSelf : Name.objectPathComponent? selfName = true
        · have hNe : selfName ≠ childObject.name := by
            intro hEqName
            exact hNotMemSelf (by simp [hEqName, hName])
          simp [hNe]
        · simp [Bool.not_eq_true] at hPathSelf
          simp [hPathSelf]
  have hSizeRes :
      plan.context.size? childObject.name =
        some (EvmYul.UInt256.ofNat childArtifact.image.size) := by
    unfold ObjectBuiltinContext.size?
    rw [hDataSizeNone, hSelfSizeNone, hCtxLayout]
    simp [ObjectLayout.size?, ObjectLayout.findEntry?, hFind,
      ObjectImage.layoutEntryFromNat]
  have hOffsetRes :
      plan.context.layout.offset? childObject.name =
        some (EvmYul.UInt256.ofNat (plan.codeBase + k)) := by
    rw [hCtxLayout]
    simp [ObjectLayout.offset?, ObjectLayout.findEntry?, hFind,
      ObjectImage.layoutEntryFromNat]
  -- The embedded bytes: code prefix has length `plan.codeBase`.
  have hBytes :
      (artifact.image.bytes.drop (plan.codeBase + k)).take
          childArtifact.image.bytes.length =
        childArtifact.image.bytes := by
    rw [hImageBytes, ← hCodeLen, drop_append_add]
    exact hTake
  refine ⟨childArtifact, plan.codeBase + k, hChildCompile, ?_, hChildName,
    ?_, ?_, ?_, ?_, ?_, hBytes⟩
  · rw [hArtifactChildren]
    exact hChildAt
  · rw [hContext]
    exact hCode
  · rw [hContext]
    exact hFindEntry
  · rw [hContext]
    exact hOffsetRes
  · rw [hContext]
    exact hSizeRes
  · rw [hLayoutEntries]
    exact hEntryMem

/-- **The creation image embeds the deployed runtime image.**

Specialization of `compileVerifiedStackObjectArtifact_child_image_embedded`
to the solc object shape, where the creation object `<C>` carries the runtime
object `<C>_deployed` as its only child.  The deployed runtime object's
verified image bytes sit verbatim inside the creation image at exactly the
offset/size that `dataoffset("<C>_deployed")`/`datasize("<C>_deployed")`
resolved to in the creation code — i.e. the bytes the constructor's
CODECOPY/RETURN sequence deploys are the verified runtime image. -/
theorem creationImage_embeds_deployedRuntimeImage
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact} {runtimeObject : Object}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols =
        some artifact)
    (hObjects : object.objects = [runtimeObject])
    (hName : Name.objectPathComponent? runtimeObject.name = true) :
    ∃ (runtimeArtifact : VerifiedStackObjectArtifact) (offset : Nat),
      runtimeObject.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols =
        some runtimeArtifact ∧
      artifact.children[0]? = some runtimeArtifact ∧
      runtimeArtifact.image.name = runtimeObject.name ∧
      object.compileVerifiedStackCodeArtifactIn? artifact.computed.context =
        some artifact.codeArtifact ∧
      artifact.computed.context.layout.findEntry? runtimeObject.name =
        some (runtimeArtifact.image.layoutEntryFromNat offset) ∧
      artifact.computed.context.layout.offset? runtimeObject.name =
        some (EvmYul.UInt256.ofNat offset) ∧
      artifact.computed.context.size? runtimeObject.name =
        some (EvmYul.UInt256.ofNat runtimeArtifact.image.size) ∧
      runtimeArtifact.image.layoutEntryFromNat offset ∈
        artifact.image.layoutEntries ∧
      (artifact.image.bytes.drop offset).take
          runtimeArtifact.image.bytes.length =
        runtimeArtifact.image.bytes := by
  have hChild : object.objects[0]? = some runtimeObject := by
    rw [hObjects]
    rfl
  exact
    compileVerifiedStackObjectArtifact_child_image_embedded
      hCompile hChild hName

end Object

end Frontend
end Solidity
end EvmCompiler
