import EvmCompiler.Solidity.Frontend

namespace EvmCompiler
namespace Solidity
namespace Frontend

inductive VerifiedStackObjectArtifact where
  | mk
      (computed : Object.ObjectComputedObjectData)
      (image : ObjectImage)
      (codeArtifact : Object.VerifiedStackCodeArtifact)
      (children : List VerifiedStackObjectArtifact)

namespace VerifiedStackObjectArtifact

def computed : VerifiedStackObjectArtifact → Object.ObjectComputedObjectData
  | .mk computed _image _codeArtifact _children => computed

def image : VerifiedStackObjectArtifact → ObjectImage
  | .mk _computed image _codeArtifact _children => image

def codeArtifact : VerifiedStackObjectArtifact →
    Object.VerifiedStackCodeArtifact
  | .mk _computed _image codeArtifact _children => codeArtifact

def children : VerifiedStackObjectArtifact →
    List VerifiedStackObjectArtifact
  | .mk _computed _image _codeArtifact children => children

end VerifiedStackObjectArtifact

namespace Object

def planVerifiedStackObjectArtifactFromChildren? (object : Object)
    (linkerSymbols : List (Name × Word))
    (childArtifacts : List VerifiedStackObjectArtifact) :
    Option (ObjectArtifactPlan × VerifiedStackCodeArtifact) :=
  object.planObjectArtifactFromChildImagesArtifactWith? linkerSymbols
    (childArtifacts.map VerifiedStackObjectArtifact.image)
    object.compileVerifiedStackCodeArtifactIn? (·.bytes)

def finishVerifiedStackObjectArtifact? (object : Object)
    (childArtifacts : List VerifiedStackObjectArtifact)
    (plan : ObjectArtifactPlan) (codeArtifact : VerifiedStackCodeArtifact) :
    Option VerifiedStackObjectArtifact := do
  if codeArtifact.bytes.length == plan.codeBase then
    if codeArtifact.immutableMarkerBytes.length == plan.codeBase then
      let ownImmutableReferences :=
        Bytecode.immutableReferenceEntriesFromCodes
          codeArtifact.bytes codeArtifact.immutableMarkerBytes
            plan.markerImmutableValues
      let payloadImmutableReferences ←
        ObjectItemRef.List.immutableReferenceEntriesFromNat?
          object.data plan.childImages plan.codeBase plan.items
      let immutableReferences :=
        ownImmutableReferences ++ payloadImmutableReferences
      let computed : ObjectComputedObjectData :=
        { childImages := plan.childImages
          items := plan.items
          dataSizes := plan.dataSizes
          dataOffsets := plan.dataOffsets
          payload := plan.payload
          codeBase := plan.codeBase
          context := plan.context
          code := codeArtifact.bytes
          markerCode := codeArtifact.immutableMarkerBytes }
      let image : ObjectImage :=
        { name := object.name
          bytes := codeArtifact.bytes ++ plan.payload
          immutableReferences := immutableReferences
          layoutEntries := plan.layout
          dataSizeEntries := plan.dataSizes
          dataOffsetEntries := plan.dataOffsets }
      some (.mk computed image codeArtifact childArtifacts)
    else
      none
  else
    none

theorem finishVerifiedStackObjectArtifact?_parts
    {object : Object} {plan : ObjectArtifactPlan}
    {childArtifacts : List VerifiedStackObjectArtifact}
    {codeArtifact : VerifiedStackCodeArtifact}
    {artifact : VerifiedStackObjectArtifact}
    (hFinish :
      object.finishVerifiedStackObjectArtifact? childArtifacts plan
          codeArtifact =
        some artifact) :
    artifact.codeArtifact = codeArtifact ∧
      artifact.children = childArtifacts ∧
      artifact.computed.context = plan.context ∧
      artifact.computed.childImages = plan.childImages ∧
      artifact.computed.payload = plan.payload ∧
      artifact.computed.code = artifact.codeArtifact.bytes ∧
      artifact.image.bytes = artifact.codeArtifact.bytes ++ plan.payload := by
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
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

mutual
  def compileVerifiedStackObjectArtifactWithLinkerSymbols?
      (object : Object) (linkerSymbols : List (Name × Word)) :
      Option VerifiedStackObjectArtifact := do
    let childArtifacts ←
      List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
        object.objects linkerSymbols
    let planned ←
      object.planVerifiedStackObjectArtifactFromChildren?
        linkerSymbols childArtifacts
    object.finishVerifiedStackObjectArtifact? childArtifacts
      planned.1 planned.2
  termination_by sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  def List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
      (objects : List Object) (linkerSymbols : List (Name × Word)) :
      Option (List VerifiedStackObjectArtifact) :=
    match objects with
    | [] => some []
    | object :: rest => do
        let head ←
          Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
            object linkerSymbols
        let tail ←
          List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
            rest linkerSymbols
        some (head :: tail)
  termination_by sizeOf objects
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    ∃ childArtifacts plan codeArtifact,
      List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
          object.objects linkerSymbols = some childArtifacts ∧
      object.planVerifiedStackObjectArtifactFromChildren?
          linkerSymbols childArtifacts = some (plan, codeArtifact) ∧
      object.finishVerifiedStackObjectArtifact? childArtifacts plan
          codeArtifact = some artifact ∧
      object.compileVerifiedStackCodeArtifactIn? plan.context =
        some artifact.codeArtifact ∧
      artifact.children = childArtifacts ∧
      artifact.computed.context = plan.context ∧
      artifact.computed.childImages = plan.childImages ∧
      artifact.computed.payload = plan.payload ∧
      artifact.image.bytes =
        artifact.codeArtifact.bytes ++ plan.payload := by
  unfold compileVerifiedStackObjectArtifactWithLinkerSymbols? at hCompile
  cases hChildren :
      List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
        object.objects linkerSymbols with
  | none => simp [hChildren] at hCompile
  | some childArtifacts =>
      cases hPlan :
          object.planVerifiedStackObjectArtifactFromChildren?
            linkerSymbols childArtifacts with
      | none => simp [hChildren, hPlan] at hCompile
      | some planned =>
          rcases planned with ⟨plan, codeArtifact⟩
          have hFinish :
              object.finishVerifiedStackObjectArtifact?
                  childArtifacts plan codeArtifact = some artifact := by
            simpa [hChildren, hPlan] using hCompile
          have hParts := finishVerifiedStackObjectArtifact?_parts hFinish
          have hCodeArtifact :
              object.compileVerifiedStackCodeArtifactIn? plan.context =
                some codeArtifact :=
            planObjectArtifactFromChildImagesArtifactWith?_compiled
              object linkerSymbols
              (childArtifacts.map VerifiedStackObjectArtifact.image)
              object.compileVerifiedStackCodeArtifactIn? (·.bytes) hPlan
          have hCode :
              object.compileVerifiedStackCodeArtifactIn? plan.context =
                some artifact.codeArtifact := by
            simpa [hParts.1] using hCodeArtifact
          refine
            ⟨childArtifacts, plan, codeArtifact, rfl, hPlan, hFinish, hCode,
              hParts.2.1, hParts.2.2.1, hParts.2.2.2.1,
              hParts.2.2.2.2.1, hParts.2.2.2.2.2.2⟩

theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    ∃ plan : ObjectArtifactPlan,
      artifact.image.bytes =
        artifact.codeArtifact.compact.bytes.toList ++
          verifiedCodeSentinel ++ plan.payload := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hArtifactChildren, _hContext, _hChildImages, _hPayload, hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, _hCompact, hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  refine ⟨plan, ?_⟩
  rw [hImage, hBytes]

theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    Assembly.Compact.DecodingCorrect artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hArtifactChildren, _hContext, _hChildImages, _hPayload, hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  rw [hImage]
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  rw [hBytes]
  simpa [List.append_assoc] using
    (Assembly.Compact.compile?_decodingCorrect_with_suffix
      hCompact (verifiedCodeSentinel ++ plan.payload))

/-- Suffix-tolerant decoding correctness: the checked object image remains a
correct decoding prefix under any appended byte suffix (for example
ABI-encoded constructor arguments in a creation frame). The exact-image
theorem `compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect`
is the `suffix := []` instance. -/
theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (suffix : List UInt8) :
    Assembly.Compact.DecodingCorrect artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix)) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hArtifactChildren, _hContext, _hChildImages, _hPayload, hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  rw [hImage]
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  rw [hBytes]
  simpa [List.append_assoc] using
    (Assembly.Compact.compile?_decodingCorrect_with_suffix
      hCompact (verifiedCodeSentinel ++ plan.payload ++ suffix))

mutual
  inductive VerifiedStackObjectArtifact.ValidFor
      (linkerSymbols : List (Name × Word)) :
      Object → VerifiedStackObjectArtifact → Prop where
    | intro
        {object : Object} {artifact : VerifiedStackObjectArtifact}
        {childArtifacts : List VerifiedStackObjectArtifact}
        {plan : ObjectArtifactPlan}
        {codeArtifact : VerifiedStackCodeArtifact}
        (children : VerifiedStackObjectArtifact.ListValidFor linkerSymbols
          object.objects childArtifacts)
        (planned : object.planVerifiedStackObjectArtifactFromChildren?
          linkerSymbols childArtifacts = some (plan, codeArtifact))
        (finished : object.finishVerifiedStackObjectArtifact?
          childArtifacts plan codeArtifact = some artifact) :
        VerifiedStackObjectArtifact.ValidFor linkerSymbols object artifact

  inductive VerifiedStackObjectArtifact.ListValidFor
      (linkerSymbols : List (Name × Word)) :
      List Object → List VerifiedStackObjectArtifact → Prop where
    | nil : VerifiedStackObjectArtifact.ListValidFor linkerSymbols [] []
    | cons
        {object : Object} {objects : List Object}
        {artifact : VerifiedStackObjectArtifact}
        {artifacts : List VerifiedStackObjectArtifact}
        (head : VerifiedStackObjectArtifact.ValidFor
          linkerSymbols object artifact)
        (tail : VerifiedStackObjectArtifact.ListValidFor
          linkerSymbols objects artifacts) :
        VerifiedStackObjectArtifact.ListValidFor linkerSymbols
          (object :: objects) (artifact :: artifacts)
end

mutual
  theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_valid
      (object : Object) (linkerSymbols : List (Name × Word))
      (artifact : VerifiedStackObjectArtifact)
      (hCompile :
        object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
            linkerSymbols = some artifact) :
      VerifiedStackObjectArtifact.ValidFor linkerSymbols object artifact := by
    unfold compileVerifiedStackObjectArtifactWithLinkerSymbols? at hCompile
    cases hChildren :
        List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
          object.objects linkerSymbols with
    | none => simp [hChildren] at hCompile
    | some childArtifacts =>
        cases hPlan : object.planVerifiedStackObjectArtifactFromChildren?
            linkerSymbols childArtifacts with
        | none => simp [hChildren, hPlan] at hCompile
        | some planned =>
            rcases planned with ⟨plan, codeArtifact⟩
            have hFinish :
                object.finishVerifiedStackObjectArtifact?
                    childArtifacts plan codeArtifact = some artifact := by
              simpa [hChildren, hPlan] using hCompile
            exact .intro
              (List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?_valid
                object.objects linkerSymbols childArtifacts hChildren)
              hPlan hFinish
  termination_by 2 * sizeOf object
  decreasing_by
    simp_wf
    cases object
    simp_wf
    omega

  theorem List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?_valid
      (objects : List Object) (linkerSymbols : List (Name × Word))
      (artifacts : List VerifiedStackObjectArtifact)
      (hCompile :
        List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
            objects linkerSymbols = some artifacts) :
      VerifiedStackObjectArtifact.ListValidFor
        linkerSymbols objects artifacts := by
    cases objects with
    | nil =>
        simp [List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?]
          at hCompile
        subst artifacts
        exact .nil
    | cons object rest =>
        unfold List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
          at hCompile
        cases hHead :
            object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
              linkerSymbols with
        | none => simp [hHead] at hCompile
        | some artifact =>
            cases hTail :
                List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?
                  rest linkerSymbols with
            | none => simp [hHead, hTail] at hCompile
            | some tail =>
                simp [hHead, hTail] at hCompile
                subst artifacts
                exact .cons
                  (compileVerifiedStackObjectArtifactWithLinkerSymbols?_valid
                    object linkerSymbols artifact hHead)
                  (List.compileVerifiedStackObjectArtifactsWithLinkerSymbols?_valid
                    rest linkerSymbols tail hTail)
  termination_by 2 * sizeOf objects + 1
  decreasing_by
    all_goals simp_all
    all_goals simp_wf
    all_goals omega
end

end Object

/-- The exported own-code immutable-reference groups of a compiled artifact:
exactly the reference entries the deploy-time patch theorems patch. -/
def VerifiedStackObjectArtifact.ownImmutableReferences
    (compiledFor : Object) (artifact : VerifiedStackObjectArtifact) :
    List (Name × List ImmutableReference) :=
  Bytecode.immutableReferenceEntriesFromCodes
    artifact.codeArtifact.bytes
    artifact.codeArtifact.immutableMarkerBytes
    (ImmutableReference.markerEntriesFromNat 0 compiledFor.loadImmutableNames)

/-- Fail-closed acceptance gate for unlinked-library artifacts.  Checks, on
the compiled artifact itself, every fact the link-time patch theorem needs
beyond compile success: the unlinked names collide with no `loadimmutable`
name; all exported own-code windows are pairwise disjoint and in bounds of
the image; and every unlinked-library window still carries zero bytes in its
high 12 positions (where the 20-byte address write does not reach). -/
def Object.unlinkedLibraryGate? (object : Object) (missing : List Name)
    (artifact : VerifiedStackObjectArtifact) : Bool :=
  let substituted := object.substituteUnlinkedLibraries missing
  let refs := artifact.ownImmutableReferences substituted
  missing.all (fun name => !(object.allLoadImmutableNames.contains name)) &&
    Bytecode.windowsPairwiseDisjoint? (refs.flatMap (fun entry => entry.snd)) &&
    refs.all (fun entry =>
      entry.snd.all (fun reference =>
        decide (reference.start + 32 ≤ artifact.image.bytes.length))) &&
    refs.all (fun entry =>
      !(missing.contains entry.fst) ||
        entry.snd.all (fun reference =>
          Bytecode.startsWithAt (List.replicate 12 0)
            artifact.image.bytes reference.start))

/-- Compile an object whose `linkersymbol` names are only partially
provided: the missing names are rewritten into `loadimmutable` markers and
flow through the one supported pipeline unchanged, then the link-time gate
is checked.  The artifact's image exports the unlinked names as extra
`immutableReferences` entries; `ObjectImage.linkReferences` re-windows them
into solc-compatible `linkReferences`. -/
def Object.compileVerifiedStackObjectArtifactUnlinked? (object : Object)
    (provided : List (Name × Word)) :
    Option VerifiedStackObjectArtifact := do
  let missing := object.missingLinkerSymbolNames provided
  let artifact ←
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
      (object.substituteUnlinkedLibraries missing) provided
  if object.unlinkedLibraryGate? missing artifact then
    some artifact
  else
    none

theorem Object.compileVerifiedStackObjectArtifactUnlinked?_parts
    {object : Object} {provided : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactUnlinked? provided =
        some artifact) :
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
        (object.substituteUnlinkedLibraries
          (object.missingLinkerSymbolNames provided)) provided =
      some artifact ∧
    object.unlinkedLibraryGate?
      (object.missingLinkerSymbolNames provided) artifact = true := by
  unfold compileVerifiedStackObjectArtifactUnlinked? at hCompile
  cases hInner :
      Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
        (object.substituteUnlinkedLibraries
          (object.missingLinkerSymbolNames provided)) provided with
  | none => simp [hInner] at hCompile
  | some compiled =>
      by_cases hGate :
          object.unlinkedLibraryGate?
            (object.missingLinkerSymbolNames provided) compiled = true
      · simp [hInner, hGate] at hCompile
        subst artifact
        exact ⟨rfl, hGate⟩
      · simp [hInner, hGate] at hCompile

namespace Program

/-- Compile with possibly unresolved `linkersymbol` names, exporting the
missing names as link references. -/
def compileArtifactUnlinked? (program : Program)
    (provided : List (Name × Word)) :
    Option VerifiedStackObjectArtifact :=
  program.object.compileVerifiedStackObjectArtifactUnlinked? provided

/-- The unlinked names of a program under a partial address assignment. -/
def missingLinkerSymbolNames (program : Program)
    (provided : List (Name × Word)) : List Name :=
  program.object.missingLinkerSymbolNames provided

end Program

end Frontend
end Solidity
end EvmCompiler
