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
  exact Assembly.Compact.compile?_decodingCorrect_with_suffix
    hCompact plan.payload

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

end Frontend
end Solidity
end EvmCompiler
