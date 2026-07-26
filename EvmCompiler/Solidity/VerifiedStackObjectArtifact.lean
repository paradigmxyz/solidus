import EvmCompiler.Solidity.Frontend
import EvmCompiler.TypedCfg.LateReturnCompactPreservation
import EvmCompiler.Assembly.StackHeadroom

namespace EvmCompiler
namespace Solidity
namespace Frontend

inductive VerifiedStackCodeChoice where
  | standard
  | late
      (artifact :
        TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.Artifact)

namespace VerifiedStackCodeChoice

def compact (choice : VerifiedStackCodeChoice)
    (standard : Object.VerifiedStackCodeArtifact) :
    Assembly.Compact.Artifact :=
  match choice with
  | .standard => standard.compact
  | .late artifact => artifact.base.base.compact.asCompact

def bytes (choice : VerifiedStackCodeChoice)
    (standard : Object.VerifiedStackCodeArtifact) : List UInt8 :=
  match choice with
  | .standard => standard.bytes
  | .late artifact =>
      artifact.base.base.compact.bytes.toList ++
        Object.verifiedCodeSentinel

def markerBytes (choice : VerifiedStackCodeChoice)
    (standard : Object.VerifiedStackCodeArtifact) : List UInt8 :=
  match choice with
  | .standard => standard.immutableMarkerBytes
  | .late _ => choice.bytes standard

def executionFuelFactor (choice : VerifiedStackCodeChoice)
    (standard : Object.VerifiedStackCodeArtifact) : Nat :=
  match choice with
  | .standard =>
      2 *
        TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
          standard.compiled.cfg
  | .late artifact => artifact.fuelBudget

theorem bytes_eq_compact_bytes_append_sentinel
    (choice : VerifiedStackCodeChoice)
    (standard : Object.VerifiedStackCodeArtifact)
    (hStandard :
      standard.bytes =
        standard.compact.bytes.toList ++ Object.verifiedCodeSentinel) :
    choice.bytes standard =
      (choice.compact standard).bytes.toList ++
        Object.verifiedCodeSentinel := by
  cases choice with
  | standard =>
      simpa [bytes, compact] using hStandard
  | late artifact =>
      rfl

end VerifiedStackCodeChoice

inductive VerifiedStackObjectArtifact where
  | mk
      (computed : Object.ObjectComputedObjectData)
      (image : ObjectImage)
      (codeArtifact : Object.VerifiedStackCodeArtifact)
      (codeChoice : VerifiedStackCodeChoice)
      (children : List VerifiedStackObjectArtifact)

namespace VerifiedStackObjectArtifact

def computed : VerifiedStackObjectArtifact → Object.ObjectComputedObjectData
  | .mk computed _image _codeArtifact _codeChoice _children => computed

def image : VerifiedStackObjectArtifact → ObjectImage
  | .mk _computed image _codeArtifact _codeChoice _children => image

def codeArtifact : VerifiedStackObjectArtifact →
    Object.VerifiedStackCodeArtifact
  | .mk _computed _image codeArtifact _codeChoice _children => codeArtifact

def codeChoice : VerifiedStackObjectArtifact → VerifiedStackCodeChoice
  | .mk _computed _image _codeArtifact codeChoice _children => codeChoice

def children : VerifiedStackObjectArtifact →
    List VerifiedStackObjectArtifact
  | .mk _computed _image _codeArtifact _codeChoice children => children

end VerifiedStackObjectArtifact

namespace Object

def lateVerifiedStackCode? (object : Object)
    (standard : VerifiedStackCodeArtifact) :
    Option
      TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.Artifact := do
  if object.loadImmutableNames.isEmpty then
    pure ()
  else
    none
  let candidate ←
    TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.compileCfg?
      standard.compiled.cfg
  let _ ←
    Assembly.StackHeadroom.mkRawCert?
      candidate.base.base.compact.asCompact
  if candidate.base.base.compact.bytes.size + 2 <
      standard.compact.bytes.size then
    some candidate
  else
    none

def verifiedStackCodeChoice (object : Object)
    (standard : VerifiedStackCodeArtifact) : VerifiedStackCodeChoice :=
  match object.lateVerifiedStackCode? standard with
  | some candidate => .late candidate
  | none => .standard

theorem lateVerifiedStackCode?_valid
    {object : Object} {standard : VerifiedStackCodeArtifact}
    {candidate :
      TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.Artifact}
    (hLate :
      object.lateVerifiedStackCode? standard = some candidate) :
    candidate.ValidFor standard.compiled.cfg := by
  unfold lateVerifiedStackCode? at hLate
  by_cases hImmutable : object.loadImmutableNames.isEmpty = true
  · simp [hImmutable] at hLate
    cases hCandidate :
        TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.compileCfg?
          standard.compiled.cfg with
    | none =>
        simp [hCandidate] at hLate
    | some compiled =>
        simp [hCandidate] at hLate
        cases hHeadroom :
            Assembly.StackHeadroom.mkRawCert?
              compiled.base.base.compact.asCompact with
        | none =>
            simp [hHeadroom] at hLate
        | some cert =>
            by_cases hSmaller :
                compiled.base.base.compact.bytes.size + 2 <
                  standard.compact.bytes.size
            · simp [hHeadroom, hSmaller] at hLate
              subst candidate
              exact
                TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.compileCfg?_valid
                  hCandidate
            · simp [hHeadroom, hSmaller] at hLate
  · have hImmutableFalse :
        object.loadImmutableNames.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hImmutable
    simp [hImmutableFalse] at hLate

theorem lateVerifiedStackCode?_rawCert
    {object : Object} {standard : VerifiedStackCodeArtifact}
    {candidate :
      TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.Artifact}
    (hLate :
      object.lateVerifiedStackCode? standard = some candidate) :
    ∃ cert,
      Assembly.StackHeadroom.mkRawCert?
          candidate.base.base.compact.asCompact =
        some cert := by
  unfold lateVerifiedStackCode? at hLate
  by_cases hImmutable : object.loadImmutableNames.isEmpty = true
  · simp [hImmutable] at hLate
    cases hCandidate :
        TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.compileCfg?
          standard.compiled.cfg with
    | none =>
        simp [hCandidate] at hLate
    | some compiled =>
        simp [hCandidate] at hLate
        cases hHeadroom :
            Assembly.StackHeadroom.mkRawCert?
              compiled.base.base.compact.asCompact with
        | none =>
            simp [hHeadroom] at hLate
        | some cert =>
            by_cases hSmaller :
                compiled.base.base.compact.bytes.size + 2 <
                  standard.compact.bytes.size
            · simp [hHeadroom, hSmaller] at hLate
              subst candidate
              exact ⟨cert, hHeadroom⟩
            · simp [hHeadroom, hSmaller] at hLate
  · have hImmutableFalse :
        object.loadImmutableNames.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hImmutable
    simp [hImmutableFalse] at hLate

theorem verifiedStackCodeChoice_late_valid
    {object : Object} {standard : VerifiedStackCodeArtifact}
    {candidate :
      TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.Artifact}
    (hChoice :
      object.verifiedStackCodeChoice standard = .late candidate) :
    candidate.ValidFor standard.compiled.cfg := by
  unfold verifiedStackCodeChoice at hChoice
  cases hLate : object.lateVerifiedStackCode? standard with
  | none =>
      simp [hLate] at hChoice
  | some selected =>
      simp [hLate] at hChoice
      subst candidate
      exact lateVerifiedStackCode?_valid hLate

theorem verifiedStackCodeChoice_late_rawCert
    {object : Object} {standard : VerifiedStackCodeArtifact}
    {candidate :
      TypedCfg.LateReturnCompactPreservation.Compact.WholeVerified.Artifact}
    (hChoice :
      object.verifiedStackCodeChoice standard = .late candidate) :
    ∃ cert,
      Assembly.StackHeadroom.mkRawCert?
          candidate.base.base.compact.asCompact =
        some cert := by
  unfold verifiedStackCodeChoice at hChoice
  cases hLate : object.lateVerifiedStackCode? standard with
  | none =>
      simp [hLate] at hChoice
  | some selected =>
      simp [hLate] at hChoice
      subst candidate
      exact lateVerifiedStackCode?_rawCert hLate

theorem lateVerifiedStackCode?_eq_none_of_not_isEmpty
    {object : Object} {standard : VerifiedStackCodeArtifact}
    (hImmutable : object.loadImmutableNames.isEmpty = false) :
    object.lateVerifiedStackCode? standard = none := by
  simp [lateVerifiedStackCode?, hImmutable]

theorem verifiedStackCodeChoice_eq_standard_of_not_isEmpty
    {object : Object} {standard : VerifiedStackCodeArtifact}
    (hImmutable : object.loadImmutableNames.isEmpty = false) :
    object.verifiedStackCodeChoice standard = .standard := by
  simp [verifiedStackCodeChoice,
    lateVerifiedStackCode?_eq_none_of_not_isEmpty hImmutable]

def selectedVerifiedStackCodeBytes (object : Object)
    (standard : VerifiedStackCodeArtifact) : List UInt8 :=
  (object.verifiedStackCodeChoice standard).bytes standard

def selectedVerifiedStackMarkerBytes (object : Object)
    (standard : VerifiedStackCodeArtifact) : List UInt8 :=
  (object.verifiedStackCodeChoice standard).markerBytes standard

def planVerifiedStackObjectArtifactFromChildren? (object : Object)
    (linkerSymbols : List (Name × Word))
    (childArtifacts : List VerifiedStackObjectArtifact) :
    Option (ObjectArtifactPlan × VerifiedStackCodeArtifact) :=
  object.planObjectArtifactFromChildImagesArtifactWith? linkerSymbols
    (childArtifacts.map VerifiedStackObjectArtifact.image)
    object.compileVerifiedStackCodeArtifactIn?
      object.selectedVerifiedStackCodeBytes

def finishVerifiedStackObjectArtifact? (object : Object)
    (childArtifacts : List VerifiedStackObjectArtifact)
    (plan : ObjectArtifactPlan) (codeArtifact : VerifiedStackCodeArtifact) :
    Option VerifiedStackObjectArtifact := do
  let codeChoice := object.verifiedStackCodeChoice codeArtifact
  let codeBytes := codeChoice.bytes codeArtifact
  let markerBytes := codeChoice.markerBytes codeArtifact
  if codeBytes.length == plan.codeBase then
    if markerBytes.length == plan.codeBase then
      let ownImmutableReferences :=
        Bytecode.immutableReferenceEntriesFromCodes
          codeBytes markerBytes
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
          code := codeBytes
          markerCode := markerBytes }
      let image : ObjectImage :=
        { name := object.name
          bytes := codeBytes ++ plan.payload
          immutableReferences := immutableReferences
          layoutEntries := plan.layout
          dataSizeEntries := plan.dataSizes
          dataOffsetEntries := plan.dataOffsets }
      some (.mk computed image codeArtifact codeChoice childArtifacts)
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
      artifact.codeChoice =
        object.verifiedStackCodeChoice codeArtifact ∧
      artifact.children = childArtifacts ∧
      artifact.computed.context = plan.context ∧
      artifact.computed.childImages = plan.childImages ∧
      artifact.computed.payload = plan.payload ∧
      artifact.computed.code =
        artifact.codeChoice.bytes artifact.codeArtifact ∧
      artifact.computed.markerCode =
        artifact.codeChoice.markerBytes artifact.codeArtifact ∧
      artifact.image.bytes =
        artifact.codeChoice.bytes artifact.codeArtifact ++ plan.payload := by
  unfold finishVerifiedStackObjectArtifact? at hFinish
  let codeChoice := object.verifiedStackCodeChoice codeArtifact
  let codeBytes := codeChoice.bytes codeArtifact
  let markerBytes := codeChoice.markerBytes codeArtifact
  cases hCodeLength : codeBytes.length == plan.codeBase with
      | false =>
          have hCodeNe : codeBytes.length ≠ plan.codeBase := by
            simpa using hCodeLength
          simp [codeChoice, codeBytes, markerBytes, hCodeNe] at hFinish
      | true =>
          have hCodeEq : codeBytes.length = plan.codeBase := by
            simpa using hCodeLength
          cases hMarkerLength :
              markerBytes.length == plan.codeBase with
          | false =>
              have hMarkerNe :
                  markerBytes.length ≠ plan.codeBase := by
                simpa using hMarkerLength
              simp [codeChoice, codeBytes, markerBytes,
                hCodeEq, hMarkerNe] at hFinish
          | true =>
              have hMarkerEq :
                  markerBytes.length = plan.codeBase := by
                simpa using hMarkerLength
              cases hPayloadReferences :
                  ObjectItemRef.List.immutableReferenceEntriesFromNat?
                    object.data plan.childImages plan.codeBase plan.items with
              | none =>
                  simp [codeChoice, codeBytes, markerBytes,
                    hCodeEq, hMarkerEq, hPayloadReferences] at hFinish
              | some payloadReferences =>
                  simp [codeChoice, codeBytes, markerBytes,
                    hCodeEq, hMarkerEq, hPayloadReferences] at hFinish
                  subst artifact
                  exact
                    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
      artifact.codeChoice =
        object.verifiedStackCodeChoice artifact.codeArtifact ∧
      artifact.children = childArtifacts ∧
      artifact.computed.context = plan.context ∧
      artifact.computed.childImages = plan.childImages ∧
      artifact.computed.payload = plan.payload ∧
      artifact.computed.code =
        artifact.codeChoice.bytes artifact.codeArtifact ∧
      artifact.computed.markerCode =
        artifact.codeChoice.markerBytes artifact.codeArtifact ∧
      artifact.image.bytes =
        artifact.codeChoice.bytes artifact.codeArtifact ++ plan.payload := by
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
          rcases hParts with
            ⟨hArtifact, hChoice, hArtifactChildren, hContext,
              hChildImages, hPayload, hComputedCode, hMarkerCode,
              hImage⟩
          have hCodeArtifact :
              object.compileVerifiedStackCodeArtifactIn? plan.context =
                some codeArtifact :=
            planObjectArtifactFromChildImagesArtifactWith?_compiled
              object linkerSymbols
              (childArtifacts.map VerifiedStackObjectArtifact.image)
              object.compileVerifiedStackCodeArtifactIn?
              object.selectedVerifiedStackCodeBytes hPlan
          have hCode :
              object.compileVerifiedStackCodeArtifactIn? plan.context =
                some artifact.codeArtifact := by
            simpa [hArtifact] using hCodeArtifact
          refine
            ⟨childArtifacts, plan, codeArtifact, rfl, hPlan, hFinish, hCode,
              ?_, hArtifactChildren, hContext, hChildImages, hPayload,
              hComputedCode, hMarkerCode, hImage⟩
          simpa [hArtifact] using hChoice

theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    ∃ plan : ObjectArtifactPlan,
      artifact.image.bytes =
        (artifact.codeChoice.compact artifact.codeArtifact).bytes.toList ++
          verifiedCodeSentinel ++ plan.payload := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hChoice, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hComputedCode, _hMarkerCode, hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, _hCompact, hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  refine ⟨plan, ?_⟩
  rw [hImage,
    artifact.codeChoice.bytes_eq_compact_bytes_append_sentinel
      artifact.codeArtifact hBytes]

theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_selectedCompactProperties
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    let selected :=
      artifact.codeChoice.compact artifact.codeArtifact
    selected.program.Valid ∧
      Assembly.Compact.Program.codeLayoutFrom
        selected.program.code 0 ∧
      Assembly.Compact.Program.codeByteLength
          selected.program.code <
        18446744073709551616 ∧
      selected.bytes =
        Assembly.Compact.encode selected.program ∧
      Assembly.Compact.Program.codeByteLength
          selected.program.code + 1 <
        18446744073709551616 := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan,
      _hFinish, hCode, hChoice, _hArtifactChildren, _hContext,
      _hChildImages, _hPayload, _hComputedCode, _hMarkerCode,
      _hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack,
      _pinnedPushPcs, _hPins, hCompact, _hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  cases hSelected : artifact.codeChoice with
  | standard =>
      have hValid := Assembly.Compact.compile?_valid hCompact
      simpa [VerifiedStackCodeChoice.compact] using
        And.intro hValid.wellFormed.1
          (And.intro hValid.wellFormed.2.1
            (And.intro hValid.wellFormed.2.2.1
              (And.intro hValid.bytes hValid.sentinelFits)))
  | late candidate =>
      have hSelectedValid :
          candidate.ValidFor artifact.codeArtifact.compiled.cfg := by
        apply verifiedStackCodeChoice_late_valid
        rw [← hChoice, hSelected]
      have hLateCompile :=
        hSelectedValid.baseValid.baseValid.compactCompile
      have hValid :=
        TypedCfg.ReturnAddressProbe.Compact.compile?_valid hLateCompile
      simpa [VerifiedStackCodeChoice.compact,
        TypedCfg.ReturnAddressProbe.Compact.Artifact.asCompact] using
        And.intro hValid.wellFormed.1
          (And.intro hValid.wellFormed.2.1
            (And.intro hValid.wellFormed.2.2.1
              (And.intro hValid.bytes hValid.sentinelFits)))

theorem compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    Assembly.Compact.DecodingCorrect
      (artifact.codeChoice.compact artifact.codeArtifact).program
      (Assembly.Bytecode.ofList artifact.image.bytes) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      hChoice, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hComputedCode, _hMarkerCode, hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  rw [hImage]
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  cases hSelected : artifact.codeChoice with
  | standard =>
      simp only [VerifiedStackCodeChoice.bytes,
        VerifiedStackCodeChoice.compact]
      rw [hBytes]
      simpa [List.append_assoc] using
        (Assembly.Compact.compile?_decodingCorrect_with_suffix
          hCompact (verifiedCodeSentinel ++ plan.payload))
  | late candidate =>
      have hSelectedValid :
          candidate.ValidFor artifact.codeArtifact.compiled.cfg := by
        apply verifiedStackCodeChoice_late_valid
        rw [← hChoice, hSelected]
      have hLateCompact :=
        hSelectedValid.baseValid.baseValid.compactCompile
      simpa [VerifiedStackCodeChoice.bytes,
        VerifiedStackCodeChoice.compact, List.append_assoc] using
        (TypedCfg.ReturnAddressProbe.Compact.compile?_decodingCorrect_with_suffix
            hLateCompact (verifiedCodeSentinel ++ plan.payload))

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
    Assembly.Compact.DecodingCorrect
      (artifact.codeChoice.compact artifact.codeArtifact).program
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix)) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      hChoice, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hComputedCode, _hMarkerCode, hImage⟩ :=
    compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts hCompile
  rw [hImage]
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, hBytes, _hMarker⟩ :=
    compileVerifiedStackCodeArtifactIn?_parts hCode
  cases hSelected : artifact.codeChoice with
  | standard =>
      simp only [VerifiedStackCodeChoice.bytes,
        VerifiedStackCodeChoice.compact]
      rw [hBytes]
      simpa [List.append_assoc] using
        (Assembly.Compact.compile?_decodingCorrect_with_suffix
          hCompact (verifiedCodeSentinel ++ plan.payload ++ suffix))
  | late candidate =>
      have hSelectedValid :
          candidate.ValidFor artifact.codeArtifact.compiled.cfg := by
        apply verifiedStackCodeChoice_late_valid
        rw [← hChoice, hSelected]
      have hLateCompact :=
        hSelectedValid.baseValid.baseValid.compactCompile
      simpa [VerifiedStackCodeChoice.bytes,
        VerifiedStackCodeChoice.compact, List.append_assoc] using
        (TypedCfg.ReturnAddressProbe.Compact.compile?_decodingCorrect_with_suffix
          hLateCompact
            (verifiedCodeSentinel ++ plan.payload ++ suffix))

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
    artifact.computed.code
    artifact.computed.markerCode
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
