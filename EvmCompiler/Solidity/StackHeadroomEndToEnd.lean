import EvmCompiler.Solidity.VerifiedStackObjectArtifact
import EvmCompiler.Assembly.StackHeadroomSound

/-!
# Verified-artifact stack-headroom endpoint

Standalone stack-headroom certification for compiled verified stack object
artifacts: `stackHeadroomCert?` produces (fail-closed) a validated per-pc
height certificate for the artifact's compact program, and the endpoint
theorems below turn a successful certificate into

* `EvmYul.EVM.X` never returning `StackOverflow` on the artifact's byte image
  entered with an empty stack (both the exact runtime image and the
  creation-frame image with appended constructor-argument suffix), and
* an escape-free strengthening of any `RunRefinesOpen` witness
  (`RunRefinesOpenNoStackOverflow`).

The certificate producer is deliberately not a blocking compile gate: the
stage-1 checker covers the uniform-height fragment (no shared procedure
bodies entered at distinct stack depths); artifacts outside the fragment
simply do not receive the strengthened theorems.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

open EvmCompiler.Assembly

/-- Fail-closed stack-headroom certificate for a compiled artifact. -/
def VerifiedStackObjectArtifact.stackHeadroomCert?
    (artifact : VerifiedStackObjectArtifact) :
    Option StackHeadroom.Cert :=
  StackHeadroom.mkCert? artifact.codeArtifact.compact

/-- On a certified artifact image entered at pc `0` with an empty stack, the
gasful frame interpreter never reports `StackOverflow`, for any jump-table
and any fuel. -/
theorem VerifiedStackObjectArtifact.x_ne_stackOverflow
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList artifact.image.bytes)
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = []) :
    ∀ fuel,
      EvmYul.EVM.X fuel validJumps gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeIn, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStackLower, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Object.compileVerifiedStackCodeArtifactIn?_parts hCodeIn
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject
  obtain ⟨plan, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Object.verifiedCodeSentinel, List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact plan.payload)
  have hInitialPoint :=
    Assembly.GasfulBridge.artifactFramePoint_initial hCompact hCode hPc
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes) validJumps :=
    Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_compile
      (validJumps := validJumps) hCompact hDecode
  have hStepInv :
      Assembly.GasfulBridge.ArtifactFrameStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes) validJumps := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (Assembly.GasfulBridge.artifactFrameStepInvariant_of_ordinaryBoundary
      hCompact hDecode hSentinel hOrdinary) hPoint hPrefix hStep hContinues
  have hFrame :=
    Assembly.GasfulBridge.artifactFrameInvariant_of_step hInitialPoint
      hStepInv
  have hCheck := StackHeadroom.mkCert?_check hCert
  intro fuel
  exact StackHeadroom.x_ne_stackOverflow_of_cert hCompact hDecode hCheck
    hSentinel hFrame hPc hStack fuel

/-- Suffix-tolerant variant for creation frames: the concrete entry point is
`X fuel validJumps` over `image.bytes ++ suffix` (ABI-encoded constructor
arguments appended after the checked image). -/
theorem VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = []) :
    ∀ fuel,
      EvmYul.EVM.X fuel validJumps gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeIn, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStackLower, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Object.compileVerifiedStackCodeArtifactIn?_parts hCodeIn
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix
  obtain ⟨plan, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Object.verifiedCodeSentinel, List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact (plan.payload ++ suffix))
  have hInitialPoint :=
    Assembly.GasfulBridge.artifactFramePoint_initial hCompact hCode hPc
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        validJumps :=
    Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_compile
      (validJumps := validJumps) hCompact hDecode
  have hStepInv :
      Assembly.GasfulBridge.ArtifactFrameStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        validJumps := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (Assembly.GasfulBridge.artifactFrameStepInvariant_of_ordinaryBoundary
      hCompact hDecode hSentinel hOrdinary) hPoint hPrefix hStep hContinues
  have hFrame :=
    Assembly.GasfulBridge.artifactFrameInvariant_of_step hInitialPoint
      hStepInv
  have hCheck := StackHeadroom.mkCert?_check hCert
  intro fuel
  exact StackHeadroom.x_ne_stackOverflow_of_cert hCompact hDecode hCheck
    hSentinel hFrame hPc hStack fuel

/-- Escape-free refinement for certified artifacts: any `RunRefinesOpen`
witness over the artifact's gasful run strengthens to the variant without
the `stackOverflow` constructor. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
    {fuel : Nat}
    {openRun :
      Simulation.Interaction Assembly.EVMException
        Assembly.StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList artifact.image.bytes)
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = [])
    (hRefines :
      Assembly.GasfulBridge.RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript) :
    StackHeadroom.RunRefinesOpenNoStackOverflow
      (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript :=
  StackHeadroom.runRefinesOpenNoStackOverflow_of_ne hRefines
    (VerifiedStackObjectArtifact.x_ne_stackOverflow hObject hCert hCode hPc
      hStack fuel)

/-- Suffix-tolerant escape-free refinement for creation frames. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
    {fuel : Nat}
    {openRun :
      Simulation.Interaction Assembly.EVMException
        Assembly.StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = [])
    (hRefines :
      Assembly.GasfulBridge.RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript) :
    StackHeadroom.RunRefinesOpenNoStackOverflow
      (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript :=
  StackHeadroom.runRefinesOpenNoStackOverflow_of_ne hRefines
    (VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix suffix
      hObject hCert hCode hPc hStack fuel)

end Frontend
end Solidity
end EvmCompiler
