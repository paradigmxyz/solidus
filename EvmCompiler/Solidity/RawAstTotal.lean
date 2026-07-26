import EvmCompiler.Solidity.RawAstEndToEnd
import EvmCompiler.Yul.GasfulCrown

/-!
# Raw-solc gasful crown (escape-free bridge)

Lifts the escape-free `RunRefinesOpenTotal` crown from the object level
(`Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal`) to the raw solc
Standard JSON entry point. The premises are exactly those of the existing
raw gasful theorem `optimizedRawSolcIrToGasfulRawBytecode` plus a
stack-headroom certificate for the compiled artifact; the conclusion keeps
the same existential structure and finite-prefix `ForwardRel` at the plain
budget fuel, and upgrades the final conjunct to
`Assembly.GasfulBridge.RunRefinesOpenTotal` at the gas-derived fuel
`max budget (gasAvailable + 6)`:

* `outOfFuel` is removed by the gas-derived structural fuel bound
  (`Assembly.GasfulFuelBound.x_ne_outOfFuel_of_gas_lt_fuel`);
* `stackOverflow` is removed by the validated stack-headroom certificate
  (`VerifiedStackObjectArtifact.x_ne_stackOverflow`);
* `badJumpDestination` is removed by the jumpdest-scan membership theorem
  (`VerifiedStackObjectArtifact.x_ne_badJumpDestination`) against the
  interpreter's own scan of the installed image.

Both the exact runtime image and the creation image with an appended
constructor-argument suffix are covered.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst

/-- Raw-solc crown endpoint: for a checked raw-solc compilation whose
artifact carries a stack-headroom certificate, the charged run at the
gas-derived fuel refines the open run with NO escape constructor. Every
outcome is a related terminal leaf, a collapsed exceptional frame in step
with the open run (with the fuel/stack/jump labels excluded on the charged
side), or the committal out-of-gas halt with pinned frame-boundary rollback
semantics. -/
theorem optimizedRawSolcIrToGasfulRawBytecodeTotal
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {cert : Assembly.StackHeadroom.Cert}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (context : Frontend.ObjectBuiltinContext)
        (structuredFuel : Nat)
        (transcript : Simulation.Interaction.Transcript),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Assembly.Accepted
            artifact.codeArtifact.compiled.certified.target ∧
            Simulation.Interaction.ForwardRel
              Yul.FunctionsInteractionPrimitive.Truncated
              (Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel artifact)
              (Raw.SourcePreservation.rawObjectRun (sourceFuel + 1)
                context selected.root
                (Yul.EndToEnd.installedSourceState artifact baseSource))
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList artifact.image.bytes)
                ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
                { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
                  pc := EvmYul.UInt256.ofNat 0 }) ∧
            Assembly.GasfulBridge.RunRefinesOpenTotal
              (EvmYul.EVM.X
                (max
                  ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
                  (gasfulInitial.gasAvailable.toNat + 6))
                (EvmYul.EVM.D_J
                  (Assembly.Bytecode.ofList artifact.image.bytes)
                  (EvmYul.UInt256.ofNat 0))
                gasfulInitial)
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList artifact.image.bytes)
                (max
                  ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
                  (gasfulInitial.gasAvailable.toNat + 6))
                { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
                  pc := EvmYul.UInt256.ofNat 0 })
              transcript := by
  rcases optimizedRawSolcIrToRawBytecode
      (sourceFuel := sourceFuel) (baseSource := baseSource) hCompile with
    ⟨json, selected, context, structuredFuel,
      hParse, hSelected, hAccepted, hForward⟩
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  have hFrameCode :=
    Yul.EndToEnd.verifiedArtifact_frameCodeInvariant
      hProgramCompile hInitial
  obtain ⟨transcript, hGasful⟩ :=
    Assembly.GasfulBridge.runRefinesOpen_recursive hFrameCode
      (max
        ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
        (gasfulInitial.gasAvailable.toNat + 6))
      Assembly.GasfulBridge.FrameReachable.initial hInitial
  have hCodeEq := Yul.EndToEnd.verifiedArtifact_initial_code_eq hInitial
  have hPcEq := Yul.EndToEnd.verifiedArtifact_initial_pc_eq hInitial
  have hStackEq := Yul.EndToEnd.verifiedArtifact_initial_stack_eq hInitial
  exact
    ⟨json, selected, context, structuredFuel, transcript,
      hParse, hSelected, hAccepted, hForward,
      Assembly.GasfulBridge.runRefinesOpenTotal_of_ne hGasful
        (Assembly.GasfulFuelBound.x_ne_outOfFuel_of_gas_lt_fuel _ _ _
          (Nat.le_max_right _ _))
        (Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow
          hProgramCompile hCert hCodeEq hPcEq hStackEq _)
        (Frontend.VerifiedStackObjectArtifact.x_ne_badJumpDestination
          hProgramCompile hCert hCodeEq hPcEq hStackEq _)⟩

/-- Suffix-tolerant raw-solc crown endpoint (creation frames): no escape
constructor over the installed creation image `image.bytes ++ suffix`,
against the interpreter's own jumpdest scan of that full image. -/
theorem optimizedRawSolcIrToGasfulRawBytecodeTotalWithCodeSuffix
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {cert : Assembly.StackHeadroom.Cert}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (Yul.EndToEnd.initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (context : Frontend.ObjectBuiltinContext)
        (structuredFuel : Nat)
        (transcript : Simulation.Interaction.Transcript),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Assembly.Accepted
            artifact.codeArtifact.compiled.certified.target ∧
            Simulation.Interaction.ForwardRel
              Yul.FunctionsInteractionPrimitive.Truncated
              (Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel artifact)
              (Raw.SourcePreservation.rawObjectRun (sourceFuel + 1)
                context selected.root
                (Yul.EndToEnd.installedSourceStateWithCodeSuffix
                  artifact suffix baseSource))
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
                ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
                { (Yul.EndToEnd.initialExpressionsStateWithCodeSuffix
                    artifact suffix baseSource).evm with
                  pc := EvmYul.UInt256.ofNat 0 }) ∧
            Assembly.GasfulBridge.RunRefinesOpenTotal
              (EvmYul.EVM.X
                (max
                  ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
                  (gasfulInitial.gasAvailable.toNat + 6))
                (EvmYul.EVM.D_J
                  (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
                  (EvmYul.UInt256.ofNat 0))
                gasfulInitial)
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
                (max
                  ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
                  (gasfulInitial.gasAvailable.toNat + 6))
                { (Yul.EndToEnd.initialExpressionsStateWithCodeSuffix
                    artifact suffix baseSource).evm with
                  pc := EvmYul.UInt256.ofNat 0 })
              transcript := by
  rcases optimizedRawSolcIrToRawBytecodeWithCodeSuffix
      (sourceFuel := sourceFuel) (baseSource := baseSource) suffix
      hCompile with
    ⟨json, selected, context, structuredFuel,
      hParse, hSelected, hAccepted, hForward⟩
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  have hFrameCode :=
    Yul.EndToEnd.verifiedArtifact_frameCodeInvariantWithCodeSuffix
      suffix hProgramCompile hInitial
  obtain ⟨transcript, hGasful⟩ :=
    Assembly.GasfulBridge.runRefinesOpen_recursive hFrameCode
      (max
        ((Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body +
                  1) *
              artifact.codeChoice.executionFuelFactor
                artifact.codeArtifact)
        (gasfulInitial.gasAvailable.toNat + 6))
      Assembly.GasfulBridge.FrameReachable.initial hInitial
  have hCodeEq :=
    Yul.EndToEnd.verifiedArtifact_initial_code_eqWithCodeSuffix suffix hInitial
  have hPcEq :=
    Yul.EndToEnd.verifiedArtifact_initial_pc_eqWithCodeSuffix suffix hInitial
  have hStackEq :=
    Yul.EndToEnd.verifiedArtifact_initial_stack_eqWithCodeSuffix suffix hInitial
  exact
    ⟨json, selected, context, structuredFuel, transcript,
      hParse, hSelected, hAccepted, hForward,
      Assembly.GasfulBridge.runRefinesOpenTotal_of_ne hGasful
        (Assembly.GasfulFuelBound.x_ne_outOfFuel_of_gas_lt_fuel _ _ _
          (Nat.le_max_right _ _))
        (Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix
          suffix hProgramCompile hCert hCodeEq hPcEq hStackEq _)
        (Frontend.VerifiedStackObjectArtifact.x_ne_badJumpDestination_withCodeSuffix
          suffix hProgramCompile hCert hCodeEq hPcEq hStackEq _)⟩

end RawAst
end Solidity
end EvmCompiler
