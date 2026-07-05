import EvmCompiler.Yul.GasfulEndToEnd
import EvmCompiler.Solidity.StackHeadroomEndToEnd
import EvmCompiler.Solidity.JumpTargetEndToEnd

/-!
# Gasful crown endpoint

Composition of the four escape-branch results into a single no-residual
gasful theorem for compiled verified stack object artifacts that carry a
stack-headroom certificate:

* the committal out-of-gas branch (`RunRefinesOpenCommittal` /
  `OutOfGasFrameSemantics`);
* the gas-derived structural fuel bound
  (`Assembly.GasfulFuelBound.x_ne_outOfFuel_of_gas_lt_fuel`), which removes
  `outOfFuel` at fuel `max budget (gasAvailable + 6)`;
* the stack-headroom certificate
  (`VerifiedStackObjectArtifact.x_ne_stackOverflow`), which removes
  `stackOverflow`;
* the jumpdest-scan membership theorem
  (`VerifiedStackObjectArtifact.x_ne_badJumpDestination`), which removes
  `badJumpDestination` against the interpreter's own scan of the installed
  image.

`Assembly.GasfulBridge.RunRefinesOpenTotal` is the bridge relation with no
escape constructor at all: the charged run either completes in refinement
with the open run, collapses an exceptional frame in step with the open run
(with the fuel/stack/jump labels excluded on the charged side), or halts
out-of-gas with the pinned frame-boundary rollback semantics. The crown
endpoints instantiate it on the public gas-bounded spine, for both the exact
runtime image and the creation image with an appended constructor-argument
suffix.
-/

namespace EvmCompiler
namespace Assembly
namespace GasfulBridge

/-- Bridge outcomes with every escape constructor removed. The charged run
either reaches a related terminal leaf, collapses an exceptional frame
together with the open run (and the charged label is provably none of
`OutOfFuel`, `StackOverflow`, `BadJumpDestination`), or halts out-of-gas with
the committal frame-boundary semantics (`Ξ` exceptional halt, `Θ` checkpoint
rollback with zero returned gas, failure flag, empty output). -/
inductive RunRefinesOpenTotal
    (gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (openRun : Simulation.Interaction EVMException StepResult) :
    Simulation.Interaction.Transcript → Prop where
  | completed {transcript openDone} :
      Simulation.Interaction.Executes openRun transcript openDone →
      DoneRel gasful openDone →
      RunRefinesOpenTotal gasful openRun transcript
  | exceptionalFrame {transcript gasErr openErr} :
      gasErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasErr ≠ EvmYul.EVM.ExecutionException.StackOverflow →
      gasErr ≠ EvmYul.EVM.ExecutionException.BadJumpDestination →
      openErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasful = .error gasErr →
      Simulation.Interaction.Executes openRun transcript (.error openErr) →
      RunRefinesOpenTotal gasful openRun transcript
  | outOfGas {transcript} :
      OutOfGasFrameSemantics gasful →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenTotal gasful openRun transcript

/-- Every total bridge outcome is in particular a committal outcome. -/
theorem RunRefinesOpenTotal.toRunRefinesOpenCommittal
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Simulation.Interaction EVMException StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hBridge : RunRefinesOpenTotal gasful openRun transcript) :
    RunRefinesOpenCommittal gasful openRun transcript := by
  cases hBridge with
  | completed hExec hDone => exact .completed hExec hDone
  | exceptionalFrame hGasFuel _hGasStack _hGasJump hOpenErr hGas hExec =>
      exact .exceptionalFrame hGasFuel hOpenErr hGas hExec
  | outOfGas hSem hFollow => exact .outOfGas hSem hFollow

/-- Combined escape pruning from the committal outcome: the two ≠-error facts
about the concrete charged run remove the `stackOverflow` and
`badJumpDestination` constructors and exclude both labels from the
collapsed-frame arm. -/
theorem runRefinesOpenTotal_of_committal
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Simulation.Interaction EVMException StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hBridge : RunRefinesOpenCommittal gasful openRun transcript)
    (hNoStackOverflow :
      gasful ≠ .error EvmYul.EVM.ExecutionException.StackOverflow)
    (hNoBadJump :
      gasful ≠ .error EvmYul.EVM.ExecutionException.BadJumpDestination) :
    RunRefinesOpenTotal gasful openRun transcript := by
  cases hBridge with
  | completed hExec hDone => exact .completed hExec hDone
  | exceptionalFrame hGasErr hOpenErr hGas hExec =>
      refine .exceptionalFrame hGasErr ?_ ?_ hOpenErr hGas hExec
      · intro hLabel
        exact hNoStackOverflow (hLabel ▸ hGas)
      · intro hLabel
        exact hNoBadJump (hLabel ▸ hGas)
  | outOfGas hSem hFollow => exact .outOfGas hSem hFollow
  | badJumpDestination hEq hFollow => exact absurd hEq hNoBadJump
  | stackOverflow hEq hFollow => exact absurd hEq hNoStackOverflow

/-- Combined escape pruning straight from `RunRefinesOpen`: the three
≠-error facts about the concrete charged run remove `outOfFuel`,
`stackOverflow`, and `badJumpDestination` in one conversion. -/
theorem runRefinesOpenTotal_of_ne
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Simulation.Interaction EVMException StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hBridge : RunRefinesOpen gasful openRun transcript)
    (hNoFuelStop :
      gasful ≠ .error EvmYul.EVM.ExecutionException.OutOfFuel)
    (hNoStackOverflow :
      gasful ≠ .error EvmYul.EVM.ExecutionException.StackOverflow)
    (hNoBadJump :
      gasful ≠ .error EvmYul.EVM.ExecutionException.BadJumpDestination) :
    RunRefinesOpenTotal gasful openRun transcript :=
  runRefinesOpenTotal_of_committal
    (runRefinesOpenCommittal_of_not_outOfFuel hBridge hNoFuelStop)
    hNoStackOverflow hNoBadJump

end GasfulBridge
end Assembly

namespace Yul
namespace EndToEnd

/-! ## Initial-state hypothesis reconciliation

The gas-bounded endpoints take `Assembly.GasfulBridge.OpenStateRel` at the
canonical installed open initial state, while the stack-headroom and
bad-jump crowns take the direct `hCode`/`hPc`/`hStack` equalities. The
lemmas below extract the direct equalities from that same `OpenStateRel`
hypothesis: the open initial state installs exactly the artifact byte image,
pc `0`, and an empty operand stack, and `OpenStateRel` preserves all
three. -/

theorem verifiedArtifact_initial_code_eq
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    gasfulInitial.executionEnv.code =
      Assembly.Bytecode.ofList artifact.image.bytes := by
  calc
    gasfulInitial.executionEnv.code =
        ({ (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 } : Assembly.EVMState).executionEnv.code :=
      hInitial.code_eq
    _ = Assembly.Bytecode.ofList artifact.image.bytes := by
      simp [initialExpressionsState, initialFunctionsState,
        Functions.StackRelation.initialTarget, Structured.RunState.initial,
        FunctionsInteractionRelation.ScopedStateRel.initialTarget,
        FunctionsInteractionRelation.ScopedStateRel.installedSourceShared,
        FunctionsInteractionRelation.SharedRel.toEVM,
        FunctionsInteractionRelation.ExecutionEnvRel.toEVM]
      simp [Simulation.OpenWorld.installEVMShared,
        Simulation.OpenWorld.installEVM]

theorem verifiedArtifact_initial_pc_eq
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    gasfulInitial.pc = EvmYul.UInt256.ofNat 0 := by
  simpa using hInitial.pc_eq

theorem verifiedArtifact_initial_stack_eq
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    gasfulInitial.stack = [] := by
  calc
    gasfulInitial.stack =
        ({ (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 } : Assembly.EVMState).stack :=
      hInitial.stack_eq
    _ = [] := by
      simp [initialExpressionsState, initialFunctionsState,
        Functions.StackRelation.initialTarget, Structured.RunState.initial,
        FunctionsInteractionRelation.ScopedStateRel.initialTarget]

theorem verifiedArtifact_initial_code_eqWithCodeSuffix
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    gasfulInitial.executionEnv.code =
      Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix) := by
  calc
    gasfulInitial.executionEnv.code =
        ({ (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 } : Assembly.EVMState).executionEnv.code :=
      hInitial.code_eq
    _ = Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix) := by
      simp [initialExpressionsStateWithCodeSuffix,
        initialFunctionsStateWithCodeSuffix,
        Functions.StackRelation.initialTarget, Structured.RunState.initial,
        FunctionsInteractionRelation.ScopedStateRel.initialTarget,
        FunctionsInteractionRelation.ScopedStateRel.installedSourceShared,
        FunctionsInteractionRelation.SharedRel.toEVM,
        FunctionsInteractionRelation.ExecutionEnvRel.toEVM]
      simp [Simulation.OpenWorld.installEVMShared,
        Simulation.OpenWorld.installEVM]

theorem verifiedArtifact_initial_pc_eqWithCodeSuffix
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    gasfulInitial.pc = EvmYul.UInt256.ofNat 0 := by
  simpa using hInitial.pc_eq

theorem verifiedArtifact_initial_stack_eqWithCodeSuffix
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    gasfulInitial.stack = [] := by
  calc
    gasfulInitial.stack =
        ({ (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 } : Assembly.EVMState).stack :=
      hInitial.stack_eq
    _ = [] := by
      simp [initialExpressionsStateWithCodeSuffix,
        initialFunctionsStateWithCodeSuffix,
        Functions.StackRelation.initialTarget, Structured.RunState.initial,
        FunctionsInteractionRelation.ScopedStateRel.initialTarget]

/-! ## Crown endpoints -/

/-- Crown endpoint: for a compiled artifact with a stack-headroom
certificate, the charged run at the gas-derived fuel refines the open run
with NO escape constructor. Every outcome is a related terminal leaf, a
collapsed exceptional frame in step with the open run, or the committal
out-of-gas halt with pinned frame-boundary rollback semantics. -/
theorem optimizedSolcYulToGasfulRawBytecodeTotal
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {cert : Assembly.StackHeadroom.Cert}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    ∃ structuredFuel transcript,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpenTotal
          (EvmYul.EVM.X
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, transcript, hAccepted, hForward, hCommittal⟩ :=
    optimizedSolcYulToGasfulRawBytecodeGasBoundedCommittal
      (sourceFuel := sourceFuel) hObject hInitial
  have hCode := verifiedArtifact_initial_code_eq hInitial
  have hPc := verifiedArtifact_initial_pc_eq hInitial
  have hStack := verifiedArtifact_initial_stack_eq hInitial
  exact ⟨structuredFuel, transcript, hAccepted, hForward,
    Assembly.GasfulBridge.runRefinesOpenTotal_of_committal hCommittal
      (Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow
        hObject hCert hCode hPc hStack _)
      (Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_badJumpDestination
        hObject hCode hPc _)⟩

/-- Crown endpoint for every genuinely finished source tree: the
finite-prefix `ForwardRel` upgrades to a full open-world `Rel`, and the
gasful bridge at the gas-derived fuel has no escape constructor. -/
theorem optimizedSolcYulToGasfulRawBytecodeFinishedTotal
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {cert : Assembly.StackHeadroom.Cert}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 })
    (hFinished : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceFinished
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (installedSourceState artifact baseSource))) :
    ∃ structuredFuel transcript,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpenTotal
          (EvmYul.EVM.X
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, transcript, hAccepted, hRel, hHalting⟩ :=
    optimizedSolcYulToGasfulRawBytecodeFinishedGasBounded
      (sourceFuel := sourceFuel) hObject hInitial hFinished
  have hCode := verifiedArtifact_initial_code_eq hInitial
  have hPc := verifiedArtifact_initial_pc_eq hInitial
  have hStack := verifiedArtifact_initial_stack_eq hInitial
  exact ⟨structuredFuel, transcript, hAccepted, hRel,
    Assembly.GasfulBridge.runRefinesOpenTotal_of_committal
      (Assembly.GasfulBridge.runRefinesOpenCommittal_of_halting hHalting)
      (Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow
        hObject hCert hCode hPc hStack _)
      (Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_badJumpDestination
        hObject hCode hPc _)⟩

/-- Crown endpoint for source trees whose every branch halts. -/
theorem optimizedSolcYulToGasfulRawBytecodeTerminalTotal
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {cert : Assembly.StackHeadroom.Cert}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 })
    (hTerminal : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceTerminal
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (installedSourceState artifact baseSource))) :
    ∃ structuredFuel transcript,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpenTotal
          (EvmYul.EVM.X
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript :=
  optimizedSolcYulToGasfulRawBytecodeFinishedTotal
    (sourceFuel := sourceFuel) hObject hCert hInitial
    (Simulation.Interaction.AllDone.mono hTerminal
      (fun sourceDone hSourceTerminal =>
        FunctionsInteractionProgram.SourceFinished.of_terminal
          hSourceTerminal))

/-! ## Suffix-tolerant crown (creation frames) -/

/-- Suffix-tolerant gas-bounded endpoint: the recursive frame bridge at
`max budget (gasAvailable + 6)` over the creation image
`image.bytes ++ suffix`, with the structural fuel escape discharged by the
gas-derived fuel bound. -/
theorem optimizedSolcYulToGasfulRawBytecodeGasBoundedWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    ∃ structuredFuel transcript,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceStateWithCodeSuffix artifact suffix baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsStateWithCodeSuffix
                artifact suffix baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpenHalting
          (EvmYul.EVM.X
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            { (initialExpressionsStateWithCodeSuffix
                artifact suffix baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, hAccepted, hForward⟩ :=
    optimizedSolcYulToRawBytecodeWithCodeSuffix (sourceFuel := sourceFuel)
      (baseSource := baseSource) suffix hObject
  have hInitialPoint :=
    verifiedArtifact_initialArtifactFramePointWithCodeSuffix suffix hObject
      hInitial
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0)) :=
    verifiedArtifact_ordinaryBoundaryInvariantWithCodeSuffix suffix hObject
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.UInt256.ofNat 0))
  have hStepInvariant : Assembly.GasfulBridge.ArtifactFrameStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.UInt256.ofNat 0)) := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (verifiedArtifact_frameStepInvariant_of_ordinaryBoundaryWithCodeSuffix
      (validJumps := EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.UInt256.ofNat 0)) suffix hObject hOrdinary)
      hPoint hPrefix hStep hContinues
  have hFrame := Assembly.GasfulBridge.artifactFrameInvariant_of_step
    hInitialPoint hStepInvariant
  have hLayout :=
    verifiedArtifact_frameLayoutInvariant_of_artifactFrameInvariantWithCodeSuffix
      suffix hObject hFrame
  have hCode :=
    verifiedArtifact_frameCodeInvariant_of_layoutWithCodeSuffix suffix hObject
      hLayout
  obtain ⟨transcript, hGasful⟩ :=
    Assembly.GasfulBridge.runRefinesOpen_recursive hCode
      (max
        (2 *
          ((Structured.InteractionStaticCost.blockBudget
              artifact.codeArtifact.compiled.expressions.toStructured
              structuredFuel
              artifact.codeArtifact.compiled.expressions.toStructured.body +
                1) *
            TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
              artifact.codeArtifact.compiled.cfg))
        (gasfulInitial.gasAvailable.toNat + 6))
      Assembly.GasfulBridge.FrameReachable.initial hInitial
  refine ⟨structuredFuel, transcript, hAccepted, hForward, ?_⟩
  exact Assembly.GasfulBridge.runRefinesOpenHalting_of_not_outOfFuel hGasful
    (Assembly.GasfulFuelBound.x_ne_outOfFuel_of_gas_lt_fuel _ _ _
      (Nat.le_max_right _ _))

/-- Suffix-tolerant crown endpoint (creation frames): no escape constructor
over the installed creation image `image.bytes ++ suffix`, against the
interpreter's own jumpdest scan of that full image. -/
theorem optimizedSolcYulToGasfulRawBytecodeTotalWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {cert : Assembly.StackHeadroom.Cert}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    ∃ structuredFuel transcript,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceStateWithCodeSuffix artifact suffix baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsStateWithCodeSuffix
                artifact suffix baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpenTotal
          (EvmYul.EVM.X
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            { (initialExpressionsStateWithCodeSuffix
                artifact suffix baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, transcript, hAccepted, hForward, hHalting⟩ :=
    optimizedSolcYulToGasfulRawBytecodeGasBoundedWithCodeSuffix
      (sourceFuel := sourceFuel) suffix hObject hInitial
  have hCode := verifiedArtifact_initial_code_eqWithCodeSuffix suffix hInitial
  have hPc := verifiedArtifact_initial_pc_eqWithCodeSuffix suffix hInitial
  have hStack :=
    verifiedArtifact_initial_stack_eqWithCodeSuffix suffix hInitial
  exact ⟨structuredFuel, transcript, hAccepted, hForward,
    Assembly.GasfulBridge.runRefinesOpenTotal_of_committal
      (Assembly.GasfulBridge.runRefinesOpenCommittal_of_halting hHalting)
      (Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix
        suffix hObject hCert hCode hPc hStack _)
      (Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_badJumpDestination_withCodeSuffix
        suffix hObject hCode hPc _)⟩

end EndToEnd
end Yul
end EvmCompiler
