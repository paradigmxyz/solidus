import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Assembly

/--
Runtime assumptions added when the verified AST-level compiler theorem is used
as a claim about actual gasful EVM frame execution.

`decodeWindow` is a decoder-resource bound, not a deployment-size policy; the
actual `DecodeSafety` facts are derived from the checked assembler layout.
`jumpdestCorrect` remains a
bytecode/EVMYulLean scanner boundary because the imported jumpdest scanner is
opaque. The remaining fields name the semantic choices intentionally not
modeled by the cost-free source language or not yet derived by the gasful-target
refinement: gas accounting, possible out-of-gas interruption, and the gas-erased
state projection. Transaction processing and external-program correctness are
not fields of this compiler boundary.
-/
structure RuntimeAssumptions
    (program : Program) (target : TargetProgram) (initial : EVMState) :
    Prop where
    decodeWindow : Bytecode.TargetFitsDecodeWindow target
    jumpdestCorrect : Bytecode.JumpdestCorrect target
    outOfGasPolicy : OutOfGasPolicyAssumption program initial
    currentContractProjection : CurrentContractProjectionAssumption program initial

  namespace RuntimeAssumptions

def withExplicitBoundaries {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (decodeWindow : Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Bytecode.JumpdestCorrect target)
      (outOfGasPolicy : OutOfGasPolicyAssumption program initial)
      (currentContractProjection :
        CurrentContractProjectionAssumption program initial) :
      RuntimeAssumptions program target initial where
    decodeWindow := decodeWindow
    jumpdestCorrect := jumpdestCorrect
    outOfGasPolicy := outOfGasPolicy
    currentContractProjection := currentContractProjection

  def withNoCallCreate {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (decodeWindow : Bytecode.TargetFitsDecodeWindow target)
    (jumpdestCorrect : Bytecode.JumpdestCorrect target)
      (outOfGasPolicy : OutOfGasPolicyAssumption program initial)
      (currentContractProjection :
        CurrentContractProjectionAssumption program initial)
      (hNoCallCreate : program.usesCallCreate = false) :
    RuntimeAssumptions program target initial :=
  let _hNoCallCreate := hNoCallCreate
  withExplicitBoundaries decodeWindow jumpdestCorrect outOfGasPolicy
      currentContractProjection

end RuntimeAssumptions

/--
Public whole-program compiler theorem for the minimal assembly layer.

There is no parser in this theorem: the verified compiler input is the
`Program` AST.  The bytecode component is a one-way encoder proof showing that
the compiled target program produces raw bytes whose EVMYulLean
decoder/fetch behavior matches the target instructions.  The observable
semantic claim is the gas-erased whole-run block trace.
-/
theorem compile_whole_program_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal) :
    Accepted program ∧
      Bytecode.compileBytes? program = some (Bytecode.encodeTarget target) ∧
        Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
          OutOfGasPolicyAssumption program initial ∧
            CurrentContractProjectionAssumption program initial ∧
              ∃ targetFinal,
                Preservation.BlockTrace program target fuel initial targetFinal ∧
                  eraseGas targetFinal = eraseGas sourceFinal := by
  obtain ⟨hAccepted, targetFinal, hEncoding, hTrace, hErase⟩ :=
    Bytecode.compile_runN_bytecode_bridge_checked hCompile
      (Bytecode.compile_decodeSafety hCompile hRuntime.decodeWindow)
      hRuntime.jumpdestCorrect hRun
  refine
    ⟨hAccepted, ?_, hEncoding, hRuntime.outOfGasPolicy,
      hRuntime.currentContractProjection, targetFinal, hTrace, hErase⟩
  simp [Bytecode.compileBytes?, hCompile]

theorem compile_whole_program_result_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial : EVMState}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runNResult program fuel initial = .ok result) :
    Accepted program ∧
      Bytecode.compileBytes? program = some (Bytecode.encodeTarget target) ∧
        Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
          OutOfGasPolicyAssumption program initial ∧
            CurrentContractProjectionAssumption program initial ∧
              Preservation.BlockTraceResult program target fuel initial result := by
  obtain ⟨hAccepted, hEncoding, hTrace⟩ :=
    Bytecode.compile_runN_result_bytecode_bridge_checked hCompile
      (Bytecode.compile_decodeSafety hCompile hRuntime.decodeWindow)
      hRuntime.jumpdestCorrect hRun
  refine
    ⟨hAccepted, ?_, hEncoding, hRuntime.outOfGasPolicy,
      hRuntime.currentContractProjection, hTrace⟩
  simp [Bytecode.compileBytes?, hCompile]

end Assembly
end EvmCompiler
