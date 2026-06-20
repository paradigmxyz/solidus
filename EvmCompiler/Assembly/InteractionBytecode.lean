import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.InteractionPreservation

namespace EvmCompiler
namespace Assembly
namespace Bytecode

namespace InteractionSemantics

/--
Open execution of encoded bytecode.

Instruction decoding is the imported EVM decoder. Once decoded, execution
reuses the Assembly target instruction and primitive kernels, so this boundary
adds no second control interpreter or external-effect semantics.
-/
def openStepResult (bytes : ByteArray) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match EvmYul.EVM.decode bytes state.pc with
  | none =>
      .done (.error .InvalidInstruction)
  | some (op, arg) =>
      match TargetInstr.ofDecoded? op arg with
      | none =>
          .done (.error .InvalidInstruction)
      | some instr =>
          Assembly.InteractionSemantics.Target.openStepInstrResult instr state

def openRunNResult (bytes : ByteArray) (fuel : Nat) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  Assembly.Control.runNResultWith (openStepResult bytes) fuel state

end InteractionSemantics

theorem openStepResult_eq_target_of_fetch
    {target : TargetProgram} {bytes : ByteArray}
    {state : EVMState} {instr : TargetInstr}
    (hDecoding : DecodingCorrect target bytes)
    (hFetch : target.fetch state.pc.toNat = some instr) :
    InteractionSemantics.openStepResult bytes state =
      Assembly.InteractionSemantics.Target.openStepResult target state := by
  obtain ⟨located, hMem, hPc, hInstr⟩ :=
    TargetProgram.exists_located_of_fetch hFetch
  have hDecode := hDecoding.decodes located hMem
  unfold decodeAt at hDecode
  have hPcWord :
      EvmYul.UInt256.ofNat located.pc = state.pc := by
    rw [hPc]
    exact EvmYul.UInt256.ofNat_toNat state.pc
  rw [hPcWord] at hDecode
  subst instr
  unfold InteractionSemantics.openStepResult
  rw [hDecode]
  simp only [TargetInstr.ofDecoded?_op_arg]
  unfold Assembly.InteractionSemantics.Target.openStepResult
    Assembly.Target.stepResultWith
  rw [hFetch]

theorem target_openStepResult_executes_fetch
    {target : TargetProgram} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hExec :
      Simulation.Interaction.Executes
        (Assembly.InteractionSemantics.Target.openStepResult target state)
        transcript (.ok result)) :
    ∃ instr,
      target.fetch state.pc.toNat = some instr ∧
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Target.openStepInstrResult instr state)
          transcript (.ok result) := by
  unfold Assembly.InteractionSemantics.Target.openStepResult
    Assembly.Target.stepResultWith at hExec
  cases hFetch : target.fetch state.pc.toNat with
  | none =>
      rw [hFetch] at hExec
      change
        Simulation.Interaction.Executes
          (.done (.error (.InvalidInstruction : EVMException)))
          transcript (.ok result) at hExec
      cases hExec
  | some instr =>
      rw [hFetch] at hExec
      exact ⟨instr, rfl, hExec⟩

/--
Every successful fetched-target branch is executed by the encoded bytecode
with the same instruction fuel, dependent interaction transcript, and result.
-/
theorem target_openRunNResult_executes_of_decoding
    {target : TargetProgram} {bytes : ByteArray}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hDecoding : DecodingCorrect target bytes)
    (hExec :
      Simulation.Interaction.Executes
        (Assembly.InteractionSemantics.Target.openRunNResult
          target fuel state)
        transcript (.ok result)) :
    Simulation.Interaction.Executes
      (InteractionSemantics.openRunNResult bytes fuel state)
      transcript (.ok result) := by
  induction fuel generalizing state transcript result with
  | zero =>
      change
        Simulation.Interaction.Executes
          (.done (.ok (StepResult.running state)))
          transcript (.ok result) at hExec
      cases hExec
      exact Simulation.Interaction.Executes.done _
  | succ fuel ih =>
      change
        Simulation.Interaction.Executes
          (Simulation.Interaction.bind
            (Assembly.InteractionSemantics.Target.openStepResult target state)
            (fun stepResult =>
              match stepResult with
              | .running mid =>
                  Assembly.InteractionSemantics.Target.openRunNResult
                    target fuel mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)))
          transcript (.ok result) at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hError | hOk
      · rcases hError with ⟨err, hOutcome, hStep⟩
        cases hOutcome
      · rcases hOk with
          ⟨stepResult, headTranscript, restTranscript,
            hTranscript, hStep, hRest⟩
        obtain ⟨instr, hFetch, hInstr⟩ :=
          target_openStepResult_executes_fetch hStep
        have hByteStep :
            Simulation.Interaction.Executes
              (InteractionSemantics.openStepResult bytes state)
              headTranscript (.ok stepResult) := by
          rw [openStepResult_eq_target_of_fetch hDecoding hFetch]
          exact hStep
        subst transcript
        change
          Simulation.Interaction.Executes
            (Simulation.Interaction.bind
              (InteractionSemantics.openStepResult bytes state)
              (fun stepResult =>
                match stepResult with
                | .running mid =>
                    InteractionSemantics.openRunNResult bytes fuel mid
                | .halted halt =>
                    Simulation.Interaction.pure (.halted halt)))
            (headTranscript ++ restTranscript) (.ok result)
        cases stepResult with
        | running mid =>
            exact
              Simulation.Interaction.Executes.bind_ok
                hByteStep (ih hRest)
        | halted halt =>
            exact
              Simulation.Interaction.Executes.bind_ok
                hByteStep hRest

theorem target_openRunNResult_executes
    {target : TargetProgram} {bytes : ByteArray}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hEncoding : EncodingCorrect target bytes)
    (hExec :
      Simulation.Interaction.Executes
        (Assembly.InteractionSemantics.Target.openRunNResult
          target fuel state)
        transcript (.ok result)) :
    Simulation.Interaction.Executes
      (InteractionSemantics.openRunNResult bytes fuel state)
      transcript (.ok result) :=
  target_openRunNResult_executes_of_decoding
    hEncoding.decodingCorrect hExec

/--
Assembly-to-bytecode open-effects theorem.

The compiler equation derives both the encoded bytes and the decoder
certificate. A concrete source branch is then realized by bytecode with the
same exact interaction transcript and terminal result.
-/
theorem compile_openRunNResult_executes
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hWindow : TargetFitsDecodeWindow target)
    (hJumpdest : JumpdestCorrect target)
    (hExec :
      Simulation.Interaction.Executes
        (Assembly.InteractionSemantics.Source.openRunNResult
          program fuel state)
        transcript (.ok result)) :
    Accepted program ∧
      compileBytes? program = some (encodeTarget target) ∧
        EncodingCorrect target (encodeTarget target) ∧
          ∃ targetFuel,
            Simulation.Interaction.Executes
              (InteractionSemantics.openRunNResult
                (encodeTarget target) targetFuel state)
              transcript (.ok result) := by
  have hEncoding :
      EncodingCorrect target (encodeTarget target) :=
    compile_encoding_correct_of_jumpdests hCompile
      (compile_decodeSafety hCompile hWindow) hJumpdest
  have hLen :
      Program.byteLength program < EvmYul.UInt256.size := by
    rw [← compile_codeByteLength hCompile]
    unfold TargetFitsDecodeWindow at hWindow
    unfold EvmYul.UInt256.size
    omega
  obtain ⟨hAccepted, targetFuel, hTarget⟩ :=
    Assembly.InteractionPreservation.compile_openRunNResult_target_executes
      hCompile hLen hExec
  refine ⟨hAccepted, ?_, hEncoding, targetFuel, ?_⟩
  · simp [compileBytes?, hCompile]
  · exact target_openRunNResult_executes hEncoding hTarget

end Bytecode
end Assembly
end EvmCompiler
