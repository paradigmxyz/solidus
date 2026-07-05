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

theorem target_openStepResult_fetch_of_successful
    {target : TargetProgram} {state : EVMState}
    (hSuccessful : Simulation.Interaction.Successful
      (Assembly.InteractionSemantics.Target.openStepResult target state)) :
    ∃ instr, target.fetch state.pc.toNat = some instr := by
  obtain ⟨transcript, outcome, hExec, hOutcome⟩ :=
    Simulation.Interaction.AllDone.exists_executes hSuccessful
  cases outcome with
  | error error => cases hOutcome
  | ok result =>
      obtain ⟨instr, hFetch, _hInstr⟩ :=
        target_openStepResult_executes_fetch hExec
      exact ⟨instr, hFetch⟩

/-- On a universally terminal compiler-produced run, payload-aware byte
decoding is not merely forward executable: the raw byte and retained Assembly
interaction trees are equal. This is the final adjacent reverse fact needed
for concrete resource replay, not a cross-pass backward-adequacy theorem. -/
theorem openRunNResult_eq_target_of_decoding_terminal
    {target : TargetProgram} {bytes : ByteArray}
    {fuel : Nat} {state : EVMState}
    (hDecoding : DecodingCorrect target bytes)
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Target.openRunNResult
        target fuel state)) :
    InteractionSemantics.openRunNResult bytes fuel state =
      Assembly.InteractionSemantics.Target.openRunNResult
        target fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      change
        Simulation.Interaction.bind
            (InteractionSemantics.openStepResult bytes state)
            (fun result =>
              match result with
              | .running mid =>
                  InteractionSemantics.openRunNResult bytes fuel mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)) =
          Simulation.Interaction.bind
            (Assembly.InteractionSemantics.Target.openStepResult target state)
            (fun result =>
              match result with
              | .running mid =>
                  Assembly.InteractionSemantics.Target.openRunNResult
                    target fuel mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt))
      have hStep := Simulation.Interaction.AllDone.bind_inv hTerminal
      have hStepSuccessful : Simulation.Interaction.Successful
          (Assembly.InteractionSemantics.Target.openStepResult
            target state) := by
        apply Simulation.Interaction.AllDone.mono hStep
        intro outcome hOutcome
        cases outcome with
        | error error => exact hOutcome
        | ok result => trivial
      obtain ⟨instr, hFetch⟩ :=
        target_openStepResult_fetch_of_successful hStepSuccessful
      rw [openStepResult_eq_target_of_fetch hDecoding hFetch]
      apply Simulation.Interaction.AllDone.bind_congr hStep
      intro result hResult
      cases result with
      | running mid => exact ih hResult
      | halted halt => rfl

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

end Bytecode
end Assembly
end EvmCompiler
