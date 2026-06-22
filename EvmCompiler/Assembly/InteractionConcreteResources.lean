import EvmCompiler.Assembly.InteractionSemantics

namespace EvmCompiler
namespace Assembly
namespace InteractionConcreteResources

open Simulation

/-
These observers are concrete relative to the current gas-erased Assembly
machine state: `MSIZE` reads that state's active-memory field and `GAS` reads
its stored gas field. This module does not charge instruction gas or prove a
refinement from fork-specific, out-of-gas-aware EVM execution. That outer
bridge is a separate production obligation.
-/

/-- Re-emit every open request while also retaining its ordered exchange in
the successful result. `prior` contains already concretized resource and
external effects. -/
def recordRequestsFrom {Error Result : Type}
    (prior : Interaction.Transcript) :
    Interaction Error Result ->
      Interaction Error (Result × Interaction.Transcript)
  | .done (.error error) => .done (.error error)
  | .done (.ok result) => .done (.ok (result, prior))
  | .request query resume =>
      .request query fun answer =>
        recordRequestsFrom
          (prior ++ [{ query := query, answer := answer }])
          (resume answer)

theorem recordRequestsFrom_executes
    {Error Result : Type}
    {prior external full : Interaction.Transcript}
    {interaction : Interaction Error Result} {result : Result}
    (hExec : Interaction.Executes
      (recordRequestsFrom prior interaction)
      external (.ok (result, full))) :
    full = prior ++ external ∧
      Interaction.Executes interaction external (.ok result) := by
  induction interaction generalizing prior external result full with
  | done outcome =>
      cases outcome with
      | error error => cases hExec
      | ok value =>
          cases hExec
          exact ⟨by simp, Interaction.Executes.done _⟩
  | request query resume ih =>
      cases hExec with
      | request answer hTail =>
          obtain ⟨hFull, hOriginal⟩ := ih answer hTail
          refine ⟨?_, Interaction.Executes.request answer hOriginal⟩
          simpa [List.append_assoc] using hFull

def resourceKind? : TargetInstr -> Option ResourceQuery
  | .prim .gas => some .gas
  | .prim .msize => some .msize
  | _ => none

def resourceValue (kind : ResourceQuery) (state : EVMState) : Word :=
  match kind with
  | .gas => EvmYul.MachineState.gas state.toMachineState
  | .msize => EvmYul.MachineState.msize state.toMachineState

def resourceExchange (kind : ResourceQuery) (value : Word) :
    Interaction.Exchange :=
  match kind with
  | .gas => { query := .resource .gas, answer := value }
  | .msize => { query := .resource .msize, answer := value }

def resourceResult (kind : ResourceQuery) (state : EVMState) : StepResult :=
  .running
    (state.replaceStackAndIncrPC
      (state.stack.push (resourceValue kind state)))

/-- One target instruction with model-state resource observers and open
external effects. The result carries the exact interleaved transcript prefix. -/
def stepInstrResultWithPrefix (instr : TargetInstr) (state : EVMState)
    (prior : Interaction.Transcript) :
    Interaction EVMException (StepResult × Interaction.Transcript) :=
  match resourceKind? instr with
  | some kind =>
      let value := resourceValue kind state
      .done
        (.ok
          (resourceResult kind state,
            prior ++ [resourceExchange kind value]))
  | none =>
      recordRequestsFrom prior
        (InteractionSemantics.Target.openStepInstrResult instr state)

theorem openStepInstrResult_executes_of_resource
    {instr : TargetInstr} {state : EVMState}
    {kind : ResourceQuery}
    (hResource : resourceKind? instr = some kind) :
    Interaction.Executes
      (InteractionSemantics.Target.openStepInstrResult instr state)
      [resourceExchange kind (resourceValue kind state)]
      (.ok (resourceResult kind state)) := by
  cases instr with
  | push32 value => simp [resourceKind?] at hResource
  | jump => simp [resourceKind?] at hResource
  | jumpi => simp [resourceKind?] at hResource
  | jumpdest => simp [resourceKind?] at hResource
  | prim op =>
      cases op <;> simp [resourceKind?] at hResource
      · cases hResource
        change Interaction.Executes
          (.request (.resource .msize) fun observed =>
            .done (.ok
              (StepResult.running
                (state.replaceStackAndIncrPC
                  (state.stack.push observed)))))
          [{ query := .resource .msize
             answer := EvmYul.MachineState.msize state.toMachineState }]
          (.ok
            (StepResult.running
              (state.replaceStackAndIncrPC
                (state.stack.push
                  (EvmYul.MachineState.msize state.toMachineState)))))
        exact Interaction.Executes.request _ (Interaction.Executes.done _)
      · cases hResource
        change Interaction.Executes
          (.request (.resource .gas) fun observed =>
            .done (.ok
              (StepResult.running
                (state.replaceStackAndIncrPC
                  (state.stack.push observed)))))
          [{ query := .resource .gas
             answer := EvmYul.MachineState.gas state.toMachineState }]
          (.ok
            (StepResult.running
              (state.replaceStackAndIncrPC
                (state.stack.push
                  (EvmYul.MachineState.gas state.toMachineState)))))
        exact Interaction.Executes.request _ (Interaction.Executes.done _)

def openStepResultWithPrefix (target : TargetProgram) (state : EVMState)
    (prior : Interaction.Transcript) :
    Interaction EVMException (StepResult × Interaction.Transcript) :=
  match target.fetch state.pc.toNat with
  | none => .done (.error .InvalidInstruction)
  | some instr => stepInstrResultWithPrefix instr state prior

theorem openStepResultWithPrefix_executes
    {target : TargetProgram} {state : EVMState}
    {prior external full : Interaction.Transcript}
    {result : StepResult}
    (hExec : Interaction.Executes
      (openStepResultWithPrefix target state prior)
      external (.ok (result, full))) :
    ∃ transcript,
      full = prior ++ transcript ∧
        Interaction.Executes
          (InteractionSemantics.Target.openStepResult target state)
          transcript (.ok result) := by
  unfold openStepResultWithPrefix at hExec
  cases hFetch : target.fetch state.pc.toNat with
  | none =>
      rw [hFetch] at hExec
      cases hExec
  | some instr =>
      simp only [hFetch] at hExec
      unfold stepInstrResultWithPrefix at hExec
      cases hResource : resourceKind? instr with
      | none =>
          simp only [hResource] at hExec
          obtain ⟨hFull, hInstr⟩ :=
            recordRequestsFrom_executes hExec
          refine ⟨external, hFull, ?_⟩
          unfold InteractionSemantics.Target.openStepResult
            Target.stepResultWith
          rw [hFetch]
          exact hInstr
      | some kind =>
          simp only [hResource] at hExec
          cases hExec
          refine
            ⟨[resourceExchange kind (resourceValue kind state)], rfl, ?_⟩
          unfold InteractionSemantics.Target.openStepResult
            Target.stepResultWith
          rw [hFetch]
          exact openStepInstrResult_executes_of_resource hResource

def openRunNResultWithPrefix (target : TargetProgram) :
    Nat -> EVMState -> Interaction.Transcript ->
      Interaction EVMException (StepResult × Interaction.Transcript)
  | 0, state, prior => .done (.ok (.running state, prior))
  | fuel + 1, state, prior => do
      let (stepResult, afterStep) ←
        openStepResultWithPrefix target state prior
      match stepResult with
      | .running mid => openRunNResultWithPrefix target fuel mid afterStep
      | .halted halt => .done (.ok (.halted halt, afterStep))

def openRunNResult (target : TargetProgram) (fuel : Nat)
    (state : EVMState) :
    Interaction EVMException (StepResult × Interaction.Transcript) :=
  openRunNResultWithPrefix target fuel state []

theorem openRunNResultWithPrefix_executes
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {prior external full : Interaction.Transcript}
    {result : StepResult}
    (hExec : Interaction.Executes
      (openRunNResultWithPrefix target fuel state prior)
      external (.ok (result, full))) :
    ∃ transcript,
      full = prior ++ transcript ∧
        Interaction.Executes
          (InteractionSemantics.Target.openRunNResult target fuel state)
          transcript (.ok result) := by
  induction fuel generalizing state prior external full result with
  | zero =>
      change Interaction.Executes
        (.done (.ok (StepResult.running state, prior)))
        external (.ok (result, full)) at hExec
      cases hExec
      exact ⟨[], by simp, Interaction.Executes.done _⟩
  | succ fuel ih =>
      change Interaction.Executes
        (Interaction.bind
          (openStepResultWithPrefix target state prior)
          (fun step =>
            match step.1 with
            | .running mid =>
                openRunNResultWithPrefix target fuel mid step.2
            | .halted halt =>
                .done (.ok (.halted halt, step.2))))
        external (.ok (result, full)) at hExec
      rcases Interaction.Executes.bind_cases hExec with hError | hOk
      · rcases hError with ⟨error, hOutcome, _hStep⟩
        cases hOutcome
      · rcases hOk with
          ⟨step, headExternal, restExternal, hExternal,
            hStep, hRest⟩
        rcases step with ⟨stepResult, afterStep⟩
        obtain ⟨headTranscript, hAfterStep, hTargetStep⟩ :=
          openStepResultWithPrefix_executes hStep
        cases stepResult with
        | running mid =>
            obtain ⟨restTranscript, hFull, hTargetRest⟩ := ih hRest
            refine ⟨headTranscript ++ restTranscript, ?_, ?_⟩
            · rw [hFull, hAfterStep, List.append_assoc]
            · change Interaction.Executes
                (Interaction.bind
                  (InteractionSemantics.Target.openStepResult target state)
                  (fun stepResult =>
                    match stepResult with
                    | .running next =>
                        InteractionSemantics.Target.openRunNResult
                          target fuel next
                    | .halted halt =>
                        Interaction.pure (.halted halt)))
                (headTranscript ++ restTranscript) (.ok result)
              exact Interaction.Executes.bind_ok
                hTargetStep hTargetRest
        | halted halt =>
            change Interaction.Executes
              (.done (.ok (StepResult.halted halt, afterStep)))
              restExternal (.ok (result, full)) at hRest
            cases hRest
            refine ⟨headTranscript, hAfterStep, ?_⟩
            change Interaction.Executes
              (Interaction.bind
                (InteractionSemantics.Target.openStepResult target state)
                (fun stepResult =>
                  match stepResult with
                  | .running next =>
                      InteractionSemantics.Target.openRunNResult
                        target fuel next
                  | .halted final =>
                      Interaction.pure (.halted final)))
              headTranscript (.ok (.halted halt))
            simpa using Interaction.Executes.bind_ok
              (next := fun stepResult =>
                match stepResult with
                | .running next =>
                    InteractionSemantics.Target.openRunNResult
                      target fuel next
                | .halted final =>
                    Interaction.pure (.halted final))
              hTargetStep (Interaction.Executes.done _)

theorem openRunNResult_executes
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {external full : Interaction.Transcript} {result : StepResult}
    (hExec : Interaction.Executes
      (openRunNResult target fuel state)
      external (.ok (result, full))) :
    Interaction.Executes
      (InteractionSemantics.Target.openRunNResult target fuel state)
      full (.ok result) := by
  obtain ⟨transcript, hFull, hTarget⟩ :=
    openRunNResultWithPrefix_executes hExec
  simpa using hFull ▸ hTarget

end InteractionConcreteResources
end Assembly
end EvmCompiler
