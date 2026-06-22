import EvmCompiler.Assembly.Semantics
import EvmCompiler.Simulation.Interaction

namespace EvmCompiler
namespace Assembly
namespace InteractionSemantics

abbrev OpenStep :=
  Simulation.Interaction EVMException EVMState

abbrev OpenStepResult :=
  Simulation.Interaction EVMException StepResult

/-- Every open branch terminates successfully with an EVM halt. -/
def Terminal : Except EVMException StepResult -> Prop
  | .ok result => result.IsTerminal
  | .error _ => False

namespace Terminal

def SafeAt (kind : HaltKind) (state : EVMState) : Prop :=
  exists final,
    Target.stepInstr (.prim kind.toPrimOp) state = .ok final

theorem SafeAt.of_sameRuntimeData
    {kind : HaltKind} {target source : EVMState}
    (hRel : SameRuntimeData target source)
    (hSafe : SafeAt kind source) :
    SafeAt kind target := by
  rcases hSafe with ⟨sourceFinal, hSource⟩
  change kind.toPrimOp.step source = .ok sourceFinal at hSource
  have hCongruence :=
    PrimOp.terminal_step_map_eraseRuntimeControl kind hRel
  cases hTarget : kind.toPrimOp.step target with
  | error error =>
      rw [hTarget, hSource] at hCongruence
      simp [Except.map] at hCongruence
  | ok targetFinal =>
      exact ⟨targetFinal, by
        change kind.toPrimOp.step target = .ok targetFinal
        exact hTarget⟩

theorem successful
    {run : Simulation.Interaction EVMException StepResult}
    (hTerminal : Simulation.Interaction.AllDone Terminal run) :
    Simulation.Interaction.Successful run := by
  apply Simulation.Interaction.AllDone.mono hTerminal
  intro outcome hOutcome
  cases outcome with
  | error error => cases hOutcome
  | ok result => trivial

end Terminal

namespace Instr

@[simp] theorem classifyFlowWith_result
    (continueTransfer : Instr -> Bool) (instr : Instr)
    (before : EVMState) (result : StepResult) :
    (instr.classifyFlowWith continueTransfer before result).result = result := by
  cases result with
  | halted halt => rfl
  | running after =>
      cases instr with
      | label name | prim name | push name | pushLabel name =>
          simp [Assembly.Instr.classifyFlowWith, FlowStep.result]
      | jump name =>
          by_cases hContinue : continueTransfer (.jump name) = true <;>
            simp [Assembly.Instr.classifyFlowWith, FlowStep.result, hContinue]
      | jumpi target =>
          cases hPop : before.stack.pop with
          | none =>
              simp [Assembly.Instr.classifyFlowWith, FlowStep.result, hPop]
          | some pair =>
              rcases pair with ⟨rest, cond⟩
              by_cases hZero : cond = EvmYul.UInt256.ofNat 0
              · simp [Assembly.Instr.classifyFlowWith, FlowStep.result,
                  hPop, hZero]
              · by_cases hContinue :
                    continueTransfer (.jumpi target) = true <;>
                  simp [Assembly.Instr.classifyFlowWith, FlowStep.result,
                    hPop, hZero, hContinue]
      | jumpDynamic =>
          by_cases hContinue : continueTransfer .jumpDynamic = true <;>
            simp [Assembly.Instr.classifyFlowWith, FlowStep.result, hContinue]

end Instr

namespace Control

theorem openRunNResultWith_add
    (step : EVMState → OpenStepResult)
    (first second : Nat) (state : EVMState) :
    Assembly.Control.runNResultWith step (first + second) state =
      (do
        let result ←
          Assembly.Control.runNResultWith step first state
        match result with
        | .running mid =>
            Assembly.Control.runNResultWith step second mid
        | .halted halt =>
            pure (.halted halt)) := by
  induction first generalizing state with
  | zero =>
      rw [Nat.zero_add]
      simp only [Assembly.Control.runNResultWith]
      change
        Assembly.Control.runNResultWith step second state =
          Simulation.Interaction.bind
            (Simulation.Interaction.pure
              (Error := EVMException) (StepResult.running state))
            (fun result =>
              match result with
              | StepResult.running mid =>
                  Assembly.Control.runNResultWith step second mid
              | StepResult.halted halt =>
                  Simulation.Interaction.pure (StepResult.halted halt))
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [Assembly.Control.runNResultWith]
      change
        Simulation.Interaction.bind (step state)
            (fun result =>
              match result with
              | .running state' =>
                  Assembly.Control.runNResultWith
                    step (first + second) state'
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind (step state)
              (fun result =>
                match result with
                | .running state' =>
                    Assembly.Control.runNResultWith step first state'
                | .halted halt =>
                    Simulation.Interaction.pure (.halted halt)))
            (fun result =>
              match result with
              | .running mid =>
                  Assembly.Control.runNResultWith step second mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt))
      rw [Simulation.Interaction.bind_assoc]
      congr
      funext result
      cases result with
      | running mid =>
          exact ih mid
      | halted halt =>
          rfl

end Control

namespace EVMState

def installWorld (state : EVMState) (world : Simulation.OpenWorld) :
    EVMState :=
  { state with
    toSharedState :=
      Simulation.OpenWorld.installEVMShared state.toSharedState world }

def finishCall (state : EVMState) (rest : EvmYul.Stack Word)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse) : EVMState :=
  let withWorld := installWorld state response.postWorld
  let machine :=
    callLocal.finishMachine state.toMachineState response.returnData
  EvmYul.EVM.State.incrPC
    { withWorld with
      toMachineState := machine
      stack := response.statusWord :: rest }

def finishCreate (state : EVMState) (rest : EvmYul.Stack Word)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse) : EVMState :=
  let withWorld := installWorld state response.postWorld
  let machine :=
    createLocal.finishMachine state.toMachineState response.returnData
  EvmYul.EVM.State.incrPC
    { withWorld with
      toMachineState := machine
      stack := response.address :: rest }

end EVMState

namespace PrimOp

def resourceStep (kind : Simulation.ResourceQuery)
    (state : EVMState) : OpenStep :=
  .request (.resource kind) fun value =>
    .done
      (.ok
        (state.replaceStackAndIncrPC (state.stack.push value)))

def callStep (kind : Simulation.CallKind)
    (state : EVMState) : OpenStep :=
  match kind.evmOperands? state.stack with
  | none => .done (.error .StackUnderflow)
  | some (rest, operands) =>
      let frame := Simulation.ExternalFrame.ofShared state.toSharedState
      if kind.allowedIn frame operands then
        let callLocal := operands.callLocal
        let request := frame.callRequest kind operands
        let world := Simulation.OpenWorld.ofEVMShared state.toSharedState
        .request (.external world (.call request)) fun response =>
          .done
            (.ok
              (EVMState.finishCall state rest callLocal response))
      else
        .done (.error .StaticModeViolation)

def createStep (kind : Simulation.CreateKind)
    (state : EVMState) : OpenStep :=
  match kind.evmOperands? state.stack with
  | none => .done (.error .StackUnderflow)
  | some (rest, operands) =>
      let frame := Simulation.ExternalFrame.ofShared state.toSharedState
      if frame.permission then
        let createLocal := operands.createLocal
        let request := frame.createRequest kind operands
        let world := Simulation.OpenWorld.ofEVMShared state.toSharedState
        .request (.external world (.create request)) fun response =>
          .done
            (.ok
              (EVMState.finishCreate state rest createLocal response))
      else
        .done (.error .StaticModeViolation)

/--
Open primitive semantics for the Assembly owner.

Ordinary primitives embed their existing semantics. `gas` and `msize` suspend
at resource queries, while every CALL/CREATE-family primitive suspends at the
one shared open-world protocol.
-/
def openStep (op : Assembly.PrimOp) (state : EVMState) : OpenStep :=
  match Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some (.call kind) => callStep kind state
  | some (.create kind) => createStep kind state
  | none =>
      match op with
      | .gas => resourceStep .gas state
      | .msize => resourceStep .msize state
      | _ => .done (op.step state)

theorem openStep_closed
    {op : Assembly.PrimOp} {state : EVMState}
    (hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM = none)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    openStep op state = .done (op.step state) := by
  cases op <;>
    simp [openStep, hExternal] at hGas hMsize ⊢

theorem externalKind_none_of_continuingStep
    {op : Assembly.PrimOp} {step : Assembly.PrimStep}
    (hStep : op.continuingStep? = some step) :
    Simulation.ExternalKind.ofEVMOperation? op.toEVM = none := by
  cases op <;>
    first
    | rfl
    | simp [Assembly.PrimOp.continuingStep?] at hStep

/-- Every non-resource continuing primitive is a closed interaction. -/
theorem openStep_of_continuingStep
    {op : Assembly.PrimOp} {step : Assembly.PrimStep} {state : EVMState}
    (hStep : op.continuingStep? = some step)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize) :
    openStep op state = .done (step.run state) := by
  have hExternal := externalKind_none_of_continuingStep hStep
  rw [openStep_closed hExternal hGas hMsize]
  exact congrArg Simulation.Interaction.done
    (Assembly.PrimOp.step_eq_continuingStep_run hStep state)

@[simp] theorem openStep_gas (state : EVMState) :
    openStep .gas state = resourceStep .gas state := rfl

@[simp] theorem openStep_msize (state : EVMState) :
    openStep .msize state = resourceStep .msize state := rfl

@[simp] theorem openStep_call (state : EVMState) :
    openStep .call state = callStep .call state := rfl

@[simp] theorem openStep_callcode (state : EVMState) :
    openStep .callcode state = callStep .callcode state := rfl

@[simp] theorem openStep_delegatecall (state : EVMState) :
    openStep .delegatecall state = callStep .delegatecall state := rfl

@[simp] theorem openStep_staticcall (state : EVMState) :
    openStep .staticcall state = callStep .staticcall state := rfl

@[simp] theorem openStep_create (state : EVMState) :
    openStep .create state = createStep .create state := rfl

@[simp] theorem openStep_create2 (state : EVMState) :
    openStep .create2 state = createStep .create2 state := rfl

end PrimOp

namespace Target

def openStepPush (width : Nat) (value : Word) (state : EVMState) : OpenStep :=
  Assembly.Target.stepPushWith
    (fun next => .done (.ok next)) width value state

def openStepPushResult (width : Nat) (value : Word)
    (state : EVMState) : OpenStepResult :=
  Simulation.Interaction.map StepResult.running
    (openStepPush width value state)

def openStepInstr (instr : TargetInstr) (state : EVMState) : OpenStep :=
  Assembly.Target.stepInstrWith
    (fun next => .done (.ok next))
    (fun err => .done (.error err))
    PrimOp.openStep instr state

def openStepInstrResult (instr : TargetInstr) (state : EVMState) :
    OpenStepResult :=
  Assembly.Target.stepInstrResultWith openStepInstr instr state

def openRunList (code : List TargetInstr) (state : EVMState) : OpenStep :=
  Assembly.Target.runListWith openStepInstr code state

def openRunListResult (code : List TargetInstr) (state : EVMState) :
    OpenStepResult :=
  Assembly.Target.runListResultWith openStepInstrResult code state

def openStep (target : TargetProgram) (state : EVMState) : OpenStep :=
  Assembly.Target.stepWith openStepInstr target state

def openStepResult (target : TargetProgram) (state : EVMState) :
    OpenStepResult :=
  Assembly.Target.stepResultWith openStepInstrResult target state

def openRunN (target : TargetProgram) (fuel : Nat) (state : EVMState) :
    OpenStep :=
  Assembly.Target.runNWith openStepInstr target fuel state

def openRunNResult (target : TargetProgram) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Target.runNResultWith openStepInstrResult target fuel state

theorem openRunNResult_add
    (target : TargetProgram) (first second : Nat)
    (state : EVMState) :
    openRunNResult target (first + second) state =
      (do
        let result ← openRunNResult target first state
        match result with
        | .running mid =>
            openRunNResult target second mid
        | .halted halt =>
            pure (.halted halt)) := by
  exact
    Control.openRunNResultWith_add
      (Assembly.Target.stepResultWith openStepInstrResult target)
      first second state

/-- Once a fetched target run halts, any additional instruction fuel is inert. -/
theorem openRunNResult_halted_add_executes
    {target : TargetProgram} {fuel extra : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript} {halt : Halt}
    (hExec : Simulation.Interaction.Executes
      (openRunNResult target fuel state) transcript (.ok (.halted halt))) :
    Simulation.Interaction.Executes
      (openRunNResult target (fuel + extra) state)
      transcript (.ok (.halted halt)) := by
  rw [openRunNResult_add]
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok
      (next := fun result =>
        match result with
        | .running mid => openRunNResult target extra mid
        | .halted final => Simulation.Interaction.pure (.halted final))
      hExec
      (Simulation.Interaction.Executes.done
        (.ok (StepResult.halted halt) : Except EVMException StepResult))
  simpa using hCombined

end Target

namespace Source

def openStepAt (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : OpenStep :=
  match instr with
  | .prim op => PrimOp.openStep op state
  | _ => .done (Assembly.Source.stepAt program pc instr state)

def openStepAtResult (program : Program) (pc : Nat) (instr : Instr)
    (state : EVMState) : OpenStepResult := do
  let state' ← openStepAt program pc instr state
  match instr.haltKind? with
  | some kind =>
      pure (.halted { kind := kind, state := state', output := kind.output state' })
  | none =>
      pure (.running state')

def openStep (program : Program) (state : EVMState) : OpenStep :=
  Assembly.Source.stepWith (openStepAt program) program state

def openStepResult (program : Program) (state : EVMState) :
    OpenStepResult :=
  Assembly.Source.stepResultWith (openStepAtResult program) program state

def openRunN (program : Program) (fuel : Nat) (state : EVMState) :
    OpenStep :=
  Assembly.Control.runNWith (openStep program) fuel state

def openRunNResult (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Control.runNResultWith (openStepResult program) fuel state

@[simp] theorem openRunNResult_zero
    (program : Program) (state : EVMState) :
    openRunNResult program 0 state =
      Simulation.Interaction.pure (.running state) := rfl

theorem openRunNResult_succ
    (program : Program) (fuel : Nat) (state : EVMState) :
    openRunNResult program (fuel + 1) state =
      (do
        let result <- openStepResult program state
        match result with
        | .running mid => openRunNResult program fuel mid
        | .halted halt => pure (.halted halt)) := rfl

theorem openRunNResult_one
    (program : Program) (state : EVMState) :
    openRunNResult program 1 state = openStepResult program state := by
  rw [show 1 = 0 + 1 by rfl, openRunNResult_succ]
  simp only [openRunNResult_zero]
  change Simulation.Interaction.bind
      (openStepResult program state)
      (fun result =>
        match result with
        | .running mid => Simulation.Interaction.pure (.running mid)
        | .halted halt => Simulation.Interaction.pure (.halted halt)) =
    openStepResult program state
  trans Simulation.Interaction.bind
    (openStepResult program state) Simulation.Interaction.pure
  · apply Simulation.Interaction.AllDone.bind_congr
      (Simulation.Interaction.AllDone.trivial
        (openStepResult program state))
    intro result _hDone
    cases result <;> rfl
  · exact Simulation.Interaction.bind_pure _

theorem openRunNResult_add
    (program : Program) (first second : Nat)
    (state : EVMState) :
    openRunNResult program (first + second) state =
      (do
        let result ← openRunNResult program first state
        match result with
        | .running mid =>
            openRunNResult program second mid
        | .halted halt =>
            pure (.halted halt)) := by
  exact
    Control.openRunNResultWith_add
      (Assembly.Source.stepResultWith (openStepAtResult program) program)
      first second state

/-- Once an Assembly source run halts, additional source-instruction fuel is
inert. -/
theorem openRunNResult_halted_add_executes
    {program : Program} {fuel extra : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript} {halt : Halt}
    (hExec : Simulation.Interaction.Executes
      (openRunNResult program fuel state)
      transcript (.ok (.halted halt))) :
    Simulation.Interaction.Executes
      (openRunNResult program (fuel + extra) state)
      transcript (.ok (.halted halt)) := by
  rw [openRunNResult_add]
  have hCombined :=
    Simulation.Interaction.Executes.bind_ok
      (next := fun result =>
        match result with
        | .running mid => openRunNResult program extra mid
        | .halted final => Simulation.Interaction.pure (.halted final))
      hExec
      (Simulation.Interaction.Executes.done
        (.ok (StepResult.halted halt) : Except EVMException StepResult))
  simpa using hCombined

def openRunUntilTransferWithPolicy
    (continueTransfer : Instr → Bool)
    (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Source.runUntilTransferWithPolicy continueTransfer
    (openStepResult program) program fuel state

@[simp] theorem openRunUntilTransferWithPolicy_zero
    (continueTransfer : Instr -> Bool)
    (program : Program) (state : EVMState) :
    openRunUntilTransferWithPolicy continueTransfer program 0 state =
      Simulation.Interaction.pure (.running state) := rfl

theorem openRunUntilTransferWithPolicy_succ
    (continueTransfer : Instr -> Bool)
    (program : Program) (fuel : Nat) (state : EVMState) :
    openRunUntilTransferWithPolicy continueTransfer
        program (fuel + 1) state =
      (do
        let flow <- Assembly.Source.flowStepWithPolicy
          continueTransfer (openStepResult program) program state
        match flow with
        | .next mid =>
            openRunUntilTransferWithPolicy continueTransfer
              program fuel mid
        | .exit result => pure result) := rfl

/-- Flow classification changes only whether control continues, never the
underlying one-instruction result. -/
theorem map_openFlowStepWithPolicy_result
    (continueTransfer : Instr -> Bool)
    (program : Program) (state : EVMState) :
    Simulation.Interaction.map FlowStep.result
        (Assembly.Source.flowStepWithPolicy continueTransfer
          (openStepResult program) program state) =
      openStepResult program state := by
  unfold Assembly.Source.flowStepWithPolicy openStepResult
    Assembly.Source.stepResultWith
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      change Simulation.Interaction.bind
          (Simulation.Interaction.error
            (Result := FlowStep)
              EvmYul.EVM.ExecutionException.InvalidInstruction)
          (fun value : FlowStep =>
            Simulation.Interaction.pure value.result) =
        Simulation.Interaction.error
          (Result := StepResult)
            EvmYul.EVM.ExecutionException.InvalidInstruction
      rfl
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp only [hAt]
      change Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (openStepAtResult program pc instr state)
            (fun result => Simulation.Interaction.pure
              (instr.classifyFlowWith continueTransfer state result)))
          (fun flow => Simulation.Interaction.pure flow.result) =
        openStepAtResult program pc instr state
      rw [Simulation.Interaction.bind_assoc]
      trans Simulation.Interaction.bind
        (openStepAtResult program pc instr state)
        Simulation.Interaction.pure
      · apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (openStepAtResult program pc instr state))
        intro result _hDone
        change Simulation.Interaction.pure
            ((instr.classifyFlowWith continueTransfer state result).result) =
          Simulation.Interaction.pure result
        rw [InteractionSemantics.Instr.classifyFlowWith_result]
      · exact Simulation.Interaction.bind_pure _

/-- Every branch of run-until-transfer is a bounded prefix of the ordinary
Assembly source runner. -/
theorem openRunUntilTransferWithPolicy_executes_openRunNResult_bounded
    {continueTransfer : Instr -> Bool}
    {program : Program} {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hExec : Simulation.Interaction.Executes
      (openRunUntilTransferWithPolicy continueTransfer
        program fuel state)
      transcript (.ok result)) :
    exists usedFuel,
      usedFuel <= fuel /\
        Simulation.Interaction.Executes
          (openRunNResult program usedFuel state)
          transcript (.ok result) := by
  induction fuel generalizing state transcript result with
  | zero =>
      rw [openRunUntilTransferWithPolicy_zero] at hExec
      cases hExec
      refine ⟨0, Nat.le_refl 0, ?_⟩
      rw [openRunNResult_zero]
      exact
        Simulation.Interaction.Executes.done
          (.ok (StepResult.running state) : Except EVMException StepResult)
  | succ fuel ih =>
      rw [openRunUntilTransferWithPolicy_succ] at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hError | hOk
      · rcases hError with ⟨error, hOutcome, _hFlow⟩
        cases hOutcome
      · rcases hOk with
          ⟨flow, headTranscript, restTranscript,
            hTranscript, hFlow, hRest⟩
        subst transcript
        have hMapped : Simulation.Interaction.Executes
            (Simulation.Interaction.map FlowStep.result
              (Assembly.Source.flowStepWithPolicy continueTransfer
                (openStepResult program) program state))
            headTranscript (.ok flow.result) := by
          unfold Simulation.Interaction.map
          have hPure : Simulation.Interaction.Executes
              (Simulation.Interaction.pure
                (Error := EVMException) flow.result)
              [] (.ok flow.result) :=
            Simulation.Interaction.Executes.done
              (.ok flow.result : Except EVMException StepResult)
          simpa using
            (Simulation.Interaction.Executes.bind_ok
              (next := fun nextFlow =>
                Simulation.Interaction.pure
                  (Error := EVMException) nextFlow.result)
              hFlow hPure)
        rw [map_openFlowStepWithPolicy_result] at hMapped
        rw [← openRunNResult_one] at hMapped
        cases flow with
        | next mid =>
            obtain ⟨tailFuel, hTailFuel, hTail⟩ := ih hRest
            refine ⟨1 + tailFuel, by omega, ?_⟩
            rw [openRunNResult_add]
            exact Simulation.Interaction.Executes.bind_ok hMapped hTail
        | exit exitResult =>
            cases hRest
            exact ⟨1, by omega, by simpa using hMapped⟩

def openRunUntilTransfer (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  openRunUntilTransferWithPolicy (fun _ => false)
    program fuel state

/--
The primitive case of the Assembly-to-resolved-instruction boundary is exact:
both sides expose the same query and use the same continuation for every
answer. This is the seed used by the pass-owned recursive composition proof.
-/
theorem prim_openStep_rel
    (program : Program) (pc : Nat) (op : Assembly.PrimOp)
    (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (openStepAt program pc (.prim op) state)
      (Target.openStepInstr (.prim op) state) := by
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

end Source

namespace Compiled

def openStep (program : Program) (state : EVMState) : OpenStep :=
  Assembly.Compiled.stepWith Target.openRunList program state

def openStepResult (program : Program) (state : EVMState) :
    OpenStepResult :=
  Assembly.Compiled.stepResultWith Target.openRunListResult program state

def openRunN (program : Program) (fuel : Nat) (state : EVMState) :
    OpenStep :=
  Assembly.Control.runNWith (openStep program) fuel state

def openRunNResult (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Control.runNResultWith (openStepResult program) fuel state

def openRunUntilTransferWithPolicy
    (continueTransfer : Instr → Bool)
    (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  Assembly.Source.runUntilTransferWithPolicy continueTransfer
    (openStepResult program) program fuel state

def openRunUntilTransfer (program : Program) (fuel : Nat)
    (state : EVMState) : OpenStepResult :=
  openRunUntilTransferWithPolicy (fun _ => false)
    program fuel state

end Compiled

end InteractionSemantics
end Assembly
end EvmCompiler
