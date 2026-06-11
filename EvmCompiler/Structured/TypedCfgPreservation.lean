import EvmCompiler.Structured.TypedCfgCompiler
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

/--
Realize Structured's ghost return frames as the concrete return-token and
caller-stack suffix carried by TypedCfg procedure execution.
-/
def realizeStack : EvmYul.Stack Word → List ReturnDest → List Word →
    Option (EvmYul.Stack Word)
  | stack, [], [] => some stack
  | stack, frame :: returns, token :: tokens =>
      realizeStack
        (stack ++ [token] ++ frame.callerStack) returns tokens
  | _stack, _returns, _tokens => none

theorem realizeStack_append_prefix
    (front stack : EvmYul.Stack Word)
    (returns : List ReturnDest) (tokens : List Word) :
    realizeStack (front ++ stack) returns tokens =
      (realizeStack stack returns tokens).map (front ++ ·) := by
  induction returns generalizing stack tokens with
  | nil =>
      cases tokens <;>
        simp [realizeStack]
  | cons frame returns ih =>
      cases tokens with
      | nil =>
          simp [realizeStack]
      | cons token tokens =>
          simpa [realizeStack, List.append_assoc] using
            ih (stack ++ [token] ++ frame.callerStack) tokens

/--
Source-to-CFG state relation.

The stack is related through concrete realization of ghost return frames.
Control position and lowering-only resource counters are compared through the
shared control-erased observation boundary, while available gas remains equal
so the Structured `gas` primitive has the same CFG-level meaning.
-/
def eraseCfgControl (state : EVMState) : EVMState :=
  { state with
    pc := EvmYul.UInt256.ofNat 0
    execLength := 0 }

@[simp] theorem eraseCfgControl_mk
    (shared : EvmYul.SharedState .EVM) (pc : EvmYul.UInt256)
    (stack : EvmYul.Stack Word) (execLength : Nat) :
    eraseCfgControl ⟨shared, pc, stack, execLength⟩ =
      ⟨shared, EvmYul.UInt256.ofNat 0, stack, 0⟩ :=
  rfl

@[simp] theorem exceptMap_eraseCfgControl_ok (state : EVMState) :
    (Except.ok state :
      Except EvmYul.EVM.ExecutionException EVMState).map eraseCfgControl =
        .ok (eraseCfgControl state) :=
  rfl

@[simp] theorem exceptMap_eraseCfgControl_error
    (err : EvmYul.EVM.ExecutionException) :
    (Except.error err :
      Except EvmYul.EVM.ExecutionException EVMState).map eraseCfgControl =
        .error err :=
  rfl

@[simp] theorem idRun_eq {α : Type} (value : α) :
    Id.run value = value :=
  rfl

def SameRuntimeData (target source : EVMState) : Prop :=
  eraseCfgControl target = eraseCfgControl source

namespace SameRuntimeData

theorem refl (state : EVMState) :
    SameRuntimeData state state :=
  rfl

theorem trans {first second third : EVMState}
    (hFirst : SameRuntimeData first second)
    (hSecond : SameRuntimeData second third) :
    SameRuntimeData first third :=
  Eq.trans hFirst hSecond

theorem sameData {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    Assembly.SameData target source := by
  cases target
  cases source
  simp [SameRuntimeData, eraseCfgControl, Assembly.SameData,
    Assembly.eraseControl, Assembly.eraseGas] at hRel ⊢
  constructor
  · simpa [hRel.1]
  · exact hRel.2

theorem stack_eq {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    target.stack = source.stack := by
  cases target
  cases source
  simp [SameRuntimeData, eraseCfgControl] at hRel
  exact hRel.2

theorem replaceStackAndIncrPC
    {target source : EVMState}
    {targetStack sourceStack : EvmYul.Stack Word} {pcΔ : Nat}
    (hRel : SameRuntimeData target source)
    (hStack : targetStack = sourceStack) :
    SameRuntimeData
      (target.replaceStackAndIncrPC targetStack (pcΔ := pcΔ))
      (source.replaceStackAndIncrPC sourceStack (pcΔ := pcΔ)) := by
  cases target
  cases source
  simp [SameRuntimeData, eraseCfgControl] at hRel ⊢
  exact ⟨hRel.1, hStack⟩

theorem replaceStack
    {target source : EVMState}
    {targetStack sourceStack : EvmYul.Stack Word}
    (hRel : SameRuntimeData target source)
    (hStack : targetStack = sourceStack) :
    SameRuntimeData
      { target with stack := targetStack }
      { source with stack := sourceStack } := by
  cases target
  cases source
  simp [SameRuntimeData, eraseCfgControl] at hRel ⊢
  exact ⟨hRel.1, hStack⟩

end SameRuntimeData

def StateRel (source : RunState) (tokens : List Word)
    (target : EVMState) : Prop :=
  ∃ stack,
    realizeStack source.evm.stack source.returns tokens = some stack ∧
      SameRuntimeData target { source.evm with stack := stack }

namespace StateRel

theorem initial (state : EVMState) :
    StateRel (RunState.initial state) [] state :=
  ⟨state.stack, rfl, rfl⟩

theorem targetCongr
    {source : RunState} {tokens : List Word}
    {target targetFinal : EVMState}
    (hSame : SameRuntimeData targetFinal target)
    (hRel : StateRel source tokens target) :
    StateRel source tokens targetFinal := by
  rcases hRel with ⟨realized, hRealize, hTarget⟩
  exact
    ⟨realized, hRealize,
      SameRuntimeData.trans hSame hTarget⟩

theorem stackView_of_pop
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word} {value : Word}
    (hRel : StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ realizedTail,
      realizeStack stack source.returns tokens = some realizedTail ∧
        target.stack = value :: realizedTail := by
  rcases hRel with ⟨realized, hRealize, hSame⟩
  cases hSourceStack : source.evm.stack with
  | nil =>
      simp [hSourceStack, EvmYul.Stack.pop] at hPop
  | cons head tail =>
      simp [hSourceStack, EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      rw [hSourceStack] at hRealize
      change
        realizeStack ([head] ++ tail) source.returns tokens =
          some realized at hRealize
      rw [realizeStack_append_prefix] at hRealize
      cases hTailRealize :
          realizeStack tail source.returns tokens with
      | none =>
          simp [hTailRealize] at hRealize
      | some realizedTail =>
          simp [hTailRealize] at hRealize
          subst realized
          exact
            ⟨realizedTail, rfl,
              by simpa using SameRuntimeData.stack_eq hSame⟩

theorem pushReturn
    {source : RunState} {tokens : List Word} {target : EVMState}
    {args callerStack realized : EvmYul.Stack Word}
    {retc : Nat} {token : Word}
    (hRealize :
      realizeStack
          (args ++ [token] ++ callerStack)
          source.returns tokens =
        some realized)
    (hSame :
      SameRuntimeData target { source.evm with stack := realized }) :
    StateRel
      ((source.withEVM { source.evm with stack := args }).pushReturn
        callerStack retc)
      (token :: tokens) target := by
  refine ⟨realized, ?_, ?_⟩
  · simpa [realizeStack, RunState.pushReturn, RunState.withEVM,
      List.append_assoc] using hRealize
  · simpa [RunState.pushReturn, RunState.withEVM] using hSame

theorem pop
    {source : RunState} {tokens : List Word} {target : EVMState}
    {shape : TypedCfg.Shape} {stack : EvmYul.Stack Word} {value : Word}
    (hRel : StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.Instr.runState .pop shape target = .ok targetFinal ∧
        StateRel
          (source.withEVM { source.evm with stack := stack })
          tokens targetFinal := by
  rcases hRel with ⟨realized, hRealize, hSame⟩
  cases hSourceStack : source.evm.stack with
  | nil =>
      simp [hSourceStack, EvmYul.Stack.pop] at hPop
  | cons head tail =>
      simp [hSourceStack, EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      rw [hSourceStack] at hRealize
      change
        realizeStack ([head] ++ tail) source.returns tokens =
          some realized at hRealize
      rw [realizeStack_append_prefix] at hRealize
      cases hTailRealize :
          realizeStack tail source.returns tokens with
      | none =>
          simp [hTailRealize] at hRealize
      | some realizedTail =>
          simp [hTailRealize] at hRealize
          subst realized
          have hTargetStack : target.stack = head :: realizedTail := by
            simpa using SameRuntimeData.stack_eq hSame
          let targetFinal :=
            target.replaceStackAndIncrPC realizedTail
          refine ⟨targetFinal, ?_, ?_⟩
          · simp [targetFinal, TypedCfg.Instr.runState,
              Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
              Assembly.PrimStep.run, hTargetStack, EvmYul.Stack.pop]
          · refine ⟨realizedTail, hTailRealize, ?_⟩
            have hAfter :=
              SameRuntimeData.replaceStackAndIncrPC hSame
                (targetStack := realizedTail)
                (sourceStack := realizedTail) (pcΔ := 1) rfl
            simpa [targetFinal, RunState.withEVM, SameRuntimeData,
              eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] using hAfter

theorem popCondition
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word} {value : Word}
    (hRel : StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      Structured.Code.popCondition target =
          .ok (targetFinal, value != EvmYul.UInt256.ofNat 0) ∧
        StateRel
          (source.withEVM { source.evm with stack := stack })
          tokens targetFinal := by
  rcases hRel with ⟨realized, hRealize, hSame⟩
  cases hSourceStack : source.evm.stack with
  | nil =>
      simp [hSourceStack, EvmYul.Stack.pop] at hPop
  | cons head tail =>
      simp [hSourceStack, EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      rw [hSourceStack] at hRealize
      change
        realizeStack ([head] ++ tail) source.returns tokens =
          some realized at hRealize
      rw [realizeStack_append_prefix] at hRealize
      cases hTailRealize :
          realizeStack tail source.returns tokens with
      | none =>
          simp [hTailRealize] at hRealize
      | some realizedTail =>
          simp [hTailRealize] at hRealize
          subst realized
          have hTargetStack : target.stack = head :: realizedTail := by
            simpa using SameRuntimeData.stack_eq hSame
          let targetFinal : EVMState :=
            { target with stack := realizedTail }
          refine ⟨targetFinal, ?_, ?_⟩
          · simp [Structured.Code.popCondition, targetFinal,
              hTargetStack, EvmYul.Stack.pop]
          · refine ⟨realizedTail, hTailRealize, ?_⟩
            have hAfter :=
              SameRuntimeData.replaceStack hSame
                (targetStack := realizedTail)
                (sourceStack := realizedTail) rfl
            simpa [targetFinal, RunState.withEVM] using hAfter

end StateRel

namespace BasicInstr

theorem runAt_toCfg
    {instr : Structured.BasicInstr} {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType :
      TypedCfg.Instr.type?
        (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output) :
    TypedCfg.Instr.runAt
        (TypedCfgCompiler.BasicInstr.toCfg instr) input state =
      (instr.step state).map fun final => (final, output) := by
  unfold TypedCfg.Instr.runAt
  rw [hType]
  cases instr <;>
    rfl

end BasicInstr

namespace PrimStep

/--
Continuing primitive semantics depend on runtime data and stack, but not on the
CFG-owned program counter or execution-length fields.
-/
theorem run_map_eraseCfgControl
    {step : Assembly.PrimStep} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (step.run target).map eraseCfgControl =
      (step.run source).map eraseCfgControl := by
  cases target with
  | mk targetShared targetPc targetStack targetExec =>
      cases source with
      | mk sourceShared sourcePc sourceStack sourceExec =>
          simp [SameRuntimeData, eraseCfgControl] at hRel
          rcases hRel with ⟨rfl, rfl⟩
          cases step with
          | bin f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.execBinOp, hPop,
                  eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | un f =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.execUnOp, hPop,
                  eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | tri f =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.execTriOp, hPop,
                  eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | executionEnv f =>
              simp [Except.map, Assembly.PrimStep.run,
                EvmYul.EVM.executionEnvOp,
                eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          | unaryExecutionEnv f =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.unaryExecutionEnvOp, hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | machineState f =>
              simp [Except.map, Assembly.PrimStep.run,
                EvmYul.EVM.machineStateOp,
                eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          | binaryMachineState f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.binaryMachineStateOp, hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | binaryMachineStateWithResult f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.binaryMachineStateOp', hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | ternaryMachineState f =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.ternaryMachineStateOp, hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | state f =>
              simp [Except.map, Assembly.PrimStep.run, EvmYul.EVM.stateOp,
                eraseCfgControl, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
          | unaryState f =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.unaryStateOp,
                  hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | binaryState f =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.binaryStateOp,
                  hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | ternaryCopy f =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.ternaryCopyOp,
                  hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | quaternaryCopy f =>
              cases hPop : targetStack.pop4 <;>
                simp [Except.map, Assembly.PrimStep.run,
                  EvmYul.EVM.quaternaryCopyOp,
                  hPop, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | pop =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | mload =>
              cases hPop : targetStack.pop <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | returndatacopy =>
              cases hPop : targetStack.pop3 with
              | none =>
                  simp [Except.map, Assembly.PrimStep.run, hPop,
                    eraseCfgControl]
              | some values =>
                  by_cases hBounds :
                      targetShared.returnData.size <
                        values.2.2.1.toNat + values.2.2.2.toNat <;>
                    simp [Except.map, Assembly.PrimStep.run, hPop,
                      hBounds, eraseCfgControl,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC]
          | dup n =>
              by_cases hLength : n ≤ targetStack.length <;>
                simp [Except.map, Assembly.PrimStep.run, EvmYul.dup,
                  hLength, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | swap n =>
              by_cases hLength : n + 1 ≤ targetStack.length <;>
                simp [Except.map, Assembly.PrimStep.run, EvmYul.swap,
                  hLength, eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log0 =>
              cases hPop : targetStack.pop2 <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log1 =>
              cases hPop : targetStack.pop3 <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log2 =>
              cases hPop : targetStack.pop4 <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log3 =>
              cases hPop : targetStack.pop5 <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | log4 =>
              cases hPop : targetStack.pop6 <;>
                simp [Except.map, Assembly.PrimStep.run, hPop,
                  eraseCfgControl,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
          | invalid =>
              rfl

end PrimStep

namespace BasicOp

/--
Structured primitive execution is insensitive to CFG-owned control counters.
The one admitted observer outside `continuingStep?`, `gas`, is covered because
`SameRuntimeData` retains the complete shared machine state.
-/
theorem step_map_eraseCfgControl
    {op : Structured.BasicOp} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (op.step target).map eraseCfgControl =
      (op.step source).map eraseCfgControl := by
  unfold Structured.BasicOp.step
  simp only [Assembly.Target.stepInstr]
  cases hStep : op.toPrimOp.continuingStep? with
  | some step =>
      rw [Assembly.PrimOp.step_eq_continuingStep_run hStep target,
        Assembly.PrimOp.step_eq_continuingStep_run hStep source]
      exact PrimStep.run_map_eraseCfgControl hRel
  | none =>
      have hCases :
          op = .gas ∨ op = .create ∨ op = .call ∨ op = .callcode ∨
            op = .delegatecall ∨ op = .create2 ∨ op = .staticcall := by
        cases op <;>
          simp [Structured.BasicOp.toPrimOp,
            Assembly.PrimOp.continuingStep?] at hStep ⊢
      rcases hCases with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change
          (EvmYul.EVM.machineStateOp EvmYul.MachineState.gas target).map
              eraseCfgControl =
            (EvmYul.EVM.machineStateOp EvmYul.MachineState.gas source).map
              eraseCfgControl
        exact
          PrimStep.run_map_eraseCfgControl
            (step := .machineState EvmYul.MachineState.gas) hRel
      all_goals
        rfl

end BasicOp

namespace BasicInstr

theorem step_map_eraseCfgControl
    {instr : Structured.BasicInstr} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (instr.step target).map eraseCfgControl =
      (instr.step source).map eraseCfgControl := by
  cases instr with
  | push value =>
      cases target with
      | mk targetShared targetPc targetStack targetExec =>
          cases source with
          | mk sourceShared sourcePc sourceStack sourceExec =>
              simp [SameRuntimeData, eraseCfgControl] at hRel
              rcases hRel with ⟨rfl, rfl⟩
              simp [Structured.BasicInstr.step, Assembly.Target.stepInstr,
                Except.map, eraseCfgControl,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
  | op op =>
      exact BasicOp.step_map_eraseCfgControl hRel

end BasicInstr

namespace Code

/--
Straight-line Structured execution is congruent under the control-erased
runtime relation.
-/
theorem run_map_eraseCfgControl
    {code : Structured.Code} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (Structured.Code.run code target).map eraseCfgControl =
      (Structured.Code.run code source).map eraseCfgControl := by
  induction code generalizing target source with
  | nil =>
      simpa [Structured.Code.run, Except.map] using hRel
  | cons instr rest ih =>
      have hHead :=
        BasicInstr.step_map_eraseCfgControl
          (instr := instr) hRel
      cases hTarget : instr.step target with
      | error targetErr =>
          cases hSource : instr.step source with
          | error sourceErr =>
              simpa [Structured.Code.run, hTarget, hSource,
                Except.map, Bind.bind, Except.bind] using hHead
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hHead
      | ok targetFinal =>
          cases hSource : instr.step source with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hHead
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hHead
              simpa [Structured.Code.run, hTarget, hSource,
                Bind.bind, Except.bind] using
                  ih (target := targetFinal) (source := sourceFinal) hHead

theorem run_sameRuntimeData_of_ok
    {code : Structured.Code} {target source targetFinal sourceFinal : EVMState}
    (hRel : SameRuntimeData target source)
    (hTarget : Structured.Code.run code target = .ok targetFinal)
    (hSource : Structured.Code.run code source = .ok sourceFinal) :
    SameRuntimeData targetFinal sourceFinal := by
  have hRun := run_map_eraseCfgControl (code := code) hRel
  simpa [hTarget, hSource, Except.map] using hRun

end Code

namespace StateRel

/--
Frame-safe straight-line code preserves the source-to-CFG state relation.
-/
theorem runCode
    {code : Structured.Code} {source final : RunState}
    {tokens : List Word} {target : EVMState}
    (hFrameSafe : code.FrameSafe)
    (hRun : Structured.Code.runState code source = .ok final)
    (hRel : StateRel source tokens target) :
    ∃ targetFinal,
      Structured.Code.run code target = .ok targetFinal ∧
        StateRel final tokens targetFinal := by
  unfold Structured.Code.runState at hRun
  cases hSourceRun : Structured.Code.run code source.evm with
  | error err =>
      simp [hSourceRun, Bind.bind, Except.bind] at hRun
  | ok sourceFinal =>
      simp [hSourceRun, Bind.bind, Except.bind] at hRun
      cases hRun
      rcases hRel with ⟨realized, hRealize, hSame⟩
      have hAppend :=
        realizeStack_append_prefix source.evm.stack []
          source.returns tokens
      cases hHidden : realizeStack [] source.returns tokens with
      | none =>
          simp [hHidden] at hAppend
          rw [hAppend] at hRealize
          cases hRealize
      | some hidden =>
          simp [hHidden] at hAppend
          rw [hAppend] at hRealize
          cases hRealize
          have hFramed :
              Structured.Code.run code
                  { source.evm with
                    stack := source.evm.stack ++ hidden } =
                .ok
                  { sourceFinal with
                    stack := sourceFinal.stack ++ hidden } :=
            hFrameSafe source.evm sourceFinal hidden hSourceRun
          have hCongruence :=
            Code.run_map_eraseCfgControl (code := code) hSame
          rw [hFramed] at hCongruence
          cases hTargetRun : Structured.Code.run code target with
          | error targetErr =>
              simp [hTargetRun, Except.map] at hCongruence
          | ok targetFinal =>
              simp [hTargetRun, Except.map] at hCongruence
              refine ⟨targetFinal, rfl, ?_⟩
              refine
                ⟨sourceFinal.stack ++ hidden, ?_, ?_⟩
              · have hFinalAppend :=
                  realizeStack_append_prefix sourceFinal.stack []
                    source.returns tokens
                simpa [RunState.withEVM, hHidden] using hFinalAppend
              · simpa [RunState.withEVM] using hCongruence

/--
Frame-safe condition evaluation preserves the concrete frame relation and
selects the same Boolean branch.
-/
theorem runCondition
    {code : Structured.Code} {source final : RunState} {cond : Bool}
    {tokens : List Word} {target : EVMState}
    (hFrameSafe : code.FrameSafe)
    (hRun :
      Structured.Code.runConditionState code source =
        .ok (final, cond))
    (hRel : StateRel source tokens target) :
    ∃ targetFinal,
      Structured.Code.runConditionState code (source.withEVM target) =
          .ok (source.withEVM targetFinal, cond) ∧
        StateRel final tokens targetFinal := by
  unfold Structured.Code.runConditionState at hRun
  unfold Structured.Code.runCondition at hRun
  cases hSourceCode : Structured.Code.run code source.evm with
  | error err =>
      simp [hSourceCode, Bind.bind, Except.bind] at hRun
  | ok afterCode =>
      cases hSourcePop : afterCode.stack.pop with
      | none =>
          simp [hSourceCode, Structured.Code.popCondition, hSourcePop,
            Bind.bind, Except.bind] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [hSourceCode, Structured.Code.popCondition, hSourcePop,
            Bind.bind, Except.bind] at hRun
          rcases hRun with ⟨hFinal, hCond⟩
          subst final
          subst cond
          have hCodeRunState :
              Structured.Code.runState code source =
                .ok (source.withEVM afterCode) := by
            simp [Structured.Code.runState, hSourceCode,
              Bind.bind, Except.bind]
          rcases runCode hFrameSafe hCodeRunState hRel with
            ⟨targetAfterCode, hTargetCode, hAfterCodeRel⟩
          rcases
              popCondition
                (source := source.withEVM afterCode)
                hAfterCodeRel hSourcePop with
            ⟨targetFinal, hTargetPop, hFinalRel⟩
          refine ⟨targetFinal, ?_, ?_⟩
          · simp [Structured.Code.runConditionState,
              Structured.Code.runCondition, hTargetCode, hTargetPop,
              Bind.bind, Except.bind, RunState.withEVM]
          · simpa [RunState.withEVM] using hFinalRel

end StateRel

namespace Code

/--
Straight-line Structured code and the generated TypedCfg body have identical
runtime behavior. The TypedCfg side additionally returns the symbolic output
shape already computed by the checked body typer.
-/
theorem runBody_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.Block.runBody (TypedCfgCompiler.Code.toCfg code) input state =
      (Structured.Code.run code state).map fun final => (final, output) := by
  induction code generalizing input output state with
  | nil =>
      simp [TypedCfgCompiler.Code.type?, TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?, TypedCfg.Block.runBody,
        Structured.Code.run] at hType ⊢
      cases hType
      rfl
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      simp only [TypedCfgCompiler.Code.toCfg, List.map_cons,
        TypedCfg.Block.bodyType?] at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
          simp [hHeadType] at hType
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [TypedCfgCompiler.Code.type?,
              TypedCfgCompiler.Code.toCfg] using hType
          simp only [TypedCfgCompiler.Code.toCfg, List.map_cons]
          unfold TypedCfg.Block.runBody
          rw [BasicInstr.runAt_toCfg hHeadType]
          cases hStep : instr.step state with
          | error err =>
              simp only [hStep, Except.map, Bind.bind, Except.bind,
                Structured.Code.run]
          | ok state' =>
              simp only [hStep, Except.map, Bind.bind, Except.bind,
                Structured.Code.run]
              exact ih hTailType

theorem runState_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state : RunState}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.Block.runBody (TypedCfgCompiler.Code.toCfg code) input
        state.evm =
      (Structured.Code.runState code state).map fun final =>
        (final.evm, output) := by
  rw [runBody_toCfg hType]
  unfold Structured.Code.runState
  cases hRun : Structured.Code.run code state.evm with
  | error err =>
      simp only [Bind.bind, Except.bind, Except.map]
  | ok final =>
      simp only [Bind.bind, Except.bind, Except.map]
      rfl

/--
A generated conditional block follows the same branch and produces the same
post-pop EVM state as the independent Structured condition evaluator.
-/
theorem run_jumpi_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state final : RunState} {cond : Bool}
    {target fallthrough : Assembly.Label}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hCond :
      Structured.Code.runConditionState code state = .ok (final, cond)) :
    TypedCfg.Block.run
        { label := target
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jumpi target fallthrough }
        state.evm =
      .ok
        (.jump (if cond then target else fallthrough) final.evm) := by
  unfold Structured.Code.runConditionState at hCond
  unfold Structured.Code.runCondition at hCond
  cases hCode : Structured.Code.run code state.evm with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hCond
  | ok afterCode =>
      cases hPop : afterCode.stack.pop with
      | none =>
          simp [hCode, Structured.Code.popCondition, hPop,
            Bind.bind, Except.bind] at hCond
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [hCode, Structured.Code.popCondition, hPop,
            Bind.bind, Except.bind] at hCond
          rcases hCond with ⟨hFinal, hBool⟩
          subst final
          by_cases hZero : value = EvmYul.UInt256.ofNat 0
          · have hBne :
                (value != EvmYul.UInt256.ofNat 0) = false := by
              subst value
              exact TypedCfg.Preservation.uint256_bne_zero_self
            have hCondFalse : cond = false := by
              calc
                cond = (value != EvmYul.UInt256.ofNat 0) := hBool.symm
                _ = false := hBne
            rw [hCondFalse]
            simp [TypedCfg.Block.run, runBody_toCfg hType, hCode,
              Except.map, Bind.bind, Except.bind, TypedCfg.Block.runTerm,
              hPop, hZero, hBne]
          · have hBne :
                (value != EvmYul.UInt256.ofNat 0) = true :=
              TypedCfg.Preservation.uint256_bne_zero_of_ne value hZero
            have hCondTrue : cond = true := by
              calc
                cond = (value != EvmYul.UInt256.ofNat 0) := hBool.symm
                _ = true := hBne
            rw [hCondTrue]
            simp [TypedCfg.Block.run, runBody_toCfg hType, hCode,
              Except.map, Bind.bind, Except.bind, TypedCfg.Block.runTerm,
              hPop, hZero, hBne]

end Code

/--
View a compiled fragment as an independently executable CFG. The continuation
label need not occur in `blocks`: `TypedCfg.Program.runN` can expose reaching it
as a residual jump.
-/
def resultProgram (result : TypedCfgCompiler.Result)
    (entry : Assembly.Label) : TypedCfg.Program where
  entry := entry
  blocks := result.blocks

/--
Every block emitted for a compiler result is available through the ambient
program's lookup function.

Fragment compilers accept arbitrary symbolic entries, so this property is
derived from the final certified CFG instead of being assumed from a fragment
in isolation.
-/
def BlocksInProgram (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) : Prop :=
  ∀ block, block ∈ result.blocks →
    program.findBlock? block.label = some block

namespace BlocksInProgram

theorem of_subset
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hUnique : program.LabelsUnique)
    (hSubset :
      ∀ block, block ∈ result.blocks → block ∈ program.blocks) :
    BlocksInProgram result program := by
  intro block hMem
  exact
    TypedCfg.Program.findBlock?_eq_some_of_mem hUnique
      (hSubset block hMem)

theorem of_subset_of_wellTyped
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hWellTyped : program.WellTyped)
    (hSubset :
      ∀ block, block ∈ result.blocks → block ∈ program.blocks) :
    BlocksInProgram result program :=
  of_subset hWellTyped.1 hSubset

theorem eventually_of_run
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {block : TypedCfg.Block} {state : EVMState}
    {outcome : TypedCfg.Outcome}
    (hBlocks : BlocksInProgram result program)
    (hMem : block ∈ result.blocks)
    (hRun : block.run state = .ok outcome) :
    program.Eventually block.label state outcome := by
  have hFind := hBlocks block hMem
  refine ⟨1, ?_⟩
  cases outcome <;>
    simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind, hRun,
      Bind.bind, Except.bind]

theorem left_of_append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hBlocks : BlocksInProgram (left.append right) program) :
    BlocksInProgram left program := by
  intro block hMem
  apply hBlocks block
  simp [TypedCfgCompiler.Result.append, hMem]

theorem right_of_append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hBlocks : BlocksInProgram (left.append right) program) :
    BlocksInProgram right program := by
  intro block hMem
  apply hBlocks block
  simp [TypedCfgCompiler.Result.append, hMem]

theorem eventually_pop_jump
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {input output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word} {value : Word}
    (hBlocks : BlocksInProgram result program)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump regular } ∈ result.blocks)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hRel : StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      program.Eventually entry target
          (TypedCfg.Outcome.jump regular targetFinal) ∧
        StateRel
          (source.withEVM { source.evm with stack := stack })
          tokens targetFinal := by
  rcases StateRel.pop (shape := input) hRel hPop with
    ⟨targetFinal, hRunPop, hFinalRel⟩
  refine ⟨targetFinal, ?_, hFinalRel⟩
  apply eventually_of_run hBlocks hMem
  simp [TypedCfg.Block.run, TypedCfg.Block.runBody,
    TypedCfg.Instr.runAt, hType, hRunPop, TypedCfg.Block.runTerm,
    Bind.bind, Except.bind]

end BlocksInProgram

/--
Semantic certificate for a compiler result that completes normally.

The output shape is compiler metadata; the execution witness is stated in the
ambient certified CFG. This is the unit composed by statement-list proofs.
-/
def RegularExecution (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry regular : Assembly.Label)
    (initial final : EVMState) : Prop :=
  ∃ output : TypedCfg.Shape,
    result.fallthrough? = some output ∧
      program.Eventually entry initial
        (TypedCfg.Outcome.jump regular final)

namespace RegularExecution

theorem append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {initial afterLeft final : EVMState}
    (hLeft :
      RegularExecution left program entry middle initial afterLeft)
    (hRight :
      RegularExecution right program middle regular afterLeft final) :
    RegularExecution (left.append right) program entry regular initial final := by
  rcases hLeft with ⟨leftOutput, hLeftFallthrough, hLeftEventually⟩
  rcases hRight with ⟨rightOutput, hRightFallthrough, hRightEventually⟩
  refine ⟨rightOutput, ?_, ?_⟩
  · simp [TypedCfgCompiler.Result.append, hRightFallthrough]
  · exact
      TypedCfg.Program.Eventually.bind_jump
        hLeftEventually hRightEventually

end RegularExecution

/--
Relational regular preservation for a compiled fragment.

Unlike `RegularExecution`, this contract is stable across compiler-introduced
control operations and concrete procedure frames.
-/
def RegularPreserves (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry regular : Assembly.Label)
    (source final : RunState) (tokens : List Word) : Prop :=
  ∀ target,
    StateRel source tokens target →
      ∃ targetFinal,
        RegularExecution result program entry regular target targetFinal ∧
          StateRel final tokens targetFinal

namespace RegularPreserves

theorem append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {source afterLeft final : RunState} {tokens : List Word}
    (hLeft :
      RegularPreserves left program entry middle source afterLeft tokens)
    (hRight :
      RegularPreserves right program middle regular afterLeft final tokens) :
    RegularPreserves (left.append right) program entry regular
      source final tokens := by
  intro target hSourceRel
  rcases hLeft target hSourceRel with
    ⟨afterLeftTarget, hLeftExec, hAfterLeftRel⟩
  rcases hRight afterLeftTarget hAfterLeftRel with
    ⟨finalTarget, hRightExec, hFinalRel⟩
  exact
    ⟨finalTarget, RegularExecution.append hLeftExec hRightExec,
      hFinalRel⟩

theorem pop_jump
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {input output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hBlocks : BlocksInProgram result program)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump regular } ∈ result.blocks)
    (hFallthrough : result.fallthrough? = some output)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    RegularPreserves result program entry regular source
      (source.withEVM { source.evm with stack := stack }) tokens := by
  intro target hRel
  rcases
      BlocksInProgram.eventually_pop_jump hBlocks hMem hType hRel hPop with
    ⟨targetFinal, hEventually, hFinalRel⟩
  exact
    ⟨targetFinal, ⟨output, hFallthrough, hEventually⟩, hFinalRel⟩

end RegularPreserves

/--
Relational execution from a CFG label to a regular continuation, independent
of which compiler fragment owns the entry label.
-/
def PathPreserves (program : TypedCfg.Program)
    (entry regular : Assembly.Label)
    (source final : RunState) (tokens : List Word) : Prop :=
  ∀ target,
    StateRel source tokens target →
      ∃ targetFinal,
        program.Eventually entry target
            (.jump regular targetFinal) ∧
          StateRel final tokens targetFinal

namespace PathPreserves

theorem of_regular
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {source final : RunState} {tokens : List Word}
    (hPreserves :
      RegularPreserves result program entry regular source final tokens) :
    PathPreserves program entry regular source final tokens := by
  intro target hRel
  rcases hPreserves target hRel with
    ⟨targetFinal, ⟨_output, _hFallthrough, hEventually⟩, hFinalRel⟩
  exact ⟨targetFinal, hEventually, hFinalRel⟩

end PathPreserves

namespace Program

/--
Successful whole-program generation exposes the exact main-fragment compiler
result, and TypedCfg well-typedness turns its obvious block-list inclusion into
ambient lookup containment.
-/
theorem main_result_of_generateWithProcEntryShapes?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? source entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped) :
    ∃ main : TypedCfgCompiler.Result,
      TypedCfgCompiler.compileBlock? source.body
          { procs := source.procs } 0 TypedCfgCompiler.entryLabel
          TypedCfg.Shape.caller ProcLabel.programEnd =
        some main ∧
      BlocksInProgram main cfg := by
  unfold TypedCfgCompiler.generateWithProcEntryShapes? at hGenerate
  cases hMain :
      TypedCfgCompiler.compileBlock? source.body
        { procs := source.procs } 0 TypedCfgCompiler.entryLabel
        TypedCfg.Shape.caller ProcLabel.programEnd with
  | none =>
      simp [hMain] at hGenerate
  | some main =>
      cases hProcs :
          TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes
            source.procs source.procs main.next with
      | none =>
          simp [hMain, hProcs] at hGenerate
      | some procResult =>
          rcases procResult with ⟨procBlocks, next, procCalls⟩
          simp [hMain, hProcs] at hGenerate
          cases hGenerate
          refine ⟨main, by simpa using hMain, ?_⟩
          apply BlocksInProgram.of_subset_of_wellTyped hWellTyped
          intro block hMem
          simp [hMem]

theorem main_result_of_artifactWithProcEntryShapes?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {artifact : TypedCfgCompiler.CompileArtifact}
    (hArtifact :
      TypedCfgCompiler.artifactWithProcEntryShapes? source entryShapes =
        some artifact) :
    ∃ main : TypedCfgCompiler.Result,
      TypedCfgCompiler.compileBlock? source.body
          { procs := source.procs } 0 TypedCfgCompiler.entryLabel
          TypedCfg.Shape.caller ProcLabel.programEnd =
        some main ∧
      BlocksInProgram main artifact.cfg := by
  unfold TypedCfgCompiler.artifactWithProcEntryShapes? at hArtifact
  cases hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? source entryShapes with
  | none =>
      simp [hGenerate] at hArtifact
  | some cfg =>
      by_cases hCheck : cfg.wellTyped? = true
      · simp [hGenerate, hCheck] at hArtifact
        cases hArtifact
        exact
          main_result_of_generateWithProcEntryShapes? hGenerate
            (TypedCfg.Program.wellTyped_of_check hCheck)
      · simp [hGenerate, hCheck] at hArtifact

end Program

namespace Stmt

/--
Ambient-program form of straight-line statement preservation.
-/
theorem eventually_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRun : Structured.Code.runState code state = .ok final) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated := by
        exact hBlocks generated (by simp [generated])
      refine ⟨1, ?_⟩
      simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind,
        generated, TypedCfg.Block.run, Code.runState_toCfg hType, hRun,
        Except.map, Bind.bind, Except.bind, TypedCfg.Block.runTerm]

/--
Straight-line statement compilation produces a compositional regular
execution certificate.
-/
theorem regular_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRun : Structured.Code.runState code state = .ok final) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  have hEventually :=
    eventually_code_of_compileStmtFuel? hCompile hBlocks hRun
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      exact ⟨output, rfl, hEventually⟩

/--
Straight-line statement preservation under concrete return-token frames and
CFG-owned control counters.
-/
theorem preserves_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : code.FrameSafe)
    (hRun : Structured.Code.runState code source = .ok final) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCode hFrameSafe hRun hRel with
    ⟨targetFinal, hTargetRun, hFinalRel⟩
  have hTargetRunState :
      Structured.Code.runState code (source.withEVM target) =
        .ok (source.withEVM targetFinal) := by
    simp [Structured.Code.runState, hTargetRun, RunState.withEVM,
      Bind.bind, Except.bind]
  refine ⟨targetFinal, ?_, hFinalRel⟩
  simpa [RunState.withEVM] using
    (regular_code_of_compileStmtFuel?
      hCompile hBlocks hTargetRunState)

/--
If the independent Structured condition evaluates to false, the compiled
conditional reaches the regular continuation without entering the body.
-/
theorem eventually_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state = .ok (final, false)) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              apply BlocksInProgram.eventually_of_run hBlocks
                (block := generated)
              · simp [generated]
              · simpa [generated] using
                  (Code.run_jumpi_toCfg
                    (target := LabelSupply.label supply 0)
                    (fallthrough := regular) hType hCond)

/--
False conditional execution also produces a regular fragment certificate.
-/
theorem regular_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state = .ok (final, false)) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  have hEventually :=
    eventually_if_false_of_compileStmtFuel? hCompile hBlocks hCond
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              exact
                ⟨{ output with slots := output.slots.tail }, rfl,
                  hEventually⟩

/--
Relational false-branch preservation under concrete procedure frames.
-/
theorem preserves_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (final, false)) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCondition hFrameSafe hCond hRel with
    ⟨targetFinal, hTargetCond, hFinalRel⟩
  refine ⟨targetFinal, ?_, hFinalRel⟩
  simpa [RunState.withEVM] using
    (regular_if_false_of_compileStmtFuel?
      hCompile hBlocks hTargetCond)

/--
True conditional execution composes the generated `jumpi` head with any
checked preservation result for the recursively compiled body.
-/
theorem eventually_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState} {outcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state = .ok (final, true))
    (hBodyEventually :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        cfg.Eventually (LabelSupply.label supply 0) final.evm outcome) :
    cfg.Eventually entry state.evm outcome := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hHeadEventually :
                  cfg.Eventually entry state.evm
                    (.jump (LabelSupply.label supply 0) final.evm) := by
                apply BlocksInProgram.eventually_of_run hBlocks
                  (block := generated)
                · simp [generated]
                · simpa [generated] using
                    (Code.run_jumpi_toCfg
                      (target := LabelSupply.label supply 0)
                      (fallthrough := regular) hType hCond)
              have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              exact
                TypedCfg.Program.Eventually.bind_jump hHeadEventually
                  (hBodyEventually hBody hBodyBlocks)

/--
Regular true-branch execution produces the same regular fragment certificate
as false-branch execution, using the recursive body certificate only for its
semantic execution witness.
-/
theorem regular_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state afterCond final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state =
        .ok (afterCond, true))
    (hBodyRegular :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularExecution bodyResult cfg
          (LabelSupply.label supply 0) regular
          afterCond.evm final.evm) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  have hEventually :
      cfg.Eventually entry state.evm
        (TypedCfg.Outcome.jump regular final.evm) :=
    eventually_if_true_of_compileStmtFuel? hCompile hBlocks hCond
      (by
        intro bodyInput bodyResult hBodyCompile hBodyBlocks
        rcases hBodyRegular hBodyCompile hBodyBlocks with
          ⟨output, hFallthrough, hBodyEventually⟩
        exact hBodyEventually)
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              exact
                ⟨{ output with slots := output.slots.tail }, rfl,
                  hEventually⟩

/--
Relational true-branch preservation composes the generated conditional head
with the recursively compiled body.
-/
theorem preserves_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterCond final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (afterCond, true))
    (hBodyPreserves :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg
          (LabelSupply.label supply 0) regular
          afterCond final tokens) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCondition hFrameSafe hCond hRel with
    ⟨targetAfterCond, hTargetCond, hAfterCondRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              rcases
                  hBodyPreserves hBody hBodyBlocks
                    targetAfterCond hAfterCondRel with
                ⟨targetFinal, hBodyExecution, hFinalRel⟩
              rcases hBodyExecution with
                ⟨bodyOutput, hBodyFallthrough, hBodyEventually⟩
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hHeadEventually :
                  cfg.Eventually entry target
                    (.jump (LabelSupply.label supply 0) targetAfterCond) := by
                apply BlocksInProgram.eventually_of_run hBlocks
                  (block := generated)
                · simp [generated]
                · simpa [generated, RunState.withEVM] using
                    (Code.run_jumpi_toCfg
                      (target := LabelSupply.label supply 0)
                      (fallthrough := regular) hType hTargetCond)
              refine ⟨targetFinal, ?_, hFinalRel⟩
              refine
                ⟨{ output with slots := output.slots.tail }, rfl, ?_⟩
              exact
                TypedCfg.Program.Eventually.bind_jump
                  hHeadEventually hBodyEventually

/--
The straight-line statement compiler preserves the independent Structured
semantics and reaches its supplied regular continuation in one CFG block.
-/
theorem runN_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hRun : Structured.Code.runState code state = .ok final) :
    (resultProgram result entry).runN 1 entry state.evm =
      Except.ok (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      simp [TypedCfg.Program.runN, TypedCfg.Program.step,
        resultProgram, TypedCfg.Program.findBlock?, TypedCfg.Block.run,
        Code.runState_toCfg hType, hRun, Except.map, Bind.bind, Except.bind,
        TypedCfg.Block.runTerm]

/--
Compiled `break` reaches the break continuation selected by the compiler
context.
-/
theorem eventually_brk_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hTarget : ctx.breakLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .brk ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump target state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.jumpOrInvalid, hTarget,
    TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
Compiled `continue` reaches the continue continuation selected by the compiler
context.
-/
theorem eventually_cont_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hTarget : ctx.continueLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .cont ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump target state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.jumpOrInvalid, hTarget,
    TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
Compiled `leave` reaches the procedure-exit continuation selected by the
compiler context.
-/
theorem eventually_leave_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hTarget : ctx.leaveLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .leave ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump target state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.jumpOrInvalid, hTarget,
    TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
The TypedCfg halt outcome records the state immediately before executing the
terminal EVM opcode. The lower-level Assembly simulation executes that opcode
when interpreting this outcome.
-/
theorem eventually_terminal_of_compileStmtFuel?
    {fuel : Nat} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.terminal kind) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.halt kind state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

end Stmt

namespace Switch

def testOutput (valueShape : TypedCfg.Shape) : TypedCfg.Shape :=
  { valueShape with slots := .word :: valueShape.slots }

def casesEntryLabel (base idx : Nat) :
    List (Word × Structured.Block) → Assembly.Label
  | [] => LabelSupply.label base 1
  | _ => TypedCfgCompiler.switchTestLabel base idx

def nextTestLabel (base idx : Nat)
    (rest : List (Word × Structured.Block)) : Assembly.Label :=
  casesEntryLabel base (idx + 1) rest

theorem testBody_type
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue : Word}
    (hHead : valueShape.slots.head? = some slot) :
    TypedCfg.Block.bodyType?
        [.dup 0, .push caseValue, .prim .eq] valueShape =
      some (testOutput valueShape) := by
  cases valueShape with
  | mk slots tail =>
      cases slots with
      | nil =>
          simp at hHead
      | cons head rest =>
          simp [TypedCfg.Block.bodyType?, TypedCfg.Instr.type?,
            TypedCfg.Shape.get?, TypedCfg.Shape.length,
            TypedCfg.Shape.pop, TypedCfg.Shape.pushWords,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α, testOutput]

/--
One generated switch test preserves the retained scrutinee and chooses the
case-entry or next-test label according to the source value comparison.
-/
theorem eventually_test
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {testLabel caseLabel nextTest : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue value : Word}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word}
    (hBlocks : BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead : valueShape.slots.head? = some slot)
    (hRel : StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      cfg.Eventually testLabel target
          (.jump
            (if caseValue = value then caseLabel else nextTest)
            targetFinal) ∧
        StateRel source tokens targetFinal := by
  let dupShape : TypedCfg.Shape :=
    { valueShape with slots := slot :: valueShape.slots }
  let pushShape : TypedCfg.Shape :=
    { dupShape with slots := .literal caseValue :: dupShape.slots }
  have hGet :
      valueShape.get? 0 = some slot := by
    rw [TypedCfg.Shape.get?, ← List.head?_eq_getElem?]
    exact hHead
  have hDupType :
      TypedCfg.Instr.type? (.dup 0) valueShape = some dupShape := by
    simp [TypedCfg.Instr.type?, hGet, dupShape]
  have hPushType :
      TypedCfg.Instr.type? (.push caseValue) dupShape =
        some pushShape := by
    rfl
  have hEqType :
      TypedCfg.Instr.type? (.prim .eq) pushShape =
        some (testOutput valueShape) := by
    have hTestType :=
      testBody_type (caseValue := caseValue) hHead
    simp [TypedCfg.Block.bodyType?, hDupType, hPushType] at hTestType
    exact hTestType
  rcases StateRel.stackView_of_pop hRel hPop with
    ⟨realizedTail, _hTailRealize, hTargetStack⟩
  let afterDup :=
    target.replaceStackAndIncrPC
      (value :: value :: realizedTail)
  let afterPush :=
    afterDup.replaceStackAndIncrPC
      (caseValue :: value :: value :: realizedTail) (pcΔ := 33)
  let afterEq :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq caseValue value :: value :: realizedTail)
  let targetFinal : EVMState :=
    { afterEq with stack := value :: realizedTail }
  have hFinalSame :
      SameRuntimeData targetFinal target := by
    cases target
    simp [targetFinal, afterEq, afterPush, afterDup,
      SameRuntimeData, eraseCfgControl,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hTargetStack ⊢
    exact hTargetStack.symm
  have hDupRun :
      TypedCfg.Instr.runAt (.dup 0) valueShape target =
        .ok (afterDup, dupShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hDupType]
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.dup, hTargetStack, afterDup,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hPushRun :
      TypedCfg.Instr.runAt (.push caseValue) dupShape afterDup =
        .ok (afterPush, pushShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hPushType]
    simp [TypedCfg.Instr.runState, afterPush, afterDup, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hEqRun :
      TypedCfg.Instr.runAt (.prim .eq) pushShape afterPush =
        .ok (afterEq, testOutput valueShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hEqType]
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push,
      afterPush, afterDup, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hBodyRun :
      TypedCfg.Block.runBody
          [.dup 0, .push caseValue, .prim .eq] valueShape target =
        .ok (afterEq, testOutput valueShape) := by
    simp only [TypedCfg.Block.runBody]
    rw [hDupRun]
    simp only [Bind.bind, Except.bind]
    rw [hPushRun]
    simp only [Bind.bind, Except.bind]
    rw [hEqRun]
  refine
    ⟨targetFinal, ?_,
      StateRel.targetCongr hFinalSame hRel⟩
  apply BlocksInProgram.eventually_of_run hBlocks hMem
  simp only [TypedCfg.Block.run, hBodyRun, Bind.bind, Except.bind,
    if_pos rfl]
  have hOneNeZero :
      EvmYul.UInt256.ofNat 1 ≠ EvmYul.UInt256.ofNat 0 := by
    decide
  by_cases hEq : caseValue = value
  · simp [TypedCfg.Block.runTerm, EvmYul.Stack.pop,
      EvmYul.UInt256.eq, hEq, hOneNeZero,
      targetFinal, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [TypedCfg.Block.runTerm, EvmYul.Stack.pop,
      EvmYul.UInt256.eq, hEq,
      targetFinal, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

/--
When the first case matches, the generated test selects that case, its entry
removes the retained scrutinee, and execution continues through the compiled
case body.
-/
theorem regular_cases_head_of_compileCasesFuel?
    {compilerFuel : Nat} {caseValue value : Word}
    {body : Structured.Block} {rest : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx valueShape
            bodyShape regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hEq : caseValue = value)
    (hBodyPreserves :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx supply
            (.generated base (2000 + idx)) bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg
          (.generated base (2000 + idx)) regular
          (source.withEVM { source.evm with stack := stack }) final tokens) :
    RegularPreserves result cfg
      (TypedCfgCompiler.switchTestLabel base idx) regular
      source final tokens := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileCasesFuel? at hCompile
  simp only at hCompile
  simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
    hPopBodyType, Bind.bind, Option.bind] at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx supply
        (.generated base (2000 + idx)) bodyShape regular with
  | none =>
      simp [hBody] at hCompile
  | some bodyResult =>
      simp only [hBody] at hCompile
      cases hTail :
          TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx base
            bodyResult.next (idx + 1) valueShape bodyShape regular with
      | none =>
          simp [hTail] at hCompile
      | some tail =>
          simp only [hTail] at hCompile
          cases hCompile
          have hBodyBlocks : BlocksInProgram bodyResult cfg := by
            intro block hMem
            apply hBlocks block
            simp [hMem]
          intro target hRel
          rcases
              eventually_test
                (testLabel := TypedCfgCompiler.switchTestLabel base idx)
                (caseLabel := LabelSupply.label base (idx + 2))
                (nextTest := nextTestLabel base idx rest)
                (caseValue := caseValue) (value := value)
                hBlocks
                (by
                  left)
                hHead hRel hPop with
            ⟨targetAfterTest, hTestEventually, hAfterTestRel⟩
          have hSelected :
              cfg.Eventually (TypedCfgCompiler.switchTestLabel base idx)
                target
                (.jump (LabelSupply.label base (idx + 2))
                  targetAfterTest) := by
            simpa [hEq] using hTestEventually
          rcases
              BlocksInProgram.eventually_pop_jump
                (entry := LabelSupply.label base (idx + 2))
                (regular := .generated base (2000 + idx))
                (input := valueShape) (output := bodyShape)
                hBlocks (by simp) hPopType hAfterTestRel hPop with
            ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
          rcases
              hBodyPreserves hBody hBodyBlocks
                targetAfterPop hAfterPopRel with
            ⟨targetFinal, hBodyExecution, hFinalRel⟩
          rcases hBodyExecution with
            ⟨_bodyOutput, _hBodyFallthrough, hBodyEventually⟩
          refine ⟨targetFinal, ?_, hFinalRel⟩
          refine ⟨bodyShape, rfl, ?_⟩
          exact
            TypedCfg.Program.Eventually.bind_jump hSelected
              (TypedCfg.Program.Eventually.bind_jump
                hEntryEventually hBodyEventually)

/--
When the first case does not match, its test preserves the retained scrutinee
and delegates to a supplied proof for the next test or the default entry.
-/
theorem regular_cases_tail_of_compileCasesFuel?
    {compilerFuel : Nat} {caseValue value : Word}
    {body : Structured.Block} {rest : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx valueShape
            bodyShape regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hNe : caseValue ≠ value)
    (hNextPreserves :
      ∀ target,
        StateRel source tokens target →
          ∃ targetFinal,
            cfg.Eventually (nextTestLabel base idx rest) target
                (.jump regular targetFinal) ∧
              StateRel final tokens targetFinal) :
    RegularPreserves result cfg
      (TypedCfgCompiler.switchTestLabel base idx) regular
      source final tokens := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileCasesFuel? at hCompile
  simp only at hCompile
  simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
    hPopBodyType, Bind.bind, Option.bind] at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx supply
        (.generated base (2000 + idx)) bodyShape regular with
  | none =>
      simp [hBody] at hCompile
  | some bodyResult =>
      simp only [hBody] at hCompile
      cases hTail :
          TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx base
            bodyResult.next (idx + 1) valueShape bodyShape regular with
      | none =>
          simp [hTail] at hCompile
      | some tail =>
          simp only [hTail] at hCompile
          cases hCompile
          intro target hRel
          rcases
              eventually_test
                (testLabel := TypedCfgCompiler.switchTestLabel base idx)
                (caseLabel := LabelSupply.label base (idx + 2))
                (nextTest := nextTestLabel base idx rest)
                (caseValue := caseValue) (value := value)
                hBlocks
                (by
                  left)
                hHead hRel hPop with
            ⟨targetAfterTest, hTestEventually, hAfterTestRel⟩
          have hSkipped :
              cfg.Eventually (TypedCfgCompiler.switchTestLabel base idx)
                target
                (.jump (nextTestLabel base idx rest)
                  targetAfterTest) := by
            simpa [hNe] using hTestEventually
          rcases hNextPreserves targetAfterTest hAfterTestRel with
            ⟨targetFinal, hNextEventually, hFinalRel⟩
          refine ⟨targetFinal, ?_, hFinalRel⟩
          refine ⟨bodyShape, rfl, ?_⟩
          exact
            TypedCfg.Program.Eventually.bind_jump
              hSkipped hNextEventually

/--
Case-chain preservation follows the independent source selector. A matching
case executes the selected compiled body; misses recurse through generated test
labels; exhausting the list delegates to the default-entry certificate.
-/
theorem path_cases_some_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx base supply idx
        valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = some selected)
    (hCasePreserves :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (.generated base (2000 + caseIdx))
            bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg
          (.generated base (2000 + caseIdx)) regular
          (source.withEVM { source.evm with stack := stack }) final tokens)
    (hDefaultPreserves :
      defaultBody = some selected →
        PathPreserves cfg (LabelSupply.label base 1) regular
          source final tokens) :
    PathPreserves cfg (casesEntryLabel base idx cases) regular
      source final tokens := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = some selected := by
            simpa [Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPreserves hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          have hCompileFull := hCompile
          have hPopBodyType :
              TypedCfg.Block.bodyType? [.pop] valueShape =
                some bodyShape := by
            simp [TypedCfg.Block.bodyType?, hPopType]
          unfold TypedCfgCompiler.compileCasesFuel? at hCompile
          simp only at hCompile
          simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
            hPopBodyType, Bind.bind, Option.bind] at hCompile
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
                supply (.generated base (2000 + idx))
                bodyShape regular with
          | none =>
              simp [hBody] at hCompile
          | some bodyResult =>
              simp only [hBody] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hTailBlocks : BlocksInProgram tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · have hSelected : body = selected := by
                      simpa [Switch.select, hEq] using hSelect
                    subst selected
                    have hRegular :=
                      regular_cases_head_of_compileCasesFuel?
                        hCompileFull hBlocks hHead hPopType hPop hEq
                        (fun hBodyCompile hCompiledBodyBlocks =>
                          hCasePreserves
                            hBodyCompile hCompiledBodyBlocks)
                    simpa [casesEntryLabel] using
                      PathPreserves.of_regular hRegular
                  · have hTailSelect :
                        Switch.select value rest defaultBody =
                          some selected := by
                      simpa [Switch.select, hEq] using hSelect
                    have hTailPreserves :=
                      ih hTail hTailBlocks hTailSelect
                        hCasePreserves hDefaultPreserves
                    have hRegular :=
                      regular_cases_tail_of_compileCasesFuel?
                        hCompileFull hBlocks hHead hPopType hPop hEq
                        hTailPreserves
                    simpa [casesEntryLabel] using
                      PathPreserves.of_regular hRegular

/--
If source selection finds no body, every generated case test misses and the
chain eventually delegates to the no-body default entry.
-/
theorem path_cases_none_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx base supply idx
        valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none)
    (hDefaultPreserves :
      defaultBody = none →
        PathPreserves cfg (LabelSupply.label base 1) regular
          source final tokens) :
    PathPreserves cfg (casesEntryLabel base idx cases) regular
      source final tokens := by
  induction cases generalizing compilerFuel supply idx result with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = none := by
            simpa [Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPreserves hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          have hCompileFull := hCompile
          have hPopBodyType :
              TypedCfg.Block.bodyType? [.pop] valueShape =
                some bodyShape := by
            simp [TypedCfg.Block.bodyType?, hPopType]
          unfold TypedCfgCompiler.compileCasesFuel? at hCompile
          simp only at hCompile
          simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
            hPopBodyType, Bind.bind, Option.bind] at hCompile
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
                supply (.generated base (2000 + idx))
                bodyShape regular with
          | none =>
              simp [hBody] at hCompile
          | some bodyResult =>
              simp only [hBody] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hTailBlocks : BlocksInProgram tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · simp [Switch.select, hEq] at hSelect
                  · have hTailSelect :
                        Switch.select value rest defaultBody = none := by
                      simpa [Switch.select, hEq] using hSelect
                    have hTailPreserves :=
                      ih hTail hTailBlocks hTailSelect
                    have hRegular :=
                      regular_cases_tail_of_compileCasesFuel?
                        hCompileFull hBlocks hHead hPopType hPop hEq
                        hTailPreserves
                    simpa [casesEntryLabel] using
                      PathPreserves.of_regular hRegular

/--
When a switch has no default body, the generated default block removes the
retained scrutinee and reaches the regular continuation.
-/
theorem regular_default_none_of_compileDefaultFuel?
    {compilerFuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1) none ctx
        supply entry valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    RegularPreserves result cfg entry regular source
      (source.withEVM { source.evm with stack := stack }) tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType] at hCompile
  cases hCompile
  apply RegularPreserves.pop_jump
    (input := valueShape) (output := bodyShape) hBlocks
  · simp
  · rfl
  · exact hType
  · exact hPop

/--
A generated nonempty default first removes the retained scrutinee, then
delegates to the compiled default body.
-/
theorem regular_default_some_of_compileDefaultFuel?
    {compilerFuel : Nat} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1) (some body) ctx
        supply entry valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyPreserves :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000) bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg (.generated supply 2000) regular
          (source.withEVM { source.evm with stack := stack }) final tokens) :
    RegularPreserves result cfg entry regular source final tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
        (supply + 1) (.generated supply 2000) bodyShape regular with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType,
        hBody] at hCompile
  | some bodyResult =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType,
        hBody] at hCompile
      cases hCompile
      have hBodyBlocks : BlocksInProgram bodyResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hMem]
      intro target hRel
      rcases
          BlocksInProgram.eventually_pop_jump
            (entry := entry) (regular := .generated supply 2000)
            (input := valueShape) (output := bodyShape)
            hBlocks (by simp) hType hRel hPop with
        ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
      rcases
          hBodyPreserves hBody hBodyBlocks targetAfterPop hAfterPopRel with
        ⟨targetFinal, hBodyExecution, hFinalRel⟩
      rcases hBodyExecution with
        ⟨_bodyOutput, _hBodyFallthrough, hBodyEventually⟩
      refine ⟨targetFinal, ?_, hFinalRel⟩
      refine ⟨bodyShape, rfl, ?_⟩
      exact
        TypedCfg.Program.Eventually.bind_jump
          hEntryEventually hBodyEventually

/--
A source switch that selects a body executes the scrutinee, follows the
generated case/default dispatch, and delegates only the selected source body to
the recursive preservation proof.
-/
theorem preserves_some_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect :
      Switch.select value cases defaultBody = some selected)
    (hSelectedPreserves :
      ∀ {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label}
        {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg bodyEntry regular
          (afterScrutinee.withEVM
            { afterScrutinee.evm with stack := stack })
          final tokens) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCode hFrameSafe hScrutinee hRel with
    ⟨targetAfterScrutinee, hTargetScrutinee, hAfterScrutineeRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCasesCompileRaw :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCasesCompileRaw] at hCompile
          | some caseResult =>
              simp only [hCasesCompileRaw] at hCompile
              have hCasesCompile :
                  TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                      cases ctx supply (supply + 1) 0 valueShape bodyShape
                      regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1)
                    valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefaultCompileRaw] at hCompile
              | some defaultResult =>
                  simp only [hDefaultCompileRaw] at hCompile
                  have hDefaultCompile :
                      TypedCfgCompiler.compileDefaultFuel?
                          (compilerFuel + 1) defaultBody ctx
                          caseResult.next
                          (LabelSupply.label supply 1)
                          valueShape bodyShape regular =
                        some defaultResult := by
                    simpa [bodyShape] using hDefaultCompileRaw
                  cases hCompile
                  have hCaseBlocks : BlocksInProgram caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      BlocksInProgram defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDispatch :
                      PathPreserves cfg
                        (casesEntryLabel supply 0 cases) regular
                        afterScrutinee final tokens := by
                    apply path_cases_some_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hValue hPopType hPop hSelect
                    · intro bodyCompilerFuel caseSupply caseIdx bodyResult
                        hBodyCompile hBodyBlocks
                      exact
                        hSelectedPreserves
                          hBodyCompile hBodyBlocks
                    · intro hDefault
                      have hDefaultSelected :
                          TypedCfgCompiler.compileDefaultFuel?
                              (compilerFuel + 1) (some selected) ctx
                              caseResult.next
                              (LabelSupply.label supply 1)
                              valueShape bodyShape regular =
                            some defaultResult := by
                        simpa [hDefault] using hDefaultCompile
                      apply PathPreserves.of_regular
                      apply regular_default_some_of_compileDefaultFuel?
                        hDefaultSelected hDefaultBlocks hPopType hPop
                      intro bodyResult hBodyCompile hBodyBlocks
                      exact
                        hSelectedPreserves
                          hBodyCompile hBodyBlocks
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadEventually :
                      cfg.Eventually entry target
                        (.jump firstTest targetAfterScrutinee) := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                    · simp [head, TypedCfg.Block.run,
                        Code.runBody_toCfg hType, hTargetScrutinee,
                        Except.map, Bind.bind, Except.bind,
                        TypedCfg.Block.runTerm]
                  rcases hDispatch targetAfterScrutinee
                      hAfterScrutineeRel with
                    ⟨targetFinal, hDispatchEventually, hFinalRel⟩
                  refine ⟨targetFinal, ?_, hFinalRel⟩
                  refine ⟨bodyShape, rfl, ?_⟩
                  exact
                    TypedCfg.Program.Eventually.bind_jump
                      hHeadEventually hDispatchEventually

/--
A source switch that selects no body executes the scrutinee, misses every
generated case test, removes the retained value in the no-body default block,
and reaches the regular continuation.
-/
theorem preserves_none_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none) :
    RegularPreserves result cfg entry regular source
      (afterScrutinee.withEVM
        { afterScrutinee.evm with stack := stack }) tokens := by
  intro target hRel
  rcases StateRel.runCode hFrameSafe hScrutinee hRel with
    ⟨targetAfterScrutinee, hTargetScrutinee, hAfterScrutineeRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCasesCompileRaw :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCasesCompileRaw] at hCompile
          | some caseResult =>
              simp only [hCasesCompileRaw] at hCompile
              have hCasesCompile :
                  TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                      cases ctx supply (supply + 1) 0 valueShape bodyShape
                      regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1)
                    valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefaultCompileRaw] at hCompile
              | some defaultResult =>
                  simp only [hDefaultCompileRaw] at hCompile
                  have hDefaultCompile :
                      TypedCfgCompiler.compileDefaultFuel?
                          (compilerFuel + 1) defaultBody ctx
                          caseResult.next
                          (LabelSupply.label supply 1)
                          valueShape bodyShape regular =
                        some defaultResult := by
                    simpa [bodyShape] using hDefaultCompileRaw
                  cases hCompile
                  have hCaseBlocks : BlocksInProgram caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      BlocksInProgram defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDispatch :
                      PathPreserves cfg
                        (casesEntryLabel supply 0 cases) regular
                        afterScrutinee
                        (afterScrutinee.withEVM
                          { afterScrutinee.evm with stack := stack })
                        tokens := by
                    apply path_cases_none_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hValue hPopType hPop hSelect
                    intro hDefault
                    have hDefaultNone :
                        TypedCfgCompiler.compileDefaultFuel?
                            (compilerFuel + 1) none ctx caseResult.next
                            (LabelSupply.label supply 1)
                            valueShape bodyShape regular =
                          some defaultResult := by
                      simpa [hDefault] using hDefaultCompile
                    apply PathPreserves.of_regular
                    exact
                      regular_default_none_of_compileDefaultFuel?
                        hDefaultNone hDefaultBlocks hPopType hPop
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadEventually :
                      cfg.Eventually entry target
                        (.jump firstTest targetAfterScrutinee) := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                    · simp [head, TypedCfg.Block.run,
                        Code.runBody_toCfg hType, hTargetScrutinee,
                        Except.map, Bind.bind, Except.bind,
                        TypedCfg.Block.runTerm]
                  rcases hDispatch targetAfterScrutinee
                      hAfterScrutineeRel with
                    ⟨targetFinal, hDispatchEventually, hFinalRel⟩
                  refine ⟨targetFinal, ?_, ?_⟩
                  · refine ⟨bodyShape, rfl, ?_⟩
                    exact
                      TypedCfg.Program.Eventually.bind_jump
                        hHeadEventually hDispatchEventually
                  · simpa [RunState.withEVM] using hFinalRel

/--
An empty switch without a default body executes the scrutinee, removes its
value in the generated default block, and reaches the regular continuation.
-/
theorem preserves_empty_none_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
        (.switch scrutinee [] none) ctx supply entry input regular =
          some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value)) :
    RegularPreserves result cfg entry regular source
      (afterScrutinee.withEVM
        { afterScrutinee.evm with stack := stack }) tokens := by
  exact
    preserves_none_of_compileStmtFuel?
      hCompile hBlocks hFrameSafe hScrutinee hPop rfl

end Switch

namespace Loop

/--
The generated loop-condition block follows the independent source condition
and preserves the concrete procedure-frame relation.
-/
theorem eventually_condition
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {cond : Structured.Code} {condValue : Bool}
    {source afterCond : RunState} {tokens : List Word}
    {target : EVMState}
    (hBlocks : BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.Code.toCfg cond) loopInput =
        some condOutput)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (afterCond, condValue))
    (hRel : StateRel source tokens target) :
    ∃ targetAfterCond,
      cfg.Eventually loopLabel target
          (.jump (if condValue then bodyLabel else endLabel)
            targetAfterCond) ∧
        StateRel afterCond tokens targetAfterCond := by
  rcases StateRel.runCondition hFrameSafe hCond hRel with
    ⟨targetAfterCond, hTargetCond, hAfterCondRel⟩
  refine ⟨targetAfterCond, ?_, hAfterCondRel⟩
  apply BlocksInProgram.eventually_of_run hBlocks hMem
  simpa [RunState.withEVM] using
    (Code.run_jumpi_toCfg
      (target := bodyLabel) (fallthrough := endLabel)
      hType hTargetCond)

end Loop

namespace Block

/--
Ambient-program form of empty statement-list preservation.
-/
theorem eventually_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump regular state.evm) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  refine ⟨1, ?_⟩
  simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind,
    generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
    TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
The empty statement-list compiler produces a regular execution certificate.
-/
theorem regular_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    RegularExecution result cfg entry regular state.evm state.evm := by
  have hEventually :=
    eventually_nil_of_compileStmtListFuel?
      (state := state) hCompile hBlocks
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  exact ⟨input, rfl, hEventually⟩

/--
Generic regular statement-list composition.

The two premises are exactly the recursive obligations of a source-evaluation
induction. Compiler result decomposition, fallthrough consistency, ambient
block containment, and execution fuel composition are discharged here once.
-/
theorem regular_cons_of_compileStmtListFuel?
    {compilerFuel : Nat} {stmt : Stmt} {rest : List Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state middle final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
        (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead :
      ∀ {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        BlocksInProgram headResult cfg →
        RegularExecution headResult cfg entry
          (TypedCfgCompiler.restLabel supply) state.evm middle.evm)
    (hTail :
      ∀ {headResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape}
        {tailResult : TypedCfgCompiler.Result},
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        BlocksInProgram tailResult cfg →
        RegularExecution tailResult cfg
          (TypedCfgCompiler.restLabel supply) regular
          middle.evm final.evm) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  cases hHeadCompile :
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
        entry input (TypedCfgCompiler.restLabel supply) with
  | none =>
      simp [hHeadCompile] at hCompile
  | some headResult =>
      cases hFallthrough : headResult.fallthrough? with
      | none =>
          simp [hHeadCompile, hFallthrough] at hCompile
          cases hCompile
          rcases hHead hHeadCompile hBlocks with
            ⟨output, hOutput, hEventually⟩
          rw [hFallthrough] at hOutput
          cases hOutput
      | some tailInput =>
          cases hTailCompile :
              TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
                headResult.next (TypedCfgCompiler.restLabel supply)
                tailInput regular with
          | none =>
              simp [hHeadCompile, hFallthrough, hTailCompile] at hCompile
          | some tailResult =>
              simp [hHeadCompile, hFallthrough, hTailCompile] at hCompile
              cases hCompile
              have hHeadBlocks :=
                BlocksInProgram.left_of_append hBlocks
              have hTailBlocks :=
                BlocksInProgram.right_of_append hBlocks
              exact
                RegularExecution.append
                  (hHead hHeadCompile hHeadBlocks)
                  (hTail hFallthrough hTailCompile hTailBlocks)

/--
An empty compiled statement list reaches its supplied regular continuation
without changing the source EVM state.
-/
theorem runN_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result) :
    (resultProgram result entry).runN 1 entry state.evm =
      Except.ok (TypedCfg.Outcome.jump regular state.evm) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  simp [TypedCfg.Program.runN, TypedCfg.Program.step,
    resultProgram, TypedCfg.Program.findBlock?, TypedCfg.Block.run,
    TypedCfg.Block.runBody, TypedCfg.Block.runTerm, Bind.bind, Except.bind]

end Block

end TypedCfgPreservation
end Structured
end EvmCompiler
