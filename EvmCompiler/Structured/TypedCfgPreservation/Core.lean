import EvmCompiler.Structured.TypedCfgCompilerFacts
import EvmCompiler.Simulation.Outcome
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

open Assembly

attribute [local simp] Assembly.PrimStep.idRun_eq

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
Control position and lowering-only resource counters are compared through
Assembly's shared control-erased observation boundary, while available gas
remains equal so the Structured `gas` primitive has the same CFG-level meaning.
-/

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

theorem returns_cons_of_tokens_cons
    {source : RunState} {token : Word} {tokens : List Word}
    {target : EVMState}
    (hRel : StateRel source (token :: tokens) target) :
    ∃ frame returns, source.returns = frame :: returns := by
  rcases hRel with ⟨realized, hRealize, hSame⟩
  cases hReturns : source.returns with
  | nil =>
      simp [hReturns, realizeStack] at hRealize
  | cons frame returns =>
      exact ⟨frame, returns, rfl⟩

/--
Terminal execution preserves realization of ghost return frames. The terminal
operation consumes only source stack operands, so compiler-owned return data
remains an untouched suffix.
-/
theorem terminal
    {kind : Assembly.HaltKind}
    {source : RunState} {sourceFinal target : EVMState}
    {tokens : List Word}
    (hRel : StateRel source tokens target)
    (hStep :
      Structured.Terminal.step kind source.evm = .ok sourceFinal) :
    ∃ targetFinal,
      Structured.Terminal.step kind target = .ok targetFinal ∧
        StateRel (source.withEVM sourceFinal) tokens targetFinal := by
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
      have hFramed :=
        Structured.Terminal.step_append_stack
          kind source.evm sourceFinal hidden hStep
      have hCongruence :=
        Structured.Terminal.step_map_eraseRuntimeControl kind hSame
      rw [hFramed] at hCongruence
      cases hTarget :
          Structured.Terminal.step kind target with
      | error err =>
          simp [hTarget, Except.map] at hCongruence
      | ok targetFinal =>
          simp [hTarget, Except.map] at hCongruence
          refine ⟨targetFinal, rfl, ?_⟩
          refine ⟨sourceFinal.stack ++ hidden, ?_, ?_⟩
          · have hFinalAppend :=
              realizeStack_append_prefix sourceFinal.stack []
                source.returns tokens
            simpa [RunState.withEVM, hHidden] using hFinalAppend
          · simpa [RunState.withEVM] using hCongruence

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
              eraseRuntimeControl, EvmYul.EVM.State.replaceStackAndIncrPC,
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
          · simp [Structured.Code.popCondition,
              EffectSemantics.Code.popCondition,
              EffectSemantics.Control.Code.popCondition, targetFinal,
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
  cases instr with
  | push value => rfl
  | op op =>
      cases op <;> rfl
  | bindLocals offset names => rfl
  | bindScratch baseDepth name slot => rfl

end BasicInstr

namespace BasicOp

/--
Typing the existing lowering of a Structured primitive exposes the same
concrete stack delta declared by its Assembly primitive.
-/
theorem type_length_toCfg
    {op : Structured.BasicOp} {input output : TypedCfg.Shape}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.basicOpToCfg op) input =
        some output) :
    ∃ inputArity outputArity,
      op.toPrimOp.stackArity? = some (inputArity, outputArity) ∧
        inputArity ≤ input.length ∧
        output.length =
          input.length - inputArity + outputArity := by
  generalize hCfg :
      TypedCfgCompiler.BasicInstr.basicOpToCfg op = cfgInstr at hType
  cases cfgInstr with
  | prim prim =>
      have hPrim : prim = op.toPrimOp := by
        cases op <;>
          simp [TypedCfgCompiler.BasicInstr.basicOpToCfg,
            Structured.BasicOp.toPrimOp] at hCfg
        all_goals
          simpa using hCfg.symm
      subst prim
      cases hArity : op.toPrimOp.stackArity? with
      | none =>
          simp [TypedCfg.Instr.type?, hArity] at hType
      | some arity =>
          rcases arity with ⟨inputArity, outputArity⟩
          have hLength :=
            TypedCfg.Instr.length_of_type?_prim hArity hType
          exact
            ⟨inputArity, outputArity, rfl,
              hLength.1, hLength.2⟩
  | pop =>
      have hArity :
          op.toPrimOp.stackArity? = some (1, 0) := by
        cases op <;>
          simp [TypedCfgCompiler.BasicInstr.basicOpToCfg,
            Structured.BasicOp.toPrimOp,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α] at hCfg ⊢
      have hLength :=
        TypedCfg.Instr.length_of_type?_pop hType
      exact ⟨1, 0, hArity, hLength.1, hLength.2⟩
  | dup depth =>
      have hArity :
          op.toPrimOp.stackArity? =
            some (depth + 1, depth + 2) := by
        cases op <;>
          simp [TypedCfgCompiler.BasicInstr.basicOpToCfg,
            Structured.BasicOp.toPrimOp,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α] at hCfg ⊢ <;>
          omega
      have hLength :=
        TypedCfg.Instr.length_of_type?_dup hType
      refine
        ⟨depth + 1, depth + 2, hArity,
          hLength.2.1, ?_⟩
      omega
  | swap depth =>
      have hArity :
          op.toPrimOp.stackArity? =
            some (depth + 2, depth + 2) := by
        cases op <;>
          simp [TypedCfgCompiler.BasicInstr.basicOpToCfg,
            Structured.BasicOp.toPrimOp,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α] at hCfg ⊢ <;>
          omega
      have hLength :=
        TypedCfg.Instr.length_of_type?_swap hType
      refine
        ⟨depth + 2, depth + 2, hArity,
          hLength.2.1, ?_⟩
      omega
  | push value | returnToken value | bindLocals value names
  | bindScratch value name slot | relabel target | unwind target =>
      cases op <;>
        simp [TypedCfgCompiler.BasicInstr.basicOpToCfg] at hCfg

/--
Structured primitive execution is insensitive to CFG-owned control counters.
The one admitted observer outside `continuingStep?`, `gas`, is covered because
`SameRuntimeData` retains the complete shared machine state.
-/
theorem step_map_eraseRuntimeControl
    {op : Structured.BasicOp} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (op.step target).map eraseRuntimeControl =
      (op.step source).map eraseRuntimeControl := by
  unfold Structured.BasicOp.step
  simp only [Assembly.Target.stepInstr_prim]
  cases hStep : op.toPrimOp.continuingStep? with
  | some step =>
      rw [Assembly.PrimOp.step_eq_continuingStep_run hStep target,
        Assembly.PrimOp.step_eq_continuingStep_run hStep source]
      exact Assembly.PrimStep.run_map_eraseRuntimeControl hRel
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
              eraseRuntimeControl =
            (EvmYul.EVM.machineStateOp EvmYul.MachineState.gas source).map
              eraseRuntimeControl
        exact
          Assembly.PrimStep.run_map_eraseRuntimeControl
            (step := .machineState EvmYul.MachineState.gas) hRel
      all_goals
        rfl

end BasicOp

namespace BasicInstr

/--
One successfully executed Structured instruction preserves the concrete lower
bound tracked by the type of its existing TypedCfg lowering.
-/
theorem step_stack_bound_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state final : EVMState}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hBound : input.length ≤ state.stack.length)
    (hStep : instr.step state = .ok final) :
    output.length ≤ final.stack.length := by
  cases instr with
  | push value =>
      simp [TypedCfgCompiler.BasicInstr.toCfg,
        TypedCfg.Instr.type?] at hType
      cases hType
      simp [Structured.BasicInstr.step,
        Assembly.Target.stepInstr] at hStep
      cases hStep
      change input.slots.length ≤ state.stack.length at hBound
      simp [TypedCfg.Shape.length,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      omega
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            hShapeBound, hOutputLength⟩ :=
        BasicOp.type_length_toCfg hType
      have hActualBound :
          inputArity ≤ state.stack.length :=
        Nat.le_trans hShapeBound hBound
      have hFinalLength :
          final.stack.length =
            state.stack.length - inputArity + outputArity := by
        apply
          Assembly.PrimOp.step_stack_length_of_stackArity
            hArity
        simpa [Structured.BasicInstr.step,
          Structured.BasicOp.step,
          Assembly.Target.stepInstr] using hStep
      omega
  | bindLocals offset names =>
      have hOutputLength :=
        TypedCfg.Instr.length_of_type?_bindLocals hType
      simp [Structured.BasicInstr.step] at hStep
      cases hStep
      omega
  | bindScratch baseDepth name slot =>
      have hOutputLength :=
        TypedCfg.Instr.length_of_type?_bindScratch hType
      simp [Structured.BasicInstr.step] at hStep
      cases hStep
      omega

/--
One successfully executed Structured instruction preserves an exact symbolic
stack length when no untracked caller suffix is present.
-/
theorem step_stack_length_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state final : EVMState}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hLength : input.length = state.stack.length)
    (hStep : instr.step state = .ok final) :
    output.length = final.stack.length := by
  cases instr with
  | push value =>
      simp [TypedCfgCompiler.BasicInstr.toCfg,
        TypedCfg.Instr.type?] at hType
      cases hType
      simp [Structured.BasicInstr.step,
        Assembly.Target.stepInstr] at hStep
      cases hStep
      change input.slots.length = state.stack.length at hLength
      simp [TypedCfg.Shape.length,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      omega
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            hShapeBound, hOutputLength⟩ :=
        BasicOp.type_length_toCfg hType
      have hActualBound :
          inputArity ≤ state.stack.length := by
        rw [← hLength]
        exact hShapeBound
      have hFinalLength :
          final.stack.length =
            state.stack.length - inputArity + outputArity := by
        apply
          Assembly.PrimOp.step_stack_length_of_stackArity
            hArity
        simpa [Structured.BasicInstr.step,
          Structured.BasicOp.step,
          Assembly.Target.stepInstr] using hStep
      omega
  | bindLocals offset names =>
      have hOutputLength :=
        TypedCfg.Instr.length_of_type?_bindLocals hType
      simp [Structured.BasicInstr.step] at hStep
      cases hStep
      omega
  | bindScratch baseDepth name slot =>
      have hOutputLength :=
        TypedCfg.Instr.length_of_type?_bindScratch hType
      simp [Structured.BasicInstr.step] at hStep
      cases hStep
      omega

/--
One accepted Structured source instruction preserves the stack bound tracked
by the source-visible projection of its full TypedCfg shape.
-/
theorem step_sourceLength_bound_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state final : EVMState}
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe? instr input output = true)
    (hBound :
      TypedCfgCompiler.Shape.sourceLength input ≤ state.stack.length)
    (hStep : instr.step state = .ok final) :
    TypedCfgCompiler.Shape.sourceLength output ≤ final.stack.length := by
  have hSourceType :=
    TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe
  exact
    step_stack_bound_of_type hSourceType hBound hStep

/--
One accepted Structured source instruction preserves an exact source-visible
frame length.
-/
theorem step_sourceLength_eq_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state final : EVMState}
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe? instr input output = true)
    (hLength :
      TypedCfgCompiler.Shape.sourceLength input = state.stack.length)
    (hStep : instr.step state = .ok final) :
    TypedCfgCompiler.Shape.sourceLength output =
      final.stack.length := by
  have hSourceType :=
    TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe
  exact
    step_stack_length_of_type hSourceType hLength hStep

/--
An accepted Structured source instruction cannot introduce a compiler-owned
return token. If the output carries one, the input already carried one.
-/
theorem input_returnTokenDepth?_eq_some_of_output
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {outputDepth : Nat}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe? instr input output = true)
    (hOutputDepth : output.returnTokenDepth? = some outputDepth) :
    ∃ inputDepth, input.returnTokenDepth? = some inputDepth := by
  cases hInputDepth : input.returnTokenDepth? with
  | some inputDepth =>
      exact ⟨inputDepth, rfl⟩
  | none =>
      have hInputView :
          TypedCfgCompiler.Shape.sourceView input = input :=
        TypedCfgCompilerFacts.Shape.sourceView_eq_self_of_returnTokenDepth?_eq_none
          hInputDepth
      have hSourceType :=
        TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe
      rw [hInputView] at hSourceType
      have hOutputEq :
          output = TypedCfgCompiler.Shape.sourceView output :=
        Option.some.inj (hType.symm.trans hSourceType)
      exact False.elim
        (TypedCfgCompilerFacts.Shape.sourceView_ne_self_of_returnTokenDepth?_eq_some
            hOutputDepth hOutputEq.symm)

/--
Accepted Structured instructions transform the source-visible prefix and the
full TypedCfg shape by the same stack delta. Equivalently, the size of the
compiler-owned hidden suffix is unchanged.
-/
theorem length_balance_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe? instr input output = true) :
    output.length + TypedCfgCompiler.Shape.sourceLength input =
      TypedCfgCompiler.Shape.sourceLength output + input.length := by
  have hSourceType :=
    TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe
  cases instr with
  | push value =>
      simp [TypedCfgCompiler.BasicInstr.toCfg,
        TypedCfg.Instr.type?] at hType hSourceType
      subst output
      have hSourceLength := congrArg TypedCfg.Shape.length hSourceType
      simp [TypedCfgCompiler.Shape.sourceLength,
        TypedCfg.Shape.length] at hSourceLength ⊢
      omega
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            _hInputBound, hOutputLength⟩ :=
        BasicOp.type_length_toCfg hType
      obtain
          ⟨sourceInputArity, sourceOutputArity, hSourceArity,
            _hSourceInputBound, hSourceOutputLength⟩ :=
        BasicOp.type_length_toCfg hSourceType
      have hArities :
          (sourceInputArity, sourceOutputArity) =
            (inputArity, outputArity) :=
        Option.some.inj (hSourceArity.symm.trans hArity)
      cases hArities
      change
        output.length +
            (TypedCfgCompiler.Shape.sourceView input).length =
          (TypedCfgCompiler.Shape.sourceView output).length +
            input.length
      omega
  | bindLocals offset names =>
      have hOutputLength :=
        TypedCfg.Instr.length_of_type?_bindLocals hType
      have hSourceOutputLength :=
        TypedCfg.Instr.length_of_type?_bindLocals hSourceType
      change
        output.length +
            (TypedCfgCompiler.Shape.sourceView input).length =
          (TypedCfgCompiler.Shape.sourceView output).length +
            input.length
      omega
  | bindScratch baseDepth name slot =>
      have hOutputLength :=
        TypedCfg.Instr.length_of_type?_bindScratch hType
      have hSourceOutputLength :=
        TypedCfg.Instr.length_of_type?_bindScratch hSourceType
      change
        output.length +
            (TypedCfgCompiler.Shape.sourceView input).length =
          (TypedCfgCompiler.Shape.sourceView output).length +
            input.length
      omega

/--
Accepted Structured instructions cannot consume the active procedure's hidden
return token.
-/
theorem output_returnTokenDepth?_eq_some_of_input
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {inputDepth : Nat}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe? instr input output = true)
    (hInputDepth : input.returnTokenDepth? = some inputDepth) :
    ∃ outputDepth, output.returnTokenDepth? = some outputDepth := by
  have hInputSource :
      TypedCfgCompiler.Shape.sourceLength input = inputDepth :=
    TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some
      hInputDepth
  have hInputLt :
      inputDepth < input.length :=
    TypedCfgCompilerFacts.Shape.returnTokenDepth?_lt_length hInputDepth
  have hBalance := length_balance_of_type hType hSafe
  have hOutputGap :
      TypedCfgCompiler.Shape.sourceLength output < output.length := by
    omega
  cases hOutputDepth : output.returnTokenDepth? with
  | some outputDepth =>
      exact ⟨outputDepth, rfl⟩
  | none =>
      have hOutputSource :
          TypedCfgCompiler.Shape.sourceLength output = output.length := by
        unfold TypedCfgCompiler.Shape.sourceLength
        rw [
          TypedCfgCompilerFacts.Shape.sourceView_eq_self_of_returnTokenDepth?_eq_none
            hOutputDepth]
      omega

namespace Code

/--
Accepted Structured code cannot introduce a compiler-owned return token.
Therefore an active output shape implies an active input shape for the entire
typed straight-line fragment.
-/
theorem input_returnTokenDepth?_eq_some_of_output
    {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {outputDepth : Nat}
    (hType :
      TypedCfgCompiler.Code.type? code input = some output)
    (hOutputDepth : output.returnTokenDepth? = some outputDepth) :
    ∃ inputDepth, input.returnTokenDepth? = some inputDepth := by
  induction code generalizing input output with
  | nil =>
      simp [TypedCfgCompiler.Code.type?] at hType
      subst output
      exact ⟨outputDepth, hOutputDepth⟩
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hMiddle :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hMiddle] at hType
      | some middle =>
          cases hSafe :
              TypedCfgCompiler.BasicInstr.sourceSafe?
                instr input middle with
          | false =>
              simp [hMiddle, hSafe] at hType
          | true =>
              have hRestType :
                  TypedCfgCompiler.Code.type? rest middle =
                    some output := by
                simpa [hMiddle, hSafe] using hType
              obtain ⟨middleDepth, hMiddleDepth⟩ :=
                ih hRestType hOutputDepth
              exact
                BasicInstr.input_returnTokenDepth?_eq_some_of_output
                  hMiddle hSafe hMiddleDepth

end Code

/--
Accepted Structured code cannot consume the active procedure's hidden return
token.
-/
theorem Code.output_returnTokenDepth?_eq_some_of_input
    {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {inputDepth : Nat}
    (hType :
      TypedCfgCompiler.Code.type? code input = some output)
    (hInputDepth : input.returnTokenDepth? = some inputDepth) :
    ∃ outputDepth, output.returnTokenDepth? = some outputDepth := by
  induction code generalizing input output inputDepth with
  | nil =>
      simp [TypedCfgCompiler.Code.type?] at hType
      subst output
      exact ⟨inputDepth, hInputDepth⟩
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hMiddle :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hMiddle] at hType
      | some middle =>
          cases hSafe :
              TypedCfgCompiler.BasicInstr.sourceSafe?
                instr input middle with
          | false =>
              simp [hMiddle, hSafe] at hType
          | true =>
              have hRestType :
                  TypedCfgCompiler.Code.type? rest middle =
                    some output := by
                simpa [hMiddle, hSafe] using hType
              obtain ⟨middleDepth, hMiddleDepth⟩ :=
                BasicInstr.output_returnTokenDepth?_eq_some_of_input
                  hMiddle hSafe hInputDepth
              exact ih hRestType hMiddleDepth

/--
An accepted Structured source instruction preserves the two-mode source-frame
invariant: caller frames retain a lower bound, while active procedure frames
retain an exact source-visible length above their return token.
-/
theorem step_sourceFrameFits_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state final : EVMState}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe? instr input output = true)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input state.stack.length)
    (hStep : instr.step state = .ok final) :
    TypedCfgCompiler.Shape.SourceFrameFits
      output final.stack.length := by
  constructor
  · exact step_sourceLength_bound_of_type hSafe hFits.1 hStep
  · intro outputDepth hOutputDepth
    obtain ⟨inputDepth, hInputDepth⟩ :=
      input_returnTokenDepth?_eq_some_of_output
        hType hSafe hOutputDepth
    have hInputSource :
        TypedCfgCompiler.Shape.sourceLength input = inputDepth :=
      TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some
        hInputDepth
    have hInputLength : state.stack.length = inputDepth :=
      hFits.2 inputDepth hInputDepth
    have hStepLength :
        TypedCfgCompiler.Shape.sourceLength output =
          final.stack.length :=
      step_sourceLength_eq_of_type hSafe
        (hInputSource.trans hInputLength.symm) hStep
    have hOutputSource :
        TypedCfgCompiler.Shape.sourceLength output = outputDepth :=
      TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some
        hOutputDepth
    omega

/--
Typed Structured execution cannot become successful only by appending
compiler-owned stack data below the visible source prefix.
-/
theorem exists_step_of_type_bound_append
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state framedFinal : EVMState}
    {hidden : EvmYul.Stack Word}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hBound : input.length ≤ state.stack.length)
    (hFramed :
      instr.step { state with stack := state.stack ++ hidden } =
        .ok framedFinal) :
    ∃ final, instr.step state = .ok final := by
  cases instr with
  | push value =>
      simp [Structured.BasicInstr.step,
        Assembly.Target.stepInstr]
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            hShapeBound, _hOutputLength⟩ :=
        BasicOp.type_length_toCfg hType
      have hActualBound :
          inputArity ≤ state.stack.length :=
        Nat.le_trans hShapeBound hBound
      simpa [Structured.BasicInstr.step,
        Structured.BasicOp.step,
        Assembly.Target.stepInstr] using
        Assembly.PrimOp.exists_step_of_stackArity_le_of_append_step
          hArity hActualBound
          (by simpa [Structured.BasicInstr.step,
            Structured.BasicOp.step,
            Assembly.Target.stepInstr] using hFramed)
  | bindLocals offset names =>
      exact ⟨state, rfl⟩
  | bindScratch baseDepth name slot =>
      exact ⟨state, rfl⟩

/--
Typed Structured execution preserves an appended compiler-owned suffix modulo
the control counters erased by the adjacent state relation.
-/
theorem step_append_stack_rel_of_type
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state final framedFinal : EVMState}
    {hidden : EvmYul.Stack Word}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hBound : input.length ≤ state.stack.length)
    (hRun : instr.step state = .ok final)
    (hFramed :
      instr.step { state with stack := state.stack ++ hidden } =
        .ok framedFinal) :
    SameRuntimeData
      framedFinal
      { final with stack := final.stack ++ hidden } := by
  cases instr with
  | push value =>
      simp [Structured.BasicInstr.step,
        Assembly.Target.stepInstr] at hRun hFramed
      subst final
      subst framedFinal
      simp [SameRuntimeData, eraseRuntimeControl,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            hShapeBound, _hOutputLength⟩ :=
        BasicOp.type_length_toCfg hType
      have hActualBound :
          inputArity ≤ state.stack.length :=
        Nat.le_trans hShapeBound hBound
      exact
        Assembly.PrimOp.step_append_stack_rel_of_stackArity_le
          hArity hActualBound
          (by simpa [Structured.BasicInstr.step,
            Structured.BasicOp.step,
            Assembly.Target.stepInstr] using hRun)
          (by simpa [Structured.BasicInstr.step,
            Structured.BasicOp.step,
            Assembly.Target.stepInstr] using hFramed)
  | bindLocals offset names =>
      simp [Structured.BasicInstr.step] at hRun hFramed
      subst final
      subst framedFinal
      exact
        SameRuntimeData.replaceStack
          (SameRuntimeData.refl state) rfl
  | bindScratch baseDepth name slot =>
      simp [Structured.BasicInstr.step] at hRun hFramed
      subst final
      subst framedFinal
      exact
        SameRuntimeData.replaceStack
          (SameRuntimeData.refl state) rfl

theorem step_map_eraseRuntimeControl
    {instr : Structured.BasicInstr} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (instr.step target).map eraseRuntimeControl =
      (instr.step source).map eraseRuntimeControl := by
  cases instr with
  | push value =>
      cases target with
      | mk targetShared targetPc targetStack targetExec =>
          cases source with
          | mk sourceShared sourcePc sourceStack sourceExec =>
              simp [SameRuntimeData, eraseRuntimeControl] at hRel
              rcases hRel with ⟨rfl, rfl⟩
              simp [Structured.BasicInstr.step, Assembly.Target.stepInstr,
                Except.map, eraseRuntimeControl,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
  | op op =>
      exact BasicOp.step_map_eraseRuntimeControl hRel
  | bindLocals offset names =>
      simpa [Structured.BasicInstr.step, Except.map] using
        congrArg
          (fun state =>
            (Except.ok state : Except EVMException EVMState))
          hRel
  | bindScratch baseDepth name slot =>
      simpa [Structured.BasicInstr.step, Except.map] using
        congrArg
          (fun state =>
            (Except.ok state : Except EVMException EVMState))
          hRel

end BasicInstr

namespace Code

/--
Straight-line Structured execution is congruent under the control-erased
runtime relation.
-/
theorem run_map_eraseRuntimeControl
    {code : Structured.Code} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    (Structured.Code.run code target).map eraseRuntimeControl =
      (Structured.Code.run code source).map eraseRuntimeControl := by
  induction code generalizing target source with
  | nil =>
      simpa [Structured.Code.run, EffectSemantics.Code.run, Except.map] using hRel
  | cons instr rest ih =>
      have hHead :=
        BasicInstr.step_map_eraseRuntimeControl
          (instr := instr) hRel
      cases hTarget : instr.step target with
      | error targetErr =>
          cases hSource : instr.step source with
          | error sourceErr =>
              simpa [Structured.Code.run, EffectSemantics.Code.run, hTarget, hSource,
                Except.map, Bind.bind, Except.bind] using hHead
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hHead
      | ok targetFinal =>
          cases hSource : instr.step source with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hHead
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hHead
              simpa [Structured.Code.run, EffectSemantics.Code.run, hTarget, hSource,
                Bind.bind, Except.bind] using
                  ih (target := targetFinal) (source := sourceFinal) hHead

theorem run_sameRuntimeData_of_ok
    {code : Structured.Code} {target source targetFinal sourceFinal : EVMState}
    (hRel : SameRuntimeData target source)
    (hTarget : Structured.Code.run code target = .ok targetFinal)
    (hSource : Structured.Code.run code source = .ok sourceFinal) :
    SameRuntimeData targetFinal sourceFinal := by
  have hRun := run_map_eraseRuntimeControl (code := code) hRel
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
            Code.run_map_eraseRuntimeControl (code := code) hSame
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
  change
    (EffectSemantics.Code.runCondition
        EffectSemantics.Ordinary.evmStateModel
        EffectSemantics.Ordinary.handler code source.evm).bind
        (fun result => .ok (source.withEVM result.1, result.2)) =
      .ok (final, cond) at hRun
  rw [EffectSemantics.Code.runCondition_eq_run_bind,
    EffectSemantics.Code.ordinary_evm_run] at hRun
  cases hSourceCode : Structured.Code.run code source.evm with
  | error err =>
      simp [hSourceCode, Bind.bind, Except.bind] at hRun
  | ok afterCode =>
      cases hSourcePop : afterCode.stack.pop with
      | none =>
          simp [hSourceCode, Structured.Code.popCondition,
            EffectSemantics.Code.popCondition,
            EffectSemantics.Control.Code.popCondition, hSourcePop,
            Bind.bind, Except.bind] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [hSourceCode, Structured.Code.popCondition,
            EffectSemantics.Code.popCondition,
            EffectSemantics.Control.Code.popCondition, hSourcePop,
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
          have hTargetCondition :
              Structured.Code.runCondition code target =
                .ok
                  (targetFinal,
                    value != EvmYul.UInt256.ofNat 0) := by
            unfold Structured.Code.runCondition
            rw [EffectSemantics.Code.runCondition_eq_run_bind,
              EffectSemantics.Code.ordinary_evm_run, hTargetCode]
            change
              EffectSemantics.Code.popCondition
                  EffectSemantics.Ordinary.evmStateModel targetAfterCode =
                .ok
                  (targetFinal,
                    value != EvmYul.UInt256.ofNat 0) at hTargetPop
            exact hTargetPop
          refine ⟨targetFinal, ?_, ?_⟩
          · simp [Structured.Code.runConditionState,
              hTargetCondition,
              Bind.bind, Except.bind, RunState.withEVM]
          · simpa [RunState.withEVM] using hFinalRel

end StateRel

namespace CallStack

theorem splitArgs?_eq_some
    {argc : Nat} {stack args callerStack : EvmYul.Stack Word}
    (hSplit :
      Structured.StackFrame.splitArgs? argc stack =
        some (args, callerStack)) :
    args.length = argc ∧ stack = args ++ callerStack := by
  unfold Structured.StackFrame.splitArgs? at hSplit
  by_cases hBound : argc ≤ stack.length
  · simp [hBound] at hSplit
    rcases hSplit with ⟨rfl, rfl⟩
    constructor
    · simp [List.length_take, Nat.min_eq_left hBound]
    · exact (List.take_append_drop argc stack).symm
  · simp [hBound] at hSplit

theorem runState_swap_eq_swap
    {depth : Nat} {shape : TypedCfg.Shape} {state : EVMState}
    (hBound : depth < 16) :
    TypedCfg.Instr.runState (.swap depth) shape state =
      EvmYul.swap (depth + 1) state := by
  interval_cases depth <;> rfl

/--
The call-entry shuffle moves a freshly pushed return token below exactly the
visible argument prefix, preserving all runtime data other than CFG control.
-/
theorem runBody_sinkTopUnder
    {input output : TypedCfg.Shape} {state : EVMState}
    (args suffix : EvmYul.Stack Word) (token : Word)
    (hType :
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.sinkTopUnder args.length) input =
        some output)
    (hBound : args.length ≤ 16) :
    ∃ final,
      TypedCfg.Block.runBody
          (TypedCfgCompiler.sinkTopUnder args.length) input
          { state with stack := token :: args ++ suffix } =
        .ok (final, output) ∧
      final.stack = args ++ [token] ++ suffix ∧
      SameRuntimeData final
        { state with stack := args ++ [token] ++ suffix } := by
  induction args using List.reverseRecOn generalizing input output state token suffix with
  | nil =>
      simp [TypedCfgCompiler.sinkTopUnder,
        TypedCfg.Block.bodyType?, TypedCfg.Block.runBody] at hType
      cases hType
      exact
        ⟨{ state with stack := [token] ++ suffix }, rfl, rfl,
          SameRuntimeData.refl _⟩
  | append_singleton front last ih =>
      have hSwapBound : front.length < 16 := by
        simp [List.length_append] at hBound
        omega
      have hFrontBound : front.length ≤ 16 := by omega
      simp only [List.length_append, List.length_singleton,
        Nat.add_one, TypedCfgCompiler.sinkTopUnder,
        TypedCfg.Block.bodyType?] at hType
      cases hHeadType :
          TypedCfg.Instr.type? (.swap front.length) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
          simp [hHeadType] at hType
          let before : EVMState :=
            { state with stack := token :: front ++ [last] ++ suffix }
          let afterSwap : EVMState :=
            before.replaceStackAndIncrPC
              (last :: front ++ [token] ++ suffix)
          have hRunSwap :
              TypedCfg.Instr.runAt (.swap front.length) input before =
                .ok (afterSwap, middle) := by
            unfold TypedCfg.Instr.runAt
            rw [hHeadType]
            simp only [Bind.bind, Except.bind]
            rw [runState_swap_eq_swap hSwapBound]
            rw [Assembly.StackShuffle.swap_snoc
              (state := before) (front := front) (suffix := suffix)
              (top := token) (last := last)]
            rfl
          rcases
              ih (input := middle) (output := output)
                (state := afterSwap) (token := last)
                (suffix := token :: suffix) hType hFrontBound with
            ⟨final, hRunTail, hStack, hSame⟩
          refine ⟨final, ?_, ?_, ?_⟩
          · rw [show
              TypedCfgCompiler.sinkTopUnder (front ++ [last]).length =
                .swap front.length ::
                  TypedCfgCompiler.sinkTopUnder front.length by
                simp [TypedCfgCompiler.sinkTopUnder]]
            unfold TypedCfg.Block.runBody
            have hRunSwap' :
                TypedCfg.Instr.runAt (.swap front.length) input
                    { state with
                      stack := token :: (front ++ [last]) ++ suffix } =
                  .ok (afterSwap, middle) := by
              simpa [before, List.append_assoc] using hRunSwap
            rw [hRunSwap']
            simp only [Bind.bind, Except.bind]
            simpa [before, afterSwap,
              EvmYul.EVM.State.replaceStackAndIncrPC] using hRunTail
          · simpa [List.append_assoc] using hStack
          · apply SameRuntimeData.trans hSame
            simp [before, afterSwap, SameRuntimeData, eraseRuntimeControl,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, List.append_assoc]

/--
Execute the complete generated call-entry body: push a return token, then move
it below the visible argument prefix.
-/
theorem runBody_callEntry
    {input output : TypedCfg.Shape} {state : EVMState}
    (args suffix : EvmYul.Stack Word) (token : Word)
    (hType :
      TypedCfg.Block.bodyType?
          (.returnToken token ::
            TypedCfgCompiler.sinkTopUnder args.length) input =
        some output)
    (hBound : args.length ≤ 16) :
    ∃ final,
      TypedCfg.Block.runBody
          (.returnToken token ::
            TypedCfgCompiler.sinkTopUnder args.length) input
          { state with stack := args ++ suffix } =
        .ok (final, output) ∧
      final.stack = args ++ [token] ++ suffix ∧
      SameRuntimeData final
        { state with stack := args ++ [token] ++ suffix } := by
  cases hHeadType :
      TypedCfg.Instr.type? (.returnToken token) input with
  | none =>
      simp [TypedCfg.Block.bodyType?, hHeadType] at hType
  | some middle =>
      simp [TypedCfg.Block.bodyType?, hHeadType] at hType
      let before : EVMState :=
        { state with stack := args ++ suffix }
      let afterPush : EVMState :=
        before.replaceStackAndIncrPC
          (token :: args ++ suffix) (pcΔ := 33)
      have hRunState :
          TypedCfg.Instr.runState (.returnToken token) input before =
            .ok afterPush := by
        simp [TypedCfg.Instr.runState, EvmYul.Stack.push,
          before, afterPush]
      have hRunToken :
          TypedCfg.Instr.runAt (.returnToken token) input before =
            .ok (afterPush, middle) := by
        unfold TypedCfg.Instr.runAt
        rw [hHeadType, hRunState]
        rfl
      rcases
          runBody_sinkTopUnder (input := middle) (output := output)
            (state := afterPush) args suffix token hType hBound with
        ⟨final, hRunTail, hStack, hSame⟩
      refine ⟨final, ?_, hStack, ?_⟩
      · unfold TypedCfg.Block.runBody
        have hRunToken' :
            TypedCfg.Instr.runAt (.returnToken token) input
                { state with stack := args ++ suffix } =
              .ok (afterPush, middle) := by
          simpa [before] using hRunToken
        rw [hRunToken']
        simp only [Bind.bind, Except.bind]
        simpa [afterPush,
          EvmYul.EVM.State.replaceStackAndIncrPC] using hRunTail
      · apply SameRuntimeData.trans hSame
        simp [before, afterPush, SameRuntimeData, eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

/--
Call-entry execution realizes the new source ghost frame with the generated
return token while retaining the older concrete frame suffix.
-/
theorem runBody_callEntry_preserves
    {source : RunState} {tokens : List Word} {target : EVMState}
    {argc retc : Nat} {args callerStack : EvmYul.Stack Word}
    {token : Word} {input output : TypedCfg.Shape}
    (hRel : StateRel source tokens target)
    (hSplit :
      Structured.StackFrame.splitArgs? argc source.evm.stack =
        some (args, callerStack))
    (hType :
      TypedCfg.Block.bodyType?
          (.returnToken token ::
            TypedCfgCompiler.sinkTopUnder argc) input =
        some output)
    (hBound : argc ≤ 16) :
    ∃ targetFinal,
      TypedCfg.Block.runBody
          (.returnToken token ::
            TypedCfgCompiler.sinkTopUnder argc) input target =
        .ok (targetFinal, output) ∧
      StateRel
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack retc)
        (token :: tokens) targetFinal := by
  rcases splitArgs?_eq_some hSplit with
    ⟨hArgsLength, hSourceStack⟩
  rcases hRel with ⟨realized, hRealize, hSame⟩
  rw [hSourceStack] at hRealize
  rw [realizeStack_append_prefix] at hRealize
  cases hCallerRealize :
      realizeStack callerStack source.returns tokens with
  | none =>
      simp [hCallerRealize] at hRealize
  | some hidden =>
      simp [hCallerRealize] at hRealize
      subst realized
      have hTargetStack : target.stack = args ++ hidden := by
        simpa using SameRuntimeData.stack_eq hSame
      have hTargetRecord :
          { target with stack := args ++ hidden } = target := by
        cases target
        simp at hTargetStack ⊢
        exact hTargetStack.symm
      have hCallType :
          TypedCfg.Block.bodyType?
              (.returnToken token ::
                TypedCfgCompiler.sinkTopUnder args.length) input =
            some output := by
        simpa [hArgsLength] using hType
      rcases
          runBody_callEntry (input := input) (output := output)
            (state := target) args hidden token hCallType
            (by simpa [hArgsLength] using hBound) with
        ⟨targetFinal, hRun, hFinalStack, hFinalSame⟩
      have hRun' :
          TypedCfg.Block.runBody
              (.returnToken token ::
                TypedCfgCompiler.sinkTopUnder argc) input target =
            .ok (targetFinal, output) := by
        simpa [hArgsLength, hTargetRecord] using hRun
      refine ⟨targetFinal, hRun', ?_⟩
      have hPushedRealize :
          realizeStack
              (args ++ [token] ++ callerStack)
              source.returns tokens =
            some (args ++ [token] ++ hidden) := by
        rw [realizeStack_append_prefix]
        simp [hCallerRealize, List.append_assoc]
      have hUpdatedSame :
          SameRuntimeData
            { target with stack := args ++ [token] ++ hidden }
            { source.evm with stack := args ++ [token] ++ hidden } := by
        simpa using
          SameRuntimeData.replaceStack hSame
            (targetStack := args ++ [token] ++ hidden)
            (sourceStack := args ++ [token] ++ hidden) rfl
      exact
        StateRel.pushReturn hPushedRealize
          (SameRuntimeData.trans hFinalSame hUpdatedSame)

/--
Erasing the selected concrete return token realizes the source operation that
pops the ghost return frame and reattaches the caller stack.
-/
theorem eraseReturnToken_preserves
    {bodyState returned : RunState} {frame : ReturnDest}
    {stack : EvmYul.Stack Word} {token : Word}
    {tokens : List Word} {target : EVMState}
    (hRel : StateRel bodyState (token :: tokens) target)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack) :
    target.stack[frame.retc]? = some token ∧
      StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        tokens
        { target with stack := target.stack.eraseIdx frame.retc } := by
  cases hReturns : bodyState.returns with
  | nil =>
      simp [RunState.popReturn?, hReturns] at hPop
  | cons head rest =>
      simp [RunState.popReturn?, hReturns] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      by_cases hLength :
          bodyState.evm.stack.length = head.retc
      · simp [Structured.StackFrame.attachReturns?, hLength] at hAttach
        subst stack
        rcases hRel with ⟨realized, hRealize, hSame⟩
        rw [hReturns] at hRealize
        simp only [realizeStack] at hRealize
        rw [realizeStack_append_prefix] at hRealize
        cases hCallerRealize :
            realizeStack head.callerStack rest tokens with
        | none =>
            simp [hCallerRealize] at hRealize
        | some hidden =>
            simp [hCallerRealize] at hRealize
            subst realized
            have hTargetStack :
                target.stack =
                  bodyState.evm.stack ++ [token] ++ hidden := by
              simpa using SameRuntimeData.stack_eq hSame
            constructor
            · rw [hTargetStack, ← hLength]
              simp
            · refine ⟨bodyState.evm.stack ++ hidden, ?_, ?_⟩
              · change
                  realizeStack
                      (bodyState.evm.stack ++ head.callerStack)
                      rest tokens =
                    some (bodyState.evm.stack ++ hidden)
                rw [realizeStack_append_prefix]
                simp [hCallerRealize]
              · have hErase :
                    target.stack.eraseIdx head.retc =
                      bodyState.evm.stack ++ hidden := by
                  rw [hTargetStack, ← hLength]
                  simpa [List.append_assoc] using
                    (TypedCfg.Preservation.List.eraseIdx_append_at_length
                      bodyState.evm.stack hidden token)
                have hAfter :=
                  SameRuntimeData.replaceStack hSame
                    (targetStack := target.stack.eraseIdx head.retc)
                    (sourceStack := bodyState.evm.stack ++ hidden)
                    hErase
                simpa [RunState.withEVM, hReturns] using hAfter
      · simp [Structured.StackFrame.attachReturns?, hLength] at hAttach

/--
A regularly returning procedure pops exactly the frame introduced at its call
boundary.
-/
theorem poppedFrame_eq_of_regular_eval
    {program : Structured.Program} {fuel retc : Nat}
    {body : Structured.Block} {source bodyState returned : RunState}
    {args callerStack : EvmYul.Stack Word} {frame : ReturnDest}
    (hBody :
      Structured.Block.Eval program fuel body
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack retc)
        (Structured.Outcome.regular bodyState))
    (hPop : bodyState.popReturn? = some (frame, returned)) :
    frame = { callerStack := callerStack, retc := retc } := by
  have hReturns :=
    Structured.Block.Eval.returns_eq_of_nonhalting hBody (by
      simp [Structured.Outcome.Nonhalting])
  simp only [Structured.Outcome.regular_state,
    RunState.pushReturn_returns, RunState.withEVM_returns] at hReturns
  unfold RunState.popReturn? at hPop
  rw [hReturns] at hPop
  simp at hPop
  exact hPop.1.symm

/--
A procedure-delimited `leave` pops the same call frame as ordinary
fallthrough.
-/
theorem poppedFrame_eq_of_leave_eval
    {program : Structured.Program} {fuel retc : Nat}
    {body : Structured.Block} {source bodyState returned : RunState}
    {args callerStack : EvmYul.Stack Word} {frame : ReturnDest}
    (hBody :
      Structured.Block.Eval program fuel body
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack retc)
        (Structured.Outcome.leave bodyState))
    (hPop : bodyState.popReturn? = some (frame, returned)) :
    frame = { callerStack := callerStack, retc := retc } := by
  have hReturns :=
    Structured.Block.Eval.returns_eq_of_nonhalting hBody (by
      simp [Structured.Outcome.Nonhalting])
  simp only [Structured.Outcome.leave_state,
    RunState.pushReturn_returns, RunState.withEVM_returns] at hReturns
  unfold RunState.popReturn? at hPop
  rw [hReturns] at hPop
  simp at hPop
  exact hPop.1.symm

end CallStack

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
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
        cases hSafe :
            TypedCfgCompiler.BasicInstr.sourceSafe? instr input middle with
        | false =>
            simp [hHeadType, hSafe] at hType
        | true =>
            have hTailType :
                TypedCfgCompiler.Code.type? rest middle = some output := by
              simpa [hHeadType, hSafe] using hType
            simp only [TypedCfgCompiler.Code.toCfg, List.map_cons]
            unfold TypedCfg.Block.runBody
            rw [BasicInstr.runAt_toCfg hHeadType]
            unfold Structured.Code.run
            rw [EffectSemantics.Code.run_cons]
            cases hStep : instr.step state with
            | error err =>
                simp only [hStep, Except.map, Bind.bind, Except.bind,
                  EffectSemantics.Ordinary.evmStateModel_evm,
                  EffectSemantics.Ordinary.evmStateModel_withEVM,
                  EffectSemantics.Ordinary.handler_afterInstr]
            | ok state' =>
                simp only [hStep, Except.map, Bind.bind, Except.bind,
                  EffectSemantics.Ordinary.evmStateModel_evm,
                  EffectSemantics.Ordinary.evmStateModel_withEVM,
                  EffectSemantics.Ordinary.handler_afterInstr]
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
  change
    (EffectSemantics.Code.runCondition
        EffectSemantics.Ordinary.evmStateModel
        EffectSemantics.Ordinary.handler code state.evm).bind
        (fun result => .ok (state.withEVM result.1, result.2)) =
      .ok (final, cond) at hCond
  rw [EffectSemantics.Code.runCondition_eq_run_bind,
    EffectSemantics.Code.ordinary_evm_run] at hCond
  cases hCode : Structured.Code.run code state.evm with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hCond
  | ok afterCode =>
      cases hPop : afterCode.stack.pop with
      | none =>
          simp [hCode, Structured.Code.popCondition,
            EffectSemantics.Code.popCondition,
            EffectSemantics.Control.Code.popCondition, hPop,
            Bind.bind, Except.bind] at hCond
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [hCode, Structured.Code.popCondition,
            EffectSemantics.Code.popCondition,
            EffectSemantics.Control.Code.popCondition, hPop,
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

def CallsInProgram (result : TypedCfgCompiler.Result)
    (calls : List TypedCfgCompiler.DispatchSite) : Prop :=
  ∀ site, site ∈ result.calls → site ∈ calls

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

namespace CallsInProgram

theorem left_of_append
    {left right : TypedCfgCompiler.Result}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hCalls : CallsInProgram (left.append right) calls) :
    CallsInProgram left calls := by
  intro site hMem
  apply hCalls site
  simp [TypedCfgCompiler.Result.append, hMem]

theorem right_of_append
    {left right : TypedCfgCompiler.Result}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hCalls : CallsInProgram (left.append right) calls) :
    CallsInProgram right calls := by
  intro site hMem
  apply hCalls site
  simp [TypedCfgCompiler.Result.append, hMem]

end CallsInProgram

namespace Block

/--
Canonical decomposition of a successful nonempty statement-list compilation.

This is a compiler fact shared by ordinary and effectful preservation proofs.
-/
theorem components_of_compileStmtListFuel?_cons
    {compilerFuel : Nat} {stmt : Structured.Stmt}
    {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
        (stmt :: rest) ctx supply entry input regular = some result) :
    ∃ headResult,
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
          entry input (TypedCfgCompiler.restLabel supply) =
        some headResult ∧
      ((headResult.fallthrough? = none ∧ result = headResult) ∨
        ∃ tailInput tailResult,
          headResult.fallthrough? = some tailInput ∧
          TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
              headResult.next (TypedCfgCompiler.restLabel supply)
              tailInput regular =
            some tailResult ∧
          result = headResult.append tailResult) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  cases hHead :
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
        entry input (TypedCfgCompiler.restLabel supply) with
  | none =>
      simp [hHead] at hCompile
  | some headResult =>
      cases hFallthrough : headResult.fallthrough? with
      | none =>
          have hEq : headResult = result := by
            simpa [hHead, hFallthrough] using hCompile
          exact
            ⟨headResult, rfl,
              Or.inl ⟨hFallthrough, hEq.symm⟩⟩
      | some tailInput =>
          cases hTail :
              TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
                headResult.next (TypedCfgCompiler.restLabel supply)
                tailInput regular with
          | none =>
              simp [hHead, hFallthrough, hTail] at hCompile
          | some tailResult =>
              have hEq : headResult.append tailResult = result := by
                simpa [hHead, hFallthrough, hTail] using hCompile
              exact
                ⟨headResult, rfl,
                  Or.inr
                    ⟨tailInput, tailResult, hFallthrough, hTail,
                      hEq.symm⟩⟩

end Block

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

namespace OutcomeSimulation

/--
Control mode extracted from a concrete TypedCfg outcome.

The pass-specific relation below maps Structured's lexical control modes to
these CFG modes through the continuation labels supplied to the compiler.
-/
inductive TargetMode where
  | fallthrough
  | jump (target : Assembly.Label)
  | returnDispatch
  | halt (kind : Assembly.HaltKind)
  | invalid
  deriving DecidableEq

def sourceView :
    Simulation.OutcomeView Structured.Outcome RunState Structured.Mode where
  state := Structured.Outcome.state
  mode := Structured.Outcome.mode

def targetState : TypedCfg.Outcome → EVMState
  | .fallthrough state
  | .jump _ state
  | .returnDispatch state
  | .halt _ state
  | .invalid state => state

def targetMode : TypedCfg.Outcome → TargetMode
  | .fallthrough _ => .fallthrough
  | .jump target _ => .jump target
  | .returnDispatch _ => .returnDispatch
  | .halt kind _ => .halt kind
  | .invalid _ => .invalid

def targetView :
    Simulation.OutcomeView TypedCfg.Outcome EVMState TargetMode where
  state := targetState
  mode := targetMode

/--
Lexical control destinations owned by a compiled Structured fragment.
-/
structure Continuations where
  regular : Assembly.Label
  breakLabel? : Option Assembly.Label := none
  continueLabel? : Option Assembly.Label := none
  leaveLabel? : Option Assembly.Label := none

def Continuations.ofContext
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label) :
    Continuations where
  regular := regular
  breakLabel? := ctx.breakLabel?
  continueLabel? := ctx.continueLabel?
  leaveLabel? := ctx.leaveLabel?

/--
Halted execution may retain any number of active procedure frames because no
return dispatch occurs after the halt.
-/
def HaltStateRel (source : RunState) (target : EVMState) : Prop :=
  ∃ tokens, StateRel source tokens target

/--
Source control permissions realized by concrete compiler continuations.

`Structured.Stmt.WF` records lexical permissions as Booleans. This adapter
connects those source-facing permissions to the labels installed in the
TypedCfg compiler context without making source semantics depend on lowering.
-/
structure ContextSupports (ctx : TypedCfgCompiler.Context)
    (canBreak canContinue canLeave : Bool) : Prop where
  breakLabel :
    canBreak = true →
      ∃ label, ctx.breakLabel? = some label
  continueLabel :
    canContinue = true →
      ∃ label, ctx.continueLabel? = some label
  leaveLabel :
    canLeave = true →
      ∃ label, ctx.leaveLabel? = some label

namespace ContextSupports

theorem withoutLoop
    {ctx : TypedCfgCompiler.Context}
    {canBreak canContinue canLeave : Bool}
    (hSupports :
      ContextSupports ctx canBreak canContinue canLeave) :
    ContextSupports
      { ctx with
        breakLabel? := none
        breakShape? := none
        continueLabel? := none
        continueShape? := none }
      false false canLeave := by
  exact
    { breakLabel := by simp
      continueLabel := by simp
      leaveLabel := hSupports.leaveLabel }

theorem loopBody
    {ctx : TypedCfgCompiler.Context}
    {canBreak canContinue canLeave : Bool}
    (hSupports :
      ContextSupports ctx canBreak canContinue canLeave)
    (breakLabel continueLabel : Assembly.Label)
    (shape : TypedCfg.Shape) :
    ContextSupports
      { ctx with
        breakLabel? := some breakLabel
        breakShape? := some shape
        continueLabel? := some continueLabel
        continueShape? := some shape }
      true true canLeave := by
  exact
    { breakLabel := by
        intro _hEnabled
        exact ⟨breakLabel, rfl⟩
      continueLabel := by
        intro _hEnabled
        exact ⟨continueLabel, rfl⟩
      leaveLabel := hSupports.leaveLabel }

end ContextSupports

/--
Mode-indexed Structured-to-TypedCfg outcome policy.

Regular and lexical control outcomes select their compiler-owned continuation.
TypedCfg halt outcomes retain the state immediately before the terminal opcode,
so the halt branch executes that opcode before applying `StateRel`.
-/
def contract (continuations : Continuations) (tokens : List Word) :
    Simulation.OutcomeContract Structured.Mode TargetMode RunState EVMState where
  relate sourceMode targetMode source target :=
    match sourceMode, targetMode with
    | .regular, .jump label =>
        label = continuations.regular ∧ StateRel source tokens target
    | .brk, .jump label =>
        continuations.breakLabel? = some label ∧ StateRel source tokens target
    | .cont, .jump label =>
        continuations.continueLabel? = some label ∧
          StateRel source tokens target
    | .leave, .jump label =>
        continuations.leaveLabel? = some label ∧ StateRel source tokens target
    | .halt kind, .halt targetKind =>
        targetKind = kind ∧
          ∃ targetFinal,
            Structured.Terminal.step kind target = .ok targetFinal ∧
              HaltStateRel source targetFinal
    | _, _ => False

abbrev Rel (continuations : Continuations) (tokens : List Word) :=
  Simulation.OutcomeRel sourceView targetView
    (contract continuations tokens)

namespace Rel

theorem regular_iff
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {label : Assembly.Label} {target : EVMState} :
    Rel continuations tokens (Structured.Outcome.regular source)
        (.jump label target) ↔
      label = continuations.regular ∧ StateRel source tokens target :=
  Iff.rfl

theorem brk_iff
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {label : Assembly.Label} {target : EVMState} :
    Rel continuations tokens (Structured.Outcome.brk source)
        (.jump label target) ↔
      continuations.breakLabel? = some label ∧
        StateRel source tokens target :=
  Iff.rfl

theorem cont_iff
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {label : Assembly.Label} {target : EVMState} :
    Rel continuations tokens (Structured.Outcome.cont source)
        (.jump label target) ↔
      continuations.continueLabel? = some label ∧
        StateRel source tokens target :=
  Iff.rfl

theorem leave_iff
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {label : Assembly.Label} {target : EVMState} :
    Rel continuations tokens (Structured.Outcome.leave source)
        (.jump label target) ↔
      continuations.leaveLabel? = some label ∧
        StateRel source tokens target :=
  Iff.rfl

theorem halt_iff
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {kind targetKind : Assembly.HaltKind}
    {target : EVMState} :
    Rel continuations tokens (Structured.Outcome.halt kind source)
        (.halt targetKind target) ↔
      targetKind = kind ∧
        ∃ targetFinal,
          Structured.Terminal.step kind target = .ok targetFinal ∧
            HaltStateRel source targetFinal :=
  Iff.rfl

theorem regular_elim
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {targetOutcome : TypedCfg.Outcome}
    (hRel :
      Rel continuations tokens
        (Structured.Outcome.regular source) targetOutcome) :
    ∃ target,
      targetOutcome = .jump continuations.regular target ∧
        StateRel source tokens target := by
  cases targetOutcome with
  | jump label target =>
      rcases regular_iff.mp hRel with ⟨rfl, hState⟩
      exact ⟨target, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem brk_elim
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {targetOutcome : TypedCfg.Outcome}
    (hRel :
      Rel continuations tokens
        (Structured.Outcome.brk source) targetOutcome) :
    ∃ label target,
      continuations.breakLabel? = some label ∧
        targetOutcome = .jump label target ∧
          StateRel source tokens target := by
  cases targetOutcome with
  | jump label target =>
      rcases brk_iff.mp hRel with ⟨hLabel, hState⟩
      exact ⟨label, target, hLabel, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem cont_elim
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {targetOutcome : TypedCfg.Outcome}
    (hRel :
      Rel continuations tokens
        (Structured.Outcome.cont source) targetOutcome) :
    ∃ label target,
      continuations.continueLabel? = some label ∧
        targetOutcome = .jump label target ∧
          StateRel source tokens target := by
  cases targetOutcome with
  | jump label target =>
      rcases cont_iff.mp hRel with ⟨hLabel, hState⟩
      exact ⟨label, target, hLabel, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem leave_elim
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {targetOutcome : TypedCfg.Outcome}
    (hRel :
      Rel continuations tokens
        (Structured.Outcome.leave source) targetOutcome) :
    ∃ label target,
      continuations.leaveLabel? = some label ∧
        targetOutcome = .jump label target ∧
          StateRel source tokens target := by
  cases targetOutcome with
  | jump label target =>
      rcases leave_iff.mp hRel with ⟨hLabel, hState⟩
      exact ⟨label, target, hLabel, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem halt_elim
    {continuations : Continuations} {tokens : List Word}
    {source : RunState} {kind : Assembly.HaltKind}
    {targetOutcome : TypedCfg.Outcome}
    (hRel :
      Rel continuations tokens
        (Structured.Outcome.halt kind source) targetOutcome) :
    ∃ target targetFinal,
      targetOutcome = .halt kind target ∧
        Structured.Terminal.step kind target = .ok targetFinal ∧
          HaltStateRel source targetFinal := by
  cases targetOutcome with
  | halt targetKind target =>
      rcases halt_iff.mp hRel with
        ⟨rfl, targetFinal, hStep, hState⟩
      exact ⟨target, targetFinal, rfl, hStep, hState⟩
  | fallthrough _ | jump _ _ | returnDispatch _ | invalid _ =>
      exact False.elim hRel

end Rel

/--
Relational execution of a Structured outcome through an ambient TypedCfg.

This is the common composition unit for statement lists, loops, switches, and
procedure calls. Compiler-result ownership and fallthrough metadata remain
separate from semantic path composition.
-/
def Path (program : TypedCfg.Program) (entry : Assembly.Label)
    (continuations : Continuations) (source : RunState)
    (outcome : Structured.Outcome) (tokens : List Word) : Prop :=
  ∀ target,
    StateRel source tokens target →
      ∃ targetOutcome,
        program.Eventually entry target targetOutcome ∧
          Rel continuations tokens outcome targetOutcome

namespace Path

theorem to_regular
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hPath :
      Path program entry continuations source
        (Structured.Outcome.regular final) tokens) :
    PathPreserves program entry continuations.regular source final tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.regular_elim hOutcomeRel with
    ⟨targetFinal, rfl, hFinalRel⟩
  exact ⟨targetFinal, hEventually, hFinalRel⟩

theorem to_brk
    {program : TypedCfg.Program} {entry targetLabel : Assembly.Label}
    {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hTarget : continuations.breakLabel? = some targetLabel)
    (hPath :
      Path program entry continuations source
        (Structured.Outcome.brk final) tokens) :
    PathPreserves program entry targetLabel source final tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.brk_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  rw [hTarget] at hLabel
  cases hLabel
  exact ⟨targetFinal, hEventually, hFinalRel⟩

theorem to_cont
    {program : TypedCfg.Program} {entry targetLabel : Assembly.Label}
    {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hTarget : continuations.continueLabel? = some targetLabel)
    (hPath :
      Path program entry continuations source
        (Structured.Outcome.cont final) tokens) :
    PathPreserves program entry targetLabel source final tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.cont_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  rw [hTarget] at hLabel
  cases hLabel
  exact ⟨targetFinal, hEventually, hFinalRel⟩

theorem to_leave
    {program : TypedCfg.Program} {entry targetLabel : Assembly.Label}
    {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hTarget : continuations.leaveLabel? = some targetLabel)
    (hPath :
      Path program entry continuations source
        (Structured.Outcome.leave final) tokens) :
    PathPreserves program entry targetLabel source final tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.leave_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  rw [hTarget] at hLabel
  cases hLabel
  exact ⟨targetFinal, hEventually, hFinalRel⟩

theorem transport_leave
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {left right : Continuations}
    {source final : RunState} {tokens : List Word}
    (hLeave : left.leaveLabel? = right.leaveLabel?)
    (hPath :
      Path program entry left source
        (Structured.Outcome.leave final) tokens) :
    Path program entry right source
      (Structured.Outcome.leave final) tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.leave_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  refine ⟨.jump label targetFinal, hEventually, ?_⟩
  exact Rel.leave_iff.mpr ⟨hLeave ▸ hLabel, hFinalRel⟩

theorem transport_brk
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {left right : Continuations}
    {source final : RunState} {tokens : List Word}
    (hBreak : left.breakLabel? = right.breakLabel?)
    (hPath :
      Path program entry left source
        (Structured.Outcome.brk final) tokens) :
    Path program entry right source
      (Structured.Outcome.brk final) tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.brk_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  refine ⟨.jump label targetFinal, hEventually, ?_⟩
  exact Rel.brk_iff.mpr ⟨hBreak ▸ hLabel, hFinalRel⟩

theorem transport_cont
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {left right : Continuations}
    {source final : RunState} {tokens : List Word}
    (hContinue : left.continueLabel? = right.continueLabel?)
    (hPath :
      Path program entry left source
        (Structured.Outcome.cont final) tokens) :
    Path program entry right source
      (Structured.Outcome.cont final) tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.cont_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  refine ⟨.jump label targetFinal, hEventually, ?_⟩
  exact Rel.cont_iff.mpr ⟨hContinue ▸ hLabel, hFinalRel⟩

theorem transport_halt
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {left right : Continuations}
    {source final : RunState} {tokens : List Word}
    {kind : Assembly.HaltKind}
    (hPath :
      Path program entry left source
        (Structured.Outcome.halt kind final) tokens) :
    Path program entry right source
      (Structured.Outcome.halt kind final) tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetOutcome, hEventually, hOutcomeRel⟩
  rcases Rel.halt_elim hOutcomeRel with
    ⟨targetBefore, targetFinal, rfl, hStep, hFinalRel⟩
  refine ⟨.halt kind targetBefore, hEventually, ?_⟩
  exact Rel.halt_iff.mpr ⟨rfl, targetFinal, hStep, hFinalRel⟩

theorem regular_of_path
    {program : TypedCfg.Program} {entry regular : Assembly.Label}
    {source final : RunState} {tokens : List Word}
    {continuations : Continuations}
    (hRegular : continuations.regular = regular)
    (hPath : PathPreserves program entry regular source final tokens) :
    Path program entry continuations source
      (Structured.Outcome.regular final) tokens := by
  intro target hRel
  rcases hPath target hRel with
    ⟨targetFinal, hEventually, hFinalRel⟩
  refine ⟨.jump regular targetFinal, hEventually, ?_⟩
  exact ⟨hRegular.symm, hFinalRel⟩

theorem regular_of_regular
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {source final : RunState} {tokens : List Word}
    {continuations : Continuations}
    (hRegular : continuations.regular = regular)
    (hPreserves :
      RegularPreserves result program entry regular source final tokens) :
    Path program entry continuations source
      (Structured.Outcome.regular final) tokens :=
  regular_of_path hRegular (PathPreserves.of_regular hPreserves)

theorem bind_jump
    {program : TypedCfg.Program} {entry next : Assembly.Label}
    {source middle : RunState} {outcome : Structured.Outcome}
    {tokens : List Word} {continuations : Continuations}
    (hFirst : PathPreserves program entry next source middle tokens)
    (hNext : Path program next continuations middle outcome tokens) :
    Path program entry continuations source outcome tokens := by
  intro target hRel
  rcases hFirst target hRel with
    ⟨targetMiddle, hFirstEventually, hMiddleRel⟩
  rcases hNext targetMiddle hMiddleRel with
    ⟨targetOutcome, hNextEventually, hOutcomeRel⟩
  exact
    ⟨targetOutcome,
      TypedCfg.Program.Eventually.bind_jump
        hFirstEventually hNextEventually,
      hOutcomeRel⟩

end Path

/--
Compiler-fragment preservation with outcome-indexed fallthrough metadata.

Every outcome carries the shared semantic path. Only regular source outcomes
require the compiler result to expose a fallthrough shape; abrupt outcomes
terminate before a statement-list tail and impose no such metadata.
-/
def Preserves (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry : Assembly.Label)
    (continuations : Continuations) (source : RunState)
    (outcome : Structured.Outcome) (tokens : List Word) : Prop :=
  Path program entry continuations source outcome tokens ∧
    (outcome.mode = .regular →
      ∃ output, result.fallthrough? = some output)

namespace Preserves

theorem path
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry : Assembly.Label} {continuations : Continuations}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    (hPreserves :
      Preserves result program entry continuations source outcome tokens) :
    Path program entry continuations source outcome tokens :=
  hPreserves.1

theorem fallthrough_of_regular
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry : Assembly.Label} {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hPreserves :
      Preserves result program entry continuations source
        (Structured.Outcome.regular final) tokens) :
    ∃ output, result.fallthrough? = some output :=
  hPreserves.2 rfl

theorem of_regular
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label} {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hRegular : continuations.regular = regular)
    (hFallthrough : ∃ output, result.fallthrough? = some output)
    (hPreserves :
      RegularPreserves result program entry regular source final tokens) :
    Preserves result program entry continuations source
      (Structured.Outcome.regular final) tokens := by
  refine
    ⟨Path.regular_of_regular hRegular hPreserves, ?_⟩
  intro _hMode
  exact hFallthrough

theorem of_path_of_nonregular
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry : Assembly.Label} {continuations : Continuations}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    (hMode : outcome.mode ≠ .regular)
    (hPath : Path program entry continuations source outcome tokens) :
    Preserves result program entry continuations source outcome tokens := by
  refine ⟨hPath, ?_⟩
  intro hRegular
  exact False.elim (hMode hRegular)

theorem to_regular_path
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry : Assembly.Label} {continuations : Continuations}
    {source final : RunState} {tokens : List Word}
    (hPreserves :
      Preserves result program entry continuations source
        (Structured.Outcome.regular final) tokens) :
    PathPreserves program entry continuations.regular source final tokens :=
  Path.to_regular hPreserves.1

end Preserves

namespace Loop

def bodyContinuations (endLabel postLabel : Assembly.Label)
    (outer : Continuations) : Continuations where
  regular := postLabel
  breakLabel? := some endLabel
  continueLabel? := some postLabel
  leaveLabel? := outer.leaveLabel?

def postContinuations (loopLabel : Assembly.Label)
    (outer : Continuations) : Continuations where
  regular := loopLabel
  leaveLabel? := outer.leaveLabel?

end Loop

end OutcomeSimulation

namespace Program

/--
Compiler-generated procedure fragment, independent of where the procedure
appears in the source list.

The route is either a direct body entry or the checked relabel adapter used by
allocation-derived procedure shapes.
-/
structure ProcFragment
    (entryShapes : TypedCfgCompiler.ProcEntryShapes)
    (allProcs : List Structured.Proc) (proc : Structured.Proc)
    (procBlocks : List TypedCfg.Block)
    (procCalls : List TypedCfgCompiler.DispatchSite) where
  supply : LabelSupply
  input : TypedCfg.Shape
  entry : Assembly.Label
  result : TypedCfgCompiler.Result
  compile :
    TypedCfgCompiler.compileBlock? proc.body
        { procs := allProcs
          leaveLabel? := some (ProcLabel.exit proc.name)
          leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
        supply entry input (ProcLabel.exit proc.name) =
      some result
  fallthrough :
    result.requireFallthrough? (TypedCfgCompiler.Shape.procExit proc) =
      some ()
  blocks :
    ∀ block, block ∈ result.blocks → block ∈ procBlocks
  calls :
    ∀ site, site ∈ result.calls → site ∈ procCalls
  route :
    (entry = ProcLabel.entry proc.name ∧
      input = TypedCfgCompiler.Shape.procEntry proc) ∨
    (∃ adapter,
      entry = ProcLabel.body proc.name ∧
      entryShapes.find? proc.name = some input ∧
      TypedCfgCompiler.Shape.requireReturnTokenDepth?
          proc.argc input = some () ∧
      TypedCfgCompiler.mkBlock?
          (ProcLabel.entry proc.name)
          (TypedCfgCompiler.Shape.procEntry proc)
          [.relabel input] (.jump (ProcLabel.body proc.name)) =
        some adapter ∧
      adapter ∈ procBlocks)

/--
Successful recursive procedure lowering yields a fragment certificate for the
procedure selected by source lookup.
-/
def procFragment_of_lowerProcBodiesWithShapes?
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs procs : List Structured.Proc}
    {supply next : LabelSupply}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    {name : Structured.Name} {proc : Structured.Proc}
    (hLower :
      TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes allProcs
          procs supply =
        some (procBlocks, next, procCalls))
    (hLookup : Structured.ProcList.lookup? name procs = some proc) :
    ProcFragment entryShapes allProcs proc procBlocks procCalls := by
  induction procs generalizing supply next procBlocks procCalls with
  | nil =>
      simp [Structured.ProcList.lookup?] at hLookup
  | cons head rest ih =>
      unfold Structured.ProcList.lookup? at hLookup
      by_cases hName : head.name = name
      · simp [hName] at hLookup
        subst proc
        unfold TypedCfgCompiler.lowerProcBodiesWithShapes? at hLower
        cases hShape : entryShapes.find? head.name with
        | none =>
            cases hBody :
                TypedCfgCompiler.compileBlock? head.body
                  { procs := allProcs
                    leaveLabel? := some (ProcLabel.exit head.name)
                    leaveShape? :=
                      some (TypedCfgCompiler.Shape.procExit head) }
                  supply (ProcLabel.entry head.name)
                  (TypedCfgCompiler.Shape.procEntry head)
                  (ProcLabel.exit head.name) with
            | none =>
                simp [hShape, hBody] at hLower
            | some bodyResult =>
                cases hRequire :
                    bodyResult.requireFallthrough?
                      (TypedCfgCompiler.Shape.procExit head) with
                | none =>
                    simp [hShape, hBody, hRequire] at hLower
                | some unit =>
                    cases unit
                    cases hTail :
                        TypedCfgCompiler.lowerProcBodiesWithShapes?
                          entryShapes allProcs rest bodyResult.next with
                    | none =>
                        simp [hShape, hBody, hRequire, hTail] at hLower
                    | some tailResult =>
                        rcases tailResult with
                          ⟨tailBlocks, tailNext, tailCalls⟩
                        simp [hShape, hBody, hRequire, hTail] at hLower
                        rcases hLower with ⟨rfl, rfl, rfl⟩
                        exact
                          { supply := supply
                            input := TypedCfgCompiler.Shape.procEntry head
                            entry := ProcLabel.entry head.name
                            result := bodyResult
                            compile := hBody
                            fallthrough := hRequire
                            blocks := by
                              intro block hMem
                              exact List.mem_append.mpr (Or.inl hMem)
                            calls := by
                              intro site hMem
                              exact List.mem_append.mpr (Or.inl hMem)
                            route := Or.inl ⟨rfl, rfl⟩ }
        | some bodyInput =>
            cases hFrame :
                TypedCfgCompiler.Shape.requireReturnTokenDepth?
                  head.argc bodyInput with
            | none =>
                simp [hShape, hFrame] at hLower
            | some unit =>
                cases unit
                cases hAdapter :
                    TypedCfgCompiler.mkBlock?
                      (ProcLabel.entry head.name)
                      (TypedCfgCompiler.Shape.procEntry head)
                      [.relabel bodyInput]
                      (.jump (ProcLabel.body head.name)) with
                | none =>
                    simp [hShape, hFrame, hAdapter] at hLower
                | some adapter =>
                    cases hBody :
                        TypedCfgCompiler.compileBlock? head.body
                          { procs := allProcs
                            leaveLabel? := some (ProcLabel.exit head.name)
                            leaveShape? :=
                              some (TypedCfgCompiler.Shape.procExit head) }
                          supply (ProcLabel.body head.name) bodyInput
                          (ProcLabel.exit head.name) with
                    | none =>
                        simp [hShape, hFrame, hAdapter, hBody] at hLower
                    | some bodyResult =>
                        cases hRequire :
                            bodyResult.requireFallthrough?
                              (TypedCfgCompiler.Shape.procExit head) with
                        | none =>
                            simp [hShape, hFrame, hAdapter, hBody, hRequire] at hLower
                        | some unit =>
                            cases unit
                            cases hTail :
                                TypedCfgCompiler.lowerProcBodiesWithShapes?
                                  entryShapes allProcs rest bodyResult.next with
                            | none =>
                                simp [hShape, hFrame, hAdapter, hBody,
                                  hRequire, hTail] at hLower
                            | some tailResult =>
                                rcases tailResult with
                                  ⟨tailBlocks, tailNext, tailCalls⟩
                                simp [hShape, hFrame, hAdapter, hBody,
                                  hRequire, hTail] at hLower
                                rcases hLower with ⟨rfl, rfl, rfl⟩
                                exact
                                  { supply := supply
                                    input := bodyInput
                                    entry := ProcLabel.body head.name
                                    result := bodyResult
                                    compile := hBody
                                    fallthrough := hRequire
                                    blocks := by
                                      intro block hMem
                                      exact
                                        List.mem_append.mpr
                                          (Or.inl
                                            (List.mem_cons_of_mem adapter hMem))
                                    calls := by
                                      intro site hMem
                                      exact List.mem_append.mpr (Or.inl hMem)
                                    route :=
                                      Or.inr
                                        ⟨adapter, rfl, hShape, hFrame, hAdapter,
                                          List.mem_append.mpr
                                            (Or.inl (List.mem_cons_self))⟩ }
      · simp [hName] at hLookup
        unfold TypedCfgCompiler.lowerProcBodiesWithShapes? at hLower
        cases hShape : entryShapes.find? head.name with
        | none =>
            cases hBody :
                TypedCfgCompiler.compileBlock? head.body
                  { procs := allProcs
                    leaveLabel? := some (ProcLabel.exit head.name)
                    leaveShape? :=
                      some (TypedCfgCompiler.Shape.procExit head) }
                  supply (ProcLabel.entry head.name)
                  (TypedCfgCompiler.Shape.procEntry head)
                  (ProcLabel.exit head.name) with
            | none =>
                simp [hShape, hBody] at hLower
            | some bodyResult =>
                cases hRequire :
                    bodyResult.requireFallthrough?
                      (TypedCfgCompiler.Shape.procExit head) with
                | none =>
                    simp [hShape, hBody, hRequire] at hLower
                | some unit =>
                    cases unit
                    cases hTail :
                        TypedCfgCompiler.lowerProcBodiesWithShapes?
                          entryShapes allProcs rest bodyResult.next with
                    | none =>
                        simp [hShape, hBody, hRequire, hTail] at hLower
                    | some tailResult =>
                        rcases tailResult with
                          ⟨tailBlocks, tailNext, tailCalls⟩
                        simp [hShape, hBody, hRequire, hTail] at hLower
                        rcases hLower with ⟨rfl, rfl, rfl⟩
                        let fragment :=
                          ih hTail hLookup
                        exact
                          { fragment with
                            blocks := by
                              intro block hMem
                              exact
                                List.mem_append.mpr
                                  (Or.inr (fragment.blocks block hMem))
                            calls := by
                              intro site hMem
                              exact
                                List.mem_append.mpr
                                  (Or.inr (fragment.calls site hMem))
                            route := by
                              rcases fragment.route with hDirect | hAdapter
                              · exact Or.inl hDirect
                              · rcases hAdapter with
                                  ⟨adapter, hEntry, hInput,
                                    hFrame, hAdapterCompile, hAdapterMem⟩
                                exact
                                  Or.inr
                                    ⟨adapter, hEntry, hInput,
                                      hFrame, hAdapterCompile,
                                      List.mem_append.mpr
                                        (Or.inr hAdapterMem)⟩ }
        | some bodyInput =>
            cases hFrame :
                TypedCfgCompiler.Shape.requireReturnTokenDepth?
                  head.argc bodyInput with
            | none =>
                simp [hShape, hFrame] at hLower
            | some unit =>
                cases unit
                cases hAdapter :
                    TypedCfgCompiler.mkBlock?
                      (ProcLabel.entry head.name)
                      (TypedCfgCompiler.Shape.procEntry head)
                      [.relabel bodyInput]
                      (.jump (ProcLabel.body head.name)) with
                | none =>
                    simp [hShape, hFrame, hAdapter] at hLower
                | some adapter =>
                    cases hBody :
                        TypedCfgCompiler.compileBlock? head.body
                          { procs := allProcs
                            leaveLabel? := some (ProcLabel.exit head.name)
                            leaveShape? :=
                              some (TypedCfgCompiler.Shape.procExit head) }
                          supply (ProcLabel.body head.name) bodyInput
                          (ProcLabel.exit head.name) with
                    | none =>
                        simp [hShape, hFrame, hAdapter, hBody] at hLower
                    | some bodyResult =>
                        cases hRequire :
                            bodyResult.requireFallthrough?
                              (TypedCfgCompiler.Shape.procExit head) with
                        | none =>
                            simp [hShape, hFrame, hAdapter, hBody, hRequire] at hLower
                        | some unit =>
                            cases unit
                            cases hTail :
                                TypedCfgCompiler.lowerProcBodiesWithShapes?
                                  entryShapes allProcs rest bodyResult.next with
                            | none =>
                                simp [hShape, hFrame, hAdapter, hBody,
                                  hRequire, hTail] at hLower
                            | some tailResult =>
                                rcases tailResult with
                                  ⟨tailBlocks, tailNext, tailCalls⟩
                                simp [hShape, hFrame, hAdapter, hBody,
                                  hRequire, hTail] at hLower
                                rcases hLower with ⟨rfl, rfl, rfl⟩
                                let fragment :=
                                  ih hTail hLookup
                                exact
                                  { fragment with
                                    blocks := by
                                      intro block hMem
                                      exact
                                        List.mem_cons_of_mem adapter
                                          (List.mem_append.mpr
                                            (Or.inr
                                              (fragment.blocks block hMem)))
                                    calls := by
                                      intro site hMem
                                      exact
                                        List.mem_append.mpr
                                          (Or.inr (fragment.calls site hMem))
                                    route := by
                                      rcases fragment.route with
                                        hDirect | hFragmentAdapter
                                      · exact Or.inl hDirect
                                      · rcases hFragmentAdapter with
                                          ⟨fragmentAdapter, hEntry, hInput,
                                            hFragmentFrame, hAdapterCompile,
                                            hAdapterMem⟩
                                        exact
                                          Or.inr
                                            ⟨fragmentAdapter, hEntry, hInput,
                                              hFragmentFrame, hAdapterCompile,
                                              List.mem_cons_of_mem adapter
                                                (List.mem_append.mpr
                                                  (Or.inr hAdapterMem))⟩ }

/--
Successful generation exposes all compiler-produced whole-program fragments and
the checked global return-token uniqueness invariant.
-/
theorem components_of_generateWithProcEntryShapes?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? source entryShapes =
        some cfg) :
    ∃ main procBlocks next procCalls,
      TypedCfgCompiler.compileBlock? source.body
          { procs := source.procs } 0 TypedCfgCompiler.entryLabel
          TypedCfg.Shape.caller ProcLabel.programEnd =
        some main ∧
      TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes
          source.procs source.procs main.next =
        some (procBlocks, next, procCalls) ∧
      ((main.calls ++ procCalls).map
        TypedCfgCompiler.DispatchSite.token).Nodup ∧
      cfg =
        { entry := TypedCfgCompiler.entryLabel
          blocks :=
            main.blocks ++ procBlocks ++
              TypedCfgCompiler.dispatchBlocks source.procs
                (main.calls ++ procCalls) ++
              [{ label := ProcLabel.programEnd
                 input :=
                   main.fallthrough?.getD TypedCfg.Shape.caller
                 body := []
                 output :=
                   main.fallthrough?.getD TypedCfg.Shape.caller
                 term := .invalid }] } := by
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
          rcases hGenerate with ⟨hTokens, hCfg⟩
          refine
            ⟨main, procBlocks, next, procCalls,
              rfl, hProcs, ?_, ?_⟩
          · simpa using hTokens
          · simpa [List.append_assoc] using hCfg.symm

/--
Checked whole-program generation context used by recursive procedure
preservation.

All compiler-produced data is recovered from successful generation; callers
provide only the source program, its selected entry shapes, and the generated
well-typed CFG.
-/
structure GeneratedContext
    (source : Structured.Program)
    (entryShapes : TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program) where
  main : TypedCfgCompiler.Result
  procBlocks : List TypedCfg.Block
  next : LabelSupply
  procCalls : List TypedCfgCompiler.DispatchSite
  mainCompile :
    TypedCfgCompiler.compileBlock? source.body
        { procs := source.procs } 0 TypedCfgCompiler.entryLabel
        TypedCfg.Shape.caller ProcLabel.programEnd =
      some main
  procsCompile :
    TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes
        source.procs source.procs main.next =
      some (procBlocks, next, procCalls)
  tokensUnique :
    ((main.calls ++ procCalls).map
      TypedCfgCompiler.DispatchSite.token).Nodup
  cfgEq :
    cfg =
      { entry := TypedCfgCompiler.entryLabel
        blocks :=
          main.blocks ++ procBlocks ++
            TypedCfgCompiler.dispatchBlocks source.procs
              (main.calls ++ procCalls) ++
            [{ label := ProcLabel.programEnd
               input :=
                 main.fallthrough?.getD TypedCfg.Shape.caller
               body := []
               output :=
                 main.fallthrough?.getD TypedCfg.Shape.caller
               term := .invalid }] }
  wellTyped : cfg.WellTyped

namespace GeneratedContext

def calls
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    List TypedCfgCompiler.DispatchSite :=
  context.main.calls ++ context.procCalls

theorem entry_eq
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    cfg.entry = TypedCfgCompiler.entryLabel := by
  rw [context.cfgEq]

theorem programEndBlock
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    cfg.findBlock? ProcLabel.programEnd =
      some
        { label := ProcLabel.programEnd
          input :=
            context.main.fallthrough?.getD TypedCfg.Shape.caller
          body := []
          output :=
            context.main.fallthrough?.getD TypedCfg.Shape.caller
          term := .invalid } := by
  let block : TypedCfg.Block :=
    { label := ProcLabel.programEnd
      input := context.main.fallthrough?.getD TypedCfg.Shape.caller
      body := []
      output := context.main.fallthrough?.getD TypedCfg.Shape.caller
      term := .invalid }
  have hMem : block ∈ cfg.blocks := by
    rw [context.cfgEq]
    simp [block, List.append_assoc]
  simpa [block] using
    TypedCfg.Program.findBlock?_eq_some_of_mem context.wellTyped.1 hMem

def of_generate
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? source entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped) :
    GeneratedContext source entryShapes cfg := by
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
          rcases hGenerate with ⟨hTokens, hCfg⟩
          exact
            { main := main
              procBlocks := procBlocks
              next := next
              procCalls := procCalls
              mainCompile := hMain
              procsCompile := hProcs
              tokensUnique := by simpa using hTokens
              cfgEq := by
                simpa [List.append_assoc] using hCfg.symm
              wellTyped := hWellTyped }

theorem mainBlocks
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    BlocksInProgram context.main cfg := by
  apply BlocksInProgram.of_subset_of_wellTyped context.wellTyped
  intro block hMem
  rw [context.cfgEq]
  simp [hMem, List.append_assoc]

theorem mainCalls
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    CallsInProgram context.main context.calls := by
  intro site hMem
  exact List.mem_append.mpr (Or.inl hMem)

theorem procFragment_of_lookup?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name source.procs = some proc) :
    ∃ fragment :
        ProcFragment entryShapes source.procs proc
          context.procBlocks context.procCalls,
      BlocksInProgram fragment.result cfg ∧
        CallsInProgram fragment.result context.calls := by
  let fragment :=
    Program.procFragment_of_lowerProcBodiesWithShapes?
      context.procsCompile hLookup
  refine ⟨fragment, ?_, ?_⟩
  · apply BlocksInProgram.of_subset_of_wellTyped context.wellTyped
    intro block hMem
    rw [context.cfgEq]
    have hProcMem := fragment.blocks block hMem
    simp [hProcMem, List.append_assoc]
  · intro site hMem
    exact
      List.mem_append.mpr
        (Or.inr (fragment.calls site hMem))

theorem dispatchBlock
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name source.procs = some proc) :
    cfg.findBlock? (ProcLabel.exit proc.name) =
      some (TypedCfgCompiler.dispatchBlock proc context.calls) := by
  have hProcMem :=
    Structured.ProcList.mem_of_lookup? hLookup
  have hMem :
      TypedCfgCompiler.dispatchBlock proc context.calls ∈ cfg.blocks := by
    change
      TypedCfgCompiler.dispatchBlock proc
          (context.main.calls ++ context.procCalls) ∈
        cfg.blocks
    have hBlocksEq :
        cfg.blocks =
          context.main.blocks ++ context.procBlocks ++
            TypedCfgCompiler.dispatchBlocks source.procs
              (context.main.calls ++ context.procCalls) ++
            [{ label := ProcLabel.programEnd
               input :=
                 context.main.fallthrough?.getD TypedCfg.Shape.caller
               body := []
               output :=
                 context.main.fallthrough?.getD TypedCfg.Shape.caller
               term := .invalid }] :=
      congrArg TypedCfg.Program.blocks context.cfgEq
    rw [hBlocksEq]
    have hDispatchMem :
        TypedCfgCompiler.dispatchBlock proc
            (context.main.calls ++ context.procCalls) ∈
          TypedCfgCompiler.dispatchBlocks source.procs
            (context.main.calls ++ context.procCalls) := by
      exact List.mem_map.mpr ⟨proc, hProcMem, rfl⟩
    simp [hDispatchMem]
  have hFind :=
    TypedCfg.Program.findBlock?_eq_some_of_mem
      context.wellTyped.1 hMem
  simpa [TypedCfgCompiler.dispatchBlock] using hFind

/--
The canonical procedure entry either is the compiled body entry or executes
the generated zero-byte relabel adapter and reaches it without changing the
runtime state.
-/
theorem eventually_procEntry
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {proc : Structured.Proc}
    {fragment :
      ProcFragment entryShapes source.procs proc
        context.procBlocks context.procCalls}
    (state : EVMState) :
    cfg.Eventually (ProcLabel.entry proc.name) state
      (.jump fragment.entry state) := by
  rcases fragment.route with hDirect | hAdapterRoute
  · rcases hDirect with ⟨hEntry, hInput⟩
    rw [hEntry]
    exact TypedCfg.Program.Eventually.residual _ _ _
  · rcases hAdapterRoute with
      ⟨adapter, hEntry, hInput, _hFrame, hAdapterCompile, hAdapterMem⟩
    have hMem : adapter ∈ cfg.blocks := by
      have hBlocksEq :
          cfg.blocks =
            context.main.blocks ++ context.procBlocks ++
              TypedCfgCompiler.dispatchBlocks source.procs
                (context.main.calls ++ context.procCalls) ++
              [{ label := ProcLabel.programEnd
                 input :=
                   context.main.fallthrough?.getD TypedCfg.Shape.caller
                 body := []
                 output :=
                   context.main.fallthrough?.getD TypedCfg.Shape.caller
                 term := .invalid }] :=
        congrArg TypedCfg.Program.blocks context.cfgEq
      rw [hBlocksEq]
      simp [hAdapterMem]
    have hFind :=
      TypedCfg.Program.findBlock?_eq_some_of_mem
        context.wellTyped.1 hMem
    unfold TypedCfgCompiler.mkBlock? at hAdapterCompile
    cases hType :
        TypedCfg.Instr.type? (.relabel fragment.input)
          (TypedCfgCompiler.Shape.procEntry proc) with
    | none =>
        simp [TypedCfg.Block.bodyType?, hType] at hAdapterCompile
    | some output =>
        simp [TypedCfg.Block.bodyType?, hType] at hAdapterCompile
        cases hAdapterCompile
        rw [hEntry]
        refine ⟨1, ?_⟩
        simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind,
          TypedCfg.Block.run, TypedCfg.Block.runBody,
          TypedCfg.Instr.runAt, hType, TypedCfg.Instr.runState,
          TypedCfg.Block.runTerm, Bind.bind, Except.bind]

end GeneratedContext

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
  rcases components_of_generateWithProcEntryShapes? hGenerate with
    ⟨main, procBlocks, next, procCalls,
      hMain, hProcs, hTokens, rfl⟩
  refine ⟨main, hMain, ?_⟩
  apply BlocksInProgram.of_subset_of_wellTyped hWellTyped
  intro block hMem
  simp [hMem, List.append_assoc]

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


end TypedCfgPreservation
end Structured
end EvmCompiler
