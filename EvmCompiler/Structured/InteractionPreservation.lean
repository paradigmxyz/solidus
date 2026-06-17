import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.Structured.InteractionSemantics
import EvmCompiler.Structured.TypedCfgPreservation.Core
import EvmCompiler.TypedCfg.InteractionSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionPreservation

namespace StateRel

/--
Expose the compiler-owned realization as one suffix below the complete
source-visible stack.
-/
theorem hiddenSuffix
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hRel : TypedCfgPreservation.StateRel source tokens target) :
    ∃ hidden,
      TypedCfgPreservation.realizeStack
          [] source.returns tokens = some hidden ∧
        Assembly.SameRuntimeData target
          { source.evm with
            stack := source.evm.stack ++ hidden } := by
  rcases hRel with ⟨realized, hRealize, hSame⟩
  have hAppend :=
    TypedCfgPreservation.realizeStack_append_prefix
      source.evm.stack [] source.returns tokens
  cases hHidden :
      TypedCfgPreservation.realizeStack [] source.returns tokens with
  | none =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
  | some hidden =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
      exact ⟨hidden, rfl, hSame⟩

end StateRel

namespace BasicInstr

/--
The existing Structured-to-TypedCfg instruction lowering preserves the
EVM-level open effect tree exactly. Specialized TypedCfg stack instructions
embed the same closed primitive step.
-/
theorem target_openRunState_toCfg
    (instr : Structured.BasicInstr) (shape : TypedCfg.Shape)
    (state : EVMState) :
    TypedCfg.InteractionSemantics.Instr.openRunState
        (TypedCfgCompiler.BasicInstr.toCfg instr) shape state =
      InteractionSemantics.BasicInstr.openStepEVM instr state := by
  cases instr with
  | push value => rfl
  | bindLocals offset names => rfl
  | bindScratch baseDepth name slot => rfl
  | op op =>
      cases op <;> rfl

abbrev RuntimeStateRel :=
  Assembly.InteractionPreservation.PrimOp.RuntimeStateRel

/--
The ordinary instruction step embedded by a Structured-only bookkeeping
instruction is congruent under runtime-control erasure.
-/
theorem closedStep_runtimeRel
    {instr : Structured.BasicInstr}
    {target source : EVMState}
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (.done (instr.step target))
      (.done (instr.step source)) := by
  apply Simulation.Interaction.Rel.done
  have hRun :=
    TypedCfgPreservation.BasicInstr.step_map_eraseRuntimeControl
      (instr := instr) hRel
  cases hTarget : instr.step target with
  | error targetError =>
      cases hSource : instr.step source with
      | error sourceError =>
          simp [hTarget, hSource, Except.map] at hRun
          exact
            Simulation.Interaction.ExceptRel.error hRun
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hRun
  | ok targetFinal =>
      cases hSource : instr.step source with
      | error sourceError =>
          simp [hTarget, hSource, Except.map] at hRun
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hRun
          exact
            Simulation.Interaction.ExceptRel.ok hRun

/--
One Structured EVM-level open instruction is insensitive to compiler-owned
runtime counters when the existing lowering is well typed.
-/
theorem openStepEVM_runtimeRel
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {target source : EVMState}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.BasicInstr.openStepEVM instr target)
      (InteractionSemantics.BasicInstr.openStepEVM instr source) := by
  cases instr with
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            _hBound, _hOutputLength⟩ :=
        TypedCfgPreservation.BasicOp.type_length_toCfg hType
      have hNoPc : op.toPrimOp ≠ .pc := by
        cases op <;> simp [Structured.BasicOp.toPrimOp]
      exact
        Assembly.InteractionPreservation.PrimOp.openStep_runtimeRel
          ⟨(inputArity, outputArity), hArity⟩ hNoPc hRel
  | push value =>
      exact closedStep_runtimeRel hRel
  | bindLocals offset names =>
      exact closedStep_runtimeRel hRel
  | bindScratch baseDepth name slot =>
      exact closedStep_runtimeRel hRel

/--
One accepted Structured instruction preserves an opaque stack suffix below
the source-visible frame for every resource answer and external-world
response.
-/
theorem openStepEVM_append_stack_rel
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    (state : EVMState) (hidden : EvmYul.Stack Word)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe?
          instr input output = true)
    (hFits :
      TypedCfgCompiler.Shape.sourceLength input ≤
        state.stack.length) :
    Simulation.Interaction.Rel
      (Assembly.InteractionPreservation.PrimOp.StackSuffixRuntimeRel
        hidden)
      (InteractionSemantics.BasicInstr.openStepEVM instr state)
      (InteractionSemantics.BasicInstr.openStepEVM instr
        { state with stack := state.stack ++ hidden }) := by
  cases instr with
  | op op =>
      have hSourceType :=
        TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe
      obtain
          ⟨inputArity, outputArity, hArity,
            hShapeBound, _hOutputLength⟩ :=
        TypedCfgPreservation.BasicOp.type_length_toCfg hSourceType
      exact
        Assembly.InteractionPreservation.PrimOp.openStep_append_stack_rel_of_stackArity_le
          state hidden hArity
          (Nat.le_trans hShapeBound hFits)
  | push value =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      cases state
      simp [
        InteractionSemantics.BasicInstr.openStepEVM,
        Structured.BasicInstr.step,
        Assembly.Target.stepInstr,
        Assembly.InteractionPreservation.PrimOp.StackSuffixStateRel,
        Assembly.SameRuntimeData, Assembly.eraseRuntimeControl,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
  | bindLocals offset names =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Assembly.SameRuntimeData.refl _
  | bindScratch baseDepth name slot =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Assembly.SameRuntimeData.refl _

def SourceFrameFitsAfter (output : TypedCfg.Shape) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final =>
      TypedCfgCompiler.Shape.SourceFrameFits
        output final.stack.length

/--
Every successful open branch of an accepted Structured instruction preserves
the source-visible frame. Primitive instructions consume only the generic
Assembly stack contract; Structured-owned bookkeeping reuses its ordinary
preservation theorem.
-/
theorem openStepEVM_sourceFrameFits
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe?
          instr input output = true)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input state.stack.length) :
    Simulation.Interaction.AllDone
      (SourceFrameFitsAfter output)
      (InteractionSemantics.BasicInstr.openStepEVM instr state) := by
  cases instr with
  | op op =>
      have hSourceType :=
        TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe
      obtain
          ⟨inputArity, outputArity, hArity,
            hInputBound, hOutputLength⟩ :=
        TypedCfgPreservation.BasicOp.type_length_toCfg hSourceType
      have hStack :=
        Assembly.InteractionPreservation.PrimOp.openStep_realizesStackArity
          (state := state) hArity
      apply Simulation.Interaction.AllDone.mono hStack
      intro outcome hOutcome
      cases outcome with
      | error err =>
          exact True.intro
      | ok final =>
          change
            TypedCfgCompiler.Shape.SourceFrameFits
              output final.stack.length
          change
            final.stack.length =
              state.stack.length - inputArity + outputArity
            at hOutcome
          constructor
          · change
              (TypedCfgCompiler.Shape.sourceView output).length ≤
                final.stack.length
            have hSourceBound := hFits.1
            change
              (TypedCfgCompiler.Shape.sourceView input).length ≤
                state.stack.length
              at hSourceBound
            have hActualBound :
                inputArity ≤ state.stack.length :=
              Nat.le_trans hInputBound hSourceBound
            change
              (TypedCfgCompiler.Shape.sourceView output).length =
                (TypedCfgCompiler.Shape.sourceView input).length -
                  inputArity + outputArity
              at hOutputLength
            omega
          · intro outputDepth hOutputDepth
            obtain ⟨inputDepth, hInputDepth⟩ :=
              TypedCfgPreservation.BasicInstr.input_returnTokenDepth?_eq_some_of_output
                hType hSafe hOutputDepth
            have hInputSource :
                TypedCfgCompiler.Shape.sourceLength input =
                  inputDepth :=
              TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some
                hInputDepth
            have hOutputSource :
                TypedCfgCompiler.Shape.sourceLength output =
                  outputDepth :=
              TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some
                hOutputDepth
            have hInputExact :=
              hFits.2 inputDepth hInputDepth
            change
              (TypedCfgCompiler.Shape.sourceView output).length =
                (TypedCfgCompiler.Shape.sourceView input).length -
                  inputArity + outputArity
              at hOutputLength
            change
              (TypedCfgCompiler.Shape.sourceView input).length =
                inputDepth
              at hInputSource
            change
              (TypedCfgCompiler.Shape.sourceView output).length =
                outputDepth
              at hOutputSource
            omega
  | push value =>
      apply Simulation.Interaction.AllDone.done
      exact
        TypedCfgPreservation.BasicInstr.step_sourceFrameFits_of_type
          hType hSafe hFits rfl
  | bindLocals offset names =>
      apply Simulation.Interaction.AllDone.done
      exact
        TypedCfgPreservation.BasicInstr.step_sourceFrameFits_of_type
          hType hSafe hFits rfl
  | bindScratch baseDepth name slot =>
      apply Simulation.Interaction.AllDone.done
      exact
        TypedCfgPreservation.BasicInstr.step_sourceFrameFits_of_type
          hType hSafe hFits rfl

def ResultRel (tokens : List Word) (output : TypedCfg.Shape)
    (source : RunState) (target : EVMState × TypedCfg.Shape) : Prop :=
  target.2 = output ∧
    TypedCfgPreservation.StateRel source tokens target.1 ∧
    TypedCfgCompiler.Shape.SourceFrameFits
      output source.evm.stack.length

abbrev DoneRel (tokens : List Word) (output : TypedCfg.Shape) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (ResultRel tokens output)

/--
One accepted Structured instruction and its existing TypedCfg lowering expose
the same open query tree and preserve the compiler-owned ghost-frame
realization for every answer.
-/
theorem openRunAt_toCfg
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hSafe :
      TypedCfgCompiler.BasicInstr.sourceSafe?
          instr input output = true)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel (DoneRel tokens output)
      (InteractionSemantics.BasicInstr.openStep instr source)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        (TypedCfgCompiler.BasicInstr.toCfg instr) input target) := by
  rcases StateRel.hiddenSuffix hRel with
    ⟨hidden, hHidden, hSame⟩
  have hSuffix :=
    openStepEVM_append_stack_rel
      source.evm hidden hSafe hFits.1
  have hRuntime :=
    openStepEVM_runtimeRel hType hSame
  have hEVMTrans :=
    Simulation.Interaction.Rel.trans
      hSuffix hRuntime.symm
  have hEVM :
      Simulation.Interaction.Rel
        (Simulation.Interaction.ExceptRel
          (fun _sourceError _targetError : EVMException => True)
          (fun sourceFinal targetFinal =>
            TypedCfgPreservation.StateRel
              (source.withEVM sourceFinal) tokens targetFinal))
        (InteractionSemantics.BasicInstr.openStepEVM
          instr source.evm)
        (InteractionSemantics.BasicInstr.openStepEVM
          instr target) := by
    apply Simulation.Interaction.Rel.mono hEVMTrans
    intro sourceDone targetDone hDone
    cases sourceDone with
    | error sourceError =>
        cases targetDone with
        | error targetError =>
            exact
              Simulation.Interaction.ExceptRel.error True.intro
        | ok targetFinal =>
            rcases hDone with
              ⟨middleDone, hSuffixDone, hRuntimeDone⟩
            cases hSuffixDone with
            | error _hSourceError =>
                cases hRuntimeDone
    | ok sourceFinal =>
        cases targetDone with
        | error targetError =>
            rcases hDone with
              ⟨middleDone, hSuffixDone, hRuntimeDone⟩
            cases hSuffixDone with
            | ok _hSuffixState =>
                cases hRuntimeDone
        | ok targetFinal =>
            rcases hDone with
              ⟨middleDone, hSuffixDone, hRuntimeDone⟩
            cases hSuffixDone with
            | ok hSuffixState =>
                cases hRuntimeDone with
                | ok hRuntimeState =>
                    apply Simulation.Interaction.ExceptRel.ok
                    refine
                      ⟨sourceFinal.stack ++ hidden, ?_, ?_⟩
                    · have hFinalAppend :=
                        TypedCfgPreservation.realizeStack_append_prefix
                          sourceFinal.stack []
                          source.returns tokens
                      simpa [RunState.withEVM, hHidden] using hFinalAppend
                    · exact
                        Assembly.SameRuntimeData.trans
                          hRuntimeState hSuffixState
  have hAllFits :=
    openStepEVM_sourceFrameFits hType hSafe hFits
  have hEVMWithFitsRaw :=
    Simulation.Interaction.Rel.strengthen_left hEVM hAllFits
  have hEVMWithFits :
      Simulation.Interaction.Rel
        (Simulation.Interaction.ExceptRel
          (fun _sourceError _targetError : EVMException => True)
          (fun sourceFinal targetFinal =>
            TypedCfgPreservation.StateRel
                (source.withEVM sourceFinal) tokens targetFinal ∧
              TypedCfgCompiler.Shape.SourceFrameFits
                output sourceFinal.stack.length))
        (InteractionSemantics.BasicInstr.openStepEVM
          instr source.evm)
        (InteractionSemantics.BasicInstr.openStepEVM
          instr target) := by
    apply Simulation.Interaction.Rel.mono hEVMWithFitsRaw
    intro sourceDone targetDone hDone
    rcases hDone with ⟨hRelated, hSourceFits⟩
    cases hRelated with
    | error _hErrors =>
        exact
          Simulation.Interaction.ExceptRel.error True.intro
    | ok hStates =>
        exact
          Simulation.Interaction.ExceptRel.ok
            ⟨hStates, hSourceFits⟩
  have hMapped :=
    Simulation.Interaction.Rel.bind hEVMWithFits
      (fun sourceFinal targetFinal hFinal =>
        Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.ok
            (show
              ResultRel tokens output
                (source.withEVM sourceFinal) (targetFinal, output)
              from ⟨rfl, hFinal.1, hFinal.2⟩)))
  simpa [
    InteractionSemantics.BasicInstr.openStep,
    Simulation.Interaction.map,
    TypedCfg.InteractionSemantics.Instr.openRunAt,
    TypedCfg.Control.Instr.runAt, hType,
    target_openRunState_toCfg] using hMapped

end BasicInstr

namespace Code

/--
Accepted straight-line Structured code preserves the open interaction tree of
its existing TypedCfg lowering. The theorem composes only the adjacent
instruction theorem and carries the source-frame invariant needed by the next
control construct.
-/
theorem openRun_toCfg
    {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hType :
      TypedCfgCompiler.Code.type? code input = some output)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (BasicInstr.DoneRel tokens output)
      (InteractionSemantics.Code.openRun code source)
      (TypedCfg.InteractionSemantics.Block.openRunBody
        (TypedCfgCompiler.Code.toCfg code) input target) := by
  induction code generalizing input source target with
  | nil =>
      simp [TypedCfgCompiler.Code.type?] at hType
      subst output
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ⟨rfl, hRel, hFits⟩
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hInstrType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hInstrType] at hType
      | some middle =>
          cases hSafe :
              TypedCfgCompiler.BasicInstr.sourceSafe?
                instr input middle with
          | false =>
              simp [hInstrType, hSafe] at hType
          | true =>
              have hRestType :
                  TypedCfgCompiler.Code.type? rest middle =
                    some output := by
                simpa [hInstrType, hSafe] using hType
              have hHead :=
                BasicInstr.openRunAt_toCfg
                  hInstrType hSafe hFits hRel
              have hComposed :
                  Simulation.Interaction.Rel
                    (BasicInstr.DoneRel tokens output)
                    (Simulation.Interaction.bind
                      (InteractionSemantics.BasicInstr.openStep
                        instr source)
                      (InteractionSemantics.Code.openRun rest))
                    (Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        (TypedCfgCompiler.BasicInstr.toCfg instr)
                        input target)
                      (fun result =>
                        TypedCfg.InteractionSemantics.Block.openRunBody
                          (TypedCfgCompiler.Code.toCfg rest)
                          result.2 result.1)) := by
                apply Simulation.Interaction.Rel.bind hHead
                intro sourceMiddle targetMiddle hMiddle
                rcases hMiddle with
                  ⟨hMiddleShape, hMiddleRel, hMiddleFits⟩
                simpa [hMiddleShape] using
                  ih hRestType hMiddleFits hMiddleRel
              simpa [
                InteractionSemantics.Code.openRun,
                EffectSemantics.Control.Code.run,
                TypedCfg.InteractionSemantics.Block.openRunBody,
                TypedCfg.Control.Block.runBody,
                TypedCfgCompiler.Code.toCfg] using hComposed

end Code

end InteractionPreservation
end Structured
end EvmCompiler
