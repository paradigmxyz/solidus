import EvmCompiler.Simulation.ObserverPass
import EvmCompiler.Structured.ObserverSemantics
import EvmCompiler.Structured.TypedCfgCompilerFacts
import EvmCompiler.Structured.TypedCfgPreservation.Core
import EvmCompiler.TypedCfg.ObserverSemantics

namespace EvmCompiler
namespace Structured
namespace ObserverPreservation

abbrev Trace := Assembly.ResourceTrace

attribute [local simp] Assembly.PrimStep.idRun_eq

def RunStateRel (left right : Structured.RunState) : Prop :=
  left.returns = right.returns ∧
    Assembly.SameRuntimeData left.evm right.evm

structure ReplayStateRel {transcript : Trace}
    (left right : ObserverSemantics.State transcript) : Prop where
  cursor : left.cursor = right.cursor
  source : RunStateRel left.source right.source

def StateRel {transcript : Trace}
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (target : EVMState) (trace : Trace) : Prop :=
  TypedCfgPreservation.StateRel source.source tokens target ∧
    source.remaining = trace

namespace ReplayStateRel

theorem refl
    {transcript : Trace}
    (state : ObserverSemantics.State transcript) :
    ReplayStateRel state state :=
  ⟨rfl, rfl, Assembly.SameRuntimeData.refl state.source.evm⟩

theorem symm
    {transcript : Trace}
    {left right : ObserverSemantics.State transcript}
    (hRel : ReplayStateRel left right) :
    ReplayStateRel right left :=
  ⟨hRel.cursor.symm,
    hRel.source.1.symm,
    Assembly.SameRuntimeData.symm hRel.source.2⟩

theorem trans
    {transcript : Trace}
    {first second third : ObserverSemantics.State transcript}
    (hFirst : ReplayStateRel first second)
    (hSecond : ReplayStateRel second third) :
    ReplayStateRel first third :=
  ⟨hFirst.cursor.trans hSecond.cursor,
    hFirst.source.1.trans hSecond.source.1,
    Assembly.SameRuntimeData.trans
      hFirst.source.2 hSecond.source.2⟩

theorem remaining_eq
    {transcript : Trace}
    {left right : ObserverSemantics.State transcript}
    (hRel : ReplayStateRel left right) :
    left.remaining = right.remaining := by
  unfold Simulation.ResourceReplay.State.remaining
  rw [hRel.cursor]

theorem withEVM
    {transcript : Trace}
    {left right : ObserverSemantics.State transcript}
    {leftEVM rightEVM : EVMState}
    (hRel : ReplayStateRel left right)
    (hEVM : Assembly.SameRuntimeData leftEVM rightEVM) :
    ReplayStateRel
      (left.withSource (left.source.withEVM leftEVM))
      (right.withSource (right.source.withEVM rightEVM)) := by
  exact
    ⟨hRel.cursor,
      by simpa using hRel.source.1,
      by simpa using hEVM⟩

end ReplayStateRel

theorem applyObserver_toOracle
    {transcript : Trace} (kind : Assembly.ResourceObserver)
    (state : ObserverSemantics.State transcript) :
    Assembly.ResourceObserver.applyOracleFromPostState
        kind state.source.evm state.remaining =
      (ObserverSemantics.applyObserver kind state).map fun final =>
        (final.source.evm, final.remaining) := by
  cases hSource :
      Simulation.ResourceReplay.consume? kind state with
  | none =>
      have hConsume :=
        Simulation.ResourceReplay.consume_remaining_eq kind state
      simp [hSource] at hConsume
      unfold Assembly.ResourceObserver.applyOracleFromPostState
      rw [← hConsume]
      simp [ObserverSemantics.applyObserver,
        hSource, Structured.invalid, Except.map,
        Bind.bind, Except.bind]
  | some consumed =>
      rcases consumed with ⟨value, state'⟩
      have hConsume :=
        Simulation.ResourceReplay.consume_remaining hSource
      have hSourceState :=
        Simulation.ResourceReplay.consume?_source hSource
      cases hOverwrite :
          Assembly.ResourceObserver.overwriteTop
            value state.source.evm with
      | error err =>
          simp [ObserverSemantics.applyObserver,
            Assembly.ResourceObserver.applyOracleFromPostState,
            hSource, hConsume, hSourceState, hOverwrite,
            Except.map, Bind.bind, Except.bind]
      | ok evm =>
          simp only [ObserverSemantics.applyObserver,
            Assembly.ResourceObserver.applyOracleFromPostState,
            hSource, hConsume, hSourceState, hOverwrite,
            Except.map, Bind.bind, Except.bind,
            Simulation.ResourceReplay.State.withSource_source,
            Simulation.ResourceReplay.State.withSource_remaining,
            RunState.withEVM_evm]

theorem overwriteTop_of_rel
    {value : Word} {left right leftFinal : EVMState}
    (hRel : Assembly.SameRuntimeData left right)
    (hLeft :
      Assembly.ResourceObserver.overwriteTop value left =
        .ok leftFinal) :
    ∃ rightFinal,
      Assembly.ResourceObserver.overwriteTop value right =
          .ok rightFinal ∧
        Assembly.SameRuntimeData leftFinal rightFinal := by
  cases hStack : left.stack with
  | nil =>
      simp [Assembly.ResourceObserver.overwriteTop, hStack] at hLeft
  | cons top rest =>
      have hRightStack : right.stack = top :: rest := by
        rw [← Assembly.SameRuntimeData.stack_eq hRel, hStack]
      simp [Assembly.ResourceObserver.overwriteTop, hStack] at hLeft
      subst leftFinal
      refine
        ⟨{ right with stack := value :: rest }, ?_, ?_⟩
      · simp [Assembly.ResourceObserver.overwriteTop, hRightStack]
      · exact Assembly.SameRuntimeData.replaceStack hRel rfl

namespace BasicInstr

theorem runState_toCfg
    (instr : Structured.BasicInstr) (input : TypedCfg.Shape)
    (state : EVMState) :
    TypedCfg.Instr.runState
        (TypedCfgCompiler.BasicInstr.toCfg instr) input state =
      instr.step state := by
  cases instr with
  | push value => rfl
  | bindLocals offset names => rfl
  | bindScratch baseDepth name slot => rfl
  | op op =>
      cases op <;> rfl

theorem observer?_toCfg (instr : Structured.BasicInstr) :
    TypedCfg.ObserverSemantics.Instr.observer?
        (TypedCfgCompiler.BasicInstr.toCfg instr) =
      match instr with
      | .op op => ObserverSemantics.basicOpObserver? op
      | _ => none := by
  cases instr with
  | push value => rfl
  | bindLocals offset names => rfl
  | bindScratch baseDepth name slot => rfl
  | op op =>
      cases op <;> rfl

theorem step_of_rel
    {instr : Structured.BasicInstr}
    {left right leftFinal : EVMState}
    (hRel : Assembly.SameRuntimeData left right)
    (hLeft : instr.step left = .ok leftFinal) :
    ∃ rightFinal,
      instr.step right = .ok rightFinal ∧
        Assembly.SameRuntimeData leftFinal rightFinal := by
  have hCongruence :=
    TypedCfgPreservation.BasicInstr.step_map_eraseRuntimeControl
      (instr := instr) hRel
  rw [hLeft] at hCongruence
  cases hRight : instr.step right with
  | error err =>
      simp [hRight, Except.map] at hCongruence
  | ok rightFinal =>
      simp [hRight, Except.map] at hCongruence
      exact ⟨rightFinal, rfl, hCongruence⟩

theorem handler_toCfg
    {transcript : Trace} (instr : Structured.BasicInstr)
    (state : ObserverSemantics.State transcript) (post : EVMState) :
    TypedCfg.ObserverSemantics.Instr.handler.afterInstr
        (TypedCfgCompiler.BasicInstr.toCfg instr) post state.remaining =
      ((ObserverSemantics.handler transcript).afterInstr instr
          (state.withSource (state.source.withEVM post))).map
        (fun final => (final.source.evm, final.remaining)) := by
  change
    (match
      TypedCfg.ObserverSemantics.Instr.observer?
        (TypedCfgCompiler.BasicInstr.toCfg instr)
    with
    | some kind =>
        Assembly.ResourceObserver.applyOracleFromPostState
          kind post state.remaining
    | none => .ok (post, state.remaining)) = _
  rw [observer?_toCfg]
  cases instr with
  | push value =>
      simp [ObserverSemantics.handler, Except.map,
        RunState.withEVM]
  | bindLocals offset names =>
      simp [ObserverSemantics.handler, Except.map,
        RunState.withEVM]
  | bindScratch baseDepth name slot =>
      simp [ObserverSemantics.handler, Except.map,
        RunState.withEVM]
  | op op =>
      cases hObserver : ObserverSemantics.basicOpObserver? op with
      | none =>
          simp [ObserverSemantics.handler, hObserver, Except.map,
            RunState.withEVM]
      | some kind =>
          simp only [ObserverSemantics.handler, hObserver]
          simpa only [
            Simulation.ResourceReplay.State.withSource_source,
            Simulation.ResourceReplay.State.withSource_remaining,
            RunState.withEVM_evm] using
            applyObserver_toOracle kind
              (state.withSource (state.source.withEVM post))

/--
One Structured instruction and its existing TypedCfg lowering consume the same
observer suffix. This is the primitive-effect leaf used by the adjacent
Structured-to-TypedCfg control proof.
-/
theorem runAt_toCfg
    {transcript : Trace} {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {state : ObserverSemantics.State transcript}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output) :
    TypedCfg.ObserverSemantics.Instr.runAt
        (TypedCfgCompiler.BasicInstr.toCfg instr) input
        state.source.evm state.remaining =
      (ObserverSemantics.Code.run [instr] state).map fun final =>
        ((final.source.evm, output), final.remaining) := by
  unfold TypedCfg.ObserverSemantics.Instr.runAt
    TypedCfg.ObserverSemantics.Instr.runState
  rw [hType, runState_toCfg]
  unfold ObserverSemantics.Code.run EffectSemantics.Code.run
  cases hStep : instr.step state.source.evm with
  | error err =>
      simp [hStep, Except.map, Bind.bind, Except.bind]
  | ok post =>
      simp only [hStep, Bind.bind, Except.bind]
      rw [handler_toCfg]
      cases hAfter :
          (ObserverSemantics.handler transcript).afterInstr instr
            (state.withSource (state.source.withEVM post)) with
      | error err =>
          simp [hStep, hAfter, EffectSemantics.Code.run,
            Except.map, Bind.bind, Except.bind]
      | ok final =>
          simp [hStep, hAfter, EffectSemantics.Code.run,
            Except.map, Bind.bind, Except.bind]

end BasicInstr

theorem handler_of_rel
    {transcript : Trace} {instr : Structured.BasicInstr}
    {left right leftFinal : ObserverSemantics.State transcript}
    (hRel : ReplayStateRel left right)
    (hLeft :
      (ObserverSemantics.handler transcript).afterInstr instr left =
        .ok leftFinal) :
    ∃ rightFinal,
      (ObserverSemantics.handler transcript).afterInstr instr right =
          .ok rightFinal ∧
        ReplayStateRel leftFinal rightFinal := by
  cases instr with
  | push value =>
      simp [ObserverSemantics.handler] at hLeft ⊢
      subst leftFinal
      exact hRel
  | bindLocals offset names =>
      simp [ObserverSemantics.handler] at hLeft ⊢
      subst leftFinal
      exact hRel
  | bindScratch baseDepth name slot =>
      simp [ObserverSemantics.handler] at hLeft ⊢
      subst leftFinal
      exact hRel
  | op op =>
      cases hObserver : ObserverSemantics.basicOpObserver? op with
      | none =>
          simp [ObserverSemantics.handler, hObserver] at hLeft ⊢
          subst leftFinal
          exact hRel
      | some kind =>
          simp only [ObserverSemantics.handler, hObserver] at hLeft ⊢
          unfold ObserverSemantics.applyObserver at hLeft ⊢
          cases hConsumeLeft :
              Simulation.ResourceReplay.consume? kind left with
          | none =>
              simp [hConsumeLeft, Structured.invalid] at hLeft
          | some consumedLeft =>
              rcases consumedLeft with ⟨value, consumedLeft⟩
              simp [hConsumeLeft] at hLeft
              obtain
                  ⟨consumedRight, hConsumeRight, hCursor, hSource⟩ :=
                Simulation.ResourceReplay.consume?_rel
                  hRel.cursor hRel.source hConsumeLeft
              rw [hConsumeRight]
              cases hOverwriteLeft :
                  Assembly.ResourceObserver.overwriteTop
                    value consumedLeft.source.evm with
              | error err =>
                  simp [hOverwriteLeft] at hLeft
              | ok leftEVM =>
                  simp [hOverwriteLeft] at hLeft
                  subst leftFinal
                  obtain ⟨rightEVM, hOverwriteRight, hEVM⟩ :=
                    overwriteTop_of_rel hSource.2 hOverwriteLeft
                  refine
                    ⟨consumedRight.withSource
                        (consumedRight.source.withEVM rightEVM),
                      by simp [hOverwriteRight], ?_⟩
                  exact
                    ⟨hCursor,
                      by simpa using hSource.1,
                      by simpa using hEVM⟩

namespace Code

theorem run_of_rel
    {transcript : Trace} {code : Structured.Code}
    {left right leftFinal : ObserverSemantics.State transcript}
    (hRel : ReplayStateRel left right)
    (hLeft : ObserverSemantics.Code.run code left = .ok leftFinal) :
    ∃ rightFinal,
      ObserverSemantics.Code.run code right = .ok rightFinal ∧
        ReplayStateRel leftFinal rightFinal := by
  induction code generalizing left right leftFinal with
  | nil =>
      simp [ObserverSemantics.Code.run,
        EffectSemantics.Code.run] at hLeft ⊢
      subst leftFinal
      exact hRel
  | cons instr rest ih =>
      unfold ObserverSemantics.Code.run EffectSemantics.Code.run at hLeft ⊢
      simp only [ObserverSemantics.stateModel_evm,
        ObserverSemantics.stateModel_withEVM] at hLeft ⊢
      cases hStepLeft : instr.step left.source.evm with
      | error err =>
          simp [hStepLeft, Bind.bind, Except.bind] at hLeft
      | ok leftEVM =>
          simp only [hStepLeft, Bind.bind, Except.bind] at hLeft
          obtain ⟨rightEVM, hStepRight, hEVM⟩ :=
            BasicInstr.step_of_rel hRel.source.2 hStepLeft
          rw [hStepRight]
          let leftMiddle :=
            left.withSource (left.source.withEVM leftEVM)
          let rightMiddle :=
            right.withSource (right.source.withEVM rightEVM)
          have hMiddleRel :
              ReplayStateRel leftMiddle rightMiddle :=
            hRel.withEVM hEVM
          cases hAfterLeft :
              (ObserverSemantics.handler transcript).afterInstr
                instr leftMiddle with
          | error err =>
              simp [leftMiddle, hAfterLeft,
                Bind.bind, Except.bind] at hLeft
          | ok leftAfter =>
              simp only [leftMiddle, hAfterLeft,
                Bind.bind, Except.bind] at hLeft
              obtain ⟨rightAfter, hAfterRight, hAfterRel⟩ :=
                handler_of_rel hMiddleRel hAfterLeft
              simp only [Bind.bind, Except.bind]
              rw [show
                (ObserverSemantics.handler transcript).afterInstr
                    instr
                      (right.withSource
                        (right.source.withEVM rightEVM)) =
                  .ok rightAfter by
                    simpa [rightMiddle] using hAfterRight]
              exact ih hAfterRel hLeft

/--
Straight-line observer execution commutes with the existing Structured-to-
TypedCfg code lowering. The target trace is exactly the unconsumed suffix of
the transcript-indexed Structured replay state.
-/
theorem runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {state : ObserverSemantics.State transcript}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.ObserverSemantics.Block.runBody
        (TypedCfgCompiler.Code.toCfg code) input
        state.source.evm state.remaining =
      (ObserverSemantics.Code.run code state).map fun final =>
        ((final.source.evm, output), final.remaining) := by
  induction code generalizing input output state with
  | nil =>
      simp [TypedCfgCompiler.Code.type?, TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?,
        TypedCfg.ObserverSemantics.Block.runBody,
        ObserverSemantics.Code.run, EffectSemantics.Code.run] at hType ⊢
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
            simp only [TypedCfgCompiler.Code.toCfg, List.map_cons,
              TypedCfg.ObserverSemantics.Block.runBody_cons]
            rw [BasicInstr.runAt_toCfg hHeadType]
            rw [
              ObserverSemantics.Code.run_cons_eq_run_single_bind
                instr rest state]
            cases hHead : ObserverSemantics.Code.run [instr] state with
            | error err =>
                simp [hHead, Except.map, Bind.bind, Except.bind]
            | ok middleState =>
                simp [hHead, Except.map, Bind.bind, Except.bind]
                change
                  TypedCfg.ObserverSemantics.Block.runBody
                      (TypedCfgCompiler.Code.toCfg rest) middle
                      middleState.source.evm middleState.remaining =
                    _
                rw [ih hTailType]
                simp [hHead, Except.map, Bind.bind, Except.bind]

/--
Backward adequacy for the straight-line portion of the adjacent pass.

When the existing TypedCfg lowering executes successfully from the exact
Structured replay state, the shared effect semantics reconstructs the
corresponding Structured code execution. No compiler certificate or replay
witness is accepted.
-/
theorem run_of_runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {state : ObserverSemantics.State transcript}
    {targetFinal : EVMState} {traceFinal : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hRun :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input
          state.source.evm state.remaining =
        .ok ((targetFinal, output), traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.run code state = .ok final ∧
        final.source.evm = targetFinal ∧
        final.remaining = traceFinal := by
  rw [runBody_toCfg hType] at hRun
  cases hSource : ObserverSemantics.Code.run code state with
  | error err =>
      simp [hSource, Except.map] at hRun
  | ok final =>
      simp [hSource, Except.map] at hRun
      rcases hRun with ⟨hEVM, hTrace⟩
      exact ⟨final, rfl, hEVM, hTrace⟩

/--
Backward adequacy for a compiled Structured condition.

The generated body and its ordinary condition pop recover both the source
branch decision and the exact remaining observer suffix.
-/
theorem runCondition_of_runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {state : ObserverSemantics.State transcript}
    {targetAfterCode targetFinal : EVMState}
    {traceFinal : Trace} {cond : Bool}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input
          state.source.evm state.remaining =
        .ok ((targetAfterCode, output), traceFinal))
    (hPop :
      Structured.Code.popCondition targetAfterCode =
        .ok (targetFinal, cond)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.runCondition code state =
          .ok (final, cond) ∧
        final.source.evm = targetFinal ∧
        final.remaining = traceFinal := by
  obtain ⟨afterCode, hCode, hEVM, hTrace⟩ :=
    run_of_runBody_toCfg hType hBody
  unfold Structured.Code.popCondition
    EffectSemantics.Code.popCondition at hPop
  cases hTargetPop : targetAfterCode.stack.pop with
  | none =>
      simp [hTargetPop] at hPop
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [hTargetPop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      let final : ObserverSemantics.State transcript :=
        afterCode.withSource
          (afterCode.source.withEVM
            { targetAfterCode with stack := stack })
      refine ⟨final, ?_, ?_, ?_⟩
      · unfold ObserverSemantics.Code.runCondition
          EffectSemantics.Code.runCondition
        have hEffectCode :
            EffectSemantics.Code.run
                (ObserverSemantics.stateModel transcript)
                (ObserverSemantics.handler transcript) code state =
              .ok afterCode :=
          hCode
        rw [hEffectCode]
        simp only [Bind.bind, Except.bind]
        unfold EffectSemantics.Code.popCondition
        simp only [ObserverSemantics.stateModel_evm,
          ObserverSemantics.stateModel_withEVM]
        rw [hEVM, hTargetPop]
      · simp [final]
      · simpa [final] using hTrace

end Code

namespace StateRel

/--
Backward-execution state relation at a checked symbolic stack shape.

`StateRel` relates the runtime data and realizes ghost return frames. The
additional source-facing length fact says every symbolic slot is backed by a
real source stack value, so target execution cannot satisfy a source operand
by reading a hidden return token or caller suffix.
-/
structure At {transcript : Trace}
    (shape : TypedCfg.Shape)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (target : EVMState) (trace : Trace) : Prop where
  rel : StateRel source tokens target trace
  sourceStack :
    TypedCfgCompiler.Shape.sourceLength shape ≤
      source.source.evm.stack.length

theorem initial (state : EVMState) (transcript : Trace) :
    StateRel
      (transcript := transcript)
      { source := RunState.initial state }
      [] state transcript := by
  exact
    ⟨TypedCfgPreservation.StateRel.initial state,
      by simp [Simulation.ResourceReplay.State.remaining]⟩

theorem At.initial (state : EVMState) (transcript : Trace) :
    At TypedCfg.Shape.caller
      (transcript := transcript)
      { source := RunState.initial state }
      [] state transcript := by
  exact
    ⟨ObserverPreservation.StateRel.initial state transcript,
      by
        simp [TypedCfgCompiler.Shape.sourceLength,
          TypedCfgCompiler.Shape.sourceView,
          TypedCfg.Shape.caller, TypedCfg.Shape.length,
          TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?]⟩

theorem targetStack_eq_source_append_hidden
    {transcript : Trace} {shape : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel : At shape source tokens target trace) :
    ∃ hidden : EvmYul.Stack Word,
      target.stack = source.source.evm.stack ++ hidden := by
  rcases hRel.rel.1 with ⟨realized, hRealize, hSame⟩
  have hAppend :=
    TypedCfgPreservation.realizeStack_append_prefix
      source.source.evm.stack [] source.source.returns tokens
  cases hHidden :
      TypedCfgPreservation.realizeStack
        [] source.source.returns tokens with
  | none =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
  | some hidden =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
      exact
        ⟨hidden,
          by simpa using Assembly.SameRuntimeData.stack_eq hSame⟩

/--
Observer-aware terminal execution lifts the ordinary frame-realization theorem;
terminal operations do not consume resource observations.
-/
theorem terminal
    {transcript : Trace} {kind : Assembly.HaltKind}
    {source : ObserverSemantics.State transcript}
    {sourceFinal target : EVMState}
    {tokens : List Word} {trace : Trace}
    (hRel : StateRel source tokens target trace)
    (hStep :
      Structured.Terminal.step kind source.source.evm =
        .ok sourceFinal) :
    ∃ targetFinal,
      Structured.Terminal.step kind target = .ok targetFinal ∧
        StateRel
          (source.withSource
            (source.source.withEVM sourceFinal))
          tokens targetFinal trace := by
  obtain ⟨targetFinal, hTargetStep, hFinalRel⟩ :=
    TypedCfgPreservation.StateRel.terminal hRel.1 hStep
  exact
    ⟨targetFinal, hTargetStep, hFinalRel,
      by simpa using hRel.2⟩

theorem popCondition
    {transcript : Trace}
    {source final : ObserverSemantics.State transcript}
    {cond : Bool} {tokens : List Word}
    {target : EVMState} {trace : Trace}
    (hPop :
      EffectSemantics.Code.popCondition
          (ObserverSemantics.stateModel transcript) source =
        .ok (final, cond))
    (hRel : StateRel source tokens target trace) :
    ∃ targetFinal,
      Structured.Code.popCondition target =
          .ok (targetFinal, cond) ∧
      StateRel final tokens targetFinal trace := by
  unfold EffectSemantics.Code.popCondition at hPop
  simp only [ObserverSemantics.stateModel_evm,
    ObserverSemantics.stateModel_withEVM] at hPop
  cases hSourcePop : source.source.evm.stack.pop with
  | none =>
      simp [hSourcePop] at hPop
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [hSourcePop] at hPop
      rcases hPop with ⟨hFinal, hCond⟩
      subst final
      subst cond
      obtain ⟨targetFinal, hTargetPop, hFinalRel⟩ :=
        TypedCfgPreservation.StateRel.popCondition
          hRel.1 hSourcePop
      exact
        ⟨targetFinal, hTargetPop,
          hFinalRel,
          by simpa using hRel.2⟩

/--
Frame-safe observer execution of straight-line Structured code is preserved by
the existing Structured-to-TypedCfg lowering. Ghost return frames are realized
only inside this adjacent pass proof; the public relation exposes no generated
tokens or replay certificate.
-/
theorem runCode
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe code)
    (hRun : ObserverSemantics.Code.run code source = .ok final)
    (hRel : StateRel source tokens target trace) :
    ∃ targetFinal traceFinal,
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetFinal, output), traceFinal) ∧
      StateRel final tokens targetFinal traceFinal := by
  rcases hRel with
    ⟨⟨realized, hRealize, hSame⟩, hTrace⟩
  have hReturns :
      final.source.returns = source.source.returns :=
    ObserverSemantics.Code.run_returns_eq hRun
  have hAppend :=
    TypedCfgPreservation.realizeStack_append_prefix
      source.source.evm.stack [] source.source.returns tokens
  cases hHidden :
      TypedCfgPreservation.realizeStack
        [] source.source.returns tokens with
  | none =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
  | some hidden =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
      have hFramed :
          ObserverSemantics.Code.run code
              (ObserverSemantics.Code.withHidden source hidden) =
            .ok (ObserverSemantics.Code.withHidden final hidden) :=
        hFrameSafe transcript source final hidden hRun
      let targetState : ObserverSemantics.State transcript :=
        source.withSource (source.source.withEVM target)
      have hReplay :
          ReplayStateRel
            (ObserverSemantics.Code.withHidden source hidden)
            targetState := by
        refine ⟨rfl, ?_, ?_⟩
        · rfl
        · simpa [targetState, ObserverSemantics.Code.withHidden,
              RunState.withEVM] using
            Assembly.SameRuntimeData.symm hSame
      obtain
          ⟨targetReplayFinal, hTargetRun, hFinalReplay⟩ :=
        Code.run_of_rel hReplay hFramed
      have hBody :=
        Code.runBody_toCfg
          (state := targetState) hType
      rw [hTargetRun] at hBody
      refine
        ⟨targetReplayFinal.source.evm,
          targetReplayFinal.remaining, ?_, ?_⟩
      · simpa [targetState, hTrace, Except.map] using hBody
      · refine ⟨?_, ?_⟩
        · refine
            ⟨final.source.evm.stack ++ hidden, ?_, ?_⟩
          · have hFinalAppend :=
              TypedCfgPreservation.realizeStack_append_prefix
                final.source.evm.stack [] final.source.returns tokens
            simpa [hReturns, hHidden] using hFinalAppend
          · simpa [ObserverSemantics.Code.withHidden,
                RunState.withEVM] using
              Assembly.SameRuntimeData.symm hFinalReplay.source.2
        · simpa using
            ReplayStateRel.remaining_eq hFinalReplay

/--
Observer-aware condition evaluation factors through the compiled TypedCfg body
and the shared stack-pop relation. The target trace is changed only by the
compiled body and remains exact through branch selection.
-/
theorem runCondition
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source final : ObserverSemantics.State transcript}
    {cond : Bool} {tokens : List Word}
    {target : EVMState} {trace : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe code)
    (hRun :
      ObserverSemantics.Code.runCondition code source =
        .ok (final, cond))
    (hRel : StateRel source tokens target trace) :
    ∃ targetAfterCode targetFinal traceFinal,
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetAfterCode, output), traceFinal) ∧
      Structured.Code.popCondition targetAfterCode =
          .ok (targetFinal, cond) ∧
      StateRel final tokens targetFinal traceFinal := by
  unfold ObserverSemantics.Code.runCondition
    EffectSemantics.Code.runCondition at hRun
  cases hCode :
      EffectSemantics.Code.run
        (ObserverSemantics.stateModel transcript)
        (ObserverSemantics.handler transcript) code source with
  | error err =>
      rw [hCode] at hRun
      contradiction
  | ok afterCode =>
      rw [hCode] at hRun
      have hObserverCode :
          ObserverSemantics.Code.run code source =
            .ok afterCode :=
        hCode
      obtain
          ⟨targetAfterCode, traceFinal,
            hTargetCode, hAfterCodeRel⟩ :=
        runCode hType hFrameSafe hObserverCode hRel
      obtain ⟨targetFinal, hTargetPop, hFinalRel⟩ :=
        popCondition hRun hAfterCodeRel
      exact
        ⟨targetAfterCode, targetFinal, traceFinal,
          hTargetCode, hTargetPop, hFinalRel⟩

end StateRel

namespace BlocksInProgram

theorem step_of_run
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {block : TypedCfg.Block} {state : EVMState}
    {trace trace' : Trace} {outcome : TypedCfg.Outcome}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result program)
    (hMem : block ∈ result.blocks)
    (hRun :
      TypedCfg.ObserverSemantics.Block.run block state trace =
        .ok (outcome, trace')) :
    TypedCfg.ObserverSemantics.Program.step
        program block.label state trace =
      .ok (outcome, trace') := by
  unfold TypedCfg.ObserverSemantics.Program.step
  rw [hBlocks block hMem]
  exact hRun

theorem eventually_of_run
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {block : TypedCfg.Block} {state : EVMState}
    {trace trace' : Trace} {outcome : TypedCfg.Outcome}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result program)
    (hMem : block ∈ result.blocks)
    (hRun :
      TypedCfg.ObserverSemantics.Block.run block state trace =
        .ok (outcome, trace')) :
    TypedCfg.ObserverSemantics.Program.Eventually
      program block.label state trace outcome trace' := by
  refine ⟨1, ?_⟩
  exact
    TypedCfg.ObserverSemantics.Program.runN_one_of_step
      (step_of_run hBlocks hMem hRun)

theorem step_pop_jump
    {transcript : Trace}
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {stack : EvmYul.Stack Word} {value : Word}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result program)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump regular } ∈ result.blocks)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hRel : StateRel source tokens target trace)
    (hPop : source.source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.step
          program entry target trace =
        .ok (.jump regular targetFinal, trace) ∧
      StateRel
        (source.withSource
          (source.source.withEVM
            { source.source.evm with stack := stack }))
        tokens targetFinal trace := by
  rcases
      TypedCfgPreservation.StateRel.pop
        (shape := input) hRel.1 hPop with
    ⟨targetFinal, hRunPop, hFinalRel⟩
  have hPlainRunAt :
      TypedCfg.Instr.runAt .pop input target =
        .ok (targetFinal, output) := by
    unfold TypedCfg.Instr.runAt
    rw [hType]
    simp [hRunPop, Bind.bind, Except.bind]
  have hObserverRunAt :
      TypedCfg.ObserverSemantics.Instr.runAt
          .pop input target trace =
        .ok ((targetFinal, output), trace) := by
    rw [TypedCfg.ObserverSemantics.Instr.runAt_of_observer?_eq_none
      (by rfl), hPlainRunAt]
    rfl
  refine
    ⟨targetFinal, ?_,
      ⟨by simpa using hFinalRel, hRel.2⟩⟩
  apply step_of_run hBlocks hMem
  unfold TypedCfg.ObserverSemantics.Block.run
  rw [TypedCfg.ObserverSemantics.Block.runBody_cons,
    hObserverRunAt]
  simp [TypedCfg.ObserverSemantics.Block.runBody_nil,
    TypedCfg.Block.runTerm, Bind.bind, Except.bind]

theorem eventually_pop_jump
    {transcript : Trace}
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {stack : EvmYul.Stack Word} {value : Word}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result program)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump regular } ∈ result.blocks)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hRel : StateRel source tokens target trace)
    (hPop : source.source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.Eventually program
        entry target trace (.jump regular targetFinal) trace ∧
      StateRel
        (source.withSource
          (source.source.withEVM
            { source.source.evm with stack := stack }))
        tokens targetFinal trace := by
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    step_pop_jump hBlocks hMem hType hRel hPop
  exact
    ⟨targetFinal,
      ⟨1, TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep⟩,
      hFinalRel⟩

end BlocksInProgram

def RegularExecution (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry regular : Assembly.Label)
    (initial : EVMState) (initialTrace : Trace)
    (final : EVMState) (finalTrace : Trace) : Prop :=
  ∃ output : TypedCfg.Shape,
    result.fallthrough? = some output ∧
      TypedCfg.ObserverSemantics.Program.Eventually
        program entry initial initialTrace
          (.jump regular final) finalTrace

def RegularPreserves {transcript : Trace}
    (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry regular : Assembly.Label)
    (source final : ObserverSemantics.State transcript)
    (tokens : List Word) : Prop :=
  ∀ target trace,
    StateRel source tokens target trace →
      ∃ targetFinal traceFinal,
        RegularExecution result program entry regular
          target trace targetFinal traceFinal ∧
        StateRel final tokens targetFinal traceFinal

namespace RegularPreserves

theorem append
    {transcript : Trace}
    {left right : TypedCfgCompiler.Result}
    {program : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {source afterLeft final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hLeft :
      RegularPreserves left program entry middle
        source afterLeft tokens)
    (hRight :
      RegularPreserves right program middle regular
        afterLeft final tokens) :
    RegularPreserves (left.append right) program entry regular
      source final tokens := by
  intro target trace hRel
  obtain
      ⟨afterLeftTarget, afterLeftTrace,
        ⟨leftOutput, hLeftFallthrough, hLeftEventually⟩,
        hAfterLeftRel⟩ :=
    hLeft target trace hRel
  obtain
      ⟨finalTarget, finalTrace,
        ⟨rightOutput, hRightFallthrough, hRightEventually⟩,
        hFinalRel⟩ :=
    hRight afterLeftTarget afterLeftTrace hAfterLeftRel
  refine
    ⟨finalTarget, finalTrace,
      ⟨rightOutput, ?_, ?_⟩, hFinalRel⟩
  · simp [TypedCfgCompiler.Result.append, hRightFallthrough]
  · exact
      TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
        hLeftEventually hRightEventually

end RegularPreserves

namespace OutcomeSimulation

abbrev Continuations :=
  TypedCfgPreservation.OutcomeSimulation.Continuations

def HaltStateRel {transcript : Trace}
    (source : ObserverSemantics.State transcript)
    (target : EVMState) (trace : Trace) : Prop :=
  ∃ tokens, StateRel source tokens target trace

def Rel {transcript : Trace}
    (continuations : Continuations) (tokens : List Word)
    (source : ObserverSemantics.Outcome (transcript := transcript))
    (target : TypedCfg.Outcome) (trace : Trace) : Prop :=
  match source.mode, target with
  | .regular, .jump label target =>
      label = continuations.regular ∧
        StateRel source.state tokens target trace
  | .brk, .jump label target =>
      continuations.breakLabel? = some label ∧
        StateRel source.state tokens target trace
  | .cont, .jump label target =>
      continuations.continueLabel? = some label ∧
        StateRel source.state tokens target trace
  | .leave, .jump label target =>
      continuations.leaveLabel? = some label ∧
        StateRel source.state tokens target trace
  | .halt kind, .halt targetKind target =>
      targetKind = kind ∧
        ∃ targetFinal,
          Structured.Terminal.step kind target = .ok targetFinal ∧
            HaltStateRel source.state targetFinal trace
  | _, _ => False

namespace Rel

theorem regular_iff
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {label : Assembly.Label} {target : EVMState} {trace : Trace} :
    Rel continuations tokens (Structured.OutcomeT.regular source)
        (.jump label target) trace ↔
      label = continuations.regular ∧
        StateRel source tokens target trace :=
  Iff.rfl

theorem brk_iff
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {label : Assembly.Label} {target : EVMState} {trace : Trace} :
    Rel continuations tokens (Structured.OutcomeT.brk source)
        (.jump label target) trace ↔
      continuations.breakLabel? = some label ∧
        StateRel source tokens target trace :=
  Iff.rfl

theorem cont_iff
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {label : Assembly.Label} {target : EVMState} {trace : Trace} :
    Rel continuations tokens (Structured.OutcomeT.cont source)
        (.jump label target) trace ↔
      continuations.continueLabel? = some label ∧
        StateRel source tokens target trace :=
  Iff.rfl

theorem leave_iff
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {label : Assembly.Label} {target : EVMState} {trace : Trace} :
    Rel continuations tokens (Structured.OutcomeT.leave source)
        (.jump label target) trace ↔
      continuations.leaveLabel? = some label ∧
        StateRel source tokens target trace :=
  Iff.rfl

theorem halt_iff
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {kind targetKind : Assembly.HaltKind}
    {target : EVMState} {trace : Trace} :
    Rel continuations tokens (Structured.OutcomeT.halt kind source)
        (.halt targetKind target) trace ↔
      targetKind = kind ∧
        ∃ targetFinal,
          Structured.Terminal.step kind target = .ok targetFinal ∧
            HaltStateRel source targetFinal trace :=
  Iff.rfl

theorem regular_elim
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      Rel continuations tokens
        (Structured.OutcomeT.regular source) targetOutcome trace) :
    ∃ target,
      targetOutcome = .jump continuations.regular target ∧
        StateRel source tokens target trace := by
  cases targetOutcome with
  | jump label target =>
      rcases regular_iff.mp hRel with ⟨rfl, hState⟩
      exact ⟨target, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem brk_elim
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      Rel continuations tokens
        (Structured.OutcomeT.brk source) targetOutcome trace) :
    ∃ label target,
      continuations.breakLabel? = some label ∧
        targetOutcome = .jump label target ∧
        StateRel source tokens target trace := by
  cases targetOutcome with
  | jump label target =>
      rcases brk_iff.mp hRel with ⟨hLabel, hState⟩
      exact ⟨label, target, hLabel, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem cont_elim
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      Rel continuations tokens
        (Structured.OutcomeT.cont source) targetOutcome trace) :
    ∃ label target,
      continuations.continueLabel? = some label ∧
        targetOutcome = .jump label target ∧
        StateRel source tokens target trace := by
  cases targetOutcome with
  | jump label target =>
      rcases cont_iff.mp hRel with ⟨hLabel, hState⟩
      exact ⟨label, target, hLabel, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem leave_elim
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      Rel continuations tokens
        (Structured.OutcomeT.leave source) targetOutcome trace) :
    ∃ label target,
      continuations.leaveLabel? = some label ∧
        targetOutcome = .jump label target ∧
        StateRel source tokens target trace := by
  cases targetOutcome with
  | jump label target =>
      rcases leave_iff.mp hRel with ⟨hLabel, hState⟩
      exact ⟨label, target, hLabel, rfl, hState⟩
  | fallthrough _ | returnDispatch _ | halt _ _ | invalid _ =>
      exact False.elim hRel

theorem halt_elim
    {transcript : Trace} {continuations : Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      Rel continuations tokens
        (Structured.OutcomeT.halt kind source) targetOutcome trace) :
    ∃ target targetFinal,
      targetOutcome = .halt kind target ∧
        Structured.Terminal.step kind target = .ok targetFinal ∧
        HaltStateRel source targetFinal trace := by
  cases targetOutcome with
  | halt targetKind target =>
      rcases halt_iff.mp hRel with
        ⟨rfl, targetFinal, hStep, hState⟩
      exact ⟨target, targetFinal, rfl, hStep, hState⟩
  | fallthrough _ | jump _ _ | returnDispatch _ | invalid _ =>
      exact False.elim hRel

end Rel

def Path {transcript : Trace}
    (program : TypedCfg.Program) (entry : Assembly.Label)
    (continuations : Continuations)
    (source : ObserverSemantics.State transcript)
    (outcome : ObserverSemantics.Outcome (transcript := transcript))
    (tokens : List Word) : Prop :=
  ∀ target trace,
    StateRel source tokens target trace →
      ∃ targetOutcome traceFinal,
        TypedCfg.ObserverSemantics.Program.Eventually
          program entry target trace targetOutcome traceFinal ∧
        Rel continuations tokens outcome targetOutcome traceFinal

def PathPreserves {transcript : Trace}
    (program : TypedCfg.Program) (entry regular : Assembly.Label)
    (source final : ObserverSemantics.State transcript)
    (tokens : List Word) : Prop :=
  ∀ target trace,
    StateRel source tokens target trace →
      ∃ targetFinal traceFinal,
        TypedCfg.ObserverSemantics.Program.Eventually
          program entry target trace
            (.jump regular targetFinal) traceFinal ∧
        StateRel final tokens targetFinal traceFinal

namespace Path

theorem to_regular
    {transcript : Trace} {program : TypedCfg.Program}
    {entry : Assembly.Label} {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hPath :
      Path program entry continuations source
        (Structured.OutcomeT.regular final) tokens) :
    PathPreserves program entry continuations.regular
      source final tokens := by
  intro target trace hRel
  rcases hPath target trace hRel with
    ⟨targetOutcome, traceFinal, hEventually, hOutcomeRel⟩
  rcases Rel.regular_elim hOutcomeRel with
    ⟨targetFinal, rfl, hFinalRel⟩
  exact ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩

theorem to_brk
    {transcript : Trace} {program : TypedCfg.Program}
    {entry targetLabel : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : continuations.breakLabel? = some targetLabel)
    (hPath :
      Path program entry continuations source
        (Structured.OutcomeT.brk final) tokens) :
    PathPreserves program entry targetLabel source final tokens := by
  intro target trace hRel
  rcases hPath target trace hRel with
    ⟨targetOutcome, traceFinal, hEventually, hOutcomeRel⟩
  rcases Rel.brk_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  rw [hTarget] at hLabel
  cases hLabel
  exact ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩

theorem to_cont
    {transcript : Trace} {program : TypedCfg.Program}
    {entry targetLabel : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : continuations.continueLabel? = some targetLabel)
    (hPath :
      Path program entry continuations source
        (Structured.OutcomeT.cont final) tokens) :
    PathPreserves program entry targetLabel source final tokens := by
  intro target trace hRel
  rcases hPath target trace hRel with
    ⟨targetOutcome, traceFinal, hEventually, hOutcomeRel⟩
  rcases Rel.cont_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  rw [hTarget] at hLabel
  cases hLabel
  exact ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩

theorem to_leave
    {transcript : Trace} {program : TypedCfg.Program}
    {entry targetLabel : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : continuations.leaveLabel? = some targetLabel)
    (hPath :
      Path program entry continuations source
        (Structured.OutcomeT.leave final) tokens) :
    PathPreserves program entry targetLabel source final tokens := by
  intro target trace hRel
  rcases hPath target trace hRel with
    ⟨targetOutcome, traceFinal, hEventually, hOutcomeRel⟩
  rcases Rel.leave_elim hOutcomeRel with
    ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩
  rw [hTarget] at hLabel
  cases hLabel
  exact ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩

theorem regular_of_path
    {transcript : Trace} {program : TypedCfg.Program}
    {entry regular : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hRegular : continuations.regular = regular)
    (hPath :
      PathPreserves program entry regular source final tokens) :
    Path program entry continuations source
      (Structured.OutcomeT.regular final) tokens := by
  intro target trace hRel
  obtain
      ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩ :=
    hPath target trace hRel
  exact
    ⟨.jump regular targetFinal, traceFinal, hEventually,
      Rel.regular_iff.mpr ⟨hRegular.symm, hFinalRel⟩⟩

theorem bind_jump
    {transcript : Trace} {program : TypedCfg.Program}
    {entry next : Assembly.Label}
    {continuations : Continuations}
    {source middle : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    (hFirst :
      PathPreserves program entry next source middle tokens)
    (hNext :
      Path program next continuations middle outcome tokens) :
    Path program entry continuations source outcome tokens := by
  intro target trace hRel
  obtain
      ⟨targetMiddle, middleTrace,
        hFirstEventually, hMiddleRel⟩ :=
    hFirst target trace hRel
  obtain
      ⟨targetOutcome, finalTrace,
        hNextEventually, hOutcomeRel⟩ :=
    hNext targetMiddle middleTrace hMiddleRel
  exact
    ⟨targetOutcome, finalTrace,
      TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
        hFirstEventually hNextEventually,
      hOutcomeRel⟩

theorem transport_brk
    {transcript : Trace} {program : TypedCfg.Program}
    {entry : Assembly.Label} {left right : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hBreak : left.breakLabel? = right.breakLabel?)
    (hPath :
      Path program entry left source
        (Structured.OutcomeT.brk final) tokens) :
    Path program entry right source
      (Structured.OutcomeT.brk final) tokens := by
  intro target trace hRel
  obtain
      ⟨targetOutcome, traceFinal,
        hEventually, hOutcomeRel⟩ :=
    hPath target trace hRel
  obtain
      ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩ :=
    Rel.brk_elim hOutcomeRel
  exact
    ⟨.jump label targetFinal, traceFinal, hEventually,
      Rel.brk_iff.mpr ⟨hBreak ▸ hLabel, hFinalRel⟩⟩

theorem transport_cont
    {transcript : Trace} {program : TypedCfg.Program}
    {entry : Assembly.Label} {left right : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hContinue :
      left.continueLabel? = right.continueLabel?)
    (hPath :
      Path program entry left source
        (Structured.OutcomeT.cont final) tokens) :
    Path program entry right source
      (Structured.OutcomeT.cont final) tokens := by
  intro target trace hRel
  obtain
      ⟨targetOutcome, traceFinal,
        hEventually, hOutcomeRel⟩ :=
    hPath target trace hRel
  obtain
      ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩ :=
    Rel.cont_elim hOutcomeRel
  exact
    ⟨.jump label targetFinal, traceFinal, hEventually,
      Rel.cont_iff.mpr ⟨hContinue ▸ hLabel, hFinalRel⟩⟩

theorem transport_leave
    {transcript : Trace} {program : TypedCfg.Program}
    {entry : Assembly.Label} {left right : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hLeave : left.leaveLabel? = right.leaveLabel?)
    (hPath :
      Path program entry left source
        (Structured.OutcomeT.leave final) tokens) :
    Path program entry right source
      (Structured.OutcomeT.leave final) tokens := by
  intro target trace hRel
  obtain
      ⟨targetOutcome, traceFinal,
        hEventually, hOutcomeRel⟩ :=
    hPath target trace hRel
  obtain
      ⟨label, targetFinal, hLabel, rfl, hFinalRel⟩ :=
    Rel.leave_elim hOutcomeRel
  exact
    ⟨.jump label targetFinal, traceFinal, hEventually,
      Rel.leave_iff.mpr ⟨hLeave ▸ hLabel, hFinalRel⟩⟩

theorem transport_halt
    {transcript : Trace} {program : TypedCfg.Program}
    {entry : Assembly.Label} {left right : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word} {kind : Assembly.HaltKind}
    (hPath :
      Path program entry left source
        (Structured.OutcomeT.halt kind final) tokens) :
    Path program entry right source
      (Structured.OutcomeT.halt kind final) tokens := by
  intro target trace hRel
  obtain
      ⟨targetOutcome, traceFinal,
        hEventually, hOutcomeRel⟩ :=
    hPath target trace hRel
  obtain
      ⟨targetBefore, targetFinal, rfl,
        hStep, hFinalRel⟩ :=
    Rel.halt_elim hOutcomeRel
  exact
    ⟨.halt kind targetBefore, traceFinal, hEventually,
      Rel.halt_iff.mpr
        ⟨rfl, targetFinal, hStep, hFinalRel⟩⟩

end Path

def Preserves {transcript : Trace}
    (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry : Assembly.Label)
    (continuations : Continuations)
    (source : ObserverSemantics.State transcript)
    (outcome : ObserverSemantics.Outcome (transcript := transcript))
    (tokens : List Word) : Prop :=
  Path program entry continuations source outcome tokens ∧
    (outcome.mode = .regular →
      ∃ output, result.fallthrough? = some output)

namespace Preserves

theorem fallthrough_of_regular
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hPreserves :
      Preserves result program entry continuations source
        (Structured.OutcomeT.regular final) tokens) :
    ∃ output, result.fallthrough? = some output :=
  hPreserves.2 rfl

theorem to_regular_path
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hPreserves :
      Preserves result program entry continuations source
        (Structured.OutcomeT.regular final) tokens) :
    PathPreserves program entry continuations.regular
      source final tokens := by
  intro target trace hRel
  obtain
      ⟨targetOutcome, traceFinal,
        hEventually, hOutcomeRel⟩ :=
    hPreserves.1 target trace hRel
  obtain ⟨targetFinal, rfl, hFinalRel⟩ :=
    Rel.regular_elim hOutcomeRel
  exact
    ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩

theorem of_path_of_nonregular
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {program : TypedCfg.Program} {entry : Assembly.Label}
    {continuations : Continuations}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    (hNonregular : outcome.mode ≠ .regular)
    (hPath :
      Path program entry continuations source outcome tokens) :
    Preserves result program entry continuations source outcome tokens := by
  exact
    ⟨hPath,
      by
        intro hRegular
        exact False.elim (hNonregular hRegular)⟩

theorem of_regular
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {program : TypedCfg.Program} {entry regular : Assembly.Label}
    {continuations : Continuations}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hRegular : continuations.regular = regular)
    (hFallthrough :
      ∃ output, result.fallthrough? = some output)
    (hPreserves :
      RegularPreserves result program entry regular
        source final tokens) :
    Preserves result program entry continuations source
      (Structured.OutcomeT.regular final) tokens := by
  refine ⟨?_, ?_⟩
  · apply Path.regular_of_path hRegular
    intro target trace hRel
    obtain
        ⟨targetFinal, traceFinal,
          ⟨_output, _hFallthrough, hEventually⟩,
          hFinalRel⟩ :=
      hPreserves target trace hRel
    exact
      ⟨targetFinal, traceFinal, hEventually, hFinalRel⟩
  · intro _hMode
    exact hFallthrough

end Preserves

end OutcomeSimulation

namespace Code

/--
A generated conditional block follows the observer-aware Structured condition,
selects the same branch, and preserves the adjacent-pass state relation.
-/
theorem run_jumpi_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source final : ObserverSemantics.State transcript}
    {cond : Bool} {tokens : List Word}
    {targetState : EVMState} {trace : Trace}
    {jumpTarget fallthrough : Assembly.Label}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe code)
    (hCond :
      ObserverSemantics.Code.runCondition code source =
        .ok (final, cond))
    (hRel : StateRel source tokens targetState trace) :
    ∃ targetFinal traceFinal,
      TypedCfg.ObserverSemantics.Block.run
          { label := jumpTarget
            input := input
            body := TypedCfgCompiler.Code.toCfg code
            output := output
            term := .jumpi jumpTarget fallthrough }
          targetState trace =
        .ok
          (.jump (if cond then jumpTarget else fallthrough) targetFinal,
            traceFinal) ∧
      StateRel final tokens targetFinal traceFinal := by
  obtain
      ⟨targetAfterCode, targetFinal, traceFinal,
        hTargetCode, hTargetPop, hFinalRel⟩ :=
    StateRel.runCondition
      hType hFrameSafe hCond hRel
  refine ⟨targetFinal, traceFinal, ?_, hFinalRel⟩
  unfold TypedCfg.ObserverSemantics.Block.run
  rw [hTargetCode]
  simp only [Bind.bind, Except.bind, ↓reduceIte]
  unfold TypedCfg.Block.runTerm
  unfold Structured.Code.popCondition
    EffectSemantics.Code.popCondition at hTargetPop
  cases hStack : targetAfterCode.stack.pop with
  | none =>
      simp [hStack] at hTargetPop
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [hStack] at hTargetPop
      rcases hTargetPop with ⟨hFinal, hBool⟩
      subst targetFinal
      subst cond
      by_cases hZero : value = EvmYul.UInt256.ofNat 0
      · have hBne :
            (value != EvmYul.UInt256.ofNat 0) = false := by
          calc
            (value != EvmYul.UInt256.ofNat 0) =
                (EvmYul.UInt256.ofNat 0 !=
                  EvmYul.UInt256.ofNat 0) := by rw [hZero]
            _ = false :=
              TypedCfg.Preservation.uint256_bne_zero_self
        rw [hBne]
        simp [hStack, hZero]
      · have hBne :
            (value != EvmYul.UInt256.ofNat 0) = true :=
          TypedCfg.Preservation.uint256_bne_zero_of_ne value hZero
        rw [hBne]
        simp [hStack, hZero]

end Code

namespace Stmt

/--
Straight-line statement compilation preserves observer replay through the
existing compiler block and the shared effectful CFG path semantics.
-/
theorem regular_code_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe code)
    (hRun : ObserverSemantics.Code.run code source = .ok final) :
    RegularPreserves result cfg entry regular source final tokens := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? code input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
      cases hCompile
      intro target trace hRel
      obtain
          ⟨targetFinal, traceFinal,
            hTargetBody, hFinalRel⟩ :=
        StateRel.runCode hType hFrameSafe hRun hRel
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hBlockRun :
          TypedCfg.ObserverSemantics.Block.run
              generated target trace =
            .ok (.jump regular targetFinal, traceFinal) := by
        unfold TypedCfg.ObserverSemantics.Block.run
        rw [hTargetBody]
        simp [generated, TypedCfg.Block.runTerm,
          Bind.bind, Except.bind]
      have hEventually :=
        BlocksInProgram.eventually_of_run
          hBlocks (block := generated) (by simp [generated]) hBlockRun
      exact
        ⟨targetFinal, traceFinal,
          ⟨output, rfl, hEventually⟩, hFinalRel⟩

/--
Straight-line observer statements satisfy the uniform outcome-indexed
certificate used by recursive block composition.
-/
theorem outcome_code_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe code)
    (hRun : ObserverSemantics.Code.run code source = .ok final) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source (Structured.OutcomeT.regular final) tokens := by
  have hPreserves :=
    regular_code_of_compileStmtFuel?
      (tokens := tokens) hCompile hBlocks hFrameSafe hRun
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? code input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
      cases hCompile
      exact
        OutcomeSimulation.Preserves.of_regular
          rfl ⟨output, rfl⟩ hPreserves

/--
When an observer-aware condition is false, the generated conditional head
reaches the regular continuation without executing the compiled body.
-/
theorem regular_if_false_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe cond)
    (hCond :
      ObserverSemantics.Code.runCondition cond source =
        .ok (final, false)) :
    RegularPreserves result cfg entry regular source final tokens := by
  obtain
      ⟨output, _condition, _bodyResult,
        hType, _hSource, _hHead, _hBody, _hRequire, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  intro target trace hRel
  obtain
      ⟨targetFinal, traceFinal,
        hBlockRun, hFinalRel⟩ :=
    Code.run_jumpi_toCfg
      (jumpTarget := LabelSupply.label supply 0)
      (fallthrough := regular)
      hType hFrameSafe hCond hRel
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term :=
        .jumpi (LabelSupply.label supply 0) regular }
  have hEventually :=
    BlocksInProgram.eventually_of_run
      hBlocks (block := generated)
        (by simp [generated])
        (by simpa [generated] using hBlockRun)
  exact
    ⟨targetFinal, traceFinal,
      ⟨{ output with slots := output.slots.tail },
        rfl, hEventually⟩,
      hFinalRel⟩

/--
The false conditional branch satisfies the uniform observer outcome
certificate.
-/
theorem outcome_if_false_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe cond)
    (hCond :
      ObserverSemantics.Code.runCondition cond source =
        .ok (final, false)) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source (Structured.OutcomeT.regular final) tokens := by
  have hPreserves :=
    regular_if_false_of_compileStmtFuel?
      (tokens := tokens) hCompile hBlocks hFrameSafe hCond
  obtain
      ⟨output, _condition, _bodyResult,
        _hType, _hSource, _hHead, _hBody, _hRequire, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  exact
    OutcomeSimulation.Preserves.of_regular
      rfl
      ⟨{ output with slots := output.slots.tail }, rfl⟩
      hPreserves

/--
Outcome-indexed true-branch preservation composes the generated conditional
head with the recursively compiled observer-aware body path.
-/
theorem outcome_if_true_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterCond : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe cond)
    (hCond :
      ObserverSemantics.Code.runCondition cond source =
        .ok (afterCond, true))
    (hBodyPreserves :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram
          bodyResult globalCalls →
        OutcomeSimulation.Path cfg
          (LabelSupply.label supply 0)
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx regular)
          afterCond outcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source outcome tokens := by
  obtain
      ⟨output, _condition, bodyResult,
        hType, _hSource, _hHead, hBody, _hRequire, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram
        bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram
        bodyResult globalCalls := by
    intro site hMem
    apply hCalls site
    simpa using hMem
  refine ⟨?_, ?_⟩
  · intro target trace hRel
    obtain
        ⟨targetAfterCond, traceAfterCond,
          hBlockRun, hAfterCondRel⟩ :=
      Code.run_jumpi_toCfg
        (jumpTarget := LabelSupply.label supply 0)
        (fallthrough := regular)
        hType hFrameSafe hCond hRel
    let generated : TypedCfg.Block :=
      { label := entry
        input := input
        body := TypedCfgCompiler.Code.toCfg cond
        output := output
        term :=
          .jumpi (LabelSupply.label supply 0) regular }
    have hHeadEventually :=
      BlocksInProgram.eventually_of_run
        hBlocks (block := generated)
          (by simp [generated])
          (by simpa [generated] using hBlockRun)
    obtain
        ⟨targetOutcome, traceFinal,
          hBodyEventually, hOutcomeRel⟩ :=
      hBodyPreserves hBody hBodyBlocks hBodyCalls
        targetAfterCond traceAfterCond hAfterCondRel
    exact
      ⟨targetOutcome, traceFinal,
        TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
          hHeadEventually hBodyEventually,
        hOutcomeRel⟩
  · intro _hRegular
    exact
      ⟨{ output with slots := output.slots.tail }, rfl⟩

theorem outcome_brk_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : ctx.breakLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .brk ctx
        supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
      ctx regular)
      source (Structured.OutcomeT.brk source) tokens := by
  obtain ⟨_hShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_brk
      hTarget hCompile
  apply
    OutcomeSimulation.Preserves.of_path_of_nonregular
      (by intro hMode; cases hMode)
  intro targetState trace hRel
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated targetState trace =
        .ok (.jump target targetState, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hEventually :=
    BlocksInProgram.eventually_of_run
      hBlocks (block := generated)
        (by simp [generated]) hRun
  exact
    ⟨.jump target targetState, trace, hEventually,
      OutcomeSimulation.Rel.brk_iff.mpr
        ⟨hTarget, hRel⟩⟩

theorem outcome_cont_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : ctx.continueLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .cont ctx
        supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
      ctx regular)
      source (Structured.OutcomeT.cont source) tokens := by
  obtain ⟨_hShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_cont
      hTarget hCompile
  apply
    OutcomeSimulation.Preserves.of_path_of_nonregular
      (by intro hMode; cases hMode)
  intro targetState trace hRel
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated targetState trace =
        .ok (.jump target targetState, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hEventually :=
    BlocksInProgram.eventually_of_run
      hBlocks (block := generated)
        (by simp [generated]) hRun
  exact
    ⟨.jump target targetState, trace, hEventually,
      OutcomeSimulation.Rel.cont_iff.mpr
        ⟨hTarget, hRel⟩⟩

theorem outcome_leave_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : ctx.leaveLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .leave ctx
        supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
      ctx regular)
      source (Structured.OutcomeT.leave source) tokens := by
  obtain ⟨_hShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_leave
      hTarget hCompile
  apply
    OutcomeSimulation.Preserves.of_path_of_nonregular
      (by intro hMode; cases hMode)
  intro targetState trace hRel
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated targetState trace =
        .ok (.jump target targetState, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hEventually :=
    BlocksInProgram.eventually_of_run
      hBlocks (block := generated)
        (by simp [generated]) hRun
  exact
    ⟨.jump target targetState, trace, hEventually,
      OutcomeSimulation.Rel.leave_iff.mpr
        ⟨hTarget, hRel⟩⟩

theorem outcome_terminal_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {sourceFinal : EVMState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
        (.terminal kind) ctx supply entry input regular =
      some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hStep :
      Structured.Terminal.step kind source.source.evm =
        .ok sourceFinal) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source
      (Structured.OutcomeT.halt kind
        (source.withSource
          (source.source.withEVM sourceFinal)))
      tokens := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  have hSource :
      TypedCfgCompiler.Shape.requireSourceWords? kind.argCount input =
        some () := by
    cases hCheck :
        TypedCfgCompiler.Shape.requireSourceWords? kind.argCount input with
    | none =>
        simp [hCheck] at hCompile
    | some unit =>
        cases unit
        rfl
  simp only [Bind.bind, Option.bind] at hCompile
  rw [hSource] at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  apply
    OutcomeSimulation.Preserves.of_path_of_nonregular
      (by intro hMode; cases hMode)
  intro target trace hRel
  obtain ⟨targetFinal, hTargetStep, hFinalRel⟩ :=
    StateRel.terminal hRel hStep
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.halt kind target, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hEventually :=
    BlocksInProgram.eventually_of_run
      hBlocks (block := generated)
        (by simp [generated]) hRun
  exact
    ⟨.halt kind target, trace, hEventually,
      OutcomeSimulation.Rel.halt_iff.mpr
        ⟨rfl, targetFinal, hTargetStep, tokens, hFinalRel⟩⟩

end Stmt

namespace Switch

abbrev testOutput :=
  TypedCfgCompilerFacts.Switch.testOutput

abbrev casesEntryLabel :=
  TypedCfgCompilerFacts.Switch.casesEntryLabel

abbrev nextTestLabel :=
  TypedCfgCompilerFacts.Switch.nextTestLabel

theorem testBody_type
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue : Word}
    (hHead : valueShape.slots.head? = some slot) :
    TypedCfg.Block.bodyType?
        [.dup 0, .push caseValue, .prim .eq] valueShape =
      some (testOutput valueShape) :=
  TypedCfgCompilerFacts.Switch.testBody_type hHead

theorem step_test
    {transcript : Trace}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {testLabel caseLabel nextTest : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue value : Word}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {stack : EvmYul.Stack Word}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead : valueShape.slots.head? = some slot)
    (hRel : StateRel source tokens target trace)
    (hPop : source.source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.step
          cfg testLabel target trace =
        .ok
          (.jump
            (if caseValue = value then caseLabel else nextTest)
            targetFinal,
            trace) ∧
      StateRel source tokens targetFinal trace := by
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
      TypedCfgCompilerFacts.Switch.testBody_type
        (caseValue := caseValue) hHead
    simp [TypedCfg.Block.bodyType?, hDupType, hPushType] at hTestType
    exact hTestType
  rcases
      TypedCfgPreservation.StateRel.stackView_of_pop
        hRel.1 hPop with
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
      Assembly.SameRuntimeData targetFinal target := by
    cases target
    simp [targetFinal, afterEq, afterPush, afterDup,
      Assembly.SameRuntimeData, Assembly.eraseRuntimeControl,
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
  have hDupObserver :
      TypedCfg.ObserverSemantics.Instr.runAt
          (.dup 0) valueShape target trace =
        .ok ((afterDup, dupShape), trace) := by
    rw [TypedCfg.ObserverSemantics.Instr.runAt_of_observer?_eq_none
      (by rfl), hDupRun]
    rfl
  have hPushObserver :
      TypedCfg.ObserverSemantics.Instr.runAt
          (.push caseValue) dupShape afterDup trace =
        .ok ((afterPush, pushShape), trace) := by
    rw [TypedCfg.ObserverSemantics.Instr.runAt_of_observer?_eq_none
      (by rfl), hPushRun]
    rfl
  have hEqObserver :
      TypedCfg.ObserverSemantics.Instr.runAt
          (.prim .eq) pushShape afterPush trace =
        .ok ((afterEq, testOutput valueShape), trace) := by
    rw [TypedCfg.ObserverSemantics.Instr.runAt_of_observer?_eq_none
      (by rfl), hEqRun]
    rfl
  have hBodyRun :
      TypedCfg.ObserverSemantics.Block.runBody
          [.dup 0, .push caseValue, .prim .eq]
          valueShape target trace =
        .ok ((afterEq, testOutput valueShape), trace) := by
    rw [TypedCfg.ObserverSemantics.Block.runBody_cons,
      hDupObserver]
    simp only [Bind.bind, Except.bind]
    rw [TypedCfg.ObserverSemantics.Block.runBody_cons,
      hPushObserver]
    simp only [Bind.bind, Except.bind]
    rw [TypedCfg.ObserverSemantics.Block.runBody_cons,
      hEqObserver]
    rfl
  refine
    ⟨targetFinal, ?_,
      ⟨TypedCfgPreservation.StateRel.targetCongr
          hFinalSame hRel.1,
        hRel.2⟩⟩
  apply BlocksInProgram.step_of_run hBlocks hMem
  simp only [TypedCfg.ObserverSemantics.Block.run, hBodyRun,
    Bind.bind, Except.bind, if_pos rfl]
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

theorem eventually_test
    {transcript : Trace}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {testLabel caseLabel nextTest : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue value : Word}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {stack : EvmYul.Stack Word}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead : valueShape.slots.head? = some slot)
    (hRel : StateRel source tokens target trace)
    (hPop : source.source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.Eventually cfg
        testLabel target trace
        (.jump
          (if caseValue = value then caseLabel else nextTest)
          targetFinal)
        trace ∧
      StateRel source tokens targetFinal trace := by
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    step_test hBlocks hMem hHead hRel hPop
  exact
    ⟨targetFinal,
      ⟨1, TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep⟩,
      hFinalRel⟩

theorem outcome_cases_some_of_compileCasesFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    {continuations : OutcomeSimulation.Continuations}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
        base supply idx valueShape bodyShape regular =
      some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody =
        some selected)
    (hCasePath :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (.generated base (2000 + caseIdx))
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram
          bodyResult globalCalls →
        OutcomeSimulation.Path cfg
          (.generated base (2000 + caseIdx)) continuations
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          outcome tokens)
    (hDefaultPath :
      defaultBody = some selected →
        OutcomeSimulation.Path cfg (LabelSupply.label base 1)
          continuations source outcome tokens) :
    OutcomeSimulation.Path cfg (casesEntryLabel base idx cases)
      continuations source outcome tokens := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = some selected := by
            simpa [Structured.Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPath hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
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
              have hRequire :
                  bodyResult.requireFallthrough? bodyShape = some () := by
                cases hRequire :
                    bodyResult.requireFallthrough? bodyShape with
                | none =>
                    simp [hRequire] at hCompile
                | some unit =>
                    cases unit
                    rfl
              simp only [hRequire] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1)
                    valueShape bodyShape regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hBodyBlocks :
                      TypedCfgPreservation.BlocksInProgram
                        bodyResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hTailBlocks :
                      TypedCfgPreservation.BlocksInProgram
                        tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hBodyCalls :
                      TypedCfgPreservation.CallsInProgram
                        bodyResult globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  have hTailCalls :
                      TypedCfgPreservation.CallsInProgram
                        tail globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · have hSelected : body = selected := by
                      simpa [Structured.Switch.select, hEq] using hSelect
                    subst selected
                    intro target trace hRel
                    rcases
                        eventually_test
                          (testLabel :=
                            TypedCfgCompiler.switchTestLabel base idx)
                          (caseLabel := LabelSupply.label base (idx + 2))
                          (nextTest := nextTestLabel base idx rest)
                          (caseValue := caseValue) (value := value)
                          hBlocks (by left) hHead hRel hPop with
                      ⟨targetAfterTest, hTestEventually,
                        hAfterTestRel⟩
                    have hSelectedTest :
                        TypedCfg.ObserverSemantics.Program.Eventually cfg
                          (TypedCfgCompiler.switchTestLabel base idx)
                          target trace
                          (.jump (LabelSupply.label base (idx + 2))
                            targetAfterTest)
                          trace := by
                      simpa [hEq] using hTestEventually
                    rcases
                        BlocksInProgram.eventually_pop_jump
                          (entry := LabelSupply.label base (idx + 2))
                          (regular := .generated base (2000 + idx))
                          (input := valueShape) (output := bodyShape)
                          hBlocks (by simp) hPopType
                          hAfterTestRel hPop with
                      ⟨targetAfterPop, hEntryEventually,
                        hAfterPopRel⟩
                    rcases
                        hCasePath hBody hBodyBlocks hBodyCalls
                          targetAfterPop trace hAfterPopRel with
                      ⟨targetOutcome, traceFinal,
                        hBodyEventually, hOutcomeRel⟩
                    exact
                      ⟨targetOutcome, traceFinal,
                        TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                          hSelectedTest
                          (TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                            hEntryEventually hBodyEventually),
                        hOutcomeRel⟩
                  · have hTailSelect :
                        Structured.Switch.select value rest defaultBody =
                          some selected := by
                      simpa [Structured.Switch.select, hEq] using hSelect
                    have hTailPath :=
                      ih hTail hTailBlocks hTailCalls hTailSelect
                        hCasePath hDefaultPath
                    intro target trace hRel
                    rcases
                        eventually_test
                          (testLabel :=
                            TypedCfgCompiler.switchTestLabel base idx)
                          (caseLabel := LabelSupply.label base (idx + 2))
                          (nextTest := nextTestLabel base idx rest)
                          (caseValue := caseValue) (value := value)
                          hBlocks (by left) hHead hRel hPop with
                      ⟨targetAfterTest, hTestEventually,
                        hAfterTestRel⟩
                    have hSkipped :
                        TypedCfg.ObserverSemantics.Program.Eventually cfg
                          (TypedCfgCompiler.switchTestLabel base idx)
                          target trace
                          (.jump (nextTestLabel base idx rest)
                            targetAfterTest)
                          trace := by
                      simpa [hEq] using hTestEventually
                    rcases
                        hTailPath targetAfterTest trace hAfterTestRel with
                      ⟨targetOutcome, traceFinal,
                        hTailEventually, hOutcomeRel⟩
                    exact
                      ⟨targetOutcome, traceFinal,
                        TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                          hSkipped hTailEventually,
                        hOutcomeRel⟩

theorem outcome_default_some_of_compileDefaultFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {body : Structured.Block} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    {continuations : OutcomeSimulation.Continuations}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hBodyPath :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000)
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram
          bodyResult globalCalls →
        OutcomeSimulation.Path cfg (.generated supply 2000)
          continuations
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          outcome tokens) :
    OutcomeSimulation.Path cfg entry continuations
      source outcome tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
        (supply + 1) (.generated supply 2000)
        bodyShape regular with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?,
        hType, hBody] at hCompile
  | some bodyResult =>
      have hRequire :
          bodyResult.requireFallthrough? bodyShape = some () := by
        cases hRequire :
            bodyResult.requireFallthrough? bodyShape with
        | none =>
            simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?,
              hType, hBody, hRequire] at hCompile
        | some unit =>
            cases unit
            rfl
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?,
        hType, hBody, hRequire] at hCompile
      cases hCompile
      have hBodyBlocks :
          TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hMem]
      have hBodyCalls :
          TypedCfgPreservation.CallsInProgram
            bodyResult globalCalls := by
        intro site hMem
        apply hCalls site
        simpa using hMem
      intro target trace hRel
      rcases
          BlocksInProgram.eventually_pop_jump
            (entry := entry) (regular := .generated supply 2000)
            (input := valueShape) (output := bodyShape)
            hBlocks (by simp) hType hRel hPop with
        ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
      rcases
          hBodyPath hBody hBodyBlocks hBodyCalls
            targetAfterPop trace hAfterPopRel with
        ⟨targetOutcome, traceFinal,
          hBodyEventually, hOutcomeRel⟩
      exact
        ⟨targetOutcome, traceFinal,
          TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
            hEntryEventually hBodyEventually,
          hOutcomeRel⟩

theorem outcome_default_none_of_compileDefaultFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {continuations : OutcomeSimulation.Continuations}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          none ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.Path cfg entry continuations source
      (Structured.OutcomeT.regular
        (source.withSource
          (source.source.withEVM
            { source.source.evm with stack := stack })))
      tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?,
    hType] at hCompile
  cases hCompile
  intro target trace hRel
  rcases
      BlocksInProgram.eventually_pop_jump
        (entry := entry) (regular := regular)
        (input := valueShape) (output := bodyShape)
        hBlocks (by simp) hType hRel hPop with
    ⟨targetFinal, hEventually, hFinalRel⟩
  exact
    ⟨.jump regular targetFinal, trace, hEventually,
      OutcomeSimulation.Rel.regular_iff.mpr
        ⟨hRegular.symm, hFinalRel⟩⟩

theorem outcome_cases_none_of_compileCasesFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {continuations : OutcomeSimulation.Continuations}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
        base supply idx valueShape bodyShape regular =
      some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = none)
    (hDefaultPath :
      defaultBody = none →
        OutcomeSimulation.Path cfg (LabelSupply.label base 1)
          continuations source
          (Structured.OutcomeT.regular
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack })))
          tokens) :
    OutcomeSimulation.Path cfg (casesEntryLabel base idx cases)
      continuations source
      (Structured.OutcomeT.regular
        (source.withSource
          (source.source.withEVM
            { source.source.evm with stack := stack })))
      tokens := by
  induction cases generalizing compilerFuel supply idx result with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = none := by
            simpa [Structured.Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPath hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
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
              have hRequire :
                  bodyResult.requireFallthrough? bodyShape = some () := by
                cases hRequire :
                    bodyResult.requireFallthrough? bodyShape with
                | none =>
                    simp [hRequire] at hCompile
                | some unit =>
                    cases unit
                    rfl
              simp only [hRequire] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1)
                    valueShape bodyShape regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hTailBlocks :
                      TypedCfgPreservation.BlocksInProgram tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · simp [Structured.Switch.select, hEq] at hSelect
                  · have hTailSelect :
                        Structured.Switch.select value rest defaultBody =
                          none := by
                      simpa [Structured.Switch.select, hEq] using hSelect
                    have hTailPath :=
                      ih hTail hTailBlocks hTailSelect
                    intro target trace hRel
                    rcases
                        eventually_test
                          (testLabel :=
                            TypedCfgCompiler.switchTestLabel base idx)
                          (caseLabel := LabelSupply.label base (idx + 2))
                          (nextTest := nextTestLabel base idx rest)
                          (caseValue := caseValue) (value := value)
                          hBlocks (by left) hHead hRel hPop with
                      ⟨targetAfterTest, hTestEventually,
                        hAfterTestRel⟩
                    have hSkipped :
                        TypedCfg.ObserverSemantics.Program.Eventually cfg
                          (TypedCfgCompiler.switchTestLabel base idx)
                          target trace
                          (.jump (nextTestLabel base idx rest)
                            targetAfterTest)
                          trace := by
                      simpa [hEq] using hTestEventually
                    rcases
                        hTailPath targetAfterTest trace hAfterTestRel with
                      ⟨targetOutcome, traceFinal,
                        hTailEventually, hOutcomeRel⟩
                    exact
                      ⟨targetOutcome, traceFinal,
                        TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                          hSkipped hTailEventually,
                        hOutcomeRel⟩

theorem outcome_some_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe scrutinee)
    (hScrutinee :
      ObserverSemantics.Code.run scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody =
        some selected)
    (hSelectedPath :
      ∀ {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram
          bodyResult globalCalls →
        OutcomeSimulation.Path cfg bodyEntry
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx regular)
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          outcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source outcome tokens := by
  have hFallthrough :=
    TypedCfgCompilerFacts.Switch.fallthrough_of_compileStmtFuel?_switch
      hCompile
  refine ⟨?_, fun _hRegular => hFallthrough⟩
  intro target trace hRel
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? scrutinee input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some valueShape =>
      have hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape =
            some () := by
        cases hCheck :
            TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape with
        | none =>
            simp [TypedCfgCompiler.mkCodeBlock?, hType, hCheck] at hCompile
        | some unit =>
            cases unit
            rfl
      simp only [TypedCfgCompiler.mkCodeBlock?, hType, Bind.bind,
        Option.bind] at hCompile
      rw [hSource] at hCompile
      simp at hCompile
      rcases
          StateRel.runCode hType hFrameSafe hScrutinee hRel with
        ⟨targetAfterScrutinee, traceAfterScrutinee,
          hTargetScrutinee, hAfterScrutineeRel⟩
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape =
                some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkCodeBlock?, hType, hValue,
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
                      cases ctx supply (supply + 1) 0
                      valueShape bodyShape regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel?
                    (compilerFuel + 1) defaultBody ctx
                    caseResult.next (LabelSupply.label supply 1)
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
                  have hCaseBlocks :
                      TypedCfgPreservation.BlocksInProgram
                        caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      TypedCfgPreservation.BlocksInProgram
                        defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hCaseCalls :
                      TypedCfgPreservation.CallsInProgram
                        caseResult globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  have hDefaultCalls :
                      TypedCfgPreservation.CallsInProgram
                        defaultResult globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  have hDispatch :
                      OutcomeSimulation.Path cfg
                        (casesEntryLabel supply 0 cases)
                        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                          ctx regular)
                        afterScrutinee outcome tokens := by
                    apply outcome_cases_some_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hCaseCalls
                      hValue hPopType hPop hSelect
                    · intro bodyCompilerFuel caseSupply caseIdx
                        bodyResult hBodyCompile hBodyBlocks hBodyCalls
                      exact
                        hSelectedPath hBodyCompile hBodyBlocks hBodyCalls
                    · intro hDefault
                      have hDefaultSelected :
                          TypedCfgCompiler.compileDefaultFuel?
                              (compilerFuel + 1) (some selected) ctx
                              caseResult.next
                              (LabelSupply.label supply 1)
                              valueShape bodyShape regular =
                            some defaultResult := by
                        simpa [hDefault] using hDefaultCompile
                      apply outcome_default_some_of_compileDefaultFuel?
                        hDefaultSelected hDefaultBlocks hDefaultCalls
                        hPopType hPop
                      intro bodyResult hBodyCompile hBodyBlocks
                        hBodyCalls
                      exact
                        hSelectedPath hBodyCompile hBodyBlocks hBodyCalls
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadRun :
                      TypedCfg.ObserverSemantics.Block.run
                          head target trace =
                        .ok
                          (.jump firstTest targetAfterScrutinee,
                            traceAfterScrutinee) := by
                    unfold TypedCfg.ObserverSemantics.Block.run
                    rw [hTargetScrutinee]
                    simp [head, TypedCfg.Block.runTerm,
                      Bind.bind, Except.bind]
                  have hHeadEventually :
                      TypedCfg.ObserverSemantics.Program.Eventually cfg
                        entry target trace
                        (.jump firstTest targetAfterScrutinee)
                        traceAfterScrutinee := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                      cases cases <;> rfl
                    · exact hHeadRun
                  rcases
                      hDispatch targetAfterScrutinee
                        traceAfterScrutinee hAfterScrutineeRel with
                    ⟨targetOutcome, traceFinal,
                      hDispatchEventually, hOutcomeRel⟩
                  exact
                    ⟨targetOutcome, traceFinal,
                      TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                        hHeadEventually hDispatchEventually,
                      hOutcomeRel⟩

theorem outcome_none_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : ObserverSemantics.State transcript}
    {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe scrutinee)
    (hScrutinee :
      ObserverSemantics.Code.run scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = none) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source
      (Structured.OutcomeT.regular
        (afterScrutinee.withSource
          (afterScrutinee.source.withEVM
            { afterScrutinee.source.evm with stack := stack })))
      tokens := by
  have hFallthrough :=
    TypedCfgCompilerFacts.Switch.fallthrough_of_compileStmtFuel?_switch
      hCompile
  refine ⟨?_, fun _hRegular => hFallthrough⟩
  intro target trace hRel
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? scrutinee input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some valueShape =>
      have hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape =
            some () := by
        cases hCheck :
            TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape with
        | none =>
            simp [TypedCfgCompiler.mkCodeBlock?, hType, hCheck] at hCompile
        | some unit =>
            cases unit
            rfl
      simp only [TypedCfgCompiler.mkCodeBlock?, hType, Bind.bind,
        Option.bind] at hCompile
      rw [hSource] at hCompile
      simp at hCompile
      rcases
          StateRel.runCode hType hFrameSafe hScrutinee hRel with
        ⟨targetAfterScrutinee, traceAfterScrutinee,
          hTargetScrutinee, hAfterScrutineeRel⟩
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape =
                some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkCodeBlock?, hType, hValue,
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
                      cases ctx supply (supply + 1) 0
                      valueShape bodyShape regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel?
                    (compilerFuel + 1) defaultBody ctx
                    caseResult.next (LabelSupply.label supply 1)
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
                  have hCaseBlocks :
                      TypedCfgPreservation.BlocksInProgram
                        caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      TypedCfgPreservation.BlocksInProgram
                        defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDispatch :
                      OutcomeSimulation.Path cfg
                        (casesEntryLabel supply 0 cases)
                        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                          ctx regular)
                        afterScrutinee
                        (Structured.OutcomeT.regular
                          (afterScrutinee.withSource
                            (afterScrutinee.source.withEVM
                              { afterScrutinee.source.evm with
                                stack := stack })))
                        tokens := by
                    apply outcome_cases_none_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hValue hPopType
                      hPop hSelect
                    intro hDefault
                    have hDefaultNone :
                        TypedCfgCompiler.compileDefaultFuel?
                            (compilerFuel + 1) none ctx
                            caseResult.next
                            (LabelSupply.label supply 1)
                            valueShape bodyShape regular =
                          some defaultResult := by
                      simpa [hDefault] using hDefaultCompile
                    exact
                      outcome_default_none_of_compileDefaultFuel?
                        hDefaultNone hDefaultBlocks hPopType hPop rfl
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadRun :
                      TypedCfg.ObserverSemantics.Block.run
                          head target trace =
                        .ok
                          (.jump firstTest targetAfterScrutinee,
                            traceAfterScrutinee) := by
                    unfold TypedCfg.ObserverSemantics.Block.run
                    rw [hTargetScrutinee]
                    simp [head, TypedCfg.Block.runTerm,
                      Bind.bind, Except.bind]
                  have hHeadEventually :
                      TypedCfg.ObserverSemantics.Program.Eventually cfg
                        entry target trace
                        (.jump firstTest targetAfterScrutinee)
                        traceAfterScrutinee := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                      cases cases <;> rfl
                    · exact hHeadRun
                  rcases
                      hDispatch targetAfterScrutinee
                        traceAfterScrutinee hAfterScrutineeRel with
                    ⟨targetOutcome, traceFinal,
                      hDispatchEventually, hOutcomeRel⟩
                  exact
                    ⟨targetOutcome, traceFinal,
                      TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                        hHeadEventually hDispatchEventually,
                      hOutcomeRel⟩

end Switch

namespace Loop

abbrev bodyContinuations :=
  TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations

abbrev postContinuations :=
  TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations

theorem eventually_condition
    {transcript : Trace}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {cond : Structured.Code} {condValue : Bool}
    {source afterCond : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe cond)
    (hCond :
      ObserverSemantics.Code.runCondition cond source =
        .ok (afterCond, condValue))
    (hRel : StateRel source tokens target trace) :
    ∃ targetAfterCond traceAfterCond,
      TypedCfg.ObserverSemantics.Program.Eventually cfg
        loopLabel target trace
        (.jump (if condValue then bodyLabel else endLabel)
          targetAfterCond)
        traceAfterCond ∧
      StateRel afterCond tokens targetAfterCond traceAfterCond := by
  obtain
      ⟨targetAfterCond, traceAfterCond,
        hBlockRun, hAfterCondRel⟩ :=
    Code.run_jumpi_toCfg
      (jumpTarget := bodyLabel) (fallthrough := endLabel)
      hType hFrameSafe hCond hRel
  exact
    ⟨targetAfterCond, traceAfterCond,
      BlocksInProgram.eventually_of_run hBlocks hMem hBlockRun,
      hAfterCondRel⟩

theorem preserves_condition
    {transcript : Trace}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {cond : Structured.Code} {condValue : Bool}
    {source afterCond : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe cond)
    (hCond :
      ObserverSemantics.Code.runCondition cond source =
        .ok (afterCond, condValue)) :
    OutcomeSimulation.PathPreserves cfg loopLabel
      (if condValue then bodyLabel else endLabel)
      source afterCond tokens := by
  intro target trace hRel
  exact
    eventually_condition hBlocks hMem hType hFrameSafe hCond hRel

theorem path_of_eval
    {transcript : Trace}
    {program : Structured.Program} {fuel bound : Nat}
    {cond : Structured.Code} {post body : Structured.Block}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {tokens : List Word}
    {outer : OutcomeSimulation.Continuations}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hFrameSafe : ObserverSemantics.Code.FrameSafe cond)
    (hOuterRegular : outer.regular = endLabel)
    (hFuelLt : fuel < bound)
    (hEval :
      ObserverSemantics.For.Eval program fuel
        cond post body source outcome)
    (hBodyPath :
      ∀ {bodyFuel : Nat}
        {bodySource : ObserverSemantics.State transcript}
        {bodyOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        ObserverSemantics.Block.Eval program bodyFuel body
            bodySource bodyOutcome →
        bodyFuel < bound →
        OutcomeSimulation.Path cfg bodyLabel
          (bodyContinuations endLabel postLabel outer)
          bodySource bodyOutcome tokens)
    (hPostPath :
      ∀ {postFuel : Nat}
        {postSource : ObserverSemantics.State transcript}
        {postOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        ObserverSemantics.Block.Eval program postFuel post
            postSource postOutcome →
        postFuel < bound →
        OutcomeSimulation.Path cfg postLabel
          (postContinuations loopLabel outer)
          postSource postOutcome tokens) :
    OutcomeSimulation.Path cfg loopLabel outer
      source outcome tokens := by
  cases hEval with
  | false hCond =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.regular_of_path hOuterRegular
      simpa using hCondition
  | body_brk hCond hBody =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      have hBodyBreak :=
        OutcomeSimulation.Path.to_brk
          (by rfl) (hBodyPath hBody (by omega))
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      exact
        OutcomeSimulation.Path.regular_of_path
          hOuterRegular hBodyBreak
  | body_leave hCond hBody =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl) (hBodyPath hBody (by omega))
  | body_halt hCond hBody =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      exact
        OutcomeSimulation.Path.transport_halt
          (hBodyPath hBody (by omega))
  | regular_post_regular hCond hBody hPost hLoop =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular
          (hBodyPath hBody (by omega)))
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular
          (hPostPath hPost (by omega)))
      exact
        path_of_eval hBlocks hMem hType hFrameSafe hOuterRegular
          (by omega) hLoop hBodyPath hPostPath
  | cont_post_regular hCond hBody hPost hLoop =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_cont
          (by rfl) (hBodyPath hBody (by omega)))
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular
          (hPostPath hPost (by omega)))
      exact
        path_of_eval hBlocks hMem hType hFrameSafe hOuterRegular
          (by omega) hLoop hBodyPath hPostPath
  | regular_post_leave hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular
          (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl) (hPostPath hPost (by omega))
  | cont_post_leave hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_cont
          (by rfl) (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl) (hPostPath hPost (by omega))
  | regular_post_halt hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular
          (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_halt
          (hPostPath hPost (by omega))
  | cont_post_halt hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_cont
          (by rfl) (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_halt
          (hPostPath hPost (by omega))
termination_by fuel

theorem outcome_of_compileStmtFuel?_and_eval
    {transcript : Trace} {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.for_ init cond post body) ctx supply entry input regular =
      some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hCondSafe : ObserverSemantics.Code.FrameSafe cond)
    (hEval :
      ObserverSemantics.Stmt.Eval program sourceFuel
        (.for_ init cond post body) source outcome)
    (hInitPath :
      ∀ {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape}
        {initFuel : Nat}
        {initSource : ObserverSemantics.State transcript}
        {initOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            (supply + 1) entry input (LabelSupply.label supply 0) =
          some initResult →
        initResult.fallthrough? = some loopInput →
        TypedCfgPreservation.BlocksInProgram initResult cfg →
        TypedCfgPreservation.CallsInProgram
          initResult globalCalls →
        ObserverSemantics.Block.Eval program initFuel init
          initSource initOutcome →
        initFuel < sourceFuel →
        OutcomeSimulation.Path cfg entry
          (postContinuations (LabelSupply.label supply 0)
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular))
          initSource initOutcome tokens)
    (hBodyPath :
      ∀ {initResult bodyResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape}
        {bodyFuel : Nat}
        {bodySource : ObserverSemantics.State transcript}
        {bodyOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            { ctx with
              breakLabel? := some regular
              breakShape? :=
                some { condOutput with slots := condOutput.slots.tail }
              continueLabel? := some (LabelSupply.label supply 2)
              continueShape? :=
                some { condOutput with slots := condOutput.slots.tail } }
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram
          bodyResult globalCalls →
        ObserverSemantics.Block.Eval program bodyFuel body
          bodySource bodyOutcome →
        bodyFuel < sourceFuel →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 1)
          (bodyContinuations regular (LabelSupply.label supply 2)
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular))
          bodySource bodyOutcome tokens)
    (hPostPath :
      ∀ {bodyResult postResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape}
        {postFuel : Nat}
        {postSource : ObserverSemantics.State transcript}
        {postOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            bodyResult.next (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) =
          some postResult →
        TypedCfgPreservation.BlocksInProgram postResult cfg →
        TypedCfgPreservation.CallsInProgram
          postResult globalCalls →
        ObserverSemantics.Block.Eval program postFuel post
          postSource postOutcome →
        postFuel < sourceFuel →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 2)
          (postContinuations (LabelSupply.label supply 0)
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular))
          postSource postOutcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source outcome tokens := by
  rcases
      TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for
        hCompile with
    ⟨initResult, loopInput, condOutput, _condition,
      bodyResult, postResult, hInitCompile, hInitFallthrough,
      hType, _hSource, _hHead, hBodyCompile, _hBodyRequire,
      hPostCompile, _hPostRequire, rfl⟩
  have hInitBlocks :
      TypedCfgPreservation.BlocksInProgram initResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hPostBlocks :
      TypedCfgPreservation.BlocksInProgram postResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hInitCalls :
      TypedCfgPreservation.CallsInProgram
        initResult globalCalls := by
    intro site hMem
    apply hCalls site
    simp [hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram
        bodyResult globalCalls := by
    intro site hMem
    apply hCalls site
    simp [hMem]
  have hPostCalls :
      TypedCfgPreservation.CallsInProgram
        postResult globalCalls := by
    intro site hMem
    apply hCalls site
    simp [hMem]
  have hLoopMem :
      { label := LabelSupply.label supply 0
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi (LabelSupply.label supply 1) regular } ∈
        (initResult.blocks ++
          [{ label := LabelSupply.label supply 0
             input := loopInput
             body := TypedCfgCompiler.Code.toCfg cond
             output := condOutput
             term := .jumpi (LabelSupply.label supply 1) regular }] ++
          bodyResult.blocks ++ postResult.blocks) := by
    simp
  refine ⟨?_, ?_⟩
  · cases hEval with
    | @for_init_regular fuel _ _ _ _ _ _ _ hInit hLoop =>
        apply OutcomeSimulation.Path.bind_jump
          (OutcomeSimulation.Path.to_regular
            (hInitPath hInitCompile hInitFallthrough
              hInitBlocks hInitCalls hInit (by omega)))
        apply path_of_eval (bound := fuel + 1)
          hBlocks hLoopMem hType hCondSafe rfl
          (by omega) hLoop
        · intro bodyFuel bodySource bodyOutcome hBody hBodyFuel
          exact
            hBodyPath hBodyCompile hBodyBlocks hBodyCalls
              hBody hBodyFuel
        · intro postFuel postSource postOutcome hPost hPostFuel
          exact
            hPostPath hPostCompile hPostBlocks hPostCalls
              hPost hPostFuel
    | for_init_leave hInit =>
        exact
          OutcomeSimulation.Path.transport_leave
            (by rfl)
            (hInitPath hInitCompile hInitFallthrough
              hInitBlocks hInitCalls hInit (by omega))
    | for_init_halt hInit =>
        exact
          OutcomeSimulation.Path.transport_halt
            (hInitPath hInitCompile hInitFallthrough
              hInitBlocks hInitCalls hInit (by omega))
  · intro _hRegular
    exact
      ⟨{ condOutput with slots := condOutput.slots.tail }, rfl⟩

end Loop

namespace Call

theorem eventually_procEntry
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {proc : Structured.Proc}
    {fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes sourceProgram.procs proc
        context.procBlocks context.procCalls}
    (state : EVMState) (trace : Trace) :
    TypedCfg.ObserverSemantics.Program.Eventually cfg
      (ProcLabel.entry proc.name) state trace
      (.jump fragment.entry state) trace := by
  rcases fragment.route with hDirect | hAdapterRoute
  · rcases hDirect with ⟨hEntry, hInput⟩
    simpa [hEntry] using
      TypedCfg.ObserverSemantics.Program.Eventually.residual
        cfg (ProcLabel.entry proc.name) state trace
  · rcases hAdapterRoute with
      ⟨adapter, hEntry, hInput, hAdapterCompile, hAdapterMem⟩
    have hMem : adapter ∈ cfg.blocks := by
      have hBlocksEq :
          cfg.blocks =
            context.main.blocks ++ context.procBlocks ++
              TypedCfgCompiler.dispatchBlocks sourceProgram.procs
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
        have hPlainRunAt :
            TypedCfg.Instr.runAt (.relabel fragment.input)
                (TypedCfgCompiler.Shape.procEntry proc) state =
              .ok (state, output) := by
          unfold TypedCfg.Instr.runAt
          rw [hType]
          simp [TypedCfg.Instr.runState, Bind.bind, Except.bind]
        have hObserverRunAt :
            TypedCfg.ObserverSemantics.Instr.runAt
                (.relabel fragment.input)
                (TypedCfgCompiler.Shape.procEntry proc)
                state trace =
              .ok ((state, output), trace) := by
          rw [TypedCfg.ObserverSemantics.Instr.runAt_of_observer?_eq_none
            (by rfl), hPlainRunAt]
          rfl
        let generated : TypedCfg.Block :=
          { label := ProcLabel.entry proc.name
            input := TypedCfgCompiler.Shape.procEntry proc
            body := [.relabel fragment.input]
            output := output
            term := .jump (ProcLabel.body proc.name) }
        have hRun :
            TypedCfg.ObserverSemantics.Block.run
                generated state trace =
              .ok
                (.jump (ProcLabel.body proc.name) state, trace) := by
          unfold TypedCfg.ObserverSemantics.Block.run
          rw [TypedCfg.ObserverSemantics.Block.runBody_cons,
            hObserverRunAt]
          simp [TypedCfg.ObserverSemantics.Block.runBody_nil,
            generated, TypedCfg.Block.runTerm,
            Bind.bind, Except.bind]
        let singleton : TypedCfgCompiler.Result :=
          { blocks := [generated]
            next := 0
            calls := []
            fallthrough? := none }
        have hContains :
            TypedCfgPreservation.BlocksInProgram singleton cfg := by
          intro block hMem
          have hEq : block = generated := by
            simpa [singleton] using hMem
          subst block
          simpa [generated] using hFind
        rw [hEntry]
        exact
          BlocksInProgram.eventually_of_run hContains
            (block := generated) (by simp [singleton]) hRun

theorem entry_eventually_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {args callerStack : EvmYul.Stack Word}
    (hLookup :
      Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.call name) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel : StateRel source tokens target trace)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc
          source.source.evm.stack =
        some (args, callerStack))
    (hProcWF : proc.WF) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.Eventually cfg
        entry target trace
        (.jump (ProcLabel.entry name) targetFinal) trace ∧
      StateRel
        (source.withSource
          ((source.source.withEVM
            { source.source.evm with stack := args }).pushReturn
              callerStack proc.retc))
        (Structured.Stmt.callToken supply :: tokens)
        targetFinal trace := by
  rcases
      TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
        hLookup hCompile with
    ⟨returnShape, output, hReturnShape, hType, rfl⟩
  rcases
      TypedCfgPreservation.CallStack.runBody_callEntry_preserves
        (retc := proc.retc)
        (token := Structured.Stmt.callToken supply)
        hRel.1 hSplit hType hProcWF.1 with
    ⟨targetFinal, hPlainBody, hFinalRel⟩
  have hSilentSink :
      ∀ depth instr,
        instr ∈ TypedCfgCompiler.sinkTopUnder depth →
          TypedCfg.ObserverSemantics.Instr.observer? instr = none := by
    intro depth
    induction depth with
    | zero =>
        intro instr hMem
        simp [TypedCfgCompiler.sinkTopUnder] at hMem
    | succ depth ih =>
        intro instr hMem
        simp [TypedCfgCompiler.sinkTopUnder] at hMem
        rcases hMem with rfl | hMem
        · rfl
        · exact ih instr hMem
  have hSilent :
      ∀ instr,
        instr ∈
            (.returnToken (Structured.Stmt.callToken supply) ::
              TypedCfgCompiler.sinkTopUnder proc.argc) →
          TypedCfg.ObserverSemantics.Instr.observer? instr = none := by
    intro instr hMem
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hMem
    · rfl
    · exact hSilentSink proc.argc instr hMem
  have hObserverBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (.returnToken (Structured.Stmt.callToken supply) ::
            TypedCfgCompiler.sinkTopUnder proc.argc)
          input target trace =
        .ok ((targetFinal, output), trace) := by
    rw [TypedCfg.ObserverSemantics.Block.runBody_of_forall_observer?_eq_none
      hSilent,
      hPlainBody]
    rfl
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body :=
        .returnToken (Structured.Stmt.callToken supply) ::
          TypedCfgCompiler.sinkTopUnder proc.argc
      output := output
      term := .jump (ProcLabel.entry name) }
  have hBlockRun :
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.jump (ProcLabel.entry name) targetFinal, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [hObserverBody]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  exact
    ⟨targetFinal,
      BlocksInProgram.eventually_of_run hBlocks
        (block := generated) (by simp [generated]) hBlockRun,
      ⟨by simpa using hFinalRel, hRel.2⟩⟩

theorem dispatch_eventually
    {transcript : Trace}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {site : TypedCfgCompiler.DispatchSite}
    {bodyState returned : ObserverSemantics.State transcript}
    {frame : ReturnDest} {stack : EvmYul.Stack Word}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs =
        some proc)
    (hSiteProc : site.procName = proc.name)
    (hSiteMem : site ∈ context.calls)
    (hRel :
      StateRel bodyState (site.token :: tokens) target trace)
    (hPop :
      bodyState.source.popReturn? =
        some (frame, returned.source))
    (hCursor : returned.cursor = bodyState.cursor)
    (hAttach :
      Structured.StackFrame.attachReturns? frame
          bodyState.source.evm.stack =
        some stack)
    (hRetc : frame.retc = proc.retc) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.Eventually cfg
        (ProcLabel.exit proc.name) target trace
        (.jump site.returnLabel targetFinal) trace ∧
      StateRel
        (returned.withSource
          (returned.source.withEVM
            { bodyState.source.evm with stack := stack }))
        tokens targetFinal trace := by
  rcases
      TypedCfgPreservation.CallStack.eraseReturnToken_preserves
        hRel.1 hPop hAttach with
    ⟨hToken, hFinalRel⟩
  have hFind :
      TypedCfg.Block.ReturnSite.findTarget? site.token
          (TypedCfgCompiler.returnSitesFor proc.name context.calls) =
        some site.returnLabel := by
    simpa [hSiteProc] using
      TypedCfgCompilerFacts.Call.findTarget?_returnSitesFor_of_mem
        context.tokensUnique hSiteMem
  have hSitesNonempty :
      (TypedCfgCompiler.returnSitesFor
        proc.name context.calls).isEmpty = false := by
    cases hSites :
        TypedCfgCompiler.returnSitesFor proc.name context.calls with
    | nil =>
        simp [hSites, TypedCfg.Block.ReturnSite.findTarget?] at hFind
    | cons head rest =>
        rfl
  have hBlock := context.dispatchBlock hLookup
  let targetFinal : EVMState :=
    { target with stack := target.stack.eraseIdx proc.retc }
  let generated := TypedCfgCompiler.dispatchBlock proc context.calls
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.jump site.returnLabel targetFinal, trace) := by
    rw [hRetc] at hToken hFinalRel
    simp [generated, TypedCfg.ObserverSemantics.Block.run,
      TypedCfg.ObserverSemantics.Block.runBody_nil,
      TypedCfgCompiler.dispatchBlock, hSitesNonempty,
      TypedCfg.Block.runTerm,
      TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit,
      hToken, hFind, targetFinal, Bind.bind, Except.bind]
  let singleton : TypedCfgCompiler.Result :=
    { blocks := [generated]
      next := 0
      calls := []
      fallthrough? := none }
  have hContains :
      TypedCfgPreservation.BlocksInProgram singleton cfg := by
    intro block hMem
    have hEq : block = generated := by
      simpa [singleton] using hMem
    subst block
    simpa [generated] using hBlock
  refine
    ⟨targetFinal,
      BlocksInProgram.eventually_of_run hContains
        (block := generated) (by simp [singleton]) hRun,
      ?_⟩
  rw [hRetc] at hFinalRel
  refine ⟨?_, ?_⟩
  simpa using hFinalRel
  simpa [Simulation.ResourceReplay.State.remaining, hCursor] using hRel.2

end Call

namespace Block

/--
The empty statement-list compiler preserves observer state and reaches the
supplied regular continuation with the same remaining trace.
-/
theorem preserves_nil_of_compileStmtListFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {state : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1) [] ctx
        supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      state (Structured.OutcomeT.regular state) tokens := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  refine ⟨?_, ?_⟩
  · intro target trace hRel
    let generated : TypedCfg.Block :=
      { label := entry
        input := input
        body := []
        output := input
        term := .jump regular }
    have hRun :
        TypedCfg.ObserverSemantics.Block.run
            generated target trace =
          .ok (.jump regular target, trace) := by
      unfold TypedCfg.ObserverSemantics.Block.run
      rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
      simp [generated, TypedCfg.Block.runTerm,
        Bind.bind, Except.bind]
    have hEventually :=
      BlocksInProgram.eventually_of_run
        hBlocks (block := generated)
          (by simp [generated]) hRun
    exact
      ⟨.jump regular target, trace, hEventually,
        OutcomeSimulation.Rel.regular_iff.mpr
          ⟨rfl, hRel⟩⟩
  · intro _hMode
    exact ⟨input, rfl⟩

/--
Outcome-indexed observer statement-list composition.

The theorem is independent of statement form: recursive statement and tail
proofs supply the adjacent semantic paths, while this lemma owns compiler
fallthrough decomposition and effectful CFG path composition.
-/
theorem preserves_cons_of_compileStmtListFuel?_and_eval
    {transcript : Trace}
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
        (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hEval :
      ObserverSemantics.Block.Eval program sourceFuel
        { stmts := stmt :: rest } source outcome)
    (hHead :
      ∀ {headResult : TypedCfgCompiler.Result}
        {stmtFuel : Nat}
        {stmtSource : ObserverSemantics.State transcript}
        {stmtOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        TypedCfgPreservation.CallsInProgram
          headResult globalCalls →
        ObserverSemantics.Stmt.Eval program stmtFuel stmt
          stmtSource stmtOutcome →
        stmtFuel < sourceFuel →
        OutcomeSimulation.Preserves headResult cfg entry
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx (TypedCfgCompiler.restLabel supply))
          stmtSource stmtOutcome tokens)
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape} {tailFuel : Nat}
        {tailSource : ObserverSemantics.State transcript}
        {tailOutcome :
          ObserverSemantics.Outcome (transcript := transcript)},
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        TypedCfgPreservation.CallsInProgram
          tailResult globalCalls →
        ObserverSemantics.Block.Eval program tailFuel
          { stmts := rest } tailSource tailOutcome →
        tailFuel < sourceFuel →
        OutcomeSimulation.Preserves tailResult cfg
          (TypedCfgCompiler.restLabel supply)
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx regular)
          tailSource tailOutcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      source outcome tokens := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    cases hEval with
    | cons_regular hStmt _hRest =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt
            (Nat.lt_succ_self _)
        obtain ⟨output, hOutput⟩ :=
          OutcomeSimulation.Preserves.fallthrough_of_regular
            hHeadPreserves
        rw [hFallthrough] at hOutput
        cases hOutput
    | cons_brk hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_brk
            (by rfl) hHeadPreserves.1
    | cons_cont hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_cont
            (by rfl) hHeadPreserves.1
    | cons_leave hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_leave
            (by rfl) hHeadPreserves.1
    | cons_halt hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_halt
            hHeadPreserves.1
  · rcases hWithTail with
      ⟨tailInput, tailResult,
        hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHeadCalls :=
      TypedCfgPreservation.CallsInProgram.left_of_append hCalls
    have hTailCalls :=
      TypedCfgPreservation.CallsInProgram.right_of_append hCalls
    cases hEval with
    | cons_regular hStmt hRest =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        have hTailPreserves :=
          hTail hFallthrough hTailCompile hTailBlocks hTailCalls
            hRest (Nat.lt_succ_self _)
        refine ⟨?_, ?_⟩
        · exact
            OutcomeSimulation.Path.bind_jump
              hHeadPreserves.to_regular_path hTailPreserves.1
        · intro hMode
          obtain ⟨output, hOutput⟩ :=
            hTailPreserves.2 hMode
          exact
            ⟨output,
              by
                simpa [TypedCfgCompiler.Result.append] using hOutput⟩
    | cons_brk hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_brk
            (by rfl) hHeadPreserves.1
    | cons_cont hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_cont
            (by rfl) hHeadPreserves.1
    | cons_leave hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_leave
            (by rfl) hHeadPreserves.1
    | cons_halt hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply
          OutcomeSimulation.Preserves.of_path_of_nonregular
            (by intro hMode; cases hMode)
        exact
          OutcomeSimulation.Path.transport_halt
            hHeadPreserves.1

end Block

mutual

  /--
  Observer-preserving compilation for a complete Structured block in a checked
  generated whole-program context.
  -/
  theorem outcome_block_of_compileFuel?_and_eval_with_calls
      {transcript : Trace} {compilerFuel sourceFuel : Nat}
      {program : Structured.Program} {block : Structured.Block}
      {entryShapes : TypedCfgCompiler.ProcEntryShapes}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
      {source : ObserverSemantics.State transcript}
      {outcome : ObserverSemantics.Outcome (transcript := transcript)}
      {tokens : List Word}
      {canBreak canContinue canLeave : Bool}
      (generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg)
      (hCompile :
        TypedCfgCompiler.compileBlockFuel? compilerFuel block ctx
            supply entry input regular =
          some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hResultCalls :
        TypedCfgPreservation.CallsInProgram result generated.calls)
      (hEval :
        ObserverSemantics.Block.Eval program sourceFuel block source outcome)
      (hWF :
        Structured.Block.WF canBreak canContinue canLeave block)
      (hFrameSafe : ObserverSemantics.Block.FrameSafe block)
      (hCalls :
        Structured.ProcList.BlockCallsResolved program.procs block)
      (hSupports :
        TypedCfgPreservation.OutcomeSimulation.ContextSupports ctx
          canBreak canContinue canLeave)
      (hProcs : ctx.procs = program.procs)
      (hProgramWF : program.WF)
      (hProgramFrameSafe : ObserverSemantics.Program.FrameSafe program) :
      OutcomeSimulation.Preserves result cfg entry
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        source outcome tokens := by
    cases compilerFuel with
    | zero =>
        simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
    | succ blockFuel =>
        unfold TypedCfgCompiler.compileBlockFuel? at hCompile
        cases blockFuel with
        | zero =>
            simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
        | succ listFuel =>
            cases block with
            | mk stmts =>
                cases stmts with
                | nil =>
                    cases hEval
                    exact
                      Block.preserves_nil_of_compileStmtListFuel?
                        hCompile hBlocks
                | cons stmt rest =>
                    cases hWF with
                    | cons hStmtWF hRestWF =>
                        cases hFrameSafe with
                        | cons hStmtFrameSafe hRestFrameSafe =>
                            cases hCalls with
                            | mk hStmtListCalls =>
                                cases hStmtListCalls with
                                | cons hStmtCalls hRestCalls =>
                                    apply
                                      Block.preserves_cons_of_compileStmtListFuel?_and_eval
                                        hCompile hBlocks hResultCalls hEval
                                    · intro headResult stmtFuel stmtSource
                                        stmtOutcome hHeadCompile hHeadBlocks
                                        hHeadCalls hHeadEval hFuelLt
                                      exact
                                        outcome_stmt_of_compileFuel?_and_eval_with_calls
                                          generated hHeadCompile hHeadBlocks
                                          hHeadCalls hHeadEval hStmtWF
                                          hStmtFrameSafe hStmtCalls hSupports
                                          hProcs hProgramWF
                                          hProgramFrameSafe
                                    · intro headResult tailResult tailInput
                                        tailFuel tailSource tailOutcome
                                        hFallthrough hTailCompile hTailBlocks
                                        hTailCalls hTailEval hFuelLt
                                      have hTailBlockCompile :
                                          TypedCfgCompiler.compileBlockFuel?
                                              (listFuel + 1)
                                              { stmts := rest } ctx
                                              headResult.next
                                              (TypedCfgCompiler.restLabel
                                                supply)
                                              tailInput regular =
                                            some tailResult := by
                                        simpa
                                          [TypedCfgCompiler.compileBlockFuel?]
                                          using hTailCompile
                                      exact
                                        outcome_block_of_compileFuel?_and_eval_with_calls
                                          generated hTailBlockCompile
                                          hTailBlocks hTailCalls hTailEval
                                          hRestWF hRestFrameSafe
                                          (.mk hRestCalls) hSupports hProcs
                                          hProgramWF
                                          hProgramFrameSafe
  termination_by sourceFuel

  /--
  Observer-preserving compilation for every Structured statement, including
  generated procedure entry, body, exit, and return dispatch.
  -/
  theorem outcome_stmt_of_compileFuel?_and_eval_with_calls
      {transcript : Trace} {compilerFuel sourceFuel : Nat}
      {program : Structured.Program} {stmt : Structured.Stmt}
      {entryShapes : TypedCfgCompiler.ProcEntryShapes}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
      {source : ObserverSemantics.State transcript}
      {outcome : ObserverSemantics.Outcome (transcript := transcript)}
      {tokens : List Word}
      {canBreak canContinue canLeave : Bool}
      (generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg)
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx
            supply entry input regular =
          some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hResultCalls :
        TypedCfgPreservation.CallsInProgram result generated.calls)
      (hEval :
        ObserverSemantics.Stmt.Eval program sourceFuel stmt source outcome)
      (hWF :
        Structured.Stmt.WF canBreak canContinue canLeave stmt)
      (hFrameSafe : ObserverSemantics.Stmt.FrameSafe stmt)
      (hCalls :
        Structured.ProcList.StmtCallsResolved program.procs stmt)
      (hSupports :
        TypedCfgPreservation.OutcomeSimulation.ContextSupports ctx
          canBreak canContinue canLeave)
      (hProcs : ctx.procs = program.procs)
      (hProgramWF : program.WF)
      (hProgramFrameSafe : ObserverSemantics.Program.FrameSafe program) :
      OutcomeSimulation.Preserves result cfg entry
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        source outcome tokens := by
    cases compilerFuel with
    | zero =>
        simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
    | succ compilerFuel =>
        cases hEval with
        | code hRun =>
            cases hFrameSafe with
            | code hCodeSafe =>
                exact
                  Stmt.outcome_code_of_compileStmtFuel?
                    hCompile hBlocks hCodeSafe hRun
        | if_false hCond =>
            cases hFrameSafe with
            | if_ hCondSafe hBodySafe =>
                exact
                  Stmt.outcome_if_false_of_compileStmtFuel?
                    hCompile hBlocks hCondSafe hCond
        | @if_true fuel _ _ _ _ _ hCond hBodyEval =>
            cases hWF with
            | if_ hBodyWF =>
                cases hFrameSafe with
                | if_ hCondSafe hBodyFrameSafe =>
                    cases hCalls with
                    | if_ hBodyCalls =>
                        apply
                          Stmt.outcome_if_true_of_compileStmtFuel?
                            hCompile hBlocks hResultCalls hCondSafe hCond
                        intro bodyInput bodyResult hBodyCompile hBodyBlocks
                          hBodyResultCalls
                        exact
                          (outcome_block_of_compileFuel?_and_eval_with_calls
                            generated hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval hBodyWF
                            hBodyFrameSafe hBodyCalls hSupports hProcs
                            hProgramWF hProgramFrameSafe).1
        | switch_none hScrutinee hPop hSelect =>
            cases hFrameSafe with
            | switch hScrutineeSafe hCaseSafe hDefaultSafe =>
                cases compilerFuel with
                | zero =>
                    rw [
                      TypedCfgCompilerFacts.Switch.compileStmtFuel?_switch_one_eq_none]
                      at hCompile
                    cases hCompile
                | succ switchFuel =>
                    exact
                      Switch.outcome_none_of_compileStmtFuel?
                        hCompile hBlocks hScrutineeSafe
                        hScrutinee hPop hSelect
        | @switch_some fuel _ _ _ _ _ _ _ _ _ _ hScrutinee hPop
            hStateAfterPop hSelect hBodyEval =>
            subst hStateAfterPop
            cases hWF with
            | switch hCaseWF hDefaultWF =>
                cases hFrameSafe with
                | switch hScrutineeSafe hCaseSafe hDefaultSafe =>
                    cases hCalls with
                    | switch hCaseCalls hDefaultCalls =>
                        cases compilerFuel with
                        | zero =>
                            rw [
                              TypedCfgCompilerFacts.Switch.compileStmtFuel?_switch_one_eq_none]
                              at hCompile
                            cases hCompile
                        | succ switchFuel =>
                            apply
                              Switch.outcome_some_of_compileStmtFuel?
                                hCompile hBlocks hResultCalls hScrutineeSafe
                                hScrutinee hPop hSelect
                            intro bodyCompilerFuel bodySupply bodyEntry
                              bodyShape bodyResult hBodyCompile hBodyBlocks
                              hBodyResultCalls
                            have hSelectedWF :=
                              Structured.Switch.wf_of_select
                                hCaseWF hDefaultWF hSelect
                            have hSelectedFrameSafe :=
                              TypedCfgCompilerFacts.switch_property_of_select
                                hCaseSafe hDefaultSafe hSelect
                            have hSelectedCalls :=
                              TypedCfgCompilerFacts.switch_property_of_select
                                hCaseCalls hDefaultCalls hSelect
                            exact
                              (outcome_block_of_compileFuel?_and_eval_with_calls
                                generated hBodyCompile hBodyBlocks
                                hBodyResultCalls hBodyEval hSelectedWF
                                hSelectedFrameSafe hSelectedCalls hSupports
                                hProcs hProgramWF
                                hProgramFrameSafe).1
        | @for_init_regular fuel _ _ _ _ _ _ _ hInitEval hLoopEval =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                cases hFrameSafe with
                | for_ hInitSafe hCondSafe hPostSafe hBodySafe =>
                    cases hCalls with
                    | for_ hInitCalls hPostCalls hBodyCalls =>
                        apply
                          Loop.outcome_of_compileStmtFuel?_and_eval
                            hCompile hBlocks hResultCalls hCondSafe
                            (.for_init_regular hInitEval hLoopEval)
                        · intro initResult loopInput initFuel initSource
                            initOutcome hInitCompile hInitFallthrough
                            hInitBlocks hInitResultCalls hInitEval' hFuelLt
                          simpa [Loop.postContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hInitCompile hInitBlocks
                              hInitResultCalls hInitEval' hInitWF hInitSafe
                              hInitCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hProgramWF
                              hProgramFrameSafe).1
                        · intro initResult bodyResult condOutput bodyFuel
                            bodySource bodyOutcome hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval' hFuelLt
                          simpa [Loop.bodyContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hBodyCompile hBodyBlocks
                              hBodyResultCalls hBodyEval' hBodyWF hBodySafe
                              hBodyCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                                hSupports regular
                                (LabelSupply.label supply 2)
                                { condOutput with
                                  slots := condOutput.slots.tail })
                              hProcs hProgramWF
                              hProgramFrameSafe).1
                        · intro bodyResult postResult condOutput postFuel
                            postSource postOutcome hPostCompile hPostBlocks
                            hPostResultCalls hPostEval' hFuelLt
                          simpa [Loop.postContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hPostCompile hPostBlocks
                              hPostResultCalls hPostEval' hPostWF hPostSafe
                              hPostCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hProgramWF
                              hProgramFrameSafe).1
        | @for_init_leave fuel _ _ _ _ _ _ hInitEval =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                cases hFrameSafe with
                | for_ hInitSafe hCondSafe hPostSafe hBodySafe =>
                    cases hCalls with
                    | for_ hInitCalls hPostCalls hBodyCalls =>
                        apply
                          Loop.outcome_of_compileStmtFuel?_and_eval
                            hCompile hBlocks hResultCalls hCondSafe
                            (.for_init_leave hInitEval)
                        · intro initResult loopInput initFuel initSource
                            initOutcome hInitCompile hInitFallthrough
                            hInitBlocks hInitResultCalls hInitEval' hFuelLt
                          simpa [Loop.postContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hInitCompile hInitBlocks
                              hInitResultCalls hInitEval' hInitWF hInitSafe
                              hInitCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hProgramWF
                              hProgramFrameSafe).1
                        · intro initResult bodyResult condOutput bodyFuel
                            bodySource bodyOutcome hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval' hFuelLt
                          simpa [Loop.bodyContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hBodyCompile hBodyBlocks
                              hBodyResultCalls hBodyEval' hBodyWF hBodySafe
                              hBodyCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                                hSupports regular
                                (LabelSupply.label supply 2)
                                { condOutput with
                                  slots := condOutput.slots.tail })
                              hProcs hProgramWF
                              hProgramFrameSafe).1
                        · intro bodyResult postResult condOutput postFuel
                            postSource postOutcome hPostCompile hPostBlocks
                            hPostResultCalls hPostEval' hFuelLt
                          simpa [Loop.postContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hPostCompile hPostBlocks
                              hPostResultCalls hPostEval' hPostWF hPostSafe
                              hPostCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hProgramWF
                              hProgramFrameSafe).1
        | @for_init_halt fuel _ _ _ _ _ _ _ hInitEval =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                cases hFrameSafe with
                | for_ hInitSafe hCondSafe hPostSafe hBodySafe =>
                    cases hCalls with
                    | for_ hInitCalls hPostCalls hBodyCalls =>
                        apply
                          Loop.outcome_of_compileStmtFuel?_and_eval
                            hCompile hBlocks hResultCalls hCondSafe
                            (.for_init_halt hInitEval)
                        · intro initResult loopInput initFuel initSource
                            initOutcome hInitCompile hInitFallthrough
                            hInitBlocks hInitResultCalls hInitEval' hFuelLt
                          simpa [Loop.postContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hInitCompile hInitBlocks
                              hInitResultCalls hInitEval' hInitWF hInitSafe
                              hInitCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hProgramWF
                              hProgramFrameSafe).1
                        · intro initResult bodyResult condOutput bodyFuel
                            bodySource bodyOutcome hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval' hFuelLt
                          simpa [Loop.bodyContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hBodyCompile hBodyBlocks
                              hBodyResultCalls hBodyEval' hBodyWF hBodySafe
                              hBodyCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                                hSupports regular
                                (LabelSupply.label supply 2)
                                { condOutput with
                                  slots := condOutput.slots.tail })
                              hProcs hProgramWF
                              hProgramFrameSafe).1
                        · intro bodyResult postResult condOutput postFuel
                            postSource postOutcome hPostCompile hPostBlocks
                            hPostResultCalls hPostEval' hFuelLt
                          simpa [Loop.postContinuations,
                            TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hPostCompile hPostBlocks
                              hPostResultCalls hPostEval' hPostWF hPostSafe
                              hPostCalls
                              (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hProgramWF
                              hProgramFrameSafe).1
        | brk =>
            cases hWF with
            | brk hAllowed =>
                rcases hSupports.breakLabel hAllowed with
                  ⟨target, hTarget⟩
                exact
                  Stmt.outcome_brk_of_compileStmtFuel?
                    hTarget hCompile hBlocks
        | cont =>
            cases hWF with
            | cont hAllowed =>
                rcases hSupports.continueLabel hAllowed with
                  ⟨target, hTarget⟩
                exact
                  Stmt.outcome_cont_of_compileStmtFuel?
                    hTarget hCompile hBlocks
        | leave hReturns =>
            cases hWF with
            | leave hAllowed =>
                rcases hSupports.leaveLabel hAllowed with
                  ⟨target, hTarget⟩
                exact
                  Stmt.outcome_leave_of_compileStmtFuel?
                    hTarget hCompile hBlocks
        | @call_regular fuel name state proc args callerStack stack
            bodyState returned frame hLookup hSplit hBody hPop hAttach =>
            have hCompilerLookup :
                Structured.ProcList.lookup? name ctx.procs = some proc := by
              simpa [hProcs] using hLookup
            have hProcWF :=
              Structured.Program.procWF_of_lookup? hProgramWF hLookup
            have hProcFrameSafe :=
              ObserverSemantics.Program.procFrameSafe_of_lookup?
                hProgramFrameSafe hLookup
            have hProcCalls :=
              Structured.Program.procCallsResolved_of_lookup?
                hProgramWF hLookup
            rcases
                TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
                  hCompilerLookup hCompile with
              ⟨returnShape, output, hReturnShape, hCallType, hResult⟩
            subst result
            let site : TypedCfgCompiler.DispatchSite :=
              { procName := name
                token := Structured.Stmt.callToken supply
                returnLabel := regular
                caseLabel := .generated supply 10000 }
            have hSiteMem : site ∈ generated.calls := by
              apply hResultCalls site
              simp [site]
            rcases generated.procFragment_of_lookup? hLookup with
              ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
            let procCtx : TypedCfgCompiler.Context :=
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name)
                leaveShape? :=
                  some (TypedCfgCompiler.Shape.procExit proc) }
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body procCtx fragment.supply fragment.entry
                    fragment.input (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?, procCtx] using
                fragment.compile
            have hProcSupports :
                TypedCfgPreservation.OutcomeSimulation.ContextSupports
                  procCtx false false true := by
              exact
                { breakLabel := by simp
                  continueLabel := by simp
                  leaveLabel := by
                    intro _hAllowed
                    exact ⟨ProcLabel.exit proc.name, rfl⟩ }
            have hBodyPreserves :=
              outcome_block_of_compileFuel?_and_eval_with_calls
                (tokens := Structured.Stmt.callToken supply :: tokens)
                generated hFragmentCompile hFragmentBlocks hFragmentCalls
                hBody hProcWF.2.2 hProcFrameSafe hProcCalls
                hProcSupports (by rfl)
                hProgramWF hProgramFrameSafe
            have hName :=
              Structured.ProcList.name_of_lookup? hLookup
            have hFrameEq :=
              ObserverSemantics.CallStack.poppedFrame_eq_of_regular_eval
                hBody hPop
            obtain ⟨hSourcePop, hCursor⟩ :=
              ObserverSemantics.stateModel_popReturn?_eq_some hPop
            refine ⟨?_, ?_⟩
            · intro target trace hRel
              rcases
                  Call.entry_eventually_of_compileStmtFuel?
                    hCompilerLookup hCompile hBlocks hRel hSplit hProcWF with
                ⟨targetAtEntry, hCallEntry, hCallRel⟩
              have hAdapter :
                  TypedCfg.ObserverSemantics.Program.Eventually cfg
                    (ProcLabel.entry name) targetAtEntry trace
                    (.jump fragment.entry targetAtEntry) trace := by
                simpa [hName] using
                  Call.eventually_procEntry generated
                    (fragment := fragment) targetAtEntry trace
              rcases
                  hBodyPreserves.to_regular_path
                    targetAtEntry trace hCallRel with
                ⟨targetAtExit, traceAtExit,
                  hBodyEventually, hBodyRel⟩
              have hSiteProc : site.procName = proc.name := by
                simp [site, hName]
              have hRetc : frame.retc = proc.retc := by
                rw [hFrameEq]
              rcases
                  Call.dispatch_eventually generated hLookup hSiteProc
                    hSiteMem hBodyRel hSourcePop hCursor hAttach hRetc with
                ⟨targetFinal, hDispatchEventually, hFinalRel⟩
              refine ⟨.jump regular targetFinal, traceAtExit, ?_, ?_⟩
              · exact
                  TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                    hCallEntry
                    (TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                      hAdapter
                      (TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                        hBodyEventually hDispatchEventually))
              · exact
                  OutcomeSimulation.Rel.regular_iff.mpr
                    ⟨rfl, hFinalRel⟩
            · intro _hRegular
              exact ⟨returnShape, rfl⟩
        | @call_leave fuel name state proc args callerStack stack
            bodyState returned frame hLookup hSplit hBody hPop hAttach =>
            have hCompilerLookup :
                Structured.ProcList.lookup? name ctx.procs = some proc := by
              simpa [hProcs] using hLookup
            have hProcWF :=
              Structured.Program.procWF_of_lookup? hProgramWF hLookup
            have hProcFrameSafe :=
              ObserverSemantics.Program.procFrameSafe_of_lookup?
                hProgramFrameSafe hLookup
            have hProcCalls :=
              Structured.Program.procCallsResolved_of_lookup?
                hProgramWF hLookup
            rcases
                TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
                  hCompilerLookup hCompile with
              ⟨returnShape, output, hReturnShape, hCallType, hResult⟩
            subst result
            let site : TypedCfgCompiler.DispatchSite :=
              { procName := name
                token := Structured.Stmt.callToken supply
                returnLabel := regular
                caseLabel := .generated supply 10000 }
            have hSiteMem : site ∈ generated.calls := by
              apply hResultCalls site
              simp [site]
            rcases generated.procFragment_of_lookup? hLookup with
              ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
            let procCtx : TypedCfgCompiler.Context :=
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name)
                leaveShape? :=
                  some (TypedCfgCompiler.Shape.procExit proc) }
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body procCtx fragment.supply fragment.entry
                    fragment.input (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?, procCtx] using
                fragment.compile
            have hProcSupports :
                TypedCfgPreservation.OutcomeSimulation.ContextSupports
                  procCtx false false true := by
              exact
                { breakLabel := by simp
                  continueLabel := by simp
                  leaveLabel := by
                    intro _hAllowed
                    exact ⟨ProcLabel.exit proc.name, rfl⟩ }
            have hBodyPreserves :=
              outcome_block_of_compileFuel?_and_eval_with_calls
                (tokens := Structured.Stmt.callToken supply :: tokens)
                generated hFragmentCompile hFragmentBlocks hFragmentCalls
                hBody hProcWF.2.2 hProcFrameSafe hProcCalls
                hProcSupports (by rfl)
                hProgramWF hProgramFrameSafe
            have hName :=
              Structured.ProcList.name_of_lookup? hLookup
            have hFrameEq :=
              ObserverSemantics.CallStack.poppedFrame_eq_of_leave_eval
                hBody hPop
            obtain ⟨hSourcePop, hCursor⟩ :=
              ObserverSemantics.stateModel_popReturn?_eq_some hPop
            refine ⟨?_, ?_⟩
            · intro target trace hRel
              rcases
                  Call.entry_eventually_of_compileStmtFuel?
                    hCompilerLookup hCompile hBlocks hRel hSplit hProcWF with
                ⟨targetAtEntry, hCallEntry, hCallRel⟩
              have hAdapter :
                  TypedCfg.ObserverSemantics.Program.Eventually cfg
                    (ProcLabel.entry name) targetAtEntry trace
                    (.jump fragment.entry targetAtEntry) trace := by
                simpa [hName] using
                  Call.eventually_procEntry generated
                    (fragment := fragment) targetAtEntry trace
              have hBodyPath :=
                OutcomeSimulation.Path.to_leave
                  (program := cfg)
                  (targetLabel := ProcLabel.exit proc.name)
                  (by rfl) hBodyPreserves.1
              rcases hBodyPath targetAtEntry trace hCallRel with
                ⟨targetAtExit, traceAtExit,
                  hBodyEventually, hBodyRel⟩
              have hSiteProc : site.procName = proc.name := by
                simp [site, hName]
              have hRetc : frame.retc = proc.retc := by
                rw [hFrameEq]
              rcases
                  Call.dispatch_eventually generated hLookup hSiteProc
                    hSiteMem hBodyRel hSourcePop hCursor hAttach hRetc with
                ⟨targetFinal, hDispatchEventually, hFinalRel⟩
              refine ⟨.jump regular targetFinal, traceAtExit, ?_, ?_⟩
              · exact
                  TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                    hCallEntry
                    (TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                      hAdapter
                      (TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                        hBodyEventually hDispatchEventually))
              · exact
                  OutcomeSimulation.Rel.regular_iff.mpr
                    ⟨rfl, hFinalRel⟩
            · intro _hRegular
              exact ⟨returnShape, rfl⟩
        | @call_halt fuel name state proc args callerStack bodyState kind
            hLookup hSplit hBody =>
            have hCompilerLookup :
                Structured.ProcList.lookup? name ctx.procs = some proc := by
              simpa [hProcs] using hLookup
            have hProcWF :=
              Structured.Program.procWF_of_lookup? hProgramWF hLookup
            have hProcFrameSafe :=
              ObserverSemantics.Program.procFrameSafe_of_lookup?
                hProgramFrameSafe hLookup
            have hProcCalls :=
              Structured.Program.procCallsResolved_of_lookup?
                hProgramWF hLookup
            rcases generated.procFragment_of_lookup? hLookup with
              ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
            let procCtx : TypedCfgCompiler.Context :=
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name)
                leaveShape? :=
                  some (TypedCfgCompiler.Shape.procExit proc) }
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body procCtx fragment.supply fragment.entry
                    fragment.input (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?, procCtx] using
                fragment.compile
            have hProcSupports :
                TypedCfgPreservation.OutcomeSimulation.ContextSupports
                  procCtx false false true := by
              exact
                { breakLabel := by simp
                  continueLabel := by simp
                  leaveLabel := by
                    intro _hAllowed
                    exact ⟨ProcLabel.exit proc.name, rfl⟩ }
            have hBodyPreserves :=
              outcome_block_of_compileFuel?_and_eval_with_calls
                (tokens := Structured.Stmt.callToken supply :: tokens)
                generated hFragmentCompile hFragmentBlocks hFragmentCalls
                hBody hProcWF.2.2 hProcFrameSafe hProcCalls
                hProcSupports (by rfl)
                hProgramWF hProgramFrameSafe
            have hName :=
              Structured.ProcList.name_of_lookup? hLookup
            apply OutcomeSimulation.Preserves.of_path_of_nonregular
              (by simp)
            intro target trace hRel
            rcases
                Call.entry_eventually_of_compileStmtFuel?
                  hCompilerLookup hCompile hBlocks hRel hSplit hProcWF with
              ⟨targetAtEntry, hCallEntry, hCallRel⟩
            have hAdapter :
                TypedCfg.ObserverSemantics.Program.Eventually cfg
                  (ProcLabel.entry name) targetAtEntry trace
                  (.jump fragment.entry targetAtEntry) trace := by
              simpa [hName] using
                Call.eventually_procEntry generated
                  (fragment := fragment) targetAtEntry trace
            rcases hBodyPreserves.1 targetAtEntry trace hCallRel with
              ⟨targetOutcome, traceAtExit,
                hBodyEventually, hOutcomeRel⟩
            rcases OutcomeSimulation.Rel.halt_elim hOutcomeRel with
              ⟨targetBefore, targetFinal, rfl, hTargetStep, hFinalRel⟩
            refine ⟨.halt kind targetBefore, traceAtExit, ?_, ?_⟩
            · exact
                TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                  hCallEntry
                  (TypedCfg.ObserverSemantics.Program.Eventually.bind_jump
                    hAdapter hBodyEventually)
            · exact
                OutcomeSimulation.Rel.halt_iff.mpr
                  ⟨rfl, targetFinal, hTargetStep, hFinalRel⟩
        | terminal hStep =>
            exact
              Stmt.outcome_terminal_of_compileStmtFuel?
                hCompile hBlocks hStep
  termination_by sourceFuel
  decreasing_by
    all_goals simp_wf
    all_goals omega

end

namespace Program

/--
Checked generation preserves a complete observer-replayed Structured main
block through the generated TypedCfg program.
-/
theorem path_of_generateWithProcEntryShapes?_and_eval
    {transcript : Trace}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {sourceFuel : Nat}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes?
          sourceProgram entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hWF : sourceProgram.WF)
    (hFrameSafe : ObserverSemantics.Program.FrameSafe sourceProgram)
    (hEval :
      ObserverSemantics.Block.Eval sourceProgram sourceFuel
        sourceProgram.body source outcome) :
    OutcomeSimulation.Path cfg TypedCfgCompiler.entryLabel
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        { procs := sourceProgram.procs } ProcLabel.programEnd)
      source outcome [] := by
  let generated :=
    TypedCfgPreservation.Program.GeneratedContext.of_generate
      hGenerate hWellTyped
  have hMainCompile :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel sourceProgram.body + 1)
          sourceProgram.body { procs := sourceProgram.procs }
          0 TypedCfgCompiler.entryLabel TypedCfg.Shape.caller
          ProcLabel.programEnd =
        some generated.main := by
    simpa [TypedCfgCompiler.compileBlock?] using generated.mainCompile
  have hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        { procs := sourceProgram.procs } false false false := by
    exact
      { breakLabel := by simp
        continueLabel := by simp
        leaveLabel := by simp }
  exact
    (outcome_block_of_compileFuel?_and_eval_with_calls
      (tokens := []) generated hMainCompile generated.mainBlocks
      generated.mainCalls hEval hWF.2.2.2.2 hFrameSafe.2
      hWF.2.2.2.1 hSupports (by rfl) hWF hFrameSafe).1

/--
Artifact-facing observer preservation with the generated well-typedness proof
recovered from the existing compiler check.
-/
theorem path_of_artifactWithProcEntryShapes?_and_eval
    {transcript : Trace}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {artifact : TypedCfgCompiler.CompileArtifact}
    {source : ObserverSemantics.State transcript}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    {sourceFuel : Nat}
    (hArtifact :
      TypedCfgCompiler.artifactWithProcEntryShapes?
          sourceProgram entryShapes =
        some artifact)
    (hWF : sourceProgram.WF)
    (hFrameSafe : ObserverSemantics.Program.FrameSafe sourceProgram)
    (hEval :
      ObserverSemantics.Block.Eval sourceProgram sourceFuel
        sourceProgram.body source outcome) :
    OutcomeSimulation.Path artifact.cfg TypedCfgCompiler.entryLabel
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        { procs := sourceProgram.procs } ProcLabel.programEnd)
      source outcome [] := by
  unfold TypedCfgCompiler.artifactWithProcEntryShapes? at hArtifact
  cases hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes?
        sourceProgram entryShapes with
  | none =>
      simp [hGenerate] at hArtifact
  | some cfg =>
      by_cases hCheck : cfg.wellTyped? = true
      · simp [hGenerate, hCheck] at hArtifact
        cases hArtifact
        exact
          path_of_generateWithProcEntryShapes?_and_eval
            hGenerate
            (TypedCfg.Program.wellTyped_of_check hCheck)
            hWF hFrameSafe hEval
      · simp [hGenerate, hCheck] at hArtifact

end Program

end ObserverPreservation
end Structured
end EvmCompiler
