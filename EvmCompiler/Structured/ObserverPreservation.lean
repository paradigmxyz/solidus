import EvmCompiler.Simulation.ObserverPass
import EvmCompiler.Structured.ObserverSemantics
import EvmCompiler.Structured.TypedCfgPreservation.Core
import EvmCompiler.TypedCfg.ObserverSemantics

namespace EvmCompiler
namespace Structured
namespace ObserverPreservation

abbrev Trace := Assembly.ResourceTrace

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

theorem symm
    {transcript : Trace}
    {left right : ObserverSemantics.State transcript}
    (hRel : ReplayStateRel left right) :
    ReplayStateRel right left :=
  ⟨hRel.cursor.symm,
    hRel.source.1.symm,
    Assembly.SameRuntimeData.symm hRel.source.2⟩

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

end Code

namespace StateRel

theorem initial (state : EVMState) (transcript : Trace) :
    StateRel
      (transcript := transcript)
      { source := RunState.initial state }
      [] state transcript := by
  exact
    ⟨TypedCfgPreservation.StateRel.initial state,
      by simp [Simulation.ResourceReplay.State.remaining]⟩

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
  have hFind := hBlocks block hMem
  refine ⟨1, ?_⟩
  rw [TypedCfg.EffectSemantics.Program.runN_succ]
  change
    TypedCfg.EffectSemantics.Block.run
        TypedCfg.ObserverSemantics.Instr.handler
        block state trace =
      .ok (outcome, trace') at hRun
  unfold TypedCfg.EffectSemantics.Program.step
  rw [hFind]
  simp only
  rw [hRun]
  cases outcome <;> rfl

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
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
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
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
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
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
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
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
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
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
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

end Stmt

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

end ObserverPreservation
end Structured
end EvmCompiler
