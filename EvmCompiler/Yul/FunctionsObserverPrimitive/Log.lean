import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

inductive LogFamily :
    EvmYul.Operation .Yul → Structured.BasicOp → Nat → Prop where
  | log0 : LogFamily (.Log .LOG0) .log0 2
  | log1 : LogFamily (.Log .LOG1) .log1 3
  | log2 : LogFamily (.Log .LOG2) .log2 4
  | log3 : LogFamily (.Log .LOG3) .log3 5
  | log4 : LogFamily (.Log .LOG4) .log4 6

theorem LogFamily.metadata
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity) :
    Expressions.Structured.BasicOp.inputs op = arity ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem forwardAtArity_log0
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel (.Log .LOG0) .log0 := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Log .LOG0) sourceValues =
            if sourceShared.executionEnv.perm = false then
              .error .StaticModeViolation
            else
              (match EvmYul.Yul.log0Op
                  (.Ok sourceShared sourceVars) sourceValues with
              | .ok (state, value?) => .ok (state, value?.toList)
              | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
      | true =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
          have hInputs :
              Expressions.Structured.BasicOp.inputs .log0 = 2 := rfl
          have hStep :
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?
                  .log0 =
                some .log0 := rfl
          cases sourceValues with
          | nil =>
              simp [hInputs] at hArity
          | cons address rest =>
              cases rest with
              | nil =>
                  simp [hInputs] at hArity
              | cons size extra =>
                  cases extra with
                  | cons head tail =>
                      simp [hInputs] at hArity
                  | nil =>
                      change
                        Except.ok
                            (.Ok
                              (EvmYul.SharedState.logOp
                                address size #[] sourceShared)
                              sourceVars,
                              []) =
                          Except.ok (source', outputs) at hCall
                      rcases hCall with ⟨rfl, rfl⟩
                      let targetShared :=
                        EvmYul.SharedState.logOp
                          address size #[] target.shared
                      refine ⟨targetShared, ?_, ?_, by rfl⟩
                      · simp [
                          Locals.Source.PrimitiveSemantics.structured,
                          hInputs, hStep, Assembly.PrimStep.run,
                          EvmYul.Stack.pop2,
                          EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC,
                          targetShared, Id.run]
                      · exact
                          ⟨EvmYul.SharedState.logOp
                              address size #[] sourceShared,
                            sourceVars, rfl,
                            StateRelation.Shared.logOp hShared
                              address size #[],
                            hVars⟩

theorem forwardAtArity_log1
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel (.Log .LOG1) .log1 := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Log .LOG1) sourceValues =
            if sourceShared.executionEnv.perm = false then
              .error .StaticModeViolation
            else
              (match EvmYul.Yul.log1Op
                  (.Ok sourceShared sourceVars) sourceValues with
              | .ok (state, value?) => .ok (state, value?.toList)
              | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
      | true =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
          have hInputs :
              Expressions.Structured.BasicOp.inputs .log1 = 3 := rfl
          have hStep :
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?
                  .log1 =
                some .log1 := rfl
          cases sourceValues with
          | nil =>
              simp [hInputs] at hArity
          | cons address rest =>
              cases rest with
              | nil =>
                  simp [hInputs] at hArity
              | cons size rest =>
                  cases rest with
                  | nil =>
                      simp [hInputs] at hArity
                  | cons topic0 extra =>
                      cases extra with
                      | cons head tail =>
                          simp [hInputs] at hArity
                      | nil =>
                          change
                            Except.ok
                                (.Ok
                                  (EvmYul.SharedState.logOp
                                    address size #[topic0] sourceShared)
                                  sourceVars,
                                  []) =
                              Except.ok (source', outputs) at hCall
                          rcases hCall with ⟨rfl, rfl⟩
                          let targetShared :=
                            EvmYul.SharedState.logOp
                              address size #[topic0] target.shared
                          refine ⟨targetShared, ?_, ?_, by rfl⟩
                          · simp [
                              Locals.Source.PrimitiveSemantics.structured,
                              hInputs, hStep, Assembly.PrimStep.run,
                              EvmYul.Stack.pop3,
                              EvmYul.EVM.State.replaceStackAndIncrPC,
                              EvmYul.EVM.State.incrPC,
                              targetShared, Id.run]
                          · exact
                              ⟨EvmYul.SharedState.logOp
                                  address size #[topic0] sourceShared,
                                sourceVars, rfl,
                                StateRelation.Shared.logOp hShared
                                  address size #[topic0],
                                hVars⟩

theorem forwardAtArity_log2
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel (.Log .LOG2) .log2 := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Log .LOG2) sourceValues =
            if sourceShared.executionEnv.perm = false then
              .error .StaticModeViolation
            else
              (match EvmYul.Yul.log2Op
                  (.Ok sourceShared sourceVars) sourceValues with
              | .ok (state, value?) => .ok (state, value?.toList)
              | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
      | true =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
          have hInputs :
              Expressions.Structured.BasicOp.inputs .log2 = 4 := rfl
          have hStep :
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?
                  .log2 =
                some .log2 := rfl
          cases sourceValues with
          | nil =>
              simp [hInputs] at hArity
          | cons address rest =>
              cases rest with
              | nil =>
                  simp [hInputs] at hArity
              | cons size rest =>
                  cases rest with
                  | nil =>
                      simp [hInputs] at hArity
                  | cons topic0 rest =>
                      cases rest with
                      | nil =>
                          simp [hInputs] at hArity
                      | cons topic1 extra =>
                          cases extra with
                          | cons head tail =>
                              simp [hInputs] at hArity
                          | nil =>
                              change
                                Except.ok
                                    (.Ok
                                      (EvmYul.SharedState.logOp
                                        address size #[topic0, topic1]
                                        sourceShared)
                                      sourceVars,
                                      []) =
                                  Except.ok (source', outputs) at hCall
                              rcases hCall with ⟨rfl, rfl⟩
                              let targetShared :=
                                EvmYul.SharedState.logOp
                                  address size #[topic0, topic1]
                                  target.shared
                              refine ⟨targetShared, ?_, ?_, by rfl⟩
                              · simp [
                                  Locals.Source.PrimitiveSemantics.structured,
                                  hInputs, hStep, Assembly.PrimStep.run,
                                  EvmYul.Stack.pop4,
                                  EvmYul.EVM.State.replaceStackAndIncrPC,
                                  EvmYul.EVM.State.incrPC,
                                  targetShared, Id.run]
                              · exact
                                  ⟨EvmYul.SharedState.logOp
                                      address size #[topic0, topic1]
                                      sourceShared,
                                    sourceVars, rfl,
                                    StateRelation.Shared.logOp hShared
                                      address size #[topic0, topic1],
                                    hVars⟩

theorem forwardAtArity_log3
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel (.Log .LOG3) .log3 := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Log .LOG3) sourceValues =
            if sourceShared.executionEnv.perm = false then
              .error .StaticModeViolation
            else
              (match EvmYul.Yul.log3Op
                  (.Ok sourceShared sourceVars) sourceValues with
              | .ok (state, value?) => .ok (state, value?.toList)
              | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
      | true =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
          have hInputs :
              Expressions.Structured.BasicOp.inputs .log3 = 5 := rfl
          have hStep :
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?
                  .log3 =
                some .log3 := rfl
          cases sourceValues with
          | nil =>
              simp [hInputs] at hArity
          | cons address rest =>
              cases rest with
              | nil =>
                  simp [hInputs] at hArity
              | cons size rest =>
                  cases rest with
                  | nil =>
                      simp [hInputs] at hArity
                  | cons topic0 rest =>
                      cases rest with
                      | nil =>
                          simp [hInputs] at hArity
                      | cons topic1 rest =>
                          cases rest with
                          | nil =>
                              simp [hInputs] at hArity
                          | cons topic2 extra =>
                              cases extra with
                              | cons head tail =>
                                  simp [hInputs] at hArity
                              | nil =>
                                  change
                                    Except.ok
                                        (.Ok
                                          (EvmYul.SharedState.logOp
                                            address size
                                            #[topic0, topic1, topic2]
                                            sourceShared)
                                          sourceVars,
                                          []) =
                                      Except.ok
                                        (source', outputs) at hCall
                                  rcases hCall with ⟨rfl, rfl⟩
                                  let targetShared :=
                                    EvmYul.SharedState.logOp
                                      address size
                                      #[topic0, topic1, topic2]
                                      target.shared
                                  refine ⟨targetShared, ?_, ?_, by rfl⟩
                                  · simp [
                                      Locals.Source.PrimitiveSemantics.structured,
                                      hInputs, hStep,
                                      Assembly.PrimStep.run,
                                      EvmYul.Stack.pop5,
                                      EvmYul.EVM.State.replaceStackAndIncrPC,
                                      EvmYul.EVM.State.incrPC,
                                      targetShared, Id.run]
                                  · exact
                                      ⟨EvmYul.SharedState.logOp
                                          address size
                                          #[topic0, topic1, topic2]
                                          sourceShared,
                                        sourceVars, rfl,
                                        StateRelation.Shared.logOp hShared
                                          address size
                                          #[topic0, topic1, topic2],
                                        hVars⟩

theorem forwardAtArity_log4
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel (.Log .LOG4) .log4 := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Log .LOG4) sourceValues =
            if sourceShared.executionEnv.perm = false then
              .error .StaticModeViolation
            else
              (match EvmYul.Yul.log4Op
                  (.Ok sourceShared sourceVars) sourceValues with
              | .ok (state, value?) => .ok (state, value?.toList)
              | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
      | true =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
          have hInputs :
              Expressions.Structured.BasicOp.inputs .log4 = 6 := rfl
          have hStep :
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?
                  .log4 =
                some .log4 := rfl
          cases sourceValues with
          | nil =>
              simp [hInputs] at hArity
          | cons address rest =>
              cases rest with
              | nil =>
                  simp [hInputs] at hArity
              | cons size rest =>
                  cases rest with
                  | nil =>
                      simp [hInputs] at hArity
                  | cons topic0 rest =>
                      cases rest with
                      | nil =>
                          simp [hInputs] at hArity
                      | cons topic1 rest =>
                          cases rest with
                          | nil =>
                              simp [hInputs] at hArity
                          | cons topic2 rest =>
                              cases rest with
                              | nil =>
                                  simp [hInputs] at hArity
                              | cons topic3 extra =>
                                  cases extra with
                                  | cons head tail =>
                                      simp [hInputs] at hArity
                                  | nil =>
                                      change
                                        Except.ok
                                            (.Ok
                                              (EvmYul.SharedState.logOp
                                                address size
                                                #[topic0, topic1, topic2,
                                                  topic3]
                                                sourceShared)
                                              sourceVars,
                                              []) =
                                          Except.ok
                                            (source', outputs) at hCall
                                      rcases hCall with ⟨rfl, rfl⟩
                                      let targetShared :=
                                        EvmYul.SharedState.logOp
                                          address size
                                          #[topic0, topic1, topic2, topic3]
                                          target.shared
                                      refine ⟨targetShared, ?_, ?_, by rfl⟩
                                      · simp [
                                          Locals.Source.PrimitiveSemantics.structured,
                                          hInputs, hStep,
                                          Assembly.PrimStep.run,
                                          EvmYul.Stack.pop6,
                                          EvmYul.EVM.State.replaceStackAndIncrPC,
                                          EvmYul.EVM.State.incrPC,
                                          targetShared, Id.run]
                                      · exact
                                          ⟨EvmYul.SharedState.logOp
                                              address size
                                              #[topic0, topic1, topic2,
                                                topic3]
                                              sourceShared,
                                            sourceVars, rfl,
                                            StateRelation.Shared.logOp hShared
                                              address size
                                              #[topic0, topic1, topic2,
                                                topic3],
                                            hVars⟩

theorem forwardAtArity_of_logFamily
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity) :
    ForwardAtArity codeRel fuel prim op := by
  cases hFamily with
  | log0 => exact forwardAtArity_log0
  | log1 => exact forwardAtArity_log1
  | log2 => exact forwardAtArity_log2
  | log3 => exact forwardAtArity_log3
  | log4 => exact forwardAtArity_log4

theorem safeLog
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    {sourceValues outputs : List Word}
    (hFamily : LogFamily prim op arity)
    (hArity : sourceValues.length = arity)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  obtain ⟨hInputs, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOpArity hYulObserver hFunctionsObserver hTerminal hOp
      (forwardAtArity_of_logFamily hFamily)
      (by simpa [hInputs] using hArity) hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
