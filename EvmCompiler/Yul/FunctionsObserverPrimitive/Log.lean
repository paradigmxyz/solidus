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

private theorem targetPermitted_of_log_succ
    {fuel : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {target : Locals.Source.State}
    {prim : EvmYul.Operation .Yul}
    {sourceValues outputs : List Word}
    {source' : EvmYul.Yul.State}
    (hPermissionRel :
      sourceShared.executionEnv.perm =
        target.shared.executionEnv.perm)
    (hStaticError :
      sourceShared.executionEnv.perm = false →
        EvmYul.Yul.primCall fuel.succ
            (.Ok sourceShared sourceVars) prim sourceValues =
          .error .StaticModeViolation)
    (hRun :
      EvmYul.Yul.primCall fuel.succ
          (.Ok sourceShared sourceVars) prim sourceValues =
        .ok (source', outputs)) :
    target.shared.executionEnv.perm = true := by
  cases hPermission : sourceShared.executionEnv.perm with
  | false =>
      rw [hStaticError hPermission] at hRun
      cases hRun
  | true =>
      simpa [hPermission] using hPermissionRel.symm

theorem LogFamily.targetPermitted_of_run
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    {source source' : EvmYul.Yul.State}
    {target : Locals.Source.State}
    {sourceValues outputs : List Word}
    (hFamily : LogFamily prim op arity)
    (hRel : StateRelation.Regular.Rel codeRel source target)
    (hRun :
      EvmYul.Yul.primCall fuel source prim sourceValues =
        .ok (source', outputs)) :
    Functions.ObserverSafety.PrimitivePermitted op target.shared := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
  | succ previous =>
      cases hFamily with
      | log0 =>
          refine targetPermitted_of_log_succ
            hShared.world.executionEnv.permission ?_ hRun
          intro hPermission
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [EvmYul.Yul.State.executionEnv, hPermission]
          rfl
      | log1 =>
          refine targetPermitted_of_log_succ
            hShared.world.executionEnv.permission ?_ hRun
          intro hPermission
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [EvmYul.Yul.State.executionEnv, hPermission]
          rfl
      | log2 =>
          refine targetPermitted_of_log_succ
            hShared.world.executionEnv.permission ?_ hRun
          intro hPermission
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [EvmYul.Yul.State.executionEnv, hPermission]
          rfl
      | log3 =>
          refine targetPermitted_of_log_succ
            hShared.world.executionEnv.permission ?_ hRun
          intro hPermission
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [EvmYul.Yul.State.executionEnv, hPermission]
          rfl
      | log4 =>
          refine targetPermitted_of_log_succ
            hShared.world.executionEnv.permission ?_ hRun
          intro hPermission
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [EvmYul.Yul.State.executionEnv, hPermission]
          rfl

theorem LogFamily.sourceRun_of_arity
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {sourceValues : List Word}
    (hFamily : LogFamily prim op arity)
    (hPermission : sourceShared.executionEnv.perm = true)
    (hArity : sourceValues.length = arity) :
    ∃ sourceAfter,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok sourceShared sourceVars) prim sourceValues =
        .ok (sourceAfter, []) := by
  cases hFamily with
  | log0 =>
      obtain ⟨address, size, rfl⟩ :=
        List.length_eq_two.mp hArity
      refine
        ⟨.Ok
            (EvmYul.SharedState.logOp
              address size #[] sourceShared)
            sourceVars,
          ?_⟩
      simp [EvmYul.Yul.primCall]
      unfold EvmYul.step
      simp [EvmYul.Yul.State.executionEnv, hPermission]
      change
        Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[] sourceShared)
              sourceVars,
              []) =
          Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[] sourceShared)
              sourceVars,
              [])
      rfl
  | log1 =>
      obtain ⟨address, size, topic0, rfl⟩ :=
        List.length_eq_three.mp hArity
      refine
        ⟨.Ok
            (EvmYul.SharedState.logOp
              address size #[topic0] sourceShared)
            sourceVars,
          ?_⟩
      simp [EvmYul.Yul.primCall]
      unfold EvmYul.step
      simp [EvmYul.Yul.State.executionEnv, hPermission]
      change
        Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0] sourceShared)
              sourceVars,
              []) =
          Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0] sourceShared)
              sourceVars,
              [])
      rfl
  | log2 =>
      obtain ⟨address, size, topic0, topic1, rfl⟩ :=
        list_eq_four_of_length_eq hArity
      refine
        ⟨.Ok
            (EvmYul.SharedState.logOp
              address size #[topic0, topic1] sourceShared)
            sourceVars,
          ?_⟩
      simp [EvmYul.Yul.primCall]
      unfold EvmYul.step
      simp [EvmYul.Yul.State.executionEnv, hPermission]
      change
        Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0, topic1] sourceShared)
              sourceVars,
              []) =
          Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0, topic1] sourceShared)
              sourceVars,
              [])
      rfl
  | log3 =>
      obtain ⟨address, size, topic0, topic1, topic2, rfl⟩ :=
        list_eq_five_of_length_eq hArity
      refine
        ⟨.Ok
            (EvmYul.SharedState.logOp
              address size #[topic0, topic1, topic2] sourceShared)
            sourceVars,
          ?_⟩
      simp [EvmYul.Yul.primCall]
      unfold EvmYul.step
      simp [EvmYul.Yul.State.executionEnv, hPermission]
      change
        Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0, topic1, topic2] sourceShared)
              sourceVars,
              []) =
          Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0, topic1, topic2] sourceShared)
              sourceVars,
              [])
      rfl
  | log4 =>
      obtain
          ⟨address, size, topic0, topic1, topic2, topic3, rfl⟩ :=
        list_eq_six_of_length_eq hArity
      refine
        ⟨.Ok
            (EvmYul.SharedState.logOp
              address size #[topic0, topic1, topic2, topic3]
              sourceShared)
            sourceVars,
          ?_⟩
      simp [EvmYul.Yul.primCall]
      unfold EvmYul.step
      simp [EvmYul.Yul.State.executionEnv, hPermission]
      change
        Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0, topic1, topic2, topic3]
                sourceShared)
              sourceVars,
              []) =
          Except.ok
            (EvmYul.Yul.State.Ok
              (EvmYul.SharedState.logOp
                address size #[topic0, topic1, topic2, topic3]
                sourceShared)
              sourceVars,
              [])
      rfl

private theorem rawNoObservableFailure_log_succ
    {fuel : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {prim : EvmYul.Operation .Yul} {values : List Word}
    {result : EvmYul.Yul.State × List Word}
    {exception : EvmYul.Yul.Exception}
    (hDispatch :
      EvmYul.Yul.primCall fuel.succ
          (.Ok sourceShared sourceVars) prim values =
        if sourceShared.executionEnv.perm = false then
          .error .StaticModeViolation
        else
          .ok result)
    (hRun :
      EvmYul.Yul.primCall fuel.succ
          (.Ok sourceShared sourceVars) prim values =
        .error exception) :
    ¬Yul.Source.Effectful.Exception.Observable exception := by
  intro hObservable
  rw [hDispatch] at hRun
  cases hPermission : sourceShared.executionEnv.perm with
  | false =>
      simp [hPermission] at hRun
      rw [← hRun] at hObservable
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | true =>
      simp [hPermission] at hRun

theorem LogFamily.rawNoObservableFailure
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {values : List Word} {exception : EvmYul.Yul.Exception}
    (hFamily : LogFamily prim op arity)
    (hArity : values.length = arity)
    (hRun :
      EvmYul.Yul.primCall fuel (.Ok sourceShared sourceVars)
          prim values =
        .error exception) :
    ¬Yul.Source.Effectful.Exception.Observable exception := by
  cases fuel with
  | zero =>
      intro hObservable
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      cases hFamily with
      | log0 =>
          obtain ⟨address, size, rfl⟩ :=
            List.length_eq_two.mp hArity
          apply rawNoObservableFailure_log_succ
            (result :=
              (.Ok
                (EvmYul.SharedState.logOp
                  address size #[] sourceShared)
                sourceVars,
                [])) _ hRun
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          rfl
      | log1 =>
          obtain ⟨address, size, topic0, rfl⟩ :=
            List.length_eq_three.mp hArity
          apply rawNoObservableFailure_log_succ
            (result :=
              (.Ok
                (EvmYul.SharedState.logOp
                  address size #[topic0] sourceShared)
                sourceVars,
                [])) _ hRun
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          rfl
      | log2 =>
          obtain ⟨address, size, topic0, topic1, rfl⟩ :=
            list_eq_four_of_length_eq hArity
          apply rawNoObservableFailure_log_succ
            (result :=
              (.Ok
                (EvmYul.SharedState.logOp
                  address size #[topic0, topic1] sourceShared)
                sourceVars,
                [])) _ hRun
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          rfl
      | log3 =>
          obtain ⟨address, size, topic0, topic1, topic2, rfl⟩ :=
            list_eq_five_of_length_eq hArity
          apply rawNoObservableFailure_log_succ
            (result :=
              (.Ok
                (EvmYul.SharedState.logOp
                  address size #[topic0, topic1, topic2] sourceShared)
                sourceVars,
                [])) _ hRun
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          rfl
      | log4 =>
          obtain
              ⟨address, size, topic0, topic1, topic2, topic3, rfl⟩ :=
            list_eq_six_of_length_eq hArity
          apply rawNoObservableFailure_log_succ
            (result :=
              (.Ok
                (EvmYul.SharedState.logOp address size
                  #[topic0, topic1, topic2, topic3] sourceShared)
                sourceVars,
                [])) _ hRun
          simp [EvmYul.Yul.primCall]
          unfold EvmYul.step
          rfl

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

theorem backwardAt_of_logFamily
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity) :
    BackwardAt codeRel (fuel + 1) prim op := by
  intro source target targetShared sourceValues outputs
    hRel hPermitted hRun
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain ⟨hInputs, _⟩ := hFamily.metadata
  have hInputLength :
      sourceValues.length =
        Expressions.Structured.BasicOp.inputs op := by
    by_contra hLength
    simp [Locals.Source.PrimitiveSemantics.structured,
      hLength, Structured.invalid] at hRun
  have hArity : sourceValues.length = arity := by
    simpa [hInputs] using hInputLength
  have hTargetPermission :
      target.shared.executionEnv.perm = true := by
    cases hFamily <;>
      simpa [Functions.ObserverSafety.PrimitivePermitted] using
        hPermitted
  have hSourcePermission :
      sourceShared.executionEnv.perm = true := by
    rw [hShared.world.executionEnv.permission]
    exact hTargetPermission
  obtain ⟨sourceAfter, hSourceRun⟩ :=
    hFamily.sourceRun_of_arity
      (fuel := fuel) hSourcePermission hArity
  have hInputArity :
      sourceValues.length =
        Expressions.Structured.BasicOp.inputs op := by
    simpa [hInputs] using hArity
  obtain
      ⟨expectedShared, hExpected, hFinalRel, hStore⟩ :=
    forwardAtArity_of_logFamily
      (codeRel := codeRel) (fuel := fuel + 1) hFamily
      (show
        StateRelation.Regular.Rel codeRel
          (.Ok sourceShared sourceVars) target from
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)
      hInputArity hSourceRun
  rw [hExpected] at hRun
  have hPair := Except.ok.inj hRun
  have hSharedEq := congrArg Prod.fst hPair
  have hOutputsEq := congrArg Prod.snd hPair
  change expectedShared = targetShared at hSharedEq
  change [] = outputs at hOutputsEq
  subst targetShared
  subst outputs
  exact ⟨sourceAfter, hSourceRun, hFinalRel, hStore⟩

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
      (fun hRaw =>
        hFamily.targetPermitted_of_run hRel.2 hRaw)
      (forwardAtArity_of_logFamily hFamily)
      (by simpa [hInputs] using hArity) hRel hRun

theorem safeLogBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {arity : Nat}
    {sourceValues outputs : List Word}
    (hFamily : LogFamily prim op arity)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval 2 source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  obtain ⟨_hInputs, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  simpa using
    (safeBasicOpBackward hYulObserver hFunctionsObserver hTerminal hOp
      (backwardAt_of_logFamily
        (codeRel := codeRel) 0 hFamily)
      hRel hRun)

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
