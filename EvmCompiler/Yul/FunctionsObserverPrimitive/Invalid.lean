import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

theorem forwardAt_invalid
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAt codeRel fuel (.System .INVALID) .invalid := by
  intro source source' target sourceValues outputs hRel hCall
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      simp [EvmYul.Yul.primCall] at hCall
      unfold EvmYul.step at hCall
      change
        Except.error EvmYul.Yul.Exception.InvalidInstruction =
          Except.ok (source', outputs) at hCall
      cases hCall

theorem backwardAt_invalid
    {codeRel : StateRelation.CodeRel} (fuel : Nat) :
    BackwardAt codeRel (fuel + 1)
      (.System .INVALID) .invalid := by
  intro source target targetShared sourceValues outputs
    hRel _hPermitted hRun
  by_cases hLength :
      sourceValues.length =
        Expressions.Structured.BasicOp.inputs .invalid
  all_goals
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Structured.invalid, hLength] at hRun

theorem rawNoObservableFailure_invalid
    {fuel : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {values : List Word} {exception : EvmYul.Yul.Exception}
    (hRun :
      EvmYul.Yul.primCall fuel (.Ok sourceShared sourceVars)
          (.System .INVALID) values =
        .error exception) :
    ¬Yul.Source.Effectful.Exception.Observable exception := by
  intro hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      have hDispatch :
          EvmYul.Yul.primCall previous.succ
              (.Ok sourceShared sourceVars)
              (.System .INVALID) values =
            .error .InvalidInstruction := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hRun
      injection hRun with hRun
      rw [← hRun] at hObservable
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem safeInvalid
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
            (.System .INVALID) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .invalid target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    (fun _ => by trivial)
    forwardAt_invalid hRel hRun

theorem safeInvalidBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .invalid target
          sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval (fuel + 2) source
            (.System .INVALID) sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  simpa using
    (safeBasicOpBackward (by rfl) (by rfl) (by rfl) (by rfl)
      (backwardAt_invalid (codeRel := codeRel) fuel) hRel hRun)

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
