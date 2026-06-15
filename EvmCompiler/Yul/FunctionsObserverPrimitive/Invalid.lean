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
      StateRelation.Replay.Rel codeRel source' target' :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAt_invalid hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
