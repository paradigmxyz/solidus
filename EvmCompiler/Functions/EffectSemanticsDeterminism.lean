import EvmCompiler.Functions.EffectSemantics

namespace EvmCompiler
namespace Functions
namespace Source
namespace Effectful
namespace Program

/-!
Cross-fuel determinism for the canonical Functions whole-program semantics.

This is a semantic property of the existing interpreter, not a compiler
backward simulation. It lets higher adjacent passes compare a forward-produced
run with a concrete run of the same Functions program.
-/

theorem runState_success_unique {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {leftFuel rightFuel : Nat} {source : σ}
    {leftOutcome rightOutcome : Outcome σ}
    (hLeft :
      runState model prim leftFuel program source =
        .ok leftOutcome)
    (hRight :
      runState model prim rightFuel program source =
        .ok rightOutcome) :
    leftOutcome = rightOutcome := by
  let commonFuel := Nat.max leftFuel rightFuel
  have hLeft' :
      runState model prim commonFuel program source =
        .ok leftOutcome :=
    Block.runScoped_mono model prim program
      (Nat.le_max_left _ _) hLeft
  have hRight' :
      runState model prim commonFuel program source =
        .ok rightOutcome :=
    Block.runScoped_mono model prim program
      (Nat.le_max_right _ _) hRight
  rw [hLeft'] at hRight'
  exact Except.ok.inj hRight'

end Program
end Effectful
end Source
end Functions
end EvmCompiler
