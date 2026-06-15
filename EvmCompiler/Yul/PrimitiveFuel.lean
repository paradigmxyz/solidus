import EvmCompiler.Yul.Primitive
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul
namespace Prim

/-!
The imported Yul primitive interpreter uses recursive fuel only for external
call/create operations. Every ordinary primitive selected by the compiler is
therefore invariant across positive fuel once those external operations are
excluded.
-/

set_option maxHeartbeats 2000000 in
theorem primCall_succ_eq_of_nonExternal
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hOp : toUncheckedBasicOp? prim = some op)
    (hNonExternal : op.toPrimOp.isExternalCallCreate = false)
    (leftFuel rightFuel : Nat) (state : EvmYul.Yul.State)
    (args : List Assembly.Word) :
    EvmYul.Yul.primCall leftFuel.succ state prim args =
      EvmYul.Yul.primCall rightFuel.succ state prim args := by
  cases prim <;> rename_i primitive <;> cases primitive
  all_goals
    simp [toUncheckedBasicOp?, toBasicOp?] at hOp
  all_goals
    subst op
  all_goals
    simp [Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isExternalCallCreate] at hNonExternal
  all_goals
    simp [EvmYul.Yul.primCall]

end Prim
end Yul
end EvmCompiler
