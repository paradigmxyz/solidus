import EvmCompiler.Solidity.RawAst
import EvmCompiler.Yul.InteractionSemantics

/-!
Semantic interface lemmas for generated raw-frontend normalizations.

`Solidity.RawAst` owns decoding and elaboration and intentionally stops at
`Solidity.Frontend.Program`.  This module is the adjacent proof bridge into the
Yul source semantics for generated frontend-owned code.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace Elab

theorem clzHelperYulInterface_call_succ
    {object : Frontend.Object} {ordered : Yul.OrderedProgram}
    {helper? arg? ret? : Option Name}
    (hInterface :
      ClzHelperYulInterface object.functions helper? arg? ret?)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered)
    (fuel : Nat) (args : List Word)
    (state : Yul.InteractionSemantics.State) :
    match helper?, arg?, ret? with
    | some helper, some arg, some ret =>
        Yul.InteractionSemantics.call (fuel + 1) args
            (some helper) (some ordered.program.contract) state =
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block (clzHelperAstBody arg ret))
              (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (state.initcall [arg] [ret] args)))
            (fun stateAfterBody =>
              pure
                ((stateAfterBody.reviveJump.overwrite? state).setStore state,
                  List.map stateAfterBody.lookup! [ret]))
    | _, _, _ => True := by
  have hLookup :=
    clzHelperYulInterface_orderedLookup
      (object := object) (ordered := ordered)
      (helper? := helper?) (arg? := arg?) (ret? := ret?)
      hInterface hConvert
  cases helper? <;> cases arg? <;> cases ret? <;> simp at hLookup ⊢
  rename_i helper arg ret
  have hLookupDef :
      ordered.program.contract.functions.lookup helper =
        some
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            [arg] [ret] (clzHelperAstBody arg ret)) := by
    simpa [clzHelperAstFunctionDef] using hLookup
  exact
    Yul.InteractionSemantics.Call.explicit_succ
      fuel args helper ordered.program.contract
      [arg] [ret] (clzHelperAstBody arg ret) state hLookupDef

end Elab
end RawAst
end Solidity
end EvmCompiler
