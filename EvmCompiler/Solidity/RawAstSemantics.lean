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

@[simp] private theorem open_bind_pure_left
    {α β : Type} (value : α)
    (next : α → Yul.InteractionSemantics.Open β) :
    Simulation.Interaction.bind (pure value) next = next value := rfl

theorem clzHelperZeroEntry_insertRet_lookupArg
    (arg ret : Name) (hArgRet : arg ≠ ret)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    let entry :=
      EvmYul.Yul.State.mkOk
        ((EvmYul.Yul.State.Ok shared store).initcall
          [arg] [ret] [EvmYul.UInt256.ofNat 0])
    (entry.insert ret (EvmYul.UInt256.ofNat 256)).lookup? arg =
      some (EvmYul.UInt256.ofNat 0) := by
  intro entry
  simp [entry, EvmYul.Yul.State.initcall, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup?,
    hArgRet, Finmap.lookup_insert_of_ne]

theorem clzHelperZeroEntry_checkAssignRet
    (arg ret : Name) (hArgRet : arg ≠ ret)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    let entry :=
      EvmYul.Yul.State.mkOk
        ((EvmYul.Yul.State.Ok shared store).initcall
          [arg] [ret] [EvmYul.UInt256.ofNat 0])
    EvmYul.Yul.checkAssignment entry [ret] = .ok () := by
  intro entry
  have hRetArg : ret ≠ arg := fun h => hArgRet h.symm
  simp [entry, EvmYul.Yul.State.initcall, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup?,
    EvmYul.Yul.checkAssignment, EvmYul.Yul.firstUndeclared?,
    EvmYul.Yul.firstDuplicate?, hRetArg, Finmap.lookup_insert_of_ne]

theorem clzHelperAstBody_zero_exec
    (fuel : Nat) (arg ret : Name) (hArgRet : arg ≠ ret)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    let entry :=
      EvmYul.Yul.State.mkOk
        ((EvmYul.Yul.State.Ok shared store).initcall
          [arg] [ret] [EvmYul.UInt256.ofNat 0])
    Yul.InteractionSemantics.exec (fuel + 20)
        (.Block (clzHelperAstBody arg ret)) code entry =
      pure
        ((entry.insert ret (EvmYul.UInt256.ofNat 256)).restrictStoreTo
          entry.store) := by
  intro entry
  let assigned := entry.insert ret (EvmYul.UInt256.ofNat 256)
  have hCheckRet :
      EvmYul.Yul.checkAssignment entry [ret] = .ok () :=
    clzHelperZeroEntry_checkAssignRet arg ret hArgRet shared store
  have hAssign :
      Yul.InteractionSemantics.exec (fuel + 18)
          (.Assign [ret] (clzHelperAstWord 256)) code entry =
        pure assigned := by
    rw [show fuel + 18 = (fuel + 17) + 1 by omega]
    rw [Yul.InteractionSemantics.Exec.assign_succ
      (fuel + 17) [ret] (clzHelperAstWord 256) code entry hCheckRet]
    simp [assigned, clzHelperAstWord, Yul.InteractionSemantics.evalValues,
      Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.Control.multifill,
      Yul.Source.Effectful.StateModel.multifill,
      Yul.InteractionSemantics.stateModel,
      EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert,
      Simulation.Interaction.pure, Simulation.Interaction.bind]
    cases entry <;> simp [Simulation.Interaction.pure]
  have hLookupArg :
      assigned.lookup? arg = some (EvmYul.UInt256.ofNat 0) := by
    simpa [assigned] using
      clzHelperZeroEntry_insertRet_lookupArg
        arg ret hArgRet shared store
  have hEvalValuesArg :
      Yul.InteractionSemantics.evalValues (fuel + 16)
          (clzHelperAstValue arg) code assigned =
        pure (assigned, [EvmYul.UInt256.ofNat 0]) := by
    simp [clzHelperAstValue, Yul.InteractionSemantics.evalValues,
      Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
      Yul.InteractionSemantics.stateModel, hLookupArg,
      Simulation.Interaction.pure, Simulation.Interaction.bind]
  have hEvalArg :
      Yul.InteractionSemantics.eval (fuel + 16)
          (clzHelperAstValue arg) code assigned =
        pure (assigned, EvmYul.UInt256.ofNat 0) := by
    rw [Yul.InteractionSemantics.eval_eq_bind, hEvalValuesArg]
    rfl
  have hIf :
      Yul.InteractionSemantics.exec (fuel + 17)
          (.If (clzHelperAstValue arg)
            (clzHelperAstNonzeroBody arg ret)) code assigned =
        pure assigned := by
    rw [show fuel + 17 = (fuel + 16) + 1 by omega]
    rw [Yul.InteractionSemantics.Exec.if_succ]
    rw [hEvalArg]
    rw [open_bind_pure_left]
    simp
  have hTail :
      Yul.InteractionSemantics.execSeq (fuel + 18)
          [EvmYul.Yul.Ast.Stmt.If
            (clzHelperAstValue arg)
            (clzHelperAstNonzeroBody arg ret)] code assigned =
        pure assigned := by
    rw [show fuel + 18 = (fuel + 17) + 1 by omega]
    rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
    rw [hIf]
    rw [open_bind_pure_left]
    simp [Yul.InteractionSemantics.ExecSeq.nil_succ, assigned, entry,
      EvmYul.Yul.State.initcall, EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.mkOk, EvmYul.Yul.State.zeroFill,
      EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert,
      Simulation.Interaction.pure,
      Simulation.Interaction.bind]
  have hTailExplicit := hTail
  simp [assigned, entry, EvmYul.Yul.State.initcall,
    EvmYul.Yul.State.setStore, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.insert] at hTailExplicit
  rw [show fuel + 20 = (fuel + 19) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [clzHelperAstBody]
  rw [show fuel + 19 = (fuel + 18) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [hAssign]
  simp [hTailExplicit, assigned, entry, clzHelperAstBody,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.mkOk, EvmYul.Yul.State.zeroFill,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert,
    Simulation.Interaction.pure, Simulation.Interaction.bind]

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
