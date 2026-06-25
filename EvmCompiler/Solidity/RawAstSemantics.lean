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

def ClzHelperFrame (arg ret : Name) (argValue retValue : Word)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) : Prop :=
  (EvmYul.Yul.State.Ok shared vars).lookup? arg = some argValue ∧
    (EvmYul.Yul.State.Ok shared vars).lookup? ret = some retValue

private theorem bool_eq_false_of_not_true {value : Bool}
    (h : ¬ value = true) :
    value = false := by
  cases value <;> simp at h ⊢

private theorem ClzHelperFrame.insert_ret
    (arg ret : Name) (hArgRet : arg ≠ ret)
    (argValue retValue newRet : Word)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    ClzHelperFrame arg ret argValue newRet
      shared (vars.insert ret newRet) := by
  constructor
  · simpa [EvmYul.Yul.State.lookup?,
      Finmap.lookup_insert_of_ne vars hArgRet] using hFrame.1
  · simp [EvmYul.Yul.State.lookup?]

private theorem ClzHelperFrame.insert_ret_arg
    (arg ret : Name) (hArgRet : arg ≠ ret)
    (argValue retValue newArg newRet : Word)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (_hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    ClzHelperFrame arg ret newArg newRet
      shared ((vars.insert ret newRet).insert arg newArg) := by
  constructor
  · simp [EvmYul.Yul.State.lookup?]
  · have hRetArg : ret ≠ arg := fun h => hArgRet h.symm
    simp [EvmYul.Yul.State.lookup?,
      Finmap.lookup_insert_of_ne (vars.insert ret newRet) hRetArg]

private theorem ClzHelperFrame.restrict_to_scope
    (arg ret : Name)
    (scopeArg scopeRet argValue retValue : Word)
    (shared : EvmYul.SharedState .Yul)
    (scopeVars finalVars : EvmYul.Yul.VarStore)
    (hScope : ClzHelperFrame arg ret scopeArg scopeRet shared scopeVars)
    (hFinal : ClzHelperFrame arg ret argValue retValue shared finalVars) :
    ClzHelperFrame arg ret argValue retValue shared
      (EvmYul.Yul.State.restrictVarStore finalVars scopeVars) := by
  have hScopeArg : scopeVars.lookup arg = some scopeArg := by
    simpa [EvmYul.Yul.State.lookup?] using hScope.1
  have hScopeRet : scopeVars.lookup ret = some scopeRet := by
    simpa [EvmYul.Yul.State.lookup?] using hScope.2
  have hFinalArg : finalVars.lookup arg = some argValue := by
    simpa [EvmYul.Yul.State.lookup?] using hFinal.1
  have hFinalRet : finalVars.lookup ret = some retValue := by
    simpa [EvmYul.Yul.State.lookup?] using hFinal.2
  constructor
  · simp [EvmYul.Yul.State.lookup?]
    rw [Yul.VarStoreRestriction.lookup_restrict_of_some
      finalVars scopeVars arg hScopeArg]
    exact hFinalArg
  · simp [EvmYul.Yul.State.lookup?]
    rw [Yul.VarStoreRestriction.lookup_restrict_of_some
      finalVars scopeVars ret hScopeRet]
    exact hFinalRet

private theorem clzPrimitive_add_openEval_succ
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (left right : Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared vars) (.ADD) [left, right] =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.add left right]) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

private theorem clzPrimitive_shr_openEval_succ
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (shift value : Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared vars) (.SHR) [shift, value] =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftRight value shift]) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

private theorem clzPrimitive_shl_openEval_succ
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (shift value : Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared vars) (.SHL) [shift, value] =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftLeft value shift]) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

private theorem clzPrimitive_iszero_openEval_succ
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (value : Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared vars) (.ISZERO) [value] =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.isZero value]) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

private theorem clzHelperAstWord_evalValues_succ
    (fuel value : Nat) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) :
    Yul.InteractionSemantics.evalValues (fuel + 1)
        (clzHelperAstWord value) code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.ofNat value]) := by
  simp [clzHelperAstWord, Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]

private theorem clzHelperAstValue_evalValues_succ
    (fuel : Nat) (name : Name) (value : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hLookup : (EvmYul.Yul.State.Ok shared vars).lookup? name =
      some value) :
    Yul.InteractionSemantics.evalValues (fuel + 1)
        (clzHelperAstValue name) code (.Ok shared vars) =
      pure ((.Ok shared vars : Yul.InteractionSemantics.State), [value]) := by
  simp [clzHelperAstValue, Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    Yul.InteractionSemantics.stateModel, hLookup]

private theorem clzHelperEvalArgs_value_word_succ
    (fuel wordValue : Nat) (name : Name) (value : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hLookup : (EvmYul.Yul.State.Ok shared vars).lookup? name =
      some value) :
    Yul.InteractionSemantics.evalArgs (fuel + 7)
        [clzHelperAstValue name, clzHelperAstWord wordValue] code
        (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [value, EvmYul.UInt256.ofNat wordValue]) := by
  rw [show fuel + 7 = (fuel + 5) + 2 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  rw [clzHelperAstValue_evalValues_succ
    (fuel + 5) name value code shared vars hLookup]
  rw [open_bind_pure_left]
  rw [show fuel + 5 = (fuel + 3) + 2 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  rw [clzHelperAstWord_evalValues_succ
    (fuel + 3) wordValue code shared vars]
  rw [open_bind_pure_left]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.nil_succ]
  rfl

private theorem clzHelperAstAdd_evalValues_succ
    (fuel addend : Nat) (ret : Name) (retValue : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hRet : (EvmYul.Yul.State.Ok shared vars).lookup? ret =
      some retValue) :
    Yul.InteractionSemantics.evalValues (fuel + 8)
        (clzHelperAstPrim .ADD
          [clzHelperAstValue ret, clzHelperAstWord addend])
        code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.add retValue
            (EvmYul.UInt256.ofNat addend)]) := by
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  simp only [clzHelperAstPrim, Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  change
    Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 7)
          [clzHelperAstWord addend, clzHelperAstValue ret] code
          (.Ok shared vars))
        (fun result =>
          Yul.InteractionSemantics.Primitive.openEval
            (fuel + 7) result.1 (.ADD) result.2.reverse) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.add retValue
            (EvmYul.UInt256.ofNat addend)])
  rw [show fuel + 7 = (fuel + 5) + 2 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  rw [clzHelperAstWord_evalValues_succ
    (fuel + 5) addend code shared vars]
  rw [open_bind_pure_left]
  rw [show fuel + 5 = (fuel + 3) + 2 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  rw [clzHelperAstValue_evalValues_succ
    (fuel + 3) ret retValue code shared vars hRet]
  rw [open_bind_pure_left]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.nil_succ]
  rw [open_bind_pure_left]
  simp
  rw [show fuel + 2 + 1 + 2 + 2 = (fuel + 5) + 2 by omega]
  rw [clzPrimitive_add_openEval_succ]

private theorem clzHelperAstShr_evalValues_succ
    (fuel checkShift : Nat) (arg : Name) (argValue : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hArg : (EvmYul.Yul.State.Ok shared vars).lookup? arg =
      some argValue) :
    Yul.InteractionSemantics.evalValues (fuel + 8)
        (clzHelperAstPrim .SHR
          [clzHelperAstWord checkShift, clzHelperAstValue arg])
        code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift)]) := by
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  simp only [clzHelperAstPrim, Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  change
    Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 7)
          [clzHelperAstValue arg, clzHelperAstWord checkShift] code
          (.Ok shared vars))
        (fun result =>
          Yul.InteractionSemantics.Primitive.openEval
            (fuel + 7) result.1 (.SHR) result.2.reverse) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift)])
  rw [clzHelperEvalArgs_value_word_succ
    fuel checkShift arg argValue code shared vars hArg]
  rw [open_bind_pure_left]
  simp
  rw [show fuel + 7 = (fuel + 5) + 2 by omega]
  rw [clzPrimitive_shr_openEval_succ]

private theorem clzHelperAstShl_evalValues_succ
    (fuel addend : Nat) (arg : Name) (argValue : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hArg : (EvmYul.Yul.State.Ok shared vars).lookup? arg =
      some argValue) :
    Yul.InteractionSemantics.evalValues (fuel + 8)
        (clzHelperAstPrim .SHL
          [clzHelperAstWord addend, clzHelperAstValue arg])
        code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftLeft argValue
            (EvmYul.UInt256.ofNat addend)]) := by
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  simp only [clzHelperAstPrim, Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  change
    Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 7)
          [clzHelperAstValue arg, clzHelperAstWord addend] code
          (.Ok shared vars))
        (fun result =>
          Yul.InteractionSemantics.Primitive.openEval
            (fuel + 7) result.1 (.SHL) result.2.reverse) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftLeft argValue
            (EvmYul.UInt256.ofNat addend)])
  rw [clzHelperEvalArgs_value_word_succ
    fuel addend arg argValue code shared vars hArg]
  rw [open_bind_pure_left]
  simp
  rw [show fuel + 7 = (fuel + 5) + 2 by omega]
  rw [clzPrimitive_shl_openEval_succ]

private theorem clzHelperAssignRetWord_exec_succ
    (fuel value : Nat) (ret : Name)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (retValue : Word)
    (hRet : (EvmYul.Yul.State.Ok shared vars).lookup? ret =
      some retValue) :
    Yul.InteractionSemantics.exec (fuel + 2)
        (.Assign [ret] (clzHelperAstWord value)) code (.Ok shared vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert ret
          (EvmYul.UInt256.ofNat value)) := by
  have hCheck :
      EvmYul.Yul.checkAssignment (.Ok shared vars) [ret] = .ok () := by
    have hRetStore : vars.lookup ret = some retValue := by
      simpa [EvmYul.Yul.State.lookup?] using hRet
    simp [EvmYul.Yul.checkAssignment, EvmYul.Yul.firstUndeclared?,
      EvmYul.Yul.firstDuplicate?, EvmYul.Yul.State.lookup?, hRetStore]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.assign_succ
    (fuel + 1) [ret] (clzHelperAstWord value) code
    (.Ok shared vars) hCheck]
  rw [clzHelperAstWord_evalValues_succ fuel value code shared vars]
  simp [Yul.Source.Effectful.Control.multifill,
    Yul.Source.Effectful.StateModel.multifill,
    Yul.InteractionSemantics.stateModel,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert,
    Simulation.Interaction.pure, Simulation.Interaction.bind]

private theorem clzHelperEvalArgs_shr_succ
    (fuel checkShift : Nat) (arg : Name) (argValue : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hArg : (EvmYul.Yul.State.Ok shared vars).lookup? arg =
      some argValue) :
    Yul.InteractionSemantics.evalArgs (fuel + 11)
        [clzHelperAstPrim .SHR
          [clzHelperAstWord checkShift, clzHelperAstValue arg]]
        code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift)]) := by
  rw [show fuel + 11 = (fuel + 9) + 2 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  rw [show fuel + 9 + 1 = (fuel + 2) + 8 by omega]
  rw [clzHelperAstShr_evalValues_succ
    (fuel + 2) checkShift arg argValue code shared vars hArg]
  rw [open_bind_pure_left]
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [Yul.InteractionSemantics.EvalArgs.nil_succ]
  rfl

private theorem clzHelperAstIszeroShr_evalValues_succ
    (fuel checkShift : Nat) (arg : Name) (argValue : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hArg : (EvmYul.Yul.State.Ok shared vars).lookup? arg =
      some argValue) :
    Yul.InteractionSemantics.evalValues (fuel + 12)
        (clzHelperAstPrim .ISZERO
          [clzHelperAstPrim .SHR
            [clzHelperAstWord checkShift, clzHelperAstValue arg]])
        code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.isZero
            (EvmYul.UInt256.shiftRight argValue
              (EvmYul.UInt256.ofNat checkShift))]) := by
  rw [show fuel + 12 = (fuel + 11) + 1 by omega]
  simp only [clzHelperAstPrim, Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    List.reverse_cons, List.reverse_nil, List.nil_append]
  change
    Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 11)
          [clzHelperAstPrim .SHR
            [clzHelperAstWord checkShift, clzHelperAstValue arg]]
          code (.Ok shared vars))
        (fun result =>
          Yul.InteractionSemantics.Primitive.openEval
            (fuel + 11) result.1 (.ISZERO) result.2.reverse) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          [EvmYul.UInt256.isZero
            (EvmYul.UInt256.shiftRight argValue
              (EvmYul.UInt256.ofNat checkShift))])
  rw [clzHelperEvalArgs_shr_succ
    fuel checkShift arg argValue code shared vars hArg]
  rw [open_bind_pure_left]
  simp
  rw [show fuel + 11 = (fuel + 9) + 2 by omega]
  rw [clzPrimitive_iszero_openEval_succ]

private theorem clzHelperAstIszeroShr_eval_succ
    (fuel checkShift : Nat) (arg : Name) (argValue : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hArg : (EvmYul.Yul.State.Ok shared vars).lookup? arg =
      some argValue) :
    Yul.InteractionSemantics.eval (fuel + 12)
        (clzHelperAstPrim .ISZERO
          [clzHelperAstPrim .SHR
            [clzHelperAstWord checkShift, clzHelperAstValue arg]])
        code (.Ok shared vars) =
      pure
        ((.Ok shared vars : Yul.InteractionSemantics.State),
          EvmYul.UInt256.isZero
            (EvmYul.UInt256.shiftRight argValue
              (EvmYul.UInt256.ofNat checkShift))) := by
  rw [Yul.InteractionSemantics.eval_eq_bind]
  rw [clzHelperAstIszeroShr_evalValues_succ
    fuel checkShift arg argValue code shared vars hArg]
  rfl

private theorem checkAssignment_single_of_lookup?
    (state : Yul.InteractionSemantics.State) (name : Name)
    (value : Word) (hLookup : state.lookup? name = some value) :
    EvmYul.Yul.checkAssignment state [name] = .ok () := by
  cases state <;>
    simp [EvmYul.Yul.checkAssignment, EvmYul.Yul.firstDuplicate?,
      EvmYul.Yul.firstUndeclared?, EvmYul.Yul.State.lookup?] at hLookup ⊢
  all_goals simp [hLookup]

private theorem clzHelperAssignRetAdd_exec_succ
    (fuel addend : Nat) (arg ret : Name)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    Yul.InteractionSemantics.exec (fuel + 10)
        (.Assign [ret]
          (clzHelperAstPrim .ADD
            [clzHelperAstValue ret, clzHelperAstWord addend]))
        code (.Ok shared vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert ret
          (EvmYul.UInt256.add retValue
            (EvmYul.UInt256.ofNat addend))) := by
  have hCheck :
      EvmYul.Yul.checkAssignment
          (EvmYul.Yul.State.Ok shared vars) [ret] = .ok () :=
    checkAssignment_single_of_lookup?
      (.Ok shared vars) ret retValue hFrame.2
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.assign_succ
    (fuel + 9) [ret]
    (clzHelperAstPrim .ADD
      [clzHelperAstValue ret, clzHelperAstWord addend])
    code (.Ok shared vars) hCheck]
  rw [show fuel + 9 = (fuel + 1) + 8 by omega]
  rw [clzHelperAstAdd_evalValues_succ
    (fuel + 1) addend ret retValue code shared vars hFrame.2]
  rw [open_bind_pure_left]
  simp [Yul.InteractionSemantics.stateModel,
    Yul.Source.Effectful.Control.multifill,
    Yul.Source.Effectful.StateModel.multifill,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

private theorem clzHelperAssignArgShl_exec_succ
    (fuel addend : Nat) (arg ret : Name)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    Yul.InteractionSemantics.exec (fuel + 10)
        (.Assign [arg]
          (clzHelperAstPrim .SHL
            [clzHelperAstWord addend, clzHelperAstValue arg]))
        code (.Ok shared vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert arg
          (EvmYul.UInt256.shiftLeft argValue
            (EvmYul.UInt256.ofNat addend))) := by
  have hCheck :
      EvmYul.Yul.checkAssignment
          (EvmYul.Yul.State.Ok shared vars) [arg] = .ok () :=
    checkAssignment_single_of_lookup?
      (.Ok shared vars) arg argValue hFrame.1
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.assign_succ
    (fuel + 9) [arg]
    (clzHelperAstPrim .SHL
      [clzHelperAstWord addend, clzHelperAstValue arg])
    code (.Ok shared vars) hCheck]
  rw [show fuel + 9 = (fuel + 1) + 8 by omega]
  rw [clzHelperAstShl_evalValues_succ
    (fuel + 1) addend arg argValue code shared vars hFrame.1]
  rw [open_bind_pure_left]
  simp [Yul.InteractionSemantics.stateModel,
    Yul.Source.Effectful.Control.multifill,
    Yul.Source.Effectful.StateModel.multifill,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

private theorem restrictStoreTo_insert_existing
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (name : Name)
    (oldValue newValue : Word)
    (hLookup : vars.lookup name = some oldValue) :
    ((EvmYul.Yul.State.Ok shared vars).insert name newValue).restrictStoreTo
        vars =
      EvmYul.Yul.State.Ok shared (vars.insert name newValue) := by
  simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.restrictStoreTo]
  apply Finmap.ext_lookup
  intro key
  cases hScope : vars.lookup key with
  | some value =>
      rw [Yul.VarStoreRestriction.lookup_restrict_of_some
        (vars.insert name newValue) vars key hScope]
  | none =>
      rw [Yul.VarStoreRestriction.lookup_restrict_of_none
        (vars.insert name newValue) vars key hScope]
      by_cases hKey : key = name
      · subst key
        simp [hLookup] at hScope
      · rw [Finmap.lookup_insert_of_ne vars hKey]
        exact hScope.symm

private theorem restrictStoreTo_insert_insert_existing
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (first second : Name)
    (oldFirst newFirst oldSecond newSecond : Word)
    (hFirst : vars.lookup first = some oldFirst)
    (hSecond : vars.lookup second = some oldSecond) :
    (((EvmYul.Yul.State.Ok shared vars).insert first newFirst).insert
        second newSecond).restrictStoreTo vars =
      ((EvmYul.Yul.State.Ok shared vars).insert first newFirst).insert
        second newSecond := by
  simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.restrictStoreTo]
  apply Finmap.ext_lookup
  intro key
  cases hScope : vars.lookup key with
  | some value =>
      rw [Yul.VarStoreRestriction.lookup_restrict_of_some
        ((vars.insert first newFirst).insert second newSecond)
        vars key hScope]
  | none =>
      rw [Yul.VarStoreRestriction.lookup_restrict_of_none
        ((vars.insert first newFirst).insert second newSecond)
        vars key hScope]
      by_cases hKeySecond : key = second
      · subst key
        simp [hSecond] at hScope
      · rw [Finmap.lookup_insert_of_ne (vars.insert first newFirst)
          hKeySecond]
        by_cases hKeyFirst : key = first
        · subst key
          simp [hFirst] at hScope
        · rw [Finmap.lookup_insert_of_ne vars hKeyFirst]
          exact hScope.symm

private theorem clzHelper_isZero_of_beq_false (value : Word)
    (hValue : (value == EvmYul.UInt256.ofNat 0) = false) :
    EvmYul.UInt256.isZero value = EvmYul.UInt256.ofNat 0 := by
  have hValueZero : (value == (⟨0⟩ : EvmYul.UInt256)) = false := by
    simpa [EvmYul.UInt256.ofNat] using hValue
  simpa [EvmYul.UInt256.isZero, EvmYul.UInt256.eq0,
    Bool.toUInt256, hValueZero]

private theorem clzHelper_isZero_ne_zero_of_beq_true (value : Word)
    (hValue : (value == EvmYul.UInt256.ofNat 0) = true) :
    EvmYul.UInt256.isZero value ≠ EvmYul.UInt256.ofNat 0 := by
  have hValueZero : (value == (⟨0⟩ : EvmYul.UInt256)) = true := by
    simpa [EvmYul.UInt256.ofNat] using hValue
  simp [EvmYul.UInt256.isZero, EvmYul.UInt256.eq0,
    Bool.toUInt256, hValueZero]
  decide

private theorem clzHelperIfIszeroShr_noop_exec_succ
    (fuel checkShift : Nat) (arg : Name) (argValue : Word)
    (body : List Yul.AstStmt) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hArg : (EvmYul.Yul.State.Ok shared vars).lookup? arg =
      some argValue)
    (hShift :
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift) ==
          EvmYul.UInt256.ofNat 0) = false) :
    Yul.InteractionSemantics.exec (fuel + 14)
        (.If
          (clzHelperAstPrim .ISZERO
            [clzHelperAstPrim .SHR
              [clzHelperAstWord checkShift, clzHelperAstValue arg]])
          body)
        code (.Ok shared vars) =
      pure (.Ok shared vars : Yul.InteractionSemantics.State) := by
  rw [show fuel + 14 = (fuel + 13) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.if_succ]
  rw [show fuel + 13 = (fuel + 1) + 12 by omega]
  rw [clzHelperAstIszeroShr_eval_succ
    (fuel + 1) checkShift arg argValue code shared vars hArg]
  rw [open_bind_pure_left]
  have hCond :
      EvmYul.UInt256.isZero
          (EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift)) =
        EvmYul.UInt256.ofNat 0 :=
    clzHelper_isZero_of_beq_false
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift)) hShift
  simp [hCond]

private theorem clzHelperAstStepBody_noop_execSeq_succ
    (fuel checkShift addend : Nat) (arg ret : Name)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars)
    (hShift :
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift) ==
          EvmYul.UInt256.ofNat 0) = false) :
    Yul.InteractionSemantics.execSeq (fuel + 16)
        (clzHelperAstStepBody arg ret (checkShift, addend))
        code (.Ok shared vars) =
      pure (.Ok shared vars : Yul.InteractionSemantics.State) := by
  rw [show fuel + 16 = (fuel + 15) + 1 by omega]
  simp only [clzHelperAstStepBody]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [show fuel + 15 = (fuel + 1) + 14 by omega]
  rw [clzHelperIfIszeroShr_noop_exec_succ
    (fuel + 1) checkShift arg argValue _ code shared vars hFrame.1 hShift]
  rw [open_bind_pure_left]
  rw [show fuel + 15 = (fuel + 14) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]

private theorem clzHelperRetAdd_block_exec_succ
    (fuel addend : Nat) (arg ret : Name)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    Yul.InteractionSemantics.exec (fuel + 13)
        (.Block
          [EvmYul.Yul.Ast.Stmt.Assign [ret]
            (clzHelperAstPrim .ADD
              [clzHelperAstValue ret, clzHelperAstWord addend])])
        code (.Ok shared vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert ret
          (EvmYul.UInt256.add retValue
            (EvmYul.UInt256.ofNat addend))) := by
  rw [show fuel + 13 = (fuel + 12) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  rw [show fuel + 12 = (fuel + 11) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [show fuel + 11 = (fuel + 1) + 10 by omega]
  rw [clzHelperAssignRetAdd_exec_succ
    (fuel + 1) addend arg ret argValue retValue code shared vars hFrame]
  rw [open_bind_pure_left]
  rw [show fuel + 11 = (fuel + 10) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  change
    pure
        (((EvmYul.Yul.State.Ok shared vars).insert ret
            (EvmYul.UInt256.add retValue
              (EvmYul.UInt256.ofNat addend))).restrictStoreTo vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert ret
          (EvmYul.UInt256.add retValue
            (EvmYul.UInt256.ofNat addend)))
  rw [restrictStoreTo_insert_existing shared vars ret retValue
    (EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat addend))
    hFrame.2]
  rfl

private theorem clzHelperRetAddArgShl_block_exec_succ
    (fuel addend : Nat) (arg ret : Name) (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    let retValue' :=
      EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat addend)
    let argValue' :=
      EvmYul.UInt256.shiftLeft argValue (EvmYul.UInt256.ofNat addend)
    Yul.InteractionSemantics.exec (fuel + 30)
        (.Block
          [EvmYul.Yul.Ast.Stmt.Assign [ret]
            (clzHelperAstPrim .ADD
              [clzHelperAstValue ret, clzHelperAstWord addend]),
           EvmYul.Yul.Ast.Stmt.Assign [arg]
            (clzHelperAstPrim .SHL
              [clzHelperAstWord addend, clzHelperAstValue arg])])
        code (.Ok shared vars) =
      pure
        (((EvmYul.Yul.State.Ok shared vars).insert ret retValue').insert
          arg argValue') := by
  intro retValue' argValue'
  have hArgAfterRet :
      (EvmYul.Yul.State.Ok shared (vars.insert ret retValue')).lookup? arg =
        some argValue := by
    simpa [EvmYul.Yul.State.lookup?,
      Finmap.lookup_insert_of_ne vars hArgRet] using hFrame.1
  have hRetAfterRet :
      (EvmYul.Yul.State.Ok shared (vars.insert ret retValue')).lookup? ret =
        some retValue' := by
    simp [EvmYul.Yul.State.lookup?]
  have hFrameAfterRet :
      ClzHelperFrame arg ret argValue retValue'
        shared (vars.insert ret retValue') := by
    exact ⟨hArgAfterRet, hRetAfterRet⟩
  rw [show fuel + 30 = (fuel + 29) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  rw [show fuel + 29 = (fuel + 28) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [show fuel + 28 = (fuel + 18) + 10 by omega]
  rw [clzHelperAssignRetAdd_exec_succ
    (fuel + 18) addend arg ret argValue retValue code shared vars hFrame]
  rw [open_bind_pure_left]
  simp [EvmYul.Yul.State.insert]
  rw [show fuel + 28 = (fuel + 27) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [show fuel + 27 = (fuel + 17) + 10 by omega]
  rw [clzHelperAssignArgShl_exec_succ
    (fuel + 17) addend arg ret argValue retValue' code shared
    (vars.insert ret retValue') hFrameAfterRet]
  rw [open_bind_pure_left]
  simp [EvmYul.Yul.State.insert]
  rw [show fuel + 27 = (fuel + 26) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  change
    pure
        ((((EvmYul.Yul.State.Ok shared vars).insert ret retValue').insert
            arg argValue').restrictStoreTo vars) =
      pure
        (((EvmYul.Yul.State.Ok shared vars).insert ret retValue').insert
          arg argValue')
  rw [restrictStoreTo_insert_insert_existing shared vars ret arg
    retValue retValue' argValue argValue' hFrame.2 hFrame.1]

private theorem clzHelperIfIszeroShr_retAddArgShl_exec_succ
    (fuel checkShift addend : Nat) (arg ret : Name)
    (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars)
    (hShift :
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift) ==
          EvmYul.UInt256.ofNat 0) = true) :
    let retValue' :=
      EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat addend)
    let argValue' :=
      EvmYul.UInt256.shiftLeft argValue (EvmYul.UInt256.ofNat addend)
    Yul.InteractionSemantics.exec (fuel + 33)
        (.If
          (clzHelperAstPrim .ISZERO
            [clzHelperAstPrim .SHR
              [clzHelperAstWord checkShift, clzHelperAstValue arg]])
          [EvmYul.Yul.Ast.Stmt.Assign [ret]
            (clzHelperAstPrim .ADD
              [clzHelperAstValue ret, clzHelperAstWord addend]),
           EvmYul.Yul.Ast.Stmt.Assign [arg]
            (clzHelperAstPrim .SHL
              [clzHelperAstWord addend, clzHelperAstValue arg])])
        code (.Ok shared vars) =
      pure
        (((EvmYul.Yul.State.Ok shared vars).insert ret retValue').insert
          arg argValue') := by
  intro retValue' argValue'
  rw [show fuel + 33 = (fuel + 32) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.if_succ]
  rw [show fuel + 32 = (fuel + 20) + 12 by omega]
  rw [clzHelperAstIszeroShr_eval_succ
    (fuel + 20) checkShift arg argValue code shared vars hFrame.1]
  rw [open_bind_pure_left]
  have hCond :
      EvmYul.UInt256.isZero
          (EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift)) ≠
        EvmYul.UInt256.ofNat 0 :=
    clzHelper_isZero_ne_zero_of_beq_true
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift)) hShift
  simp [hCond]
  rw [show fuel + 32 = (fuel + 2) + 30 by omega]
  rw [clzHelperRetAddArgShl_block_exec_succ
    (fuel + 2) addend arg ret hArgRet argValue retValue code shared vars
    hFrame]

private theorem clzHelperIfIszeroShr_retAdd_exec_succ
    (fuel checkShift addend : Nat) (arg ret : Name)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars)
    (hShift :
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift) ==
          EvmYul.UInt256.ofNat 0) = true) :
    Yul.InteractionSemantics.exec (fuel + 16)
        (.If
          (clzHelperAstPrim .ISZERO
            [clzHelperAstPrim .SHR
              [clzHelperAstWord checkShift, clzHelperAstValue arg]])
          [EvmYul.Yul.Ast.Stmt.Assign [ret]
            (clzHelperAstPrim .ADD
              [clzHelperAstValue ret, clzHelperAstWord addend])])
        code (.Ok shared vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert ret
          (EvmYul.UInt256.add retValue
            (EvmYul.UInt256.ofNat addend))) := by
  rw [show fuel + 16 = (fuel + 15) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.if_succ]
  rw [show fuel + 15 = (fuel + 3) + 12 by omega]
  rw [clzHelperAstIszeroShr_eval_succ
    (fuel + 3) checkShift arg argValue code shared vars hFrame.1]
  rw [open_bind_pure_left]
  have hCond :
      EvmYul.UInt256.isZero
          (EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift)) ≠
        EvmYul.UInt256.ofNat 0 :=
    clzHelper_isZero_ne_zero_of_beq_true
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift)) hShift
  simp [hCond]
  rw [show fuel + 15 = (fuel + 2) + 13 by omega]
  rw [clzHelperRetAdd_block_exec_succ
    (fuel + 2) addend arg ret argValue retValue code shared vars hFrame]

private theorem clzHelperAstStepBody_addOne_execSeq_succ
    (fuel checkShift : Nat) (arg ret : Name)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars)
    (hShift :
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift) ==
          EvmYul.UInt256.ofNat 0) = true) :
    Yul.InteractionSemantics.execSeq (fuel + 18)
        (clzHelperAstStepBody arg ret (checkShift, 1))
        code (.Ok shared vars) =
      pure
        ((EvmYul.Yul.State.Ok shared vars).insert ret
          (EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat 1))) := by
  rw [show fuel + 18 = (fuel + 17) + 1 by omega]
  simp only [clzHelperAstStepBody, beq_self_eq_true, ↓reduceIte,
    List.append_nil]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [show fuel + 17 = (fuel + 1) + 16 by omega]
  rw [clzHelperIfIszeroShr_retAdd_exec_succ
    (fuel + 1) checkShift 1 arg ret argValue retValue code shared vars
    hFrame hShift]
  rw [open_bind_pure_left]
  rw [show fuel + 17 = (fuel + 16) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  simp [EvmYul.Yul.State.insert]

private theorem clzHelperAstStepBody_addShift_execSeq_succ
    (fuel checkShift addend : Nat) (arg ret : Name)
    (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars)
    (hAddend : (addend == 1) = false)
    (hShift :
      (EvmYul.UInt256.shiftRight argValue
        (EvmYul.UInt256.ofNat checkShift) ==
          EvmYul.UInt256.ofNat 0) = true) :
    let retValue' :=
      EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat addend)
    let argValue' :=
      EvmYul.UInt256.shiftLeft argValue (EvmYul.UInt256.ofNat addend)
    Yul.InteractionSemantics.execSeq (fuel + 35)
        (clzHelperAstStepBody arg ret (checkShift, addend))
        code (.Ok shared vars) =
      pure
        (((EvmYul.Yul.State.Ok shared vars).insert ret retValue').insert
          arg argValue') := by
  intro retValue' argValue'
  rw [show fuel + 35 = (fuel + 34) + 1 by omega]
  simp [clzHelperAstStepBody, hAddend]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [show fuel + 34 = (fuel + 1) + 33 by omega]
  rw [clzHelperIfIszeroShr_retAddArgShl_exec_succ
    (fuel + 1) checkShift addend arg ret hArgRet argValue retValue code
    shared vars hFrame hShift]
  rw [open_bind_pure_left]
  rw [show fuel + 34 = (fuel + 33) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  simp [EvmYul.Yul.State.insert]
  rfl

private def clzHelperAstStepList (arg ret : Name) :
    List (Nat × Nat) → List Yul.AstStmt
  | [] => []
  | step :: rest =>
      clzHelperAstStepBody arg ret step ++
        clzHelperAstStepList arg ret rest

private theorem clzHelperAstStepList_execSeq_succ
    (steps : List (Nat × Nat)) (fuel : Nat) (arg ret : Name)
    (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    let result := steps.foldl clzHelperValueStep (retValue, argValue)
    ∃ finalVars,
      Yul.InteractionSemantics.execSeq (fuel + steps.length + 40)
          (clzHelperAstStepList arg ret steps) code (.Ok shared vars) =
        pure (.Ok shared finalVars : Yul.InteractionSemantics.State) ∧
      ClzHelperFrame arg ret result.snd result.fst shared finalVars := by
  induction steps generalizing fuel vars argValue retValue with
  | nil =>
      intro result
      refine ⟨vars, ?_, ?_⟩
      · simp only [clzHelperAstStepList, List.length_nil]
        rw [show fuel + 0 + 40 = (fuel + 39) + 1 by omega]
        rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      · simpa using hFrame
  | cons step rest ih =>
      rcases step with ⟨checkShift, addend⟩
      intro result
      by_cases hShift :
          (EvmYul.UInt256.shiftRight argValue
            (EvmYul.UInt256.ofNat checkShift) ==
              EvmYul.UInt256.ofNat 0) = true
      · by_cases hAddendEq : addend = 1
        · subst addend
          let retValue' :=
            EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat 1)
          have hFrame' :
              ClzHelperFrame arg ret argValue retValue'
                shared (vars.insert ret retValue') :=
            ClzHelperFrame.insert_ret arg ret hArgRet
              argValue retValue retValue' shared vars hFrame
          rcases ih (fuel := fuel) (vars := vars.insert ret retValue')
              (argValue := argValue) (retValue := retValue') hFrame' with
            ⟨finalVars, hRest, hFinal⟩
          refine ⟨finalVars, ?_, ?_⟩
          · rw [show fuel + (((checkShift, 1) :: rest).length) + 40 =
              (fuel + rest.length + 40) + 1 by simp; omega]
            simp only [clzHelperAstStepList, clzHelperAstStepBody,
              beq_self_eq_true, ↓reduceIte, List.append_nil,
              List.singleton_append]
            rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
            rw [show fuel + rest.length + 40 =
              (fuel + rest.length + 24) + 16 by omega]
            rw [clzHelperIfIszeroShr_retAdd_exec_succ
              (fuel + rest.length + 24) checkShift 1 arg ret argValue
              retValue code shared vars hFrame hShift]
            rw [open_bind_pure_left]
            simp [EvmYul.Yul.State.insert, retValue']
            exact hRest
          · simpa [result, clzHelperValueStep, hShift, retValue']
              using hFinal
        · have hAddendFalse : (addend == 1) = false := by
            cases addend with
            | zero => rfl
            | succ n =>
                cases n with
                | zero => exact False.elim (hAddendEq rfl)
                | succ n => rfl
          let retValue' :=
            EvmYul.UInt256.add retValue (EvmYul.UInt256.ofNat addend)
          let argValue' :=
            EvmYul.UInt256.shiftLeft argValue (EvmYul.UInt256.ofNat addend)
          have hFrame' :
              ClzHelperFrame arg ret argValue' retValue'
                shared ((vars.insert ret retValue').insert arg argValue') :=
            ClzHelperFrame.insert_ret_arg arg ret hArgRet
              argValue retValue argValue' retValue' shared vars hFrame
          rcases ih (fuel := fuel)
              (vars := (vars.insert ret retValue').insert arg argValue')
              (argValue := argValue') (retValue := retValue') hFrame' with
            ⟨finalVars, hRest, hFinal⟩
          refine ⟨finalVars, ?_, ?_⟩
          · rw [show fuel + (((checkShift, addend) :: rest).length) + 40 =
              (fuel + rest.length + 40) + 1 by simp; omega]
            simp [clzHelperAstStepList, clzHelperAstStepBody,
              hAddendFalse, List.append_assoc]
            rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
            rw [show fuel + rest.length + 40 =
              (fuel + rest.length + 7) + 33 by omega]
            rw [clzHelperIfIszeroShr_retAddArgShl_exec_succ
              (fuel + rest.length + 7) checkShift addend arg ret hArgRet
              argValue retValue code shared vars hFrame hShift]
            rw [open_bind_pure_left]
            simp [EvmYul.Yul.State.insert, retValue', argValue']
            exact hRest
          · simpa [result, clzHelperValueStep, hShift, hAddendFalse,
              retValue', argValue'] using hFinal
      · have hShiftFalse :
            (EvmYul.UInt256.shiftRight argValue
              (EvmYul.UInt256.ofNat checkShift) ==
                EvmYul.UInt256.ofNat 0) = false :=
          bool_eq_false_of_not_true hShift
        rcases ih (fuel := fuel) (vars := vars)
            (argValue := argValue) (retValue := retValue) hFrame with
          ⟨finalVars, hRest, hFinal⟩
        refine ⟨finalVars, ?_, ?_⟩
        · rw [show fuel + (((checkShift, addend) :: rest).length) + 40 =
            (fuel + rest.length + 40) + 1 by simp; omega]
          simp only [clzHelperAstStepList, clzHelperAstStepBody,
            List.singleton_append]
          rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
          rw [show fuel + rest.length + 40 =
            (fuel + rest.length + 26) + 14 by omega]
          rw [clzHelperIfIszeroShr_noop_exec_succ
            (fuel + rest.length + 26) checkShift arg argValue _ code
            shared vars hFrame.1 hShiftFalse]
          rw [open_bind_pure_left]
          exact hRest
        · simpa [result, clzHelperValueStep, hShiftFalse] using hFinal

private theorem clzHelperAstStepList_append_eq_foldl
    (arg ret : Name) (steps : List (Nat × Nat))
    (acc : List Yul.AstStmt) :
    acc ++ clzHelperAstStepList arg ret steps =
      steps.foldl
        (fun body step => body ++ clzHelperAstStepBody arg ret step)
        acc := by
  induction steps generalizing acc with
  | nil =>
      simp [clzHelperAstStepList]
  | cons step rest ih =>
      simpa [clzHelperAstStepList, List.append_assoc] using
        ih (acc := acc ++ clzHelperAstStepBody arg ret step)

private theorem clzHelperAstNonzeroBody_eq_assign_stepList
    (arg ret : Name) :
    clzHelperAstNonzeroBody arg ret =
      [EvmYul.Yul.Ast.Stmt.Assign [ret] (clzHelperAstWord 0)] ++
        clzHelperAstStepList arg ret clzHelperStepSchedule := by
  simpa [clzHelperAstNonzeroBody] using
    (clzHelperAstStepList_append_eq_foldl
      arg ret clzHelperStepSchedule
      [EvmYul.Yul.Ast.Stmt.Assign [ret] (clzHelperAstWord 0)]).symm

private theorem clzHelperAstNonzeroBody_execSeq_succ
    (fuel : Nat) (arg ret : Name) (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    let result :=
      clzHelperStepSchedule.foldl clzHelperValueStep
        (EvmYul.UInt256.ofNat 0, argValue)
    ∃ finalVars,
      Yul.InteractionSemantics.execSeq
          (fuel + clzHelperStepSchedule.length + 41)
          (clzHelperAstNonzeroBody arg ret) code (.Ok shared vars) =
        pure (.Ok shared finalVars : Yul.InteractionSemantics.State) ∧
      ClzHelperFrame arg ret result.snd result.fst shared finalVars := by
  intro result
  let zero := EvmYul.UInt256.ofNat 0
  have hFrameAfterAssign :
      ClzHelperFrame arg ret argValue zero
        shared (vars.insert ret zero) :=
    ClzHelperFrame.insert_ret arg ret hArgRet
      argValue retValue zero shared vars hFrame
  rcases clzHelperAstStepList_execSeq_succ
      clzHelperStepSchedule fuel arg ret hArgRet argValue zero code shared
      (vars.insert ret zero) hFrameAfterAssign with
    ⟨finalVars, hRest, hFinal⟩
  refine ⟨finalVars, ?_, ?_⟩
  · rw [clzHelperAstNonzeroBody_eq_assign_stepList]
    rw [show fuel + clzHelperStepSchedule.length + 41 =
      (fuel + clzHelperStepSchedule.length + 40) + 1 by omega]
    simp only [List.singleton_append]
    rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
    rw [show fuel + clzHelperStepSchedule.length + 40 =
      (fuel + clzHelperStepSchedule.length + 38) + 2 by omega]
    rw [clzHelperAssignRetWord_exec_succ
      (fuel + clzHelperStepSchedule.length + 38) 0 ret code shared vars
      retValue hFrame.2]
    rw [open_bind_pure_left]
    simp [EvmYul.Yul.State.insert, zero]
    exact hRest
  · simpa [result, zero] using hFinal

private theorem clzHelperAstNonzeroBody_block_exec_succ
    (fuel : Nat) (arg ret : Name) (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    let result :=
      clzHelperStepSchedule.foldl clzHelperValueStep
        (EvmYul.UInt256.ofNat 0, argValue)
    ∃ finalVars,
      Yul.InteractionSemantics.exec
          (fuel + clzHelperStepSchedule.length + 42)
          (.Block (clzHelperAstNonzeroBody arg ret)) code (.Ok shared vars) =
        pure (.Ok shared finalVars : Yul.InteractionSemantics.State) ∧
      ClzHelperFrame arg ret result.snd result.fst shared finalVars := by
  intro result
  rcases clzHelperAstNonzeroBody_execSeq_succ
      fuel arg ret hArgRet argValue retValue code shared vars hFrame with
    ⟨rawVars, hBody, hRawFrame⟩
  refine ⟨EvmYul.Yul.State.restrictVarStore rawVars vars, ?_, ?_⟩
  · rw [show fuel + clzHelperStepSchedule.length + 42 =
      (fuel + clzHelperStepSchedule.length + 41) + 1 by omega]
    rw [Yul.InteractionSemantics.Exec.block_succ]
    rw [hBody]
    rw [open_bind_pure_left]
    simp [EvmYul.Yul.State.restrictStoreTo, EvmYul.Yul.State.store]
  · exact
      ClzHelperFrame.restrict_to_scope arg ret argValue retValue
        result.snd result.fst shared vars rawVars hFrame hRawFrame

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
