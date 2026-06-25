import EvmCompiler.Solidity.RawAstOccurrence
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

private theorem clzHelper_word_beq_eq_true_iff_eq (left right : Word) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftVal =>
      cases right with
      | mk rightVal =>
          constructor
          · intro hEq
            have hVal : leftVal = rightVal := eq_of_beq hEq
            cases hVal
            rfl
          · intro hEq
            cases hEq
            simp [EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq]

private theorem clzHelper_word_ne_of_beq_false (left right : Word)
    (hEq : (left == right) = false) :
    left ≠ right := by
  intro hSame
  have hTrue : (left == right) = true :=
    (clzHelper_word_beq_eq_true_iff_eq left right).2 hSame
  rw [hTrue] at hEq
  contradiction

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

private theorem clzHelperAstValue_eval_succ
    (fuel : Nat) (name : Name) (value : Word)
    (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hLookup : (EvmYul.Yul.State.Ok shared vars).lookup? name =
      some value) :
    Yul.InteractionSemantics.eval (fuel + 1)
        (clzHelperAstValue name) code (.Ok shared vars) =
      pure ((.Ok shared vars : Yul.InteractionSemantics.State), value) := by
  rw [Yul.InteractionSemantics.eval_eq_bind]
  rw [clzHelperAstValue_evalValues_succ
    fuel name value code shared vars hLookup]
  rfl

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

private theorem clzHelperAstBody_block_exec_succ
    (fuel : Nat) (arg ret : Name) (hArgRet : arg ≠ ret)
    (argValue retValue : Word) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore)
    (hFrame : ClzHelperFrame arg ret argValue retValue shared vars) :
    ∃ finalArg finalVars,
      Yul.InteractionSemantics.exec
          (fuel + clzHelperStepSchedule.length + 50)
          (.Block (clzHelperAstBody arg ret)) code (.Ok shared vars) =
        pure (.Ok shared finalVars : Yul.InteractionSemantics.State) ∧
      ClzHelperFrame arg ret finalArg (clzHelperValue argValue)
        shared finalVars := by
  let retInit := EvmYul.UInt256.ofNat 256
  have hFrameAfterRet :
      ClzHelperFrame arg ret argValue retInit
        shared (vars.insert ret retInit) :=
    ClzHelperFrame.insert_ret arg ret hArgRet
      argValue retValue retInit shared vars hFrame
  by_cases hArgZero :
      (argValue == EvmYul.UInt256.ofNat 0) = true
  · have hArgEq :
        argValue = EvmYul.UInt256.ofNat 0 :=
      (clzHelper_word_beq_eq_true_iff_eq
        argValue (EvmYul.UInt256.ofNat 0)).1 hArgZero
    let finalVars :=
      EvmYul.Yul.State.restrictVarStore (vars.insert ret retInit) vars
    refine ⟨argValue, finalVars, ?_, ?_⟩
    · rw [show fuel + clzHelperStepSchedule.length + 50 =
        (fuel + clzHelperStepSchedule.length + 49) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.block_succ]
      simp only [clzHelperAstBody, List.singleton_append]
      rw [show fuel + clzHelperStepSchedule.length + 49 =
        (fuel + clzHelperStepSchedule.length + 48) + 1 by omega]
      rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
      rw [show fuel + clzHelperStepSchedule.length + 48 =
        (fuel + clzHelperStepSchedule.length + 46) + 2 by omega]
      rw [clzHelperAssignRetWord_exec_succ
        (fuel + clzHelperStepSchedule.length + 46) 256 ret code shared
        vars retValue hFrame.2]
      rw [open_bind_pure_left]
      simp [EvmYul.Yul.State.insert, retInit]
      rw [show fuel + clzHelperStepSchedule.length + 48 =
        (fuel + clzHelperStepSchedule.length + 47) + 1 by omega]
      rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
      rw [show fuel + clzHelperStepSchedule.length + 47 =
        (fuel + clzHelperStepSchedule.length + 46) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.if_succ]
      rw [show fuel + clzHelperStepSchedule.length + 46 =
        (fuel + clzHelperStepSchedule.length + 45) + 1 by omega]
      rw [clzHelperAstValue_eval_succ
        (fuel + clzHelperStepSchedule.length + 45) arg argValue code shared
        (vars.insert ret retInit) hFrameAfterRet.1]
      rw [open_bind_pure_left]
      simp [hArgEq]
      rw [show fuel + clzHelperStepSchedule.length + 47 =
        (fuel + clzHelperStepSchedule.length + 46) + 1 by omega]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      rw [open_bind_pure_left]
      simp [EvmYul.Yul.State.restrictStoreTo, EvmYul.Yul.State.store,
        EvmYul.Yul.State.insert, finalVars, retInit]
    · have hRestricted :
          ClzHelperFrame arg ret argValue retInit shared finalVars :=
        ClzHelperFrame.restrict_to_scope arg ret argValue retValue
          argValue retInit shared vars (vars.insert ret retInit)
          hFrame hFrameAfterRet
      simpa [clzHelperValue, hArgZero, retInit] using hRestricted
  · have hArgZeroFalse :
        (argValue == EvmYul.UInt256.ofNat 0) = false :=
      bool_eq_false_of_not_true hArgZero
    have hArgNe :
        argValue ≠ EvmYul.UInt256.ofNat 0 :=
      clzHelper_word_ne_of_beq_false
        argValue (EvmYul.UInt256.ofNat 0) hArgZeroFalse
    rcases clzHelperAstNonzeroBody_block_exec_succ
        (fuel + 4) arg ret hArgRet argValue retInit code shared
        (vars.insert ret retInit) hFrameAfterRet with
      ⟨innerVars, hInnerExec, hInnerFrame⟩
    let result :=
      clzHelperStepSchedule.foldl clzHelperValueStep
        (EvmYul.UInt256.ofNat 0, argValue)
    let finalVars := EvmYul.Yul.State.restrictVarStore innerVars vars
    refine ⟨result.snd, finalVars, ?_, ?_⟩
    · rw [show fuel + clzHelperStepSchedule.length + 50 =
        (fuel + clzHelperStepSchedule.length + 49) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.block_succ]
      simp only [clzHelperAstBody, List.singleton_append]
      rw [show fuel + clzHelperStepSchedule.length + 49 =
        (fuel + clzHelperStepSchedule.length + 48) + 1 by omega]
      rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
      rw [show fuel + clzHelperStepSchedule.length + 48 =
        (fuel + clzHelperStepSchedule.length + 46) + 2 by omega]
      rw [clzHelperAssignRetWord_exec_succ
        (fuel + clzHelperStepSchedule.length + 46) 256 ret code shared
        vars retValue hFrame.2]
      rw [open_bind_pure_left]
      simp [EvmYul.Yul.State.insert, retInit]
      rw [show fuel + clzHelperStepSchedule.length + 48 =
        (fuel + clzHelperStepSchedule.length + 47) + 1 by omega]
      rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
      rw [show fuel + clzHelperStepSchedule.length + 47 =
        (fuel + clzHelperStepSchedule.length + 46) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.if_succ]
      rw [show fuel + clzHelperStepSchedule.length + 46 =
        (fuel + clzHelperStepSchedule.length + 45) + 1 by omega]
      rw [clzHelperAstValue_eval_succ
        (fuel + clzHelperStepSchedule.length + 45) arg argValue code shared
        (vars.insert ret retInit) hFrameAfterRet.1]
      rw [open_bind_pure_left]
      simp [hArgNe]
      rw [show fuel + clzHelperStepSchedule.length + 46 =
        (fuel + 4) + clzHelperStepSchedule.length + 42 by omega]
      rw [hInnerExec]
      rw [open_bind_pure_left]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      rw [open_bind_pure_left]
      simp [EvmYul.Yul.State.restrictStoreTo, EvmYul.Yul.State.store,
        finalVars]
    · have hRestricted :
          ClzHelperFrame arg ret result.snd result.fst shared finalVars :=
        ClzHelperFrame.restrict_to_scope arg ret argValue retValue
          result.snd result.fst shared vars innerVars hFrame hInnerFrame
      simpa [clzHelperValue, hArgZeroFalse, result] using hRestricted

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

theorem clzHelperYulInterface_call_value_succ
    {object : Frontend.Object} {ordered : Yul.OrderedProgram}
    {helper arg ret : Name}
    (hInterface :
      ClzHelperYulInterface object.functions (some helper) (some arg)
        (some ret))
    (hConvert : object.toSolcYulOrderedProgram? = some ordered)
    (hArgRet : arg ≠ ret)
    (fuel : Nat) (argValue : Word)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) :
    ∃ finalState,
      Yul.InteractionSemantics.call
          (fuel + clzHelperStepSchedule.length + 51)
          [argValue] (some helper) (some ordered.program.contract)
          (.Ok shared vars) =
        pure (finalState, [clzHelperValue argValue]) := by
  let zero := EvmYul.UInt256.ofNat 0
  let entryVars : EvmYul.Yul.VarStore :=
    ((default : EvmYul.Yul.VarStore).insert ret zero).insert arg argValue
  have hEntry :
      EvmYul.Yul.State.mkOk
          ((EvmYul.Yul.State.Ok shared vars).initcall
            [arg] [ret] [argValue]) =
        (EvmYul.Yul.State.Ok shared entryVars) := by
    simp [entryVars, zero, EvmYul.Yul.State.initcall,
      EvmYul.Yul.State.setStore, EvmYul.Yul.State.zeroFill,
      EvmYul.Yul.State.multifill, EvmYul.Yul.State.mkOk,
      EvmYul.Yul.State.insert, EvmYul.UInt256.ofNat, Id.run]
  have hEntryFrame :
      ClzHelperFrame arg ret argValue zero shared entryVars := by
    constructor
    · simp [entryVars, EvmYul.Yul.State.lookup?]
    · have hRetArg : ret ≠ arg := fun h => hArgRet h.symm
      simp [entryVars, EvmYul.Yul.State.lookup?,
        Finmap.lookup_insert_of_ne
          ((default : EvmYul.Yul.VarStore).insert ret zero) hRetArg]
  rcases clzHelperAstBody_block_exec_succ
      fuel arg ret hArgRet argValue zero
      (some ordered.program.contract) shared entryVars hEntryFrame with
    ⟨finalArg, bodyVars, hBody, hFinalFrame⟩
  let finalState :=
    ((EvmYul.Yul.State.Ok shared bodyVars).reviveJump.overwrite?
      (EvmYul.Yul.State.Ok shared vars)).setStore
        (EvmYul.Yul.State.Ok shared vars)
  refine ⟨finalState, ?_⟩
  rw [show fuel + clzHelperStepSchedule.length + 51 =
    (fuel + clzHelperStepSchedule.length + 50) + 1 by omega]
  rw [clzHelperYulInterface_call_succ
    (object := object) (ordered := ordered)
    (helper? := some helper) (arg? := some arg) (ret? := some ret)
    hInterface hConvert (fuel + clzHelperStepSchedule.length + 50)
    [argValue] (.Ok shared vars)]
  rw [hEntry]
  rw [hBody]
  rw [open_bind_pure_left]
  have hLookupRet :
      (EvmYul.Yul.State.Ok shared bodyVars).lookup! ret =
        clzHelperValue argValue := by
    simp [EvmYul.Yul.State.lookup!, hFinalFrame.2]
  simp [finalState, hLookupRet]

theorem codeGeneratedNormalizationEvidence_clzHelper_call_value_succ
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (helper? : Option Name) (arg? : Option Name) (ret? : Option Name),
      match helper?, arg?, ret? with
      | some helper, some arg, some ret =>
          ∀ (fuel : Nat) (argValue : Word)
            (shared : EvmYul.SharedState .Yul)
            (vars : EvmYul.Yul.VarStore),
            ∃ finalState,
              Yul.InteractionSemantics.call
                  (fuel + clzHelperStepSchedule.length + 51)
                  [argValue] (some helper)
                  (some ordered.program.contract) (.Ok shared vars) =
                pure (finalState, [clzHelperValue argValue])
      | _, _, _ => True := by
  rcases hEvidence with
    ⟨_coreDispatcher, _state, helper?, arg?, ret?, _hCore,
      _hElab, _hFunctions, _hHelper, _hArg, _hRet, hDistinct,
      _hClz, hInterface, _hHoisted⟩
  refine ⟨helper?, arg?, ret?, ?_⟩
  cases helper? <;> cases arg? <;> cases ret? <;>
    simp [ClzNamesDistinct] at hDistinct hInterface ⊢
  rename_i helper arg ret
  intro fuel argValue shared vars
  exact
    clzHelperYulInterface_call_value_succ
      hInterface hConvert hDistinct fuel argValue shared vars

theorem generatedNormalizationEvidence_clzHelper_call_value_succ
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (helper? : Option Name) (arg? : Option Name)
            (ret? : Option Name),
          match helper?, arg?, ret? with
          | some helper, some arg, some ret =>
              ∀ (fuel : Nat) (argValue : Word)
                (shared : EvmYul.SharedState .Yul)
                (vars : EvmYul.Yul.VarStore),
                ∃ finalState,
                  Yul.InteractionSemantics.call
                      (fuel + clzHelperStepSchedule.length + 51)
                      [argValue] (some helper)
                      (some ordered.program.contract) (.Ok shared vars) =
                    pure (finalState, [clzHelperValue argValue])
          | _, _, _ => True := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_clzHelper_call_value_succ
          hCodeEvidence hConvert

theorem decodeAndElaborateSolcIr?_clzHelper_call_value_succ
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (helper? : Option Name) (arg? : Option Name)
                      (ret? : Option Name),
                    match helper?, arg?, ret? with
                    | some helper, some arg, some ret =>
                        ∀ (fuel : Nat) (argValue : Word)
                          (shared : EvmYul.SharedState .Yul)
                          (vars : EvmYul.Yul.VarStore),
                          ∃ finalState,
                            Yul.InteractionSemantics.call
                                (fuel + clzHelperStepSchedule.length + 51)
                                [argValue] (some helper)
                                (some ordered.program.contract)
                                (.Ok shared vars) =
                              pure (finalState, [clzHelperValue argValue])
                    | _, _, _ => True := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_clzHelper_call_value_succ
        hEvidence hObjectConvert⟩

def HoistedCallSemantics (state : State)
    (ordered : Yul.OrderedProgram) : Prop :=
  ∀ {generated : Name} {fn : Frontend.FunctionDef}
    {yulFn : Yul.AstFunctionDefinition},
    (generated, fn) ∈ state.hoistedFunctions →
      fn.toYul? = some yulFn →
        ∀ (fuel : Nat) (args : List Word)
          (source : Yul.InteractionSemantics.State),
          Yul.InteractionSemantics.call (fuel + 1) args
              (some generated) (some ordered.program.contract) source =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.exec fuel
                (.Block yulFn.body) (some ordered.program.contract)
                (EvmYul.Yul.State.mkOk
                  (source.initcall yulFn.params yulFn.rets args)))
              (fun stateAfterBody =>
                pure
                  ((stateAfterBody.reviveJump.overwrite? source).setStore
                    source,
                    List.map stateAfterBody.lookup! yulFn.rets))

theorem yulExprUserCall_lookup_of_exprOk
    {profile : Yul.SolcValidation.DialectProfile}
    {contract : Yul.AstContract} {vars : List Name}
    {expected : Nat} {functionName : Name}
    {args : List Yul.AstExpr} {expr : Yul.AstExpr}
    (hOccurrence :
      Yul.YulOccurrence.ExprUserCall functionName args expr)
    (hOk :
      Yul.SolcValidation.ExprOk? profile contract vars expected expr =
        true) :
    ∃ params returns body,
      contract.functions.lookup functionName =
        some (.Def params returns body) := by
  induction hOccurrence generalizing expected with
  | here =>
      exact Yul.SolcValidation.exprOk_functionCall_lookup_exists hOk
  | @callArg callee outerArgs arg hMem _ ih =>
      cases callee with
      | inl prim =>
          have hArgsOk :
              Yul.SolcValidation.ExprsOk? profile contract vars
                  outerArgs =
                true :=
            Yul.SolcValidation.exprsOk_of_exprOk_primitive hOk
          have hArgOk :
              Yul.SolcValidation.ExprOk? profile contract vars 1 arg =
                true :=
            Yul.SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk hMem
          exact ih hArgOk
      | inr outerName =>
          cases hLookup :
              contract.functions.lookup outerName with
          | none =>
              simp [Yul.SolcValidation.ExprOk?,
                Yul.SolcValidation.lookupFunction?, hLookup] at hOk
          | some outerFn =>
              cases outerFn with
              | Def params returns body =>
                  have hArgsOk :
                      Yul.SolcValidation.ExprsOk? profile contract vars
                          outerArgs =
                        true :=
                    Yul.SolcValidation.exprsOk_of_exprOk_functionCall
                      hOk hLookup
                  have hArgOk :
                      Yul.SolcValidation.ExprOk? profile contract vars 1
                          arg =
                        true :=
                    Yul.SolcValidation.exprOk_of_exprsOk_of_mem hArgsOk
                      hMem
                  exact ih hArgOk

mutual
  theorem yulStmtUserCall_lookup_of_stmtOk
      {profile : Yul.SolcValidation.DialectProfile}
      {contract : Yul.AstContract}
      {functionNames vars : List Name}
      {canBreak canContinue canLeave : Bool}
      {functionName : Name} {args : List Yul.AstExpr}
      {stmt : Yul.AstStmt}
      (hOccurrence :
        Yul.YulOccurrence.StmtUserCall functionName args stmt)
      (hOk :
        Yul.SolcValidation.StmtOk? profile contract functionNames vars
            canBreak canContinue canLeave stmt =
          true) :
      ∃ params returns body,
        contract.functions.lookup functionName =
          some (.Def params returns body) := by
    cases hOccurrence with
    | block hBody =>
        exact yulStmtListUserCall_lookup_of_stmtsOk hBody hOk
    | letValue hValue =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulExprUserCall_lookup_of_exprOk hValue hOk.2
    | assignValue hValue =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulExprUserCall_lookup_of_exprOk hValue hOk.2
    | exprStmt hValue =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulExprUserCall_lookup_of_exprOk hValue hOk
    | switchScrutinee hScrutinee =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulExprUserCall_lookup_of_exprOk hScrutinee hOk.1
    | switchCase hCases =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulCaseListUserCall_lookup_of_casesOk hCases hOk.2.2.1
    | switchDefault hDefault =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulStmtListUserCall_lookup_of_stmtsOk hDefault hOk.2.2.2
    | forCondition hCondition =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulExprUserCall_lookup_of_exprOk hCondition hOk.1
    | forPost hPost =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulStmtListUserCall_lookup_of_stmtsOk hPost hOk.2.1
    | forBody hBody =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulStmtListUserCall_lookup_of_stmtsOk hBody hOk.2.2
    | ifCondition hCondition =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulExprUserCall_lookup_of_exprOk hCondition hOk.1
    | ifBody hBody =>
        simp [Yul.SolcValidation.StmtOk?] at hOk
        exact yulStmtListUserCall_lookup_of_stmtsOk hBody hOk.2

  theorem yulStmtListUserCall_lookup_of_stmtsOk
      {profile : Yul.SolcValidation.DialectProfile}
      {contract : Yul.AstContract}
      {functionNames vars : List Name}
      {canBreak canContinue canLeave : Bool}
      {functionName : Name} {args : List Yul.AstExpr}
      {stmts : List Yul.AstStmt}
      (hOccurrence :
        Yul.YulOccurrence.StmtListUserCall functionName args stmts)
      (hOk :
        Yul.SolcValidation.StmtsOk? profile contract functionNames vars
            canBreak canContinue canLeave stmts =
          true) :
      ∃ params returns body,
        contract.functions.lookup functionName =
          some (.Def params returns body) := by
    cases hOccurrence with
    | head hStmt =>
        have hParts := Yul.SolcValidation.stmtsOk_cons_parts hOk
        exact yulStmtUserCall_lookup_of_stmtOk hStmt hParts.1
    | tail hTail =>
        have hParts := Yul.SolcValidation.stmtsOk_cons_parts hOk
        exact yulStmtListUserCall_lookup_of_stmtsOk hTail hParts.2

  theorem yulCaseListUserCall_lookup_of_casesOk
      {profile : Yul.SolcValidation.DialectProfile}
      {contract : Yul.AstContract}
      {functionNames vars : List Name}
      {canBreak canContinue canLeave : Bool}
      {functionName : Name} {args : List Yul.AstExpr}
      {cases : List (Word × List Yul.AstStmt)}
      (hOccurrence :
        Yul.YulOccurrence.CaseListUserCall functionName args cases)
      (hOk :
        Yul.SolcValidation.CasesOk? profile contract functionNames vars
            canBreak canContinue canLeave cases =
          true) :
      ∃ params returns body,
        contract.functions.lookup functionName =
          some (.Def params returns body) := by
    cases hOccurrence with
    | head hBody =>
        simp [Yul.SolcValidation.CasesOk?] at hOk
        exact yulStmtListUserCall_lookup_of_stmtsOk hBody hOk.1
    | tail hTail =>
        simp [Yul.SolcValidation.CasesOk?] at hOk
        exact yulCaseListUserCall_lookup_of_casesOk hTail hOk.2
end

structure FocusedGeneratedCallOccurrence
    (state : State) (ordered : Yul.OrderedProgram)
    (generated : Name) (fn : Frontend.FunctionDef)
    (params returns : List Name) (body : List Yul.AstStmt)
    (args : List Yul.AstExpr) : Prop where
  hoisted : (generated, fn) ∈ state.hoistedFunctions
  toYul? : fn.toYul? = some (.Def params returns body)
  lookup :
    ordered.program.contract.functions.lookup generated =
      some (.Def params returns body)

structure FocusedGeneratedCallPrefixEvidence
    (ordered : Yul.OrderedProgram)
    (generated : Name)
    (params returns : List Name) (body : List Yul.AstStmt)
    (args : List Yul.AstExpr) (stmts : List Yul.AstStmt)
    (fuel : Nat) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) : Prop where
  lookup :
    ordered.program.contract.functions.lookup generated =
      some (.Def params returns body)
  splitPrefix :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
      (suffix : List Yul.AstStmt),
      stmts = pre ++ stmt :: suffix ∧
        Yul.YulOccurrence.StmtUserCall generated args stmt ∧
          Yul.InteractionSemantics.execSeq
            (fuel + pre.length + 1) stmts code (.Ok shared vars) =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.execSeq
                (fuel + pre.length + 1) pre code (.Ok shared vars))
              (fun stateAfterPre =>
                Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                  (fuel + 1) (stmt :: suffix) code stateAfterPre)

namespace FocusedGeneratedCallPrefixEvidence

theorem of_yulOccurrence
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {fuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hLookup :
      ordered.program.contract.functions.lookup generated =
        some (.Def params returns body))
    (hOccurrence :
      Yul.YulOccurrence.StmtListUserCall generated args stmts) :
    FocusedGeneratedCallPrefixEvidence ordered generated params returns
      body args stmts fuel code shared vars := by
  rcases
      Yul.YulOccurrence.StmtListUserCall.exists_split_stmt_execSeq_prefix
        hOccurrence fuel code shared vars with
    ⟨pre, stmt, suffix, hSplit, hStmt, hPrefix⟩
  exact
    ⟨hLookup, pre, stmt, suffix, hSplit, hStmt, hPrefix⟩

theorem call_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {stmts : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hEvidence :
      FocusedGeneratedCallPrefixEvidence ordered generated params returns
        body argExprs stmts prefixFuel code shared vars)
    (callFuel : Nat) (args : List Word)
    (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.call (callFuel + 1) args
        (some generated) (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.exec callFuel
          (.Block body) (some ordered.program.contract)
          (EvmYul.Yul.State.mkOk
            (source.initcall params returns args)))
        (fun stateAfterBody =>
          pure
            ((stateAfterBody.reviveJump.overwrite? source).setStore
              source,
              List.map stateAfterBody.lookup! returns)) := by
  exact
    Yul.InteractionSemantics.Call.explicit_succ
      callFuel args generated ordered.program.contract params returns body
      source hEvidence.lookup

theorem evalValues_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hEvidence :
      FocusedGeneratedCallPrefixEvidence ordered generated params returns
        body argExprs stmts prefixFuel code shared vars)
    (fuel : Nat) (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.evalValues (fuel + 2)
        (.Call (.inr generated) argExprs)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 1)
          argExprs.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              pure
                ((stateAfterBody.reviveJump.overwrite?
                    argsResult.1).setStore argsResult.1,
                  List.map stateAfterBody.lookup! returns))) := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.EvalValues.internal_succ
    (fuel + 1) generated argExprs (some ordered.program.contract) source]
  apply congrArg
  funext argsResult
  exact call_succ hEvidence fuel argsResult.2.reverse argsResult.1

theorem eval_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hEvidence :
      FocusedGeneratedCallPrefixEvidence ordered generated params returns
        body argExprs stmts prefixFuel code shared vars)
    (fuel : Nat) (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.eval (fuel + 2)
        (.Call (.inr generated) argExprs)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs (fuel + 1)
            argExprs.reverse (some ordered.program.contract) source)
          (fun argsResult =>
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.exec fuel
                (.Block body) (some ordered.program.contract)
                (EvmYul.Yul.State.mkOk
                  (argsResult.1.initcall params returns
                    argsResult.2.reverse)))
              (fun stateAfterBody =>
                pure
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1,
                    List.map stateAfterBody.lookup! returns))))
        (fun result => pure (result.1, result.2.head!)) := by
  rw [Yul.InteractionSemantics.eval_eq_bind]
  rw [evalValues_succ hEvidence fuel source]

end FocusedGeneratedCallPrefixEvidence

structure FocusedGeneratedCallSemanticInterface
    (ordered : Yul.OrderedProgram)
    (generated : Name)
    (params returns : List Name) (body : List Yul.AstStmt)
    (args : List Yul.AstExpr) (stmts : List Yul.AstStmt)
    (prefixFuel : Nat) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) : Prop where
  prefixEvidence :
    FocusedGeneratedCallPrefixEvidence ordered generated params returns
      body args stmts prefixFuel code shared vars
  call_succ :
    ∀ (fuel : Nat) (callArgs : List Word)
      (source : Yul.InteractionSemantics.State),
      Yul.InteractionSemantics.call (fuel + 1) callArgs
          (some generated) (some ordered.program.contract) source =
        Simulation.Interaction.bind
          (Yul.InteractionSemantics.exec fuel
            (.Block body) (some ordered.program.contract)
            (EvmYul.Yul.State.mkOk
              (source.initcall params returns callArgs)))
          (fun stateAfterBody =>
            pure
              ((stateAfterBody.reviveJump.overwrite? source).setStore
                source,
                List.map stateAfterBody.lookup! returns))
  evalValues_succ :
    ∀ (fuel : Nat) (source : Yul.InteractionSemantics.State),
      Yul.InteractionSemantics.evalValues (fuel + 2)
          (.Call (.inr generated) args)
          (some ordered.program.contract) source =
        Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs (fuel + 1)
            args.reverse (some ordered.program.contract) source)
          (fun argsResult =>
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.exec fuel
                (.Block body) (some ordered.program.contract)
                (EvmYul.Yul.State.mkOk
                  (argsResult.1.initcall params returns
                    argsResult.2.reverse)))
              (fun stateAfterBody =>
                pure
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1,
                    List.map stateAfterBody.lookup! returns)))
  eval_succ :
    ∀ (fuel : Nat) (source : Yul.InteractionSemantics.State),
      Yul.InteractionSemantics.eval (fuel + 2)
          (.Call (.inr generated) args)
          (some ordered.program.contract) source =
        Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (Yul.InteractionSemantics.evalArgs (fuel + 1)
              args.reverse (some ordered.program.contract) source)
            (fun argsResult =>
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.exec fuel
                  (.Block body) (some ordered.program.contract)
                  (EvmYul.Yul.State.mkOk
                    (argsResult.1.initcall params returns
                      argsResult.2.reverse)))
                (fun stateAfterBody =>
                  pure
                    ((stateAfterBody.reviveJump.overwrite?
                        argsResult.1).setStore argsResult.1,
                      List.map stateAfterBody.lookup! returns))))
          (fun result => pure (result.1, result.2.head!))

namespace FocusedGeneratedCallSemanticInterface

theorem of_prefixEvidence
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hEvidence :
      FocusedGeneratedCallPrefixEvidence ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    FocusedGeneratedCallSemanticInterface ordered generated params returns
      body args stmts prefixFuel code shared vars := by
  exact
    { prefixEvidence := hEvidence
      call_succ := by
        intro fuel callArgs source
        exact
          FocusedGeneratedCallPrefixEvidence.call_succ hEvidence fuel
            callArgs source
      evalValues_succ := by
        intro fuel source
        exact
          FocusedGeneratedCallPrefixEvidence.evalValues_succ hEvidence fuel
            source
      eval_succ := by
        intro fuel source
        exact
          FocusedGeneratedCallPrefixEvidence.eval_succ hEvidence fuel source }

theorem exprStmtCall_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars)
    (fuel : Nat) (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.exec (fuel + 3)
        (.ExprStmtCall (.Call (.inr generated) args))
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 2)
          args.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              pure
                (Yul.InteractionSemantics.stateModel.multifill []
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1)
                  (List.map stateAfterBody.lookup! returns)))) := by
  rw [show fuel + 3 = (fuel + 1) + 2 by omega]
  rw [Yul.InteractionSemantics.Exec.expr_internal_succ]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs (fuel + 2)
        args.reverse (some ordered.program.contract) source))
  intro argsResult _hDone
  rw [hInterface.call_succ fuel argsResult.2.reverse argsResult.1]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.exec fuel
        (.Block body) (some ordered.program.contract)
        (EvmYul.Yul.State.mkOk
          (argsResult.1.initcall params returns argsResult.2.reverse))))
  intro stateAfterBody _hBodyDone
  rfl

theorem letCall_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars)
    (fuel : Nat) (names : List EvmYul.Identifier)
    (source : Yul.InteractionSemantics.State)
    (hCheck : EvmYul.Yul.checkDeclaration source names = .ok ()) :
    Yul.InteractionSemantics.exec (fuel + 3)
        (.Let names (some (.Call (.inr generated) args)))
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 1)
          args.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              pure
                (Yul.InteractionSemantics.stateModel.multifill names
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1)
                  (List.map stateAfterBody.lookup! returns)))) := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.let_some_succ
    (fuel + 2) names _ (some ordered.program.contract) source hCheck]
  rw [hInterface.evalValues_succ fuel source]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs (fuel + 1)
        args.reverse (some ordered.program.contract) source))
  intro argsResult _hDone
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.exec fuel
        (.Block body) (some ordered.program.contract)
        (EvmYul.Yul.State.mkOk
          (argsResult.1.initcall params returns argsResult.2.reverse))))
  intro stateAfterBody _hBodyDone
  rfl

theorem assignCall_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars)
    (fuel : Nat) (names : List EvmYul.Identifier)
    (source : Yul.InteractionSemantics.State)
    (hCheck : EvmYul.Yul.checkAssignment source names = .ok ()) :
    Yul.InteractionSemantics.exec (fuel + 3)
        (.Assign names (.Call (.inr generated) args))
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 1)
          args.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              pure
                (Yul.InteractionSemantics.stateModel.multifill names
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1)
                  (List.map stateAfterBody.lookup! returns)))) := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.assign_succ
    (fuel + 2) names _ (some ordered.program.contract) source hCheck]
  rw [hInterface.evalValues_succ fuel source]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs (fuel + 1)
        args.reverse (some ordered.program.contract) source))
  intro argsResult _hDone
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.exec fuel
        (.Block body) (some ordered.program.contract)
        (EvmYul.Yul.State.mkOk
          (argsResult.1.initcall params returns argsResult.2.reverse))))
  intro stateAfterBody _hBodyDone
  rfl

theorem ifConditionCall_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars)
    (fuel : Nat) (ifBody : List Yul.AstStmt)
    (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.exec (fuel + 3)
        (.If (.Call (.inr generated) args) ifBody)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 1)
          args.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              let stateAfterCall :=
                ((stateAfterBody.reviveJump.overwrite?
                    argsResult.1).setStore argsResult.1)
              let values := List.map stateAfterBody.lookup! returns
              if values.head! ≠ EvmYul.UInt256.ofNat 0 then
                Yul.InteractionSemantics.exec (fuel + 2)
                  (.Block ifBody) (some ordered.program.contract)
                  stateAfterCall
              else
                pure stateAfterCall)) := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.if_succ]
  rw [hInterface.eval_succ fuel source]
  rw [Simulation.Interaction.bind_assoc]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs (fuel + 1)
        args.reverse (some ordered.program.contract) source))
  intro argsResult _hDone
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.exec fuel
        (.Block body) (some ordered.program.contract)
        (EvmYul.Yul.State.mkOk
          (argsResult.1.initcall params returns argsResult.2.reverse))))
  intro stateAfterBody _hBodyDone
  rw [open_bind_pure_left]
  rfl

theorem switchScrutineeCall_succ
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars)
    (fuel : Nat) (cases : List (Word × List Yul.AstStmt))
    (defaultBody : List Yul.AstStmt)
    (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.exec (fuel + 3)
        (.Switch (.Call (.inr generated) args) cases defaultBody)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 1)
          args.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              let stateAfterCall :=
                ((stateAfterBody.reviveJump.overwrite?
                    argsResult.1).setStore argsResult.1)
              let values := List.map stateAfterBody.lookup! returns
              Yul.InteractionSemantics.exec (fuel + 2)
                (.Block
                  (EvmYul.Yul.selectSwitchCase values.head! defaultBody
                    cases))
                (some ordered.program.contract) stateAfterCall)) := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.switch_succ]
  rw [hInterface.eval_succ fuel source]
  rw [Simulation.Interaction.bind_assoc]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs (fuel + 1)
        args.reverse (some ordered.program.contract) source))
  intro argsResult _hDone
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.exec fuel
        (.Block body) (some ordered.program.contract)
        (EvmYul.Yul.State.mkOk
          (argsResult.1.initcall params returns argsResult.2.reverse))))
  intro stateAfterBody _hBodyDone
  rw [open_bind_pure_left]
  rfl

structure ExprContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars)
    (expr : Yul.AstExpr) : Prop where
  evalArgContext :
    Yul.YulOccurrence.ExprUserCall.EvalArgContext generated args expr

theorem ExprContext.ofOccurrence
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {expr : Yul.AstExpr}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hOccurrence :
      Yul.YulOccurrence.ExprUserCall generated args expr) :
    ExprContext hInterface expr :=
  ⟨Yul.YulOccurrence.ExprUserCall.evalArgContext hOccurrence⟩

theorem ExprContext.directOrCallArgPrefix
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {expr : Yul.AstExpr}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : ExprContext hInterface expr) :
    expr = .Call (.inr generated) args ∨
      ∃ (callee : EvmYul.Operation .Yul ⊕ Name)
          (outerArgs before : List Yul.AstExpr) (arg : Yul.AstExpr)
          (after : List Yul.AstExpr),
        expr = .Call callee outerArgs ∧
          outerArgs.reverse = before ++ arg :: after ∧
            ExprContext hInterface arg ∧
              ∀ (fuel : Nat) (source : Yul.InteractionSemantics.State),
                Yul.InteractionSemantics.evalValues
                    (fuel + 2 * before.length + 3)
                    expr (some ordered.program.contract) source =
                  Simulation.Interaction.bind
                    (Yul.InteractionSemantics.evalArgs
                      (fuel + 2 * before.length + 2) before
                      (some ordered.program.contract) source)
                    (fun beforeResult =>
                      Simulation.Interaction.bind
                        (Yul.InteractionSemantics.evalValues (fuel + 1)
                          arg (some ordered.program.contract)
                          beforeResult.1)
                        (fun argResult =>
                          Simulation.Interaction.bind
                            (Yul.InteractionSemantics.evalArgs fuel after
                              (some ordered.program.contract) argResult.1)
                            (fun afterResult =>
                              let evaluatedArgs :=
                                beforeResult.2 ++
                                  argResult.2.head! :: afterResult.2
                              match callee with
                              | .inl prim =>
                                  Yul.InteractionSemantics.primitiveSemantics.eval
                                    (fuel + 2 * before.length + 2)
                                    afterResult.1 prim
                                    evaluatedArgs.reverse
                              | .inr functionName =>
                                  Yul.InteractionSemantics.call
                                    (fuel + 2 * before.length + 2)
                                    evaluatedArgs.reverse
                                    (some functionName)
                                    (some ordered.program.contract)
                                    afterResult.1))) := by
  cases hContext with
  | mk hEvalArgContext =>
      cases hEvalArgContext with
      | here =>
          exact Or.inl rfl
      | @callArg callee outerArgs arg before after hSplit hTail =>
          refine
            Or.inr
              ⟨callee, outerArgs, before, arg, after, rfl, hSplit,
                ⟨hTail⟩, ?_⟩
          intro fuel source
          exact
            Yul.YulOccurrence.ExprUserCall.evalValues_callArgPrefix_succ
              fuel callee outerArgs before arg after
              (some ordered.program.contract) source hSplit

mutual
  inductive StmtContext
      {ordered : Yul.OrderedProgram}
      {generated : Name}
      {params returns : List Name} {body : List Yul.AstStmt}
      {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
      {prefixFuel : Nat} {code : Option Yul.AstContract}
      {shared : EvmYul.SharedState .Yul}
      {vars : EvmYul.Yul.VarStore}
      (hInterface :
        FocusedGeneratedCallSemanticInterface ordered generated params returns
          body args stmts prefixFuel code shared vars) :
      Yul.AstStmt → Prop where
    | block {blockBody : List Yul.AstStmt} :
        StmtListContext hInterface blockBody →
          StmtContext hInterface (.Block blockBody)
    | letValue {names : List Name} {value : Yul.AstExpr} :
        ExprContext hInterface value →
          StmtContext hInterface (.Let names (some value))
    | assignValue {names : List Name} {value : Yul.AstExpr} :
        ExprContext hInterface value →
          StmtContext hInterface (.Assign names value)
    | exprStmt {value : Yul.AstExpr} :
        ExprContext hInterface value →
          StmtContext hInterface (.ExprStmtCall value)
    | switchScrutinee
        {scrutinee : Yul.AstExpr} {cases : List (Word × List Yul.AstStmt)}
        {defaultBody : List Yul.AstStmt} :
        ExprContext hInterface scrutinee →
          StmtContext hInterface (.Switch scrutinee cases defaultBody)
    | switchCase
        {scrutinee : Yul.AstExpr} {cases : List (Word × List Yul.AstStmt)}
        {defaultBody : List Yul.AstStmt} :
        CaseListContext hInterface cases →
          StmtContext hInterface (.Switch scrutinee cases defaultBody)
    | switchDefault
        {scrutinee : Yul.AstExpr} {cases : List (Word × List Yul.AstStmt)}
        {defaultBody : List Yul.AstStmt} :
        StmtListContext hInterface defaultBody →
          StmtContext hInterface (.Switch scrutinee cases defaultBody)
    | forCondition
        {condition : Yul.AstExpr} {post body : List Yul.AstStmt} :
        ExprContext hInterface condition →
          StmtContext hInterface (.For condition post body)
    | forPost
        {condition : Yul.AstExpr} {post body : List Yul.AstStmt} :
        StmtListContext hInterface post →
          StmtContext hInterface (.For condition post body)
    | forBody
        {condition : Yul.AstExpr} {post body : List Yul.AstStmt} :
        StmtListContext hInterface body →
          StmtContext hInterface (.For condition post body)
    | ifCondition {condition : Yul.AstExpr} {body : List Yul.AstStmt} :
        ExprContext hInterface condition →
          StmtContext hInterface (.If condition body)
    | ifBody {condition : Yul.AstExpr} {body : List Yul.AstStmt} :
        StmtListContext hInterface body →
          StmtContext hInterface (.If condition body)

  inductive StmtListContext
      {ordered : Yul.OrderedProgram}
      {generated : Name}
      {params returns : List Name} {body : List Yul.AstStmt}
      {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
      {prefixFuel : Nat} {code : Option Yul.AstContract}
      {shared : EvmYul.SharedState .Yul}
      {vars : EvmYul.Yul.VarStore}
      (hInterface :
        FocusedGeneratedCallSemanticInterface ordered generated params returns
          body args stmts prefixFuel code shared vars) :
      List Yul.AstStmt → Prop where
    | head {stmt : Yul.AstStmt} {rest : List Yul.AstStmt} :
        StmtContext hInterface stmt →
          StmtListContext hInterface (stmt :: rest)
    | tail {stmt : Yul.AstStmt} {rest : List Yul.AstStmt} :
        StmtListContext hInterface rest →
          StmtListContext hInterface (stmt :: rest)

  inductive CaseListContext
      {ordered : Yul.OrderedProgram}
      {generated : Name}
      {params returns : List Name} {body : List Yul.AstStmt}
      {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
      {prefixFuel : Nat} {code : Option Yul.AstContract}
      {shared : EvmYul.SharedState .Yul}
      {vars : EvmYul.Yul.VarStore}
      (hInterface :
        FocusedGeneratedCallSemanticInterface ordered generated params returns
          body args stmts prefixFuel code shared vars) :
      List (Word × List Yul.AstStmt) → Prop where
    | head {value : Word} {caseBody : List Yul.AstStmt}
        {rest : List (Word × List Yul.AstStmt)} :
        StmtListContext hInterface caseBody →
          CaseListContext hInterface ((value, caseBody) :: rest)
    | tail {head : Word × List Yul.AstStmt}
        {rest : List (Word × List Yul.AstStmt)} :
        CaseListContext hInterface rest →
          CaseListContext hInterface (head :: rest)
end

inductive StmtExprSlot
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    Yul.AstStmt → Yul.AstExpr → Prop where
  | letValue {names : List Name} {value : Yul.AstExpr} :
      ExprContext hInterface value →
        StmtExprSlot hInterface (.Let names (some value)) value
  | assignValue {names : List Name} {value : Yul.AstExpr} :
      ExprContext hInterface value →
        StmtExprSlot hInterface (.Assign names value) value
  | exprStmt {value : Yul.AstExpr} :
      ExprContext hInterface value →
        StmtExprSlot hInterface (.ExprStmtCall value) value
  | switchScrutinee
      {scrutinee : Yul.AstExpr} {cases : List (Word × List Yul.AstStmt)}
      {defaultBody : List Yul.AstStmt} :
      ExprContext hInterface scrutinee →
        StmtExprSlot hInterface (.Switch scrutinee cases defaultBody)
          scrutinee
  | forCondition {condition : Yul.AstExpr}
      {post body : List Yul.AstStmt} :
      ExprContext hInterface condition →
        StmtExprSlot hInterface (.For condition post body) condition
  | ifCondition {condition : Yul.AstExpr} {body : List Yul.AstStmt} :
      ExprContext hInterface condition →
        StmtExprSlot hInterface (.If condition body) condition

inductive StmtListSlot
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    Yul.AstStmt → List Yul.AstStmt → Prop where
  | block {blockBody : List Yul.AstStmt} :
      StmtListContext hInterface blockBody →
        StmtListSlot hInterface (.Block blockBody) blockBody
  | switchDefault
      {scrutinee : Yul.AstExpr} {cases : List (Word × List Yul.AstStmt)}
      {defaultBody : List Yul.AstStmt} :
      StmtListContext hInterface defaultBody →
        StmtListSlot hInterface (.Switch scrutinee cases defaultBody)
          defaultBody
  | forPost {condition : Yul.AstExpr} {post body : List Yul.AstStmt} :
      StmtListContext hInterface post →
        StmtListSlot hInterface (.For condition post body) post
  | forBody {condition : Yul.AstExpr} {post body : List Yul.AstStmt} :
      StmtListContext hInterface body →
        StmtListSlot hInterface (.For condition post body) body
  | ifBody {condition : Yul.AstExpr} {body : List Yul.AstStmt} :
      StmtListContext hInterface body →
        StmtListSlot hInterface (.If condition body) body

inductive StmtCaseListSlot
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    Yul.AstStmt → List (Word × List Yul.AstStmt) → Prop where
  | switchCase
      {scrutinee : Yul.AstExpr} {cases : List (Word × List Yul.AstStmt)}
      {defaultBody : List Yul.AstStmt} :
      CaseListContext hInterface cases →
        StmtCaseListSlot hInterface (.Switch scrutinee cases defaultBody)
          cases

theorem StmtContext.toSlot
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : StmtContext hInterface stmt) :
    (∃ expr, StmtExprSlot hInterface stmt expr) ∨
      (∃ stmtList, StmtListSlot hInterface stmt stmtList) ∨
        (∃ cases, StmtCaseListSlot hInterface stmt cases) := by
  cases hContext with
  | block hBody =>
      exact Or.inr (Or.inl ⟨_, StmtListSlot.block hBody⟩)
  | letValue hValue =>
      exact Or.inl ⟨_, StmtExprSlot.letValue hValue⟩
  | assignValue hValue =>
      exact Or.inl ⟨_, StmtExprSlot.assignValue hValue⟩
  | exprStmt hValue =>
      exact Or.inl ⟨_, StmtExprSlot.exprStmt hValue⟩
  | switchScrutinee hScrutinee =>
      exact Or.inl ⟨_, StmtExprSlot.switchScrutinee hScrutinee⟩
  | switchCase hCases =>
      exact Or.inr (Or.inr ⟨_, StmtCaseListSlot.switchCase hCases⟩)
  | switchDefault hDefault =>
      exact Or.inr (Or.inl ⟨_, StmtListSlot.switchDefault hDefault⟩)
  | forCondition hCondition =>
      exact Or.inl ⟨_, StmtExprSlot.forCondition hCondition⟩
  | forPost hPost =>
      exact Or.inr (Or.inl ⟨_, StmtListSlot.forPost hPost⟩)
  | forBody hBody =>
      exact Or.inr (Or.inl ⟨_, StmtListSlot.forBody hBody⟩)
  | ifCondition hCondition =>
      exact Or.inl ⟨_, StmtExprSlot.ifCondition hCondition⟩
  | ifBody hBody =>
      exact Or.inr (Or.inl ⟨_, StmtListSlot.ifBody hBody⟩)

namespace StmtExprSlot

theorem exprContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {expr : Yul.AstExpr}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtExprSlot hInterface stmt expr) :
    ExprContext hInterface expr := by
  cases hSlot with
  | letValue hExpr => exact hExpr
  | assignValue hExpr => exact hExpr
  | exprStmt hExpr => exact hExpr
  | switchScrutinee hExpr => exact hExpr
  | forCondition hExpr => exact hExpr
  | ifCondition hExpr => exact hExpr

theorem directOrCallArgPrefix
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {expr : Yul.AstExpr}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtExprSlot hInterface stmt expr) :
    expr = .Call (.inr generated) args ∨
      ∃ (callee : EvmYul.Operation .Yul ⊕ Name)
          (outerArgs before : List Yul.AstExpr) (arg : Yul.AstExpr)
          (after : List Yul.AstExpr),
        expr = .Call callee outerArgs ∧
          outerArgs.reverse = before ++ arg :: after ∧
            ExprContext hInterface arg ∧
              ∀ (fuel : Nat) (source : Yul.InteractionSemantics.State),
                Yul.InteractionSemantics.evalValues
                    (fuel + 2 * before.length + 3)
                    expr (some ordered.program.contract) source =
                  Simulation.Interaction.bind
                    (Yul.InteractionSemantics.evalArgs
                      (fuel + 2 * before.length + 2) before
                      (some ordered.program.contract) source)
                    (fun beforeResult =>
                      Simulation.Interaction.bind
                        (Yul.InteractionSemantics.evalValues (fuel + 1)
                          arg (some ordered.program.contract)
                          beforeResult.1)
                        (fun argResult =>
                          Simulation.Interaction.bind
                            (Yul.InteractionSemantics.evalArgs fuel after
                              (some ordered.program.contract) argResult.1)
                            (fun afterResult =>
                              let evaluatedArgs :=
                                beforeResult.2 ++
                                  argResult.2.head! :: afterResult.2
                              match callee with
                              | .inl prim =>
                                  Yul.InteractionSemantics.primitiveSemantics.eval
                                    (fuel + 2 * before.length + 2)
                                    afterResult.1 prim
                                    evaluatedArgs.reverse
                              | .inr functionName =>
                                  Yul.InteractionSemantics.call
                                    (fuel + 2 * before.length + 2)
                                    evaluatedArgs.reverse
                                    (some functionName)
                                    (some ordered.program.contract)
                                    afterResult.1))) := by
  exact ExprContext.directOrCallArgPrefix (exprContext hSlot)

end StmtExprSlot

mutual
  theorem StmtContext.ofOccurrence
      {ordered : Yul.OrderedProgram}
      {generated : Name}
      {params returns : List Name} {body : List Yul.AstStmt}
      {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
      {prefixFuel : Nat} {code : Option Yul.AstContract}
      {shared : EvmYul.SharedState .Yul}
      {vars : EvmYul.Yul.VarStore}
      {stmt : Yul.AstStmt}
      {hInterface :
        FocusedGeneratedCallSemanticInterface ordered generated params returns
          body args stmts prefixFuel code shared vars}
      (hOccurrence :
        Yul.YulOccurrence.StmtUserCall generated args stmt) :
      StmtContext hInterface stmt := by
    cases hOccurrence with
    | block hBody =>
        exact StmtContext.block (StmtListContext.ofOccurrence hBody)
    | letValue hValue =>
        exact StmtContext.letValue (ExprContext.ofOccurrence hValue)
    | assignValue hValue =>
        exact StmtContext.assignValue (ExprContext.ofOccurrence hValue)
    | exprStmt hValue =>
        exact StmtContext.exprStmt (ExprContext.ofOccurrence hValue)
    | switchScrutinee hScrutinee =>
        exact StmtContext.switchScrutinee
          (ExprContext.ofOccurrence hScrutinee)
    | switchCase hCases =>
        exact StmtContext.switchCase (CaseListContext.ofOccurrence hCases)
    | switchDefault hDefault =>
        exact StmtContext.switchDefault
          (StmtListContext.ofOccurrence hDefault)
    | forCondition hCondition =>
        exact StmtContext.forCondition
          (ExprContext.ofOccurrence hCondition)
    | forPost hPost =>
        exact StmtContext.forPost (StmtListContext.ofOccurrence hPost)
    | forBody hBody =>
        exact StmtContext.forBody (StmtListContext.ofOccurrence hBody)
    | ifCondition hCondition =>
        exact StmtContext.ifCondition
          (ExprContext.ofOccurrence hCondition)
    | ifBody hBody =>
        exact StmtContext.ifBody (StmtListContext.ofOccurrence hBody)

  theorem StmtListContext.ofOccurrence
      {ordered : Yul.OrderedProgram}
      {generated : Name}
      {params returns : List Name} {body : List Yul.AstStmt}
      {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
      {prefixFuel : Nat} {code : Option Yul.AstContract}
      {shared : EvmYul.SharedState .Yul}
      {vars : EvmYul.Yul.VarStore}
      {stmtList : List Yul.AstStmt}
      {hInterface :
        FocusedGeneratedCallSemanticInterface ordered generated params returns
          body args stmts prefixFuel code shared vars}
      (hOccurrence :
        Yul.YulOccurrence.StmtListUserCall generated args stmtList) :
      StmtListContext hInterface stmtList := by
    cases hOccurrence with
    | head hStmt =>
        exact StmtListContext.head (StmtContext.ofOccurrence hStmt)
    | tail hTail =>
        exact StmtListContext.tail (StmtListContext.ofOccurrence hTail)

  theorem CaseListContext.ofOccurrence
      {ordered : Yul.OrderedProgram}
      {generated : Name}
      {params returns : List Name} {body : List Yul.AstStmt}
      {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
      {prefixFuel : Nat} {code : Option Yul.AstContract}
      {shared : EvmYul.SharedState .Yul}
      {vars : EvmYul.Yul.VarStore}
      {cases : List (Word × List Yul.AstStmt)}
      {hInterface :
        FocusedGeneratedCallSemanticInterface ordered generated params returns
          body args stmts prefixFuel code shared vars}
      (hOccurrence :
        Yul.YulOccurrence.CaseListUserCall generated args cases) :
      CaseListContext hInterface cases := by
    cases hOccurrence with
    | head hBody =>
        exact CaseListContext.head (StmtListContext.ofOccurrence hBody)
    | tail hTail =>
        exact CaseListContext.tail (CaseListContext.ofOccurrence hTail)
end

namespace StmtListContext

theorem exists_split_stmt
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : StmtListContext hInterface stmtList) :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmtList = pre ++ stmt :: suffix ∧
        StmtContext hInterface stmt := by
  induction stmtList with
  | nil =>
      cases hContext
  | cons head rest ih =>
      cases hContext with
      | head hStmt =>
          exact ⟨[], head, rest, rfl, hStmt⟩
      | tail hTail =>
          rcases ih hTail with ⟨pre, stmt, suffix, hSplit, hStmt⟩
          exact ⟨head :: pre, stmt, suffix, by simp [hSplit], hStmt⟩

theorem exists_split_stmt_execSeq_prefix
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : StmtListContext hInterface stmtList)
    (fuel : Nat) (codeOverride : Option Yul.AstContract)
    (entryShared : EvmYul.SharedState .Yul)
    (entryVars : EvmYul.Yul.VarStore) :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmtList = pre ++ stmt :: suffix ∧
        StmtContext hInterface stmt ∧
          Yul.InteractionSemantics.execSeq
            (fuel + pre.length + 1) stmtList codeOverride
            (.Ok entryShared entryVars) =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.execSeq
                (fuel + pre.length + 1) pre codeOverride
                (.Ok entryShared entryVars))
              (fun stateAfterPre =>
                Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                  (fuel + 1) (stmt :: suffix) codeOverride
                  stateAfterPre) := by
  rcases exists_split_stmt hContext with
    ⟨pre, stmt, suffix, hSplit, hStmt⟩
  subst stmtList
  exact
    ⟨pre, stmt, suffix, rfl, hStmt,
      Yul.YulOccurrence.StmtListUserCall.execSeq_prefix_cons_succ
        fuel pre stmt suffix codeOverride entryShared entryVars⟩

theorem exists_split_stmt_execSeq_prefix_all
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : StmtListContext hInterface stmtList) :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmtList = pre ++ stmt :: suffix ∧
        StmtContext hInterface stmt ∧
          ∀ (fuel : Nat) (codeOverride : Option Yul.AstContract)
            (entryShared : EvmYul.SharedState .Yul)
            (entryVars : EvmYul.Yul.VarStore),
            Yul.InteractionSemantics.execSeq
              (fuel + pre.length + 1) stmtList codeOverride
              (.Ok entryShared entryVars) =
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.execSeq
                  (fuel + pre.length + 1) pre codeOverride
                  (.Ok entryShared entryVars))
                (fun stateAfterPre =>
                  Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                    (fuel + 1) (stmt :: suffix) codeOverride
                    stateAfterPre) := by
  rcases exists_split_stmt hContext with
    ⟨pre, stmt, suffix, hSplit, hStmt⟩
  subst stmtList
  refine ⟨pre, stmt, suffix, rfl, hStmt, ?_⟩
  intro fuel codeOverride entryShared entryVars
  exact
    Yul.YulOccurrence.StmtListUserCall.execSeq_prefix_cons_succ
      fuel pre stmt suffix codeOverride entryShared entryVars

end StmtListContext

namespace CaseListContext

theorem exists_split_case
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {cases : List (Word × List Yul.AstStmt)}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : CaseListContext hInterface cases) :
    ∃ (pre : List (Word × List Yul.AstStmt)) (value : Word)
        (caseBody : List Yul.AstStmt)
        (suffix : List (Word × List Yul.AstStmt)),
      cases = pre ++ (value, caseBody) :: suffix ∧
        StmtListContext hInterface caseBody := by
  induction cases with
  | nil =>
      cases hContext
  | cons head rest ih =>
      cases hContext with
      | @head value caseBody _ hBody =>
          exact ⟨[], value, caseBody, rest, rfl, hBody⟩
      | tail hTail =>
          rcases ih hTail with
            ⟨pre, value, caseBody, suffix, hSplit, hBody⟩
          exact
            ⟨head :: pre, value, caseBody, suffix,
              by simp [hSplit], hBody⟩

end CaseListContext

namespace StmtListSlot

theorem stmtListContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtListSlot hInterface stmt stmtList) :
    StmtListContext hInterface stmtList := by
  cases hSlot with
  | block hList => exact hList
  | switchDefault hList => exact hList
  | forPost hList => exact hList
  | forBody hList => exact hList
  | ifBody hList => exact hList

theorem exists_split_stmt_execSeq_prefix
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtListSlot hInterface stmt stmtList)
    (fuel : Nat) (codeOverride : Option Yul.AstContract)
    (entryShared : EvmYul.SharedState .Yul)
    (entryVars : EvmYul.Yul.VarStore) :
    ∃ (pre : List Yul.AstStmt) (focused : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmtList = pre ++ focused :: suffix ∧
        StmtContext hInterface focused ∧
          Yul.InteractionSemantics.execSeq
            (fuel + pre.length + 1) stmtList codeOverride
            (.Ok entryShared entryVars) =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.execSeq
                (fuel + pre.length + 1) pre codeOverride
                (.Ok entryShared entryVars))
              (fun stateAfterPre =>
                Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                  (fuel + 1) (focused :: suffix) codeOverride
                  stateAfterPre) := by
  exact
    StmtListContext.exists_split_stmt_execSeq_prefix
      (stmtListContext hSlot) fuel codeOverride entryShared entryVars

theorem exists_split_stmt_execSeq_prefix_all
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtListSlot hInterface stmt stmtList) :
    ∃ (pre : List Yul.AstStmt) (focused : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmtList = pre ++ focused :: suffix ∧
        StmtContext hInterface focused ∧
          ∀ (fuel : Nat) (codeOverride : Option Yul.AstContract)
            (entryShared : EvmYul.SharedState .Yul)
            (entryVars : EvmYul.Yul.VarStore),
            Yul.InteractionSemantics.execSeq
              (fuel + pre.length + 1) stmtList codeOverride
              (.Ok entryShared entryVars) =
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.execSeq
                  (fuel + pre.length + 1) pre codeOverride
                  (.Ok entryShared entryVars))
                (fun stateAfterPre =>
                  Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                    (fuel + 1) (focused :: suffix) codeOverride
                    stateAfterPre) := by
  exact
    StmtListContext.exists_split_stmt_execSeq_prefix_all
      (stmtListContext hSlot)

end StmtListSlot

namespace StmtCaseListSlot

theorem caseListContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {cases : List (Word × List Yul.AstStmt)}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtCaseListSlot hInterface stmt cases) :
    CaseListContext hInterface cases := by
  cases hSlot with
  | switchCase hCases => exact hCases

theorem exists_split_case_stmt_execSeq_prefix
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {cases : List (Word × List Yul.AstStmt)}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtCaseListSlot hInterface stmt cases)
    (fuel : Nat) (codeOverride : Option Yul.AstContract)
    (entryShared : EvmYul.SharedState .Yul)
    (entryVars : EvmYul.Yul.VarStore) :
    ∃ (casePre : List (Word × List Yul.AstStmt)) (value : Word)
        (caseBody : List Yul.AstStmt)
        (caseSuffix : List (Word × List Yul.AstStmt))
        (pre : List Yul.AstStmt) (focused : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      cases = casePre ++ (value, caseBody) :: caseSuffix ∧
        caseBody = pre ++ focused :: suffix ∧
          StmtContext hInterface focused ∧
            Yul.InteractionSemantics.execSeq
              (fuel + pre.length + 1) caseBody codeOverride
              (.Ok entryShared entryVars) =
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.execSeq
                  (fuel + pre.length + 1) pre codeOverride
                  (.Ok entryShared entryVars))
                (fun stateAfterPre =>
                  Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                    (fuel + 1) (focused :: suffix) codeOverride
                    stateAfterPre) := by
  rcases CaseListContext.exists_split_case (caseListContext hSlot) with
    ⟨casePre, value, caseBody, caseSuffix, hCases, hBody⟩
  rcases
      StmtListContext.exists_split_stmt_execSeq_prefix hBody fuel
        codeOverride entryShared entryVars with
    ⟨pre, focused, suffix, hBodySplit, hFocused, hPrefix⟩
  exact
    ⟨casePre, value, caseBody, caseSuffix, pre, focused, suffix,
      hCases, hBodySplit, hFocused, hPrefix⟩

theorem exists_split_case_stmt_execSeq_prefix_all
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt} {cases : List (Word × List Yul.AstStmt)}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hSlot : StmtCaseListSlot hInterface stmt cases) :
    ∃ (casePre : List (Word × List Yul.AstStmt)) (value : Word)
        (caseBody : List Yul.AstStmt)
        (caseSuffix : List (Word × List Yul.AstStmt))
        (pre : List Yul.AstStmt) (focused : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      cases = casePre ++ (value, caseBody) :: caseSuffix ∧
        caseBody = pre ++ focused :: suffix ∧
          StmtContext hInterface focused ∧
            ∀ (fuel : Nat) (codeOverride : Option Yul.AstContract)
              (entryShared : EvmYul.SharedState .Yul)
              (entryVars : EvmYul.Yul.VarStore),
              Yul.InteractionSemantics.execSeq
                (fuel + pre.length + 1) caseBody codeOverride
                (.Ok entryShared entryVars) =
                Simulation.Interaction.bind
                  (Yul.InteractionSemantics.execSeq
                    (fuel + pre.length + 1) pre codeOverride
                    (.Ok entryShared entryVars))
                  (fun stateAfterPre =>
                    Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                      (fuel + 1) (focused :: suffix) codeOverride
                      stateAfterPre) := by
  rcases CaseListContext.exists_split_case (caseListContext hSlot) with
    ⟨casePre, value, caseBody, caseSuffix, hCases, hBody⟩
  rcases
      StmtListContext.exists_split_stmt_execSeq_prefix_all hBody with
    ⟨pre, focused, suffix, hBodySplit, hFocused, hPrefix⟩
  exact
    ⟨casePre, value, caseBody, caseSuffix, pre, focused, suffix,
      hCases, hBodySplit, hFocused, hPrefix⟩

end StmtCaseListSlot

namespace StmtContext

def ExprCallArgPrefixEval
    (ordered : Yul.OrderedProgram)
    (expr : Yul.AstExpr)
    (callee : EvmYul.Operation .Yul ⊕ Name)
    (before : List Yul.AstExpr) (arg : Yul.AstExpr)
    (after : List Yul.AstExpr) : Prop :=
  ∀ (fuel : Nat) (source : Yul.InteractionSemantics.State),
    Yul.InteractionSemantics.evalValues
        (fuel + 2 * before.length + 3)
        expr (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs
          (fuel + 2 * before.length + 2) before
          (some ordered.program.contract) source)
        (fun beforeResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.evalValues (fuel + 1)
              arg (some ordered.program.contract)
              beforeResult.1)
            (fun argResult =>
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.evalArgs fuel after
                  (some ordered.program.contract) argResult.1)
                (fun afterResult =>
                  let evaluatedArgs :=
                    beforeResult.2 ++ argResult.2.head! :: afterResult.2
                  match callee with
                  | .inl prim =>
                      Yul.InteractionSemantics.primitiveSemantics.eval
                        (fuel + 2 * before.length + 2)
                        afterResult.1 prim evaluatedArgs.reverse
                  | .inr functionName =>
                      Yul.InteractionSemantics.call
                        (fuel + 2 * before.length + 2)
                        evaluatedArgs.reverse (some functionName)
                        (some ordered.program.contract)
                        afterResult.1)))

def StmtListPrefixExec
    (stmtList pre : List Yul.AstStmt) (focused : Yul.AstStmt)
    (suffix : List Yul.AstStmt) : Prop :=
  ∀ (fuel : Nat) (codeOverride : Option Yul.AstContract)
    (entryShared : EvmYul.SharedState .Yul)
    (entryVars : EvmYul.Yul.VarStore),
    Yul.InteractionSemantics.execSeq
      (fuel + pre.length + 1) stmtList codeOverride
      (.Ok entryShared entryVars) =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.execSeq
          (fuel + pre.length + 1) pre codeOverride
          (.Ok entryShared entryVars))
        (fun stateAfterPre =>
          Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
            (fuel + 1) (focused :: suffix) codeOverride stateAfterPre)

inductive RecursiveSemanticStep
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    Yul.AstStmt → Prop where
  | exprDirect
      {stmt : Yul.AstStmt} {expr : Yul.AstExpr} :
      StmtExprSlot hInterface stmt expr →
        expr = .Call (.inr generated) args →
          RecursiveSemanticStep hInterface stmt
  | exprCallArgPrefix
      {stmt : Yul.AstStmt} {expr : Yul.AstExpr}
      {callee : EvmYul.Operation .Yul ⊕ Name}
      {outerArgs before : List Yul.AstExpr} {arg : Yul.AstExpr}
      {after : List Yul.AstExpr} :
      StmtExprSlot hInterface stmt expr →
        expr = .Call callee outerArgs →
          outerArgs.reverse = before ++ arg :: after →
            ExprContext hInterface arg →
              ExprCallArgPrefixEval ordered expr callee before arg after →
                RecursiveSemanticStep hInterface stmt
  | stmtListPrefix
      {stmt : Yul.AstStmt} {stmtList : List Yul.AstStmt}
      {pre : List Yul.AstStmt} {focused : Yul.AstStmt}
      {suffix : List Yul.AstStmt} :
      StmtListSlot hInterface stmt stmtList →
        stmtList = pre ++ focused :: suffix →
          StmtContext hInterface focused →
            StmtListPrefixExec stmtList pre focused suffix →
              RecursiveSemanticStep hInterface stmt
  | caseListPrefix
      {stmt : Yul.AstStmt} {cases : List (Word × List Yul.AstStmt)}
      {casePre : List (Word × List Yul.AstStmt)} {value : Word}
      {caseBody : List Yul.AstStmt}
      {caseSuffix : List (Word × List Yul.AstStmt)}
      {pre : List Yul.AstStmt} {focused : Yul.AstStmt}
      {suffix : List Yul.AstStmt} :
      StmtCaseListSlot hInterface stmt cases →
        cases = casePre ++ (value, caseBody) :: caseSuffix →
          caseBody = pre ++ focused :: suffix →
            StmtContext hInterface focused →
              StmtListPrefixExec caseBody pre focused suffix →
                RecursiveSemanticStep hInterface stmt

theorem recursiveSemanticStep
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmt : Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : StmtContext hInterface stmt) :
    RecursiveSemanticStep hInterface stmt := by
  rcases StmtContext.toSlot hContext with
    ⟨expr, hExprSlot⟩ | hRest
  · rcases StmtExprSlot.directOrCallArgPrefix hExprSlot with
      hDirect | hPrefix
    · exact RecursiveSemanticStep.exprDirect hExprSlot hDirect
    · rcases hPrefix with
        ⟨callee, outerArgs, before, arg, after, hExpr, hSplit,
          hArg, hEval⟩
      exact
        RecursiveSemanticStep.exprCallArgPrefix hExprSlot hExpr hSplit
          hArg hEval
  · rcases hRest with ⟨stmtList, hListSlot⟩ | ⟨cases, hCaseSlot⟩
    · rcases
        StmtListSlot.exists_split_stmt_execSeq_prefix_all hListSlot with
          ⟨pre, focused, suffix, hSplit, hFocused, hPrefix⟩
      exact
        RecursiveSemanticStep.stmtListPrefix hListSlot hSplit hFocused
          hPrefix
    · rcases
        StmtCaseListSlot.exists_split_case_stmt_execSeq_prefix_all
          hCaseSlot with
          ⟨casePre, value, caseBody, caseSuffix, pre, focused, suffix,
            hCases, hBody, hFocused, hPrefix⟩
      exact
        RecursiveSemanticStep.caseListPrefix hCaseSlot hCases hBody
          hFocused hPrefix

end StmtContext

namespace StmtListContext

theorem exists_split_stmt_recursiveSemanticStep
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {stmtList : List Yul.AstStmt}
    {hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars}
    (hContext : StmtListContext hInterface stmtList) :
    ∃ (pre : List Yul.AstStmt) (focused : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmtList = pre ++ focused :: suffix ∧
        StmtContext.RecursiveSemanticStep hInterface focused ∧
          ∀ (fuel : Nat) (codeOverride : Option Yul.AstContract)
            (entryShared : EvmYul.SharedState .Yul)
            (entryVars : EvmYul.Yul.VarStore),
            Yul.InteractionSemantics.execSeq
              (fuel + pre.length + 1) stmtList codeOverride
              (.Ok entryShared entryVars) =
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.execSeq
                  (fuel + pre.length + 1) pre codeOverride
                  (.Ok entryShared entryVars))
                (fun stateAfterPre =>
                  Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                    (fuel + 1) (focused :: suffix) codeOverride
                    stateAfterPre) := by
  rcases exists_split_stmt_execSeq_prefix_all hContext with
    ⟨pre, focused, suffix, hSplit, hFocused, hPrefix⟩
  exact
    ⟨pre, focused, suffix, hSplit,
      StmtContext.recursiveSemanticStep hFocused, hPrefix⟩

end StmtListContext

theorem stmtListContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    StmtListContext hInterface stmts := by
  rcases hInterface.prefixEvidence.splitPrefix with
    ⟨pre, stmt, suffix, hSplit, hStmt, _hPrefix⟩
  subst stmts
  exact
    StmtListContext.ofOccurrence
      (Yul.YulOccurrence.StmtListUserCall.of_split_stmt hStmt)

theorem splitStmtContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmts = pre ++ stmt :: suffix ∧
        StmtContext hInterface stmt := by
  rcases hInterface.prefixEvidence.splitPrefix with
    ⟨pre, stmt, suffix, hSplit, hStmt, _hPrefix⟩
  exact
    ⟨pre, stmt, suffix, hSplit, StmtContext.ofOccurrence hStmt⟩

theorem stmtListPrefixContext
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmts = pre ++ stmt :: suffix ∧
        StmtContext hInterface stmt ∧
          Yul.InteractionSemantics.execSeq
            (prefixFuel + pre.length + 1) stmts code (.Ok shared vars) =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.execSeq
                (prefixFuel + pre.length + 1) pre code (.Ok shared vars))
              (fun stateAfterPre =>
                Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                  (prefixFuel + 1) (stmt :: suffix) code stateAfterPre) := by
  rcases hInterface.prefixEvidence.splitPrefix with
    ⟨pre, stmt, suffix, hSplit, hStmt, hPrefix⟩
  exact
    ⟨pre, stmt, suffix, hSplit, StmtContext.ofOccurrence hStmt,
      hPrefix⟩

theorem stmtListRecursiveSemanticStep
    {ordered : Yul.OrderedProgram}
    {generated : Name}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hInterface :
      FocusedGeneratedCallSemanticInterface ordered generated params returns
        body args stmts prefixFuel code shared vars) :
    ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
      stmts = pre ++ stmt :: suffix ∧
        StmtContext.RecursiveSemanticStep hInterface stmt ∧
          Yul.InteractionSemantics.execSeq
            (prefixFuel + pre.length + 1) stmts code (.Ok shared vars) =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.execSeq
                (prefixFuel + pre.length + 1) pre code (.Ok shared vars))
              (fun stateAfterPre =>
                Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                  (prefixFuel + 1) (stmt :: suffix) code stateAfterPre) := by
  rcases
      StmtListContext.exists_split_stmt_recursiveSemanticStep
        (stmtListContext hInterface) with
    ⟨pre, stmt, suffix, hSplit, hStep, hPrefix⟩
  exact
    ⟨pre, stmt, suffix, hSplit, hStep,
      hPrefix prefixFuel code shared vars⟩

end FocusedGeneratedCallSemanticInterface

def FocusedGeneratedStmtListCallPrefix
    (state : State) (ordered : Yul.OrderedProgram)
    (generated : Name) (fn : Frontend.FunctionDef)
    (params returns : List Name) (body : List Yul.AstStmt)
    (args : List Yul.AstExpr) (stmts : List Yul.AstStmt)
    (fuel : Nat) (code : Option Yul.AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) : Prop :=
    FocusedGeneratedCallOccurrence state ordered generated fn
      params returns body args ∧
      ∃ (pre : List Yul.AstStmt) (stmt : Yul.AstStmt)
        (suffix : List Yul.AstStmt),
        stmts = pre ++ stmt :: suffix ∧
          Yul.YulOccurrence.StmtUserCall generated args stmt ∧
            Yul.InteractionSemantics.execSeq
              (fuel + pre.length + 1) stmts code (.Ok shared vars) =
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.execSeq
                  (fuel + pre.length + 1) pre code (.Ok shared vars))
                (fun stateAfterPre =>
                  Yul.YulOccurrence.StmtListUserCall.continueAfterPrefix
                    (fuel + 1) (stmt :: suffix) code stateAfterPre)

namespace FocusedGeneratedStmtListCallPrefix

theorem of_yulOccurrence
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {args : List Yul.AstExpr} {stmts : List Yul.AstStmt}
    {fuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hFocused :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body args)
    (hOccurrence :
      Yul.YulOccurrence.StmtListUserCall generated args stmts) :
    FocusedGeneratedStmtListCallPrefix state ordered generated fn
      params returns body args stmts fuel code shared vars := by
  rcases
      Yul.YulOccurrence.StmtListUserCall.exists_split_stmt_execSeq_prefix
        hOccurrence fuel code shared vars with
    ⟨pre, stmt, suffix, hSplit, hStmt, hPrefix⟩
  exact
    ⟨hFocused, pre, stmt, suffix, hSplit, hStmt, hPrefix⟩

theorem dispatcher_of_frontend
    {state : State} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {frontendArgs : List Frontend.Expr} {yulArgs : List Yul.AstExpr}
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hFocused :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body yulArgs)
    (hOccurrence :
      FrontendOccurrence.StmtListUserCall generated frontendArgs
        object.dispatcher)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered)
    (hArgs : Frontend.Expr.List.toYul? frontendArgs = some yulArgs) :
    FocusedGeneratedStmtListCallPrefix state ordered generated fn
      params returns body yulArgs
      [ordered.program.contract.dispatcher] fuel
      (some ordered.program.contract) shared vars := by
  exact
    of_yulOccurrence hFocused
      (FrontendOccurrence.Object.dispatcherOccurrence_toOrdered?
        hOccurrence hConvert hArgs)

theorem dispatcher_of_frontend_existsArgs
    {state : State} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    {frontendArgs : List Frontend.Expr}
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hFocused :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body argExprs)
    (hOccurrence :
      FrontendOccurrence.StmtListUserCall generated frontendArgs
        object.dispatcher)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ yulArgs,
      FocusedGeneratedStmtListCallPrefix state ordered generated fn
        params returns body yulArgs
        [ordered.program.contract.dispatcher] fuel
        (some ordered.program.contract) shared vars := by
  rcases
      FrontendOccurrence.Object.dispatcherOccurrence_args_toYul?
        hOccurrence hConvert with
    ⟨yulArgs, hArgs⟩
  have hFocusedArgs :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body yulArgs := by
    exact ⟨hFocused.hoisted, hFocused.toYul?, hFocused.lookup⟩
  exact
    ⟨yulArgs,
      dispatcher_of_frontend hFocusedArgs hOccurrence hConvert hArgs⟩

theorem functionBody_of_frontend
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {calleeFn contextFn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {contextParams contextReturns : List Name}
    {contextBody : List Yul.AstStmt}
    {frontendArgs : List Frontend.Expr} {yulArgs : List Yul.AstExpr}
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hFocused :
      FocusedGeneratedCallOccurrence state ordered generated calleeFn
        params returns body yulArgs)
    (hOccurrence :
      FrontendOccurrence.StmtListUserCall generated frontendArgs
        contextFn.body)
    (hContext :
      contextFn.toYul? =
        some (.Def contextParams contextReturns contextBody))
    (hArgs : Frontend.Expr.List.toYul? frontendArgs = some yulArgs) :
    FocusedGeneratedStmtListCallPrefix state ordered generated calleeFn
      params returns body yulArgs contextBody fuel
      (some ordered.program.contract) shared vars := by
  exact
    of_yulOccurrence hFocused
      (FrontendOccurrence.FunctionDef.bodyOccurrence_toYul?
        hOccurrence hContext hArgs)

theorem functionBody_of_frontend_existsArgs
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {calleeFn contextFn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {contextParams contextReturns : List Name}
    {contextBody : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    {frontendArgs : List Frontend.Expr}
    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hFocused :
      FocusedGeneratedCallOccurrence state ordered generated calleeFn
        params returns body argExprs)
    (hOccurrence :
      FrontendOccurrence.StmtListUserCall generated frontendArgs
        contextFn.body)
    (hContext :
      contextFn.toYul? =
        some (.Def contextParams contextReturns contextBody)) :
    ∃ yulArgs,
      FocusedGeneratedStmtListCallPrefix state ordered generated calleeFn
        params returns body yulArgs contextBody fuel
        (some ordered.program.contract) shared vars := by
  rcases
      FrontendOccurrence.FunctionDef.bodyOccurrence_args_toYul?
        hOccurrence hContext with
    ⟨yulArgs, hArgs⟩
  have hFocusedArgs :
      FocusedGeneratedCallOccurrence state ordered generated calleeFn
        params returns body yulArgs := by
    exact ⟨hFocused.hoisted, hFocused.toYul?, hFocused.lookup⟩
  exact
    ⟨yulArgs,
      functionBody_of_frontend hFocusedArgs hOccurrence hContext hArgs⟩

end FocusedGeneratedStmtListCallPrefix

theorem FocusedGeneratedCallOccurrence.call_succ
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    (hOccurrence :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body argExprs)
    (fuel : Nat) (args : List Word)
    (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.call (fuel + 1) args
        (some generated) (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.exec fuel
          (.Block body) (some ordered.program.contract)
          (EvmYul.Yul.State.mkOk
            (source.initcall params returns args)))
        (fun stateAfterBody =>
          pure
            ((stateAfterBody.reviveJump.overwrite? source).setStore
              source,
              List.map stateAfterBody.lookup! returns)) := by
  exact
    Yul.InteractionSemantics.Call.explicit_succ
      fuel args generated ordered.program.contract params returns body
      source hOccurrence.lookup

theorem FocusedGeneratedCallOccurrence.evalValues_succ
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    (hOccurrence :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body argExprs)
    (fuel : Nat) (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.evalValues (fuel + 2)
        (.Call (.inr generated) argExprs)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (fuel + 1)
          argExprs.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec fuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              pure
                ((stateAfterBody.reviveJump.overwrite?
                    argsResult.1).setStore argsResult.1,
                  List.map stateAfterBody.lookup! returns))) := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.EvalValues.internal_succ
    (fuel + 1) generated argExprs (some ordered.program.contract) source]
  apply congrArg
  funext argsResult
  exact FocusedGeneratedCallOccurrence.call_succ
    hOccurrence fuel argsResult.2.reverse argsResult.1

theorem FocusedGeneratedCallOccurrence.eval_succ
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    (hOccurrence :
      FocusedGeneratedCallOccurrence state ordered generated fn
        params returns body argExprs)
    (fuel : Nat) (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.eval (fuel + 2)
        (.Call (.inr generated) argExprs)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs (fuel + 1)
            argExprs.reverse (some ordered.program.contract) source)
          (fun argsResult =>
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.exec fuel
                (.Block body) (some ordered.program.contract)
                (EvmYul.Yul.State.mkOk
                  (argsResult.1.initcall params returns
                    argsResult.2.reverse)))
              (fun stateAfterBody =>
                pure
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1,
                    List.map stateAfterBody.lookup! returns))))
        (fun result => pure (result.1, result.2.head!)) := by
  rw [Yul.InteractionSemantics.eval_eq_bind]
  rw [FocusedGeneratedCallOccurrence.evalValues_succ hOccurrence fuel source]

namespace FocusedGeneratedStmtListCallPrefix

theorem call_succ
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body stmts : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    {stmtFuel prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hPrefix :
      FocusedGeneratedStmtListCallPrefix state ordered generated fn
        params returns body argExprs stmts prefixFuel code shared vars)
    (args : List Word) (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.call (stmtFuel + 1) args
        (some generated) (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.exec stmtFuel
          (.Block body) (some ordered.program.contract)
          (EvmYul.Yul.State.mkOk
            (source.initcall params returns args)))
        (fun stateAfterBody =>
          pure
            ((stateAfterBody.reviveJump.overwrite? source).setStore
              source,
              List.map stateAfterBody.lookup! returns)) := by
  rcases hPrefix with ⟨hFocused, _hSplit⟩
  exact FocusedGeneratedCallOccurrence.call_succ
    hFocused stmtFuel args source

theorem evalValues_succ
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body stmts : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    {stmtFuel prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hPrefix :
      FocusedGeneratedStmtListCallPrefix state ordered generated fn
        params returns body argExprs stmts prefixFuel code shared vars)
    (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.evalValues (stmtFuel + 2)
        (.Call (.inr generated) argExprs)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (stmtFuel + 1)
          argExprs.reverse (some ordered.program.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.exec stmtFuel
              (.Block body) (some ordered.program.contract)
              (EvmYul.Yul.State.mkOk
                (argsResult.1.initcall params returns
                  argsResult.2.reverse)))
            (fun stateAfterBody =>
              pure
                ((stateAfterBody.reviveJump.overwrite?
                    argsResult.1).setStore argsResult.1,
                  List.map stateAfterBody.lookup! returns))) := by
  rcases hPrefix with ⟨hFocused, _hSplit⟩
  exact FocusedGeneratedCallOccurrence.evalValues_succ
    hFocused stmtFuel source

theorem eval_succ
    {state : State} {ordered : Yul.OrderedProgram}
    {generated : Name} {fn : Frontend.FunctionDef}
    {params returns : List Name} {body stmts : List Yul.AstStmt}
    {argExprs : List Yul.AstExpr}
    {stmtFuel prefixFuel : Nat} {code : Option Yul.AstContract}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hPrefix :
      FocusedGeneratedStmtListCallPrefix state ordered generated fn
        params returns body argExprs stmts prefixFuel code shared vars)
    (source : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.eval (stmtFuel + 2)
        (.Call (.inr generated) argExprs)
        (some ordered.program.contract) source =
      Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs (stmtFuel + 1)
            argExprs.reverse (some ordered.program.contract) source)
          (fun argsResult =>
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.exec stmtFuel
                (.Block body) (some ordered.program.contract)
                (EvmYul.Yul.State.mkOk
                  (argsResult.1.initcall params returns
                    argsResult.2.reverse)))
              (fun stateAfterBody =>
                pure
                  ((stateAfterBody.reviveJump.overwrite?
                      argsResult.1).setStore argsResult.1,
                    List.map stateAfterBody.lookup! returns))))
        (fun result => pure (result.1, result.2.head!)) := by
  rcases hPrefix with ⟨hFocused, _hSplit⟩
  exact FocusedGeneratedCallOccurrence.eval_succ
    hFocused stmtFuel source

end FocusedGeneratedStmtListCallPrefix

theorem codeGeneratedNormalizationEvidence_hoistedCallSemantics
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          HoistedCallSemantics state ordered := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, hHoistedRetained⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated fn yulFn hHoisted hFn fuel args source
  have hMem : (generated, fn) ∈ object.functions :=
    hHoistedRetained (generated, fn) hHoisted
  have hLookup :
      ordered.program.contract.functions.lookup generated = some yulFn :=
    Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
      hConvert hMem hFn
  cases yulFn with
  | Def params rets body =>
      exact
        Yul.InteractionSemantics.Call.explicit_succ
          fuel args generated ordered.program.contract params rets body
          source hLookup

theorem generatedNormalizationEvidence_hoistedCallSemantics
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              HoistedCallSemantics state ordered := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_hoistedCallSemantics
          hCodeEvidence hConvert

theorem decodeAndElaborateSolcIr?_hoistedCallSemantics
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        HoistedCallSemantics state ordered := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_hoistedCallSemantics
        hEvidence hObjectConvert⟩

theorem codeGeneratedNormalizationEvidence_focusedGeneratedCallOccurrence
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated : Name} {fn : Frontend.FunctionDef}
              {params returns : List Name} {body : List Yul.AstStmt}
              {argExprs : List Yul.AstExpr},
            (generated, fn) ∈ state.hoistedFunctions →
              fn.toYul? = some (.Def params returns body) →
                FocusedGeneratedCallOccurrence state ordered generated fn
                  params returns body argExprs := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, hHoistedRetained⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated fn params returns body argExprs hHoisted hFn
  have hMem : (generated, fn) ∈ object.functions :=
    hHoistedRetained (generated, fn) hHoisted
  have hLookup :
      ordered.program.contract.functions.lookup generated =
        some (.Def params returns body) :=
    Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
      hConvert hMem hFn
  exact ⟨hHoisted, hFn, hLookup⟩

theorem codeGeneratedNormalizationEvidence_dispatcherPrefix
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated : Name} {fn : Frontend.FunctionDef}
              {params returns : List Name} {body : List Yul.AstStmt}
              {frontendArgs : List Frontend.Expr}
              {yulArgs : List Yul.AstExpr}
              {fuel : Nat} {shared : EvmYul.SharedState .Yul}
              {vars : EvmYul.Yul.VarStore},
            (generated, fn) ∈ state.hoistedFunctions →
              fn.toYul? = some (.Def params returns body) →
                FrontendOccurrence.StmtListUserCall generated frontendArgs
                  object.dispatcher →
                  Frontend.Expr.List.toYul? frontendArgs = some yulArgs →
                    FocusedGeneratedStmtListCallPrefix state ordered
                      generated fn params returns body yulArgs
                      [ordered.program.contract.dispatcher] fuel
                      (some ordered.program.contract) shared vars := by
  rcases
      codeGeneratedNormalizationEvidence_focusedGeneratedCallOccurrence
        hEvidence hConvert with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      hFocused⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated fn params returns body frontendArgs yulArgs fuel shared
    vars hHoisted hFn hOccurrence hArgs
  exact
    FocusedGeneratedStmtListCallPrefix.dispatcher_of_frontend
      (hFocused hHoisted hFn) hOccurrence hConvert hArgs

theorem codeGeneratedNormalizationEvidence_dispatcherPrefixOfFrontendOccurrence
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated : Name} {fn : Frontend.FunctionDef}
              {params returns : List Name} {body : List Yul.AstStmt}
              {frontendArgs : List Frontend.Expr}
              {fuel : Nat} {shared : EvmYul.SharedState .Yul}
              {vars : EvmYul.Yul.VarStore},
            (generated, fn) ∈ state.hoistedFunctions →
              fn.toYul? = some (.Def params returns body) →
                FrontendOccurrence.StmtListUserCall generated frontendArgs
                  object.dispatcher →
                  ∃ yulArgs,
                    FocusedGeneratedStmtListCallPrefix state ordered
                      generated fn params returns body yulArgs
                      [ordered.program.contract.dispatcher] fuel
                      (some ordered.program.contract) shared vars := by
  rcases
      codeGeneratedNormalizationEvidence_focusedGeneratedCallOccurrence
        hEvidence hConvert with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      hFocused⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated fn params returns body frontendArgs fuel shared vars
    hHoisted hFn hOccurrence
  exact
    FocusedGeneratedStmtListCallPrefix.dispatcher_of_frontend_existsArgs
      (hFocused (argExprs := []) hHoisted hFn) hOccurrence hConvert

theorem codeGeneratedNormalizationEvidence_functionBodyPrefix
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated contextGenerated : Name}
              {calleeFn contextFn : Frontend.FunctionDef}
              {params returns : List Name} {body : List Yul.AstStmt}
              {contextParams contextReturns : List Name}
              {contextBody : List Yul.AstStmt}
              {frontendArgs : List Frontend.Expr}
              {yulArgs : List Yul.AstExpr}
              {fuel : Nat} {shared : EvmYul.SharedState .Yul}
              {vars : EvmYul.Yul.VarStore},
            (generated, calleeFn) ∈ state.hoistedFunctions →
              calleeFn.toYul? = some (.Def params returns body) →
                (contextGenerated, contextFn) ∈ state.hoistedFunctions →
                  contextFn.toYul? =
                    some (.Def contextParams contextReturns contextBody) →
                    FrontendOccurrence.StmtListUserCall generated frontendArgs
                      contextFn.body →
                      Frontend.Expr.List.toYul? frontendArgs = some yulArgs →
                        ordered.program.contract.functions.lookup
                            contextGenerated =
                          some (.Def contextParams contextReturns
                            contextBody) ∧
                        FocusedGeneratedStmtListCallPrefix state ordered
                          generated calleeFn params returns body yulArgs
                          contextBody fuel (some ordered.program.contract)
                          shared vars := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, hHoistedRetained⟩
  have hFocusedEvidence :
      ∀ {generated : Name} {fn : Frontend.FunctionDef}
          {params returns : List Name} {body : List Yul.AstStmt}
          {argExprs : List Yul.AstExpr},
        (generated, fn) ∈ state.hoistedFunctions →
          fn.toYul? = some (.Def params returns body) →
            FocusedGeneratedCallOccurrence state ordered generated fn
              params returns body argExprs := by
    intro generated fn params returns body argExprs hHoisted hFn
    have hMem : (generated, fn) ∈ object.functions :=
      hHoistedRetained (generated, fn) hHoisted
    have hLookup :
        ordered.program.contract.functions.lookup generated =
          some (.Def params returns body) :=
      Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
        hConvert hMem hFn
    exact ⟨hHoisted, hFn, hLookup⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated contextGenerated calleeFn contextFn params returns body
    contextParams contextReturns contextBody frontendArgs yulArgs fuel shared
    vars hCalleeHoisted hCalleeFn hContextHoisted hContextFn hOccurrence
    hArgs
  have hContextMem : (contextGenerated, contextFn) ∈ object.functions :=
    hHoistedRetained (contextGenerated, contextFn) hContextHoisted
  have hContextLookup :
      ordered.program.contract.functions.lookup contextGenerated =
        some (.Def contextParams contextReturns contextBody) :=
    Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
      hConvert hContextMem hContextFn
  exact
    ⟨hContextLookup,
      FocusedGeneratedStmtListCallPrefix.functionBody_of_frontend
        (hFocusedEvidence hCalleeHoisted hCalleeFn)
        hOccurrence hContextFn hArgs⟩

theorem codeGeneratedNormalizationEvidence_functionBodyPrefixOfFrontendOccurrence
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated contextGenerated : Name}
              {calleeFn contextFn : Frontend.FunctionDef}
              {params returns : List Name} {body : List Yul.AstStmt}
              {contextParams contextReturns : List Name}
              {contextBody : List Yul.AstStmt}
              {frontendArgs : List Frontend.Expr}
              {fuel : Nat} {shared : EvmYul.SharedState .Yul}
              {vars : EvmYul.Yul.VarStore},
            (generated, calleeFn) ∈ state.hoistedFunctions →
              calleeFn.toYul? = some (.Def params returns body) →
                (contextGenerated, contextFn) ∈ state.hoistedFunctions →
                  contextFn.toYul? =
                    some (.Def contextParams contextReturns contextBody) →
                    FrontendOccurrence.StmtListUserCall generated frontendArgs
                      contextFn.body →
                      ordered.program.contract.functions.lookup
                          contextGenerated =
                        some (.Def contextParams contextReturns
                          contextBody) ∧
                      ∃ yulArgs,
                        FocusedGeneratedStmtListCallPrefix state ordered
                          generated calleeFn params returns body yulArgs
                          contextBody fuel (some ordered.program.contract)
                          shared vars := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, hHoistedRetained⟩
  have hFocusedEvidence :
      ∀ {generated : Name} {fn : Frontend.FunctionDef}
          {params returns : List Name} {body : List Yul.AstStmt}
          {argExprs : List Yul.AstExpr},
        (generated, fn) ∈ state.hoistedFunctions →
          fn.toYul? = some (.Def params returns body) →
            FocusedGeneratedCallOccurrence state ordered generated fn
              params returns body argExprs := by
    intro generated fn params returns body argExprs hHoisted hFn
    have hMem : (generated, fn) ∈ object.functions :=
      hHoistedRetained (generated, fn) hHoisted
    have hLookup :
        ordered.program.contract.functions.lookup generated =
          some (.Def params returns body) :=
      Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
        hConvert hMem hFn
    exact ⟨hHoisted, hFn, hLookup⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated contextGenerated calleeFn contextFn params returns body
    contextParams contextReturns contextBody frontendArgs fuel shared vars
    hCalleeHoisted hCalleeFn hContextHoisted hContextFn hOccurrence
  have hContextMem : (contextGenerated, contextFn) ∈ object.functions :=
    hHoistedRetained (contextGenerated, contextFn) hContextHoisted
  have hContextLookup :
      ordered.program.contract.functions.lookup contextGenerated =
        some (.Def contextParams contextReturns contextBody) :=
    Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
      hConvert hContextMem hContextFn
  exact
    ⟨hContextLookup,
      FocusedGeneratedStmtListCallPrefix.functionBody_of_frontend_existsArgs
        (hFocusedEvidence (argExprs := []) hCalleeHoisted hCalleeFn)
        hOccurrence hContextFn⟩

theorem codeGeneratedNormalizationEvidence_prefixOfCodeRoute
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated : Name} {calleeFn : Frontend.FunctionDef}
              {params returns : List Name} {body : List Yul.AstStmt}
              {frontendArgs : List Frontend.Expr}
              {fuel : Nat} {shared : EvmYul.SharedState .Yul}
              {vars : EvmYul.Yul.VarStore},
            (generated, calleeFn) ∈ state.hoistedFunctions →
              calleeFn.toYul? = some (.Def params returns body) →
                RawOccurrence.CodeElaborationRoute state generated
                  frontendArgs object.dispatcher →
                  ∃ (yulArgs : List Yul.AstExpr)
                    (stmts : List Yul.AstStmt),
                    FocusedGeneratedStmtListCallPrefix state ordered
                      generated calleeFn params returns body yulArgs stmts
                      fuel (some ordered.program.contract) shared vars := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, hHoistedRetained⟩
  have hFocusedEvidence :
      ∀ {generated : Name} {fn : Frontend.FunctionDef}
          {params returns : List Name} {body : List Yul.AstStmt}
          {argExprs : List Yul.AstExpr},
        (generated, fn) ∈ state.hoistedFunctions →
          fn.toYul? = some (.Def params returns body) →
            FocusedGeneratedCallOccurrence state ordered generated fn
              params returns body argExprs := by
    intro generated fn params returns body argExprs hHoisted hFn
    have hMem : (generated, fn) ∈ object.functions :=
      hHoistedRetained (generated, fn) hHoisted
    have hLookup :
        ordered.program.contract.functions.lookup generated =
          some (.Def params returns body) :=
      Frontend.Object.toSolcYulOrderedProgram?_functionLookup_of_mem
        hConvert hMem hFn
    exact ⟨hHoisted, hFn, hLookup⟩
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated calleeFn params returns body frontendArgs fuel shared vars
    hCalleeHoisted hCalleeFn hRoute
  cases hRoute with
  | dispatcher hOccurrence =>
      rcases
          FocusedGeneratedStmtListCallPrefix.dispatcher_of_frontend_existsArgs
            (hFocusedEvidence (argExprs := []) hCalleeHoisted hCalleeFn)
            hOccurrence hConvert with
        ⟨yulArgs, hPrefix⟩
      exact ⟨yulArgs, [ordered.program.contract.dispatcher], hPrefix⟩
  | functionBody contextName contextFn hContextHoisted hOccurrence =>
      have hContextMem : (contextName, contextFn) ∈ object.functions :=
        hHoistedRetained (contextName, contextFn) hContextHoisted
      rcases
          Frontend.Object.toSolcYulOrderedProgram?_functionToYul_of_mem
            hConvert hContextMem with
        ⟨contextYulFn, hContextFn, _hContextLookup⟩
      cases contextYulFn with
      | Def contextParams contextReturns contextBody =>
          rcases
              FocusedGeneratedStmtListCallPrefix.functionBody_of_frontend_existsArgs
                (hFocusedEvidence (argExprs := []) hCalleeHoisted
                  hCalleeFn)
                hOccurrence hContextFn with
            ⟨yulArgs, hPrefix⟩
          exact ⟨yulArgs, contextBody, hPrefix⟩

theorem codeGeneratedNormalizationEvidence_prefixEvidenceOfCodeRoute
    {code : List Raw.Stmt} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {generated : Name} {frontendArgs : List Frontend.Expr}
              {fuel : Nat} {shared : EvmYul.SharedState .Yul}
              {vars : EvmYul.Yul.VarStore},
            RawOccurrence.CodeElaborationRoute state generated
              frontendArgs object.dispatcher →
              ∃ (params returns : List Name) (body : List Yul.AstStmt)
                (yulArgs : List Yul.AstExpr) (stmts : List Yul.AstStmt),
                FocusedGeneratedCallPrefixEvidence ordered generated
                  params returns body yulArgs stmts fuel
                  (some ordered.program.contract) shared vars := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, hHoistedRetained⟩
  have hContractOk :
      Yul.SolcValidation.ContractOkWithEntries? object.dialectProfile
          ordered.program.contract ordered.functionEntries =
        true := by
    simpa [Yul.SolcValidation.ProgramOkWithEntries?] using
      Frontend.Object.toSolcYulOrderedProgram?_programOkWithEntries
        hConvert
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro generated frontendArgs fuel shared vars hRoute
  cases hRoute with
  | dispatcher hOccurrence =>
      rcases
          FrontendOccurrence.Object.dispatcherOccurrence_args_toYul?
            hOccurrence hConvert with
        ⟨yulArgs, hArgs⟩
      have hYulOccurrence :
          Yul.YulOccurrence.StmtListUserCall generated yulArgs
            [ordered.program.contract.dispatcher] :=
        FrontendOccurrence.Object.dispatcherOccurrence_toOrdered?
          hOccurrence hConvert hArgs
      have hDispatcherOk :
          Yul.SolcValidation.StmtOk? object.dialectProfile
              ordered.program.contract
              (ordered.functionEntries.map Prod.fst) [] false false false
              ordered.program.contract.dispatcher =
            true :=
        Yul.SolcValidation.contractOkWithEntries_dispatcherOk hContractOk
      have hStmtsOk :
          Yul.SolcValidation.StmtsOk? object.dialectProfile
              ordered.program.contract
              (ordered.functionEntries.map Prod.fst) [] false false false
              [ordered.program.contract.dispatcher] =
            true := by
        simp [Yul.SolcValidation.StmtsOk?, hDispatcherOk]
      rcases yulStmtListUserCall_lookup_of_stmtsOk hYulOccurrence
          hStmtsOk with
        ⟨params, returns, body, hLookup⟩
      exact
        ⟨params, returns, body, yulArgs,
          [ordered.program.contract.dispatcher],
          FocusedGeneratedCallPrefixEvidence.of_yulOccurrence
            hLookup hYulOccurrence⟩
  | functionBody contextName contextFn hContextHoisted hOccurrence =>
      have hContextMem : (contextName, contextFn) ∈ object.functions :=
        hHoistedRetained (contextName, contextFn) hContextHoisted
      rcases
          Frontend.Object.toSolcYulOrderedProgram?_functionEntry_of_mem
            hConvert hContextMem with
        ⟨contextYulFn, hContextFn, hContextEntry, _hContextLookup⟩
      cases contextYulFn with
      | Def contextParams contextReturns contextBody =>
          rcases
              FrontendOccurrence.FunctionDef.bodyOccurrence_args_toYul?
                hOccurrence hContextFn with
            ⟨yulArgs, hArgs⟩
          have hYulOccurrence :
              Yul.YulOccurrence.StmtListUserCall generated yulArgs
                contextBody :=
            FrontendOccurrence.FunctionDef.bodyOccurrence_toYul?
              hOccurrence hContextFn hArgs
          have hBodyOk :
              Yul.SolcValidation.StmtsOk? object.dialectProfile
                  ordered.program.contract
                  (ordered.functionEntries.map Prod.fst)
                  (Yul.identNames contextReturns ++
                    Yul.identNames contextParams)
                  false false true contextBody =
                true :=
            Yul.SolcValidation.contractOkWithEntries_function_bodyOk_of_mem
              hContractOk hContextEntry
          rcases yulStmtListUserCall_lookup_of_stmtsOk hYulOccurrence
              hBodyOk with
            ⟨params, returns, body, hLookup⟩
          exact
            ⟨params, returns, body, yulArgs, contextBody,
              FocusedGeneratedCallPrefixEvidence.of_yulOccurrence
                hLookup hYulOccurrence⟩

theorem codeGeneratedNormalizationEvidence_codeRouteOfRawOccurrence
    {code : List Raw.Stmt} {object : Frontend.Object}
    (hEvidence :
      Raw.Object.CodeGeneratedNormalizationEvidence code object) :
    ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
        (helper? arg? ret? : Option Name),
      elaborateCodeCore code = .ok (coreDispatcher, state) ∧
        elaborateCode code =
          .ok (object.dispatcher, object.functions,
            helper?, arg?, ret?) ∧
          ∀ {functionName : Name} {rawArgs : List Raw.Expr},
            RawOccurrence.StmtListUserCall functionName rawArgs code →
              functionName ≠ "memoryguard" →
                functionName ≠ "clz" →
                  CallClass.classifyCall functionName = .user →
                    ∃ (generated : Name)
                      (frontendArgs : List Frontend.Expr),
                      RawOccurrence.CodeElaborationRoute state generated
                        frontendArgs object.dispatcher := by
  rcases hEvidence with
    ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
      _hFunctions, _hHelper, _hArg, _hRet, _hDistinct, _hClz,
      _hInterface, _hHoistedRetained⟩
  have hDispatcherEq : object.dispatcher = coreDispatcher := by
    rcases elaborateCode_parts hElab with
      ⟨stateFromElab, hCoreFromElab, _hFunctions, _hHelper,
        _hArg, _hRet⟩
    rw [hCore] at hCoreFromElab
    simp at hCoreFromElab
    exact hCoreFromElab.1.symm
  refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
  intro functionName rawArgs hOccurrence hNotMemoryguard hNotClz hKind
  rcases RawOccurrence.Elab.elaborateCodeCore_codeRoute hCore
      hOccurrence hNotMemoryguard hNotClz hKind with
    ⟨generated, frontendArgs, hRoute⟩
  exact ⟨generated, frontendArgs, by simpa [hDispatcherEq] using hRoute⟩

theorem generatedNormalizationEvidence_codeRouteOfRawOccurrence
    {raw : Raw.Object} {object : Frontend.Object}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {functionName : Name} {rawArgs : List Raw.Expr},
                RawOccurrence.StmtListUserCall functionName rawArgs code →
                  functionName ≠ "memoryguard" →
                    functionName ≠ "clz" →
                      CallClass.classifyCall functionName = .user →
                        ∃ (generated : Name)
                          (frontendArgs : List Frontend.Expr),
                          RawOccurrence.CodeElaborationRoute state generated
                            frontendArgs object.dispatcher := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_codeRouteOfRawOccurrence
          hCodeEvidence

theorem generatedNormalizationEvidence_focusedGeneratedCallOccurrence
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {generated : Name} {fn : Frontend.FunctionDef}
                  {params returns : List Name} {body : List Yul.AstStmt}
                  {argExprs : List Yul.AstExpr},
                (generated, fn) ∈ state.hoistedFunctions →
                  fn.toYul? = some (.Def params returns body) →
                    FocusedGeneratedCallOccurrence state ordered generated fn
                      params returns body argExprs := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_focusedGeneratedCallOccurrence
          hCodeEvidence hConvert

theorem generatedNormalizationEvidence_dispatcherPrefix
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {generated : Name} {fn : Frontend.FunctionDef}
                  {params returns : List Name} {body : List Yul.AstStmt}
                  {frontendArgs : List Frontend.Expr}
                  {yulArgs : List Yul.AstExpr}
                  {fuel : Nat} {shared : EvmYul.SharedState .Yul}
                  {vars : EvmYul.Yul.VarStore},
                (generated, fn) ∈ state.hoistedFunctions →
                  fn.toYul? = some (.Def params returns body) →
                    FrontendOccurrence.StmtListUserCall generated frontendArgs
                      object.dispatcher →
                    Frontend.Expr.List.toYul? frontendArgs = some yulArgs →
                      FocusedGeneratedStmtListCallPrefix state ordered
                        generated fn params returns body yulArgs
                        [ordered.program.contract.dispatcher] fuel
                        (some ordered.program.contract) shared vars := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_dispatcherPrefix
          hCodeEvidence hConvert

theorem generatedNormalizationEvidence_dispatcherPrefixOfFrontendOccurrence
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {generated : Name} {fn : Frontend.FunctionDef}
                  {params returns : List Name} {body : List Yul.AstStmt}
                  {frontendArgs : List Frontend.Expr}
                  {fuel : Nat} {shared : EvmYul.SharedState .Yul}
                  {vars : EvmYul.Yul.VarStore},
                (generated, fn) ∈ state.hoistedFunctions →
                  fn.toYul? = some (.Def params returns body) →
                    FrontendOccurrence.StmtListUserCall generated
                      frontendArgs object.dispatcher →
                    ∃ yulArgs,
                      FocusedGeneratedStmtListCallPrefix state ordered
                        generated fn params returns body yulArgs
                        [ordered.program.contract.dispatcher] fuel
                        (some ordered.program.contract) shared vars := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_dispatcherPrefixOfFrontendOccurrence
          hCodeEvidence hConvert

theorem generatedNormalizationEvidence_functionBodyPrefix
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {generated contextGenerated : Name}
                  {calleeFn contextFn : Frontend.FunctionDef}
                  {params returns : List Name} {body : List Yul.AstStmt}
                  {contextParams contextReturns : List Name}
                  {contextBody : List Yul.AstStmt}
                  {frontendArgs : List Frontend.Expr}
                  {yulArgs : List Yul.AstExpr}
                  {fuel : Nat} {shared : EvmYul.SharedState .Yul}
                  {vars : EvmYul.Yul.VarStore},
                (generated, calleeFn) ∈ state.hoistedFunctions →
                  calleeFn.toYul? = some (.Def params returns body) →
                    (contextGenerated, contextFn) ∈ state.hoistedFunctions →
                    contextFn.toYul? =
                      some (.Def contextParams contextReturns contextBody) →
                    FrontendOccurrence.StmtListUserCall generated frontendArgs
                      contextFn.body →
                    Frontend.Expr.List.toYul? frontendArgs = some yulArgs →
                      ordered.program.contract.functions.lookup
                          contextGenerated =
                        some (.Def contextParams contextReturns contextBody) ∧
                      FocusedGeneratedStmtListCallPrefix state ordered
                        generated calleeFn params returns body yulArgs
                        contextBody fuel (some ordered.program.contract)
                        shared vars := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_functionBodyPrefix
          hCodeEvidence hConvert

theorem generatedNormalizationEvidence_functionBodyPrefixOfFrontendOccurrence
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {generated contextGenerated : Name}
                  {calleeFn contextFn : Frontend.FunctionDef}
                  {params returns : List Name} {body : List Yul.AstStmt}
                  {contextParams contextReturns : List Name}
                  {contextBody : List Yul.AstStmt}
                  {frontendArgs : List Frontend.Expr}
                  {fuel : Nat} {shared : EvmYul.SharedState .Yul}
                  {vars : EvmYul.Yul.VarStore},
                (generated, calleeFn) ∈ state.hoistedFunctions →
                  calleeFn.toYul? =
                    some (.Def params returns body) →
                    (contextGenerated, contextFn) ∈
                      state.hoistedFunctions →
                    contextFn.toYul? =
                      some (.Def contextParams contextReturns
                        contextBody) →
                    FrontendOccurrence.StmtListUserCall generated
                      frontendArgs contextFn.body →
                    ordered.program.contract.functions.lookup
                        contextGenerated =
                      some (.Def contextParams contextReturns
                        contextBody) ∧
                    ∃ yulArgs,
                      FocusedGeneratedStmtListCallPrefix state ordered
                        generated calleeFn params returns body yulArgs
                        contextBody fuel (some ordered.program.contract)
                        shared vars := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_functionBodyPrefixOfFrontendOccurrence
          hCodeEvidence hConvert

theorem generatedNormalizationEvidence_prefixOfCodeRoute
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {generated : Name} {calleeFn : Frontend.FunctionDef}
                  {params returns : List Name} {body : List Yul.AstStmt}
                  {frontendArgs : List Frontend.Expr}
                  {fuel : Nat} {shared : EvmYul.SharedState .Yul}
                  {vars : EvmYul.Yul.VarStore},
                (generated, calleeFn) ∈ state.hoistedFunctions →
                  calleeFn.toYul? = some (.Def params returns body) →
                    RawOccurrence.CodeElaborationRoute state generated
                      frontendArgs object.dispatcher →
                    ∃ (yulArgs : List Yul.AstExpr)
                      (stmts : List Yul.AstStmt),
                      FocusedGeneratedStmtListCallPrefix state ordered
                        generated calleeFn params returns body yulArgs stmts
                        fuel (some ordered.program.contract) shared vars := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      exact
        codeGeneratedNormalizationEvidence_prefixOfCodeRoute
          hCodeEvidence hConvert

theorem generatedNormalizationEvidence_prefixOfRawOccurrence
    {raw : Raw.Object} {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    (hEvidence : Raw.Object.GeneratedNormalizationEvidence raw object)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered) :
    match raw.code? with
    | none => True
    | some code =>
        ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
            (helper? arg? ret? : Option Name),
          elaborateCodeCore code = .ok (coreDispatcher, state) ∧
            elaborateCode code =
              .ok (object.dispatcher, object.functions,
                helper?, arg?, ret?) ∧
              ∀ {functionName : Name} {rawArgs : List Raw.Expr},
                RawOccurrence.StmtListUserCall functionName rawArgs code →
                  functionName ≠ "memoryguard" →
                    functionName ≠ "clz" →
                      CallClass.classifyCall functionName = .user →
                        ∃ (generated : Name)
                          (frontendArgs : List Frontend.Expr),
                          ∀ {fuel : Nat}
                              {shared : EvmYul.SharedState .Yul}
                              {vars : EvmYul.Yul.VarStore},
                            ∃ (params returns : List Name)
                              (body : List Yul.AstStmt)
                              (yulArgs : List Yul.AstExpr)
                              (stmts : List Yul.AstStmt),
                              FocusedGeneratedCallPrefixEvidence ordered
                                generated params returns body yulArgs stmts
                                fuel (some ordered.program.contract) shared
                                vars := by
  cases hRawCode : raw.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      have hCodeEvidence :
          Raw.Object.CodeGeneratedNormalizationEvidence code object := by
        simpa [Raw.Object.GeneratedNormalizationEvidence, hRawCode]
          using hEvidence.2.2.2
      have hPrefix :
          ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
              (helper? arg? ret? : Option Name),
            elaborateCodeCore code = .ok (coreDispatcher, state) ∧
              elaborateCode code =
                .ok (object.dispatcher, object.functions,
                  helper?, arg?, ret?) ∧
                ∀ {generated : Name} {frontendArgs : List Frontend.Expr}
                    {fuel : Nat} {shared : EvmYul.SharedState .Yul}
                    {vars : EvmYul.Yul.VarStore},
                  RawOccurrence.CodeElaborationRoute state generated
                    frontendArgs object.dispatcher →
                    ∃ (params returns : List Name)
                      (body : List Yul.AstStmt)
                      (yulArgs : List Yul.AstExpr)
                      (stmts : List Yul.AstStmt),
                      FocusedGeneratedCallPrefixEvidence ordered generated
                        params returns body yulArgs stmts fuel
                        (some ordered.program.contract) shared vars := by
        exact
          codeGeneratedNormalizationEvidence_prefixEvidenceOfCodeRoute
            hCodeEvidence hConvert
      have hRoute :
          ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
              (helper? arg? ret? : Option Name),
            elaborateCodeCore code = .ok (coreDispatcher, state) ∧
              elaborateCode code =
                .ok (object.dispatcher, object.functions,
                  helper?, arg?, ret?) ∧
                ∀ {functionName : Name} {rawArgs : List Raw.Expr},
                  RawOccurrence.StmtListUserCall functionName rawArgs code →
                    functionName ≠ "memoryguard" →
                      functionName ≠ "clz" →
                        CallClass.classifyCall functionName = .user →
                          ∃ (generated : Name)
                            (frontendArgs : List Frontend.Expr),
                            RawOccurrence.CodeElaborationRoute state
                              generated frontendArgs object.dispatcher := by
        simpa [hRawCode] using
          generatedNormalizationEvidence_codeRouteOfRawOccurrence hEvidence
      rcases hPrefix with
        ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hPrefixRest⟩
      rcases hPrefixRest with ⟨hElab, hPrefixRoute⟩
      rcases hRoute with
        ⟨coreDispatcherRoute, stateRoute, helperRoute?, argRoute?,
          retRoute?, hCoreRoute, hRouteRest⟩
      rcases hRouteRest with ⟨hElabRoute, hRouteOfRaw⟩
      rw [hCore] at hCoreRoute
      simp at hCoreRoute
      rcases hCoreRoute with ⟨hDispatcherEq, hStateEq⟩
      subst coreDispatcherRoute
      subst stateRoute
      refine ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
      intro functionName rawArgs hOccurrence hNotMemoryguard hNotClz hKind
      rcases hRouteOfRaw hOccurrence hNotMemoryguard hNotClz hKind with
        ⟨generated, frontendArgs, hRoute⟩
      exact
        ⟨generated, frontendArgs,
          fun {fuel shared vars} => hPrefixRoute hRoute⟩

theorem decodeAndElaborateSolcIr?_focusedGeneratedCallOccurrence
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {generated : Name} {fn : Frontend.FunctionDef}
                            {params returns : List Name}
                            {body : List Yul.AstStmt}
                            {argExprs : List Yul.AstExpr},
                          (generated, fn) ∈ state.hoistedFunctions →
                            fn.toYul? = some (.Def params returns body) →
                              FocusedGeneratedCallOccurrence state ordered
                                generated fn params returns body argExprs := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_focusedGeneratedCallOccurrence
        hEvidence hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_dispatcherPrefix
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {generated : Name} {fn : Frontend.FunctionDef}
                            {params returns : List Name}
                            {body : List Yul.AstStmt}
                            {frontendArgs : List Frontend.Expr}
                            {yulArgs : List Yul.AstExpr}
                            {fuel : Nat}
                            {shared : EvmYul.SharedState .Yul}
                            {vars : EvmYul.Yul.VarStore},
                          (generated, fn) ∈ state.hoistedFunctions →
                            fn.toYul? = some (.Def params returns body) →
                            FrontendOccurrence.StmtListUserCall generated
                              frontendArgs object.dispatcher →
                            Frontend.Expr.List.toYul? frontendArgs =
                              some yulArgs →
                            FocusedGeneratedStmtListCallPrefix state ordered
                              generated fn params returns body yulArgs
                              [ordered.program.contract.dispatcher] fuel
                              (some ordered.program.contract) shared vars := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_dispatcherPrefix
        hEvidence hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_dispatcherPrefixOfFrontendOccurrence
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {generated : Name} {fn : Frontend.FunctionDef}
                            {params returns : List Name}
                            {body : List Yul.AstStmt}
                            {frontendArgs : List Frontend.Expr}
                            {fuel : Nat}
                            {shared : EvmYul.SharedState .Yul}
                            {vars : EvmYul.Yul.VarStore},
                          (generated, fn) ∈ state.hoistedFunctions →
                            fn.toYul? = some (.Def params returns body) →
                            FrontendOccurrence.StmtListUserCall generated
                              frontendArgs object.dispatcher →
                            ∃ yulArgs,
                              FocusedGeneratedStmtListCallPrefix state ordered
                                generated fn params returns body yulArgs
                                [ordered.program.contract.dispatcher] fuel
                                (some ordered.program.contract) shared vars := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_dispatcherPrefixOfFrontendOccurrence
        hEvidence hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_functionBodyPrefix
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {generated contextGenerated : Name}
                            {calleeFn contextFn : Frontend.FunctionDef}
                            {params returns : List Name}
                            {body : List Yul.AstStmt}
                            {contextParams contextReturns : List Name}
                            {contextBody : List Yul.AstStmt}
                            {frontendArgs : List Frontend.Expr}
                            {yulArgs : List Yul.AstExpr}
                            {fuel : Nat}
                            {shared : EvmYul.SharedState .Yul}
                            {vars : EvmYul.Yul.VarStore},
                          (generated, calleeFn) ∈ state.hoistedFunctions →
                            calleeFn.toYul? =
                              some (.Def params returns body) →
                            (contextGenerated, contextFn) ∈
                              state.hoistedFunctions →
                            contextFn.toYul? =
                              some (.Def contextParams contextReturns
                                contextBody) →
                            FrontendOccurrence.StmtListUserCall generated
                              frontendArgs contextFn.body →
                            Frontend.Expr.List.toYul? frontendArgs =
                              some yulArgs →
                            ordered.program.contract.functions.lookup
                                contextGenerated =
                              some (.Def contextParams contextReturns
                                contextBody) ∧
                            FocusedGeneratedStmtListCallPrefix state ordered
                              generated calleeFn params returns body yulArgs
                              contextBody fuel (some ordered.program.contract)
                              shared vars := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_functionBodyPrefix
        hEvidence hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_functionBodyPrefixOfFrontendOccurrence
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {generated contextGenerated : Name}
                            {calleeFn contextFn : Frontend.FunctionDef}
                            {params returns : List Name}
                            {body : List Yul.AstStmt}
                            {contextParams contextReturns : List Name}
                            {contextBody : List Yul.AstStmt}
                            {frontendArgs : List Frontend.Expr}
                            {fuel : Nat}
                            {shared : EvmYul.SharedState .Yul}
                            {vars : EvmYul.Yul.VarStore},
                          (generated, calleeFn) ∈ state.hoistedFunctions →
                            calleeFn.toYul? =
                              some (.Def params returns body) →
                            (contextGenerated, contextFn) ∈
                              state.hoistedFunctions →
                            contextFn.toYul? =
                              some (.Def contextParams contextReturns
                                contextBody) →
                            FrontendOccurrence.StmtListUserCall generated
                              frontendArgs contextFn.body →
                            ordered.program.contract.functions.lookup
                                contextGenerated =
                              some (.Def contextParams contextReturns
                                contextBody) ∧
                            ∃ yulArgs,
                              FocusedGeneratedStmtListCallPrefix state ordered
                                generated calleeFn params returns body yulArgs
                                contextBody fuel
                                (some ordered.program.contract) shared vars := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_functionBodyPrefixOfFrontendOccurrence
        hEvidence hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_prefixOfCodeRoute
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {generated : Name}
                            {calleeFn : Frontend.FunctionDef}
                            {params returns : List Name}
                            {body : List Yul.AstStmt}
                            {frontendArgs : List Frontend.Expr}
                            {fuel : Nat}
                            {shared : EvmYul.SharedState .Yul}
                            {vars : EvmYul.Yul.VarStore},
                          (generated, calleeFn) ∈ state.hoistedFunctions →
                            calleeFn.toYul? =
                              some (.Def params returns body) →
                            RawOccurrence.CodeElaborationRoute state
                              generated frontendArgs object.dispatcher →
                            ∃ (yulArgs : List Yul.AstExpr)
                              (stmts : List Yul.AstStmt),
                              FocusedGeneratedStmtListCallPrefix state ordered
                                generated calleeFn params returns body
                                yulArgs stmts fuel
                                (some ordered.program.contract) shared vars := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_prefixOfCodeRoute
        hEvidence hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_prefixOfRawOccurrence
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {functionName : Name}
                            {rawArgs : List Raw.Expr},
                          RawOccurrence.StmtListUserCall functionName
                            rawArgs code →
                            functionName ≠ "memoryguard" →
                              functionName ≠ "clz" →
                                CallClass.classifyCall functionName =
                                  .user →
                                  ∃ (generated : Name)
                                    (frontendArgs : List Frontend.Expr),
                                    ∀ {fuel : Nat}
                                        {shared : EvmYul.SharedState .Yul}
                                        {vars : EvmYul.Yul.VarStore},
                                      ∃ (params returns : List Name)
                                        (body : List Yul.AstStmt)
                                        (yulArgs : List Yul.AstExpr)
                                        (stmts : List Yul.AstStmt),
                                        FocusedGeneratedCallPrefixEvidence
                                          ordered generated params returns
                                          body yulArgs stmts fuel
                                          (some
                                            ordered.program.contract)
                                          shared vars := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  have hObjectConvert :
      object.toSolcYulOrderedProgram? = some ordered := by
    simpa [hProgram] using hConvert
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_prefixOfRawOccurrence hEvidence
        hObjectConvert⟩

theorem decodeAndElaborateSolcIr?_semanticInterfaceOfRawOccurrence
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program} {ordered : Yul.OrderedProgram}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program)
    (hConvert : program.object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {functionName : Name}
                            {rawArgs : List Raw.Expr},
                          RawOccurrence.StmtListUserCall functionName
                            rawArgs code →
                            functionName ≠ "memoryguard" →
                              functionName ≠ "clz" →
                                CallClass.classifyCall functionName =
                                  .user →
                                  ∃ (generated : Name)
                                    (frontendArgs : List Frontend.Expr),
                                    ∀ {fuel : Nat}
                                        {shared : EvmYul.SharedState .Yul}
                                        {vars : EvmYul.Yul.VarStore},
                                      ∃ (params returns : List Name)
                                        (body : List Yul.AstStmt)
                                        (yulArgs : List Yul.AstExpr)
                                        (stmts : List Yul.AstStmt),
                                        FocusedGeneratedCallSemanticInterface
                                          ordered generated params returns
                                          body yulArgs stmts fuel
                                          (some
                                            ordered.program.contract)
                                          shared vars := by
  rcases decodeAndElaborateSolcIr?_prefixOfRawOccurrence hDecode hConvert with
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram, hPrefix⟩
  refine ⟨json, selected, object, hParse, hSelected, hObject, hProgram, ?_⟩
  cases hRawCode : selected.root.code? with
  | none =>
      simp [hRawCode]
  | some code =>
      rw [hRawCode] at hPrefix
      rcases hPrefix with
        ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab,
          hOccurrencePrefix⟩
      refine
        ⟨coreDispatcher, state, helper?, arg?, ret?, hCore, hElab, ?_⟩
      intro functionName rawArgs hOccurrence hNotMemoryguard hNotClz
        hKind
      rcases hOccurrencePrefix hOccurrence hNotMemoryguard hNotClz
          hKind with
        ⟨generated, frontendArgs, hGenerated⟩
      refine ⟨generated, frontendArgs, ?_⟩
      intro fuel shared vars
      rcases hGenerated with
        ⟨params, returns, body, yulArgs, stmts, hEvidence⟩
      exact
        ⟨params, returns, body, yulArgs, stmts,
          FocusedGeneratedCallSemanticInterface.of_prefixEvidence
            hEvidence⟩

theorem decodeAndElaborateSolcIr?_codeRouteOfRawOccurrence
    {rawJson : String} {selection : Selection}
    {program : Frontend.Program}
    (hDecode :
      decodeAndElaborateSolcIr? rawJson selection = some program) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              match selected.root.code? with
              | none => True
              | some code =>
                  ∃ (coreDispatcher : List Frontend.Stmt) (state : State)
                      (helper? arg? ret? : Option Name),
                    elaborateCodeCore code = .ok (coreDispatcher, state) ∧
                      elaborateCode code =
                        .ok (object.dispatcher, object.functions,
                          helper?, arg?, ret?) ∧
                        ∀ {functionName : Name}
                            {rawArgs : List Raw.Expr},
                          RawOccurrence.StmtListUserCall functionName
                            rawArgs code →
                            functionName ≠ "memoryguard" →
                              functionName ≠ "clz" →
                                CallClass.classifyCall functionName =
                                  .user →
                                  ∃ (generated : Name)
                                    (frontendArgs : List Frontend.Expr),
                                    RawOccurrence.CodeElaborationRoute state
                                      generated frontendArgs
                                      object.dispatcher := by
  rcases decodeAndElaborateSolcIr?_generatedNormalizationEvidence
      hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hEvidence,
      hProgram⟩
  exact
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram,
      generatedNormalizationEvidence_codeRouteOfRawOccurrence hEvidence⟩

end Elab
end RawAst
end Solidity
end EvmCompiler
