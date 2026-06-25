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
