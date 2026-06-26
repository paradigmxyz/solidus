import EvmCompiler.Solidity.RawAst
import EvmCompiler.Yul.InteractionSemantics

/-!
Semantic preservation for the compiler-generated `clz` helper.

`RawAst.Elab.ClzHelperExecution` gives the generated frontend fragment a small
executable model. This module relates that model to the actual canonical Yul
interaction semantics after checked `Frontend.Expr/Stmt.toYul?` conversion.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace Raw
namespace ClzPreservation

abbrev State := Yul.InteractionSemantics.State
abbrev Open (α : Type) := Yul.InteractionSemantics.Open α
abbrev ModelState := Elab.ClzHelperModel.State

mutual
  def exprFuel : Frontend.Expr → Nat
    | .lit _ | .stringLit _ | .bytesLit _ | .var _ => 1
    | .call _ _ args => exprListFuel args + 2

  def exprListFuel : List Frontend.Expr → Nat
    | [] => 1
    | expr :: rest => exprFuel expr + exprListFuel rest + 2
end

mutual
  def stmtFuel : Frontend.Stmt → Nat
    | .block body => stmtListFuel body + 1
    | .assign _ value => exprFuel value + 1
    | .ifThen condition body =>
        exprFuel condition + stmtListFuel body + 3
    | .letDecl _ none | .break | .continue | .leave => 1
    | .letDecl _ (some value) | .exprStmt value => exprFuel value + 1
    | .functionDef _ _ _ body => stmtListFuel body + 1
    | .switch condition cases defaultBody =>
        exprFuel condition + caseListFuel cases + stmtListFuel defaultBody + 3
    | .forLoop pre condition post body =>
        stmtListFuel pre + exprFuel condition + stmtListFuel post +
          stmtListFuel body + 4

  def stmtListFuel : List Frontend.Stmt → Nat
    | [] => 1
    | stmt :: rest => stmtFuel stmt + stmtListFuel rest + 1

  def caseListFuel :
      List (Frontend.SwitchCaseValue × List Frontend.Stmt) → Nat
    | [] => 1
    | (_, body) :: rest => stmtListFuel body + caseListFuel rest + 1
end

def helperBodyFuel : Nat :=
  stmtListFuel (Elab.clzHelperBody "" "")

theorem helperBodyFuel_eq (argName returnName : Name) :
    stmtListFuel (Elab.clzHelperBody argName returnName) = helperBodyFuel := by
  rfl

theorem helperBodyFuel_value : helperBodyFuel = 330 := by
  rfl

theorem clzHelperFunctionDef_resolveObjectBuiltinsIn?
    (argName returnName : Name)
    (context : Frontend.ObjectBuiltinContext) :
    Frontend.FunctionDef.resolveObjectBuiltinsIn?
        (Elab.clzHelperFunctionDef argName returnName) context =
      some (Elab.clzHelperFunctionDef argName returnName) := by
  unfold Elab.clzHelperFunctionDef Elab.clzHelperBody
    Elab.clzHelperNonzeroBody Elab.clzHelperAppendStep
    Elab.clzHelperStepBody Elab.clzHelperStepSchedule Elab.clzPrim
    Elab.clzValue Elab.clzWord
    Frontend.FunctionDef.resolveObjectBuiltinsIn?
  simp [Frontend.Stmt.List.resolveObjectBuiltinsIn?,
    Frontend.Stmt.resolveObjectBuiltinsIn?,
    Frontend.Expr.resolveObjectBuiltinsIn?,
    Frontend.Expr.List.resolveObjectBuiltinsIn?]

/-- The generated helper owns exactly two semantically relevant names. Other
Yul locals may remain in the store, but helper expressions never inspect them.
-/
structure StateRel (argName returnName : Name)
    (model : ModelState) (actual : State) : Prop where
  regular : ∃ shared store, actual = .Ok shared store
  arg : actual.lookup? argName = some model.arg
  ret : actual.lookup? returnName = some model.ret

namespace StateRel

theorem checkAssignment_arg
    {argName returnName : Name} {model : ModelState} {actual : State}
    (hRel : StateRel argName returnName model actual) :
    EvmYul.Yul.checkAssignment actual [argName] = .ok () := by
  rcases hRel.regular with ⟨shared, store, rfl⟩
  have hSome : Finmap.lookup argName store = some model.arg := hRel.arg
  unfold EvmYul.Yul.checkAssignment EvmYul.Yul.firstDuplicate?
    EvmYul.Yul.firstUndeclared?
  simp only [EvmYul.Yul.State.lookup?]
  simp [EvmYul.Yul.firstDuplicate?, hSome]

theorem checkAssignment_ret
    {argName returnName : Name} {model : ModelState} {actual : State}
    (hRel : StateRel argName returnName model actual) :
    EvmYul.Yul.checkAssignment actual [returnName] = .ok () := by
  rcases hRel.regular with ⟨shared, store, rfl⟩
  have hSome : Finmap.lookup returnName store = some model.ret := hRel.ret
  unfold EvmYul.Yul.checkAssignment EvmYul.Yul.firstDuplicate?
    EvmYul.Yul.firstUndeclared?
  simp only [EvmYul.Yul.State.lookup?]
  simp [EvmYul.Yul.firstDuplicate?, hSome]

theorem assign_arg
    {argName returnName : Name} {model : ModelState} {actual : State}
    (hRel : StateRel argName returnName model actual)
    (hNames : argName ≠ returnName) (value : Frontend.Word) :
    StateRel argName returnName { model with arg := value }
      (actual.multifill [argName] [value]) := by
  rcases hRel.regular with ⟨shared, store, rfl⟩
  constructor
  · exact ⟨shared, store.insert argName value, rfl⟩
  · simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert,
      EvmYul.Yul.State.lookup?]
  · simp only [EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup?]
    change Finmap.lookup returnName (store.insert argName value) = _
    rw [Finmap.lookup_insert_of_ne store (Ne.symm hNames)]
    exact hRel.ret

theorem assign_ret
    {argName returnName : Name} {model : ModelState} {actual : State}
    (hRel : StateRel argName returnName model actual)
    (hNames : argName ≠ returnName) (value : Frontend.Word) :
    StateRel argName returnName { model with ret := value }
      (actual.multifill [returnName] [value]) := by
  rcases hRel.regular with ⟨shared, store, rfl⟩
  constructor
  · exact ⟨shared, store.insert returnName value, rfl⟩
  · simp only [EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup?]
    change Finmap.lookup argName (store.insert returnName value) = _
    rw [Finmap.lookup_insert_of_ne store hNames]
    exact hRel.arg
  · simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert,
      EvmYul.Yul.State.lookup?]

theorem restrict_to_entry
    {argName returnName : Name}
    {entryModel finalModel : ModelState} {entry final : State}
    (hEntry : StateRel argName returnName entryModel entry)
    (hFinal : StateRel argName returnName finalModel final) :
    StateRel argName returnName finalModel
      (final.restrictStoreTo entry.store) := by
  rcases hEntry.regular with ⟨entryShared, entryStore, rfl⟩
  rcases hFinal.regular with ⟨finalShared, finalStore, rfl⟩
  constructor
  · exact
      ⟨finalShared,
        EvmYul.Yul.State.restrictVarStore finalStore entryStore, rfl⟩
  · simp only [EvmYul.Yul.State.restrictStoreTo,
      EvmYul.Yul.State.store, EvmYul.Yul.State.lookup?]
    rw [Yul.VarStoreRestriction.lookup_restrict_of_some
      finalStore entryStore argName hEntry.arg]
    exact hFinal.arg
  · simp only [EvmYul.Yul.State.restrictStoreTo,
      EvmYul.Yul.State.store, EvmYul.Yul.State.lookup?]
    rw [Yul.VarStoreRestriction.lookup_restrict_of_some
      finalStore entryStore returnName hEntry.ret]
    exact hFinal.ret

theorem lookup_of_readName
    {argName returnName name : Name}
    {model : ModelState} {actual : State} {value : Frontend.Word}
    (hRel : StateRel argName returnName model actual)
    (hRead :
      Elab.ClzHelperExecution.readName? argName returnName name model =
        some value) :
    actual.lookup? name = some value := by
  by_cases hArg : name = argName
  · subst name
    simp [Elab.ClzHelperExecution.readName?] at hRead
    subst value
    exact hRel.arg
  · by_cases hRet : name = returnName
    · subst name
      simp [Elab.ClzHelperExecution.readName?, hArg] at hRead
      subst value
      exact hRel.ret
    · simp [Elab.ClzHelperExecution.readName?, hArg, hRet] at hRead

theorem writeName_preserved
    {argName returnName name : Name}
    {model finalModel : ModelState} {actual : State}
    {value : Frontend.Word}
    (hRel : StateRel argName returnName model actual)
    (hNames : argName ≠ returnName)
    (hWrite :
      Elab.ClzHelperExecution.writeName? argName returnName name value model =
        some finalModel) :
    EvmYul.Yul.checkAssignment actual [name] = .ok () ∧
      StateRel argName returnName finalModel
        (actual.multifill [name] [value]) := by
  by_cases hArg : name = argName
  · subst name
    simp [Elab.ClzHelperExecution.writeName?] at hWrite
    subst finalModel
    exact ⟨hRel.checkAssignment_arg, hRel.assign_arg hNames value⟩
  · by_cases hRet : name = returnName
    · subst name
      simp [Elab.ClzHelperExecution.writeName?, hArg] at hWrite
      subst finalModel
      exact ⟨hRel.checkAssignment_ret, hRel.assign_ret hNames value⟩
    · simp [Elab.ClzHelperExecution.writeName?, hArg, hRet] at hWrite

theorem initcall
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (shared : EvmYul.SharedState .Yul) (callerStore : EvmYul.Yul.VarStore)
    (value : Frontend.Word) :
    StateRel argName returnName
      { arg := value, ret := Elab.ClzHelperModel.zero }
      (EvmYul.Yul.State.mkOk
        ((.Ok shared callerStore : State).initcall
          [argName] [returnName] [value])) := by
  constructor
  · refine ⟨shared, ?_, ?_⟩
    · exact
        ((default : EvmYul.Yul.VarStore).insert
          returnName Elab.ClzHelperModel.zero).insert
          argName value
    · rfl
  · simp [EvmYul.Yul.State.mkOk, EvmYul.Yul.State.initcall,
      EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup?]
  · simp [EvmYul.Yul.State.mkOk, EvmYul.Yul.State.initcall,
      EvmYul.Yul.State.setStore,
      EvmYul.Yul.State.zeroFill, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup?,
      Ne.symm hNames]
    rfl

theorem multifill_sharedState
    {argName returnName : Name} {model : ModelState} {actual : State}
    (hRel : StateRel argName returnName model actual)
    (names : List Name) (values : List Frontend.Word) :
    (actual.multifill names values).sharedState = actual.sharedState := by
  rcases hRel.regular with ⟨shared, store, rfl⟩
  unfold EvmYul.Yul.State.multifill
  have fold_ok (pairs : List (Name × Frontend.Word)) :
      ∃ finalStore,
        List.foldr (fun pair state => state.insert pair.1 pair.2)
            (.Ok shared store : State) pairs =
          .Ok shared finalStore := by
    induction pairs with
    | nil => exact ⟨store, rfl⟩
    | cons pair rest ih =>
        rcases pair with ⟨name, value⟩
        rcases ih with ⟨restStore, hRest⟩
        refine ⟨restStore.insert name value, ?_⟩
        simp only [List.foldr]
        rw [hRest]
        rfl
  rcases fold_ok (List.zip names values) with ⟨finalStore, hFinal⟩
  change
    (List.foldr (fun pair state => state.insert pair.1 pair.2)
      (.Ok shared store : State) (List.zip names values)).sharedState =
        (.Ok shared store : State).sharedState
  rw [hFinal]
  rfl

theorem restrictStoreTo_sharedState
    {argName returnName : Name} {model : ModelState} {actual : State}
    (hRel : StateRel argName returnName model actual)
    (scope : EvmYul.Yul.VarStore) :
    (actual.restrictStoreTo scope).sharedState = actual.sharedState := by
  rcases hRel.regular with ⟨shared, store, rfl⟩
  rfl

end StateRel

namespace Primitive

theorem add
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared store) (.ADD : EvmYul.Operation .Yul) [left, right] =
      .done (.ok (.Ok shared store, [EvmYul.UInt256.add left right])) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

theorem shl
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (shift value : Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared store) (.SHL : EvmYul.Operation .Yul) [shift, value] =
      .done
        (.ok
          (.Ok shared store, [EvmYul.UInt256.shiftLeft value shift])) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

theorem shr
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (shift value : Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared store) (.SHR : EvmYul.Operation .Yul) [shift, value] =
      .done
        (.ok
          (.Ok shared store, [EvmYul.UInt256.shiftRight value shift])) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

theorem iszero
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (value : Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
        (.Ok shared store) (.ISZERO : EvmYul.Operation .Yul) [value] =
      .done (.ok (.Ok shared store, [EvmYul.UInt256.isZero value])) := by
  simp [Yul.InteractionSemantics.Primitive.openEval,
    Yul.InteractionSemantics.Primitive.closedEval,
    Simulation.ExternalKind.ofYulOperation?,
    Simulation.CallKind.ofYulOperation?,
    Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  unfold EvmYul.step
  rfl

end Primitive

theorem exprListFuel_reverse (exprs : List Frontend.Expr) :
    exprListFuel exprs.reverse = exprListFuel exprs := by
  induction exprs with
  | nil => rfl
  | cons head rest tail_ih =>
      simp only [List.reverse_cons]
      have append_singleton : ∀ xs : List Frontend.Expr,
          exprListFuel (xs ++ [head]) =
            exprListFuel xs + exprFuel head + 2 := by
        intro xs
        induction xs with
        | nil => simp [exprListFuel, Nat.add_comm]
        | cons item items append_ih =>
            simp only [List.cons_append, exprListFuel]
            rw [append_ih]
            omega
      rw [append_singleton, tail_ih]
      simp only [exprListFuel]
      omega

theorem evalExprList?_append
    (argName returnName : Name) (model : ModelState)
    {left right : List Frontend.Expr}
    {leftValues rightValues : List Frontend.Word}
    (hLeft :
      Elab.ClzHelperExecution.evalExprList? argName returnName model left =
        some leftValues)
    (hRight :
      Elab.ClzHelperExecution.evalExprList? argName returnName model right =
        some rightValues) :
    Elab.ClzHelperExecution.evalExprList? argName returnName model
        (left ++ right) = some (leftValues ++ rightValues) := by
  induction left generalizing leftValues with
  | nil =>
      simp [Elab.ClzHelperExecution.evalExprList?] at hLeft ⊢
      subst leftValues
      exact hRight
  | cons head rest ih =>
      simp only [Elab.ClzHelperExecution.evalExprList?] at hLeft
      cases hHead : Elab.ClzHelperExecution.evalExpr?
          argName returnName model head with
      | none => simp [hHead] at hLeft
      | some headValue =>
          cases hRest : Elab.ClzHelperExecution.evalExprList?
              argName returnName model rest with
          | none => simp [hHead, hRest] at hLeft
          | some restValues =>
              simp [hHead, hRest] at hLeft
              subst leftValues
              simp only [List.cons_append,
                Elab.ClzHelperExecution.evalExprList?, hHead]
              rw [ih hRest]
              rfl

theorem evalExprList?_reverse
    (argName returnName : Name) (model : ModelState)
    (exprs : List Frontend.Expr) (values : List Frontend.Word)
    (hEval :
      Elab.ClzHelperExecution.evalExprList? argName returnName model exprs =
        some values) :
    Elab.ClzHelperExecution.evalExprList? argName returnName model
        exprs.reverse = some values.reverse := by
  induction exprs generalizing values with
  | nil =>
      simp [Elab.ClzHelperExecution.evalExprList?] at hEval ⊢
      exact hEval
  | cons head rest ih =>
      simp only [Elab.ClzHelperExecution.evalExprList?] at hEval
      cases hHead : Elab.ClzHelperExecution.evalExpr?
          argName returnName model head with
      | none => simp [hHead] at hEval
      | some headValue =>
          cases hRest : Elab.ClzHelperExecution.evalExprList?
              argName returnName model rest with
          | none => simp [hHead, hRest] at hEval
          | some restValues =>
              simp [hHead, hRest] at hEval
              subst values
              rw [List.reverse_cons, List.reverse_cons]
              exact evalExprList?_append argName returnName model
                (ih restValues hRest)
                (by
                  simp [Elab.ClzHelperExecution.evalExprList?, hHead])

theorem toYul?_append
    {left right : List Frontend.Expr}
    {yulLeft yulRight : List EvmYul.Yul.Ast.Expr}
    (hLeft : Frontend.Expr.List.toYul? left = some yulLeft)
    (hRight : Frontend.Expr.List.toYul? right = some yulRight) :
    Frontend.Expr.List.toYul? (left ++ right) =
      some (yulLeft ++ yulRight) := by
  induction left generalizing yulLeft with
  | nil =>
      simp [Frontend.Expr.List.toYul?] at hLeft ⊢
      subst yulLeft
      exact hRight
  | cons head rest ih =>
      simp only [Frontend.Expr.List.toYul?] at hLeft
      cases hHead : Frontend.Expr.toYul? head with
      | none => simp [hHead] at hLeft
      | some yulHead =>
          cases hRest : Frontend.Expr.List.toYul? rest with
          | none => simp [hHead, hRest] at hLeft
          | some yulRest =>
              simp [hHead, hRest] at hLeft
              subst yulLeft
              simp only [List.cons_append, Frontend.Expr.List.toYul?, hHead,
                ]
              rw [ih hRest]
              rfl

theorem toYul?_reverse
    (exprs : List Frontend.Expr) (yulExprs : List EvmYul.Yul.Ast.Expr)
    (hYul : Frontend.Expr.List.toYul? exprs = some yulExprs) :
    Frontend.Expr.List.toYul? exprs.reverse = some yulExprs.reverse := by
  induction exprs generalizing yulExprs with
  | nil =>
      simp [Frontend.Expr.List.toYul?] at hYul ⊢
      exact hYul
  | cons head rest ih =>
      simp only [Frontend.Expr.List.toYul?] at hYul
      cases hHead : Frontend.Expr.toYul? head with
      | none => simp [hHead] at hYul
      | some yulHead =>
          cases hRest : Frontend.Expr.List.toYul? rest with
          | none => simp [hHead, hRest] at hYul
          | some yulRest =>
              simp [hHead, hRest] at hYul
              subst yulExprs
              rw [List.reverse_cons, List.reverse_cons]
              exact toYul?_append (ih yulRest hRest)
                (by simp [Frontend.Expr.List.toYul?, hHead])

theorem primitive_of_model
    {fuel : Nat} {callee : Name} {values : List Frontend.Word}
    {value : Frontend.Word} {actual : State}
    (hRegular : ∃ shared store, actual = .Ok shared store)
    (hEval :
      Elab.ClzHelperExecution.evalPrimitive? callee values = some value) :
    ∃ op,
      Frontend.Primitive.ofName? callee = some op ∧
      Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
          actual op values = .done (.ok (actual, [value])) := by
  rcases hRegular with ⟨shared, store, rfl⟩
  rcases values with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;>
    simp only [Elab.ClzHelperExecution.evalPrimitive?] at hEval
  · simp at hEval
  · by_cases hZero : callee = "iszero"
    · subst callee
      injection hEval with hValue
      subst value
      exact ⟨.ISZERO, rfl, Primitive.iszero fuel shared store first⟩
    · simp [hZero] at hEval
  · cases rest with
    | cons third tail => simp at hEval
    | nil =>
        by_cases hAdd : callee = "add"
        · subst callee
          injection hEval with hValue
          subst value
          exact ⟨.ADD, rfl, Primitive.add fuel shared store first second⟩
        · by_cases hShl : callee = "shl"
          · subst callee
            injection hEval with hValue
            subst value
            exact ⟨.SHL, rfl, Primitive.shl fuel shared store first second⟩
          · by_cases hShr : callee = "shr"
            · subst callee
              injection hEval with hValue
              subst value
              exact ⟨.SHR, rfl, Primitive.shr fuel shared store first second⟩
            · simp [hAdd, hShl, hShr] at hEval

theorem primitive_of_model_at
    {fuel : Nat} {callee : Name} {values : List Frontend.Word}
    {value : Frontend.Word} {actual : State}
    (hRegular : ∃ shared store, actual = .Ok shared store)
    (hFuel : 2 ≤ fuel)
    (hEval :
      Elab.ClzHelperExecution.evalPrimitive? callee values = some value) :
    ∃ op,
      Frontend.Primitive.ofName? callee = some op ∧
      Yul.InteractionSemantics.Primitive.openEval fuel actual op values =
        .done (.ok (actual, [value])) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  simpa [Nat.add_comm] using
    (primitive_of_model (fuel := extra) hRegular hEval)

theorem truthy_eq_true_iff (value : Frontend.Word) :
    Elab.ClzHelperExecution.truthy value = true ↔
      value ≠ Elab.ClzHelperModel.zero := by
  cases value with
  | mk value =>
      simp [Elab.ClzHelperExecution.truthy, bne,
        Elab.ClzHelperModel.zero, EvmYul.instBEqUInt256,
        EvmYul.instBEqUInt256.beq, EvmYul.UInt256.ofNat, Id.run]

mutual
  theorem evalExpr_of_model
      {argName returnName : Name} {model : ModelState} {actual : State}
      {expr : Frontend.Expr} {yulExpr : EvmYul.Yul.Ast.Expr}
      {value : Frontend.Word}
      (hRel : StateRel argName returnName model actual)
      (hEval :
        Elab.ClzHelperExecution.evalExpr? argName returnName model expr =
          some value)
      (hYul : Frontend.Expr.toYul? expr = some yulExpr)
      (code : Option EvmYul.Yul.Ast.YulContract) (fuel : Nat)
      (hFuel : exprFuel expr ≤ fuel) :
      Yul.InteractionSemantics.evalValues fuel yulExpr code actual =
        .done (.ok (actual, [value])) := by
    cases expr with
    | lit literal =>
        simp only [Elab.ClzHelperExecution.evalExpr?] at hEval
        injection hEval with hValue
        subst value
        simp only [Frontend.Expr.toYul?] at hYul
        injection hYul with hExpr
        subst yulExpr
        cases fuel with
        | zero => simp [exprFuel] at hFuel
        | succ previous =>
            simp [Yul.InteractionSemantics.evalValues,
              Yul.Source.Canonical.evalValues,
              Yul.Source.Effectful.evalValues]
            rfl
    | stringLit literal =>
        simp [Elab.ClzHelperExecution.evalExpr?] at hEval
    | bytesLit literal =>
        simp [Elab.ClzHelperExecution.evalExpr?] at hEval
    | var name =>
        simp only [Elab.ClzHelperExecution.evalExpr?] at hEval
        have hLookup := StateRel.lookup_of_readName hRel hEval
        simp only [Frontend.Expr.toYul?] at hYul
        injection hYul with hExpr
        subst yulExpr
        cases fuel with
        | zero => simp [exprFuel] at hFuel
        | succ previous =>
            simp [Yul.InteractionSemantics.evalValues,
              Yul.Source.Canonical.evalValues,
              Yul.Source.Effectful.evalValues,
              Yul.InteractionSemantics.stateModel, hLookup]
            rfl
    | call kind callee args =>
        cases kind with
        | primitive =>
            simp only [Elab.ClzHelperExecution.evalExpr?] at hEval
            cases hArgsEval : Elab.ClzHelperExecution.evalExprList?
                argName returnName model args with
            | none => simp [hArgsEval] at hEval
            | some values =>
                have hPrimEval :
                    Elab.ClzHelperExecution.evalPrimitive? callee values =
                      some value := by
                  simpa [hArgsEval] using hEval
                simp only [Frontend.Expr.toYul?] at hYul
                cases hOp : Frontend.Primitive.ofName? callee with
                | none => simp [hOp] at hYul
                | some op =>
                    cases hArgsYul : Frontend.Expr.List.toYul? args with
                    | none => simp [hOp, hArgsYul] at hYul
                    | some yulArgs =>
                        simp [hOp, hArgsYul] at hYul
                        subst yulExpr
                        have hEvalReverse :=
                          evalExprList?_reverse argName returnName model
                            args values hArgsEval
                        have hYulReverse :=
                          toYul?_reverse args yulArgs hArgsYul
                        have hFuelTwo : 2 ≤ fuel := by
                          simp only [exprFuel] at hFuel
                          omega
                        have hFuelPred :
                            exprListFuel args.reverse ≤ fuel - 1 := by
                          rw [exprListFuel_reverse]
                          simp only [exprFuel] at hFuel
                          omega
                        have hArgsRun := evalExprList_of_model hRel
                          hEvalReverse hYulReverse code (fuel - 1) hFuelPred
                        change
                          Yul.Source.Effectful.evalArgs
                              Yul.InteractionSemantics.stateModel
                              Yul.InteractionSemantics.primitiveSemantics
                              (fuel - 1) yulArgs.reverse code actual =
                            .done (.ok (actual, values.reverse)) at hArgsRun
                        have hOpenFuel : 2 ≤ fuel - 1 := by
                          have hArgsPositive : 1 ≤ exprListFuel args := by
                            cases args <;> simp [exprListFuel]
                          simp only [exprFuel] at hFuel
                          omega
                        rcases primitive_of_model_at hRel.regular hOpenFuel
                            hPrimEval with
                          ⟨modelOp, hModelOp, hPrimitiveRun⟩
                        rw [hOp] at hModelOp
                        injection hModelOp with hOpEq
                        subst modelOp
                        have hFuelEq : fuel = (fuel - 1) + 1 := by omega
                        rw [hFuelEq]
                        simp only [Yul.InteractionSemantics.evalValues,
                          Yul.Source.Canonical.evalValues,
                          Yul.Source.Effectful.evalValues]
                        rw [hArgsRun]
                        simpa [Simulation.Interaction.instMonad,
                          Simulation.Interaction.bind,
                          Yul.InteractionSemantics.primitiveSemantics]
                          using hPrimitiveRun
        | user => simp [Elab.ClzHelperExecution.evalExpr?] at hEval
        | objectBuiltin =>
            simp [Elab.ClzHelperExecution.evalExpr?] at hEval
        | dialectBuiltin =>
            simp [Elab.ClzHelperExecution.evalExpr?] at hEval
  termination_by fuel
  decreasing_by all_goals omega

  theorem evalExprList_of_model
      {argName returnName : Name} {model : ModelState} {actual : State}
      {exprs : List Frontend.Expr}
      {yulExprs : List EvmYul.Yul.Ast.Expr}
      {values : List Frontend.Word}
      (hRel : StateRel argName returnName model actual)
      (hEval :
        Elab.ClzHelperExecution.evalExprList? argName returnName model exprs =
          some values)
      (hYul : Frontend.Expr.List.toYul? exprs = some yulExprs)
      (code : Option EvmYul.Yul.Ast.YulContract) (fuel : Nat)
      (hFuel : exprListFuel exprs ≤ fuel) :
      Yul.InteractionSemantics.evalArgs fuel yulExprs code actual =
        .done (.ok (actual, values)) := by
    cases exprs with
    | nil =>
        simp [Elab.ClzHelperExecution.evalExprList?] at hEval
        subst values
        simp [Frontend.Expr.List.toYul?] at hYul
        subst yulExprs
        cases fuel with
        | zero => simp [exprListFuel] at hFuel
        | succ previous =>
            exact Yul.InteractionSemantics.EvalArgs.nil_succ previous code
              actual
    | cons head rest =>
        simp only [Elab.ClzHelperExecution.evalExprList?] at hEval
        cases hHeadEval : Elab.ClzHelperExecution.evalExpr?
            argName returnName model head with
        | none => simp [hHeadEval] at hEval
        | some headValue =>
            cases hRestEval : Elab.ClzHelperExecution.evalExprList?
                argName returnName model rest with
            | none => simp [hHeadEval, hRestEval] at hEval
            | some restValues =>
                simp [hHeadEval, hRestEval] at hEval
                subst values
                simp only [Frontend.Expr.List.toYul?] at hYul
                cases hHeadYul : Frontend.Expr.toYul? head with
                | none => simp [hHeadYul] at hYul
                | some yulHead =>
                    cases hRestYul : Frontend.Expr.List.toYul? rest with
                    | none => simp [hHeadYul, hRestYul] at hYul
                    | some yulRest =>
                        simp [hHeadYul, hRestYul] at hYul
                        subst yulExprs
                        have hFuelEq : fuel = (fuel - 2) + 2 := by
                          simp only [exprListFuel] at hFuel
                          omega
                        rw [hFuelEq,
                          Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
                        have hHeadRun := evalExpr_of_model hRel hHeadEval
                          hHeadYul code ((fuel - 2) + 1) (by
                            simp only [exprListFuel] at hFuel
                            omega)
                        rw [hHeadRun]
                        simp only [Simulation.Interaction.bind_done_ok]
                        have hRestRun := evalExprList_of_model hRel hRestEval
                          hRestYul code (fuel - 2) (by
                            simp only [exprListFuel] at hFuel
                            omega)
                        rw [hRestRun]
                        rfl
  termination_by fuel
  decreasing_by all_goals omega
end

mutual
  theorem execStmt_of_model
      {argName returnName : Name} {model finalModel : ModelState}
      {actual : State} {stmt : Frontend.Stmt}
      {yulStmt : EvmYul.Yul.Ast.Stmt}
      (hRel : StateRel argName returnName model actual)
      (hNames : argName ≠ returnName)
      (hExec :
        Elab.ClzHelperExecution.execStmt? argName returnName model stmt =
          some finalModel)
      (hYul : Frontend.Stmt.toYul? stmt = some yulStmt)
      (code : Option EvmYul.Yul.Ast.YulContract) (fuel : Nat)
      (hFuel : stmtFuel stmt ≤ fuel) :
      ∃ finalActual,
        Yul.InteractionSemantics.exec fuel yulStmt code actual =
          .done (.ok finalActual) ∧
        StateRel argName returnName finalModel finalActual ∧
        finalActual.sharedState = actual.sharedState := by
    cases stmt with
    | block body =>
        simp only [stmtFuel] at hFuel
        simp only [Elab.ClzHelperExecution.execStmt?] at hExec
        simp only [Frontend.Stmt.toYul?] at hYul
        cases hBodyYul : Frontend.Stmt.List.toYul? body with
        | none => simp [hBodyYul] at hYul
        | some yulBody =>
            simp [hBodyYul] at hYul
            subst yulStmt
            have hBodyRun := execStmts_of_model hRel hNames hExec hBodyYul
              code (fuel - 1) (by omega)
            rcases hBodyRun with
              ⟨afterBody, hRun, hAfterRel, hAfterShared⟩
            refine
              ⟨afterBody.restrictStoreTo actual.store, ?_, ?_, ?_⟩
            · have hFuelEq : fuel = (fuel - 1) + 1 := by omega
              rw [hFuelEq, Yul.InteractionSemantics.Exec.block_succ, hRun]
              rfl
            · exact hRel.restrict_to_entry hAfterRel
            · exact
                (hAfterRel.restrictStoreTo_sharedState actual.store).trans
                  hAfterShared
    | assign names valueExpr =>
        cases names with
        | nil => simp [Elab.ClzHelperExecution.execStmt?] at hExec
        | cons name rest =>
            cases rest with
            | cons next tail =>
                simp [Elab.ClzHelperExecution.execStmt?] at hExec
            | nil =>
                simp only [Elab.ClzHelperExecution.execStmt?] at hExec
                cases hValueEval : Elab.ClzHelperExecution.evalExpr?
                    argName returnName model valueExpr with
                | none => simp [hValueEval] at hExec
                | some value =>
                    cases hWrite : Elab.ClzHelperExecution.writeName?
                        argName returnName name value model with
                    | none => simp [hValueEval, hWrite] at hExec
                    | some writtenModel =>
                        simp [hValueEval, hWrite] at hExec
                        subst finalModel
                        simp only [Frontend.Stmt.toYul?] at hYul
                        cases hValueYul : Frontend.Expr.toYul? valueExpr with
                        | none => simp [hValueYul] at hYul
                        | some yulValue =>
                            simp [hValueYul] at hYul
                            subst yulStmt
                            rcases StateRel.writeName_preserved hRel hNames
                                hWrite with
                              ⟨hCheck, hWrittenRel⟩
                            have hValueRun := evalExpr_of_model hRel hValueEval
                              hValueYul code (fuel - 1) (by
                                simp only [stmtFuel] at hFuel
                                omega)
                            refine
                              ⟨actual.multifill [name] [value], ?_,
                                hWrittenRel,
                                hRel.multifill_sharedState [name] [value]⟩
                            have hFuelEq : fuel = (fuel - 1) + 1 := by
                              simp only [stmtFuel] at hFuel
                              omega
                            rw [hFuelEq,
                              Yul.InteractionSemantics.Exec.assign_one_succ
                                (fuel - 1) name yulValue code actual hCheck,
                              hValueRun]
                            rfl
    | ifThen condition body =>
        simp only [stmtFuel] at hFuel
        simp only [Elab.ClzHelperExecution.execStmt?] at hExec
        cases hConditionEval : Elab.ClzHelperExecution.evalExpr?
            argName returnName model condition with
        | none => simp [hConditionEval] at hExec
        | some conditionValue =>
            simp only [Frontend.Stmt.toYul?] at hYul
            cases hConditionYul : Frontend.Expr.toYul? condition with
            | none => simp [hConditionYul] at hYul
            | some yulCondition =>
                cases hBodyYul : Frontend.Stmt.List.toYul? body with
                | none => simp [hConditionYul, hBodyYul] at hYul
                | some yulBody =>
                    simp [hConditionYul, hBodyYul] at hYul
                    subst yulStmt
                    have hConditionRun := evalExpr_of_model hRel
                      hConditionEval hConditionYul code (fuel - 1) (by omega)
                    have hConditionEvalRun :
                        Yul.InteractionSemantics.eval (fuel - 1)
                            yulCondition code actual =
                          .done (.ok (actual, conditionValue)) := by
                      rw [Yul.InteractionSemantics.eval_eq_bind,
                        hConditionRun]
                      rfl
                    have hFuelEq : fuel = (fuel - 1) + 1 := by omega
                    by_cases hTruthy :
                        Elab.ClzHelperExecution.truthy conditionValue
                    · simp [hConditionEval, hTruthy] at hExec
                      cases hBodyExec : Elab.ClzHelperExecution.execStmts?
                          argName returnName model body with
                      | none => simp [hBodyExec] at hExec
                      | some bodyModel =>
                          simp [hBodyExec] at hExec
                          subst finalModel
                          have hBodyRun := execStmts_of_model hRel hNames
                            hBodyExec hBodyYul code (fuel - 2) (by omega)
                          rcases hBodyRun with
                            ⟨afterBody, hAfterBody, hAfterRel, hAfterShared⟩
                          have hConditionNe :
                              conditionValue ≠ EvmYul.UInt256.ofNat 0 := by
                            exact (truthy_eq_true_iff conditionValue).mp
                              hTruthy
                          refine
                            ⟨afterBody.restrictStoreTo actual.store, ?_,
                              hRel.restrict_to_entry hAfterRel,
                              (hAfterRel.restrictStoreTo_sharedState
                                actual.store).trans hAfterShared⟩
                          rw [hFuelEq,
                            Yul.InteractionSemantics.Exec.if_succ,
                            hConditionEvalRun]
                          simp [Simulation.Interaction.bind, hConditionNe]
                          have hBlockFuelEq :
                              fuel - 1 = (fuel - 2) + 1 := by omega
                          rw [hBlockFuelEq,
                            Yul.InteractionSemantics.Exec.block_succ,
                            hAfterBody]
                          rfl
                    · simp [hConditionEval, hTruthy] at hExec
                      subst finalModel
                      have hConditionEq :
                          conditionValue = EvmYul.UInt256.ofNat 0 := by
                        by_contra hNe
                        exact hTruthy
                          ((truthy_eq_true_iff conditionValue).mpr hNe)
                      refine ⟨actual, ?_, hRel, rfl⟩
                      rw [hFuelEq, Yul.InteractionSemantics.Exec.if_succ,
                        hConditionEvalRun]
                      simp [Simulation.Interaction.instMonad,
                        Simulation.Interaction.bind, hConditionEq]
                      rfl
    | letDecl names value =>
        simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | exprStmt expr =>
        simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | functionDef name params returns body =>
        simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | switch condition cases defaultBody =>
        simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | forLoop pre condition post body =>
        simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | «break» => simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | «continue» => simp [Elab.ClzHelperExecution.execStmt?] at hExec
    | «leave» => simp [Elab.ClzHelperExecution.execStmt?] at hExec
  termination_by stmtFuel stmt
  decreasing_by
    all_goals subst_vars
    all_goals simp only [stmtFuel]
    all_goals omega

  theorem execStmts_of_model
      {argName returnName : Name} {model finalModel : ModelState}
      {actual : State} {stmts : List Frontend.Stmt}
      {yulStmts : List EvmYul.Yul.Ast.Stmt}
      (hRel : StateRel argName returnName model actual)
      (hNames : argName ≠ returnName)
      (hExec :
        Elab.ClzHelperExecution.execStmts? argName returnName model stmts =
          some finalModel)
      (hYul : Frontend.Stmt.List.toYul? stmts = some yulStmts)
      (code : Option EvmYul.Yul.Ast.YulContract) (fuel : Nat)
      (hFuel : stmtListFuel stmts ≤ fuel) :
      ∃ finalActual,
        Yul.InteractionSemantics.execSeq fuel yulStmts code actual =
          .done (.ok finalActual) ∧
        StateRel argName returnName finalModel finalActual ∧
        finalActual.sharedState = actual.sharedState := by
    cases stmts with
    | nil =>
        simp [Elab.ClzHelperExecution.execStmts?] at hExec
        subst finalModel
        simp [Frontend.Stmt.List.toYul?] at hYul
        subst yulStmts
        cases fuel with
        | zero => simp [stmtListFuel] at hFuel
        | succ previous =>
            exact
              ⟨actual,
                Yul.InteractionSemantics.ExecSeq.nil_succ previous code actual,
                hRel, rfl⟩
    | cons head rest =>
        simp only [stmtListFuel] at hFuel
        simp only [Elab.ClzHelperExecution.execStmts?] at hExec
        cases hHeadExec : Elab.ClzHelperExecution.execStmt?
            argName returnName model head with
        | none => simp [hHeadExec] at hExec
        | some midModel =>
            cases hRestExec : Elab.ClzHelperExecution.execStmts?
                argName returnName midModel rest with
            | none => simp [hHeadExec, hRestExec] at hExec
            | some restModel =>
                simp [hHeadExec, hRestExec] at hExec
                subst finalModel
                simp only [Frontend.Stmt.List.toYul?] at hYul
                cases hHeadYul : Frontend.Stmt.toYul? head with
                | none => simp [hHeadYul] at hYul
                | some yulHead =>
                    cases hRestYul : Frontend.Stmt.List.toYul? rest with
                    | none => simp [hHeadYul, hRestYul] at hYul
                    | some yulRest =>
                        simp [hHeadYul, hRestYul] at hYul
                        subst yulStmts
                        have hHeadRun := execStmt_of_model hRel hNames
                          hHeadExec hHeadYul code (fuel - 1) (by omega)
                        rcases hHeadRun with
                          ⟨midActual, hMidRun, hMidRel, hMidShared⟩
                        have hRestRun := execStmts_of_model hMidRel hNames
                          hRestExec hRestYul code (fuel - 1) (by omega)
                        rcases hRestRun with
                          ⟨finalActual, hFinalRun, hFinalRel, hFinalShared⟩
                        refine
                          ⟨finalActual, ?_, hFinalRel,
                            hFinalShared.trans hMidShared⟩
                        have hFuelEq : fuel = (fuel - 1) + 1 := by omega
                        rw [hFuelEq,
                          Yul.InteractionSemantics.ExecSeq.cons_succ,
                          hMidRun]
                        rcases hMidRel.regular with ⟨shared, store, rfl⟩
                        exact hFinalRun
  termination_by stmtListFuel stmts
  decreasing_by
    all_goals subst_vars
    all_goals simp only [stmtListFuel]
    all_goals omega
end

theorem clzHelperBody_exec
    (argName returnName : Name) (hNames : argName ≠ returnName)
    (shared : EvmYul.SharedState .Yul) (callerStore : EvmYul.Yul.VarStore)
    (value : Frontend.Word)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat)
    (hFuel :
      stmtListFuel (Elab.clzHelperBody argName returnName) ≤ fuel) :
    ∃ yulBody finalActual,
      Frontend.Stmt.List.toYul?
          (Elab.clzHelperBody argName returnName) = some yulBody ∧
        Yul.InteractionSemantics.execSeq
            fuel yulBody code
            (EvmYul.Yul.State.mkOk
              ((.Ok shared callerStore : State).initcall
                [argName] [returnName] [value])) =
          .done (.ok finalActual) ∧
        finalActual.lookup? returnName =
            some (Elab.ClzHelperModel.run value) ∧
          ∃ finalStore, finalActual = .Ok shared finalStore := by
  rcases Elab.clzHelperFunctionDef_toYul?_some argName returnName with
    ⟨yulBody, hFunctionYul⟩
  unfold Elab.clzHelperFunctionDef Frontend.FunctionDef.toYul? at hFunctionYul
  cases hBodyYul : Frontend.Stmt.List.toYul?
      (Elab.clzHelperBody argName returnName) with
  | none => simp [hBodyYul] at hFunctionYul
  | some convertedBody =>
      simp [hBodyYul] at hFunctionYul
      subst yulBody
      let initialModel : ModelState :=
        { arg := value, ret := Elab.ClzHelperModel.zero }
      let finalModel := Elab.ClzHelperExecution.expectedFinalState value
      have hModelRun :
          Elab.ClzHelperExecution.execStmts? argName returnName
              initialModel (Elab.clzHelperBody argName returnName) =
            some finalModel := by
        exact Elab.ClzHelperExecution.exec_clzHelperBody_eq_expectedFinalState
          argName returnName hNames value Elab.ClzHelperModel.zero
      have hInitialRel :
          StateRel argName returnName initialModel
            (EvmYul.Yul.State.mkOk
              ((.Ok shared callerStore : State).initcall
                [argName] [returnName] [value])) := by
        exact StateRel.initcall argName returnName hNames shared callerStore
          value
      rcases execStmts_of_model hInitialRel hNames hModelRun hBodyYul code
          fuel hFuel with
        ⟨finalActual, hActualRun, hFinalRel, hFinalShared⟩
      refine ⟨convertedBody, finalActual, rfl, hActualRun, ?_, ?_⟩
      · rw [hFinalRel.ret]
        exact congrArg some
          (Elab.ClzHelperExecution.expectedFinalState_ret_eq_run value)
      · rcases hFinalRel.regular with
          ⟨finalShared, finalStore, hFinalActual⟩
        refine ⟨finalStore, ?_⟩
        rw [hFinalActual] at hFinalShared ⊢
        simp only [EvmYul.Yul.State.sharedState] at hFinalShared
        subst finalShared
        rfl

theorem clzHelperCall
    {contract : EvmYul.Yul.Ast.YulContract}
    {helper argName returnName : Name}
    {yulBody : List EvmYul.Yul.Ast.Stmt}
    (hNames : argName ≠ returnName)
    (hLookup :
      contract.functions.lookup helper =
        some (.Def [argName] [returnName] yulBody))
    (hBodyYul :
      Frontend.Stmt.List.toYul?
          (Elab.clzHelperBody argName returnName) = some yulBody)
    (shared : EvmYul.SharedState .Yul) (callerStore : EvmYul.Yul.VarStore)
    (value : Frontend.Word) (fuel : Nat)
    (hFuel :
      stmtListFuel (Elab.clzHelperBody argName returnName) + 2 ≤ fuel) :
    Yul.InteractionSemantics.call
        fuel
        [value] (some helper) (some contract) (.Ok shared callerStore) =
      .done
        (.ok
          ((.Ok shared callerStore : State),
            [Elab.ClzHelperModel.run value])) := by
  rcases clzHelperBody_exec argName returnName hNames shared callerStore
      value (some contract) (fuel - 2) (by omega) with
    ⟨convertedBody, finalActual, hConverted, hExec, hRet,
      ⟨finalStore, hFinal⟩⟩
  rw [hBodyYul] at hConverted
  injection hConverted with hBodies
  subst convertedBody
  subst finalActual
  have hCallFuel : fuel = (fuel - 1) + 1 := by omega
  rw [hCallFuel,
    Yul.InteractionSemantics.Call.explicit_succ
      (fuel - 1)
      [value] helper contract [argName] [returnName] yulBody
      (.Ok shared callerStore) hLookup]
  have hBlockFuel : fuel - 1 = (fuel - 2) + 1 := by omega
  rw [hBlockFuel, Yul.InteractionSemantics.Exec.block_succ, hExec]
  let entryStore : EvmYul.Yul.VarStore :=
    ((default : EvmYul.Yul.VarStore).insert
      returnName Elab.ClzHelperModel.zero).insert argName value
  have hEntry :
      EvmYul.Yul.State.mkOk
          ((.Ok shared callerStore : State).initcall
            [argName] [returnName] [value]) =
        .Ok shared entryStore := by
    rfl
  have hEntryRet :
      Finmap.lookup returnName entryStore =
        some Elab.ClzHelperModel.zero := by
    simp [entryStore, Ne.symm hNames]
  have hRestrictedRet :
      Finmap.lookup returnName
          (EvmYul.Yul.State.restrictVarStore finalStore entryStore) =
        some (Elab.ClzHelperModel.run value) := by
    rw [Yul.VarStoreRestriction.lookup_restrict_of_some
      finalStore entryStore returnName hEntryRet]
    exact hRet
  rw [hEntry]
  simp only [Simulation.Interaction.instMonad]
  rw [Simulation.Interaction.bind_done_ok]
  unfold Simulation.Interaction.pure
  rw [Simulation.Interaction.bind_done_ok]
  simp [EvmYul.Yul.State.restrictStoreTo, EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.lookup?]
  change
    (Finmap.lookup returnName
      (EvmYul.Yul.State.restrictVarStore finalStore entryStore)).getD
        (EvmYul.UInt256.ofNat 0) = Elab.ClzHelperModel.run value
  rw [hRestrictedRet]
  rfl

end ClzPreservation
end Raw
end RawAst
end Solidity
end EvmCompiler
