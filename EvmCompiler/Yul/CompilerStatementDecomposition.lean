import EvmCompiler.Yul.Compiler
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul

/-!
Ordinary unchecked-compiler decompositions for individual Yul statements.

These equations expose the existing compiler to adjacent preservation proofs;
they do not define an alternate lowering.
-/

namespace Stmt

inductive SwitchDefaultLowering
    (fuel : Nat) (before : Fresh.State) :
    List AstStmt → Option Functions.Block → Fresh.State → Prop where
  | none :
      SwitchDefaultLowering fuel before [] none before
  | some
      {head : AstStmt} {tail : List AstStmt}
      {lower : Functions.Block} {after : Fresh.State}
      (lowering :
        List.toBlockUncheckedFuel? fuel before (head :: tail) =
          some (lower, after)) :
      SwitchDefaultLowering fuel before (head :: tail)
        (some lower) after

namespace SwitchDefaultLowering

theorem freshExtends
    {fuel : Nat} {before after : Fresh.State}
    {body : List AstStmt} {lower : Option Functions.Block}
    (hLower :
      SwitchDefaultLowering fuel before body lower after) :
    Fresh.Extends before after := by
  cases hLower with
  | none => exact Fresh.Extends.refl before
  | some lowering =>
      exact List.toBlockUncheckedFuel?_stateExtends lowering

end SwitchDefaultLowering

inductive SwitchSelectionLowering
    (start final : Fresh.State)
    (value : Word) (defaultBody : List AstStmt)
    (cases : List (Word × List AstStmt))
    (lowerCases : List (Word × Functions.Block))
    (lowerDefault : Option Functions.Block) : Prop where
  | none
      (source :
        EvmYul.Yul.selectSwitchCase value defaultBody cases = [])
      (target :
        Functions.Source.Switch.select value lowerCases lowerDefault = none)
      (freshExtends : Fresh.Extends start final) :
      SwitchSelectionLowering start final value defaultBody cases
        lowerCases lowerDefault
  | some
      {sourceBody : List AstStmt}
      {lowerBody : Functions.Block}
      {bodyFuel : Nat}
      {bodyBefore bodyAfter : Fresh.State}
      (source :
        EvmYul.Yul.selectSwitchCase value defaultBody cases = sourceBody)
      (target :
        Functions.Source.Switch.select value lowerCases lowerDefault =
          some lowerBody)
      (lowering :
        List.toBlockUncheckedFuel? bodyFuel bodyBefore sourceBody =
          some (lowerBody, bodyAfter))
      (beforeExtends : Fresh.Extends start bodyBefore)
      (afterExtends : Fresh.Extends bodyAfter final) :
      SwitchSelectionLowering start final value defaultBody cases
        lowerCases lowerDefault

namespace SwitchSelectionLowering

theorem freshExtends
    {start final : Fresh.State}
    {value : Word} {defaultBody : List AstStmt}
    {cases : List (Word × List AstStmt)}
    {lowerCases : List (Word × Functions.Block)}
    {lowerDefault : Option Functions.Block}
    (hSelection :
      SwitchSelectionLowering start final value defaultBody cases
        lowerCases lowerDefault) :
    Fresh.Extends start final := by
  cases hSelection with
  | none _ _ hFresh => exact hFresh
  | some _ _ hLower hBefore hAfter =>
      exact
        Fresh.Extends.trans hBefore
          (Fresh.Extends.trans
            (List.toBlockUncheckedFuel?_stateExtends hLower)
            hAfter)

end SwitchSelectionLowering

theorem toFunctionsListUncheckedFuel?_block_parts
    {fuel : Nat} {before after : Fresh.State}
    {body : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.Block body) =
        some (lower, after)) :
    ∃ previous lowerBody,
      fuel = previous + 1 ∧
      List.toBlockUncheckedFuel? previous before body =
        some (lowerBody, after) ∧
      lower = [.block lowerBody] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ previous =>
      cases hBody :
          List.toBlockUncheckedFuel? previous before body with
      | none =>
          simp [toFunctionsListUncheckedFuel?, hBody] at hLower
      | some result =>
          rcases result with ⟨lowerBody, final⟩
          simp [toFunctionsListUncheckedFuel?, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨previous, lowerBody, rfl, hBody, rfl⟩

theorem toFunctionsListUncheckedFuel?_block_of_toBlock
    {fuel : Nat} {before after : Fresh.State}
    {body : List AstStmt} {lowerBody : Functions.Block}
    (hLower :
      List.toBlockUncheckedFuel? fuel before body =
        some (lowerBody, after)) :
    toFunctionsListUncheckedFuel? (fuel + 1) before (.Block body) =
      some ([.block lowerBody], after) := by
  simp [toFunctionsListUncheckedFuel?, hLower]

theorem toFunctionsListUncheckedFuel?_if_parts
    {fuel : Nat} {before after : Fresh.State}
    {cond : AstExpr} {body : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.If cond body) =
        some (lower, after)) :
    ∃ previous preCond lowerCond middle lowerBody,
      fuel = previous + 1 ∧
      Expr.lower1Unchecked? before cond =
        some (preCond, lowerCond, middle) ∧
      List.toBlockUncheckedFuel? previous middle body =
        some (lowerBody, after) ∧
      lower = preCond ++ [.if_ lowerCond lowerBody] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ previous =>
      cases hCond : Expr.lower1Unchecked? before cond with
      | none =>
          simp [toFunctionsListUncheckedFuel?, hCond] at hLower
      | some condResult =>
          rcases condResult with ⟨preCond, lowerCond, middle⟩
          cases hBody :
              List.toBlockUncheckedFuel? previous middle body with
          | none =>
              simp [toFunctionsListUncheckedFuel?, hCond, hBody] at hLower
          | some bodyResult =>
              rcases bodyResult with ⟨lowerBody, final⟩
              simp [toFunctionsListUncheckedFuel?, hCond, hBody] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                ⟨previous, preCond, lowerCond, middle, lowerBody,
                  rfl, by simpa using hCond, by simpa using hBody, rfl⟩

theorem CaseList.toFunctionsUncheckedFuel?_nil_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List (Word × Functions.Block)}
    (hLower :
      CaseList.toFunctionsUncheckedFuel? fuel before [] =
        some (lower, after)) :
    lower = [] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [CaseList.toFunctionsUncheckedFuel?] at hLower
  | succ previous =>
      simp [CaseList.toFunctionsUncheckedFuel?] at hLower
      exact ⟨hLower.1, hLower.2.symm⟩

theorem CaseList.toFunctionsUncheckedFuel?_cons_parts
    {fuel : Nat} {before after : Fresh.State}
    {value : Word} {body : List AstStmt}
    {rest : List (Word × List AstStmt)}
    {lower : List (Word × Functions.Block)}
    (hLower :
      CaseList.toFunctionsUncheckedFuel? fuel before
          ((value, body) :: rest) =
        some (lower, after)) :
    ∃ previous lowerBody middle lowerRest,
      fuel = previous + 1 ∧
      List.toBlockUncheckedFuel? previous before body =
        some (lowerBody, middle) ∧
      CaseList.toFunctionsUncheckedFuel? previous middle rest =
        some (lowerRest, after) ∧
      lower = (value, lowerBody) :: lowerRest := by
  cases fuel with
  | zero =>
      simp [CaseList.toFunctionsUncheckedFuel?] at hLower
  | succ previous =>
      cases hBody :
          List.toBlockUncheckedFuel? previous before body with
      | none =>
          simp [CaseList.toFunctionsUncheckedFuel?, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨lowerBody, middle⟩
          cases hRest :
              CaseList.toFunctionsUncheckedFuel? previous middle rest with
          | none =>
              simp [CaseList.toFunctionsUncheckedFuel?, hBody, hRest]
                at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, final⟩
              simp [CaseList.toFunctionsUncheckedFuel?, hBody, hRest]
                at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                ⟨previous, lowerBody, middle, lowerRest,
                  rfl, hBody, hRest, rfl⟩

theorem SwitchSelectionLowering.of_compilers
    {caseFuel defaultFuel : Nat}
    {start afterCases final : Fresh.State}
    {value : Word} {defaultBody : List AstStmt}
    {cases : List (Word × List AstStmt)}
    {lowerCases : List (Word × Functions.Block)}
    {lowerDefault : Option Functions.Block}
    (hCases :
      CaseList.toFunctionsUncheckedFuel? caseFuel start cases =
        Option.some (lowerCases, afterCases))
    (hDefault :
      SwitchDefaultLowering defaultFuel afterCases defaultBody
        lowerDefault final) :
    SwitchSelectionLowering start final value defaultBody cases
      lowerCases lowerDefault := by
  induction cases generalizing caseFuel start lowerCases afterCases with
  | nil =>
      rcases
        CaseList.toFunctionsUncheckedFuel?_nil_parts hCases
        with ⟨rfl, rfl⟩
      cases hDefault with
      | none =>
          exact
            .none (by simp [EvmYul.Yul.selectSwitchCase])
              (by simp [Functions.Source.Switch.select])
              (Fresh.Extends.refl _)
      | some hLower =>
          exact
            .some (by simp [EvmYul.Yul.selectSwitchCase])
              (by simp [Functions.Source.Switch.select])
              hLower (Fresh.Extends.refl _)
              (Fresh.Extends.refl final)
  | cons head rest ih =>
      rcases head with ⟨caseValue, caseBody⟩
      obtain
          ⟨previous, lowerBody, middle, lowerRest,
            _hFuel, hBody, hRest, hLowerCases⟩ :=
        CaseList.toFunctionsUncheckedFuel?_cons_parts hCases
      subst lowerCases
      have hTail :=
        ih hRest hDefault
      by_cases hMatch : caseValue = value
      · exact
          .some
            (by simp [EvmYul.Yul.selectSwitchCase, hMatch])
            (by simp [Functions.Source.Switch.select, hMatch])
            hBody (Fresh.Extends.refl start)
            hTail.freshExtends
      · cases hTail with
        | none hSource hTarget hFresh =>
            exact
              .none
                (by
                  simp [EvmYul.Yul.selectSwitchCase, hMatch, hSource])
                (by
                  simp [Functions.Source.Switch.select, hMatch, hTarget])
                (Fresh.Extends.trans
                  (List.toBlockUncheckedFuel?_stateExtends hBody)
                  hFresh)
        | some hSource hTarget hSelected hPrefix hSuffix =>
            exact
              .some
                (by
                  simp [EvmYul.Yul.selectSwitchCase, hMatch, hSource])
                (by
                  simp [Functions.Source.Switch.select, hMatch, hTarget])
                hSelected
                (Fresh.Extends.trans
                  (List.toBlockUncheckedFuel?_stateExtends hBody)
                  hPrefix)
                hSuffix

theorem toFunctionsListUncheckedFuel?_switch_parts
    {fuel : Nat} {before after : Fresh.State}
    {scrutinee : AstExpr}
    {cases : List (Word × List AstStmt)}
    {defaultBody : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Switch scrutinee cases defaultBody) =
        some (lower, after)) :
    ∃ previous preScrutinee lowerScrutinee afterScrutinee
        lowerCases afterCases lowerDefault,
      fuel = previous + 1 ∧
      Expr.lower1Unchecked? before scrutinee =
        some (preScrutinee, lowerScrutinee, afterScrutinee) ∧
      CaseList.toFunctionsUncheckedFuel? previous afterScrutinee cases =
        some (lowerCases, afterCases) ∧
      SwitchDefaultLowering previous afterCases defaultBody
        lowerDefault after ∧
      lower =
        preScrutinee ++
          [.switch lowerScrutinee lowerCases lowerDefault] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ previous =>
      cases hScrutinee : Expr.lower1Unchecked? before scrutinee with
      | none =>
          simp [toFunctionsListUncheckedFuel?, hScrutinee] at hLower
      | some scrutineeResult =>
          rcases scrutineeResult with
            ⟨preScrutinee, lowerScrutinee, afterScrutinee⟩
          cases hCases :
              CaseList.toFunctionsUncheckedFuel?
                previous afterScrutinee cases with
          | none =>
              simp [toFunctionsListUncheckedFuel?, hScrutinee, hCases]
                at hLower
          | some casesResult =>
              rcases casesResult with ⟨lowerCases, afterCases⟩
              cases defaultBody with
              | nil =>
                  simp [toFunctionsListUncheckedFuel?,
                    hScrutinee, hCases] at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact
                    ⟨previous, preScrutinee, lowerScrutinee,
                      afterScrutinee, lowerCases, afterCases, none,
                      rfl, by simpa using hScrutinee, hCases,
                      SwitchDefaultLowering.none, rfl⟩
              | cons defaultHead defaultTail =>
                  cases hDefault :
                      List.toBlockUncheckedFuel? previous afterCases
                        (defaultHead :: defaultTail) with
                  | none =>
                      simp [toFunctionsListUncheckedFuel?,
                        hScrutinee, hCases, hDefault] at hLower
                  | some defaultResult =>
                      rcases defaultResult with ⟨lowerDefault, final⟩
                      simp [toFunctionsListUncheckedFuel?,
                        hScrutinee, hCases, hDefault] at hLower
                      rcases hLower with ⟨rfl, rfl⟩
                      exact
                        ⟨previous, preScrutinee, lowerScrutinee,
                          afterScrutinee, lowerCases, afterCases,
                          some lowerDefault, rfl,
                          by simpa using hScrutinee, hCases,
                          SwitchDefaultLowering.some hDefault, rfl⟩

theorem toFunctionsListUncheckedFuel?_for_parts
    {fuel : Nat} {before after : Fresh.State}
    {cond : AstExpr} {post body : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.For cond post body) =
        some (lower, after)) :
    ∃ previous preCond lowerCond afterCond lowerPost afterPost lowerBody,
      fuel = previous + 1 ∧
      Expr.lower1Unchecked? before cond =
        some (preCond, lowerCond, afterCond) ∧
      List.toBlockUncheckedFuel? previous afterCond post =
        some (lowerPost, afterPost) ∧
      List.toBlockUncheckedFuel? previous afterPost body =
        some (lowerBody, after) ∧
      lower =
        [.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
          lowerPost
          { stmts :=
              preCond ++
                .if_
                  (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                  { stmts := [.brk] } ::
                lowerBody.stmts }] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ previous =>
      cases hCond : Expr.lower1Unchecked? before cond with
      | none =>
          simp [toFunctionsListUncheckedFuel?, hCond] at hLower
      | some condResult =>
          rcases condResult with ⟨preCond, lowerCond, afterCond⟩
          cases hPost :
              List.toBlockUncheckedFuel? previous afterCond post with
          | none =>
              simp [toFunctionsListUncheckedFuel?, hCond, hPost] at hLower
          | some postResult =>
              rcases postResult with ⟨lowerPost, afterPost⟩
              cases hBody :
                  List.toBlockUncheckedFuel? previous afterPost body with
              | none =>
                  simp [toFunctionsListUncheckedFuel?, hCond, hPost, hBody]
                    at hLower
              | some bodyResult =>
                  rcases bodyResult with ⟨lowerBody, final⟩
                  simp [toFunctionsListUncheckedFuel?, hCond, hPost, hBody]
                    at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact
                    ⟨previous, preCond, lowerCond, afterCond, lowerPost,
                      afterPost, lowerBody, rfl, rfl, hPost, hBody, rfl⟩

theorem toFunctionsListUncheckedFuel?_let_none_parts
    {fuel : Nat} {before after : Fresh.State}
    {names : List EvmYul.Identifier}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.Let names none) =
        some (lower, after)) :
    lower = initNames (identNames names) ∧
      after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_leave_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before .Leave =
        some (lower, after)) :
    lower = [.leave] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_continue_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before .Continue =
        some (lower, after)) :
    lower = [.cont] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_break_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before .Break =
        some (lower, after)) :
    lower = [.brk] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_let_one_parts
    {fuel : Nat} {before after : Fresh.State}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Let [name] (some expr)) =
        some (lower, after)) :
    ∃ pre lowerValue,
      Expr.lower1Unchecked? before expr =
        some (pre, lowerValue, after) ∧
      lower =
        pre ++ [Functions.Stmt.let_ (identName name) lowerValue] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      rw [toFunctionsListUncheckedFuel?_let_one_noncall
        fuel before name expr hNotFunctionCall] at hLower
      cases hValue : Expr.lower1Unchecked? before expr with
      | none =>
          simp [hValue] at hLower
      | some result =>
          rcases result with ⟨pre, lowerValue, final⟩
          simp [hValue] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨pre, lowerValue, rfl, rfl⟩

theorem toFunctionsListUncheckedFuel?_assign_one_parts
    {fuel : Nat} {before after : Fresh.State}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Assign [name] expr) =
        some (lower, after)) :
    ∃ pre lowerValue,
      Expr.lower1Unchecked? before expr =
        some (pre, lowerValue, after) ∧
      lower =
        pre ++ [Functions.Stmt.assign (identName name) lowerValue] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      rw [toFunctionsListUncheckedFuel?_assign_one_noncall
        fuel before name expr hNotFunctionCall] at hLower
      cases hValue : Expr.lower1Unchecked? before expr with
      | none =>
          simp [hValue] at hLower
      | some result =>
          rcases result with ⟨pre, lowerValue, final⟩
          simp [hValue] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨pre, lowerValue, rfl, rfl⟩

theorem toFunctionsListUncheckedFuel?_expr_primitive_parts
    {fuel : Nat} {before after : Fresh.State}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {lower : List Functions.Stmt}
    (hNonterminal : Prim.terminal? prim = none)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.ExprStmtCall (.Call (.inl prim) args)) =
        some (lower, after)) :
    ∃ pre lowerExpr,
      Expr.lower0Unchecked? before (.Call (.inl prim) args) =
        some (pre, lowerExpr, after) ∧
      lower = pre ++ [Functions.Stmt.expr lowerExpr] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp only [toFunctionsListUncheckedFuel?] at hLower
      rw [hNonterminal] at hLower
      cases hExpr :
          Expr.lower0Unchecked? before (.Call (.inl prim) args) with
      | none =>
          simp [hExpr] at hLower
      | some result =>
          rcases result with ⟨pre, lowerExpr, final⟩
          simp [hExpr] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨pre, lowerExpr, rfl, rfl⟩

theorem toFunctionsListUncheckedFuel?_let_noncall_singleton
    {fuel : Nat} {before after : Fresh.State}
    {names : List EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Let names (some expr)) =
        some (lower, after)) :
    ∃ name, names = [name] := by
  cases fuel with
  | zero => cases hLower
  | succ fuel =>
      cases names with
      | nil =>
          cases expr with
          | Lit value => cases hLower
          | Var name => cases hLower
          | Call callee args =>
              cases callee with
              | inl prim => cases hLower
              | inr functionName =>
                  exact (hNotFunctionCall functionName args rfl).elim
      | cons name rest =>
          cases rest with
          | nil => exact ⟨name, rfl⟩
          | cons next rest =>
              cases expr with
              | Lit value => cases hLower
              | Var varName => cases hLower
              | Call callee args =>
                  cases callee with
                  | inl prim => cases hLower
                  | inr functionName =>
                      exact (hNotFunctionCall functionName args rfl).elim

theorem toFunctionsListUncheckedFuel?_assign_noncall_singleton
    {fuel : Nat} {before after : Fresh.State}
    {names : List EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.Assign names expr) =
        some (lower, after)) :
    ∃ name, names = [name] := by
  cases fuel with
  | zero => cases hLower
  | succ fuel =>
      cases names with
      | nil =>
          cases expr with
          | Lit value => cases hLower
          | Var name => cases hLower
          | Call callee args =>
              cases callee with
              | inl prim => cases hLower
              | inr functionName =>
                  exact (hNotFunctionCall functionName args rfl).elim
      | cons name rest =>
          cases rest with
          | nil => exact ⟨name, rfl⟩
          | cons next rest =>
              cases expr with
              | Lit value => cases hLower
              | Var varName => cases hLower
              | Call callee args =>
                  cases callee with
                  | inl prim => cases hLower
                  | inr functionName =>
                      exact (hNotFunctionCall functionName args rfl).elim

end Stmt
end Yul
end EvmCompiler
