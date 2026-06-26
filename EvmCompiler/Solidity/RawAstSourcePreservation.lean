import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.RawAstClzPreservation
import EvmCompiler.Solidity.RawAstClzAllocation
import EvmCompiler.Solidity.RawAstSourceSemantics
import EvmCompiler.Yul.EndToEnd
import EvmCompiler.Yul.FunctionsInteractionPrimitive

/-!
Semantic interface for preserving accepted raw solc Yul to ordered Yul.

This file intentionally contains the relation shape, not the final source
theorem.  The remaining proof work should discharge `ObjectPreserved` from
`decodeAndElaborateSolcIr?` success and the checked frontend validation facts,
then compose it with `RawAstEndToEnd`.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace Raw
namespace SourcePreservation

abbrev State := Yul.InteractionSemantics.State
abbrev Failure := Yul.InteractionSemantics.Failure
abbrev Open (α : Type) := Yul.InteractionSemantics.Open α

theorem classifyCall_objectBuiltin_mem
    {name : Name}
    (hClass : CallClass.classifyCall name = .objectBuiltin) :
    name ∈ CallClass.objectBuiltins := by
  unfold CallClass.classifyCall at hClass
  cases hPrimitive : Frontend.Primitive.ofName? name with
  | some op => simp [hPrimitive] at hClass
  | none =>
      simp [hPrimitive] at hClass
      by_cases hObject : name ∈ CallClass.objectBuiltins
      · exact hObject
      · cases hDialect : CallClass.unsupportedDialectBuiltin? name <;>
          simp [hObject, hDialect] at hClass

theorem rawObjectBuiltinNameArg_of_elaboration
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {elabState finalElabState : Elab.State} {name : Name}
    (hElab :
      (Elab.Expr.elaborate rawExpr).run elabState =
        .ok (front, finalElabState))
    (hName : Frontend.Expr.objectBuiltinNameArg? front = some name) :
    Raw.SourceSemantics.objectBuiltinNameArg? rawExpr = some name := by
  cases rawExpr with
  | literal literal =>
      cases literal with
      | number value =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
      | bool value =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
      | stringLit value =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
          subst name
          rfl
      | bytesLit bytes =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
          subst name
          rfl
  | identifier ident =>
      unfold Elab.Expr.elaborate at hElab
      cases hVisible :
          (Elab.requireIdentifierVisible ident "expression").run elabState with
      | error err => simp [hVisible] at hElab
      | ok visibleResult =>
          rcases visibleResult with ⟨_, visibleState⟩
          simp [hVisible] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
  | functionCall callee args =>
      by_cases hMemoryguard : callee = "memoryguard"
      · subst callee
        cases args with
        | nil =>
            simp [Elab.Expr.elaborate] at hElab
            unfold Elab.throw at hElab
            change
              (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
                .ok (front, finalElabState) at hElab
            cases hElab
        | cons arg rest =>
            cases rest with
            | nil =>
                unfold Elab.Expr.elaborate at hElab
                cases hArg : (Elab.Expr.elaborate arg).run elabState with
                | error err => simp [hArg] at hElab
                | ok argResult =>
                    rcases argResult with ⟨frontArg, argState⟩
                    simp [hArg] at hElab
                    rcases hElab with ⟨rfl, rfl⟩
                    simp [Frontend.Expr.objectBuiltinNameArg?] at hName
            | cons extra tail =>
                simp [Elab.Expr.elaborate] at hElab
                unfold Elab.throw at hElab
                change
                  (Except.error _ :
                    Except String (Frontend.Expr × Elab.State)) =
                    .ok (front, finalElabState) at hElab
                cases hElab
      · by_cases hClz : callee = "clz"
        · subst callee
          cases args with
          | nil =>
              simp [Elab.Expr.elaborate] at hElab
              unfold Elab.throw at hElab
              change
                (Except.error _ :
                  Except String (Frontend.Expr × Elab.State)) =
                  .ok (front, finalElabState) at hElab
              cases hElab
          | cons arg rest =>
              cases rest with
              | nil =>
                  unfold Elab.Expr.elaborate at hElab
                  cases hArg : (Elab.Expr.elaborate arg).run elabState with
                  | error err => simp [hArg] at hElab
                  | ok argResult =>
                      rcases argResult with ⟨frontArg, argState⟩
                      simp [hArg] at hElab
                      cases hHelper : Elab.ensureClzHelper.run argState with
                      | error err => simp [hHelper] at hElab
                      | ok helperResult =>
                          rcases helperResult with ⟨helper, helperState⟩
                          simp [hHelper] at hElab
                          rcases hElab with ⟨rfl, rfl⟩
                          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | cons extra tail =>
                  simp [Elab.Expr.elaborate] at hElab
                  unfold Elab.throw at hElab
                  change
                    (Except.error _ :
                      Except String (Frontend.Expr × Elab.State)) =
                      .ok (front, finalElabState) at hElab
                  cases hElab
        · unfold Elab.Expr.elaborate at hElab
          simp [StateT.run_bind] at hElab
          cases hArgs : (Elab.Expr.List.elaborate args).run elabState with
          | error err => simp [hArgs] at hElab
          | ok argsResult =>
              rcases argsResult with ⟨frontArgs, argsState⟩
              simp [hArgs] at hElab
              cases hKind : CallClass.classifyCall callee with
              | primitive =>
                  simp [hKind] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | objectBuiltin =>
                  simp [hKind] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | dialectBuiltin =>
                  simp [hKind] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | user =>
                  simp [hKind] at hElab
                  cases hResolve :
                      Elab.resolveFunctionIn callee argsState.functionScopes with
                  | none =>
                      simp [Elab.resolveFunction, hResolve] at hElab
                      unfold Elab.throw at hElab
                      change
                        (Except.error _ :
                          Except String (Frontend.Expr × Elab.State)) =
                          .ok (front, finalElabState) at hElab
                      cases hElab
                  | some generated =>
                      simp [Elab.resolveFunction, hResolve] at hElab
                      rcases hElab with ⟨rfl, rfl⟩
                      simp [Frontend.Expr.objectBuiltinNameArg?] at hName

theorem exprList_elaborate_length
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState)) :
    fronts.length = rawExprs.length := by
  induction rawExprs generalizing elabState finalElabState fronts with
  | nil =>
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rfl
  | cons rawHead rawTail ih =>
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              simp [ih hTail]

theorem stmtList_elaborate_length
    {rawStmts : List Raw.Stmt} {fronts : List Frontend.Stmt}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Stmt.List.elaborate rawStmts).run elabState =
        .ok (fronts, finalElabState)) :
    fronts.length = rawStmts.length := by
  induction rawStmts generalizing elabState finalElabState fronts with
  | nil =>
      simp [Elab.Stmt.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rfl
  | cons rawHead rawTail ih =>
      unfold Elab.Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Stmt.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Stmt.List.elaborate rawTail).run headState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              simp [ih hTail]

theorem stmtList_elaborateBlock_false_length
    {rawStmts : List Raw.Stmt} {fronts : List Frontend.Stmt}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Stmt.List.elaborateBlock rawStmts false).run elabState =
        .ok (fronts, finalElabState)) :
    fronts.length = rawStmts.length := by
  unfold Elab.Stmt.List.elaborateBlock at hElab
  simp [StateT.run_bind] at hElab
  cases hScope :
      (Elab.Stmt.List.localFunctionScope rawStmts).run elabState with
  | error err => simp [hScope] at hElab
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, scopeState⟩
      simp [hScope] at hElab
      cases hPush : (Elab.pushFunctionScope scope).run scopeState with
      | error err => simp [hPush] at hElab
      | ok pushResult =>
          rcases pushResult with ⟨_, pushedState⟩
          simp [hPush] at hElab
          cases hHoist :
              (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                pushedState with
          | error err => simp [hHoist] at hElab
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              simp [hHoist] at hElab
              cases hCode :
                  (Elab.Stmt.List.elaborate rawStmts).run hoistState with
              | error err => simp [hCode] at hElab
              | ok codeResult =>
                  rcases codeResult with ⟨frontCode, codeState⟩
                  simp [hCode] at hElab
                  cases hPop : Elab.popFunctionScope.run codeState with
                  | error err => simp [hPop] at hElab
                  | ok popResult =>
                      rcases popResult with ⟨_, poppedState⟩
                      simp [hPop] at hElab
                      rcases hElab with ⟨rfl, rfl⟩
                      exact stmtList_elaborate_length hCode

theorem exprList_elaborate_single_head
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate [rawExpr]).run elabState =
        .ok ([front], finalElabState)) :
    ∃ headState,
      (Elab.Expr.elaborate rawExpr).run elabState =
        .ok (front, headState) := by
  unfold Elab.Expr.List.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hHead : (Elab.Expr.elaborate rawExpr).run elabState with
  | error err => simp [hHead] at hElab
  | ok headResult =>
      rcases headResult with ⟨frontHead, headState⟩
      simp [hHead, Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨hFront, _hFinal⟩
      subst frontHead
      refine ⟨headState, ?_⟩
      rfl

theorem exprList_elaborate_cons_parts
    {rawHead : Raw.Expr} {rawTail : List Raw.Expr}
    {fronts : List Frontend.Expr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate (rawHead :: rawTail)).run elabState =
        .ok (fronts, finalElabState)) :
    ∃ frontHead frontTail headState,
      fronts = frontHead :: frontTail ∧
        (Elab.Expr.elaborate rawHead).run elabState =
          .ok (frontHead, headState) ∧
        (Elab.Expr.List.elaborate rawTail).run headState =
          .ok (frontTail, finalElabState) := by
  unfold Elab.Expr.List.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
  | error err => simp [hHead] at hElab
  | ok headResult =>
      rcases headResult with ⟨frontHead, headState⟩
      simp [hHead] at hElab
      cases hTail : (Elab.Expr.List.elaborate rawTail).run headState with
      | error err => simp [hTail] at hElab
      | ok tailResult =>
          rcases tailResult with ⟨frontTail, tailState⟩
          simp [hTail] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          exact
            ⟨frontHead, frontTail, headState, rfl,
              by simpa using hHead, by simpa using hTail⟩

theorem exprList_elaborate_three_parts
    {rawFirst rawSecond rawThird : Raw.Expr}
    {frontFirst frontSecond frontThird : Frontend.Expr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate [rawFirst, rawSecond, rawThird]).run
          elabState =
        .ok ([frontFirst, frontSecond, frontThird], finalElabState)) :
    ∃ firstState secondState,
      (Elab.Expr.elaborate rawFirst).run elabState =
          .ok (frontFirst, firstState) ∧
        (Elab.Expr.elaborate rawSecond).run firstState =
          .ok (frontSecond, secondState) ∧
        (Elab.Expr.elaborate rawThird).run secondState =
          .ok (frontThird, finalElabState) := by
  rcases exprList_elaborate_cons_parts hElab with
    ⟨actualFirst, frontTail, firstState,
      hFront, hFirst, hTail⟩
  simp at hFront
  rcases hFront with ⟨rfl, rfl⟩
  rcases exprList_elaborate_cons_parts hTail with
    ⟨actualSecond, frontLast, secondState,
      hTailFront, hSecond, hLast⟩
  simp at hTailFront
  rcases hTailFront with ⟨rfl, rfl⟩
  rcases exprList_elaborate_cons_parts hLast with
    ⟨actualThird, frontNil, thirdState,
      hLastFront, hThird, hNil⟩
  simp at hLastFront
  rcases hLastFront with ⟨rfl, rfl⟩
  simp [Elab.Expr.List.elaborate] at hNil
  change
    Except.ok ([], thirdState) =
      Except.ok ([], finalElabState) at hNil
  injection hNil with hState
  cases hState
  exact ⟨firstState, secondState, hFirst, hSecond, hThird⟩

theorem rawSingleObjectBuiltinNameArg_of_list_elaboration
    {rawArgs : List Raw.Expr} {frontArgs : List Frontend.Expr}
    {elabState finalElabState : Elab.State}
    {frontNameArg : Frontend.Expr} {dataName : Name}
    (hElab :
      (Elab.Expr.List.elaborate rawArgs).run elabState =
        .ok (frontArgs, finalElabState))
    (hFrontArgs : frontArgs = [frontNameArg])
    (hFrontName :
      Frontend.Expr.objectBuiltinNameArg? frontNameArg = some dataName) :
    ∃ rawNameArg,
      rawArgs = [rawNameArg] ∧
        Raw.SourceSemantics.objectBuiltinNameArg? rawNameArg = some dataName := by
  have hLengths := exprList_elaborate_length hElab
  rw [hFrontArgs] at hLengths hElab
  have hRawLength : rawArgs.length = 1 := by simpa using hLengths.symm
  rw [List.length_eq_one_iff] at hRawLength
  rcases hRawLength with ⟨rawNameArg, rfl⟩
  rcases exprList_elaborate_single_head hElab with
    ⟨nameState, hNameElab⟩
  exact
    ⟨rawNameArg, rfl,
      rawObjectBuiltinNameArg_of_elaboration hNameElab hFrontName⟩

theorem objectBuiltinCall_elaboration_parts
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr}
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .objectBuiltin)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState)) :
    ∃ frontArgs argsState,
      (Elab.Expr.List.elaborate rawArgs).run elabState =
          .ok (frontArgs, argsState) ∧
        front = .call .objectBuiltin name frontArgs ∧
        finalElabState = argsState := by
  unfold Elab.Expr.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      exact ⟨frontArgs, argsState, by rfl, rfl, rfl⟩

theorem functionCall_elaboration_kind_parts
    {name : Name} {rawArgs : List Raw.Expr}
    {kind : Frontend.CallKind}
    {state finalState : Elab.State}
    {front : Frontend.Expr}
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = kind)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run state =
        .ok (front, finalState)) :
    ∃ callee frontArgs,
      front = .call kind callee frontArgs := by
  unfold Elab.Expr.elaborate at hElab
  simp [hNotMemoryguard, hNotClz, StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run state with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      cases kind with
      | primitive =>
          rcases hElab with ⟨rfl, rfl⟩
          exact ⟨name, frontArgs, rfl⟩
      | objectBuiltin =>
          rcases hElab with ⟨rfl, rfl⟩
          exact ⟨name, frontArgs, rfl⟩
      | dialectBuiltin =>
          rcases hElab with ⟨rfl, rfl⟩
          exact ⟨name, frontArgs, rfl⟩
      | user =>
          cases hResolve :
              Elab.resolveFunctionIn name argsState.functionScopes with
          | none =>
              simp [Elab.resolveFunction, StateT.run_bind,
                StateT.run_get, hResolve] at hElab
              unfold Elab.throw at hElab
              change
                (Except.error _ :
                  Except String (Frontend.Expr × Elab.State)) =
                    .ok (front, finalState) at hElab
              cases hElab
          | some generated =>
              simp [Elab.resolveFunction, hResolve] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              exact ⟨generated, frontArgs, rfl⟩

theorem switchCaseValue_elaboration_word
    {rawValue : Raw.SwitchCaseValue}
    {frontValue : Frontend.SwitchCaseValue}
    {word : Frontend.Word}
    (hElab :
      Elab.SwitchCaseValue.elaborate rawValue = .ok frontValue)
    (hWord : frontValue.toWord? = some word) :
    Raw.SourceSemantics.switchCaseValueWord? rawValue = some word := by
  cases rawValue with
  | literal literal =>
      cases literal with
      | number value =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord
      | bool value =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord
      | stringLit value =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord
      | bytesLit bytes =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord

theorem memoryguard_elaboration_parts
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr}
    (hElab :
      (Elab.Expr.elaborate (.functionCall "memoryguard" rawArgs)).run
        elabState = .ok (front, finalElabState)) :
    ∃ rawValue frontValue valueState,
      rawArgs = [rawValue] ∧
        front = .call .objectBuiltin "memoryguard" [frontValue] ∧
        (Elab.Expr.elaborate rawValue).run elabState =
          .ok (frontValue, valueState) ∧
        finalElabState = valueState := by
  cases rawArgs with
  | nil =>
      simp [Elab.Expr.elaborate] at hElab
      unfold Elab.throw at hElab
      change
        (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
          .ok (front, finalElabState) at hElab
      cases hElab
  | cons rawValue rest =>
      cases rest with
      | nil =>
          unfold Elab.Expr.elaborate at hElab
          cases hValue : (Elab.Expr.elaborate rawValue).run elabState with
          | error err => simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              simp [hValue] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              exact ⟨rawValue, frontValue, valueState, rfl, rfl, hValue, rfl⟩
      | cons extra tail =>
          simp [Elab.Expr.elaborate] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab

theorem clz_elaboration_parts
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr}
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run
        elabState = .ok (front, finalElabState)) :
    ∃ rawArg frontArg argState helper helperState,
      rawArgs = [rawArg] ∧
        (Elab.Expr.elaborate rawArg).run elabState =
          .ok (frontArg, argState) ∧
        Elab.ensureClzHelper.run argState = .ok (helper, helperState) ∧
        front = .call .user helper [frontArg] ∧
        finalElabState = helperState := by
  cases rawArgs with
  | nil =>
      simp [Elab.Expr.elaborate] at hElab
      unfold Elab.throw at hElab
      change
        (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
          .ok (front, finalElabState) at hElab
      cases hElab
  | cons rawArg rest =>
      cases rest with
      | nil =>
          unfold Elab.Expr.elaborate at hElab
          cases hArg : (Elab.Expr.elaborate rawArg).run elabState with
          | error err => simp [hArg] at hElab
          | ok argResult =>
              rcases argResult with ⟨frontArg, argState⟩
              simp [hArg] at hElab
              cases hHelper : Elab.ensureClzHelper.run argState with
              | error err => simp [hHelper] at hElab
              | ok helperResult =>
                  rcases helperResult with ⟨helper, helperState⟩
                  simp [hHelper] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  exact
                    ⟨rawArg, frontArg, argState, helper, helperState,
                      rfl, hArg, hHelper, rfl, rfl⟩
      | cons extra tail =>
          simp [Elab.Expr.elaborate] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab

def SameDoneRel {α : Type} :
    Except Failure α → Except Failure α → Prop :=
  Eq

/-- At the dispatcher-sequence boundary the ordered side has already executed
the dispatcher lexical block, while the raw side is still immediately before
its enclosing block restriction. Errors agree exactly; successful ordered
states are the raw state restricted to the common block-entry store. -/
def PendingBlockDoneRel (entryStore : EvmYul.Yul.VarStore) :
    Except Failure State → Except Failure State → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun raw ordered => ordered = raw.restrictStoreTo entryStore)

/-- Intermediate statement-list outcomes inside one lexical block. Most
statements preserve exact state; administrative empty-block stubs may apply the
block-entry restriction early on abrupt states. The enclosing block erases
that distinction. -/
def BlockSeqDoneRel (entryStore : EvmYul.Yul.VarStore) :
    Except Failure State → Except Failure State → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun raw ordered =>
      match raw with
      | .Ok _ _ => ordered = raw
      | .OutOfFuel | .Checkpoint _ =>
          ordered = raw ∨ ordered = raw.restrictStoreTo entryStore)

/-- A recursive sequence may reuse its enclosing block entry store after a
regular prefix. On an abrupt initial state, that store must be the state's own
entry store so an administrative empty block is related correctly. -/
def BlockEntryCompatible (entryStore : EvmYul.Yul.VarStore) : State → Prop
  | .Ok _ _ => True
  | state => state.store = entryStore

theorem forward_refl {α : Type}
    (truncated : Failure → Prop)
    (run : Open α) :
    Simulation.Interaction.ForwardRel truncated SameDoneRel run run := by
  induction run with
  | done result =>
      exact .done rfl
  | request query resume ih =>
      exact .request ih

def rawObjectRun (fuel : Nat) (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (state : State) : Open State :=
  Raw.SourceSemantics.execObjectCode fuel
    (Raw.SourceSemantics.contextForObject context) object state

def orderedRun (fuel : Nat) (ordered : Yul.OrderedProgram)
    (state : State) : Open State :=
  Yul.InteractionSemantics.exec fuel
    (.Block [ordered.program.contract.dispatcher])
    (some ordered.program.contract) state

def BlockRunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.execBlock rawFuel
      (Raw.SourceSemantics.contextForObject context) code state)
    (orderedRun orderedFuel ordered state)

/-- Exact preservation for raw multi-value expression evaluation before any
enclosing statement applies declaration/assignment writeback. -/
def ExprValuesRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawExpr : Raw.Expr) (orderedExpr : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.evalValues rawFuel context rawExpr state)
    (Yul.InteractionSemantics.evalValues orderedFuel orderedExpr
      (some contract) state)

/-- Exact preservation for scalar expression evaluation. -/
def ExprRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawExpr : Raw.Expr) (orderedExpr : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.eval rawFuel context rawExpr state)
    (Yul.InteractionSemantics.eval orderedFuel orderedExpr
      (some contract) state)

/-- Exact preservation for left-to-right argument-list evaluation. Call sites
pass reversed source lists on both sides, matching canonical Yul semantics. -/
def ArgsRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawArgs : List Raw.Expr) (orderedArgs : List Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.evalArgs rawFuel context rawArgs state)
    (Yul.InteractionSemantics.evalArgs orderedFuel orderedArgs
      (some contract) state)

/-- Primitive evaluation at potentially different source/target meta-fuels.
The recursive frontend proof derives this locally; equal fuels use
`forward_refl`, while widened target fuel needs a primitive-family lemma. -/
def PrimitiveRunForward (rawFuel orderedFuel : Nat)
    (state : State) (op : EvmYul.Operation .Yul)
    (args : List Frontend.Word) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
    (Yul.InteractionSemantics.primitiveSemantics.eval
      rawFuel state op args)
    (Yul.InteractionSemantics.primitiveSemantics.eval
      orderedFuel state op args)

theorem primitiveOpenEval_succ_succ_eq
    (left right : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval (left + 2) state op args =
      Yul.InteractionSemantics.Primitive.openEval (right + 2) state op args := by
  cases op <;> rename_i inner <;> cases inner <;>
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      EvmYul.Yul.primCall]

theorem primitiveOpenEval_one_eq_or_truncated
    (right : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval 1 state op args =
        Yul.InteractionSemantics.Primitive.openEval (right + 2) state op args ∨
      ∃ failure,
        Yul.InteractionSemantics.Primitive.openEval 1 state op args =
            .done (.error failure) ∧
          Yul.FunctionsInteractionPrimitive.Truncated failure := by
  cases op <;> rename_i inner <;> cases inner <;>
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.FunctionsInteractionPrimitive.Truncated,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      EvmYul.Yul.primCall]

/-- Widening only the target primitive fuel preserves every source run. At
fuel zero, and at the one-fuel `EXTCODEHASH` edge, source exhaustion is the
declared truncation relation; all other positive runs are definitionally
fuel-insensitive after the primitive dispatcher is classified. -/
theorem primitiveRunForward_slack
    (rawFuel slack : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Frontend.Word) :
    PrimitiveRunForward rawFuel (rawFuel + slack) state op args := by
  unfold PrimitiveRunForward
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Yul.InteractionSemantics.Primitive.openEval rawFuel state op args)
      (Yul.InteractionSemantics.Primitive.openEval
        (rawFuel + slack) state op args)
  cases rawFuel with
  | zero =>
      simp only [Yul.InteractionSemantics.Primitive.openEval]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
  | succ predecessor =>
      cases predecessor with
      | zero =>
          cases slack with
          | zero =>
              simpa using
                (forward_refl Yul.FunctionsInteractionPrimitive.Truncated
                  (Yul.InteractionSemantics.Primitive.openEval
                    1 state op args))
          | succ extra =>
              rcases primitiveOpenEval_one_eq_or_truncated
                  extra state op args with hEq | hTruncated
              · rw [show 1 + (extra + 1) = extra + 2 by omega]
                rw [hEq]
                exact
                  forward_refl Yul.FunctionsInteractionPrimitive.Truncated _
              · rcases hTruncated with ⟨failure, hRun, hFailure⟩
                rw [show 1 + (extra + 1) = extra + 2 by omega]
                rw [hRun]
                exact
                  Simulation.Interaction.ForwardRel.truncated hFailure
      | succ residual =>
          have hEq :=
            primitiveOpenEval_succ_succ_eq
              residual (residual + slack) state op args
          rw [show residual + 1 + 1 = residual + 2 by omega]
          rw [show residual + 1 + 1 + slack =
            (residual + slack) + 2 by omega]
          rw [hEq]
          exact
            forward_refl Yul.FunctionsInteractionPrimitive.Truncated _

/-- Generic lexical-block preservation under an explicit raw function context
and active ordered contract. -/
def BlockCodeRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCode : List Raw.Stmt) (orderedCode : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.execBlock rawFuel context rawCode state)
    (Yul.InteractionSemantics.exec orderedFuel (.Block orderedCode)
      (some contract) state)

/-- Selection and recursive body preservation for a lowered switch. Successful
frontend elaboration will construct this relation from the raw/ordered case
lists, so statement simulation never receives a case-specific replay premise. -/
def SwitchCasesRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt))
    (rawDefault : List Raw.Stmt)
    (orderedCases : List (Frontend.Word × List Frontend.AstStmt))
    (orderedDefault : List Frontend.AstStmt)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (stateAfterCondition : State) (value : Frontend.Word),
    ∃ rawBody orderedBody,
      Raw.SourceSemantics.selectSwitchCase value rawDefault rawCases =
          some rawBody ∧
        EvmYul.Yul.selectSwitchCase value orderedDefault orderedCases =
          orderedBody ∧
        BlockCodeRunForward rawFuel orderedFuel
          context rawBody orderedBody contract stateAfterCondition

def LoopRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCondition : Raw.Expr) (rawPost rawBody : List Raw.Stmt)
    (orderedCondition : Frontend.AstExpr)
    (orderedPost orderedBody : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
    (Raw.SourceSemantics.loop rawFuel context
      rawCondition rawPost rawBody state)
    (Yul.InteractionSemantics.loop orderedFuel orderedCondition
      orderedPost orderedBody (some contract) state)

/-- Pointwise semantic correspondence for switch cases. Literal conversion and
body preservation are stored once per case; selection is proved generically
from this relation rather than replayed by each switch statement. -/
inductive SwitchCaseListRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (contract : Frontend.AstContract) :
    List (Raw.SwitchCaseValue × List Raw.Stmt) →
      List (Frontend.Word × List Frontend.AstStmt) → Prop where
  | nil : SwitchCaseListRunForward rawFuel orderedFuel context contract [] []
  | cons
      {rawValue : Raw.SwitchCaseValue} {rawBody : List Raw.Stmt}
      {rawRest : List (Raw.SwitchCaseValue × List Raw.Stmt)}
      {word : Frontend.Word} {orderedBody : List Frontend.AstStmt}
      {orderedRest : List (Frontend.Word × List Frontend.AstStmt)}
      (value :
        Raw.SourceSemantics.switchCaseValueWord? rawValue = some word)
      (body :
        ∀ state,
          BlockCodeRunForward rawFuel orderedFuel
            context rawBody orderedBody contract state)
      (rest :
        SwitchCaseListRunForward rawFuel orderedFuel context contract
          rawRest orderedRest) :
      SwitchCaseListRunForward rawFuel orderedFuel context contract
        ((rawValue, rawBody) :: rawRest)
        ((word, orderedBody) :: orderedRest)

theorem word_beq_eq_true_iff_eq (left right : Frontend.Word) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftValue =>
      cases right with
      | mk rightValue =>
          constructor
          · intro hEq
            have hValue : leftValue = rightValue := eq_of_beq hEq
            cases hValue
            rfl
          · intro hEq
            cases hEq
            change (leftValue == leftValue) = true
            exact BEq.rfl

theorem SwitchCaseListRunForward.select
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {orderedCases : List (Frontend.Word × List Frontend.AstStmt)}
    {rawDefault : List Raw.Stmt}
    {orderedDefault : List Frontend.AstStmt}
    {contract : Frontend.AstContract}
    (hCases :
      SwitchCaseListRunForward rawFuel orderedFuel context contract
        rawCases orderedCases)
    (hDefault :
      ∀ state,
        BlockCodeRunForward rawFuel orderedFuel
          context rawDefault orderedDefault contract state) :
    SwitchCasesRunForward rawFuel orderedFuel context
      rawCases rawDefault orderedCases orderedDefault contract := by
  intro stateAfterCondition selectedValue
  induction hCases with
  | nil =>
      exact
        ⟨rawDefault, orderedDefault,
          by simp [Raw.SourceSemantics.selectSwitchCase],
          by simp [EvmYul.Yul.selectSwitchCase],
          hDefault stateAfterCondition⟩
  | @cons rawValue rawBody rawRest word orderedBody orderedRest
      hValue hBody hRest ih =>
      by_cases hSelected : selectedValue = word
      · have hBeq : (selectedValue == word) = true :=
          (word_beq_eq_true_iff_eq selectedValue word).mpr hSelected
        exact
          ⟨rawBody, orderedBody,
            by simp only [Raw.SourceSemantics.selectSwitchCase, hValue,
              hBeq, ↓reduceIte],
            by simp [EvmYul.Yul.selectSwitchCase, hSelected],
            hBody stateAfterCondition⟩
      · have hBeq : (selectedValue == word) = false :=
          Bool.eq_false_iff.mpr (fun h =>
            hSelected
              ((word_beq_eq_true_iff_eq selectedValue word).mp h))
        have hWordNe : word ≠ selectedValue := Ne.symm hSelected
        rcases ih with
          ⟨rawSelected, orderedSelected, hRaw, hOrdered, hRun⟩
        exact
          ⟨rawSelected, orderedSelected,
            by simpa [Raw.SourceSemantics.selectSwitchCase, hValue,
              hBeq] using hRaw,
            by simpa [EvmYul.Yul.selectSwitchCase, hWordNe] using hOrdered,
            hRun⟩

/-- Compiler-owned evidence that one elaborated expression survives object
builtin resolution and converts to the exact canonical ordered expression. -/
structure ExprNormalized (context : Frontend.ObjectBuiltinContext)
    (front : Frontend.Expr) (ordered : Frontend.AstExpr) where
  resolved : Frontend.Expr
  resolve : front.resolveObjectBuiltinsIn? context = some resolved
  toYul : resolved.toYul? = some ordered

structure ExprListNormalized (context : Frontend.ObjectBuiltinContext)
    (front : List Frontend.Expr) (ordered : List Frontend.AstExpr) where
  resolved : List Frontend.Expr
  resolve : Frontend.Expr.List.resolveObjectBuiltinsIn? front context =
    some resolved
  toYul : Frontend.Expr.List.toYul? resolved = some ordered

structure StmtNormalized (context : Frontend.ObjectBuiltinContext)
    (front : Frontend.Stmt) (ordered : Frontend.AstStmt) where
  resolved : Frontend.Stmt
  resolve : front.resolveObjectBuiltinsIn? context = some resolved
  toYul : resolved.toYul? = some ordered

structure StmtListNormalized (context : Frontend.ObjectBuiltinContext)
    (front : List Frontend.Stmt) (ordered : List Frontend.AstStmt) where
  resolved : List Frontend.Stmt
  resolve : Frontend.Stmt.List.resolveObjectBuiltinsIn? front context =
    some resolved
  toYul : Frontend.Stmt.List.toYul? resolved = some ordered

/-- Checked object-builtin resolution and canonical conversion for a switch
case list. Keeping this relation separate lets switch selection consume the
same recursively preserved block interface as ordinary lexical blocks. -/
structure CaseListNormalized (context : Frontend.ObjectBuiltinContext)
    (front : List (Frontend.SwitchCaseValue × List Frontend.Stmt))
    (ordered : List (Frontend.Word × List Frontend.AstStmt)) where
  resolved : List (Frontend.SwitchCaseValue × List Frontend.Stmt)
  resolve :
    Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? front context =
      some resolved
  toYul : Frontend.Stmt.CaseList.toYul? resolved = some ordered

def orderedImmutablePatchStmt
    (reference : Frontend.ImmutableReference)
    (base value : Frontend.AstExpr) : Frontend.AstStmt :=
  .ExprStmtCall
    (.Call (.inl .MSTORE)
      [.Call (.inl .ADD)
        [base, .Lit (EvmYul.UInt256.ofNat reference.start)], value])

def orderedImmutablePatchStmts
    (references : List Frontend.ImmutableReference)
    (base value : Frontend.AstExpr) : List Frontend.AstStmt :=
  references.map fun reference =>
    orderedImmutablePatchStmt reference base value

def orderedForStmt
    (pre : List Frontend.AstStmt) (condition : Frontend.AstExpr)
    (post body : List Frontend.AstStmt) : Frontend.AstStmt :=
  let loop : Frontend.AstStmt := .For condition post body
  match pre with
  | [] => loop
  | _ => .Block (pre ++ [loop])

namespace ExprListNormalized

def nil (context : Frontend.ObjectBuiltinContext) :
    ExprListNormalized context [] [] where
  resolved := []
  resolve := by simp [Frontend.Expr.List.resolveObjectBuiltinsIn?]
  toYul := rfl

theorem nil_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : List Frontend.AstExpr}
    (hNormalized : ExprListNormalized context [] ordered) :
    ordered = [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Expr.List.toYul?] using hToYul.symm

theorem cons_parts
    {context : Frontend.ObjectBuiltinContext}
    {frontHead : Frontend.Expr} {frontTail : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    (hNormalized :
      ExprListNormalized context (frontHead :: frontTail)
        ordered) :
    ∃ orderedHead orderedTail,
      ordered = orderedHead :: orderedTail ∧
        Nonempty (ExprNormalized context frontHead orderedHead) ∧
        Nonempty (ExprListNormalized context frontTail orderedTail) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.List.resolveObjectBuiltinsIn? at hResolve
  cases hHeadResolve :
      Frontend.Expr.resolveObjectBuiltinsIn? frontHead context with
  | none => simp [hHeadResolve] at hResolve
  | some resolvedHead =>
      cases hTailResolve :
          Frontend.Expr.List.resolveObjectBuiltinsIn? frontTail context with
      | none => simp [hHeadResolve, hTailResolve] at hResolve
      | some resolvedTail =>
          simp [hHeadResolve, hTailResolve] at hResolve
          subst resolved
          unfold Frontend.Expr.List.toYul? at hToYul
          cases hHeadToYul : Frontend.Expr.toYul? resolvedHead with
          | none => simp [hHeadToYul] at hToYul
          | some headYul =>
              cases hTailToYul :
                  Frontend.Expr.List.toYul? resolvedTail with
              | none => simp [hHeadToYul, hTailToYul] at hToYul
              | some tailYul =>
                  simp [hHeadToYul, hTailToYul] at hToYul
                  exact
                    ⟨headYul, tailYul, hToYul.symm,
                      ⟨{
                        resolved := resolvedHead
                        resolve := hHeadResolve
                        toYul := hHeadToYul }⟩,
                      ⟨{
                        resolved := resolvedTail
                        resolve := hTailResolve
                        toYul := hTailToYul }⟩⟩

end ExprListNormalized

namespace StmtListNormalized

def nil (context : Frontend.ObjectBuiltinContext) :
    StmtListNormalized context [] [] where
  resolved := []
  resolve := by simp [Frontend.Stmt.List.resolveObjectBuiltinsIn?]
  toYul := rfl

theorem nil_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : List Frontend.AstStmt}
    (hNormalized : StmtListNormalized context [] ordered) :
    ordered = [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.List.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.List.toYul?] using hToYul.symm

theorem cons_parts
    {context : Frontend.ObjectBuiltinContext}
    {frontHead : Frontend.Stmt} {frontTail : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    (hNormalized :
      StmtListNormalized context (frontHead :: frontTail)
        ordered) :
    ∃ orderedHead orderedTail,
      ordered = orderedHead :: orderedTail ∧
        Nonempty (StmtNormalized context frontHead orderedHead) ∧
        Nonempty (StmtListNormalized context frontTail orderedTail) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.List.resolveObjectBuiltinsIn? at hResolve
  cases hHeadResolve :
      Frontend.Stmt.resolveObjectBuiltinsIn? frontHead context with
  | none => simp [hHeadResolve] at hResolve
  | some resolvedHead =>
      cases hTailResolve :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? frontTail context with
      | none => simp [hHeadResolve, hTailResolve] at hResolve
      | some resolvedTail =>
          simp [hHeadResolve, hTailResolve] at hResolve
          subst resolved
          unfold Frontend.Stmt.List.toYul? at hToYul
          cases hHeadToYul : Frontend.Stmt.toYul? resolvedHead with
          | none => simp [hHeadToYul] at hToYul
          | some headYul =>
              cases hTailToYul :
                  Frontend.Stmt.List.toYul? resolvedTail with
              | none => simp [hHeadToYul, hTailToYul] at hToYul
              | some tailYul =>
                  simp [hHeadToYul, hTailToYul] at hToYul
                  exact
                    ⟨headYul, tailYul, hToYul.symm,
                      ⟨{
                        resolved := resolvedHead
                        resolve := hHeadResolve
                        toYul := hHeadToYul }⟩,
                      ⟨{
                        resolved := resolvedTail
                        resolve := hTailResolve
                        toYul := hTailToYul }⟩⟩

theorem length_eq
    {context : Frontend.ObjectBuiltinContext}
    {front : List Frontend.Stmt} {ordered : List Frontend.AstStmt}
    (hNormalized : StmtListNormalized context front ordered) :
    ordered.length = front.length := by
  induction front generalizing ordered with
  | nil =>
      rw [nil_ordered hNormalized]
      rfl
  | cons frontHead frontTail ih =>
      rcases cons_parts hNormalized with
        ⟨orderedHead, orderedTail, rfl, _hHead, ⟨hTail⟩⟩
      simp [ih hTail]

end StmtListNormalized

namespace CaseListNormalized

theorem nil_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : List (Frontend.Word × List Frontend.AstStmt)}
    (hNormalized : CaseListNormalized context [] ordered) :
    ordered = [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.CaseList.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.CaseList.toYul?] using hToYul.symm

theorem cons_parts
    {context : Frontend.ObjectBuiltinContext}
    {frontValue : Frontend.SwitchCaseValue}
    {frontBody : List Frontend.Stmt}
    {frontRest : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {ordered : List (Frontend.Word × List Frontend.AstStmt)}
    (hNormalized :
      CaseListNormalized context
        ((frontValue, frontBody) :: frontRest) ordered) :
    ∃ orderedValue orderedBody orderedRest,
      ordered = (orderedValue, orderedBody) :: orderedRest ∧
        frontValue.toWord? = some orderedValue ∧
        Nonempty (StmtListNormalized context frontBody orderedBody) ∧
        Nonempty (CaseListNormalized context frontRest orderedRest) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? at hResolve
  cases hBodyResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? frontBody context with
  | none => simp [hBodyResolve] at hResolve
  | some resolvedBody =>
      cases hRestResolve :
          Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? frontRest context with
      | none => simp [hBodyResolve, hRestResolve] at hResolve
      | some resolvedRest =>
          simp [hBodyResolve, hRestResolve] at hResolve
          subst resolved
          unfold Frontend.Stmt.CaseList.toYul? at hToYul
          cases hValue : frontValue.toWord? with
          | none => simp [hValue] at hToYul
          | some orderedValue =>
              cases hBodyToYul : Frontend.Stmt.List.toYul? resolvedBody with
              | none => simp [hValue, hBodyToYul] at hToYul
              | some orderedBody =>
                  cases hRestToYul :
                      Frontend.Stmt.CaseList.toYul? resolvedRest with
                  | none =>
                      simp [hValue, hBodyToYul, hRestToYul] at hToYul
                  | some orderedRest =>
                      simp [hValue, hBodyToYul, hRestToYul] at hToYul
                      exact
                        ⟨orderedValue, orderedBody, orderedRest,
                          hToYul.symm, by simpa using hValue,
                          ⟨{
                            resolved := resolvedBody
                            resolve := hBodyResolve
                            toYul := hBodyToYul }⟩,
                          ⟨{
                            resolved := resolvedRest
                            resolve := hRestResolve
                            toYul := hRestToYul }⟩⟩

end CaseListNormalized

theorem immutablePatchStmt_toYul_parts
    {reference : Frontend.ImmutableReference}
    {base value : Frontend.Expr}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hPatch : reference.patchStmt? base value = some front)
    (hToYul : front.toYul? = some ordered) :
    ∃ orderedBase orderedValue,
      base.toYul? = some orderedBase ∧
        value.toYul? = some orderedValue ∧
        ordered =
          orderedImmutablePatchStmt reference orderedBase orderedValue := by
  unfold Frontend.ImmutableReference.patchStmt? at hPatch
  split at hPatch
  next hPatchable =>
    simp at hPatch
    subst front
    cases hBase : base.toYul? with
    | none =>
        simp [Frontend.Stmt.toYul?, Frontend.Expr.toYul?,
          Frontend.Expr.List.toYul?, Frontend.Primitive.ofName?, hBase]
          at hToYul
    | some orderedBase =>
        cases hValue : value.toYul? with
        | none =>
            simp [Frontend.Stmt.toYul?, Frontend.Expr.toYul?,
              Frontend.Expr.List.toYul?, Frontend.Primitive.ofName?,
              hBase, hValue] at hToYul
        | some orderedValue =>
            simp [Frontend.Stmt.toYul?, Frontend.Expr.toYul?,
              Frontend.Expr.List.toYul?, Frontend.Primitive.ofName?,
              hBase, hValue, orderedImmutablePatchStmt] at hToYul
            exact
              ⟨orderedBase, orderedValue, by simpa using hBase,
                by simpa using hValue, hToYul.symm⟩
  next hNotPatchable => simp at hPatch

theorem immutablePatchStmts_toYul
    {references : List Frontend.ImmutableReference}
    {base value : Frontend.Expr}
    {front : List Frontend.Stmt}
    {orderedBase orderedValue : Frontend.AstExpr}
    (hPatch :
      Frontend.ImmutableReference.List.patchStmts?
        references base value = some front)
    (hBase : base.toYul? = some orderedBase)
    (hValue : value.toYul? = some orderedValue) :
    Frontend.Stmt.List.toYul? front =
      some (orderedImmutablePatchStmts
        references orderedBase orderedValue) := by
  induction references generalizing front with
  | nil =>
      simp [Frontend.ImmutableReference.List.patchStmts?] at hPatch
      subst front
      rfl
  | cons reference rest ih =>
      unfold Frontend.ImmutableReference.List.patchStmts? at hPatch
      cases hHead : reference.patchStmt? base value with
      | none => simp [hHead] at hPatch
      | some frontHead =>
          cases hTail :
              Frontend.ImmutableReference.List.patchStmts?
                rest base value with
          | none => simp [hHead, hTail] at hPatch
          | some frontTail =>
              simp [hHead, hTail] at hPatch
              subst front
              have hHeadToYul :
                  frontHead.toYul? =
                    some
                      (orderedImmutablePatchStmt
                        reference orderedBase orderedValue) := by
                unfold Frontend.ImmutableReference.patchStmt? at hHead
                split at hHead
                next hPatchable =>
                  simp at hHead
                  subst frontHead
                  simp [Frontend.Stmt.toYul?, Frontend.Expr.toYul?,
                    Frontend.Expr.List.toYul?, Frontend.Primitive.ofName?,
                    hBase, hValue, orderedImmutablePatchStmt]
                next hNotPatchable => simp at hHead
              simp [Frontend.Stmt.List.toYul?, hHeadToYul,
                ih hTail, orderedImmutablePatchStmts]

theorem immutablePatchStmts_toYul_parts
    {references : List Frontend.ImmutableReference}
    {base value : Frontend.Expr}
    {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    (hNonempty : references ≠ [])
    (hPatch :
      Frontend.ImmutableReference.List.patchStmts?
        references base value = some front)
    (hToYul : Frontend.Stmt.List.toYul? front = some ordered) :
    ∃ orderedBase orderedValue,
      base.toYul? = some orderedBase ∧
        value.toYul? = some orderedValue ∧
        ordered =
          orderedImmutablePatchStmts
            references orderedBase orderedValue := by
  cases references with
  | nil => exact False.elim (hNonempty rfl)
  | cons reference rest =>
      unfold Frontend.ImmutableReference.List.patchStmts? at hPatch
      cases hHead : reference.patchStmt? base value with
      | none => simp [hHead] at hPatch
      | some frontHead =>
          cases hTail :
              Frontend.ImmutableReference.List.patchStmts?
                rest base value with
          | none => simp [hHead, hTail] at hPatch
          | some frontTail =>
              have hWholePatch :
                  Frontend.ImmutableReference.List.patchStmts?
                      (reference :: rest) base value =
                    some (frontHead :: frontTail) := by
                simp [Frontend.ImmutableReference.List.patchStmts?,
                  hHead, hTail]
              simp [hHead, hTail] at hPatch
              subst front
              unfold Frontend.Stmt.List.toYul? at hToYul
              cases hHeadToYul : frontHead.toYul? with
              | none => simp [hHeadToYul] at hToYul
              | some orderedHead =>
                  cases hTailToYul :
                      Frontend.Stmt.List.toYul? frontTail with
                  | none => simp [hHeadToYul, hTailToYul] at hToYul
                  | some orderedTail =>
                      simp [hHeadToYul, hTailToYul] at hToYul
                      rcases
                          immutablePatchStmt_toYul_parts
                            hHead hHeadToYul with
                        ⟨orderedBase, orderedValue,
                          hBase, hValue, hOrderedHead⟩
                      have hAll :=
                        immutablePatchStmts_toYul hWholePatch hBase hValue
                      simp [Frontend.Stmt.List.toYul?, hHeadToYul,
                        hTailToYul] at hAll
                      exact
                        ⟨orderedBase, orderedValue, hBase, hValue,
                          hToYul.symm.trans hAll⟩

theorem rawImmutablePatchStmts_exists_of_frontend
    {references : List Frontend.ImmutableReference}
    {frontBase frontValue : Frontend.Expr}
    {frontStmts : List Frontend.Stmt}
    {rawBase rawValue : Raw.Expr}
    (hPatch :
      Frontend.ImmutableReference.List.patchStmts?
        references frontBase frontValue = some frontStmts) :
    ∃ rawStmts,
      Raw.SourceSemantics.patchSetImmutableStmts?
        references rawBase rawValue = some rawStmts := by
  induction references generalizing frontStmts with
  | nil => exact ⟨[], rfl⟩
  | cons reference rest ih =>
      unfold Frontend.ImmutableReference.List.patchStmts? at hPatch
      cases hHead : reference.patchStmt? frontBase frontValue with
      | none => simp [hHead] at hPatch
      | some frontHead =>
          cases hTail :
              Frontend.ImmutableReference.List.patchStmts?
                rest frontBase frontValue with
          | none => simp [hHead, hTail] at hPatch
          | some frontTail =>
              simp [hHead, hTail] at hPatch
              rcases ih hTail with ⟨rawTail, hRawTail⟩
              unfold Frontend.ImmutableReference.patchStmt? at hHead
              split at hHead
              next hPatchable =>
                refine
                  ⟨.expressionStatement
                      (.functionCall "mstore"
                        [ .functionCall "add"
                            [rawBase,
                              .literal
                                (.number
                                  (EvmYul.UInt256.ofNat reference.start))],
                          rawValue ]) :: rawTail,
                    ?_⟩
                simp [Raw.SourceSemantics.patchSetImmutableStmts?,
                  Raw.SourceSemantics.patchSetImmutableStmt?,
                  hPatchable, hRawTail]
              next hNotPatchable => simp at hHead

namespace ExprNormalized

theorem literal_parts
    {context : Frontend.ObjectBuiltinContext}
    {literal : Raw.Literal}
    {state finalState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    (hElab :
      (Elab.Expr.elaborate (.literal literal)).run state =
        .ok (front, finalState))
    (hNormalized : ExprNormalized context front ordered) :
    ∃ value,
      Raw.SourceSemantics.literalWord? literal = some value ∧
        ordered = .Lit value := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  cases literal with
  | number value =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
      subst ordered
      exact ⟨value, rfl, rfl⟩
  | bool value =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
      subst ordered
      exact ⟨EvmYul.UInt256.ofNat (if value then 1 else 0), rfl, rfl⟩
  | stringLit value =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      cases hWord : Frontend.StringLiteral.word? value with
      | none => simp [Frontend.Expr.toYul?, hWord] at hToYul
      | some word =>
          simp [Frontend.Expr.toYul?, hWord] at hToYul
          subst ordered
          exact ⟨word, by simp [Raw.SourceSemantics.literalWord?, hWord], rfl⟩
  | bytesLit bytes =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      cases hWord : Frontend.StringLiteral.wordBytes? bytes with
      | none => simp [Frontend.Expr.toYul?, hWord] at hToYul
      | some word =>
          simp [Frontend.Expr.toYul?, hWord] at hToYul
          subst ordered
          exact ⟨word, by simp [Raw.SourceSemantics.literalWord?, hWord], rfl⟩

theorem identifier_ordered
    {context : Frontend.ObjectBuiltinContext}
    {name : Name} {state finalState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    (hElab :
      (Elab.Expr.elaborate (.identifier name)).run state =
        .ok (front, finalState))
    (hNormalized : ExprNormalized context front ordered) :
    ordered = .Var name := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Elab.Expr.elaborate at hElab
  simp at hElab
  cases hVisible :
      (Elab.requireIdentifierVisible name "expression").run state with
  | error err => simp [hVisible] at hElab
  | ok result =>
      rcases result with ⟨_, visibleState⟩
      simp [hVisible] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hResolved : resolved = .var name := by
        unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
        exact Option.some.inj hResolve.symm
      subst resolved
      simpa [Frontend.Expr.toYul?] using hToYul.symm

theorem primitive_call_parts
    {context : Frontend.ObjectBuiltinContext}
    {callee : Name} {args : List Frontend.Expr}
    {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context (.call .primitive callee args) ordered) :
    ∃ op orderedArgs,
      Frontend.Primitive.ofName? callee = some op ∧
        ordered = .Call (.inl op) orderedArgs ∧
        Nonempty (ExprListNormalized context args orderedArgs) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      unfold Frontend.Expr.toYul? at hToYul
      cases hOp : Frontend.Primitive.ofName? callee with
      | none => simp [hOp] at hToYul
      | some op =>
          cases hArgsToYul : Frontend.Expr.List.toYul? resolvedArgs with
          | none => simp [hOp, hArgsToYul] at hToYul
          | some orderedArgs =>
              simp [hOp, hArgsToYul] at hToYul
              exact
                ⟨op, orderedArgs, rfl, hToYul.symm,
                  ⟨{
                    resolved := resolvedArgs
                    resolve := hArgsResolve
                    toYul := hArgsToYul }⟩⟩

theorem user_call_parts
    {context : Frontend.ObjectBuiltinContext}
    {callee : Name} {args : List Frontend.Expr}
    {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context (.call .user callee args) ordered) :
    ∃ orderedArgs,
      ordered = .Call (.inr callee) orderedArgs ∧
        Nonempty (ExprListNormalized context args orderedArgs) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      unfold Frontend.Expr.toYul? at hToYul
      cases hArgsToYul : Frontend.Expr.List.toYul? resolvedArgs with
      | none => simp [hArgsToYul] at hToYul
      | some orderedArgs =>
          simp [hArgsToYul] at hToYul
          exact
            ⟨orderedArgs, hToYul.symm,
              ⟨{
                resolved := resolvedArgs
                resolve := hArgsResolve
                toYul := hArgsToYul }⟩⟩

theorem dialect_call_false
    {context : Frontend.ObjectBuiltinContext}
    {callee : Name} {args : List Frontend.Expr}
    {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context (.call .dialectBuiltin callee args) ordered) :
    False := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul

theorem setimmutable_call_false
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "setimmutable" args) ordered) :
    False := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul

end ExprNormalized

namespace StmtNormalized

theorem setimmutable_args_eq_three
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context
        (.exprStmt (.call .objectBuiltin "setimmutable" args)) ordered) :
    ∃ base nameArg value, args = [base, nameArg, value] := by
  by_contra hNoThree
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  have hGenericResolve :
      Frontend.Stmt.resolveObjectBuiltinsIn?
          (.exprStmt (.call .objectBuiltin "setimmutable" args)) context =
        (Frontend.Expr.resolveObjectBuiltinsIn?
          (.call .objectBuiltin "setimmutable" args) context).bind
            (fun expr => some (.exprStmt expr)) := by
    cases args with
    | nil => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
    | cons base rest =>
        cases rest with
        | nil => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
        | cons nameArg rest =>
            cases rest with
            | nil => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
            | cons value rest =>
                cases rest with
                | nil => exact False.elim (hNoThree ⟨base, nameArg, value, rfl⟩)
                | cons extra tail =>
                    simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  rw [hGenericResolve] at hResolve
  cases hExprResolve :
      Frontend.Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "setimmutable" args) context with
  | none => simp [hExprResolve] at hResolve
  | some resolvedExpr =>
      simp [hExprResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hExprToYul : resolvedExpr.toYul? with
      | none => simp [hExprToYul] at hToYul
      | some orderedExpr =>
          exact False.elim
            (ExprNormalized.setimmutable_call_false
              { resolved := resolvedExpr
                resolve := hExprResolve
                toYul := hExprToYul })

theorem let_none_ordered
    {context : Frontend.ObjectBuiltinContext}
    {names : List Name} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.letDecl names none) ordered) :
    ordered = .Let names none := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem let_some_parts
    {context : Frontend.ObjectBuiltinContext}
    {names : List Name} {value : Frontend.Expr}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.letDecl names (some value)) ordered) :
    ∃ orderedValue,
      ordered = .Let names (some orderedValue) ∧
        Nonempty (ExprNormalized context value orderedValue) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hValueResolve : value.resolveObjectBuiltinsIn? context with
  | none => simp [hValueResolve] at hResolve
  | some resolvedValue =>
      simp [hValueResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hValueToYul : resolvedValue.toYul? with
      | none => simp [hValueToYul] at hToYul
      | some orderedValue =>
          simp [hValueToYul] at hToYul
          exact
            ⟨orderedValue, hToYul.symm,
              ⟨{
                resolved := resolvedValue
                resolve := hValueResolve
                toYul := hValueToYul }⟩⟩

theorem assign_parts
    {context : Frontend.ObjectBuiltinContext}
    {names : List Name} {value : Frontend.Expr}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.assign names value) ordered) :
    ∃ orderedValue,
      ordered = .Assign names orderedValue ∧
        Nonempty (ExprNormalized context value orderedValue) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hValueResolve : value.resolveObjectBuiltinsIn? context with
  | none => simp [hValueResolve] at hResolve
  | some resolvedValue =>
      simp [hValueResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hValueToYul : resolvedValue.toYul? with
      | none => simp [hValueToYul] at hToYul
      | some orderedValue =>
          simp [hValueToYul] at hToYul
          exact
            ⟨orderedValue, hToYul.symm,
              ⟨{
                resolved := resolvedValue
                resolve := hValueResolve
                toYul := hValueToYul }⟩⟩

theorem setimmutable_parts
    {context : Frontend.ObjectBuiltinContext}
    {base nameArg value : Frontend.Expr}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context
        (.exprStmt
          (.call .objectBuiltin "setimmutable" [base, nameArg, value]))
        ordered) :
    ∃ immutableName references resolvedBase resolvedValue frontPatch
        orderedBase orderedValue,
      Frontend.Expr.objectBuiltinNameArg? nameArg = some immutableName ∧
        context.findImmutableReferences? immutableName = some references ∧
        references ≠ [] ∧
        Frontend.ImmutableReference.List.patchStmts?
          references resolvedBase resolvedValue = some frontPatch ∧
        ordered =
          .Block
            (orderedImmutablePatchStmts
              references orderedBase orderedValue) ∧
        Nonempty (ExprNormalized context base orderedBase) ∧
        Nonempty (ExprNormalized context value orderedValue) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
  | none => simp [hName] at hResolve
  | some immutableName =>
      cases hBaseResolve : base.resolveObjectBuiltinsIn? context with
      | none => simp [hName, hBaseResolve] at hResolve
      | some resolvedBase =>
          cases hValueResolve : value.resolveObjectBuiltinsIn? context with
          | none => simp [hName, hBaseResolve, hValueResolve] at hResolve
          | some resolvedValue =>
              cases hRefs :
                  context.findImmutableReferences? immutableName with
              | none =>
                  simp [hName, hBaseResolve, hValueResolve, hRefs] at hResolve
              | some references =>
                  cases hPatch :
                      Frontend.ImmutableReference.List.patchStmts?
                        references resolvedBase resolvedValue with
                  | none =>
                      simp [hName, hBaseResolve, hValueResolve, hRefs,
                        hPatch] at hResolve
                  | some frontPatch =>
                      simp [hName, hBaseResolve, hValueResolve, hRefs,
                        hPatch] at hResolve
                      subst resolved
                      unfold Frontend.Stmt.toYul? at hToYul
                      cases hPatchToYul :
                          Frontend.Stmt.List.toYul? frontPatch with
                      | none => simp [hPatchToYul] at hToYul
                      | some orderedPatch =>
                          simp [hPatchToYul] at hToYul
                          have hNonempty : references ≠ [] := by
                            unfold
                              Frontend.ObjectBuiltinContext.findImmutableReferences?
                              at hRefs
                            generalize hCollected :
                                Frontend.ObjectBuiltinContext.collectImmutableReferences
                                  context.immutableReferences immutableName =
                                  collected at hRefs
                            cases collected with
                            | nil => simp at hRefs
                            | cons reference rest =>
                                simp at hRefs
                                subst references
                                simp
                          rcases
                              immutablePatchStmts_toYul_parts
                                hNonempty hPatch hPatchToYul with
                            ⟨orderedBase, orderedValue,
                              hBaseToYul, hValueToYul, hOrderedPatch⟩
                          exact
                            ⟨immutableName, references, resolvedBase,
                              resolvedValue, frontPatch,
                              orderedBase, orderedValue,
                              by simpa using hName, hRefs, hNonempty,
                              hPatch,
                              by simpa [hOrderedPatch] using hToYul.symm,
                              ⟨{
                                resolved := resolvedBase
                                resolve := hBaseResolve
                                toYul := hBaseToYul }⟩,
                              ⟨{
                                resolved := resolvedValue
                                resolve := hValueResolve
                                toYul := hValueToYul }⟩⟩

/-- Generic expression-statement normalization outside the dedicated
`setimmutable` expansion. The caller proves that the frontend resolver takes
its ordinary expression route; successful normalization then supplies the
exact canonical call expression. -/
theorem exprStmt_parts_of_generic_resolve
    {context : Frontend.ObjectBuiltinContext}
    {expr : Frontend.Expr} {ordered : Frontend.AstStmt}
    (hGeneric :
      Frontend.Stmt.resolveObjectBuiltinsIn? (.exprStmt expr) context =
        (do
          let resolvedExpr ← expr.resolveObjectBuiltinsIn? context
          some (.exprStmt resolvedExpr)))
    (hNormalized : StmtNormalized context (.exprStmt expr) ordered) :
    ∃ orderedExpr,
      ordered = .ExprStmtCall orderedExpr ∧
        Nonempty (ExprNormalized context expr orderedExpr) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  rw [hGeneric] at hResolve
  cases hExprResolve : expr.resolveObjectBuiltinsIn? context with
  | none => simp [hExprResolve] at hResolve
  | some resolvedExpr =>
      simp [hExprResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hExprToYul : resolvedExpr.toYul? with
      | none => simp [hExprToYul] at hToYul
      | some orderedExpr =>
          simp [hExprToYul] at hToYul
          exact
            ⟨orderedExpr, hToYul.symm,
              ⟨{
                resolved := resolvedExpr
                resolve := hExprResolve
                toYul := hExprToYul }⟩⟩

theorem exprStmt_call_parts_of_not_setimmutable
    {context : Frontend.ObjectBuiltinContext}
    {kind : Frontend.CallKind} {callee : Name}
    {args : List Frontend.Expr} {ordered : Frontend.AstStmt}
    (hNotSetimmutable :
      kind ≠ .objectBuiltin ∨ callee ≠ "setimmutable")
    (hNormalized :
      StmtNormalized context (.exprStmt (.call kind callee args)) ordered) :
    ∃ orderedExpr,
      ordered = .ExprStmtCall orderedExpr ∧
        Nonempty
          (ExprNormalized context (.call kind callee args) orderedExpr) := by
  apply exprStmt_parts_of_generic_resolve _ hNormalized
  cases kind with
  | primitive => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  | user => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  | dialectBuiltin => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  | objectBuiltin =>
      have hCallee : callee ≠ "setimmutable" := by
        rcases hNotSetimmutable with hKind | hCallee
        · exact False.elim (hKind rfl)
        · exact hCallee
      simp [Frontend.Stmt.resolveObjectBuiltinsIn?, hCallee]

theorem block_parts
    {context : Frontend.ObjectBuiltinContext}
    {body : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context (.block body) ordered) :
    ∃ orderedBody,
      ordered = .Block orderedBody ∧
        Nonempty (StmtListNormalized context body orderedBody) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hBodyResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
  | none => simp [hBodyResolve] at hResolve
  | some resolvedBody =>
      simp [hBodyResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hBodyToYul : Frontend.Stmt.List.toYul? resolvedBody with
      | none => simp [hBodyToYul] at hToYul
      | some orderedBody =>
          simp [hBodyToYul] at hToYul
          exact
            ⟨orderedBody, hToYul.symm,
              ⟨{
                resolved := resolvedBody
                resolve := hBodyResolve
                toYul := hBodyToYul }⟩⟩

theorem switch_parts
    {context : Frontend.ObjectBuiltinContext}
    {condition : Frontend.Expr}
    {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {default : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.switch condition cases default) ordered) :
    ∃ orderedCondition orderedCases orderedDefault,
      ordered = .Switch orderedCondition orderedCases orderedDefault ∧
        Nonempty (ExprNormalized context condition orderedCondition) ∧
        Nonempty (CaseListNormalized context cases orderedCases) ∧
        Nonempty (StmtListNormalized context default orderedDefault) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hConditionResolve : condition.resolveObjectBuiltinsIn? context with
  | none => simp [hConditionResolve] at hResolve
  | some resolvedCondition =>
      cases hCasesResolve :
          Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? cases context with
      | none => simp [hConditionResolve, hCasesResolve] at hResolve
      | some resolvedCases =>
          cases hDefaultResolve :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? default context with
          | none =>
              simp [hConditionResolve, hCasesResolve, hDefaultResolve]
                at hResolve
          | some resolvedDefault =>
              simp [hConditionResolve, hCasesResolve, hDefaultResolve]
                at hResolve
              subst resolved
              unfold Frontend.Stmt.toYul? at hToYul
              cases hConditionToYul : resolvedCondition.toYul? with
              | none => simp [hConditionToYul] at hToYul
              | some orderedCondition =>
                  cases hCasesToYul :
                      Frontend.Stmt.CaseList.toYul? resolvedCases with
                  | none => simp [hConditionToYul, hCasesToYul] at hToYul
                  | some orderedCases =>
                      cases hDefaultToYul :
                          Frontend.Stmt.List.toYul? resolvedDefault with
                      | none =>
                          simp [hConditionToYul, hCasesToYul,
                            hDefaultToYul] at hToYul
                      | some orderedDefault =>
                          simp [hConditionToYul, hCasesToYul,
                            hDefaultToYul] at hToYul
                          exact
                            ⟨orderedCondition, orderedCases, orderedDefault,
                              hToYul.symm,
                              ⟨{
                                resolved := resolvedCondition
                                resolve := hConditionResolve
                                toYul := hConditionToYul }⟩,
                              ⟨{
                                resolved := resolvedCases
                                resolve := hCasesResolve
                                toYul := hCasesToYul }⟩,
                              ⟨{
                                resolved := resolvedDefault
                                resolve := hDefaultResolve
                                toYul := hDefaultToYul }⟩⟩

theorem for_parts
    {context : Frontend.ObjectBuiltinContext}
    {pre : List Frontend.Stmt} {condition : Frontend.Expr}
    {post body : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.forLoop pre condition post body) ordered) :
    ∃ orderedPre orderedCondition orderedPost orderedBody,
      ordered =
        orderedForStmt orderedPre orderedCondition orderedPost orderedBody ∧
        Nonempty (StmtListNormalized context pre orderedPre) ∧
        Nonempty (ExprNormalized context condition orderedCondition) ∧
        Nonempty (StmtListNormalized context post orderedPost) ∧
        Nonempty (StmtListNormalized context body orderedBody) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hPreResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? pre context with
  | none => simp [hPreResolve] at hResolve
  | some resolvedPre =>
      cases hConditionResolve : condition.resolveObjectBuiltinsIn? context with
      | none => simp [hPreResolve, hConditionResolve] at hResolve
      | some resolvedCondition =>
          cases hPostResolve :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? post context with
          | none =>
              simp [hPreResolve, hConditionResolve, hPostResolve] at hResolve
          | some resolvedPost =>
              cases hBodyResolve :
                  Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
              | none =>
                  simp [hPreResolve, hConditionResolve, hPostResolve,
                    hBodyResolve] at hResolve
              | some resolvedBody =>
                  simp [hPreResolve, hConditionResolve, hPostResolve,
                    hBodyResolve] at hResolve
                  subst resolved
                  unfold Frontend.Stmt.toYul? at hToYul
                  cases hPreToYul : Frontend.Stmt.List.toYul? resolvedPre with
                  | none => simp [hPreToYul] at hToYul
                  | some orderedPre =>
                      cases hConditionToYul : resolvedCondition.toYul? with
                      | none => simp [hPreToYul, hConditionToYul] at hToYul
                      | some orderedCondition =>
                          cases hPostToYul :
                              Frontend.Stmt.List.toYul? resolvedPost with
                          | none =>
                              simp [hPreToYul, hConditionToYul,
                                hPostToYul] at hToYul
                          | some orderedPost =>
                              cases hBodyToYul :
                                  Frontend.Stmt.List.toYul? resolvedBody with
                              | none =>
                                  simp [hPreToYul, hConditionToYul,
                                    hPostToYul, hBodyToYul] at hToYul
                              | some orderedBody =>
                                  simp [hPreToYul, hConditionToYul,
                                    hPostToYul, hBodyToYul,
                                    orderedForStmt] at hToYul
                                  have hOrdered :
                                      ordered =
                                        orderedForStmt orderedPre
                                          orderedCondition orderedPost
                                          orderedBody := by
                                    cases orderedPre with
                                    | nil =>
                                        simpa [orderedForStmt] using hToYul.symm
                                    | cons head tail =>
                                        simpa [orderedForStmt] using hToYul.symm
                                  exact
                                    ⟨orderedPre, orderedCondition,
                                      orderedPost, orderedBody,
                                      hOrdered,
                                      ⟨{
                                        resolved := resolvedPre
                                        resolve := hPreResolve
                                        toYul := hPreToYul }⟩,
                                      ⟨{
                                        resolved := resolvedCondition
                                        resolve := hConditionResolve
                                        toYul := hConditionToYul }⟩,
                                      ⟨{
                                        resolved := resolvedPost
                                        resolve := hPostResolve
                                        toYul := hPostToYul }⟩,
                                      ⟨{
                                        resolved := resolvedBody
                                        resolve := hBodyResolve
                                        toYul := hBodyToYul }⟩⟩

theorem if_parts
    {context : Frontend.ObjectBuiltinContext}
    {condition : Frontend.Expr} {body : List Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.ifThen condition body) ordered) :
    ∃ orderedCondition orderedBody,
      ordered = .If orderedCondition orderedBody ∧
        Nonempty (ExprNormalized context condition orderedCondition) ∧
        Nonempty (StmtListNormalized context body orderedBody) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hConditionResolve : condition.resolveObjectBuiltinsIn? context with
  | none => simp [hConditionResolve] at hResolve
  | some resolvedCondition =>
      cases hBodyResolve :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
      | none => simp [hConditionResolve, hBodyResolve] at hResolve
      | some resolvedBody =>
          simp [hConditionResolve, hBodyResolve] at hResolve
          subst resolved
          unfold Frontend.Stmt.toYul? at hToYul
          cases hConditionToYul : resolvedCondition.toYul? with
          | none => simp [hConditionToYul] at hToYul
          | some orderedCondition =>
              cases hBodyToYul : Frontend.Stmt.List.toYul? resolvedBody with
              | none => simp [hConditionToYul, hBodyToYul] at hToYul
              | some orderedBody =>
                  simp [hConditionToYul, hBodyToYul] at hToYul
                  exact
                    ⟨orderedCondition, orderedBody, hToYul.symm,
                      ⟨{
                        resolved := resolvedCondition
                        resolve := hConditionResolve
                        toYul := hConditionToYul }⟩,
                      ⟨{
                        resolved := resolvedBody
                        resolve := hBodyResolve
                        toYul := hBodyToYul }⟩⟩

theorem functionDef_ordered
    {context : Frontend.ObjectBuiltinContext}
    {name : Name} {params returns : List Name}
    {body : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context
        (.functionDef name params returns body) ordered) :
    ordered = .Block [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hBodyResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
  | none => simp [hBodyResolve] at hResolve
  | some resolvedBody =>
      simp [hBodyResolve] at hResolve
      subst resolved
      simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem break_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context .break ordered) :
    ordered = .Break := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem continue_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context .continue ordered) :
    ordered = .Continue := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem leave_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context .leave ordered) :
    ordered = .Leave := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

end StmtNormalized

/-- Static compiler evidence for one raw function binding. It records the
checked function elaboration and its canonical ordered target, but no semantic
preservation premise. `generatedScopes` is the definition-site lexical suffix
under which the function body was elaborated. -/
structure CompiledFunctionBinding
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (generated : Name)
    (rawFn : Raw.SourceSemantics.FunctionDef)
    (generatedScopes : List (List (Name × Name))) where
  frontFn : Frontend.FunctionDef
  functionState : Elab.State
  finalFunctionState : Elab.State
  orderedBody : List Frontend.AstStmt
  functionScopes : functionState.functionScopes = generatedScopes
  elaborates :
    (Elab.FunctionDef.elaborate rawFn.params rawFn.returns rawFn.body).run
        functionState = .ok (frontFn, finalFunctionState)
  bodyNormalized :
    StmtListNormalized builtinContext frontFn.body orderedBody
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def rawFn.params rawFn.returns orderedBody)

/-- One raw function scope and the generated-name scope produced for the same
block. Generated lookup is complete with respect to raw lookup; each resolved
binding carries its checked canonical target. -/
structure CompiledFunctionScope
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawScope : Raw.SourceSemantics.FunctionScope)
    (generatedScope : List (Name × Name))
    (generatedScopes : List (List (Name × Name))) : Prop where
  binding :
    ∀ {rawName generated},
      Elab.lookupFunctionInScope rawName generatedScope = some generated →
        ∃ rawFn,
          Raw.SourceSemantics.lookupFunctionInScope rawName rawScope =
              some rawFn ∧
            Nonempty
              (CompiledFunctionBinding builtinContext contract
                generated rawFn generatedScopes)
  rawLookupNone :
    ∀ {rawName},
      Elab.lookupFunctionInScope rawName generatedScope = none →
        Raw.SourceSemantics.lookupFunctionInScope rawName rawScope = none

/-- Lexically aligned raw and generated function-scope stacks. The head scope
stores definition-site evidence against the entire generated suffix. -/
inductive CompiledFunctionScopes
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) :
    List Raw.SourceSemantics.FunctionScope →
      List (List (Name × Name)) → Prop where
  | nil : CompiledFunctionScopes builtinContext contract [] []
  | rawEmpty
      {rawRest : List Raw.SourceSemantics.FunctionScope}
      {generatedScopes : List (List (Name × Name))}
      (tail :
        CompiledFunctionScopes builtinContext contract
          rawRest generatedScopes) :
      CompiledFunctionScopes builtinContext contract
        ([] :: rawRest) generatedScopes
  | cons
      {rawScope : Raw.SourceSemantics.FunctionScope}
      {rawRest : List Raw.SourceSemantics.FunctionScope}
      {generatedScope : List (Name × Name)}
      {generatedRest : List (List (Name × Name))}
      (head :
        CompiledFunctionScope builtinContext contract rawScope generatedScope
          (generatedScope :: generatedRest))
      (tail :
        CompiledFunctionScopes builtinContext contract rawRest generatedRest) :
      CompiledFunctionScopes builtinContext contract
        (rawScope :: rawRest) (generatedScope :: generatedRest)

namespace CompiledFunctionScopes

/-- Resolve an elaborator user-function lookup to the corresponding raw
definition-site lexical suffix and checked ordered function binding. -/
theorem resolve
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawScopes : List Raw.SourceSemantics.FunctionScope}
    {generatedScopes : List (List (Name × Name))}
    (hScopes :
      CompiledFunctionScopes builtinContext contract rawScopes generatedScopes)
    {rawName generated : Name}
    (hResolve :
      Elab.resolveFunctionIn rawName generatedScopes = some generated) :
    ∃ rawFn rawLexical generatedLexical,
      Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn
          rawName rawScopes = some (rawFn, rawLexical) ∧
        Nonempty
          (CompiledFunctionBinding builtinContext contract
            generated rawFn generatedLexical) ∧
        CompiledFunctionScopes builtinContext contract
          rawLexical generatedLexical := by
  induction hScopes with
  | nil =>
      simp [Elab.resolveFunctionIn] at hResolve
  | rawEmpty tail ih =>
      rcases ih hResolve with
        ⟨rawFn, rawLexical, generatedLexical,
          hRawResolve, hBinding, hLexical⟩
      refine
        ⟨rawFn, rawLexical, generatedLexical, ?_, hBinding, hLexical⟩
      simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
        Raw.SourceSemantics.lookupFunctionInScope, hRawResolve]
  | @cons rawScope rawRest generatedScope generatedRest hHead hTail ih =>
      cases hLookup : Elab.lookupFunctionInScope rawName generatedScope with
      | none =>
          have hRawNone := hHead.rawLookupNone hLookup
          have hOuter :
              Elab.resolveFunctionIn rawName generatedRest = some generated := by
            simpa [Elab.resolveFunctionIn, hLookup] using hResolve
          rcases ih hOuter with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, hBinding, hLexical⟩
          refine
            ⟨rawFn, rawLexical, generatedLexical, ?_, hBinding, hLexical⟩
          simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
            hRawNone, hRawResolve]
      | some resolved =>
          have hGenerated : resolved = generated := by
            simpa [Elab.resolveFunctionIn, hLookup] using hResolve
          subst resolved
          rcases hHead.binding hLookup with
            ⟨rawFn, hRawLookup, hBinding⟩
          refine
            ⟨rawFn, rawScope :: rawRest, generatedScope :: generatedRest,
              ?_, hBinding, .cons hHead hTail⟩
          simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
            hRawLookup]

end CompiledFunctionScopes

/-- Raw object-builtin execution and frontend normalization share every
metadata field. The frontend may replace only `memoryContract`, which raw
source execution never inspects. -/
def ObjectBuiltinContextsAgree
    (source target : Frontend.ObjectBuiltinContext) : Prop :=
  { source with memoryContract := target.memoryContract } = target

namespace ObjectBuiltinContextsAgree

theorem withMemoryContract
    (source : Frontend.ObjectBuiltinContext)
    (memoryContract : MemoryContract.Contract) :
    ObjectBuiltinContextsAgree source
      { source with memoryContract := memoryContract } := by
  rfl

theorem size?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.size? name = target.size? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem offset?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.offset? name = target.offset? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem findLinkerSymbol?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.findLinkerSymbol? name = target.findLinkerSymbol? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem findImmutableValue?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.findImmutableValue? name = target.findImmutableValue? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem findImmutableReferences?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.findImmutableReferences? name =
      target.findImmutableReferences? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

end ObjectBuiltinContextsAgree

/-- All frontend context needed to simulate one raw expression or block. The
object metadata is shared exactly, while lexical function names are related to
their generated frontend names by checked elaboration evidence. -/
structure CompiledContext
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawContext : Raw.SourceSemantics.Context)
    (generatedScopes : List (List (Name × Name))) : Prop where
  objectBuiltins :
    ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext
  functionScopes :
    CompiledFunctionScopes builtinContext contract
      rawContext.functionScopes generatedScopes

namespace CompiledFunctionBinding

/-- Peel the checked function elaboration down to the lexical block run used
by recursive semantic preservation. Identifier-scope setup is erased, while
the definition-site generated function scopes are retained exactly. -/
theorem block_parts
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generated : Name}
    {rawFn : Raw.SourceSemantics.FunctionDef}
    {generatedScopes : List (List (Name × Name))}
    (hBinding :
      CompiledFunctionBinding builtinContext contract
        generated rawFn generatedScopes) :
    ∃ bodyState finalBodyState frontBody orderedBody,
      bodyState.functionScopes = generatedScopes ∧
        (Elab.Stmt.List.elaborateBlock rawFn.body true).run bodyState =
          .ok (frontBody, finalBodyState) ∧
        Nonempty (StmtListNormalized builtinContext frontBody orderedBody) ∧
        contract.functions.lookup generated =
          some (.Def rawFn.params rawFn.returns orderedBody) := by
  rcases hBinding with
    ⟨frontFn, functionState, finalFunctionState, orderedBody,
      hFunctionScopes, hFunction, hNormalized, hOrderedLookup⟩
  unfold Elab.FunctionDef.elaborate at hFunction
  simp [StateT.run_bind] at hFunction
  cases hPush : Elab.pushIdentifierScope.run functionState with
  | error err => simp [hPush] at hFunction
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      have hPushScopes :
          pushedState.functionScopes = functionState.functionScopes :=
        Elab.pushIdentifierScope_preserves_functionScopes hPush
      simp [hPush] at hFunction
      cases hDeclare :
          (Elab.declareIdentifiers (rawFn.params ++ rawFn.returns)
            "function parameter/result").run pushedState with
      | error err => simp [hDeclare] at hFunction
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          have hDeclareScopes :
              declaredState.functionScopes = pushedState.functionScopes :=
            Elab.declareIdentifiers_preserves_functionScopes
              (rawFn.params ++ rawFn.returns)
              "function parameter/result" hDeclare
          simp [hDeclare] at hFunction
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawFn.body true).run
                declaredState with
          | error err => simp [hBody] at hFunction
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hFunction
              cases hPop : Elab.popIdentifierScope.run bodyState with
              | error err => simp [hPop] at hFunction
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  simp [hPop] at hFunction
                  rcases hFunction with ⟨hFrontFn, _hFinalState⟩
                  have hFrontBody : frontFn.body = frontBody := by
                    rw [← hFrontFn]
                  rw [hFrontBody] at hNormalized
                  refine
                    ⟨declaredState, bodyState, frontBody, orderedBody,
                      ?_, hBody, ⟨hNormalized⟩, hOrderedLookup⟩
                  rw [hDeclareScopes, hPushScopes, hFunctionScopes]

end CompiledFunctionBinding

/-- Bundled semantic evidence for one elaborated raw user call. The frontend
derivation supplies the generated callee lookup; recursive preservation
supplies the callee body for every argument result. -/
structure GeneratedUserCallRun
    (rawFuel orderedArgsFuel orderedBodyFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawName : Name) (rawArgs : List Raw.Expr)
    (generated : Name) (orderedArgs : List Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) where
  fn : Raw.SourceSemantics.FunctionDef
  lexicalScopes : List Raw.SourceSemantics.FunctionScope
  orderedBody : List Frontend.AstStmt
  notClz : rawName ≠ "clz"
  callClass : CallClass.classifyCall rawName = .user
  rawLookup :
    Raw.SourceSemantics.lookupFunctionWithLexicalScopes context rawName =
      some (fn, lexicalScopes)
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def fn.params fn.returns orderedBody)
  argsForward :
    ArgsRunForward (rawFuel + 1) (orderedArgsFuel + 1)
      context rawArgs.reverse orderedArgs.reverse contract state
  bodyForward :
    ∀ (stateAfterArgs : State) (values : List Frontend.Word),
      BlockCodeRunForward rawFuel orderedBodyFuel
        { context with functionScopes := lexicalScopes }
        fn.body orderedBody contract
        (Yul.InteractionSemantics.stateModel.withSource stateAfterArgs
          (EvmYul.Yul.State.mkOk
            (stateAfterArgs.initcall fn.params fn.returns values.reverse)))

/-- Compiler-owned ordered binding for the one generated `clz` helper. -/
structure CompiledClzBinding
    (contract : Frontend.AstContract) (generated : Name) where
  argName : Name
  returnName : Name
  yulBody : List Frontend.AstStmt
  namesDistinct : argName ≠ returnName
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def [argName] [returnName] yulBody)
  bodyToYul :
    Frontend.Stmt.List.toYul?
        (Elab.clzHelperBody argName returnName) = some yulBody

/-- Canonical ordered-Yul evidence for one frontend function retained in the
elaborator's hoisted-function accumulator. This contains only checked syntax
lowering; recursive execution preservation is supplied separately by source
fuel induction. -/
structure CompiledHoistedFunctionBinding
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (generated : Name) (frontFn : Frontend.FunctionDef) where
  orderedBody : List Frontend.AstStmt
  bodyNormalized :
    StmtListNormalized builtinContext frontFn.body orderedBody
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def frontFn.params frontFn.returns orderedBody)

/-- Every function accumulated at one successful elaborator state has a
checked canonical binding in the active ordered contract. -/
def HoistedFunctionResolverAt
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) (elabState : Elab.State) : Prop :=
  ∀ {generated : Name} {frontFn : Frontend.FunctionDef},
    (generated, frontFn) ∈ elabState.hoistedFunctions →
      Nonempty
        (CompiledHoistedFunctionBinding
          builtinContext contract generated frontFn)

/-- Monotone inclusion of the compiler-owned hoisted-function accumulator. -/
def HoistedFunctionsExtend (before after : Elab.State) : Prop :=
  ∀ {entry : Name × Frontend.FunctionDef},
    entry ∈ before.hoistedFunctions → entry ∈ after.hoistedFunctions

namespace HoistedFunctionsExtend

theorem refl (state : Elab.State) : HoistedFunctionsExtend state state := by
  intro entry hEntry
  exact hEntry

theorem trans
    {first middle last : Elab.State}
    (hFirst : HoistedFunctionsExtend first middle)
    (hLast : HoistedFunctionsExtend middle last) :
    HoistedFunctionsExtend first last := by
  intro entry hEntry
  exact hLast (hFirst hEntry)

theorem of_preserves
    {α : Type} {action : Elab.ElabM α}
    (hPreserves : Elab.PreservesHoisted action)
    {before after : Elab.State} {value : α}
    (hRun : action.run before = .ok (value, after)) :
    HoistedFunctionsExtend before after := by
  intro entry hEntry
  exact hPreserves hRun hEntry

end HoistedFunctionsExtend

namespace HoistedFunctionResolverAt

/-- Pull ordered binding resolution backward along a checked monotone
elaborator transition. -/
theorem of_extends
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {before after : Elab.State}
    (hExtends : HoistedFunctionsExtend before after)
    (hAfter : HoistedFunctionResolverAt builtinContext contract after) :
    HoistedFunctionResolverAt builtinContext contract before := by
  intro generated frontFn hEntry
  exact hAfter (hExtends hEntry)

end HoistedFunctionResolverAt

/-- State-scoped resolver from exact generated names retained by one successful
elaboration path to the checked ordered helper binding in the active contract.
The enclosing code proof constructs this from its final elaborator state; it
does not quantify over unrelated states or arbitrary helper allocations. -/
def ClzBindingResolverAt (contract : Frontend.AstContract)
    (elabState : Elab.State) : Prop :=
  ∀ {generated arg ret : Name},
    Elab.ClzAllocatedAs elabState generated arg ret →
      Nonempty (CompiledClzBinding contract generated)

namespace ClzBindingResolverAt

/-- Pull a final-state resolver backward along one checked monotone elaborator
transition. This is the recursive continuation rule used by expression,
statement, and block preservation. -/
theorem of_extends
    {contract : Frontend.AstContract}
    {before after : Elab.State}
    (hExtends : Elab.ClzAllocationExtends before after)
    (hAfter : ClzBindingResolverAt contract after) :
    ClzBindingResolverAt contract before := by
  intro generated arg ret hAllocated
  exact hAfter (hExtends.allocated hAllocated)

end ClzBindingResolverAt

/-- Bundled generated-helper evidence for one actual elaborator action. Entry
allocation is reachable, and every exact allocation retained at the action's
final state resolves to the checked canonical helper in the active contract. -/
structure ClzCompilationPath
    (contract : Frontend.AstContract)
    (entry final : Elab.State) : Prop where
  entryValid : Elab.ClzAllocationValid entry
  finalResolver : ClzBindingResolverAt contract final

namespace ClzCompilationPath

/-- Restrict a path to its prefix. The suffix's monotone allocation transition
pulls final helper resolution back to the prefix endpoint. -/
theorem prefixPath
    {contract : Frontend.AstContract}
    {entry mid final : Elab.State}
    (path : ClzCompilationPath contract entry final)
    (hSuffix : Elab.ClzAllocationExtends mid final) :
    ClzCompilationPath contract entry mid where
  entryValid := path.entryValid
  finalResolver :=
    ClzBindingResolverAt.of_extends hSuffix path.finalResolver

/-- Restrict a path to its suffix. The prefix transition supplies reachable
allocation validity at the suffix entry. -/
theorem suffixPath
    {contract : Frontend.AstContract}
    {entry mid final : Elab.State}
    (path : ClzCompilationPath contract entry final)
    (hPrefix : Elab.ClzAllocationExtends entry mid) :
    ClzCompilationPath contract mid final where
  entryValid := hPrefix.after_valid
  finalResolver := path.finalResolver

end ClzCompilationPath

/-- Complete compiler-owned evidence along one successful frontend action.
Expressions may project the clz component; block recursion additionally uses
the final hoisted-function resolver to construct nested lexical scopes. -/
structure FrontendCompilationPath
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (entry final : Elab.State) : Prop
    extends ClzCompilationPath contract entry final where
  hoistedResolver :
    HoistedFunctionResolverAt builtinContext contract final

namespace FrontendCompilationPath

def clz
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {entry final : Elab.State}
    (path : FrontendCompilationPath builtinContext contract entry final) :
    ClzCompilationPath contract entry final :=
  path.toClzCompilationPath

theorem prefixPath
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {entry mid final : Elab.State}
    (path : FrontendCompilationPath builtinContext contract entry final)
    (hClzSuffix : Elab.ClzAllocationExtends mid final)
    (hHoistedSuffix : HoistedFunctionsExtend mid final) :
    FrontendCompilationPath builtinContext contract entry mid where
  entryValid := path.entryValid
  finalResolver :=
    ClzBindingResolverAt.of_extends hClzSuffix path.finalResolver
  hoistedResolver :=
    HoistedFunctionResolverAt.of_extends
      hHoistedSuffix path.hoistedResolver

theorem suffixPath
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {entry mid final : Elab.State}
    (path : FrontendCompilationPath builtinContext contract entry final)
    (hClzPrefix : Elab.ClzAllocationExtends entry mid) :
    FrontendCompilationPath builtinContext contract mid final where
  entryValid := hClzPrefix.after_valid
  finalResolver := path.finalResolver
  hoistedResolver := path.hoistedResolver

theorem subpath
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {entry subEntry subFinal final : Elab.State}
    (path : FrontendCompilationPath builtinContext contract entry final)
    (hPrefix : Elab.ClzAllocationExtends entry subEntry)
    (hSuffixClz : Elab.ClzAllocationExtends subFinal final)
    (hSuffixHoisted : HoistedFunctionsExtend subFinal final) :
    FrontendCompilationPath builtinContext contract subEntry subFinal :=
  (path.suffixPath hPrefix).prefixPath hSuffixClz hSuffixHoisted

end FrontendCompilationPath

/-- Checked raw-function binding augmented with the exact generated-helper path
through that function's elaboration. No semantic call premise is stored. -/
structure PathCompiledFunctionBinding
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (generated : Name)
    (rawFn : Raw.SourceSemantics.FunctionDef)
    (generatedScopes : List (List (Name × Name))) where
  frontFn : Frontend.FunctionDef
  functionState : Elab.State
  finalFunctionState : Elab.State
  orderedBody : List Frontend.AstStmt
  functionScopes : functionState.functionScopes = generatedScopes
  elaborates :
    (Elab.FunctionDef.elaborate rawFn.params rawFn.returns rawFn.body).run
        functionState = .ok (frontFn, finalFunctionState)
  bodyNormalized :
    StmtListNormalized builtinContext frontFn.body orderedBody
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def rawFn.params rawFn.returns orderedBody)
  compilationPath :
    FrontendCompilationPath builtinContext contract
      functionState finalFunctionState

namespace PathCompiledFunctionBinding

def toCompiled
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generated : Name}
    {rawFn : Raw.SourceSemantics.FunctionDef}
    {generatedScopes : List (List (Name × Name))}
    (binding :
      PathCompiledFunctionBinding builtinContext contract
        generated rawFn generatedScopes) :
    CompiledFunctionBinding builtinContext contract
      generated rawFn generatedScopes where
  frontFn := binding.frontFn
  functionState := binding.functionState
  finalFunctionState := binding.finalFunctionState
  orderedBody := binding.orderedBody
  functionScopes := binding.functionScopes
  elaborates := binding.elaborates
  bodyNormalized := binding.bodyNormalized
  orderedLookup := binding.orderedLookup

theorem block_parts
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generated : Name}
    {rawFn : Raw.SourceSemantics.FunctionDef}
    {generatedScopes : List (List (Name × Name))}
    (binding :
      PathCompiledFunctionBinding builtinContext contract
        generated rawFn generatedScopes) :
    ∃ bodyState finalBodyState frontBody orderedBody,
      bodyState.functionScopes = generatedScopes ∧
        (Elab.Stmt.List.elaborateBlock rawFn.body true).run bodyState =
          .ok (frontBody, finalBodyState) ∧
        Nonempty (StmtListNormalized builtinContext frontBody orderedBody) ∧
        contract.functions.lookup generated =
          some (.Def rawFn.params rawFn.returns orderedBody) ∧
        Nonempty
          (FrontendCompilationPath builtinContext contract
            bodyState finalBodyState) := by
  have hFunction := binding.elaborates
  unfold Elab.FunctionDef.elaborate at hFunction
  simp [StateT.run_bind] at hFunction
  cases hPush : Elab.pushIdentifierScope.run binding.functionState with
  | error err => simp [hPush] at hFunction
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      have hPushExt :=
        Elab.pushIdentifierScope_preserves_clzAllocation
          hPush binding.compilationPath.entryValid
      have hPushScopes :
          pushedState.functionScopes =
            binding.functionState.functionScopes :=
        Elab.pushIdentifierScope_preserves_functionScopes hPush
      simp [hPush] at hFunction
      cases hDeclare :
          (Elab.declareIdentifiers (rawFn.params ++ rawFn.returns)
            "function parameter/result").run pushedState with
      | error err => simp [hDeclare] at hFunction
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          have hDeclareExt :=
            Elab.declareIdentifiers_preserves_clzAllocation
              (rawFn.params ++ rawFn.returns)
              "function parameter/result" hDeclare hPushExt.after_valid
          have hDeclareScopes :
              declaredState.functionScopes = pushedState.functionScopes :=
            Elab.declareIdentifiers_preserves_functionScopes
              (rawFn.params ++ rawFn.returns)
              "function parameter/result" hDeclare
          simp [hDeclare] at hFunction
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawFn.body true).run
                declaredState with
          | error err => simp [hBody] at hFunction
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              have hBodyExt :=
                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                  rawFn.body true hBody hDeclareExt.after_valid
              simp [hBody] at hFunction
              cases hPop : Elab.popIdentifierScope.run bodyState with
              | error err => simp [hPop] at hFunction
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  have hPopExt :=
                    Elab.popIdentifierScope_preserves_clzAllocation
                      hPop hBodyExt.after_valid
                  simp [hPop] at hFunction
                  rcases hFunction with ⟨hFrontFn, hFinalState⟩
                  have hFinalResolver :
                      ClzBindingResolverAt contract poppedState := by
                    rw [hFinalState]
                    exact binding.compilationPath.finalResolver
                  have hFinalHoistedResolver :
                      HoistedFunctionResolverAt builtinContext contract
                        poppedState := by
                    rw [hFinalState]
                    exact binding.compilationPath.hoistedResolver
                  have hPopHoisted :
                      HoistedFunctionsExtend bodyState poppedState := by
                    intro entry hEntry
                    exact
                      Elab.popIdentifierScope_preserves_hoistedFunction_mem
                        hPop hEntry
                  have hBodyPath :
                      FrontendCompilationPath builtinContext contract
                        declaredState bodyState :=
                    { entryValid := hDeclareExt.after_valid
                      finalResolver :=
                        ClzBindingResolverAt.of_extends
                          hPopExt hFinalResolver
                      hoistedResolver :=
                        HoistedFunctionResolverAt.of_extends
                          hPopHoisted hFinalHoistedResolver }
                  have hFrontBody : binding.frontFn.body = frontBody := by
                    rw [← hFrontFn]
                  have hNormalized := binding.bodyNormalized
                  rw [hFrontBody] at hNormalized
                  refine
                    ⟨declaredState, bodyState, frontBody,
                      binding.orderedBody, ?_, hBody, ⟨hNormalized⟩,
                      binding.orderedLookup, ⟨hBodyPath⟩⟩
                  rw [hDeclareScopes, hPushScopes, binding.functionScopes]

end PathCompiledFunctionBinding

/-- Construct the complete checked binding for any local function selected
from one successful hoist pass. The enclosing compilation path supplies only
compiler-generated syntax evidence; body execution remains recursive proof
work and is not stored here. -/
theorem pathCompiledFunctionBinding_of_hoist
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {stmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state finalState : Elab.State}
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    (hMem :
      .functionDefinition name params returns body ∈ stmts)
    (hLookup : Elab.lookupFunctionInScope name scope = some generated)
    (hHoist :
      (Elab.Stmt.List.hoistLocalFunctions stmts scope).run state =
        .ok ((), finalState))
    (hPath :
      FrontendCompilationPath builtinContext contract state finalState) :
    Nonempty
      (PathCompiledFunctionBinding builtinContext contract generated
        { params := params, returns := returns, body := body }
        state.functionScopes) := by
  induction stmts generalizing state finalState with
  | nil =>
      simp at hMem
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition head headParams headReturns headBody =>
          simp at hMem
          rcases hMem with hHead | hTail
          · rcases hHead with
              ⟨hName, hParams, hReturns, hBody⟩
            subst head
            subst headParams
            subst headReturns
            subst headBody
            unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
            simp [hLookup, StateT.run_bind] at hHoist
            cases hFn :
                (Elab.FunctionDef.elaborate params returns body).run state with
            | error err =>
                simp [hFn] at hHoist
            | ok fnResult =>
                rcases fnResult with ⟨frontFn, fnState⟩
                simp [hFn, StateT.run_modify] at hHoist
                let addedState : Elab.State :=
                  { fnState with
                    hoistedFunctions :=
                      (generated, frontFn) :: fnState.hoistedFunctions }
                have hModify :
                    ((modify fun current : Elab.State =>
                      { current with
                        hoistedFunctions :=
                          (generated, frontFn) ::
                            current.hoistedFunctions }) :
                      Elab.ElabM Unit).run fnState =
                      .ok ((), addedState) := by
                  rfl
                have hFnExt :=
                  Elab.FunctionDef.elaborate_preserves_clzAllocation
                    params returns body hFn hPath.entryValid
                have hModifyExt :=
                  Elab.hoistFunctionEntry_preserves_clzAllocation
                    generated frontFn hModify hFnExt.after_valid
                have hRestExt :=
                  Elab.Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                    rest scope hHoist hModifyExt.after_valid
                have hSuffixExt :
                    Elab.ClzAllocationExtends fnState finalState :=
                  Elab.ClzAllocationExtends.trans hModifyExt hRestExt
                have hModifyHoisted :
                    HoistedFunctionsExtend fnState addedState := by
                  intro entry hEntry
                  exact
                    Elab.hoistFunctionEntry_preserves_hoistedFunction_mem
                      generated frontFn hModify hEntry
                have hRestHoisted :
                    HoistedFunctionsExtend addedState finalState := by
                  intro entry hEntry
                  exact
                    Elab.Stmt.List.hoistLocalFunctions_preserves_hoistedFunction_mem
                      rest scope hHoist hEntry
                have hSuffixHoisted :
                    HoistedFunctionsExtend fnState finalState :=
                  HoistedFunctionsExtend.trans
                    hModifyHoisted hRestHoisted
                have hEntry :
                    (generated, frontFn) ∈ finalState.hoistedFunctions :=
                  hRestHoisted (by simp [addedState])
                rcases hPath.hoistedResolver hEntry with ⟨hOrdered⟩
                have hFrontFields :=
                  Elab.FunctionDef.elaborate_params_returns hFn
                have hOrderedLookup := hOrdered.orderedLookup
                rw [hFrontFields.1, hFrontFields.2] at hOrderedLookup
                exact ⟨{
                  frontFn := frontFn
                  functionState := state
                  finalFunctionState := fnState
                  orderedBody := hOrdered.orderedBody
                  functionScopes := rfl
                  elaborates := hFn
                  bodyNormalized := hOrdered.bodyNormalized
                  orderedLookup := hOrderedLookup
                  compilationPath := {
                    entryValid := hPath.entryValid
                    finalResolver :=
                      ClzBindingResolverAt.of_extends
                        hSuffixExt hPath.finalResolver
                    hoistedResolver :=
                      HoistedFunctionResolverAt.of_extends
                        hSuffixHoisted hPath.hoistedResolver } }⟩
          · unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
            simp [StateT.run_bind] at hHoist
            cases hHeadLookup :
                Elab.lookupFunctionInScope head scope with
            | none =>
                simp [hHeadLookup] at hHoist
                unfold Elab.throw at hHoist
                cases hHoist
            | some headGenerated =>
                simp [hHeadLookup] at hHoist
                cases hFn :
                    (Elab.FunctionDef.elaborate
                      headParams headReturns headBody).run state with
                | error err =>
                    rw [hFn] at hHoist
                    cases hHoist
                | ok fnResult =>
                    rcases fnResult with ⟨frontFn, fnState⟩
                    simp [hFn, StateT.run_modify] at hHoist
                    let addedState : Elab.State :=
                      { fnState with
                        hoistedFunctions :=
                          (headGenerated, frontFn) ::
                            fnState.hoistedFunctions }
                    have hModify :
                        ((modify fun current : Elab.State =>
                          { current with
                            hoistedFunctions :=
                              (headGenerated, frontFn) ::
                                current.hoistedFunctions }) :
                          Elab.ElabM Unit).run fnState =
                          .ok ((), addedState) := by
                      rfl
                    have hFnExt :=
                      Elab.FunctionDef.elaborate_preserves_clzAllocation
                        headParams headReturns headBody hFn hPath.entryValid
                    have hModifyExt :=
                      Elab.hoistFunctionEntry_preserves_clzAllocation
                        headGenerated frontFn hModify hFnExt.after_valid
                    have hPrefixExt :
                        Elab.ClzAllocationExtends state addedState :=
                      Elab.ClzAllocationExtends.trans hFnExt hModifyExt
                    have hTailPath := hPath.suffixPath hPrefixExt
                    rcases ih hTail hHoist hTailPath with ⟨binding⟩
                    have hFnScopes :
                        fnState.functionScopes = state.functionScopes :=
                      Elab.FunctionDef.elaborate_preserves_functionScopes
                        headParams headReturns headBody hFn
                    have hAddedScopes :
                        addedState.functionScopes = state.functionScopes := by
                      simpa [addedState] using hFnScopes
                    rw [hAddedScopes] at binding
                    exact ⟨binding⟩
      | block nested =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | variableDeclaration names value? =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | assignment names value =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | expressionStatement expr =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | switch scrutinee cases default =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | forLoop pre condition post loopBody =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | ifThen condition ifBody =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | «break» =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | «continue» =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath
      | «leave» =>
          unfold Elab.Stmt.List.hoistLocalFunctions at hHoist
          simp at hMem
          exact ih hMem hHoist hPath

structure PathCompiledFunctionScope
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawScope : Raw.SourceSemantics.FunctionScope)
    (generatedScope : List (Name × Name))
    (generatedScopes : List (List (Name × Name))) : Prop where
  binding :
    ∀ {rawName generated},
      Elab.lookupFunctionInScope rawName generatedScope = some generated →
        ∃ rawFn,
          Raw.SourceSemantics.lookupFunctionInScope rawName rawScope =
              some rawFn ∧
            Nonempty
              (PathCompiledFunctionBinding builtinContext contract
                generated rawFn generatedScopes)
  rawLookupNone :
    ∀ {rawName},
      Elab.lookupFunctionInScope rawName generatedScope = none →
        Raw.SourceSemantics.lookupFunctionInScope rawName rawScope = none

private def LocalFunctionScopeNamesAgree
    (rawScope : Raw.SourceSemantics.FunctionScope)
    (generatedScope : List (Name × Name)) : Prop :=
  ∀ name,
    rawScope.any (fun entry => entry.fst == name) =
      generatedScope.any (fun entry => entry.fst == name)

/-- Successful generated-scope collection constructs the raw semantic scope
and preserves its exact set of source names. -/
private theorem localFunctionScope_rawFunctionScope
    {stmts : List Raw.Stmt}
    {state finalState : Elab.State}
    {generatedScope : List (Name × Name)}
    (hRun :
      (Elab.Stmt.List.localFunctionScope stmts).run state =
        .ok (generatedScope, finalState)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope ∧
        LocalFunctionScopeNamesAgree rawScope generatedScope := by
  induction stmts generalizing state finalState generatedScope with
  | nil =>
      simp [Elab.Stmt.List.localFunctionScope] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact ⟨[], rfl, by intro name; simp⟩
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          simp [StateT.run_bind] at hRun
          cases hTail :
              (Elab.Stmt.List.localFunctionScope rest).run state with
          | error err => simp [hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨generatedTail, tailState⟩
              simp [hTail] at hRun
              cases hDuplicate :
                  (generatedTail.any fun entry => entry.fst == name) with
              | true =>
                  simp [hDuplicate] at hRun
                  unfold Elab.throw at hRun
                  cases hRun
              | false =>
                  simp [hDuplicate] at hRun
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run
                        tailState with
                  | error err => simp [hDeclare] at hRun
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      simp [hDeclare] at hRun
                      cases hFresh :
                          (Elab.freshGeneratedFunctionName name).run
                            declaredState with
                      | error err => simp [hFresh] at hRun
                      | ok freshResult =>
                          rcases freshResult with ⟨generated, freshState⟩
                          simp [hFresh] at hRun
                          rcases hRun with ⟨rfl, rfl⟩
                          rcases ih hTail with
                            ⟨rawTail, hRawTail, hNames⟩
                          have hRawDuplicate :
                              (rawTail.any fun entry =>
                                entry.fst == name) = false := by
                            rw [hNames name, hDuplicate]
                          refine
                            ⟨(name, { params, returns, body }) :: rawTail,
                              ?_, ?_⟩
                          · simp [Raw.SourceSemantics.functionScope?,
                              hRawTail, hRawDuplicate]
                          · intro query
                            simp [LocalFunctionScopeNamesAgree,
                              hNames query]
      | block nested =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | variableDeclaration names value? =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | assignment names value =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | expressionStatement expr =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | switch scrutinee cases default =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | forLoop pre condition post loopBody =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | ifThen condition ifBody =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | «break» =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | «continue» =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩
      | «leave» =>
          unfold Elab.Stmt.List.localFunctionScope at hRun
          rcases ih hRun with ⟨rawScope, hRaw, hNames⟩
          exact
            ⟨rawScope,
              by simp [Raw.SourceSemantics.functionScope?, hRaw], hNames⟩

private theorem rawFunctionScope_eq_empty_of_noImmediate
    {stmts : List Raw.Stmt}
    {rawScope : Raw.SourceSemantics.FunctionScope}
    (hNone :
      Elab.Stmt.List.hasImmediateFunctionDefinition stmts = false)
    (hScope :
      Raw.SourceSemantics.functionScope? stmts = some rawScope) :
    rawScope = [] := by
  induction stmts generalizing rawScope with
  | nil =>
      simpa [Raw.SourceSemantics.functionScope?] using
        Option.some.inj hScope
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
      | block nested =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | variableDeclaration names value? =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | assignment names value =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | expressionStatement expr =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | switch scrutinee cases default =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | forLoop pre condition post loopBody =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | ifThen condition ifBody =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | «break» =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | «continue» =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope
      | «leave» =>
          simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone
          simp [Raw.SourceSemantics.functionScope?] at hScope
          exact ih hNone hScope

private theorem rawFunctionScope_of_noImmediate
    {stmts : List Raw.Stmt}
    (hNone :
      Elab.Stmt.List.hasImmediateFunctionDefinition stmts = false) :
    Raw.SourceSemantics.functionScope? stmts = some [] := by
  induction stmts with
  | nil => rfl
  | cons stmt rest ih =>
      cases stmt <;>
        simp [Elab.Stmt.List.hasImmediateFunctionDefinition] at hNone <;>
        simp [Raw.SourceSemantics.functionScope?, ih hNone]

/-- Construct the complete lexical-scope relation from the two checked scope
collectors and the actual local-function hoist path. -/
theorem pathCompiledFunctionScope_of_localHoist
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {stmts : List Raw.Stmt}
    {rawScope : Raw.SourceSemantics.FunctionScope}
    {generatedScope : List (Name × Name)}
    {generatedRest : List (List (Name × Name))}
    {scopeInit scopeState hoistState finalState : Elab.State}
    (hRawScope :
      Raw.SourceSemantics.functionScope? stmts = some rawScope)
    (hGeneratedScope :
      (Elab.Stmt.List.localFunctionScope stmts).run scopeInit =
        .ok (generatedScope, scopeState))
    (hHoist :
      (Elab.Stmt.List.hoistLocalFunctions stmts generatedScope).run
        hoistState = .ok ((), finalState))
    (hScopes :
      hoistState.functionScopes = generatedScope :: generatedRest)
    (hPath :
      FrontendCompilationPath builtinContext contract
        hoistState finalState) :
    PathCompiledFunctionScope builtinContext contract rawScope
      generatedScope (generatedScope :: generatedRest) where
  binding := by
    intro rawName generated hLookup
    rcases Elab.Stmt.List.localFunctionScope_lookup_functionDefinition
        hGeneratedScope hLookup with
      ⟨params, returns, body, hMem⟩
    have hRawLookup :=
      Raw.SourceSemantics.functionScope?_functionDefinition_lookup
        hRawScope hMem
    have hBinding :=
      pathCompiledFunctionBinding_of_hoist
        hMem hLookup hHoist hPath
    rw [hScopes] at hBinding
    exact
      ⟨{ params := params, returns := returns, body := body },
        hRawLookup, hBinding⟩
  rawLookupNone := by
    intro rawName hGeneratedNone
    cases hRawLookup :
        Raw.SourceSemantics.lookupFunctionInScope rawName rawScope with
    | none => rfl
    | some rawFn =>
        rcases
            Raw.SourceSemantics.functionScope?_lookup_functionDefinition
              hRawScope hRawLookup with
          ⟨params, returns, body, hMem, _hRawFn⟩
        rcases Elab.Stmt.List.localFunctionScope_functionDefinition_lookup
            hGeneratedScope hMem with
          ⟨generated, hGeneratedLookup⟩
        rw [hGeneratedNone] at hGeneratedLookup
        cases hGeneratedLookup

inductive PathCompiledFunctionScopes
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) :
    List Raw.SourceSemantics.FunctionScope →
      List (List (Name × Name)) → Prop where
  | nil : PathCompiledFunctionScopes builtinContext contract [] []
  | rawEmpty
      {rawRest : List Raw.SourceSemantics.FunctionScope}
      {generatedScopes : List (List (Name × Name))}
      (tail :
        PathCompiledFunctionScopes builtinContext contract
          rawRest generatedScopes) :
      PathCompiledFunctionScopes builtinContext contract
        ([] :: rawRest) generatedScopes
  | cons
      {rawScope : Raw.SourceSemantics.FunctionScope}
      {rawRest : List Raw.SourceSemantics.FunctionScope}
      {generatedScope : List (Name × Name)}
      {generatedRest : List (List (Name × Name))}
      (head :
        PathCompiledFunctionScope builtinContext contract rawScope
          generatedScope (generatedScope :: generatedRest))
      (tail :
        PathCompiledFunctionScopes builtinContext contract
          rawRest generatedRest) :
      PathCompiledFunctionScopes builtinContext contract
        (rawScope :: rawRest) (generatedScope :: generatedRest)

namespace PathCompiledFunctionScopes

theorem resolve
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawScopes : List Raw.SourceSemantics.FunctionScope}
    {generatedScopes : List (List (Name × Name))}
    (hScopes :
      PathCompiledFunctionScopes builtinContext contract
        rawScopes generatedScopes)
    {rawName generated : Name}
    (hResolve :
      Elab.resolveFunctionIn rawName generatedScopes = some generated) :
    ∃ rawFn rawLexical generatedLexical,
      Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn
          rawName rawScopes = some (rawFn, rawLexical) ∧
        Nonempty
          (PathCompiledFunctionBinding builtinContext contract
            generated rawFn generatedLexical) ∧
        PathCompiledFunctionScopes builtinContext contract
          rawLexical generatedLexical := by
  induction hScopes with
  | nil =>
      simp [Elab.resolveFunctionIn] at hResolve
  | rawEmpty tail ih =>
      rcases ih hResolve with
        ⟨rawFn, rawLexical, generatedLexical,
          hRawResolve, hBinding, hLexical⟩
      refine
        ⟨rawFn, rawLexical, generatedLexical, ?_, hBinding, hLexical⟩
      simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
        Raw.SourceSemantics.lookupFunctionInScope, hRawResolve]
  | @cons rawScope rawRest generatedScope generatedRest hHead hTail ih =>
      cases hLookup : Elab.lookupFunctionInScope rawName generatedScope with
      | none =>
          have hRawNone := hHead.rawLookupNone hLookup
          have hOuter :
              Elab.resolveFunctionIn rawName generatedRest = some generated := by
            simpa [Elab.resolveFunctionIn, hLookup] using hResolve
          rcases ih hOuter with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, hBinding, hLexical⟩
          refine
            ⟨rawFn, rawLexical, generatedLexical, ?_, hBinding, hLexical⟩
          simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
            hRawNone, hRawResolve]
      | some resolved =>
          have hGenerated : resolved = generated := by
            simpa [Elab.resolveFunctionIn, hLookup] using hResolve
          subst resolved
          rcases hHead.binding hLookup with
            ⟨rawFn, hRawLookup, hBinding⟩
          refine
            ⟨rawFn, rawScope :: rawRest, generatedScope :: generatedRest,
              ?_, hBinding, .cons hHead hTail⟩
          simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
            hRawLookup]

theorem toCompiled
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawScopes : List Raw.SourceSemantics.FunctionScope}
    {generatedScopes : List (List (Name × Name))}
    (hScopes :
      PathCompiledFunctionScopes builtinContext contract
        rawScopes generatedScopes) :
    CompiledFunctionScopes builtinContext contract
      rawScopes generatedScopes := by
  induction hScopes with
  | nil => exact .nil
  | rawEmpty tail ih => exact .rawEmpty ih
  | cons head tail ih =>
      exact .cons
        { binding := by
            intro rawName generated hLookup
            rcases head.binding hLookup with
              ⟨rawFn, hRaw, ⟨binding⟩⟩
            exact ⟨rawFn, hRaw, ⟨binding.toCompiled⟩⟩
          rawLookupNone := head.rawLookupNone }
        ih

end PathCompiledFunctionScopes

/-- Object metadata plus lexical function bindings, each carrying its actual
function-elaboration helper path. This is the context used only by the new
path-scoped semantic recursion. -/
structure PathCompiledContext
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawContext : Raw.SourceSemantics.Context)
    (generatedScopes : List (List (Name × Name))) : Prop where
  objectBuiltins :
    ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext
  functionScopes :
    PathCompiledFunctionScopes builtinContext contract
      rawContext.functionScopes generatedScopes

namespace PathCompiledContext

def withEmptyFunctionScope
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    (context :
      PathCompiledContext builtinContext contract rawContext generatedScopes) :
    PathCompiledContext builtinContext contract
      (rawContext.withFunctionScope []) generatedScopes where
  objectBuiltins := context.objectBuiltins
  functionScopes := .rawEmpty context.functionScopes

def toCompiled
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    (context :
      PathCompiledContext builtinContext contract rawContext generatedScopes) :
    CompiledContext builtinContext contract rawContext generatedScopes where
  objectBuiltins := context.objectBuiltins
  functionScopes := context.functionScopes.toCompiled

end PathCompiledContext

/-- Temporary recursive callback used by the generic expression classifier.
It remains private scaffolding until statement continuation preservation
constructs `ClzBindingResolverAt` for each reachable final state. -/
def ClzBindingResolver (contract : Frontend.AstContract) : Prop :=
  ∀ {argState : Elab.State} {generated : Name}
    {helperState : Elab.State},
    Elab.ensureClzHelper.run argState = .ok (generated, helperState) →
      Nonempty (CompiledClzBinding contract generated)

/-- Bundled semantic evidence for one generated `clz` call. The argument is
preserved recursively; helper lookup, conversion, execution fuel, and the
result equation are owned by the frontend-generated binding. -/
structure GeneratedClzCallRun
    (rawArgFuel orderedArgFuel orderedCallFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawArg : Raw.Expr) (generated : Name)
    (orderedArg : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) where
  binding : CompiledClzBinding contract generated
  bodyFuel :
    Raw.ClzPreservation.stmtListFuel
        (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
      orderedCallFuel
  argForward :
    ExprRunForward rawArgFuel orderedArgFuel
      context rawArg orderedArg contract state

theorem exprValuesRunForward_zero
    {orderedFuel : Nat} {context : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ExprValuesRunForward 0 orderedFuel
      context rawExpr orderedExpr contract state := by
  unfold ExprValuesRunForward Raw.SourceSemantics.evalValues
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem argsRunForward_zero
    {orderedFuel : Nat} {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward 0 orderedFuel
      context rawArgs orderedArgs contract state := by
  unfold ArgsRunForward
  rw [Raw.SourceSemantics.evalArgs_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem argsRunForward_nil_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward (rawFuel + 1) (orderedFuel + 1)
      context [] [] contract state := by
  unfold ArgsRunForward
  rw [Raw.SourceSemantics.EvalArgs.nil_succ]
  rw [Yul.InteractionSemantics.EvalArgs.nil_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

/-- With one unit of source fuel, a nonempty argument list reaches expression
fuel zero and truncates before any source effect. -/
theorem argsRunForward_cons_one
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawHead : Raw.Expr} {rawTail : List Raw.Expr}
    {orderedHead : Frontend.AstExpr}
    {orderedTail : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward 1 (orderedFuel + 1)
      context (rawHead :: rawTail) (orderedHead :: orderedTail)
      contract state := by
  unfold ArgsRunForward
  rw [show
    Raw.SourceSemantics.evalArgs 1 context (rawHead :: rawTail) state =
      Raw.SourceSemantics.fail state .OutOfFuel by
        unfold Raw.SourceSemantics.evalArgs
          Raw.SourceSemantics.evalTail Raw.SourceSemantics.eval
          Raw.SourceSemantics.evalValues Raw.SourceSemantics.fail
        simp only
        change
          Simulation.Interaction.bind
              (Simulation.Interaction.bind
                (Yul.InteractionSemantics.Primitive.fail state .OutOfFuel :
                  Open (State × List Frontend.Word))
                (fun result => pure (result.1, result.2.head!)))
              (fun result =>
                Yul.InteractionSemantics.Primitive.fail
                  result.1 .OutOfFuel) =
            Yul.InteractionSemantics.Primitive.fail state .OutOfFuel
        rw [Yul.InteractionSemantics.Primitive.bind_fail]
        rw [Yul.InteractionSemantics.Primitive.bind_fail]]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_literal_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {literal : Raw.Literal} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hLiteral : Raw.SourceSemantics.literalWord? literal = some value) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.literal literal) (.Lit value) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.literal_succ
    rawFuel context literal state value hLiteral]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_identifier_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hLookup : state.lookup? name = some value) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.identifier name) (.Var name) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.identifier_succ
    rawFuel context name state value hLookup]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    Yul.InteractionSemantics.stateModel, id_eq, hLookup]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_identifier_succ_any
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name}
    {contract : Frontend.AstContract} {state : State} :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.identifier name) (.Var name) contract state := by
  cases hLookup : state.lookup? name with
  | some value =>
      exact exprValuesRunForward_identifier_succ hLookup
  | none =>
      unfold ExprValuesRunForward
      unfold Raw.SourceSemantics.evalValues
        Yul.InteractionSemantics.evalValues Yul.Source.Canonical.evalValues
        Yul.Source.Effectful.evalValues
      simp only [hLookup, Yul.InteractionSemantics.stateModel, id_eq]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_elaborated_literal
    {rawFuel orderedFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {literal : Raw.Literal}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hElab :
      (Elab.Expr.elaborate (.literal literal)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.literal literal) ordered contract state := by
  rcases ExprNormalized.literal_parts hElab hNormalized with
    ⟨value, hLiteral, hOrdered⟩
  subst ordered
  exact exprValuesRunForward_literal_succ hLiteral

theorem exprValuesRunForward_of_elaborated_identifier
    {rawFuel orderedFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {name : Name}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hElab :
      (Elab.Expr.elaborate (.identifier name)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.identifier name) ordered contract state := by
  have hOrdered := ExprNormalized.identifier_ordered hElab hNormalized
  subst ordered
  exact exprValuesRunForward_identifier_succ_any

theorem exprRunForward_of_values
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    ExprRunForward rawFuel orderedFuel
      context rawExpr orderedExpr contract state := by
  unfold ExprRunForward ExprValuesRunForward at *
  rw [Raw.SourceSemantics.Eval.eval_eq_bind]
  rw [Yul.InteractionSemantics.eval_eq_bind]
  refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result => exact Simulation.Interaction.ForwardRel.done rfl

theorem ExprRunForward.withEmptyFunctionScope
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun :
      ExprRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    ExprRunForward rawFuel orderedFuel
      (context.withFunctionScope []) rawExpr orderedExpr contract state := by
  unfold ExprRunForward at *
  rw [(Raw.SourceSemantics.emptyFunctionScopeEvalEq
    rawFuel context).eval rawExpr state]
  exact hRun

/-- Semantic compiler interface for one expression under a constant target
fuel slack. The successor shape is stable under recursive argument traversal,
while the slack absorbs fixed frontend expansion depth. -/
def ExprElaborationRunForward
    (slack : Nat)
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel : Nat)
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    (Elab.Expr.elaborate rawExpr).run elabState =
        .ok (front, finalElabState) →
      ExprNormalized builtinContext front ordered →
        ExprValuesRunForward rawFuel (rawFuel + slack)
          rawContext rawExpr ordered contract state

/-- Source-facing expression preservation at one source fuel. The checked
context relates both object metadata and generated lexical function scopes. -/
def ScopedExprElaborationRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      (Elab.Expr.elaborate rawExpr).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext rawExpr ordered contract state

/-- Source-facing recursive expression interface at every source fuel. -/
def ScopedExprElaborationRunForward
    (slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel,
    ScopedExprElaborationRunForwardAt rawFuel slack builtinContext contract

/-- The well-founded recursive hypothesis available strictly below one source
fuel. Call and argument constructors consume this form. -/
def ScopedExprElaborationRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedExprElaborationRunForwardAt rawFuel slack builtinContext contract

/-- Path-scoped expression preservation. Unlike the older private callback
interface, this carries only evidence computed for the actual successful
elaborator action. -/
def ScopedExprPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Expr.elaborate rawExpr).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext rawExpr ordered contract state

def ScopedExprPathRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedExprPathRunForwardAt rawFuel slack builtinContext contract

theorem ScopedExprElaborationRunForward.below
    {slack bound : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract) :
    ScopedExprElaborationRunForwardBelow
      bound slack builtinContext contract := by
  intro rawFuel _hFuel
  exact hExpr rawFuel

/-- Recursive lexical-block interface paired with
`ScopedExprElaborationRunForward`. Child blocks construct a fresh head scope;
function calls reuse the definition-site suffix returned by
`CompiledFunctionScopes.resolve`. -/
def ScopedBlockElaborationRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          BlockCodeRunForward rawFuel (rawFuel + slack)
            rawContext rawCode ordered contract state

def ScopedBlockElaborationRunForward
    (slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel,
    ScopedBlockElaborationRunForwardAt rawFuel slack builtinContext contract

def ScopedBlockElaborationRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedBlockElaborationRunForwardAt rawFuel slack builtinContext contract

/-- Path-scoped lexical-block preservation, paired with
`ScopedExprPathRunForwardAt` for the final mutual source-fuel induction. -/
def ScopedBlockPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      FrontendCompilationPath builtinContext contract
        elabState finalElabState →
      (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          BlockCodeRunForward rawFuel (rawFuel + slack)
            rawContext rawCode ordered contract state

def ScopedBlockPathRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedBlockPathRunForwardAt rawFuel slack builtinContext contract

theorem scopedExprPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedExprPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  exact exprValuesRunForward_zero

theorem ScopedBlockElaborationRunForward.below
    {slack bound : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hBlock :
      ScopedBlockElaborationRunForward slack builtinContext contract) :
    ScopedBlockElaborationRunForwardBelow
      bound slack builtinContext contract := by
  intro rawFuel _hFuel
  exact hBlock rawFuel

theorem scopedExprElaborationRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedExprElaborationRunForwardAt
      0 slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hElab hNormalized
  exact exprValuesRunForward_zero

theorem blockCodeRunForward_zero
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {ordered : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    BlockCodeRunForward 0 orderedFuel
      rawContext rawCode ordered contract state := by
  unfold BlockCodeRunForward
  rw [Raw.SourceSemantics.execBlock_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem scopedBlockElaborationRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedBlockElaborationRunForwardAt
      0 slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState state
    hContext hElab hNormalized
  exact blockCodeRunForward_zero

theorem scopedBlockPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedBlockPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  exact blockCodeRunForward_zero

/-- Private semantic interface for compiler-generated `clz` replacement at one
fuel. The final frontend theorem discharges this from helper generation,
ordered lookup, and the helper-body execution theorem. -/
def ClzElaborationRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext (.functionCall "clz" rawArgs)
            ordered contract state

/-- Path-scoped generated-`clz` interface used by the final recursive frontend
theorem. It exposes no resolver over unrelated elaborator states. -/
def ClzPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext (.functionCall "clz" rawArgs)
            ordered contract state

/-- Pointwise checked expression compilation, independent of the order in
which runtime argument evaluation visits the list. -/
inductive ExprListCompiled (builtinContext : Frontend.ObjectBuiltinContext) :
    List Raw.Expr → List Frontend.AstExpr → Prop where
  | nil : ExprListCompiled builtinContext [] []
  | cons
      {rawHead : Raw.Expr} {orderedHead : Frontend.AstExpr}
      {rawTail : List Raw.Expr} {orderedTail : List Frontend.AstExpr}
      {frontHead : Frontend.Expr}
      {elabState finalElabState : Elab.State}
      (headElaborates :
        (Elab.Expr.elaborate rawHead).run elabState =
          .ok (frontHead, finalElabState))
      (headNormalized :
        ExprNormalized builtinContext frontHead orderedHead)
      (tail : ExprListCompiled builtinContext rawTail orderedTail) :
      ExprListCompiled builtinContext
        (rawHead :: rawTail) (orderedHead :: orderedTail)

namespace ExprListCompiled

theorem of_elaboration
    {builtinContext : Frontend.ObjectBuiltinContext} :
    ∀ {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
      {ordered : List Frontend.AstExpr}
      {elabState finalElabState : Elab.State},
      (Elab.Expr.List.elaborate rawExprs).run elabState =
          .ok (fronts, finalElabState) →
        ExprListNormalized builtinContext fronts ordered →
          ExprListCompiled builtinContext rawExprs ordered := by
  intro rawExprs
  induction rawExprs with
  | nil =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := ExprListNormalized.nil_ordered hNormalized
      subst ordered
      exact .nil
  | cons rawHead rawTail ih =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases ExprListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              exact
                .cons hHead hHeadNormalized
                  (ih hTail hTailNormalized)

theorem append
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawLeft rawRight : List Raw.Expr}
    {orderedLeft orderedRight : List Frontend.AstExpr}
    (hLeft : ExprListCompiled builtinContext rawLeft orderedLeft)
    (hRight : ExprListCompiled builtinContext rawRight orderedRight) :
    ExprListCompiled builtinContext
      (rawLeft ++ rawRight) (orderedLeft ++ orderedRight) := by
  induction hLeft with
  | nil => exact hRight
  | cons hElab hNormalized hTail ih =>
      exact .cons hElab hNormalized ih

theorem reverse
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hCompiled : ExprListCompiled builtinContext rawExprs ordered) :
    ExprListCompiled builtinContext rawExprs.reverse ordered.reverse := by
  induction hCompiled with
  | nil => exact .nil
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hNormalized hTail ih =>
      simpa using
        append ih
          (.cons hElab hNormalized
            (.nil : ExprListCompiled builtinContext [] []))

end ExprListCompiled

/-- Pointwise expression compilation with one fixed generated lexical scope
stack. This retains precisely the state relation that ordinary user calls need
after runtime reverses the argument list. -/
inductive ScopedExprListCompiled
    (builtinContext : Frontend.ObjectBuiltinContext)
    (generatedScopes : List (List (Name × Name))) :
    List Raw.Expr → List Frontend.AstExpr → Prop where
  | nil : ScopedExprListCompiled builtinContext generatedScopes [] []
  | cons
      {rawHead : Raw.Expr} {orderedHead : Frontend.AstExpr}
      {rawTail : List Raw.Expr} {orderedTail : List Frontend.AstExpr}
      {frontHead : Frontend.Expr}
      {elabState finalElabState : Elab.State}
      (headElaborates :
        (Elab.Expr.elaborate rawHead).run elabState =
          .ok (frontHead, finalElabState))
      (headScopes : elabState.functionScopes = generatedScopes)
      (headNormalized :
        ExprNormalized builtinContext frontHead orderedHead)
      (tail :
        ScopedExprListCompiled builtinContext generatedScopes
          rawTail orderedTail) :
      ScopedExprListCompiled builtinContext generatedScopes
        (rawHead :: rawTail) (orderedHead :: orderedTail)

namespace ScopedExprListCompiled

theorem of_elaboration
    {builtinContext : Frontend.ObjectBuiltinContext} :
    ∀ {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
      {ordered : List Frontend.AstExpr}
      {elabState finalElabState : Elab.State},
      (Elab.Expr.List.elaborate rawExprs).run elabState =
          .ok (fronts, finalElabState) →
        ExprListNormalized builtinContext fronts ordered →
          ScopedExprListCompiled builtinContext elabState.functionScopes
            rawExprs ordered := by
  intro rawExprs
  induction rawExprs with
  | nil =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := ExprListNormalized.nil_ordered hNormalized
      subst ordered
      exact .nil
  | cons rawHead rawTail ih =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases ExprListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              have hHeadScopes :
                  headElabState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes
                  rawHead hHead
              have hTailCompiled := ih hTail hTailNormalized
              rw [hHeadScopes] at hTailCompiled
              exact
                .cons hHead rfl hHeadNormalized hTailCompiled

theorem append
    {builtinContext : Frontend.ObjectBuiltinContext}
    {generatedScopes : List (List (Name × Name))}
    {rawLeft rawRight : List Raw.Expr}
    {orderedLeft orderedRight : List Frontend.AstExpr}
    (hLeft :
      ScopedExprListCompiled builtinContext generatedScopes
        rawLeft orderedLeft)
    (hRight :
      ScopedExprListCompiled builtinContext generatedScopes
        rawRight orderedRight) :
    ScopedExprListCompiled builtinContext generatedScopes
      (rawLeft ++ rawRight) (orderedLeft ++ orderedRight) := by
  induction hLeft with
  | nil => exact hRight
  | cons hElab hScopes hNormalized hTail ih =>
      exact .cons hElab hScopes hNormalized ih

theorem reverse
    {builtinContext : Frontend.ObjectBuiltinContext}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hCompiled :
      ScopedExprListCompiled builtinContext generatedScopes
        rawExprs ordered) :
    ScopedExprListCompiled builtinContext generatedScopes
      rawExprs.reverse ordered.reverse := by
  induction hCompiled with
  | nil => exact .nil
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hScopes hNormalized hTail ih =>
      simpa using
        append ih
          (.cons hElab hScopes hNormalized
            (.nil :
              ScopedExprListCompiled builtinContext generatedScopes [] []))

end ScopedExprListCompiled

/-- Pointwise expression compilation carrying the exact generated-helper path
for each occurrence. Because paths are stored per node, the evidence survives
the runtime reversal of call arguments without pretending elaboration itself
ran in reverse. -/
inductive PathScopedExprListCompiled
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (generatedScopes : List (List (Name × Name))) :
    List Raw.Expr → List Frontend.AstExpr → Prop where
  | nil :
      PathScopedExprListCompiled builtinContext contract generatedScopes [] []
  | cons
      {rawHead : Raw.Expr} {orderedHead : Frontend.AstExpr}
      {rawTail : List Raw.Expr} {orderedTail : List Frontend.AstExpr}
      {frontHead : Frontend.Expr}
      {elabState finalElabState : Elab.State}
      (headElaborates :
        (Elab.Expr.elaborate rawHead).run elabState =
          .ok (frontHead, finalElabState))
      (headScopes : elabState.functionScopes = generatedScopes)
      (headNormalized :
        ExprNormalized builtinContext frontHead orderedHead)
      (headPath :
        ClzCompilationPath contract elabState finalElabState)
      (tail :
        PathScopedExprListCompiled builtinContext contract generatedScopes
          rawTail orderedTail) :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        (rawHead :: rawTail) (orderedHead :: orderedTail)

namespace PathScopedExprListCompiled

theorem of_elaboration
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ∀ {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
      {ordered : List Frontend.AstExpr}
      {elabState finalElabState : Elab.State},
      (Elab.Expr.List.elaborate rawExprs).run elabState =
          .ok (fronts, finalElabState) →
        ExprListNormalized builtinContext fronts ordered →
          ClzCompilationPath contract elabState finalElabState →
            PathScopedExprListCompiled builtinContext contract
              elabState.functionScopes rawExprs ordered := by
  intro rawExprs
  induction rawExprs with
  | nil =>
      intro fronts ordered elabState finalElabState hElab hNormalized hPath
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := ExprListNormalized.nil_ordered hNormalized
      subst ordered
      exact .nil
  | cons rawHead rawTail ih =>
      intro fronts ordered elabState finalElabState hElab hNormalized hPath
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases ExprListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              have hHeadExt :=
                Elab.Expr.elaborate_preserves_clzAllocation rawHead
                  hHead hPath.entryValid
              have hTailExt :=
                Elab.Expr.List.elaborate_preserves_clzAllocation rawTail
                  hTail hHeadExt.after_valid
              have hHeadScopes :
                  headElabState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes rawHead hHead
              have hHeadPath :
                  ClzCompilationPath contract elabState headElabState :=
                hPath.prefixPath hTailExt
              have hTailPath :
                  ClzCompilationPath contract
                    headElabState tailElabState :=
                hPath.suffixPath hHeadExt
              have hTailCompiled :=
                ih hTail hTailNormalized hTailPath
              rw [hHeadScopes] at hTailCompiled
              exact
                .cons hHead rfl hHeadNormalized hHeadPath hTailCompiled

theorem append
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generatedScopes : List (List (Name × Name))}
    {rawLeft rawRight : List Raw.Expr}
    {orderedLeft orderedRight : List Frontend.AstExpr}
    (hLeft :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawLeft orderedLeft)
    (hRight :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawRight orderedRight) :
    PathScopedExprListCompiled builtinContext contract generatedScopes
      (rawLeft ++ rawRight) (orderedLeft ++ orderedRight) := by
  induction hLeft with
  | nil => exact hRight
  | cons hElab hScopes hNormalized hPath hTail ih =>
      exact .cons hElab hScopes hNormalized hPath ih

theorem reverse
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hCompiled :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawExprs ordered) :
    PathScopedExprListCompiled builtinContext contract generatedScopes
      rawExprs.reverse ordered.reverse := by
  induction hCompiled with
  | nil => exact .nil
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hScopes hNormalized hPath hTail ih =>
      simpa using
        append ih
          (.cons hElab hScopes hNormalized hPath
            (.nil :
              PathScopedExprListCompiled builtinContext contract
                generatedScopes [] []))

end PathScopedExprListCompiled

theorem argsRunForward_cons
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {rawRest : List Raw.Expr}
    {orderedArg : Frontend.AstExpr}
    {orderedRest : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hHead :
      ExprRunForward (rawFuel + 1) (orderedFuel + 1)
        context rawArg orderedArg contract state)
    (hTail :
      ∀ (stateAfterArg : State),
        ArgsRunForward rawFuel orderedFuel
          context rawRest orderedRest contract stateAfterArg) :
    ArgsRunForward (rawFuel + 2) (orderedFuel + 2)
      context (rawArg :: rawRest) (orderedArg :: orderedRest)
      contract state := by
  unfold ArgsRunForward ExprRunForward at *
  simp only [Raw.SourceSemantics.evalArgs, Raw.SourceSemantics.evalTail,
    Yul.InteractionSemantics.evalArgs, Yul.Source.Canonical.evalArgs,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.evalTail]
  refine Simulation.Interaction.ForwardRel.bind_custom hHead ?_
  intro rawHeadDone orderedHeadDone hHeadDone
  unfold SameDoneRel at hHeadDone
  subst orderedHeadDone
  cases rawHeadDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok headResult =>
      rcases headResult with ⟨stateAfterArg, value⟩
      refine
        Simulation.Interaction.ForwardRel.bind_custom
          (hTail stateAfterArg) ?_
      intro rawTailDone orderedTailDone hTailDone
      unfold SameDoneRel at hTailDone
      subst orderedTailDone
      cases rawTailDone with
      | error error =>
          exact Simulation.Interaction.ForwardRel.done rfl
      | ok tailResult =>
          exact Simulation.Interaction.ForwardRel.done rfl

theorem argsRunForward_nil_slack
    (fuel slack : Nat)
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward fuel (fuel + slack)
      context [] [] contract state := by
  cases fuel with
  | zero => exact argsRunForward_zero
  | succ residual =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (argsRunForward_nil_succ
          (rawFuel := residual) (orderedFuel := residual + slack)
          (context := context) (contract := contract) (state := state))

theorem argsRunForward_single_of_below
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawExpr orderedExpr contract state) :
    ArgsRunForward fuel (fuel + slack)
      context [rawExpr] [orderedExpr] contract state := by
  cases fuel with
  | zero => exact argsRunForward_zero
  | succ predecessor =>
      cases predecessor with
      | zero =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (argsRunForward_cons_one
              (orderedFuel := slack) (context := context)
              (rawHead := rawExpr) (rawTail := [])
              (orderedHead := orderedExpr) (orderedTail := [])
              (contract := contract) (state := state))
      | succ residual =>
          have hHead :
              ExprRunForward (residual + 1) (residual + slack + 1)
                context rawExpr orderedExpr contract state := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hExpr (residual + 1) (by omega) state
          have hTail :
              ∀ stateAfter,
                ArgsRunForward residual (residual + slack)
                  context [] [] contract stateAfter := by
            intro stateAfter
            exact
              argsRunForward_nil_slack residual slack
                (context := context) (contract := contract)
                (state := stateAfter)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (argsRunForward_cons
              (rawFuel := residual) (orderedFuel := residual + slack)
              (context := context) (rawArg := rawExpr) (rawRest := [])
              (orderedArg := orderedExpr) (orderedRest := [])
              (contract := contract) (state := state) hHead
              hTail)

theorem argsRunForward_pair_of_below
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawFirst rawSecond : Raw.Expr}
    {orderedFirst orderedSecond : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hFirst :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawFirst orderedFirst contract state)
    (hSecond :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawSecond orderedSecond contract state) :
    ArgsRunForward fuel (fuel + slack)
      context [rawFirst, rawSecond] [orderedFirst, orderedSecond]
      contract state := by
  cases fuel with
  | zero => exact argsRunForward_zero
  | succ predecessor =>
      cases predecessor with
      | zero =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (argsRunForward_cons_one
              (orderedFuel := slack) (context := context)
              (rawHead := rawFirst) (rawTail := [rawSecond])
              (orderedHead := orderedFirst)
              (orderedTail := [orderedSecond])
              (contract := contract) (state := state))
      | succ residual =>
          have hHead :
              ExprRunForward (residual + 1) (residual + slack + 1)
                context rawFirst orderedFirst contract state := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hFirst (residual + 1) (by omega) state
          have hTail :
              ∀ stateAfter,
                ArgsRunForward residual (residual + slack)
                  context [rawSecond] [orderedSecond]
                  contract stateAfter := by
            intro stateAfter
            exact
              argsRunForward_single_of_below
                (fuel := residual) (slack := slack)
                (context := context) (contract := contract)
                (state := stateAfter)
                (fun n hN state => hSecond n (by omega) state)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (argsRunForward_cons
              (rawFuel := residual) (orderedFuel := residual + slack)
              (context := context) (rawArg := rawFirst)
              (rawRest := [rawSecond]) (orderedArg := orderedFirst)
              (orderedRest := [orderedSecond]) (contract := contract)
              (state := state) hHead hTail)

theorem orderedEvalArgs_single
    (fuel : Nat) (arg : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) :
    Yul.InteractionSemantics.evalArgs (fuel + 3) [arg]
        (some contract) state =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.eval (fuel + 2) arg
          (some contract) state)
        (fun result => Simulation.Interaction.pure (result.1, [result.2])) := by
  rw [show fuel + 3 = (fuel + 1) + 2 by omega,
    Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  simp only [Yul.InteractionSemantics.evalArgs,
    Yul.Source.Canonical.evalArgs, Yul.Source.Effectful.evalArgs]
  rw [Yul.InteractionSemantics.eval_eq_bind]
  rw [show fuel + 1 + 1 = fuel + 2 by omega]
  rw [Simulation.Interaction.bind_assoc]
  apply congrArg (fun next =>
    Simulation.Interaction.bind
      (Yul.InteractionSemantics.evalValues
        (fuel + 2) arg (some contract) state) next)
  funext result
  rfl

theorem argsRunForward_of_scoped_compiled
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract) :
    ∀ {rawContext : Raw.SourceSemantics.Context}
      {generatedScopes : List (List (Name × Name))}
      {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr},
      CompiledContext builtinContext contract rawContext generatedScopes →
        ScopedExprListCompiled builtinContext generatedScopes
          rawExprs ordered →
          ∀ (rawBase : Nat) (state : State),
            ArgsRunForward
              (rawBase + 2 * rawExprs.length + 1)
              ((rawBase + slack) + 2 * rawExprs.length + 1)
              rawContext rawExprs ordered contract state := by
  intro rawContext generatedScopes rawExprs ordered hContext hCompiled
  induction hCompiled with
  | nil =>
      intro rawBase state
      simpa using
        (argsRunForward_nil_succ
          (rawFuel := rawBase) (orderedFuel := rawBase + slack)
          (context := rawContext) (contract := contract) (state := state))
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hScopes hNormalized hTail ih =>
      intro rawBase state
      let rawTailFuel := rawBase + 2 * rawTail.length + 1
      let orderedTailFuel := rawTailFuel + slack
      have hHeadContext :
          CompiledContext builtinContext contract rawContext
            elabState.functionScopes :=
        { objectBuiltins := hContext.objectBuiltins
          functionScopes := by
            simpa [hScopes] using hContext.functionScopes }
      have hHeadValues :=
        hExpr (rawTailFuel + 1) hHeadContext
          (state := state) hElab hNormalized
      have hHeadRun := exprRunForward_of_values hHeadValues
      have hHeadRun' :
          ExprRunForward (rawTailFuel + 1) (orderedTailFuel + 1)
            rawContext rawHead orderedHead contract state := by
        simpa [orderedTailFuel, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hHeadRun
      have hCons :=
        argsRunForward_cons
          (rawFuel := rawTailFuel) (orderedFuel := orderedTailFuel)
          (context := rawContext) (rawArg := rawHead)
          (rawRest := rawTail) (orderedArg := orderedHead)
          (orderedRest := orderedTail) (contract := contract)
          (state := state) hHeadRun'
          (fun stateAfterHead =>
            by
              simpa [rawTailFuel, orderedTailFuel, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                (ih rawBase stateAfterHead))
      simpa [rawTailFuel, orderedTailFuel, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCons

theorem argsRunForward_reverse_of_scoped_elaboration
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (rawBase : Nat) (state : State) :
    ArgsRunForward
      (rawBase + 2 * rawExprs.length + 1)
      ((rawBase + slack) + 2 * rawExprs.length + 1)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ScopedExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ScopedExprListCompiled.reverse hCompiled
  simpa using
    argsRunForward_of_scoped_compiled hExpr hContext hReversed
      rawBase state

/-- Argument-list preservation at every source fuel. The two-step source
schedule mirrors `evalArgs`/`evalTail`: fuel zero truncates immediately, fuel
one truncates on a nonempty head, and fuel `n + 2` recursively evaluates the
head at `n + 1` and the tail at `n`. -/
theorem argsRunForward_of_scoped_compiled_fuel
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hContext :
      CompiledContext builtinContext contract rawContext generatedScopes)
    (hCompiled :
      ScopedExprListCompiled builtinContext generatedScopes
        rawExprs ordered) :
  ∀ (rawFuel : Nat) (state : State),
      ArgsRunForward rawFuel (rawFuel + slack)
        rawContext rawExprs ordered contract state := by
  intro rawFuel
  induction rawFuel using Nat.strong_induction_on generalizing
      rawExprs ordered with
  | h rawFuel ih =>
      intro state
      cases rawFuel with
      | zero =>
          exact argsRunForward_zero
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := 0) (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | cons hElab hScopes hNormalized hTail =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_cons_one
                      (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
          | succ residual =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := residual + 1)
                      (orderedFuel := (residual + 1) + slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | @cons rawHead orderedHead rawTail orderedTail frontHead
                  elabState finalElabState hElab hScopes hNormalized hTail =>
                  have hHeadContext :
                      CompiledContext builtinContext contract rawContext
                        elabState.functionScopes :=
                    { objectBuiltins := hContext.objectBuiltins
                      functionScopes := by
                        simpa [hScopes] using hContext.functionScopes }
                  have hHeadValues :=
                    hExpr (residual + 1) hHeadContext
                      (state := state) hElab hNormalized
                  have hHead := exprRunForward_of_values hHeadValues
                  have hTailRun :
                      ∀ stateAfterHead,
                        ArgsRunForward residual (residual + slack)
                          rawContext rawTail orderedTail contract
                          stateAfterHead := by
                    intro stateAfterHead
                    exact
                      ih residual (by omega) hTail stateAfterHead
                  have hCons :=
                    argsRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := rawContext) (rawArg := rawHead)
                      (rawRest := rawTail) (orderedArg := orderedHead)
                      (orderedRest := orderedTail) (contract := contract)
                      (state := state) (by
                        simpa [Nat.add_comm, Nat.add_left_comm,
                          Nat.add_assoc] using hHead)
                      hTailRun
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using hCons

/-- Argument preservation from only the strictly-lower expression hypotheses
needed by the source evaluator. This is the form used by the final source-fuel
induction. -/
theorem argsRunForward_of_scoped_compiled_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hContext :
      CompiledContext builtinContext contract rawContext generatedScopes)
    (hCompiled :
      ScopedExprListCompiled builtinContext generatedScopes
        rawExprs ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs ordered contract state := by
  induction rawFuel using Nat.strong_induction_on generalizing
      rawExprs ordered state with
  | h rawFuel ih =>
      cases rawFuel with
      | zero =>
          exact argsRunForward_zero
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := 0) (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | cons hElab hScopes hNormalized hTail =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_cons_one
                      (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
          | succ residual =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := residual + 1)
                      (orderedFuel := (residual + 1) + slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | @cons rawHead orderedHead rawTail orderedTail frontHead
                  elabState finalElabState hElab hScopes hNormalized hTail =>
                  have hHeadContext :
                      CompiledContext builtinContext contract rawContext
                        elabState.functionScopes :=
                    { objectBuiltins := hContext.objectBuiltins
                      functionScopes := by
                        simpa [hScopes] using hContext.functionScopes }
                  have hHeadValues :=
                    hExpr (residual + 1) (by omega)
                      hHeadContext (state := state) hElab hNormalized
                  have hHead := exprRunForward_of_values hHeadValues
                  have hTailBelow :
                      ScopedExprElaborationRunForwardBelow
                        residual slack builtinContext contract := by
                    intro fuel hFuel
                    exact hExpr fuel (by omega)
                  have hTailRun :
                      ∀ stateAfterHead,
                        ArgsRunForward residual (residual + slack)
                          rawContext rawTail orderedTail contract
                          stateAfterHead := by
                    intro stateAfterHead
                    exact
                      ih residual (by omega) hTailBelow hTail
                        stateAfterHead
                  have hCons :=
                    argsRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := rawContext) (rawArg := rawHead)
                      (rawRest := rawTail) (orderedArg := orderedHead)
                      (orderedRest := orderedTail) (contract := contract)
                      (state := state) (by
                        simpa [Nat.add_comm, Nat.add_left_comm,
                          Nat.add_assoc] using hHead)
                      hTailRun
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using hCons

theorem argsRunForward_reverse_of_scoped_elaboration_fuel
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ScopedExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ScopedExprListCompiled.reverse hCompiled
  exact
    argsRunForward_of_scoped_compiled_fuel
      hExpr hContext hReversed rawFuel state

theorem argsRunForward_reverse_of_scoped_elaboration_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ScopedExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ScopedExprListCompiled.reverse hCompiled
  exact
    argsRunForward_of_scoped_compiled_fuel_below
      hExpr hContext hReversed state

/-- Arbitrary-fuel argument preservation over occurrence-local compilation
paths. This is stable under argument reversal because each node retains its
own exact elaborator path to the final artifact binding. -/
theorem argsRunForward_of_path_scoped_compiled_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hContext :
      PathCompiledContext builtinContext contract rawContext generatedScopes)
    (hCompiled :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawExprs ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs ordered contract state := by
  induction rawFuel using Nat.strong_induction_on generalizing
      rawExprs ordered state with
  | h rawFuel ih =>
      cases rawFuel with
      | zero =>
          exact argsRunForward_zero
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := 0) (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | cons hElab hScopes hNormalized hPath hTail =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_cons_one
                      (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
          | succ residual =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := residual + 1)
                      (orderedFuel := (residual + 1) + slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | @cons rawHead orderedHead rawTail orderedTail frontHead
                  elabState finalElabState hElab hScopes hNormalized
                  hHeadPath hTail =>
                  have hHeadContext :
                      PathCompiledContext builtinContext contract rawContext
                        elabState.functionScopes :=
                    { objectBuiltins := hContext.objectBuiltins
                      functionScopes := by
                        simpa [hScopes] using hContext.functionScopes }
                  have hHeadValues :=
                    hExpr (residual + 1) (by omega)
                      hHeadContext hHeadPath (state := state)
                        hElab hNormalized
                  have hHead := exprRunForward_of_values hHeadValues
                  have hTailBelow :
                      ScopedExprPathRunForwardBelow
                        residual slack builtinContext contract := by
                    intro fuel hFuel
                    exact hExpr fuel (by omega)
                  have hTailRun :
                      ∀ stateAfterHead,
                        ArgsRunForward residual (residual + slack)
                          rawContext rawTail orderedTail contract
                          stateAfterHead := by
                    intro stateAfterHead
                    exact
                      ih residual (by omega) hTailBelow hTail
                        stateAfterHead
                  have hCons :=
                    argsRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := rawContext) (rawArg := rawHead)
                      (rawRest := rawTail) (orderedArg := orderedHead)
                      (orderedRest := orderedTail) (contract := contract)
                      (state := state) (by
                        simpa [Nat.add_comm, Nat.add_left_comm,
                          Nat.add_assoc] using hHead)
                      hTailRun
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using hCons

theorem argsRunForward_reverse_of_path_elaboration_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    PathScopedExprListCompiled.of_elaboration hElab hNormalized hPath
  have hReversed := PathScopedExprListCompiled.reverse hCompiled
  exact
    argsRunForward_of_path_scoped_compiled_fuel_below
      hExpr hContext hReversed state

theorem argsRunForward_of_compiled
    {slack : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract) :
    ∀ {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr},
      ExprListCompiled builtinContext rawExprs ordered →
        ∀ (rawBase : Nat) (state : State),
          ArgsRunForward
            (rawBase + 2 * rawExprs.length + 1)
            ((rawBase + slack) + 2 * rawExprs.length + 1)
            rawContext rawExprs ordered contract state := by
  intro rawExprs ordered hCompiled
  induction hCompiled with
  | nil =>
      intro rawBase state
      simpa using
        (argsRunForward_nil_succ
          (rawFuel := rawBase) (orderedFuel := rawBase + slack)
          (context := rawContext) (contract := contract) (state := state))
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hNormalized hTail ih =>
      intro rawBase state
      let rawTailFuel := rawBase + 2 * rawTail.length + 1
      let orderedTailFuel := rawTailFuel + slack
      have hHeadValues :=
        hExpr (rawTailFuel + 1)
          (state := state) hElab hNormalized
      have hHeadRun := exprRunForward_of_values hHeadValues
      have hHeadRun' :
          ExprRunForward (rawTailFuel + 1) (orderedTailFuel + 1)
            rawContext rawHead orderedHead contract state := by
        simpa [orderedTailFuel, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hHeadRun
      have hCons :=
        argsRunForward_cons
          (rawFuel := rawTailFuel) (orderedFuel := orderedTailFuel)
          (context := rawContext) (rawArg := rawHead)
          (rawRest := rawTail) (orderedArg := orderedHead)
          (orderedRest := orderedTail) (contract := contract)
          (state := state) hHeadRun'
          (fun stateAfterHead =>
            by
              simpa [rawTailFuel, orderedTailFuel, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                (ih rawBase stateAfterHead))
      simpa [rawTailFuel, orderedTailFuel, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCons

theorem argsRunForward_reverse_of_elaboration
    {slack : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (rawBase : Nat) (state : State) :
    ArgsRunForward
      (rawBase + 2 * rawExprs.length + 1)
      ((rawBase + slack) + 2 * rawExprs.length + 1)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ExprListCompiled.reverse hCompiled
  simpa using
    (argsRunForward_of_compiled hExpr hReversed
      rawBase state)

theorem argsRunForward_of_elaboration
    {slack : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (rawBase : Nat) (state : State) :
    ArgsRunForward
      (rawBase + 2 * rawExprs.length + 1)
      ((rawBase + slack) + 2 * rawExprs.length + 1)
      rawContext rawExprs ordered contract state :=
  argsRunForward_of_compiled hExpr
    (ExprListCompiled.of_elaboration hElab hNormalized) rawBase state

theorem exprValuesRunForward_primitiveCall_of_runs
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {orderedArgs : List Frontend.AstExpr}
    {op : EvmYul.Operation .Yul}
    {contract : Frontend.AstContract} {state : State}
    (hClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hOp : Frontend.Primitive.ofName? name = some op)
    (hArgs :
      ArgsRunForward rawFuel orderedFuel context
        rawArgs.reverse orderedArgs.reverse contract state)
    (hPrimitive :
      ∀ (stateAfterArgs : State) (values : List Frontend.Word),
        PrimitiveRunForward rawFuel orderedFuel
          stateAfterArgs op values.reverse) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.functionCall name rawArgs) (.Call (.inl op) orderedArgs)
      contract state := by
  unfold ExprValuesRunForward ArgsRunForward at *
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    rawFuel context name rawArgs state hClz]
  simp only [hClass, hOp]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  refine Simulation.Interaction.ForwardRel.bind_custom hArgs ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      exact hPrimitive result.1 result.2

theorem exprRunForward_numberLiteral_slack
    (fuel slack value : Nat)
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    ExprRunForward fuel (fuel + slack) context
      (.literal (.number (EvmYul.UInt256.ofNat value)))
      (.Lit (EvmYul.UInt256.ofNat value)) contract state := by
  cases fuel with
  | zero => exact exprRunForward_of_values exprValuesRunForward_zero
  | succ residual =>
      apply exprRunForward_of_values
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_literal_succ
          (rawFuel := residual) (orderedFuel := residual + slack)
          (context := context) (contract := contract) (state := state)
          (literal := .number (EvmYul.UInt256.ofNat value))
          (value := EvmYul.UInt256.ofNat value) rfl)

theorem exprValuesRunForward_immutablePatchAdd
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawBase : Raw.Expr} {orderedBase : Frontend.AstExpr}
    {reference : Frontend.ImmutableReference}
    {contract : Frontend.AstContract} {state : State}
    (hBase :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawBase orderedBase contract state) :
    ExprValuesRunForward fuel (fuel + slack) context
      (.functionCall "add"
        [rawBase,
          .literal (.number (EvmYul.UInt256.ofNat reference.start))])
      (.Call (.inl .ADD)
        [orderedBase, .Lit (EvmYul.UInt256.ofNat reference.start)])
      contract state := by
  cases fuel with
  | zero => exact exprValuesRunForward_zero
  | succ residual =>
      have hArgs :
          ArgsRunForward residual (residual + slack) context
            [ .literal
                (.number (EvmYul.UInt256.ofNat reference.start)),
              rawBase ]
            [ .Lit (EvmYul.UInt256.ofNat reference.start),
              orderedBase ] contract state :=
        argsRunForward_pair_of_below
          (fuel := residual) (slack := slack)
          (context := context) (contract := contract) (state := state)
          (fun n _hN state =>
            exprRunForward_numberLiteral_slack
              n slack reference.start
              (context := context) (contract := contract) (state := state))
          (fun n hN state => hBase n (by omega) state)
      have hRun :=
        exprValuesRunForward_primitiveCall_of_runs
          (rawFuel := residual) (orderedFuel := residual + slack)
          (context := context) (name := "add")
          (rawArgs :=
            [rawBase,
              .literal
                (.number (EvmYul.UInt256.ofNat reference.start))])
          (orderedArgs :=
            [orderedBase,
              .Lit (EvmYul.UInt256.ofNat reference.start)])
          (op := .ADD) (contract := contract) (state := state)
          (by decide) rfl rfl hArgs
          (fun stateAfterArgs values =>
            primitiveRunForward_slack residual slack
              stateAfterArgs .ADD values.reverse)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_immutablePatchCall
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawBase rawValue : Raw.Expr}
    {orderedBase orderedValue : Frontend.AstExpr}
    {reference : Frontend.ImmutableReference}
    {contract : Frontend.AstContract} {state : State}
    (hBase :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawBase orderedBase contract state)
    (hValue :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawValue orderedValue contract state) :
    ExprValuesRunForward fuel (fuel + slack) context
      (.functionCall "mstore"
        [ .functionCall "add"
            [rawBase,
              .literal
                (.number (EvmYul.UInt256.ofNat reference.start))],
          rawValue ])
      (.Call (.inl .MSTORE)
        [ .Call (.inl .ADD)
            [orderedBase,
              .Lit (EvmYul.UInt256.ofNat reference.start)],
          orderedValue ])
      contract state := by
  cases fuel with
  | zero => exact exprValuesRunForward_zero
  | succ residual =>
      have hArgs :
          ArgsRunForward residual (residual + slack) context
            [ rawValue,
              .functionCall "add"
                [rawBase,
                  .literal
                    (.number (EvmYul.UInt256.ofNat reference.start))] ]
            [ orderedValue,
              .Call (.inl .ADD)
                [orderedBase,
                  .Lit (EvmYul.UInt256.ofNat reference.start)] ]
            contract state :=
        argsRunForward_pair_of_below
          (fuel := residual) (slack := slack)
          (context := context) (contract := contract) (state := state)
          (fun n hN state => hValue n (by omega) state)
          (fun n hN state =>
            exprRunForward_of_values
              (exprValuesRunForward_immutablePatchAdd
                (fuel := n) (slack := slack)
                (context := context) (rawBase := rawBase)
                (orderedBase := orderedBase) (reference := reference)
                (contract := contract) (state := state)
                (fun m hM state => hBase m (by omega) state)))
      have hRun :=
        exprValuesRunForward_primitiveCall_of_runs
          (rawFuel := residual) (orderedFuel := residual + slack)
          (context := context) (name := "mstore")
          (rawArgs :=
            [ .functionCall "add"
                [rawBase,
                  .literal
                    (.number (EvmYul.UInt256.ofNat reference.start))],
              rawValue ])
          (orderedArgs :=
            [ .Call (.inl .ADD)
                [orderedBase,
                  .Lit (EvmYul.UInt256.ofNat reference.start)],
              orderedValue ])
          (op := .MSTORE) (contract := contract) (state := state)
          (by decide) rfl rfl hArgs
          (fun stateAfterArgs values =>
            primitiveRunForward_slack residual slack
              stateAfterArgs .MSTORE values.reverse)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_primitiveCall_succ
    {fuel : Nat} {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {orderedArgs : List Frontend.AstExpr}
    {op : EvmYul.Operation .Yul}
    {contract : Frontend.AstContract} {state : State}
    (hClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hOp : Frontend.Primitive.ofName? name = some op)
    (hArgs :
      ArgsRunForward fuel fuel context rawArgs.reverse orderedArgs.reverse
        contract state) :
    ExprValuesRunForward (fuel + 1) (fuel + 1)
      context (.functionCall name rawArgs) (.Call (.inl op) orderedArgs)
      contract state :=
  exprValuesRunForward_primitiveCall_of_runs
    hClz hClass hOp hArgs
    (fun stateAfterArgs values =>
      forward_refl Yul.FunctionsInteractionPrimitive.Truncated
        (Yul.InteractionSemantics.primitiveSemantics.eval
          fuel stateAfterArgs op values.reverse))

theorem exprValuesRunForward_of_elaborated_primitiveCall
    {slack rawBase : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hPrimitive :
      ∀ (op : EvmYul.Operation .Yul),
        Frontend.Primitive.ofName? name = some op →
          ∀ (stateAfterArgs : State) (values : List Frontend.Word),
            PrimitiveRunForward
              (rawBase + 2 * rawArgs.length + 1)
              ((rawBase + slack) + 2 * rawArgs.length + 1)
              stateAfterArgs op values.reverse) :
    ExprValuesRunForward
      (rawBase + 2 * rawArgs.length + 2)
      ((rawBase + slack) + 2 * rawArgs.length + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  unfold Elab.Expr.elaborate at hElab
  simp at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases ExprNormalized.primitive_call_parts hNormalized with
        ⟨op, orderedArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
      let rawArgsFuel := rawBase + 2 * rawArgs.length + 1
      let orderedArgsFuel :=
        (rawBase + slack) + 2 * rawArgs.length + 1
      have hArgsRun :=
        argsRunForward_reverse_of_elaboration hExpr hArgs hArgsNormalized
          rawBase state
      have hCall :=
        exprValuesRunForward_primitiveCall_of_runs
          hNotClz hClass hOp hArgsRun (hPrimitive op hOp)
      have hRawFuel :
          rawBase + 2 * rawArgs.length + 2 =
            (rawBase + 2 * rawArgs.length + 1) + 1 := by
        omega
      have hOrderedFuel :
          (rawBase + slack) + 2 * rawArgs.length + 2 =
            ((rawBase + slack) + 2 * rawArgs.length + 1) + 1 := by
        omega
      rw [hRawFuel, hOrderedFuel]
      exact hCall

theorem exprValuesRunForward_of_scoped_elaborated_primitiveCall_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        argsFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hPrimitive :
      ∀ (op : EvmYul.Operation .Yul),
        Frontend.Primitive.ofName? name = some op →
          ∀ (stateAfterArgs : State) (values : List Frontend.Word),
            PrimitiveRunForward
              argsFuel (argsFuel + slack)
              stateAfterArgs op values.reverse) :
    ExprValuesRunForward
      (argsFuel + 1)
      ((argsFuel + slack) + 1)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  unfold Elab.Expr.elaborate at hElab
  simp at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases ExprNormalized.primitive_call_parts hNormalized with
        ⟨op, orderedArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
      have hArgsRun :=
        argsRunForward_reverse_of_scoped_elaboration_fuel_below
          hExpr hContext hArgs hArgsNormalized
          state
      have hCall :=
        exprValuesRunForward_primitiveCall_of_runs
          hNotClz hClass hOp hArgsRun (hPrimitive op hOp)
      exact hCall

theorem exprValuesRunForward_of_path_elaborated_primitiveCall_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        argsFuel slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hPrimitive :
      ∀ (op : EvmYul.Operation .Yul),
        Frontend.Primitive.ofName? name = some op →
          ∀ (stateAfterArgs : State) (values : List Frontend.Word),
            PrimitiveRunForward
              argsFuel (argsFuel + slack)
              stateAfterArgs op values.reverse) :
    ExprValuesRunForward
      (argsFuel + 1)
      ((argsFuel + slack) + 1)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  unfold Elab.Expr.elaborate at hElab
  simp at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases ExprNormalized.primitive_call_parts hNormalized with
        ⟨op, orderedArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
      have hArgsRun :=
        argsRunForward_reverse_of_path_elaboration_fuel_below
          hExpr hContext hPath hArgs hArgsNormalized state
      exact
        exprValuesRunForward_primitiveCall_of_runs
          hNotClz hClass hOp hArgsRun (hPrimitive op hOp)

theorem exprValuesRunForward_userCall_one
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user) :
    ExprValuesRunForward 1 orderedFuel rawContext
      (.functionCall name rawArgs) ordered contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    0 rawContext name rawArgs state hNotClz]
  simp only [hClass]
  rw [Raw.SourceSemantics.evalArgs_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_objectBuiltinCall_one
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .objectBuiltin) :
    ExprValuesRunForward 1 orderedFuel rawContext
      (.functionCall name rawArgs) ordered contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    0 rawContext name rawArgs state hNotClz]
  simp only [hClass]
  unfold Raw.SourceSemantics.evalObjectBuiltin
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_clz_one
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ExprValuesRunForward 1 orderedFuel rawContext
      (.functionCall "clz" [rawArg]) ordered contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.clz_succ 0 rawContext rawArg state]
  unfold Raw.SourceSemantics.eval
  simp only [Raw.SourceSemantics.evalValues]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_generatedClz
    {rawArgFuel orderedBase : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {generated : Name}
    {orderedArg : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun : GeneratedClzCallRun rawArgFuel (orderedBase + 2)
      (orderedBase + 3)
      context rawArg generated orderedArg contract state) :
    ExprValuesRunForward (rawArgFuel + 1) (orderedBase + 4)
      context (.functionCall "clz" [rawArg])
      (.Call (.inr generated) [orderedArg]) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.clz_succ]
  rw [show orderedBase + 4 = (orderedBase + 3) + 1 by omega,
    Yul.InteractionSemantics.EvalValues.internal_succ]
  simp only [List.reverse_singleton]
  rw [orderedEvalArgs_single]
  rw [Simulation.Interaction.bind_assoc]
  have hArg := hRun.argForward
  unfold ExprRunForward at hArg
  refine Simulation.Interaction.ForwardRel.bind_custom hArg ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      rcases result with ⟨stateAfterArg, value⟩
      cases stateAfterArg with
      | OutOfFuel =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [
                Yul.FunctionsInteractionPrimitive.Truncated])
      | Checkpoint jump =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [
                Yul.FunctionsInteractionPrimitive.Truncated])
      | Ok shared store =>
          simp only [Simulation.Interaction.instMonad,
            Simulation.Interaction.pure, Simulation.Interaction.bind,
            List.reverse_singleton]
          rw [Raw.ClzPreservation.clzHelperCall
            hRun.binding.namesDistinct hRun.binding.orderedLookup
            hRun.binding.bodyToYul
            shared store value (orderedBase + 3) hRun.bodyFuel]
          apply Simulation.Interaction.ForwardRel.done
          unfold SameDoneRel
          rw [Elab.ClzHelperModel.run_eq_reference]

theorem exprValuesRunForward_of_scoped_clz_parts
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {frontArg : Frontend.Expr}
    {orderedArg : Frontend.AstExpr} {generated : Name}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        context elabState.functionScopes)
    (hArgElab :
      (Elab.Expr.elaborate rawArg).run elabState =
        .ok (frontArg, finalElabState))
    (hArgNormalized :
      ExprNormalized builtinContext frontArg orderedArg)
    (binding : CompiledClzBinding contract generated)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" [rawArg])
      (.Call (.inr generated) [orderedArg]) contract state := by
  have hArgValues :=
    hExpr (state := state) hContext hArgElab hArgNormalized
  have hArgRun := exprRunForward_of_values hArgValues
  let orderedBase := rawArgFuel + slack - 2
  have hBase : orderedBase + 2 = rawArgFuel + slack := by
    dsimp [orderedBase]
    omega
  have hBodyFuel :
      Raw.ClzPreservation.stmtListFuel
          (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
        orderedBase + 3 := by
    rw [Raw.ClzPreservation.helperBodyFuel_eq]
    dsimp [orderedBase]
    omega
  have hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2) (orderedBase + 3)
        context rawArg generated
        orderedArg contract state :=
    { binding := binding
      bodyFuel := hBodyFuel
      argForward := by simpa [hBase] using hArgRun }
  have hCall := exprValuesRunForward_generatedClz hRun
  have hTargetEq : orderedBase + 4 = rawArgFuel + slack + 2 := by
    dsimp [orderedBase]
    omega
  rw [hTargetEq] at hCall
  exact hCall

theorem exprValuesRunForward_of_scoped_elaborated_clz_at
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        context elabState.functionScopes)
    (hValid : Elab.ClzAllocationValid elabState)
    (hBindings : ClzBindingResolverAt contract finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" rawArgs) ordered contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  have hArgExt :=
    Elab.Expr.elaborate_preserves_clzAllocation rawArg hArgElab hValid
  rcases Elab.ensureClzHelper_allocated hEnsure hArgExt.after_valid with
    ⟨argName, returnName, hAllocated⟩
  rcases hBindings hAllocated with ⟨binding⟩
  exact
    exprValuesRunForward_of_scoped_clz_parts
      hExpr hContext hArgElab hArgNormalized binding
      hArgTarget hHelperFuel

/-- Path-native generated-`clz` preservation. The argument prefix receives a
resolver transported backward through `ensureClzHelper`; the exact helper
binding is then read from the actual expression-final state. -/
theorem exprValuesRunForward_of_scoped_elaborated_clz_path
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        context elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" rawArgs) ordered contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  have hArgExt :=
    Elab.Expr.elaborate_preserves_clzAllocation rawArg
      hArgElab hPath.entryValid
  have hEnsureExt :=
    Elab.ensureClzHelper_preserves_clzAllocation
      hEnsure hArgExt.after_valid
  have hArgPath :
      ClzCompilationPath contract elabState argState :=
    hPath.prefixPath hEnsureExt
  have hArgValues :=
    hExpr (state := state) hContext hArgPath hArgElab hArgNormalized
  have hArgRun := exprRunForward_of_values hArgValues
  rcases Elab.ensureClzHelper_allocated hEnsure hArgExt.after_valid with
    ⟨argName, returnName, hAllocated⟩
  rcases hPath.finalResolver hAllocated with ⟨binding⟩
  let orderedBase := rawArgFuel + slack - 2
  have hBase : orderedBase + 2 = rawArgFuel + slack := by
    dsimp [orderedBase]
    omega
  have hBodyFuel :
      Raw.ClzPreservation.stmtListFuel
          (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
        orderedBase + 3 := by
    rw [Raw.ClzPreservation.helperBodyFuel_eq]
    dsimp [orderedBase]
    omega
  have hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2) (orderedBase + 3)
        context rawArg generated
        orderedArg contract state :=
    { binding := binding
      bodyFuel := hBodyFuel
      argForward := by simpa [hBase] using hArgRun }
  have hCall := exprValuesRunForward_generatedClz hRun
  have hTargetEq : orderedBase + 4 = rawArgFuel + slack + 2 := by
    dsimp [orderedBase]
    omega
  rw [hTargetEq] at hCall
  exact hCall

theorem exprValuesRunForward_of_scoped_elaborated_clz
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        context elabState.functionScopes)
    (hBindings : ClzBindingResolver contract)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" rawArgs) ordered contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  rcases hBindings hEnsure with ⟨binding⟩
  exact
    exprValuesRunForward_of_scoped_clz_parts
      hExpr hContext hArgElab hArgNormalized binding
      hArgTarget hHelperFuel

def clzFrontendSlack : Nat :=
  Raw.ClzPreservation.helperBodyFuel + 1

/-- Compiler-owned frontend expansion budget at one raw semantic fuel. The
fixed component executes the generated `clz` helper body; each additional raw
fuel level covers at most one nested frontend control/call expansion. -/
def sourceFuelFrontendSlack (rawFuel : Nat) : Nat :=
  Raw.ClzPreservation.helperBodyFuel + rawFuel

theorem clzElaborationRunForwardAt_zero
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzElaborationRunForwardAt
      0 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hElab hNormalized
  exact exprValuesRunForward_zero

theorem clzElaborationRunForwardAt_one
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzElaborationRunForwardAt
      1 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hElab hNormalized
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  exact exprValuesRunForward_clz_one

theorem clzElaborationRunForwardAt_succ_succ
    {argFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        (argFuel + 1) Raw.ClzPreservation.helperBodyFuel
        builtinContext contract)
    (hBindings : ClzBindingResolver contract) :
    ClzElaborationRunForwardAt
      (argFuel + 2) clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hElab hNormalized
  have hArgTarget :
      2 ≤ (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel := by
    rw [Raw.ClzPreservation.helperBodyFuel_value]
    omega
  have hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel + 1 := by
    omega
  have hCall := exprValuesRunForward_of_scoped_elaborated_clz
    (state := state) hExpr hContext hBindings hElab hNormalized
      hArgTarget hHelperFuel
  simpa [clzFrontendSlack, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hCall

theorem clzPathRunForwardAt_zero
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzPathRunForwardAt
      0 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  exact exprValuesRunForward_zero

theorem clzPathRunForwardAt_one
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzPathRunForwardAt
      1 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  exact exprValuesRunForward_clz_one

theorem clzPathRunForwardAt_succ_succ
    {argFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardAt
        (argFuel + 1) Raw.ClzPreservation.helperBodyFuel
        builtinContext contract) :
    ClzPathRunForwardAt
      (argFuel + 2) clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  have hArgTarget :
      2 ≤ (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel := by
    rw [Raw.ClzPreservation.helperBodyFuel_value]
    omega
  have hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel + 1 := by
    omega
  have hCall := exprValuesRunForward_of_scoped_elaborated_clz_path
    (state := state) hExpr hContext hPath hElab hNormalized
      hArgTarget hHelperFuel
  simpa [clzFrontendSlack, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hCall

/-- Fuel-indexed generated-`clz` preservation at any compiler budget at least
`sourceFuelFrontendSlack`. The recursive argument receives exactly one less
slack, matching the one extra generated call layer. -/
theorem clzPathRunForwardAt_succ_succ_of_slack
    {argFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hSlack : sourceFuelFrontendSlack (argFuel + 2) ≤ slack)
    (hExpr :
      ScopedExprPathRunForwardAt
        (argFuel + 1) (slack - 1) builtinContext contract) :
    ClzPathRunForwardAt
      (argFuel + 2) slack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  have hArgTarget :
      2 ≤ (argFuel + 1) + (slack - 1) := by
    unfold sourceFuelFrontendSlack at hSlack
    rw [Raw.ClzPreservation.helperBodyFuel_value] at hSlack
    omega
  have hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        (argFuel + 1) + (slack - 1) + 1 := by
    unfold sourceFuelFrontendSlack at hSlack
    omega
  have hCall :=
    exprValuesRunForward_of_scoped_elaborated_clz_path
      (state := state) hExpr hContext hPath hElab hNormalized
        hArgTarget hHelperFuel
  have hPositive : 1 ≤ slack := by
    unfold sourceFuelFrontendSlack at hSlack
    omega
  have hTargetFuel :
      (argFuel + 1 + (slack - 1)) + 2 = argFuel + 2 + slack := by
    omega
  rw [hTargetFuel] at hCall
  exact hCall

/-- Call-body execution and caller restoration supplied by one bundled
generated-call occurrence, independently of its argument-fuel schedule. -/
theorem generatedUserCallRun_call_succ
    {rawFuel orderedArgsFuel orderedBodyFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {entryState stateAfterArgs : State}
    {reversedValues : List Frontend.Word}
    (hRun :
      GeneratedUserCallRun rawFuel orderedArgsFuel orderedBodyFuel
        context rawName rawArgs generated orderedArgs contract entryState) :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.call (rawFuel + 1) context
        reversedValues.reverse rawName stateAfterArgs)
      (Yul.InteractionSemantics.call (orderedBodyFuel + 1)
        reversedValues.reverse (some generated) (some contract)
        stateAfterArgs) := by
  rw [Raw.SourceSemantics.Call.explicit_succ
    rawFuel context reversedValues.reverse rawName stateAfterArgs
    hRun.fn hRun.lexicalScopes hRun.rawLookup]
  rw [Yul.InteractionSemantics.Call.explicit_succ
    orderedBodyFuel reversedValues.reverse generated contract
    hRun.fn.params hRun.fn.returns hRun.orderedBody stateAfterArgs
    hRun.orderedLookup]
  have hBodyForward := hRun.bodyForward stateAfterArgs reversedValues
  unfold BlockCodeRunForward at hBodyForward
  refine
    Simulation.Interaction.ForwardRel.bind_custom hBodyForward ?_
  intro rawBodyDone orderedBodyDone hBodyDone
  unfold SameDoneRel at hBodyDone
  subst orderedBodyDone
  cases rawBodyDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok stateAfterBody => exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_userCall_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun : GeneratedUserCallRun rawFuel orderedFuel orderedFuel context
      rawName rawArgs generated orderedArgs contract state) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 2)
      context (.functionCall rawName rawArgs)
      (.Call (.inr generated) orderedArgs) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context rawName rawArgs state hRun.notClz]
  simp only [hRun.callClass]
  rw [Yul.InteractionSemantics.EvalValues.internal_succ]
  have hArgsForward := hRun.argsForward
  unfold ArgsRunForward at hArgsForward
  refine
    Simulation.Interaction.ForwardRel.bind_custom hArgsForward ?_
  intro rawArgsDone orderedArgsDone hArgsDone
  unfold SameDoneRel at hArgsDone
  subst orderedArgsDone
  cases rawArgsDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok argsResult =>
      rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
      exact generatedUserCallRun_call_succ hRun

/-- Frontend-owned provider for a direct elaborated user call. The recursive
source-fuel proof will construct it from lexical compilation evidence; callers
see neither generated names nor callee layouts. -/
def UserCallElaborationRunForward
    (slack : Nat)
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawBase : Nat)
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {state : State},
    (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState) →
      ExprNormalized builtinContext front ordered →
        ∃ generated orderedArgs,
          ordered = .Call (.inr generated) orderedArgs ∧
            Nonempty
              (GeneratedUserCallRun
                (rawBase + 2 * rawArgs.length)
                ((rawBase + slack) + 2 * rawArgs.length)
                ((rawBase + slack) + 2 * rawArgs.length)
                rawContext name rawArgs generated orderedArgs contract state)

theorem exprValuesRunForward_of_elaborated_userCall
    {slack rawBase : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hUser :
      UserCallElaborationRunForward
        slack rawContext builtinContext contract)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (rawBase + 2 * rawArgs.length + 2)
      ((rawBase + slack) + 2 * rawArgs.length + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  rcases hUser rawBase hElab hNormalized with
    ⟨generated, orderedArgs, rfl, ⟨hRun⟩⟩
  have hCall := exprValuesRunForward_userCall_succ hRun
  have hRawFuel :
      rawBase + 2 * rawArgs.length + 2 =
        (rawBase + 2 * rawArgs.length) + 2 := by
    omega
  have hOrderedFuel :
      (rawBase + slack) + 2 * rawArgs.length + 2 =
        ((rawBase + slack) + 2 * rawArgs.length) + 2 := by
    omega
  rw [hRawFuel, hOrderedFuel]
  exact hCall

/-- Ordinary generated user calls are preserved from compiler-derived lexical
scope evidence and the lower-fuel recursive expression/block hypotheses. No
callee-preservation or generated-layout premise is exposed. -/
theorem exprValuesRunForward_of_scoped_elaborated_userCall_below
    {slack callFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hBlock :
      ScopedBlockElaborationRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (callFuel + 2)
      ((callFuel + slack) + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  unfold Elab.Expr.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      have hArgsScopes :
          argsState.functionScopes = elabState.functionScopes :=
        Elab.Expr.List.elaborate_preserves_functionScopes rawArgs hArgs
      have hArgsContext :
          CompiledContext builtinContext contract rawContext
            argsState.functionScopes :=
        { objectBuiltins := hContext.objectBuiltins
          functionScopes := by
            simpa [hArgsScopes] using hContext.functionScopes }
      simp [hArgs, hClass] at hElab
      cases hResolve :
          Elab.resolveFunctionIn name argsState.functionScopes with
      | none =>
          simp [Elab.resolveFunction, StateT.run_bind,
            StateT.run_get, hResolve] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab
      | some generated =>
          simp [Elab.resolveFunction, hResolve] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases ExprNormalized.user_call_parts hNormalized with
            ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
          rcases CompiledFunctionScopes.resolve
              hArgsContext.functionScopes hResolve with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, ⟨hBinding⟩, hLexicalScopes⟩
          rcases CompiledFunctionBinding.block_parts hBinding with
            ⟨bodyElabState, finalBodyElabState, frontBody, orderedBody,
              hBodyScopes, hBodyElab, ⟨hBodyNormalized⟩,
              hOrderedLookup⟩
          have hBodyContext :
              CompiledContext builtinContext contract
                { rawContext with functionScopes := rawLexical }
                bodyElabState.functionScopes :=
            { objectBuiltins := by
                simpa using hContext.objectBuiltins
              functionScopes := by
                simpa [hBodyScopes] using hLexicalScopes }
          have hArgsRun :=
            argsRunForward_reverse_of_scoped_elaboration_fuel_below
              (rawFuel := callFuel + 1)
              (fun fuel hFuel => hExpr fuel (by omega))
              hContext hArgs hArgsNormalized state
          have hRawLookup :
              Raw.SourceSemantics.lookupFunctionWithLexicalScopes
                  rawContext name = some (rawFn, rawLexical) := by
            simpa [Raw.SourceSemantics.lookupFunctionWithLexicalScopes]
              using hRawResolve
          have hRun :
              GeneratedUserCallRun callFuel (callFuel + slack)
                (callFuel + slack)
                rawContext name rawArgs generated orderedArgs contract state :=
            { fn := rawFn
              lexicalScopes := rawLexical
              orderedBody := orderedBody
              notClz := hNotClz
              callClass := hClass
              rawLookup := hRawLookup
              orderedLookup := hOrderedLookup
              argsForward := by
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hArgsRun
              bodyForward := by
                intro stateAfterArgs values
                have hBody :=
                  hBlock callFuel (by omega)
                    (rawContext :=
                      { rawContext with functionScopes := rawLexical })
                    hBodyContext
                    (state :=
                      Yul.InteractionSemantics.stateModel.withSource
                        stateAfterArgs
                        (EvmYul.Yul.State.mkOk
                          (stateAfterArgs.initcall rawFn.params
                            rawFn.returns values.reverse)))
                    hBodyElab hBodyNormalized
                simpa [Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using hBody }
          have hCall := exprValuesRunForward_userCall_succ hRun
          exact hCall

/-- Construct the bundled generated-call execution evidence from one actual
checked path. Both value-position calls and expression statements consume this
same interface; generated names and callee layouts remain existential. -/
theorem generatedUserCallRun_of_path_elaboration_below
    {argsSlack bodySlack callFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (callFuel + 2) argsSlack builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (callFuel + 2) bodySlack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ∃ generated orderedArgs,
      ordered = .Call (.inr generated) orderedArgs ∧
        Nonempty
          (GeneratedUserCallRun callFuel (callFuel + argsSlack)
            (callFuel + bodySlack)
            rawContext name rawArgs generated orderedArgs contract state) := by
  unfold Elab.Expr.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      have hArgsScopes :
          argsState.functionScopes = elabState.functionScopes :=
        Elab.Expr.List.elaborate_preserves_functionScopes rawArgs hArgs
      have hArgsContext :
          PathCompiledContext builtinContext contract rawContext
            argsState.functionScopes :=
        { objectBuiltins := hContext.objectBuiltins
          functionScopes := by
            simpa [hArgsScopes] using hContext.functionScopes }
      simp [hArgs, hClass] at hElab
      cases hResolve :
          Elab.resolveFunctionIn name argsState.functionScopes with
      | none =>
          simp [Elab.resolveFunction, StateT.run_bind,
            StateT.run_get, hResolve] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab
      | some generated =>
          simp [Elab.resolveFunction, hResolve] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases ExprNormalized.user_call_parts hNormalized with
            ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
          rcases PathCompiledFunctionScopes.resolve
              hArgsContext.functionScopes hResolve with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, ⟨hBinding⟩, hLexicalScopes⟩
          rcases PathCompiledFunctionBinding.block_parts hBinding with
            ⟨bodyElabState, finalBodyElabState, frontBody, orderedBody,
              hBodyScopes, hBodyElab, ⟨hBodyNormalized⟩,
              hOrderedLookup, ⟨hBodyPath⟩⟩
          have hBodyContext :
              PathCompiledContext builtinContext contract
                { rawContext with functionScopes := rawLexical }
                bodyElabState.functionScopes :=
            { objectBuiltins := by
                simpa using hContext.objectBuiltins
              functionScopes := by
                simpa [hBodyScopes] using hLexicalScopes }
          have hArgsRun :=
            argsRunForward_reverse_of_path_elaboration_fuel_below
              (rawFuel := callFuel + 1)
              (fun fuel hFuel => hExpr fuel (by omega))
              hContext hPath hArgs hArgsNormalized state
          have hRawLookup :
              Raw.SourceSemantics.lookupFunctionWithLexicalScopes
                  rawContext name = some (rawFn, rawLexical) := by
            simpa [Raw.SourceSemantics.lookupFunctionWithLexicalScopes]
              using hRawResolve
          have hRun :
              GeneratedUserCallRun callFuel (callFuel + argsSlack)
                (callFuel + bodySlack)
                rawContext name rawArgs generated orderedArgs contract state :=
            { fn := rawFn
              lexicalScopes := rawLexical
              orderedBody := orderedBody
              notClz := hNotClz
              callClass := hClass
              rawLookup := hRawLookup
              orderedLookup := hOrderedLookup
              argsForward := by
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hArgsRun
              bodyForward := by
                intro stateAfterArgs values
                have hBody :=
                  hBlock callFuel (by omega)
                    (rawContext :=
                      { rawContext with functionScopes := rawLexical })
                    hBodyContext hBodyPath
                    (state :=
                      Yul.InteractionSemantics.stateModel.withSource
                        stateAfterArgs
                        (EvmYul.Yul.State.mkOk
                          (stateAfterArgs.initcall rawFn.params
                            rawFn.returns values.reverse)))
                    hBodyElab hBodyNormalized
                simpa [Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using hBody }
          exact ⟨generated, orderedArgs, rfl, ⟨hRun⟩⟩

/-- Path-scoped ordinary user calls. The lexical lookup returns a checked
callee binding carrying its own function-body elaboration path, so recursive
calls and generated `clz` inside nested functions require no semantic oracle. -/
theorem exprValuesRunForward_of_path_elaborated_userCall_below
    {slack callFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (callFuel + 2)
      ((callFuel + slack) + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  rcases generatedUserCallRun_of_path_elaboration_below
      hExpr hBlock hContext hPath hNotMemoryguard hNotClz hClass
      hElab hNormalized with
    ⟨generated, orderedArgs, rfl, ⟨hRun⟩⟩
  exact exprValuesRunForward_userCall_succ hRun

namespace ExprNormalized

theorem datasize_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "datasize" args) ordered) :
    ∃ nameArg dataName size,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some dataName ∧
        context.size? dataName = some size ∧
        ordered = .Lit size := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some dataName =>
              cases hSize : context.size? dataName with
              | none => simp [hName, hSize] at hResolve
              | some size =>
                  simp [hName, hSize] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, dataName, size, rfl, hName, hSize,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem dataoffset_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "dataoffset" args) ordered) :
    ∃ nameArg dataName offset,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some dataName ∧
        context.offset? dataName = some offset ∧
        ordered = .Lit offset := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some dataName =>
              cases hOffset : context.offset? dataName with
              | none => simp [hName, hOffset] at hResolve
              | some offset =>
                  simp [hName, hOffset] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, dataName, offset, rfl, hName, hOffset,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem linkersymbol_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "linkersymbol" args) ordered) :
    ∃ nameArg linkerName value,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some linkerName ∧
        context.findLinkerSymbol? linkerName = some value ∧
        ordered = .Lit value := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some linkerName =>
              cases hValue : context.findLinkerSymbol? linkerName with
              | none => simp [hName, hValue] at hResolve
              | some value =>
                  simp [hName, hValue] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, linkerName, value, rfl, hName, hValue,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem loadimmutable_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "loadimmutable" args) ordered) :
    ∃ nameArg immutableName value,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some immutableName ∧
        context.findImmutableValue? immutableName = some value ∧
        ordered = .Lit value := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some immutableName =>
              cases hValue : context.findImmutableValue? immutableName with
              | none => simp [hName, hValue] at hResolve
              | some value =>
                  simp [hName, hValue] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, immutableName, value, rfl, hName, hValue,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem datacopy_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "datacopy" args) ordered) :
    ∃ target offset size orderedArgs op,
      args = [target, offset, size] ∧
        Frontend.Primitive.ofName? "codecopy" = some op ∧
        ordered = .Call (.inl op) orderedArgs ∧
        Nonempty
          (ExprListNormalized context [target, offset, size] orderedArgs) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons target rest =>
      cases rest with
      | nil =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn? [target] context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul
      | cons offset rest =>
          cases rest with
          | nil =>
              cases hArgsResolve :
                  Frontend.Expr.List.resolveObjectBuiltinsIn?
                    [target, offset] context with
              | none => simp [hArgsResolve] at hResolve
              | some resolvedArgs =>
                  simp [hArgsResolve] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
          | cons size rest =>
              cases rest with
              | nil =>
                  cases hTarget :
                      target.resolveObjectBuiltinsIn? context with
                  | none => simp [hTarget] at hResolve
                  | some resolvedTarget =>
                      cases hOffset :
                          offset.resolveObjectBuiltinsIn? context with
                      | none => simp [hTarget, hOffset] at hResolve
                      | some resolvedOffset =>
                          cases hSize :
                              size.resolveObjectBuiltinsIn? context with
                          | none =>
                              simp [hTarget, hOffset, hSize] at hResolve
                          | some resolvedSize =>
                              simp [hTarget, hOffset, hSize] at hResolve
                              subst resolved
                              unfold Frontend.Expr.toYul? at hToYul
                              cases hOp :
                                  Frontend.Primitive.ofName? "codecopy" with
                              | none => simp [hOp] at hToYul
                              | some op =>
                                  cases hArgsYul :
                                      Frontend.Expr.List.toYul?
                                        [resolvedTarget, resolvedOffset,
                                          resolvedSize] with
                                  | none => simp [hOp, hArgsYul] at hToYul
                                  | some orderedArgs =>
                                      simp [hOp, hArgsYul] at hToYul
                                      refine
                                        ⟨target, offset, size, orderedArgs,
                                          op, rfl, by rfl, hToYul.symm, ⟨{
                                            resolved :=
                                              [resolvedTarget,
                                                resolvedOffset, resolvedSize]
                                            resolve := by
                                              simp [Frontend.Expr.List.resolveObjectBuiltinsIn?,
                                                hTarget, hOffset, hSize]
                                            toYul := hArgsYul }⟩⟩
              | cons extra tail =>
                  cases hArgsResolve :
                      Frontend.Expr.List.resolveObjectBuiltinsIn?
                        (target :: offset :: size :: extra :: tail) context with
                  | none => simp [hArgsResolve] at hResolve
                  | some resolvedArgs =>
                      simp [hArgsResolve] at hResolve
                      subst resolved
                      simp [Frontend.Expr.toYul?] at hToYul

theorem memoryguard_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "memoryguard" args) ordered) :
    ∃ value size,
      args = [value] ∧
        Nonempty (ExprNormalized context value (.Lit size)) ∧
        ordered = .Lit size := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons value rest =>
      cases rest with
      | nil =>
          cases hValue : value.resolveObjectBuiltinsIn? context with
          | none => simp [hValue] at hResolve
          | some resolvedValue =>
              cases resolvedValue with
              | lit size =>
                  simp [hValue] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  have hValueNormalized :
                      ExprNormalized context value (.Lit size) :=
                    { resolved := .lit size
                      resolve := hValue
                      toYul := rfl }
                  exact
                    ⟨value, size, rfl,
                      ⟨hValueNormalized⟩,
                      hToYul.symm⟩
              | stringLit literal => simp [hValue] at hResolve
              | bytesLit bytes => simp [hValue] at hResolve
              | var name => simp [hValue] at hResolve
              | call kind callee callArgs => simp [hValue] at hResolve
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (value :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

end ExprNormalized

theorem exprValuesRunForward_datasize_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {dataName : Name} {size : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName : Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some dataName)
    (hSize : context.objectBuiltins.size? dataName = some size) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "datasize" [nameArg]) (.Lit size)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "datasize" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "datasize" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit size) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.datasize_succ
    rawFuel context nameArg state dataName size hName hSize]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_scoped_elaborated_datasize
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "datasize" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "datasize" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "datasize") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.datasize_parts hNormalized with
    ⟨frontNameArg, dataName, size, hFrontArgs,
      hFrontName, hSize, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_datasize_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.size?_eq hBuiltins]
        exact hSize))

theorem exprValuesRunForward_dataoffset_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {dataName : Name} {offset : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName : Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some dataName)
    (hOffset : context.objectBuiltins.offset? dataName = some offset) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "dataoffset" [nameArg]) (.Lit offset)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "dataoffset" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "dataoffset" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit offset) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.dataoffset_succ
    rawFuel context nameArg state dataName offset hName hOffset]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_scoped_elaborated_dataoffset
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "dataoffset" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "dataoffset" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "dataoffset") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.dataoffset_parts hNormalized with
    ⟨frontNameArg, dataName, offset, hFrontArgs,
      hFrontName, hOffset, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_dataoffset_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.offset?_eq hBuiltins]
        exact hOffset))

theorem exprValuesRunForward_linkersymbol_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {linkerName : Name} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName : Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some linkerName)
    (hValue :
      context.objectBuiltins.findLinkerSymbol? linkerName = some value) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "linkersymbol" [nameArg]) (.Lit value)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "linkersymbol" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "linkersymbol" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit value) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.linkersymbol_succ
    rawFuel context nameArg state linkerName value hName hValue]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_scoped_elaborated_linkersymbol
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "linkersymbol" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "linkersymbol" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "linkersymbol") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.linkersymbol_parts hNormalized with
    ⟨frontNameArg, linkerName, value, hFrontArgs,
      hFrontName, hValue, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_linkersymbol_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.findLinkerSymbol?_eq hBuiltins]
        exact hValue))

theorem exprValuesRunForward_loadimmutable_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {immutableName : Name} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName :
      Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some immutableName)
    (hValue :
      context.objectBuiltins.findImmutableValue? immutableName = some value) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "loadimmutable" [nameArg]) (.Lit value)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "loadimmutable" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "loadimmutable" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit value) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.loadimmutable_succ
    rawFuel context nameArg state immutableName value hName hValue]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_scoped_elaborated_loadimmutable
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "loadimmutable" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "loadimmutable" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "loadimmutable") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.loadimmutable_parts hNormalized with
    ⟨frontNameArg, immutableName, value, hFrontArgs,
      hFrontName, hValue, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_loadimmutable_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.findImmutableValue?_eq hBuiltins]
        exact hValue))

theorem exprValuesRunForward_datacopy_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {orderedArgs : List Frontend.AstExpr}
    {op : EvmYul.Operation .Yul}
    {contract : Frontend.AstContract} {state : State}
    (hOp : Frontend.Primitive.ofName? "codecopy" = some op)
    (hArgs :
      ArgsRunForward rawFuel orderedFuel context
        rawArgs.reverse orderedArgs.reverse contract state)
    (hPrimitive :
      ∀ (stateAfterArgs : State) (values : List Frontend.Word),
        PrimitiveRunForward rawFuel orderedFuel
          stateAfterArgs op values.reverse) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "datacopy" rawArgs)
      (.Call (.inl op) orderedArgs) contract state := by
  unfold ExprValuesRunForward ArgsRunForward at *
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "datacopy" rawArgs state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "datacopy" rawArgs state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Call (.inl op) orderedArgs) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.datacopy_succ
    rawFuel context rawArgs state op hOp]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  refine Simulation.Interaction.ForwardRel.bind_custom hArgs ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      exact hPrimitive result.1 result.2

theorem exprValuesRunForward_of_scoped_elaborated_datacopy_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        argsFuel (slack + 1) builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "datacopy" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (argsFuel + 2) ((argsFuel + 2) + slack)
      rawContext (.functionCall "datacopy" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "datacopy") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.datacopy_parts hNormalized with
    ⟨target, offset, size, orderedArgs, op,
      hFrontArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
  rw [hFrontArgs] at hArgs
  have hArgsRun :=
    argsRunForward_reverse_of_scoped_elaboration_fuel_below
      hExpr hContext hArgs hArgsNormalized
      state
  have hRun :=
    exprValuesRunForward_datacopy_succ
      (rawFuel := argsFuel)
      (orderedFuel := argsFuel + (slack + 1))
      hOp hArgsRun
      (fun stateAfterArgs values =>
        primitiveRunForward_slack argsFuel (slack + 1)
          stateAfterArgs op values.reverse)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_of_path_elaborated_datacopy_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        argsFuel (slack + 1) builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "datacopy" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (argsFuel + 2) ((argsFuel + 2) + slack)
      rawContext (.functionCall "datacopy" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "datacopy") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.datacopy_parts hNormalized with
    ⟨target, offset, size, orderedArgs, op,
      hFrontArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
  rw [hFrontArgs] at hArgs
  have hArgsRun :=
    argsRunForward_reverse_of_path_elaboration_fuel_below
      hExpr hContext hPath hArgs hArgsNormalized state
  have hRun :=
    exprValuesRunForward_datacopy_succ
      (rawFuel := argsFuel)
      (orderedFuel := argsFuel + (slack + 1))
      hOp hArgsRun
      (fun stateAfterArgs values =>
        primitiveRunForward_slack argsFuel (slack + 1)
          stateAfterArgs op values.reverse)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_memoryguard_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawValue : Raw.Expr} {size : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hValue :
      ExprRunForward rawFuel (orderedFuel + 1)
        context rawValue (.Lit size) contract state) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "memoryguard" [rawValue])
      (.Lit size) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "memoryguard" [rawValue] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "memoryguard" [rawValue] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit size) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.memoryguard_succ]
  have hTarget :
      Simulation.Interaction.bind
          (Yul.InteractionSemantics.eval (orderedFuel + 1)
            (.Lit size) (some contract) state)
          (fun result => pure (result.1, [result.2])) =
        Yul.InteractionSemantics.evalValues (orderedFuel + 1)
          (.Lit size) (some contract) state := by
    unfold Yul.InteractionSemantics.eval Yul.Source.Canonical.eval
      Yul.Source.Effectful.eval Yul.InteractionSemantics.evalValues
      Yul.Source.Canonical.evalValues Yul.Source.Effectful.evalValues
    rfl
  rw [← hTarget]
  unfold ExprRunForward at hValue
  refine Simulation.Interaction.ForwardRel.bind_custom hValue ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result => exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_scoped_elaborated_memoryguard_below
    {slack valueFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        (valueFuel + 1) (slack + 2) builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "memoryguard" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (valueFuel + 2) ((valueFuel + 2) + slack)
      rawContext (.functionCall "memoryguard" rawArgs)
      ordered contract state := by
  rcases memoryguard_elaboration_parts hElab with
    ⟨rawValue, frontValue, valueState, rfl, rfl, hValueElab, rfl⟩
  rcases ExprNormalized.memoryguard_parts hNormalized with
    ⟨normalizedValue, size, hFrontArgs, ⟨hValueNormalized⟩, rfl⟩
  rcases List.cons.inj hFrontArgs with ⟨hFrontValue, _⟩
  subst normalizedValue
  have hValueValues :=
    hExpr valueFuel (by omega) hContext (state := state)
      hValueElab hValueNormalized
  have hValueRun := exprRunForward_of_values hValueValues
  have hRun :=
    exprValuesRunForward_memoryguard_succ
      (rawFuel := valueFuel)
      (orderedFuel := valueFuel + slack + 1)
      hValueRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_of_path_elaborated_memoryguard_below
    {slack valueFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (valueFuel + 1) (slack + 2) builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "memoryguard" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (valueFuel + 2) ((valueFuel + 2) + slack)
      rawContext (.functionCall "memoryguard" rawArgs)
      ordered contract state := by
  rcases memoryguard_elaboration_parts hElab with
    ⟨rawValue, frontValue, valueState, rfl, rfl, hValueElab, rfl⟩
  rcases ExprNormalized.memoryguard_parts hNormalized with
    ⟨normalizedValue, size, hFrontArgs, ⟨hValueNormalized⟩, rfl⟩
  rcases List.cons.inj hFrontArgs with ⟨hFrontValue, _⟩
  subst normalizedValue
  have hValueValues :=
    hExpr valueFuel (by omega) hContext hPath (state := state)
      hValueElab hValueNormalized
  have hValueRun := exprRunForward_of_values hValueValues
  have hRun :=
    exprValuesRunForward_memoryguard_succ
      (rawFuel := valueFuel)
      (orderedFuel := valueFuel + slack + 1)
      hValueRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

/-- Generic successor expression constructor. Primitive, ordinary user-call,
and object-builtin cases are selected from the canonical Lean classifier;
unsupported dialect calls and expression-position `setimmutable` are rejected
by successful normalization. `clz` remains the one private generated-helper
interface to discharge. -/
theorem scopedExprElaborationRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprElaborationRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockElaborationRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hClz :
      ClzElaborationRunForwardAt
        (fuel + 1) slack builtinContext contract) :
    ScopedExprElaborationRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hElab hNormalized
  cases rawExpr with
  | literal literal =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_literal
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | identifier name =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_identifier
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | functionCall name rawArgs =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases fuel with
        | zero =>
            exact
              exprValuesRunForward_objectBuiltinCall_one
                (orderedFuel := 1 + slack) (by decide) rfl
        | succ residual =>
            have hValueExpr :
                ScopedExprElaborationRunForwardBelow
                  (residual + 1) (slack + 2)
                  builtinContext contract := by
              intro childFuel hChild
              exact hExpr 2 childFuel (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (exprValuesRunForward_of_scoped_elaborated_memoryguard_below
                (slack := slack) (valueFuel := residual)
                hValueExpr hContext hElab hNormalized)
      · by_cases hClzName : name = "clz"
        · subst name
          exact hClz hContext hElab hNormalized
        · cases hClass : CallClass.classifyCall name with
          | primitive =>
              have hArgExpr :
                  ScopedExprElaborationRunForwardBelow
                    fuel slack builtinContext contract := by
                intro childFuel hChild
                exact hExpr 0 childFuel (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (exprValuesRunForward_of_scoped_elaborated_primitiveCall_below
                  (slack := slack) (argsFuel := fuel)
                  hArgExpr hContext hMemoryguard hClzName hClass
                  hElab hNormalized
                  (fun op _hOp stateAfterArgs values =>
                    primitiveRunForward_slack fuel slack
                      stateAfterArgs op values.reverse))
          | user =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_userCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hRecursiveExpr :
                      ScopedExprElaborationRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hExpr 0
                  have hRecursiveBlock :
                      ScopedBlockElaborationRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hBlock
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                    (exprValuesRunForward_of_scoped_elaborated_userCall_below
                      (slack := slack) (callFuel := residual)
                      hRecursiveExpr hRecursiveBlock hContext
                      hMemoryguard hClzName hClass hElab hNormalized)
          | objectBuiltin =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_objectBuiltinCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hObjectName := classifyCall_objectBuiltin_mem hClass
                  simp [CallClass.objectBuiltins] at hObjectName
                  rcases hObjectName with
                    (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_datasize
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_dataoffset
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · have hArgExpr :
                        ScopedExprElaborationRunForwardBelow
                          residual (slack + 1)
                          builtinContext contract := by
                      intro childFuel hChild
                      exact hExpr 1 childFuel (by omega)
                    exact
                      exprValuesRunForward_of_scoped_elaborated_datacopy_below
                        (slack := slack) (argsFuel := residual)
                        hArgExpr hContext hElab hNormalized
                  · rcases objectBuiltinCall_elaboration_parts
                        hMemoryguard hClzName hClass hElab with
                      ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
                    exact False.elim
                      (ExprNormalized.setimmutable_call_false hNormalized)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_loadimmutable
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_linkersymbol
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact False.elim (hMemoryguard rfl)
          | dialectBuiltin =>
              unfold Elab.Expr.elaborate at hElab
              simp [StateT.run_bind] at hElab
              cases hArgs :
                  (Elab.Expr.List.elaborate rawArgs).run elabState with
              | error err => simp [hArgs] at hElab
              | ok argsResult =>
                  rcases argsResult with ⟨frontArgs, argsState⟩
                  simp [hArgs, hClass] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  exact False.elim
                    (ExprNormalized.dialect_call_false hNormalized)

/-- Generic path-scoped successor expression constructor. Every accepted raw
expression class is covered using only lower source fuel, occurrence-local
elaboration paths, and path-aware lexical function bindings. -/
theorem scopedExprPathRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hClz :
      ClzPathRunForwardAt
        (fuel + 1) slack builtinContext contract) :
    ScopedExprPathRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  cases rawExpr with
  | literal literal =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_literal
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | identifier name =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_identifier
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | functionCall name rawArgs =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases fuel with
        | zero =>
            exact
              exprValuesRunForward_objectBuiltinCall_one
                (orderedFuel := 1 + slack) (by decide) rfl
        | succ residual =>
            have hValueExpr :
                ScopedExprPathRunForwardBelow
                  (residual + 1) (slack + 2)
                  builtinContext contract := by
              intro childFuel hChild
              exact hExpr 2 childFuel (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (exprValuesRunForward_of_path_elaborated_memoryguard_below
                (slack := slack) (valueFuel := residual)
                hValueExpr hContext hPath hElab hNormalized)
      · by_cases hClzName : name = "clz"
        · subst name
          exact hClz hContext hPath hElab hNormalized
        · cases hClass : CallClass.classifyCall name with
          | primitive =>
              have hArgExpr :
                  ScopedExprPathRunForwardBelow
                    fuel slack builtinContext contract := by
                intro childFuel hChild
                exact hExpr 0 childFuel (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (exprValuesRunForward_of_path_elaborated_primitiveCall_below
                  (slack := slack) (argsFuel := fuel)
                  hArgExpr hContext hPath hMemoryguard hClzName hClass
                  hElab hNormalized
                  (fun op _hOp stateAfterArgs values =>
                    primitiveRunForward_slack fuel slack
                      stateAfterArgs op values.reverse))
          | user =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_userCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hRecursiveExpr :
                      ScopedExprPathRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hExpr 0
                  have hRecursiveBlock :
                      ScopedBlockPathRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hBlock
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                    (exprValuesRunForward_of_path_elaborated_userCall_below
                      (slack := slack) (callFuel := residual)
                      hRecursiveExpr hRecursiveBlock hContext hPath
                      hMemoryguard hClzName hClass hElab hNormalized)
          | objectBuiltin =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_objectBuiltinCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hObjectName := classifyCall_objectBuiltin_mem hClass
                  simp [CallClass.objectBuiltins] at hObjectName
                  rcases hObjectName with
                    (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_datasize
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_dataoffset
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · have hArgExpr :
                        ScopedExprPathRunForwardBelow
                          residual (slack + 1)
                          builtinContext contract := by
                      intro childFuel hChild
                      exact hExpr 1 childFuel (by omega)
                    exact
                      exprValuesRunForward_of_path_elaborated_datacopy_below
                        (slack := slack) (argsFuel := residual)
                        hArgExpr hContext hPath hElab hNormalized
                  · rcases objectBuiltinCall_elaboration_parts
                        hMemoryguard hClzName hClass hElab with
                      ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
                    exact False.elim
                      (ExprNormalized.setimmutable_call_false hNormalized)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_loadimmutable
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_linkersymbol
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact False.elim (hMemoryguard rfl)
          | dialectBuiltin =>
              unfold Elab.Expr.elaborate at hElab
              simp [StateT.run_bind] at hElab
              cases hArgs :
                  (Elab.Expr.List.elaborate rawArgs).run elabState with
              | error err => simp [hArgs] at hElab
              | ok argsResult =>
                  rcases argsResult with ⟨frontArgs, argsState⟩
                  simp [hArgs, hClass] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  exact False.elim
                    (ExprNormalized.dialect_call_false hNormalized)

/-- Exact pre-block statement preservation used by the recursive frontend
proof. Lexical-store restriction is handled only by block constructors. -/
def StmtRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawStmt : Raw.Stmt) (orderedStmt : Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.exec rawFuel context rawStmt state)
    (Yul.InteractionSemantics.exec orderedFuel orderedStmt
      (some contract) state)

/-- Statement preservation inside one lexical block. Regular outcomes remain
exact; only abrupt outcomes may expose the administrative store restriction
introduced by an erased nested function declaration. -/
def ScopedStmtRunForward (entryStore : EvmYul.Yul.VarStore)
    (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawStmt : Raw.Stmt) (orderedStmt : Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    (BlockSeqDoneRel entryStore)
    (Raw.SourceSemantics.exec rawFuel context rawStmt state)
    (Yul.InteractionSemantics.exec orderedFuel orderedStmt
      (some contract) state)

theorem scopedStmtRunForward_of_exact
    {entryStore : EvmYul.Yul.VarStore}
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {orderedStmt : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExact :
      StmtRunForward rawFuel orderedFuel
        context rawStmt orderedStmt contract state) :
    ScopedStmtRunForward entryStore rawFuel orderedFuel
      context rawStmt orderedStmt contract state := by
  unfold StmtRunForward ScopedStmtRunForward at *
  apply Simulation.Interaction.ForwardRel.mono hExact
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ExceptRel.error rfl
  | ok rawState =>
      cases rawState with
      | Ok => exact Simulation.Interaction.ExceptRel.ok rfl
      | OutOfFuel => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)
      | Checkpoint => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)

theorem stmtRunForward_zero
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {orderedStmt : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward 0 orderedFuel
      context rawStmt orderedStmt contract state := by
  unfold StmtRunForward
  rw [show Raw.SourceSemantics.exec 0 context rawStmt state =
      Raw.SourceSemantics.fail state .OutOfFuel by
    simp [Raw.SourceSemantics.exec]]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem stmtRunForward_variableDeclaration_none_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {names : List Name}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.variableDeclaration names none) (.Let names none)
      contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.variableDeclaration_none_succ]
  cases hCheck : EvmYul.Yul.checkDeclaration state names with
  | error error =>
      unfold Yul.InteractionSemantics.exec Yul.Source.Canonical.exec
        Yul.Source.Effectful.exec
      simp only [Yul.InteractionSemantics.stateModel, id_eq, hCheck]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      cases result
      rw [Yul.InteractionSemantics.Exec.let_none_succ
        orderedFuel names (some contract) state hCheck]
      exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_variableDeclaration_some_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {names : List Name} {rawExpr : Raw.Expr}
    {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.variableDeclaration names (some rawExpr))
      (.Let names (some orderedExpr)) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.variableDeclaration_some_succ]
  cases hCheck : EvmYul.Yul.checkDeclaration state names with
  | error error =>
      unfold Yul.InteractionSemantics.exec Yul.Source.Canonical.exec
        Yul.Source.Effectful.exec
      simp only [Yul.InteractionSemantics.stateModel, id_eq, hCheck]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      cases result
      rw [Yul.InteractionSemantics.Exec.let_some_succ
        orderedFuel names orderedExpr (some contract) state hCheck]
      unfold ExprValuesRunForward at hValues
      refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
      intro rawDone orderedDone hDone
      unfold SameDoneRel at hDone
      subst orderedDone
      cases rawDone with
      | error error => exact Simulation.Interaction.ForwardRel.done rfl
      | ok result => exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_assignment_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {names : List Name} {rawExpr : Raw.Expr}
    {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.assignment names rawExpr)
      (.Assign names orderedExpr) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.assignment_succ]
  cases hCheck : EvmYul.Yul.checkAssignment state names with
  | error error =>
      unfold Yul.InteractionSemantics.exec Yul.Source.Canonical.exec
        Yul.Source.Effectful.exec
      simp only [Yul.InteractionSemantics.stateModel, id_eq, hCheck]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      cases result
      rw [Yul.InteractionSemantics.Exec.assign_succ
        orderedFuel names orderedExpr (some contract) state hCheck]
      unfold ExprValuesRunForward at hValues
      refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
      intro rawDone orderedDone hDone
      unfold SameDoneRel at hDone
      subst orderedDone
      cases rawDone with
      | error error => exact Simulation.Interaction.ForwardRel.done rfl
      | ok result => exact Simulation.Interaction.ForwardRel.done rfl

/-- Primitive expression statements consume the shared expression simulation
and discard its values through the canonical empty destination list. -/
theorem stmtRunForward_expressionStatement_primitive_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {op : EvmYul.Operation .Yul}
    {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hNotSetimmutable : name ≠ "setimmutable")
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel context
        (.functionCall name rawArgs) (.Call (.inl op) orderedArgs)
        contract state) :
    StmtRunForward (rawFuel + 1) orderedFuel context
      (.expressionStatement (.functionCall name rawArgs))
      (.ExprStmtCall (.Call (.inl op) orderedArgs)) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable]
  rw [Yul.InteractionSemantics.Exec.expr_primitive]
  unfold ExprValuesRunForward at hValues
  refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      rcases result with ⟨stateAfterExpr, values⟩
      cases stateAfterExpr <;>
        exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_immutablePatchStmt
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {reference : Frontend.ImmutableReference}
    {rawBase rawValue : Raw.Expr} {rawStmt : Raw.Stmt}
    {orderedBase orderedValue : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hPatch :
      Raw.SourceSemantics.patchSetImmutableStmt?
        reference rawBase rawValue = some rawStmt)
    (hBase :
      ∀ extra n, n < fuel → ∀ state,
        ExprRunForward n (n + (slack + extra))
          context rawBase orderedBase contract state)
    (hValue :
      ∀ extra n, n < fuel → ∀ state,
        ExprRunForward n (n + (slack + extra))
          context rawValue orderedValue contract state) :
    StmtRunForward fuel (fuel + slack) context rawStmt
      (orderedImmutablePatchStmt reference orderedBase orderedValue)
      contract state := by
  unfold Raw.SourceSemantics.patchSetImmutableStmt? at hPatch
  split at hPatch
  next hPatchable =>
    simp at hPatch
    subst rawStmt
    cases fuel with
    | zero => exact stmtRunForward_zero
    | succ residual =>
        have hValues :=
          exprValuesRunForward_immutablePatchCall
            (fuel := residual) (slack := slack + 1)
            (context := context) (rawBase := rawBase)
            (rawValue := rawValue) (orderedBase := orderedBase)
            (orderedValue := orderedValue) (reference := reference)
            (contract := contract) (state := state)
            (fun n hN state => hBase 1 n (by omega) state)
            (fun n hN state => hValue 1 n (by omega) state)
        simpa [orderedImmutablePatchStmt, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
          (stmtRunForward_expressionStatement_primitive_succ
            (rawFuel := residual)
            (orderedFuel := residual + (slack + 1))
            (context := context) (name := "mstore")
            (rawArgs :=
              [ .functionCall "add"
                  [rawBase,
                    .literal
                      (.number
                        (EvmYul.UInt256.ofNat reference.start))],
                rawValue ])
            (op := .MSTORE)
            (orderedArgs :=
              [ .Call (.inl .ADD)
                  [orderedBase,
                    .Lit (EvmYul.UInt256.ofNat reference.start)],
                orderedValue ])
            (contract := contract) (state := state)
            (by decide) hValues)
  next hNotPatchable => simp at hPatch

theorem stmtRunForward_expressionStatement_call_one
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hNotSetimmutable : name ≠ "setimmutable") :
    StmtRunForward 1 orderedFuel context
      (.expressionStatement (.functionCall name rawArgs))
      ordered contract state := by
  unfold StmtRunForward
  rw [show 1 = 0 + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable, Raw.SourceSemantics.evalValues,
    Raw.SourceSemantics.fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem stmtRunForward_expressionStatement_userCall_two
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hNotSetimmutable : name ≠ "setimmutable")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user) :
    StmtRunForward 2 orderedFuel context
      (.expressionStatement (.functionCall name rawArgs))
      ordered contract state := by
  unfold StmtRunForward
  rw [show 2 = 1 + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable]
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    0 context name rawArgs state hNotClz]
  simp only [hClass]
  rw [Raw.SourceSemantics.evalArgs_zero]
  unfold Raw.SourceSemantics.fail
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.Primitive.fail state .OutOfFuel :
            Open (State × List Frontend.Word))
          (fun result =>
            Raw.SourceSemantics.call 0 context result.2.reverse
              name result.1))
        (fun result => pure result.1))
      _
  rw [Simulation.Interaction.bind_assoc]
  rw [Yul.InteractionSemantics.Primitive.bind_fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

/-- The expression-statement constructor consumes the same generated-call
evidence with one additional unit of target argument fuel. Callee-body fuel,
lookup, return restoration, and value discard remain shared with value-position
calls. -/
theorem stmtRunForward_expressionStatement_userCall_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun :
      GeneratedUserCallRun rawFuel (orderedFuel + 1) orderedFuel
        context rawName rawArgs generated orderedArgs contract state) :
    StmtRunForward (rawFuel + 3) (orderedFuel + 3)
      context (.expressionStatement (.functionCall rawName rawArgs))
      (.ExprStmtCall (.Call (.inr generated) orderedArgs))
      contract state := by
  have hNotSetimmutable : rawName ≠ "setimmutable" := by
    intro hName
    subst rawName
    have hClass := hRun.callClass
    simp [CallClass.classifyCall, CallClass.objectBuiltins,
      Frontend.Primitive.ofName?] at hClass
  unfold StmtRunForward
  rw [show rawFuel + 3 = (rawFuel + 2) + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable, hRun.notClz]
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context rawName rawArgs state hRun.notClz]
  simp only [hRun.callClass]
  rw [show orderedFuel + 3 = (orderedFuel + 1) + 2 by omega]
  rw [Yul.InteractionSemantics.Exec.expr_internal_succ]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Raw.SourceSemantics.evalArgs (rawFuel + 1) context
            rawArgs.reverse state)
          (fun argsResult =>
            Raw.SourceSemantics.call (rawFuel + 1) context
              argsResult.2.reverse rawName argsResult.1))
        (fun callResult => pure callResult.1))
      _
  rw [Simulation.Interaction.bind_assoc]
  have hArgsForward := hRun.argsForward
  unfold ArgsRunForward at hArgsForward
  refine
    Simulation.Interaction.ForwardRel.bind_custom hArgsForward ?_
  intro rawArgsDone orderedArgsDone hArgsDone
  unfold SameDoneRel at hArgsDone
  subst orderedArgsDone
  cases rawArgsDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok argsResult =>
      rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
      have hCallForward :=
        generatedUserCallRun_call_succ
          (stateAfterArgs := stateAfterArgs)
          (reversedValues := reversedValues) hRun
      refine
        Simulation.Interaction.ForwardRel.bind_custom hCallForward ?_
      intro rawCallDone orderedCallDone hCallDone
      unfold SameDoneRel at hCallDone
      subst orderedCallDone
      cases rawCallDone with
      | error error => exact Simulation.Interaction.ForwardRel.done rfl
      | ok callResult =>
          rcases callResult with ⟨stateAfterCall, values⟩
          cases stateAfterCall <;>
            exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_expressionStatement_generatedClz
    {rawArgFuel orderedBase : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {generated : Name}
    {orderedArg : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2)
        (orderedBase + 2) context rawArg generated orderedArg
        contract state) :
    StmtRunForward (rawArgFuel + 2) (orderedBase + 4)
      context (.expressionStatement (.functionCall "clz" [rawArg]))
      (.ExprStmtCall (.Call (.inr generated) [orderedArg]))
      contract state := by
  unfold StmtRunForward
  rw [show rawArgFuel + 2 = (rawArgFuel + 1) + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp
  rw [Raw.SourceSemantics.EvalValues.clz_succ]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Raw.SourceSemantics.eval rawArgFuel context rawArg state)
          (fun result =>
            match result.1 with
            | .Ok _ _ =>
                pure
                  (result.1,
                    [Elab.ClzHelperModel.reference result.2])
            | .OutOfFuel | .Checkpoint _ =>
                Raw.SourceSemantics.fail result.1 .OutOfFuel))
        (fun result => pure result.1))
      _
  rw [Simulation.Interaction.bind_assoc]
  rw [show orderedBase + 4 = (orderedBase + 2) + 2 by omega]
  rw [Yul.InteractionSemantics.Exec.expr_internal_succ]
  simp only [List.reverse_singleton]
  rw [orderedEvalArgs_single]
  simp only [Simulation.Interaction.bind_assoc]
  have hArg := hRun.argForward
  unfold ExprRunForward at hArg
  refine Simulation.Interaction.ForwardRel.bind_custom hArg ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      rcases result with ⟨stateAfterArg, value⟩
      cases stateAfterArg with
      | OutOfFuel =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
      | Checkpoint jump =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
      | Ok shared store =>
          simp only [Simulation.Interaction.instMonad,
            Simulation.Interaction.pure, Simulation.Interaction.bind,
            List.reverse_singleton]
          rw [Raw.ClzPreservation.clzHelperCall
            hRun.binding.namesDistinct hRun.binding.orderedLookup
            hRun.binding.bodyToYul shared store value
            (orderedBase + 2) hRun.bodyFuel]
          exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_of_path_elaborated_clz
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        context elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack) :
    StmtRunForward (rawArgFuel + 2) ((rawArgFuel + 2) + slack)
      context (.expressionStatement (.functionCall "clz" rawArgs))
      (.ExprStmtCall ordered) contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  have hArgExt :=
    Elab.Expr.elaborate_preserves_clzAllocation rawArg
      hArgElab hPath.entryValid
  have hEnsureExt :=
    Elab.ensureClzHelper_preserves_clzAllocation
      hEnsure hArgExt.after_valid
  have hArgPath :
      ClzCompilationPath contract elabState argState :=
    hPath.prefixPath hEnsureExt
  have hArgValues :=
    hExpr (state := state) hContext hArgPath hArgElab hArgNormalized
  have hArgRun := exprRunForward_of_values hArgValues
  rcases Elab.ensureClzHelper_allocated hEnsure hArgExt.after_valid with
    ⟨argName, returnName, hAllocated⟩
  rcases hPath.finalResolver hAllocated with ⟨binding⟩
  let orderedBase := rawArgFuel + slack - 2
  have hBase : orderedBase + 2 = rawArgFuel + slack := by
    dsimp [orderedBase]
    omega
  have hBodyFuel :
      Raw.ClzPreservation.stmtListFuel
          (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
        orderedBase + 2 := by
    rw [Raw.ClzPreservation.helperBodyFuel_eq]
    dsimp [orderedBase]
    omega
  have hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2)
        (orderedBase + 2) context rawArg generated orderedArg
        contract state :=
    { binding := binding
      bodyFuel := hBodyFuel
      argForward := by simpa [hBase] using hArgRun }
  have hCall := stmtRunForward_expressionStatement_generatedClz hRun
  have hTargetEq :
      orderedBase + 4 = rawArgFuel + 2 + slack := by
    dsimp [orderedBase]
    omega
  rw [hTargetEq] at hCall
  exact hCall

/-- Every accepted ordinary call statement is derived from checked
elaboration and normalization. Generated user calls use the bundled occurrence
interface; primitive and `datacopy` statements consume the generic expression
simulation. Only `clz` and `setimmutable` remain separate frontend-owned
normalizations. -/
theorem scopedStmtRunForward_of_path_elaborated_callStatement_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotClz : name ≠ "clz")
    (hNotSetimmutable : name ≠ "setimmutable")
    (hElab :
      (Elab.Stmt.elaborate
        (.expressionStatement (.functionCall name rawArgs))).run
          elabState = .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 1) ((fuel + 1) + slack)
      rawContext (.expressionStatement (.functionCall name rawArgs))
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  cases hSupported :
      CallClass.supportedExpressionStatementCall? name with
  | false =>
      simp [hSupported] at hElab
      change
        (Except.error "unsupported Yul expression statement call" :
          Except String (Frontend.Stmt × Elab.State)) =
            .ok (front, finalElabState) at hElab
      cases hElab
  | true =>
      simp [hSupported, StateT.run_bind] at hElab
      cases hExprElab :
          (Elab.Expr.elaborate (.functionCall name rawArgs)).run
            elabState with
      | error err => simp [hExprElab] at hElab
      | ok exprResult =>
          rcases exprResult with ⟨frontExpr, exprState⟩
          simp [hExprElab] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          have hNotMemoryguard : name ≠ "memoryguard" := by
            intro hName
            subst name
            have hRejected :
                CallClass.supportedExpressionStatementCall?
                    "memoryguard" = false := by
              rfl
            rw [hRejected] at hSupported
            cases hSupported
          cases hClass : CallClass.classifyCall name with
          | primitive =>
              rcases functionCall_elaboration_kind_parts
                  hNotMemoryguard hNotClz hClass hExprElab with
                ⟨callee, frontArgs, rfl⟩
              rcases StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                  (Or.inl (by intro hKind; cases hKind)) hNormalized with
                ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
              rcases ExprNormalized.primitive_call_parts hExprNormalized with
                ⟨op, orderedArgs, hOp, rfl, hArgsNormalized⟩
              have hValues :=
                hExpr 1 fuel (by omega) (state := state)
                  hContext hPath hExprElab hExprNormalized
              apply scopedStmtRunForward_of_exact
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using
                  (stmtRunForward_expressionStatement_primitive_succ
                    hNotSetimmutable hValues)
          | user =>
              rcases functionCall_elaboration_kind_parts
                  hNotMemoryguard hNotClz hClass hExprElab with
                ⟨generated, frontArgs, rfl⟩
              rcases StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                  (Or.inl (by intro hKind; cases hKind)) hNormalized with
                ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
              cases fuel with
              | zero =>
                  exact scopedStmtRunForward_of_exact
                    (stmtRunForward_expressionStatement_call_one
                      (orderedFuel := 1 + slack)
                      hNotSetimmutable)
              | succ predecessor =>
                  cases predecessor with
                  | zero =>
                      exact scopedStmtRunForward_of_exact
                        (stmtRunForward_expressionStatement_userCall_two
                          (orderedFuel := 2 + slack)
                          hNotSetimmutable hNotClz hClass)
                  | succ callFuel =>
                      have hArgsExpr :
                          ScopedExprPathRunForwardBelow
                            (callFuel + 2) (slack + 1)
                            builtinContext contract := by
                        intro childFuel hChild
                        exact hExpr 1 childFuel (by omega)
                      have hBodyBlock :
                          ScopedBlockPathRunForwardBelow
                            (callFuel + 2) slack
                            builtinContext contract := by
                        intro childFuel hChild
                        exact hBlock childFuel (by omega)
                      rcases generatedUserCallRun_of_path_elaboration_below
                          hArgsExpr hBodyBlock hContext hPath
                          hNotMemoryguard hNotClz hClass
                          hExprElab hExprNormalized with
                        ⟨resolved, orderedArgs, hOrdered, ⟨hRun⟩⟩
                      cases hOrdered
                      apply scopedStmtRunForward_of_exact
                      simpa [Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using
                          (stmtRunForward_expressionStatement_userCall_succ
                            hRun)
          | objectBuiltin =>
              have hObject :
                  name = "datacopy" ∨ name = "setimmutable" := by
                unfold CallClass.supportedExpressionStatementCall?
                  at hSupported
                simp [hClass] at hSupported
                exact hSupported
              rcases hObject with hDatacopy | hSetimmutable
              · subst name
                rcases objectBuiltinCall_elaboration_parts
                    hNotMemoryguard hNotClz hClass hExprElab with
                  ⟨frontArgs, argsState, hArgsElab, hFront, hFinal⟩
                subst frontExpr
                subst exprState
                rcases
                    StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                      (Or.inr (by decide)) hNormalized with
                  ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
                rcases ExprNormalized.datacopy_parts hExprNormalized with
                  ⟨target, offset, size, orderedArgs, op,
                    hArgs, hOp, rfl, hArgsNormalized⟩
                have hValues :=
                  hExpr 1 fuel (by omega) (state := state)
                    hContext hPath hExprElab hExprNormalized
                apply scopedStmtRunForward_of_exact
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using
                    (stmtRunForward_expressionStatement_primitive_succ
                      (by decide) hValues)
              · exact False.elim (hNotSetimmutable hSetimmutable)
          | dialectBuiltin =>
              unfold CallClass.supportedExpressionStatementCall?
                at hSupported
              simp [hClass] at hSupported

theorem stmtRunForward_block_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hBlock :
      BlockCodeRunForward rawFuel orderedFuel
        context rawCode orderedCode contract state) :
    StmtRunForward (rawFuel + 1) orderedFuel
      context (.block rawCode) (.Block orderedCode) contract state := by
  unfold StmtRunForward BlockCodeRunForward at *
  rw [Raw.SourceSemantics.Exec.block_succ]
  exact hBlock

theorem stmtRunForward_ifThen_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {orderedCondition : Frontend.AstExpr}
    {rawBody : List Raw.Stmt} {orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hCondition :
      ExprRunForward rawFuel orderedFuel
        context rawCondition orderedCondition contract state)
    (hBody :
      ∀ (stateAfterCondition : State) (value : Frontend.Word),
        value ≠ EvmYul.UInt256.ofNat 0 →
          BlockCodeRunForward rawFuel orderedFuel
            context rawBody orderedBody contract stateAfterCondition) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.ifThen rawCondition rawBody)
      (.If orderedCondition orderedBody) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.ifThen_succ]
  rw [Yul.InteractionSemantics.Exec.if_succ]
  unfold ExprRunForward at hCondition
  refine Simulation.Interaction.ForwardRel.bind_custom hCondition ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok conditionResult =>
      rcases conditionResult with ⟨stateAfterCondition, value⟩
      change
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
          (if value ≠ EvmYul.UInt256.ofNat 0 then
            Raw.SourceSemantics.execBlock rawFuel context rawBody
              stateAfterCondition
          else
            pure stateAfterCondition)
          (if value ≠ EvmYul.UInt256.ofNat 0 then
            Yul.InteractionSemantics.exec orderedFuel (.Block orderedBody)
              (some contract) stateAfterCondition
          else
            pure stateAfterCondition)
      split
      case isTrue hRawTruthy =>
        exact hBody stateAfterCondition value hRawTruthy
      case isFalse hRawFalse =>
        exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_switch_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {orderedCondition : Frontend.AstExpr}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {rawDefault : List Raw.Stmt}
    {orderedCases : List (Frontend.Word × List Frontend.AstStmt)}
    {orderedDefault : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hCondition :
      ExprRunForward rawFuel orderedFuel
        context rawCondition orderedCondition contract state)
    (hCases :
      SwitchCasesRunForward rawFuel orderedFuel context
        rawCases rawDefault orderedCases orderedDefault contract) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.switch rawCondition rawCases rawDefault)
      (.Switch orderedCondition orderedCases orderedDefault)
      contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.switch_succ]
  rw [Yul.InteractionSemantics.Exec.switch_succ]
  unfold ExprRunForward at hCondition
  refine Simulation.Interaction.ForwardRel.bind_custom hCondition ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok conditionResult =>
      rcases conditionResult with ⟨stateAfterCondition, value⟩
      rcases hCases stateAfterCondition value with
        ⟨rawBody, orderedBody, hRawSelected, hOrderedSelected, hBody⟩
      simp only [hRawSelected, hOrderedSelected]
      exact hBody

private theorem loopZeroReentryRunForward
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {entry source : State} :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (do
        let stateAfterLoop ←
          Raw.SourceSemantics.loop 0 context rawCondition rawPost rawBody entry
        pure (stateAfterLoop.overwrite? source))
      (do
        let stateAfterLoop ←
          Yul.InteractionSemantics.exec orderedFuel
            (.For orderedCondition orderedPost orderedBody)
            (some contract) entry
        pure (stateAfterLoop.overwrite? source)) := by
  rw [Raw.SourceSemantics.Loop.zero]
  unfold Raw.SourceSemantics.fail
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.Primitive.fail entry .OutOfFuel)
        (fun stateAfterLoop : State =>
          (pure (stateAfterLoop.overwrite? source) : Open State)))
      _
  rw [Yul.InteractionSemantics.Primitive.bind_fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

private theorem loopReentryRunForward
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {entry source : State}
    (hLoop :
      LoopRunForward fuel (fuel + slack) context
        rawCondition rawPost rawBody orderedCondition
        orderedPost orderedBody contract entry) :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (do
        let stateAfterLoop ←
          Raw.SourceSemantics.loop fuel context
            rawCondition rawPost rawBody entry
        pure (stateAfterLoop.overwrite? source))
      (do
        let stateAfterLoop ←
          Yul.InteractionSemantics.exec (fuel + slack + 1)
            (.For orderedCondition orderedPost orderedBody)
            (some contract) entry
        pure (stateAfterLoop.overwrite? source)) := by
  rw [Yul.InteractionSemantics.Exec.for_succ]
  refine Simulation.Interaction.ForwardRel.bind_custom hLoop ?_
  intro rawLoopDone orderedLoopDone hLoopDone
  unfold SameDoneRel at hLoopDone
  subst orderedLoopDone
  cases rawLoopDone <;>
    exact Simulation.Interaction.ForwardRel.done rfl

private theorem orderedExecSeq_append
    {fuel : Nat} {pre suffix : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hPre : pre ≠ []) :
    Yul.InteractionSemantics.execSeq fuel
        (pre ++ suffix) (some contract) state =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.execSeq fuel
          pre (some contract) state)
        (fun stateAfterPre =>
          match stateAfterPre with
          | .Ok _ _ =>
              Yul.InteractionSemantics.execSeq (fuel - pre.length) suffix
                (some contract) stateAfterPre
          | .OutOfFuel | .Checkpoint _ => pure stateAfterPre) := by
  induction pre generalizing fuel state with
  | nil => exact (hPre rfl).elim
  | cons head rest ih =>
      cases fuel with
      | zero =>
          simp [Yul.InteractionSemantics.ExecSeq.zero,
            Yul.InteractionSemantics.Primitive.fail]
      | succ residual =>
          rw [List.cons_append]
          rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
          rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
          rw [Simulation.Interaction.bind_assoc]
          apply congrArg
          funext stateAfterHead
          cases stateAfterHead with
          | OutOfFuel => rfl
          | Checkpoint jump => rfl
          | Ok shared vars =>
              cases rest with
              | nil =>
                  cases residual with
                  | zero =>
                      simp [Yul.InteractionSemantics.ExecSeq.zero,
                        Yul.InteractionSemantics.Primitive.fail]
                  | succ tailFuel =>
                      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
                      change _ =
                        Simulation.Interaction.bind
                          (Simulation.Interaction.done
                            (.ok (EvmYul.Yul.State.Ok shared vars))) _
                      rw [Simulation.Interaction.bind_done_ok]
                      simp
              | cons next tail =>
                  rw [ih (by simp)]
                  simp only [List.length_cons]
                  rw [show residual - (tail.length + 1) =
                    residual + 1 - (tail.length + 1 + 1) by omega]

private theorem orderedExecSeq_append_of_nonempty
    {fuel : Nat} {pre suffix : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hPre : pre ≠ []) :
    Yul.InteractionSemantics.execSeq (fuel + pre.length)
        (pre ++ suffix) (some contract) state =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.execSeq (fuel + pre.length)
          pre (some contract) state)
        (fun stateAfterPre =>
          match stateAfterPre with
          | .Ok _ _ =>
              Yul.InteractionSemantics.execSeq fuel suffix
                (some contract) stateAfterPre
          | .OutOfFuel | .Checkpoint _ => pure stateAfterPre) := by
  simpa using
    (orderedExecSeq_append (fuel := fuel + pre.length) hPre)

/-- A regularly completed raw statement list must have consumed fewer list
steps than the supplied source fuel. Abrupt states and errors impose no bound;
they never enter an appended continuation. -/
def RawSeqRegularFuelBound (fuel : Nat) (code : List Raw.Stmt) :
    Except Failure State → Prop
  | .ok (.Ok _ _) => code.length < fuel
  | .error _ | .ok .OutOfFuel | .ok (.Checkpoint _) => True

theorem rawExecSeq_allDone_regular_fuel_bound
    (fuel : Nat) (context : Raw.SourceSemantics.Context)
    (code : List Raw.Stmt) (state : State) :
    Simulation.Interaction.AllDone
      (RawSeqRegularFuelBound fuel code)
      (Raw.SourceSemantics.execSeq fuel context code state) := by
  induction fuel generalizing code state with
  | zero =>
      rw [Raw.SourceSemantics.execSeq_zero]
      exact .done (by simp [RawSeqRegularFuelBound])
  | succ fuel ih =>
      cases code with
      | nil =>
          rw [Raw.SourceSemantics.ExecSeq.nil_succ]
          exact .done (by cases state <;> simp [RawSeqRegularFuelBound])
      | cons head rest =>
          rw [Raw.SourceSemantics.ExecSeq.cons_succ]
          refine
            Simulation.Interaction.AllDone.bind
              (Simulation.Interaction.AllDone.trivial
                (Raw.SourceSemantics.exec fuel context head state)) ?_ ?_
          · intro error _hError
            simp [RawSeqRegularFuelBound]
          · intro stateAfterHead _hHead
            cases stateAfterHead with
            | OutOfFuel =>
                exact .done (by simp [RawSeqRegularFuelBound])
            | Checkpoint jump =>
                exact .done (by simp [RawSeqRegularFuelBound])
            | Ok shared store =>
                exact
                  Simulation.Interaction.AllDone.mono
                    (ih rest (.Ok shared store)) (by
                      intro outcome hOutcome
                      cases outcome with
                      | error error =>
                          simp [RawSeqRegularFuelBound]
                      | ok finalState =>
                          cases finalState with
                          | OutOfFuel =>
                              simp [RawSeqRegularFuelBound]
                          | Checkpoint jump =>
                              simp [RawSeqRegularFuelBound]
                          | Ok finalShared finalStore =>
                              simp [RawSeqRegularFuelBound] at hOutcome ⊢
                              omega)

private theorem orderedExecSeq_single_for
    {fuel : Nat} {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    Yul.InteractionSemantics.execSeq (fuel + 2)
        [.For condition post body] (some contract) state =
      Yul.InteractionSemantics.loop fuel condition post body
        (some contract) state := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.Exec.for_succ]
  simp only [Yul.InteractionSemantics.ExecSeq.nil_succ]
  have hContinuation :
      (fun stateAfterStmt : State =>
        match stateAfterStmt with
        | .Ok _ _ => (pure stateAfterStmt : Open State)
        | .OutOfFuel | .Checkpoint _ =>
            (pure stateAfterStmt : Open State)) =
        (fun stateAfterStmt => (pure stateAfterStmt : Open State)) := by
    funext stateAfterStmt
    cases stateAfterStmt <;> rfl
  calc
    _ = Simulation.Interaction.bind
        (Yul.InteractionSemantics.loop fuel condition post body
          (some contract) state)
        (fun stateAfterStmt => (pure stateAfterStmt : Open State)) :=
      congrArg
        (fun continuation =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.loop fuel condition post body
              (some contract) state)
            continuation)
        hContinuation
    _ = _ := Simulation.Interaction.monad_bind_pure _

private theorem loopRestrictedRunForward
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    {entryStore : EvmYul.Yul.VarStore}
    (hLoop :
      LoopRunForward rawFuel orderedFuel context
        rawCondition rawPost rawBody orderedCondition
        orderedPost orderedBody contract state) :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (do
        let stateAfterLoop ←
          Raw.SourceSemantics.loop rawFuel context
            rawCondition rawPost rawBody state
        pure (stateAfterLoop.restrictStoreTo entryStore))
      (do
        let stateAfterLoop ←
          Yul.InteractionSemantics.execSeq (orderedFuel + 2)
            [.For orderedCondition orderedPost orderedBody]
            (some contract) state
        pure (stateAfterLoop.restrictStoreTo entryStore)) := by
  rw [orderedExecSeq_single_for]
  refine Simulation.Interaction.ForwardRel.bind_custom hLoop ?_
  intro rawLoopDone orderedLoopDone hLoopDone
  unfold SameDoneRel at hLoopDone
  subst orderedLoopDone
  cases rawLoopDone <;>
    exact Simulation.Interaction.ForwardRel.done rfl

theorem loopRunForward_zero
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    LoopRunForward 0 orderedFuel context
      rawCondition rawPost rawBody orderedCondition
      orderedPost orderedBody contract state := by
  unfold LoopRunForward
  rw [Raw.SourceSemantics.Loop.zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem loopRunForward_one
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    LoopRunForward 1 orderedFuel context
      rawCondition rawPost rawBody orderedCondition
      orderedPost orderedBody contract state := by
  unfold LoopRunForward
  rw [Raw.SourceSemantics.Loop.one]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem loopRunForward_of_components
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hCondition :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawCondition orderedCondition contract state)
    (hPost :
      ∀ n, n < fuel → ∀ state,
        BlockCodeRunForward n (n + slack)
          context rawPost orderedPost contract state)
    (hBody :
      ∀ n, n < fuel → ∀ state,
        BlockCodeRunForward n (n + slack)
          context rawBody orderedBody contract state) :
    LoopRunForward fuel (fuel + slack) context
      rawCondition rawPost rawBody orderedCondition
      orderedPost orderedBody contract state := by
  induction fuel using Nat.strong_induction_on generalizing state with
  | h fuel ih =>
      cases fuel with
      | zero =>
          unfold LoopRunForward
          rw [Raw.SourceSemantics.Loop.zero]
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
      | succ predecessor =>
          cases predecessor with
          | zero =>
              unfold LoopRunForward
              rw [Raw.SourceSemantics.Loop.one]
              exact
                Simulation.Interaction.ForwardRel.truncated
                  (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
          | succ residual =>
              unfold LoopRunForward
              rw [show residual + 1 + 1 + slack =
                (residual + slack) + 1 + 1 by omega]
              rw [Raw.SourceSemantics.Loop.succ_succ]
              rw [Yul.InteractionSemantics.Exec.loop_succ_succ]
              simp only [Yul.InteractionSemantics.stateModel, id_eq]
              have hConditionRun :=
                hCondition residual (by omega)
                  (EvmYul.Yul.State.mkOk state)
              refine
                Simulation.Interaction.ForwardRel.bind_custom
                  hConditionRun ?_
              intro rawConditionDone orderedConditionDone hConditionDone
              unfold SameDoneRel at hConditionDone
              subst orderedConditionDone
              cases rawConditionDone with
              | error error =>
                  exact Simulation.Interaction.ForwardRel.done rfl
              | ok conditionResult =>
                  rcases conditionResult with
                    ⟨stateAfterCondition, conditionValue⟩
                  dsimp
                  split
                  next hZero =>
                    have hCanonicalZero :
                        conditionValue = EvmYul.UInt256.ofNat 0 := by
                      simpa [EvmYul.UInt256.ofNat] using hZero
                    simp only [if_pos hCanonicalZero]
                    exact Simulation.Interaction.ForwardRel.done rfl
                  next hZero =>
                    have hCanonicalNonzero :
                        conditionValue ≠ EvmYul.UInt256.ofNat 0 := by
                      simpa [EvmYul.UInt256.ofNat] using hZero
                    simp only [if_neg hCanonicalNonzero]
                    refine
                      Simulation.Interaction.ForwardRel.bind_custom
                        (hBody residual (by omega) stateAfterCondition) ?_
                    intro rawBodyDone orderedBodyDone hBodyDone
                    unfold SameDoneRel at hBodyDone
                    subst orderedBodyDone
                    cases rawBodyDone with
                    | error error =>
                        exact Simulation.Interaction.ForwardRel.done rfl
                    | ok stateAfterBody =>
                        cases stateAfterBody with
                        | OutOfFuel =>
                            exact Simulation.Interaction.ForwardRel.done rfl
                        | Checkpoint jump =>
                            cases jump with
                            | Break shared store =>
                                exact
                                  Simulation.Interaction.ForwardRel.done rfl
                            | Leave shared store =>
                                exact
                                  Simulation.Interaction.ForwardRel.done rfl
                            | Continue shared store =>
                                refine
                                  Simulation.Interaction.ForwardRel.bind_custom
                                    (hPost residual (by omega)
                                      (.Ok shared store)) ?_
                                intro rawPostDone orderedPostDone hPostDone
                                unfold SameDoneRel at hPostDone
                                subst orderedPostDone
                                cases rawPostDone with
                                | error error =>
                                    exact
                                      Simulation.Interaction.ForwardRel.done rfl
                                | ok stateAfterPost =>
                                    cases stateAfterPost with
                                    | OutOfFuel =>
                                        exact
                                          Simulation.Interaction.ForwardRel.done
                                            rfl
                                    | Checkpoint postJump =>
                                        cases postJump with
                                        | Leave postShared postStore =>
                                            exact
                                              Simulation.Interaction.ForwardRel.done
                                                rfl
                                        | Break postShared postStore =>
                                            simp only
                                            cases residual with
                                            | zero =>
                                                exact loopZeroReentryRunForward
                                            | succ recursiveFuel =>
                                                rw [show recursiveFuel + 1 - 1 =
                                                  recursiveFuel by omega]
                                                rw [show recursiveFuel + 1 + slack =
                                                  (recursiveFuel + slack) + 1 by
                                                    omega]
                                                exact loopReentryRunForward
                                                  (ih recursiveFuel (by omega)
                                                      (state :=
                                                        (EvmYul.Yul.State.Checkpoint
                                                          (.Break postShared
                                                            postStore)).overwrite?
                                                              state)
                                                      (fun n hN state =>
                                                        hCondition n (by omega)
                                                          state)
                                                      (fun n hN state =>
                                                        hPost n (by omega) state)
                                                      (fun n hN state =>
                                                        hBody n (by omega) state))
                                        | Continue postShared postStore =>
                                            simp only
                                            cases residual with
                                            | zero =>
                                                exact loopZeroReentryRunForward
                                            | succ recursiveFuel =>
                                                rw [show recursiveFuel + 1 - 1 =
                                                  recursiveFuel by omega]
                                                rw [show recursiveFuel + 1 + slack =
                                                  (recursiveFuel + slack) + 1 by
                                                    omega]
                                                exact loopReentryRunForward
                                                  (ih recursiveFuel (by omega)
                                                      (state :=
                                                        (EvmYul.Yul.State.Checkpoint
                                                          (.Continue postShared
                                                            postStore)).overwrite?
                                                              state)
                                                      (fun n hN state =>
                                                        hCondition n (by omega)
                                                          state)
                                                      (fun n hN state =>
                                                        hPost n (by omega) state)
                                                      (fun n hN state =>
                                                        hBody n (by omega) state))
                                    | Ok postShared postStore =>
                                        simp only
                                        cases residual with
                                        | zero =>
                                            exact loopZeroReentryRunForward
                                        | succ recursiveFuel =>
                                            rw [show recursiveFuel + 1 - 1 =
                                              recursiveFuel by omega]
                                            rw [show recursiveFuel + 1 + slack =
                                              (recursiveFuel + slack) + 1 by
                                                omega]
                                            exact loopReentryRunForward
                                              (ih recursiveFuel (by omega)
                                                  (state :=
                                                    (EvmYul.Yul.State.Ok
                                                      postShared postStore).overwrite?
                                                      state)
                                                  (fun n hN state =>
                                                    hCondition n (by omega)
                                                      state)
                                                  (fun n hN state =>
                                                    hPost n (by omega) state)
                                                  (fun n hN state =>
                                                    hBody n (by omega) state))
                        | Ok shared store =>
                            refine
                              Simulation.Interaction.ForwardRel.bind_custom
                                (hPost residual (by omega) (.Ok shared store)) ?_
                            intro rawPostDone orderedPostDone hPostDone
                            unfold SameDoneRel at hPostDone
                            subst orderedPostDone
                            cases rawPostDone with
                            | error error =>
                                exact Simulation.Interaction.ForwardRel.done rfl
                            | ok stateAfterPost =>
                                cases stateAfterPost with
                                | OutOfFuel =>
                                    exact
                                      Simulation.Interaction.ForwardRel.done rfl
                                | Checkpoint postJump =>
                                    cases postJump with
                                    | Leave postShared postStore =>
                                        exact
                                          Simulation.Interaction.ForwardRel.done
                                            rfl
                                    | Break postShared postStore =>
                                        simp only
                                        cases residual with
                                        | zero =>
                                            exact loopZeroReentryRunForward
                                        | succ recursiveFuel =>
                                            rw [show recursiveFuel + 1 - 1 =
                                              recursiveFuel by omega]
                                            rw [show recursiveFuel + 1 + slack =
                                              (recursiveFuel + slack) + 1 by
                                                omega]
                                            exact loopReentryRunForward
                                              (ih recursiveFuel (by omega)
                                                  (state :=
                                                    (EvmYul.Yul.State.Checkpoint
                                                      (.Break postShared
                                                        postStore)).overwrite? state)
                                                  (fun n hN state =>
                                                    hCondition n (by omega) state)
                                                  (fun n hN state =>
                                                    hPost n (by omega) state)
                                                  (fun n hN state =>
                                                    hBody n (by omega) state))
                                    | Continue postShared postStore =>
                                        simp only
                                        cases residual with
                                        | zero =>
                                            exact loopZeroReentryRunForward
                                        | succ recursiveFuel =>
                                            rw [show recursiveFuel + 1 - 1 =
                                              recursiveFuel by omega]
                                            rw [show recursiveFuel + 1 + slack =
                                              (recursiveFuel + slack) + 1 by
                                                omega]
                                            exact loopReentryRunForward
                                              (ih recursiveFuel (by omega)
                                                  (state :=
                                                    (EvmYul.Yul.State.Checkpoint
                                                      (.Continue postShared
                                                        postStore)).overwrite? state)
                                                  (fun n hN state =>
                                                    hCondition n (by omega) state)
                                                  (fun n hN state =>
                                                    hPost n (by omega) state)
                                                  (fun n hN state =>
                                                    hBody n (by omega) state))
                                | Ok postShared postStore =>
                                    simp only
                                    cases residual with
                                    | zero =>
                                        exact loopZeroReentryRunForward
                                    | succ recursiveFuel =>
                                        rw [show recursiveFuel + 1 - 1 =
                                          recursiveFuel by omega]
                                        rw [show recursiveFuel + 1 + slack =
                                          (recursiveFuel + slack) + 1 by omega]
                                        exact loopReentryRunForward
                                          (ih recursiveFuel (by omega)
                                              (state :=
                                                (EvmYul.Yul.State.Ok
                                                  postShared postStore).overwrite?
                                                  state)
                                              (fun n hN state =>
                                                hCondition n (by omega) state)
                                              (fun n hN state =>
                                                hPost n (by omega) state)
                                                  (fun n hN state =>
                                                    hBody n (by omega) state))

/-- Enter a loop after a nonempty statement prefix. If the prefix exhausts
source fuel, zero/one truncation is immediate; otherwise the common recursive
component slack survives the administrative subtraction exactly. -/
theorem loopRunForward_after_nonemptyPrefix
    {fuel slack prefixLength : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {rawPost rawBody : List Raw.Stmt}
    {orderedCondition : Frontend.AstExpr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hCondition :
      ∀ n, n < fuel → ∀ state,
        ExprRunForward n (n + slack)
          context rawCondition orderedCondition contract state)
    (hPost :
      ∀ n, n < fuel → ∀ state,
        BlockCodeRunForward n (n + slack)
          context rawPost orderedPost contract state)
    (hBody :
      ∀ n, n < fuel → ∀ state,
        BlockCodeRunForward n (n + slack)
          context rawBody orderedBody contract state) :
    LoopRunForward (fuel - prefixLength - 1)
      (fuel + slack - prefixLength - 1)
      context rawCondition rawPost rawBody orderedCondition
      orderedPost orderedBody contract state := by
  by_cases hLoopFuel : prefixLength + 3 ≤ fuel
  · have hTargetFuel :
        fuel + slack - prefixLength - 1 =
          (fuel - prefixLength - 1) + slack := by
      omega
    rw [hTargetFuel]
    exact
      loopRunForward_of_components
        (fun n hN state => hCondition n (by omega) state)
        (fun n hN state => hPost n (by omega) state)
        (fun n hN state => hBody n (by omega) state)
  · have hSmall : fuel - prefixLength - 1 ≤ 1 := by omega
    cases hSourceFuel : fuel - prefixLength - 1 with
    | zero => exact loopRunForward_zero
    | succ residual =>
        have hResidual : residual = 0 := by omega
        subst residual
        exact loopRunForward_one

theorem stmtRunForward_for_nonempty
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawPre rawPost rawBody : List Raw.Stmt}
    {rawCondition : Raw.Expr}
    {orderedPre orderedPost orderedBody : List Frontend.AstStmt}
    {orderedCondition : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hScope : Raw.SourceSemantics.functionScope? rawPre = some scope)
    (hLength : orderedPre.length = rawPre.length)
    (hNonempty : orderedPre ≠ [])
    (hPre :
      Simulation.Interaction.ForwardRel
        Yul.FunctionsInteractionPrimitive.Truncated
        (BlockSeqDoneRel state.store)
        (Raw.SourceSemantics.execSeq fuel
          (context.withFunctionScope scope) rawPre state)
        (Yul.InteractionSemantics.execSeq (fuel + (slack + 1))
          orderedPre (some contract) state))
    (hLoop :
      ∀ loopState,
        LoopRunForward (fuel - rawPre.length - 1)
          (fuel + slack - rawPre.length - 1)
          (context.withFunctionScope scope)
          rawCondition rawPost rawBody orderedCondition
          orderedPost orderedBody contract loopState) :
    StmtRunForward (fuel + 2) (fuel + 2 + slack)
      context (.forLoop rawPre rawCondition rawPost rawBody)
      (.Block
        (orderedPre ++
          [.For orderedCondition orderedPost orderedBody]))
      contract state := by
  have hRawNonempty : rawPre ≠ [] := by
    intro hRaw
    subst rawPre
    have hOrderedLength : orderedPre.length = 0 := by
      simpa using hLength
    exact hNonempty (List.eq_nil_of_length_eq_zero hOrderedLength)
  obtain ⟨rawHead, rawTail, rfl⟩ :=
    List.exists_cons_of_ne_nil hRawNonempty
  unfold StmtRunForward
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [Raw.SourceSemantics.Exec.forLoop_succ]
  rw [Raw.SourceSemantics.ExecFor.succ]
  simp only [hScope]
  rw [show fuel + 2 + slack = (fuel + 1 + slack) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  rw [orderedExecSeq_append hNonempty]
  simp only [Simulation.Interaction.bind_assoc]
  have hPre' :=
    Simulation.Interaction.ForwardRel.strengthen_left hPre
      (rawExecSeq_allDone_regular_fuel_bound fuel
        (context.withFunctionScope scope) (rawHead :: rawTail) state)
  rw [show fuel + (slack + 1) = fuel + 1 + slack by omega] at hPre'
  refine Simulation.Interaction.ForwardRel.bind_custom hPre' ?_
  intro rawPreDone orderedPreDone hPreDone
  rcases hPreDone with ⟨hPreDone, hFuelBound⟩
  cases hPreDone with
  | error hError =>
      subst_vars
      exact Simulation.Interaction.ForwardRel.done rfl
  | @ok rawState orderedState hState =>
      cases rawState with
      | Ok shared vars =>
          subst orderedState
          have hFuel : (rawHead :: rawTail).length < fuel := hFuelBound
          rw [show fuel + 1 + slack - orderedPre.length =
            (fuel + slack - (rawHead :: rawTail).length - 1) + 2 by
              rw [hLength]
              omega]
          exact loopRestrictedRunForward (hLoop (.Ok shared vars))
      | OutOfFuel =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact Simulation.Interaction.ForwardRel.done rfl
          | inr hRestricted =>
              subst orderedState
              change
                Simulation.Interaction.ForwardRel
                  Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
                  (pure
                    ((EvmYul.Yul.State.OutOfFuel : State).restrictStoreTo
                      state.store))
                  (pure
                    (((EvmYul.Yul.State.OutOfFuel : State).restrictStoreTo
                      state.store).restrictStoreTo state.store))
              rw [Yul.InteractionSemantics.State.restrictStoreTo_idem]
              exact Simulation.Interaction.ForwardRel.done rfl
      | Checkpoint jump =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact Simulation.Interaction.ForwardRel.done rfl
          | inr hRestricted =>
              subst orderedState
              cases jump with
              | Break shared vars =>
                  change
                    Simulation.Interaction.ForwardRel
                      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
                      (pure
                        ((EvmYul.Yul.State.Checkpoint
                          (.Break shared vars)).restrictStoreTo state.store))
                      (pure
                        (((EvmYul.Yul.State.Checkpoint
                          (.Break shared vars)).restrictStoreTo
                            state.store).restrictStoreTo state.store))
                  rw [Yul.InteractionSemantics.State.restrictStoreTo_idem]
                  exact Simulation.Interaction.ForwardRel.done rfl
              | Continue shared vars =>
                  change
                    Simulation.Interaction.ForwardRel
                      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
                      (pure
                        ((EvmYul.Yul.State.Checkpoint
                          (.Continue shared vars)).restrictStoreTo state.store))
                      (pure
                        (((EvmYul.Yul.State.Checkpoint
                          (.Continue shared vars)).restrictStoreTo
                            state.store).restrictStoreTo state.store))
                  rw [Yul.InteractionSemantics.State.restrictStoreTo_idem]
                  exact Simulation.Interaction.ForwardRel.done rfl
              | Leave shared vars =>
                  change
                    Simulation.Interaction.ForwardRel
                      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
                      (pure
                        ((EvmYul.Yul.State.Checkpoint
                          (.Leave shared vars)).restrictStoreTo state.store))
                      (pure
                        (((EvmYul.Yul.State.Checkpoint
                          (.Leave shared vars)).restrictStoreTo
                            state.store).restrictStoreTo state.store))
                  rw [Yul.InteractionSemantics.State.restrictStoreTo_idem]
                  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_for_empty
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawPost rawBody : List Raw.Stmt} {rawCondition : Raw.Expr}
    {orderedPost orderedBody : List Frontend.AstStmt}
    {orderedCondition : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hLoop :
      ∀ loopState,
        LoopRunForward (fuel - 1) (fuel - 1 + (slack + 2))
          (context.withFunctionScope [])
          rawCondition rawPost rawBody orderedCondition
          orderedPost orderedBody contract loopState) :
    StmtRunForward (fuel + 2) (fuel + 2 + slack)
      context (.forLoop [] rawCondition rawPost rawBody)
      (.For orderedCondition orderedPost orderedBody) contract state := by
  unfold StmtRunForward
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [Raw.SourceSemantics.Exec.forLoop_succ]
  rw [Raw.SourceSemantics.ExecFor.succ]
  simp only [Raw.SourceSemantics.functionScope?]
  rw [show fuel + 2 + slack = (fuel + 1 + slack) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.for_succ]
  cases fuel with
  | zero =>
      rw [Raw.SourceSemantics.execSeq_zero]
      unfold Raw.SourceSemantics.fail
      change
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
          (Simulation.Interaction.bind
            (Yul.InteractionSemantics.Primitive.fail state .OutOfFuel)
            _)
          _
      rw [Yul.InteractionSemantics.Primitive.bind_fail]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
  | succ residual =>
      rw [Raw.SourceSemantics.ExecSeq.nil_succ]
      rw [show residual + 1 - 1 = residual by omega]
      rw [show residual + 1 + 1 + slack =
        residual + (slack + 2) by omega]
      change
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
          (Simulation.Interaction.bind
            (Simulation.Interaction.done (.ok state))
            (fun stateAfterPre =>
              Simulation.Interaction.bind
                (Raw.SourceSemantics.loop residual
                  (context.withFunctionScope [])
                  rawCondition rawPost rawBody stateAfterPre)
                Simulation.Interaction.pure))
          (Yul.InteractionSemantics.loop (residual + (slack + 2))
            orderedCondition orderedPost orderedBody (some contract) state)
      rw [Simulation.Interaction.bind_done_ok]
      rw [Simulation.Interaction.bind_pure]
      simpa using hLoop state

theorem stmtRunForward_for_one
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawPre rawPost rawBody : List Raw.Stmt}
    {rawCondition : Raw.Expr}
    {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward 1 orderedFuel context
      (.forLoop rawPre rawCondition rawPost rawBody)
      ordered contract state := by
  unfold StmtRunForward
  rw [show 1 = 0 + 1 by omega]
  rw [Raw.SourceSemantics.Exec.forLoop_succ]
  simp [Raw.SourceSemantics.execFor, Raw.SourceSemantics.fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem stmtRunForward_break_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context .break .Break contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.break_succ]
  rw [Yul.InteractionSemantics.Exec.brk_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_continue_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context .continue .Continue contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.continue_succ]
  rw [Yul.InteractionSemantics.Exec.cont_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_leave_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context .leave .Leave contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.leave_succ]
  rw [Yul.InteractionSemantics.Exec.leave_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_functionDefinition_stub_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {contract : Frontend.AstContract}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 2)
      context (.functionDefinition name params returns body)
      (.Block []) contract (.Ok shared store) := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (pure (EvmYul.Yul.State.Ok shared store))
      (pure (EvmYul.Yul.State.Ok shared
        (EvmYul.Yul.State.restrictVarStore store store)))
  rw [Yul.VarStoreRestriction.restrict_self]
  exact Simulation.Interaction.ForwardRel.done rfl

/-- Erased nested function declarations are exact on regular states. On an
abrupt block entry, their administrative empty block may apply the enclosing
entry-store restriction early. -/
theorem scopedStmtRunForward_functionDefinition_stub_succ
    {rawFuel orderedFuel : Nat}
    {entryStore : EvmYul.Yul.VarStore}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {contract : Frontend.AstContract} {state : State}
    (hCompatible : BlockEntryCompatible entryStore state) :
    ScopedStmtRunForward entryStore (rawFuel + 1) (orderedFuel + 2)
      context (.functionDefinition name params returns body)
      (.Block []) contract state := by
  cases state with
  | Ok shared store =>
      exact scopedStmtRunForward_of_exact
        stmtRunForward_functionDefinition_stub_succ
  | OutOfFuel =>
      unfold ScopedStmtRunForward
      rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
      rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.block_succ]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      exact
        Simulation.Interaction.ForwardRel.done
          (Simulation.Interaction.ExceptRel.ok (Or.inl rfl))
  | Checkpoint jump =>
      unfold ScopedStmtRunForward
      rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
      rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.block_succ]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      rw [← hCompatible]
      cases jump <;>
        exact
          Simulation.Interaction.ForwardRel.done
            (Simulation.Interaction.ExceptRel.ok (Or.inr rfl))

def BlockElaborationRunForward
    (slack : Nat)
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel : Nat)
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
        .ok (front, finalElabState) →
      StmtListNormalized builtinContext front ordered →
        BlockCodeRunForward rawFuel (rawFuel + slack)
          rawContext rawCode ordered contract state

theorem stmtRunForward_of_elaborated_variableDeclaration_none
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {names : List Name}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab :
      (Elab.Stmt.elaborate (.variableDeclaration names none)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext (.variableDeclaration names none)
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp at hElab
  cases hDeclare :
      (Elab.declareIdentifiers names "variable").run elabState with
  | error err => simp [hDeclare] at hElab
  | ok result =>
      rcases result with ⟨_, declaredState⟩
      simp [hDeclare] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := StmtNormalized.let_none_ordered hNormalized
      subst ordered
      exact stmtRunForward_variableDeclaration_none_succ

theorem stmtRunForward_of_elaborated_variableDeclaration_some
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {names : List Name} {rawValue : Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate
        (.variableDeclaration names (some rawValue))).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) ((rawFuel + slack) + 1)
      rawContext (.variableDeclaration names (some rawValue))
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp at hElab
  cases hValue : (Elab.Expr.elaborate rawValue).run elabState with
  | error err => simp [hValue] at hElab
  | ok valueResult =>
      rcases valueResult with ⟨frontValue, valueState⟩
      simp [hValue] at hElab
      cases hDeclare :
          (Elab.declareIdentifiers names "variable").run valueState with
      | error err => simp [hDeclare] at hElab
      | ok result =>
          rcases result with ⟨_, declaredState⟩
          simp [hDeclare] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.let_some_parts hNormalized with
            ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
          exact
            stmtRunForward_variableDeclaration_some_succ
              (hExpr rawFuel (state := state)
                hValue hValueNormalized)

theorem stmtRunForward_of_elaborated_assignment
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {names : List Name} {rawValue : Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate (.assignment names rawValue)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) ((rawFuel + slack) + 1)
      rawContext (.assignment names rawValue) ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hVisible :
      (Elab.requireIdentifiersVisible names "assignment").run elabState with
  | error err => simp [hVisible] at hElab
  | ok visibleResult =>
      rcases visibleResult with ⟨_, visibleState⟩
      simp [hVisible] at hElab
      cases hValue : (Elab.Expr.elaborate rawValue).run visibleState with
      | error err => simp [hValue] at hElab
      | ok valueResult =>
          rcases valueResult with ⟨frontValue, valueState⟩
          simp [hValue] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.assign_parts hNormalized with
            ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
          exact
            stmtRunForward_assignment_succ
              (hExpr rawFuel (state := state)
                hValue hValueNormalized)

theorem stmtRunForward_of_elaborated_break
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab : (Elab.Stmt.elaborate .break).run elabState =
      .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext .break ordered contract state := by
  simp [Elab.Stmt.elaborate] at hElab
  rcases hElab with ⟨rfl, rfl⟩
  have hOrdered := StmtNormalized.break_ordered hNormalized
  subst ordered
  exact stmtRunForward_break_succ

theorem stmtRunForward_of_elaborated_continue
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab : (Elab.Stmt.elaborate .continue).run elabState =
      .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext .continue ordered contract state := by
  simp [Elab.Stmt.elaborate] at hElab
  rcases hElab with ⟨rfl, rfl⟩
  have hOrdered := StmtNormalized.continue_ordered hNormalized
  subst ordered
  exact stmtRunForward_continue_succ

theorem stmtRunForward_of_elaborated_leave
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab : (Elab.Stmt.elaborate .leave).run elabState =
      .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext .leave ordered contract state := by
  simp [Elab.Stmt.elaborate] at hElab
  rcases hElab with ⟨rfl, rfl⟩
  have hOrdered := StmtNormalized.leave_ordered hNormalized
  subst ordered
  exact stmtRunForward_leave_succ

theorem stmtRunForward_of_elaborated_block
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawBody : List Raw.Stmt}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hBlock :
      BlockElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate (.block rawBody)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (rawFuel + slack)
      rawContext (.block rawBody) ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp at hElab
  cases hBody :
      (Elab.Stmt.List.elaborateBlock rawBody true).run elabState with
  | error err => simp [hBody] at hElab
  | ok bodyResult =>
      rcases bodyResult with ⟨frontBody, bodyState⟩
      simp [hBody] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases StmtNormalized.block_parts hNormalized with
        ⟨orderedBody, rfl, ⟨hBodyNormalized⟩⟩
      exact
        stmtRunForward_block_succ
          (hBlock rawFuel (state := state)
            hBody hBodyNormalized)

theorem stmtRunForward_of_elaborated_ifThen
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawCondition : Raw.Expr} {rawBody : List Raw.Stmt}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hBlock :
      BlockElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate (.ifThen rawCondition rawBody)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) ((rawFuel + slack) + 1)
      rawContext (.ifThen rawCondition rawBody) ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hCondition : (Elab.Expr.elaborate rawCondition).run elabState with
  | error err => simp [hCondition] at hElab
  | ok conditionResult =>
      rcases conditionResult with ⟨frontCondition, conditionState⟩
      simp [hCondition] at hElab
      cases hBody :
          (Elab.Stmt.List.elaborateBlock rawBody true).run
            conditionState with
      | error err => simp [hBody] at hElab
      | ok bodyResult =>
          rcases bodyResult with ⟨frontBody, bodyState⟩
          simp [hBody] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.if_parts hNormalized with
            ⟨orderedCondition, orderedBody, rfl,
              ⟨hConditionNormalized⟩, ⟨hBodyNormalized⟩⟩
          apply stmtRunForward_ifThen_succ
          · exact
              exprRunForward_of_values
                (hExpr rawFuel (state := state)
                  hCondition hConditionNormalized)
          · intro stateAfterCondition value _hTruthy
            exact
              hBlock rawFuel
                (state := stateAfterCondition) hBody hBodyNormalized

/-- Semantic compiler interface for one statement under arbitrary residual
fuel. The full frontend proof constructs this from expression, block, switch,
loop, and generated-call preservation; list traversal is generic below. -/
def StmtElaborationRunForward
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel orderedFuel : Nat)
    {rawStmt : Raw.Stmt} {front : Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    (Elab.Stmt.elaborate rawStmt).run elabState =
        .ok (front, finalElabState) →
      StmtNormalized builtinContext front ordered →
        StmtRunForward rawFuel orderedFuel
          rawContext rawStmt ordered contract state

/-- Exact pre-block statement-list preservation. Both sides still carry the
same lexical store; the dispatcher adapter below accounts for the ordered
dispatcher's additional block boundary. -/
def SeqRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCode : List Raw.Stmt) (orderedCode : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.execSeq rawFuel context rawCode state)
    (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
      (some contract) state)

def ScopedSeqRunForward (entryStore : EvmYul.Yul.VarStore)
    (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCode : List Raw.Stmt) (orderedCode : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    (BlockSeqDoneRel entryStore)
    (Raw.SourceSemantics.execSeq rawFuel context rawCode state)
    (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
      (some contract) state)

/-- One checked statement occurrence under its exact frontend state path. This
is the statement component consumed by the generic recursive list theorem. -/
def ScopedStmtPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {front : Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State},
    BlockEntryCompatible entryStore state →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      FrontendCompilationPath builtinContext contract
        elabState finalElabState →
      (Elab.Stmt.elaborate rawStmt).run elabState =
          .ok (front, finalElabState) →
      StmtNormalized builtinContext front ordered →
      ScopedStmtRunForward entryStore rawFuel (rawFuel + slack)
        rawContext rawStmt ordered contract state

/-- The four statement families with genuinely distinct control/call
semantics. The generic statement classifier handles all remaining constructors
directly and consumes one bundled provider for these cases. -/
inductive StmtNeedsSpecialPreservation : Raw.Stmt → Prop where
  | expressionStatement (expr : Raw.Expr) :
      StmtNeedsSpecialPreservation (.expressionStatement expr)
  | functionDefinition (name : Name) (params returns : List Name)
      (body : List Raw.Stmt) :
      StmtNeedsSpecialPreservation
        (.functionDefinition name params returns body)
  | switch (scrutinee : Raw.Expr)
      (cases : List (Raw.SwitchCaseValue × List Raw.Stmt))
      (default : List Raw.Stmt) :
      StmtNeedsSpecialPreservation (.switch scrutinee cases default)
  | forLoop (pre : List Raw.Stmt) (condition : Raw.Expr)
      (post body : List Raw.Stmt) :
      StmtNeedsSpecialPreservation (.forLoop pre condition post body)

def ScopedStmtSpecialRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {front : Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State},
    StmtNeedsSpecialPreservation rawStmt →
      BlockEntryCompatible entryStore state →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      FrontendCompilationPath builtinContext contract
        elabState finalElabState →
      (Elab.Stmt.elaborate rawStmt).run elabState =
          .ok (front, finalElabState) →
      StmtNormalized builtinContext front ordered →
      ScopedStmtRunForward entryStore rawFuel (rawFuel + slack)
        rawContext rawStmt ordered contract state

/-- Whole statement-list preservation under one enclosing lexical-block entry
store. Recursive tails start in regular states, so the same entry store remains
compatible without weakening regular outcome equality. -/
def ScopedSeqPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State},
    BlockEntryCompatible entryStore state →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      FrontendCompilationPath builtinContext contract
        elabState finalElabState →
      (Elab.Stmt.List.elaborate rawCode).run elabState =
          .ok (front, finalElabState) →
      StmtListNormalized builtinContext front ordered →
      ScopedSeqRunForward entryStore rawFuel (rawFuel + slack)
        rawContext rawCode ordered contract state

def ScopedSeqPathRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedSeqPathRunForwardAt rawFuel slack builtinContext contract

/-- Build the pointwise switch-case interface from the actual checked case-list
elaboration path. Each case body is discharged by the generic recursive block
theorem at the same source fuel. -/
theorem switchCaseListRunForward_of_path_elaboration_below
    {bound fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hFuel : fuel < bound)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        bound slack builtinContext contract) :
    ∀ {rawContext : Raw.SourceSemantics.Context}
      {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
      {frontCases :
        List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      {orderedCases : List (Frontend.Word × List Frontend.AstStmt)}
      {elabState finalElabState : Elab.State},
      PathCompiledContext builtinContext contract
          rawContext elabState.functionScopes →
        FrontendCompilationPath builtinContext contract
          elabState finalElabState →
        (Elab.Stmt.CaseList.elaborate rawCases).run elabState =
          .ok (frontCases, finalElabState) →
        CaseListNormalized builtinContext frontCases orderedCases →
        SwitchCaseListRunForward fuel (fuel + slack)
          rawContext contract rawCases orderedCases := by
  intro rawContext rawCases
  induction rawCases with
  | nil =>
      intro frontCases orderedCases elabState finalElabState
        hContext hPath hElab hNormalized
      simp [Elab.Stmt.CaseList.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := CaseListNormalized.nil_ordered hNormalized
      subst orderedCases
      exact .nil
  | cons rawCase rawRest ih =>
      rcases rawCase with ⟨rawValue, rawBody⟩
      intro frontCases orderedCases elabState finalElabState
        hContext hPath hElab hNormalized
      unfold Elab.Stmt.CaseList.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hValue : Elab.SwitchCaseValue.elaborate rawValue with
      | error err =>
          simp [hValue] at hElab
          unfold Elab.throw at hElab
          cases hElab
      | ok frontValue =>
          simp [hValue] at hElab
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawBody true).run elabState with
          | error err => simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hElab
              cases hRest :
                  (Elab.Stmt.CaseList.elaborate rawRest).run bodyState with
              | error err => simp [hRest] at hElab
              | ok restResult =>
                  rcases restResult with ⟨frontRest, restState⟩
                  simp [hRest] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  rcases CaseListNormalized.cons_parts hNormalized with
                    ⟨orderedValue, orderedBody, orderedRest, rfl,
                      hOrderedValue, ⟨hBodyNormalized⟩,
                      ⟨hRestNormalized⟩⟩
                  have hBodyExt :=
                    Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                      rawBody true hBody hPath.entryValid
                  have hRestExt :=
                    Elab.Stmt.CaseList.elaborate_preserves_clzAllocation
                      rawRest hRest hBodyExt.after_valid
                  have hRestHoisted :
                      HoistedFunctionsExtend bodyState restState := by
                    intro entry hEntry
                    exact
                      Elab.Stmt.CaseList.elaborate_preserves_hoistedFunction_mem
                        rawRest hRest hEntry
                  have hBodyPath :
                      FrontendCompilationPath builtinContext contract
                        elabState bodyState :=
                    hPath.prefixPath hRestExt hRestHoisted
                  have hRestPath :
                      FrontendCompilationPath builtinContext contract
                        bodyState restState :=
                    hPath.suffixPath hBodyExt
                  have hBodyScopes :
                      bodyState.functionScopes =
                        elabState.functionScopes :=
                    Elab.Stmt.List.elaborateBlock_preserves_functionScopes
                      rawBody true hBody
                  have hRestContext :
                      PathCompiledContext builtinContext contract
                        rawContext bodyState.functionScopes := by
                    simpa [hBodyScopes] using hContext
                  have hBodyRun :
                      ∀ state,
                        BlockCodeRunForward fuel (fuel + slack)
                          rawContext rawBody orderedBody contract state := by
                    intro state
                    exact
                      hBlock fuel hFuel (state := state)
                        hContext hBodyPath hBody hBodyNormalized
                  exact
                    .cons
                      (switchCaseValue_elaboration_word hValue hOrderedValue)
                      hBodyRun
                      (ih hRestContext hRestPath hRest hRestNormalized)

theorem scopedStmtRunForward_switch_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {rawDefault : List Raw.Stmt}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      FrontendCompilationPath builtinContext contract
        elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate
        (.switch rawCondition rawCases rawDefault)).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 1) (fuel + 1 + slack)
      rawContext (.switch rawCondition rawCases rawDefault)
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hCondition :
      (Elab.Expr.elaborate rawCondition).run elabState with
  | error err => simp [hCondition] at hElab
  | ok conditionResult =>
      rcases conditionResult with ⟨frontCondition, conditionState⟩
      simp [hCondition] at hElab
      cases hCases :
          (Elab.Stmt.CaseList.elaborate rawCases).run conditionState with
      | error err => simp [hCases] at hElab
      | ok casesResult =>
          rcases casesResult with ⟨frontCases, casesState⟩
          simp [hCases] at hElab
          cases hDefault :
              (Elab.Stmt.List.elaborateBlock rawDefault true).run
                casesState with
          | error err => simp [hDefault] at hElab
          | ok defaultResult =>
              rcases defaultResult with ⟨frontDefault, defaultState⟩
              simp [hDefault] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtNormalized.switch_parts hNormalized with
                ⟨orderedCondition, orderedCases, orderedDefault, rfl,
                  ⟨hConditionNormalized⟩, ⟨hCasesNormalized⟩,
                  ⟨hDefaultNormalized⟩⟩
              have hConditionExt :=
                Elab.Expr.elaborate_preserves_clzAllocation rawCondition
                  hCondition hPath.entryValid
              have hCasesExt :=
                Elab.Stmt.CaseList.elaborate_preserves_clzAllocation
                  rawCases hCases hConditionExt.after_valid
              have hDefaultExt :=
                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                  rawDefault true hDefault hCasesExt.after_valid
              have hDefaultHoisted :
                  HoistedFunctionsExtend casesState defaultState := by
                intro entry hEntry
                exact
                  Elab.Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                    rawDefault true hDefault hEntry
              have hConditionPath :
                  ClzCompilationPath contract elabState conditionState :=
                hPath.clz.prefixPath
                  (Elab.ClzAllocationExtends.trans hCasesExt hDefaultExt)
              have hCasesPath :
                  FrontendCompilationPath builtinContext contract
                    conditionState casesState :=
                (hPath.suffixPath hConditionExt).prefixPath
                  hDefaultExt hDefaultHoisted
              have hDefaultPath :
                  FrontendCompilationPath builtinContext contract
                    casesState defaultState :=
                hPath.suffixPath
                  (Elab.ClzAllocationExtends.trans hConditionExt hCasesExt)
              have hConditionScopes :
                  conditionState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes
                  rawCondition hCondition
              have hCasesScopes :
                  casesState.functionScopes =
                    conditionState.functionScopes :=
                Elab.Stmt.CaseList.elaborate_preserves_functionScopes
                  rawCases hCases
              have hCasesContext :
                  PathCompiledContext builtinContext contract
                    rawContext conditionState.functionScopes := by
                simpa [hConditionScopes] using hContext
              have hDefaultContext :
                  PathCompiledContext builtinContext contract
                    rawContext casesState.functionScopes := by
                simpa [hCasesScopes] using hCasesContext
              have hConditionRun :=
                hExpr fuel (by omega) (state := state)
                  hContext hConditionPath hCondition hConditionNormalized
              have hCasesRun :=
                switchCaseListRunForward_of_path_elaboration_below
                  (fuel := fuel) (slack := slack) (by omega) hBlock
                  hCasesContext hCasesPath hCases hCasesNormalized
              have hDefaultRun :
                  ∀ stateAfterCondition,
                    BlockCodeRunForward fuel (fuel + slack)
                      rawContext rawDefault orderedDefault contract
                      stateAfterCondition := by
                intro stateAfterCondition
                exact
                  hBlock fuel (by omega) (state := stateAfterCondition)
                    hDefaultContext hDefaultPath hDefault hDefaultNormalized
              apply scopedStmtRunForward_of_exact
              have hSwitch :=
                stmtRunForward_switch_succ
                  (rawFuel := fuel) (orderedFuel := fuel + slack)
                  (context := rawContext) (contract := contract)
                  (state := state)
                  (exprRunForward_of_values hConditionRun)
                  (SwitchCaseListRunForward.select hCasesRun hDefaultRun)
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hSwitch

/-- Checked `for` preservation for the elaborator branch that retains a local
function scope across the initializer, condition, post, and body. -/
theorem scopedStmtRunForward_for_withFunctions_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ∀ extra,
        ScopedBlockPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hSeq :
      ScopedSeqPathRunForwardAt
        fuel (slack + 1) builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawPre rawPost rawBody : List Raw.Stmt}
    {rawCondition : Raw.Expr}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hHasFunctions :
      Elab.Stmt.List.hasImmediateFunctionDefinition rawPre = true)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      FrontendCompilationPath builtinContext contract
        elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate
        (.forLoop rawPre rawCondition rawPost rawBody)).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 2) (fuel + 2 + slack)
      rawContext (.forLoop rawPre rawCondition rawPost rawBody)
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp only [hHasFunctions, Bool.true_eq_false, ↓reduceIte] at hElab
  simp [StateT.run_bind] at hElab
  cases hPushIdentifier : Elab.pushIdentifierScope.run elabState with
  | error err => simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hElab
      cases hPre :
          (Elab.Stmt.List.elaborateForInitBlockWithScope rawPre).run
            identifierPushedState with
      | error err => simp [hPre] at hElab
      | ok preResult =>
          rcases preResult with ⟨frontPre, preState⟩
          simp [hPre] at hElab
          cases hCondition :
              (Elab.Expr.elaborate rawCondition).run preState with
          | error err => simp [hCondition] at hElab
          | ok conditionResult =>
              rcases conditionResult with
                ⟨frontCondition, conditionState⟩
              simp [hCondition] at hElab
              cases hPost :
                  (Elab.Stmt.List.elaborateBlock rawPost true).run
                    conditionState with
              | error err => simp [hPost] at hElab
              | ok postResult =>
                  rcases postResult with ⟨frontPost, postState⟩
                  simp [hPost] at hElab
                  cases hBody :
                      (Elab.Stmt.List.elaborateBlock rawBody true).run
                        postState with
                  | error err => simp [hBody] at hElab
                  | ok bodyResult =>
                      rcases bodyResult with ⟨frontBody, bodyState⟩
                      simp [hBody] at hElab
                      cases hPopFunction :
                          Elab.popFunctionScope.run bodyState with
                      | error err => simp [hPopFunction] at hElab
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hElab
                          cases hPopIdentifier :
                              Elab.popIdentifierScope.run
                                functionPoppedState with
                          | error err => simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨rfl, rfl⟩
                              rcases StmtNormalized.for_parts hNormalized with
                                ⟨orderedPre, orderedCondition,
                                  orderedPost, orderedBody, rfl,
                                  ⟨hPreNormalized⟩,
                                  ⟨hConditionNormalized⟩,
                                  ⟨hPostNormalized⟩,
                                  ⟨hBodyNormalized⟩⟩
                              have hPushIdentifierExt :=
                                Elab.pushIdentifierScope_preserves_clzAllocation
                                  hPushIdentifier hPath.entryValid
                              have hPreExt :=
                                Elab.Stmt.List.elaborateForInitBlockWithScope_preserves_clzAllocation
                                  rawPre hPre
                                  hPushIdentifierExt.after_valid
                              have hConditionExt :=
                                Elab.Expr.elaborate_preserves_clzAllocation
                                  rawCondition hCondition hPreExt.after_valid
                              have hPostExt :=
                                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                                  rawPost true hPost
                                  hConditionExt.after_valid
                              have hBodyExt :=
                                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                                  rawBody true hBody hPostExt.after_valid
                              have hPopFunctionExt :=
                                Elab.popFunctionScope_preserves_clzAllocation
                                  hPopFunction hBodyExt.after_valid
                              have hPopIdentifierExt :=
                                Elab.popIdentifierScope_preserves_clzAllocation
                                  hPopIdentifier hPopFunctionExt.after_valid
                              have hBodyHoisted :
                                  HoistedFunctionsExtend postState bodyState := by
                                intro entry hEntry
                                exact
                                  Elab.Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                                    rawBody true hBody hEntry
                              have hPopFunctionHoisted :
                                  HoistedFunctionsExtend bodyState
                                    functionPoppedState := by
                                intro entry hEntry
                                exact
                                  Elab.popFunctionScope_preserves_hoistedFunction_mem
                                    hPopFunction hEntry
                              have hPopIdentifierHoisted :
                                  HoistedFunctionsExtend functionPoppedState
                                    identifierPoppedState := by
                                intro entry hEntry
                                exact
                                  Elab.popIdentifierScope_preserves_hoistedFunction_mem
                                    hPopIdentifier hEntry
                              have hAfterBodyClz :
                                  Elab.ClzAllocationExtends bodyState
                                    identifierPoppedState :=
                                Elab.ClzAllocationExtends.trans
                                  hPopFunctionExt hPopIdentifierExt
                              have hAfterBodyHoisted :
                                  HoistedFunctionsExtend bodyState
                                    identifierPoppedState :=
                                HoistedFunctionsExtend.trans
                                  hPopFunctionHoisted hPopIdentifierHoisted
                              have hBeforeBodyClz :
                                  Elab.ClzAllocationExtends elabState
                                    postState :=
                                Elab.ClzAllocationExtends.trans
                                  hPushIdentifierExt
                                  (Elab.ClzAllocationExtends.trans hPreExt
                                    (Elab.ClzAllocationExtends.trans
                                      hConditionExt hPostExt))
                              have hBodyPath :
                                  FrontendCompilationPath builtinContext
                                    contract postState bodyState :=
                                hPath.subpath hBeforeBodyClz
                                  hAfterBodyClz hAfterBodyHoisted
                              have hPostHoisted :
                                  HoistedFunctionsExtend conditionState
                                    postState := by
                                intro entry hEntry
                                exact
                                  Elab.Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                                    rawPost true hPost hEntry
                              have hAfterPostClz :
                                  Elab.ClzAllocationExtends postState
                                    identifierPoppedState :=
                                Elab.ClzAllocationExtends.trans hBodyExt
                                  hAfterBodyClz
                              have hAfterPostHoisted :
                                  HoistedFunctionsExtend postState
                                    identifierPoppedState :=
                                HoistedFunctionsExtend.trans hBodyHoisted
                                  hAfterBodyHoisted
                              have hBeforePostClz :
                                  Elab.ClzAllocationExtends elabState
                                    conditionState :=
                                Elab.ClzAllocationExtends.trans
                                  hPushIdentifierExt
                                  (Elab.ClzAllocationExtends.trans hPreExt
                                    hConditionExt)
                              have hPostPath :
                                  FrontendCompilationPath builtinContext
                                    contract conditionState postState :=
                                hPath.subpath hBeforePostClz
                                  hAfterPostClz hAfterPostHoisted
                              have hAfterConditionClz :
                                  Elab.ClzAllocationExtends conditionState
                                    identifierPoppedState :=
                                Elab.ClzAllocationExtends.trans hPostExt
                                  hAfterPostClz
                              have hBeforeConditionClz :
                                  Elab.ClzAllocationExtends elabState
                                    preState :=
                                Elab.ClzAllocationExtends.trans
                                  hPushIdentifierExt hPreExt
                              have hConditionPath :
                                  ClzCompilationPath contract preState
                                    conditionState :=
                                (hPath.clz.suffixPath
                                  hBeforeConditionClz).prefixPath
                                    hAfterConditionClz
                              have hPushIdentifierScopes :
                                  identifierPushedState.functionScopes =
                                    elabState.functionScopes :=
                                Elab.pushIdentifierScope_preserves_functionScopes
                                  hPushIdentifier
                              unfold
                                Elab.Stmt.List.elaborateForInitBlockWithScope
                                at hPre
                              simp [StateT.run_bind] at hPre
                              cases hScope :
                                  (Elab.Stmt.List.localFunctionScope rawPre).run
                                    identifierPushedState with
                              | error err => simp [hScope] at hPre
                              | ok scopeResult =>
                                  rcases scopeResult with
                                    ⟨generatedScope, scopeState⟩
                                  simp [hScope] at hPre
                                  cases hPushFunction :
                                      (Elab.pushFunctionScope
                                        generatedScope).run scopeState with
                                  | error err =>
                                      simp [hPushFunction] at hPre
                                  | ok pushFunctionResult =>
                                      rcases pushFunctionResult with
                                        ⟨_, functionPushedState⟩
                                      simp [hPushFunction] at hPre
                                      cases hHoist :
                                          (Elab.Stmt.List.hoistLocalFunctions
                                            rawPre generatedScope).run
                                            functionPushedState with
                                      | error err => simp [hHoist] at hPre
                                      | ok hoistResult =>
                                          rcases hoistResult with
                                            ⟨_, hoistState⟩
                                          simp [hHoist] at hPre
                                          cases hPreCode :
                                              (Elab.Stmt.List.elaborate
                                                rawPre).run hoistState with
                                          | error err =>
                                              simp [hPreCode] at hPre
                                          | ok preCodeResult =>
                                              rcases preCodeResult with
                                                ⟨frontPreCode,
                                                  preCodeState⟩
                                              simp [hPreCode] at hPre
                                              rcases hPre with ⟨rfl, rfl⟩
                                              rcases
                                                  localFunctionScope_rawFunctionScope
                                                    hScope with
                                                ⟨rawScope, hRawScope,
                                                  _hNames⟩
                                              have hScopeExt :=
                                                Elab.Stmt.List.localFunctionScope_preserves_clzAllocation
                                                  rawPre hScope
                                                  hPushIdentifierExt.after_valid
                                              have hPushFunctionExt :=
                                                Elab.pushFunctionScope_preserves_clzAllocation
                                                  generatedScope hPushFunction
                                                  hScopeExt.after_valid
                                              have hHoistExt :=
                                                Elab.Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                                                  rawPre generatedScope hHoist
                                                  hPushFunctionExt.after_valid
                                              have hPreCodeExt :=
                                                Elab.Stmt.List.elaborate_preserves_clzAllocation
                                                  rawPre hPreCode
                                                  hHoistExt.after_valid
                                              have hAfterPreClz :
                                                  Elab.ClzAllocationExtends
                                                    preCodeState
                                                    identifierPoppedState :=
                                                Elab.ClzAllocationExtends.trans
                                                  hConditionExt
                                                  hAfterConditionClz
                                              have hConditionHoisted :
                                                  HoistedFunctionsExtend
                                                    preCodeState
                                                    conditionState := by
                                                intro entry hEntry
                                                exact
                                                  Elab.Expr.elaborate_preserves_hoistedFunction_mem
                                                    rawCondition hCondition
                                                    hEntry
                                              have hAfterConditionHoisted :
                                                  HoistedFunctionsExtend
                                                    conditionState
                                                    identifierPoppedState :=
                                                HoistedFunctionsExtend.trans
                                                  hPostHoisted
                                                  hAfterPostHoisted
                                              have hAfterPreHoisted :
                                                  HoistedFunctionsExtend
                                                    preCodeState
                                                    identifierPoppedState :=
                                                HoistedFunctionsExtend.trans
                                                  hConditionHoisted
                                                  hAfterConditionHoisted
                                              have hBeforeHoistClz :
                                                  Elab.ClzAllocationExtends
                                                    elabState
                                                    functionPushedState :=
                                                Elab.ClzAllocationExtends.trans
                                                  hPushIdentifierExt
                                                  (Elab.ClzAllocationExtends.trans
                                                    hScopeExt hPushFunctionExt)
                                              have hAfterHoistClz :
                                                  Elab.ClzAllocationExtends
                                                    hoistState
                                                    identifierPoppedState :=
                                                Elab.ClzAllocationExtends.trans
                                                  hPreCodeExt hAfterPreClz
                                              have hPreCodeHoisted :
                                                  HoistedFunctionsExtend
                                                    hoistState preCodeState := by
                                                intro entry hEntry
                                                exact
                                                  Elab.Stmt.List.elaborate_preserves_hoistedFunction_mem
                                                    rawPre hPreCode hEntry
                                              have hAfterHoistHoisted :
                                                  HoistedFunctionsExtend
                                                    hoistState
                                                    identifierPoppedState :=
                                                HoistedFunctionsExtend.trans
                                                  hPreCodeHoisted
                                                  hAfterPreHoisted
                                              have hHoistPath :
                                                  FrontendCompilationPath
                                                    builtinContext contract
                                                    functionPushedState
                                                    hoistState :=
                                                hPath.subpath
                                                  hBeforeHoistClz
                                                  hAfterHoistClz
                                                  hAfterHoistHoisted
                                              have hBeforePreCodeClz :
                                                  Elab.ClzAllocationExtends
                                                    elabState hoistState :=
                                                Elab.ClzAllocationExtends.trans
                                                  hBeforeHoistClz hHoistExt
                                              have hPreCodePath :
                                                  FrontendCompilationPath
                                                    builtinContext contract
                                                    hoistState preCodeState :=
                                                hPath.subpath
                                                  hBeforePreCodeClz
                                                  hAfterPreClz
                                                  hAfterPreHoisted
                                              have hScopeScopes :
                                                  scopeState.functionScopes =
                                                    identifierPushedState.functionScopes :=
                                                Elab.Stmt.List.localFunctionScope_preserves_functionScopes
                                                  rawPre hScope
                                              have hPushFunctionScopes :
                                                  functionPushedState.functionScopes =
                                                    generatedScope ::
                                                      scopeState.functionScopes :=
                                                Elab.pushFunctionScope_functionScopes
                                                  hPushFunction
                                              have hHoistScopes :
                                                  hoistState.functionScopes =
                                                    functionPushedState.functionScopes :=
                                                Elab.Stmt.List.hoistLocalFunctions_preserves_functionScopes
                                                  rawPre generatedScope hHoist
                                              have hPreCodeScopes :
                                                  preCodeState.functionScopes =
                                                    hoistState.functionScopes :=
                                                Elab.Stmt.List.elaborate_preserves_functionScopes
                                                  rawPre hPreCode
                                              have hFunctionPushedScopes :
                                                  functionPushedState.functionScopes =
                                                    generatedScope ::
                                                      elabState.functionScopes := by
                                                rw [hPushFunctionScopes,
                                                  hScopeScopes,
                                                  hPushIdentifierScopes]
                                              have hScopeBinding :=
                                                pathCompiledFunctionScope_of_localHoist
                                                  hRawScope hScope hHoist
                                                  hFunctionPushedScopes
                                                  hHoistPath
                                              have hLoopContext :
                                                  PathCompiledContext
                                                    builtinContext contract
                                                    (rawContext.withFunctionScope
                                                      rawScope)
                                                    preCodeState.functionScopes := by
                                                refine
                                                  { objectBuiltins :=
                                                      hContext.objectBuiltins
                                                    functionScopes := ?_ }
                                                rw [hPreCodeScopes,
                                                  hHoistScopes,
                                                  hFunctionPushedScopes]
                                                exact
                                                  .cons hScopeBinding
                                                    hContext.functionScopes
                                              have hPreRun :=
                                                have hPreContext :
                                                    PathCompiledContext
                                                      builtinContext contract
                                                      (rawContext.withFunctionScope
                                                        rawScope)
                                                      hoistState.functionScopes := by
                                                  simpa [hPreCodeScopes] using
                                                    hLoopContext
                                                hSeq
                                                  (state := state)
                                                  (entryStore := state.store)
                                                  (by cases state <;>
                                                    simp [BlockEntryCompatible])
                                                  hPreContext hPreCodePath
                                                  hPreCode hPreNormalized
                                              have hConditionScopes :
                                                  conditionState.functionScopes =
                                                    preCodeState.functionScopes :=
                                                Elab.Expr.elaborate_preserves_functionScopes
                                                  rawCondition hCondition
                                              have hPostScopes :
                                                  postState.functionScopes =
                                                    conditionState.functionScopes :=
                                                Elab.Stmt.List.elaborateBlock_preserves_functionScopes
                                                  rawPost true hPost
                                              have hPostContext :
                                                  PathCompiledContext
                                                    builtinContext contract
                                                    (rawContext.withFunctionScope
                                                      rawScope)
                                                    conditionState.functionScopes := by
                                                simpa [hConditionScopes] using
                                                  hLoopContext
                                              have hBodyContext :
                                                  PathCompiledContext
                                                    builtinContext contract
                                                    (rawContext.withFunctionScope
                                                      rawScope)
                                                    postState.functionScopes := by
                                                simpa [hPostScopes] using
                                                  hPostContext
                                              have hLengthFront :
                                                  frontPreCode.length =
                                                    rawPre.length :=
                                                stmtList_elaborate_length
                                                  hPreCode
                                              have hLengthOrdered :
                                                  orderedPre.length =
                                                    rawPre.length := by
                                                rw [StmtListNormalized.length_eq
                                                  hPreNormalized,
                                                  hLengthFront]
                                              have hRawNonempty :
                                                  rawPre ≠ [] := by
                                                intro hEmpty
                                                subst rawPre
                                                simp
                                                  [Elab.Stmt.List.hasImmediateFunctionDefinition]
                                                  at hHasFunctions
                                              have hOrderedNonempty :
                                                  orderedPre ≠ [] := by
                                                intro hEmpty
                                                subst orderedPre
                                                have : rawPre.length = 0 := by
                                                  simpa using
                                                    hLengthOrdered.symm
                                                exact hRawNonempty
                                                  (List.eq_nil_of_length_eq_zero
                                                    this)
                                              have hOrderedForm :
                                                  orderedForStmt orderedPre
                                                      orderedCondition
                                                      orderedPost orderedBody =
                                                    .Block
                                                      (orderedPre ++
                                                        [.For orderedCondition
                                                          orderedPost
                                                          orderedBody]) := by
                                                cases orderedPre with
                                                | nil =>
                                                    exact
                                                      (hOrderedNonempty rfl).elim
                                                | cons head tail => rfl
                                              rw [hOrderedForm]
                                              apply
                                                scopedStmtRunForward_of_exact
                                              apply stmtRunForward_for_nonempty
                                                hRawScope hLengthOrdered
                                                hOrderedNonempty hPreRun
                                              intro loopState
                                              apply
                                                loopRunForward_after_nonemptyPrefix
                                              · intro n hN conditionEntry
                                                apply exprRunForward_of_values
                                                exact
                                                  hExpr 0 n (by omega)
                                                    (state := conditionEntry)
                                                    hLoopContext
                                                    hConditionPath hCondition
                                                    hConditionNormalized
                                              · intro n hN postEntry
                                                exact
                                                  hBlock 0 n (by omega)
                                                    (state := postEntry)
                                                    hPostContext hPostPath
                                                    hPost hPostNormalized
                                              · intro n hN bodyEntry
                                                exact
                                                  hBlock 0 n (by omega)
                                                    (state := bodyEntry)
                                                  hBodyContext hBodyPath
                                                  hBody hBodyNormalized

/-- Bundled semantic interface for one non-scope-retaining `for` initializer.
The recursive frontend theorem constructs it from generic sequence
preservation and successful `elaborateBlock ... false`. -/
def EmptyForInitPathRunForwardAt
    (fuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    Elab.Stmt.List.hasImmediateFunctionDefinition rawCode = false →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      FrontendCompilationPath builtinContext contract
        elabState finalElabState →
      (Elab.Stmt.List.elaborateBlock rawCode false).run elabState =
        .ok (front, finalElabState) →
      StmtListNormalized builtinContext front ordered →
      ScopedSeqRunForward state.store fuel (fuel + slack)
        (rawContext.withFunctionScope []) rawCode ordered contract state

/-- Checked `for` preservation for the elaborator branch whose temporary
initializer scope is popped before the condition. The corresponding raw scope
is empty and is represented explicitly by the scope relation's `rawEmpty`
constructor. -/
theorem scopedStmtRunForward_for_withoutFunctions_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ∀ extra,
        ScopedBlockPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hSeq :
      ScopedSeqPathRunForwardAt
        fuel (slack + 1) builtinContext contract)
    (hInit :
      EmptyForInitPathRunForwardAt
        fuel (slack + 1) builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawPre rawPost rawBody : List Raw.Stmt}
    {rawCondition : Raw.Expr}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hNoFunctions :
      Elab.Stmt.List.hasImmediateFunctionDefinition rawPre = false)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      FrontendCompilationPath builtinContext contract
        elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate
        (.forLoop rawPre rawCondition rawPost rawBody)).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 2) (fuel + 2 + slack)
      rawContext (.forLoop rawPre rawCondition rawPost rawBody)
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp only [hNoFunctions, Bool.false_eq_true, ↓reduceIte] at hElab
  simp [StateT.run_bind] at hElab
  cases hPushIdentifier : Elab.pushIdentifierScope.run elabState with
  | error err => simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hElab
      cases hPre :
          (Elab.Stmt.List.elaborateBlock rawPre false).run
            identifierPushedState with
      | error err => simp [hPre] at hElab
      | ok preResult =>
          rcases preResult with ⟨frontPre, preState⟩
          simp [hPre] at hElab
          cases hCondition :
              (Elab.Expr.elaborate rawCondition).run preState with
          | error err => simp [hCondition] at hElab
          | ok conditionResult =>
              rcases conditionResult with
                ⟨frontCondition, conditionState⟩
              simp [hCondition] at hElab
              cases hPost :
                  (Elab.Stmt.List.elaborateBlock rawPost true).run
                    conditionState with
              | error err => simp [hPost] at hElab
              | ok postResult =>
                  rcases postResult with ⟨frontPost, postState⟩
                  simp [hPost] at hElab
                  cases hBody :
                      (Elab.Stmt.List.elaborateBlock rawBody true).run
                        postState with
                  | error err => simp [hBody] at hElab
                  | ok bodyResult =>
                      rcases bodyResult with ⟨frontBody, bodyState⟩
                      simp [hBody] at hElab
                      cases hPopIdentifier :
                          Elab.popIdentifierScope.run bodyState with
                      | error err => simp [hPopIdentifier] at hElab
                      | ok popIdentifierResult =>
                          rcases popIdentifierResult with
                            ⟨_, identifierPoppedState⟩
                          simp [hPopIdentifier] at hElab
                          rcases hElab with ⟨rfl, rfl⟩
                          rcases StmtNormalized.for_parts hNormalized with
                            ⟨orderedPre, orderedCondition,
                              orderedPost, orderedBody, rfl,
                              ⟨hPreNormalized⟩,
                              ⟨hConditionNormalized⟩,
                              ⟨hPostNormalized⟩,
                              ⟨hBodyNormalized⟩⟩
                          have hPushIdentifierExt :=
                            Elab.pushIdentifierScope_preserves_clzAllocation
                              hPushIdentifier hPath.entryValid
                          have hPreExt :=
                            Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                              rawPre false hPre
                              hPushIdentifierExt.after_valid
                          have hConditionExt :=
                            Elab.Expr.elaborate_preserves_clzAllocation
                              rawCondition hCondition hPreExt.after_valid
                          have hPostExt :=
                            Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                              rawPost true hPost
                              hConditionExt.after_valid
                          have hBodyExt :=
                            Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                              rawBody true hBody hPostExt.after_valid
                          have hPopIdentifierExt :=
                            Elab.popIdentifierScope_preserves_clzAllocation
                              hPopIdentifier hBodyExt.after_valid
                          have hConditionHoisted :
                              HoistedFunctionsExtend preState
                                conditionState := by
                            intro entry hEntry
                            exact
                              Elab.Expr.elaborate_preserves_hoistedFunction_mem
                                rawCondition hCondition hEntry
                          have hPostHoisted :
                              HoistedFunctionsExtend conditionState
                                postState := by
                            intro entry hEntry
                            exact
                              Elab.Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                                rawPost true hPost hEntry
                          have hBodyHoisted :
                              HoistedFunctionsExtend postState bodyState := by
                            intro entry hEntry
                            exact
                              Elab.Stmt.List.elaborateBlock_preserves_hoistedFunction_mem
                                rawBody true hBody hEntry
                          have hPopIdentifierHoisted :
                              HoistedFunctionsExtend bodyState
                                identifierPoppedState := by
                            intro entry hEntry
                            exact
                              Elab.popIdentifierScope_preserves_hoistedFunction_mem
                                hPopIdentifier hEntry
                          have hAfterBodyHoisted :
                              HoistedFunctionsExtend bodyState
                                identifierPoppedState :=
                            hPopIdentifierHoisted
                          have hBeforeBodyClz :
                              Elab.ClzAllocationExtends elabState postState :=
                            Elab.ClzAllocationExtends.trans
                              hPushIdentifierExt
                              (Elab.ClzAllocationExtends.trans hPreExt
                                (Elab.ClzAllocationExtends.trans
                                  hConditionExt hPostExt))
                          have hBodyPath :
                              FrontendCompilationPath builtinContext contract
                                postState bodyState :=
                            hPath.subpath hBeforeBodyClz hPopIdentifierExt
                              hAfterBodyHoisted
                          have hAfterPostClz :
                              Elab.ClzAllocationExtends postState
                                identifierPoppedState :=
                            Elab.ClzAllocationExtends.trans hBodyExt
                              hPopIdentifierExt
                          have hAfterPostHoisted :
                              HoistedFunctionsExtend postState
                                identifierPoppedState :=
                            HoistedFunctionsExtend.trans hBodyHoisted
                              hPopIdentifierHoisted
                          have hBeforePostClz :
                              Elab.ClzAllocationExtends elabState
                                conditionState :=
                            Elab.ClzAllocationExtends.trans
                              hPushIdentifierExt
                              (Elab.ClzAllocationExtends.trans hPreExt
                                hConditionExt)
                          have hPostPath :
                              FrontendCompilationPath builtinContext contract
                                conditionState postState :=
                            hPath.subpath hBeforePostClz hAfterPostClz
                              hAfterPostHoisted
                          have hAfterConditionClz :
                              Elab.ClzAllocationExtends conditionState
                                identifierPoppedState :=
                            Elab.ClzAllocationExtends.trans hPostExt
                              hAfterPostClz
                          have hBeforeConditionClz :
                              Elab.ClzAllocationExtends elabState preState :=
                            Elab.ClzAllocationExtends.trans
                              hPushIdentifierExt hPreExt
                          have hConditionPath :
                              ClzCompilationPath contract preState
                                conditionState :=
                            (hPath.clz.suffixPath
                              hBeforeConditionClz).prefixPath
                                hAfterConditionClz
                          have hAfterPreClz :
                              Elab.ClzAllocationExtends preState
                                identifierPoppedState :=
                            Elab.ClzAllocationExtends.trans hConditionExt
                              hAfterConditionClz
                          have hAfterConditionHoisted :
                              HoistedFunctionsExtend conditionState
                                identifierPoppedState :=
                            HoistedFunctionsExtend.trans hPostHoisted
                              hAfterPostHoisted
                          have hAfterPreHoisted :
                              HoistedFunctionsExtend preState
                                identifierPoppedState :=
                            HoistedFunctionsExtend.trans hConditionHoisted
                              hAfterConditionHoisted
                          have hPrePath :
                              FrontendCompilationPath builtinContext contract
                                identifierPushedState preState :=
                            hPath.subpath hPushIdentifierExt hAfterPreClz
                              hAfterPreHoisted
                          have hPushIdentifierScopes :
                              identifierPushedState.functionScopes =
                                elabState.functionScopes :=
                            Elab.pushIdentifierScope_preserves_functionScopes
                              hPushIdentifier
                          have hPreScopes :
                              preState.functionScopes =
                                identifierPushedState.functionScopes :=
                            Elab.Stmt.List.elaborateBlock_preserves_functionScopes
                              rawPre false hPre
                          have hPreContext :
                              PathCompiledContext builtinContext contract
                                rawContext
                                identifierPushedState.functionScopes := by
                            simpa [hPushIdentifierScopes] using hContext
                          have hPreRun :=
                            hInit (state := state) hNoFunctions
                              hPreContext hPrePath
                              hPre hPreNormalized
                          have hLoopContext :
                              PathCompiledContext builtinContext contract
                                (rawContext.withFunctionScope [])
                                preState.functionScopes := by
                            simpa [hPreScopes, hPushIdentifierScopes] using
                              hContext.withEmptyFunctionScope
                          have hConditionScopes :
                              conditionState.functionScopes =
                                preState.functionScopes :=
                            Elab.Expr.elaborate_preserves_functionScopes
                              rawCondition hCondition
                          have hPostScopes :
                              postState.functionScopes =
                                conditionState.functionScopes :=
                            Elab.Stmt.List.elaborateBlock_preserves_functionScopes
                              rawPost true hPost
                          have hPostContext :
                              PathCompiledContext builtinContext contract
                                (rawContext.withFunctionScope [])
                                conditionState.functionScopes := by
                            simpa [hConditionScopes] using hLoopContext
                          have hBodyContext :
                              PathCompiledContext builtinContext contract
                                (rawContext.withFunctionScope [])
                                postState.functionScopes := by
                            simpa [hPostScopes] using hPostContext
                          have hLengthFront :
                              frontPre.length = rawPre.length :=
                            stmtList_elaborateBlock_false_length hPre
                          have hLengthOrdered :
                              orderedPre.length = rawPre.length := by
                            rw [StmtListNormalized.length_eq hPreNormalized,
                              hLengthFront]
                          have hRawScope :=
                            rawFunctionScope_of_noImmediate hNoFunctions
                          cases rawPre with
                          | nil =>
                              have hOrderedEmpty : orderedPre = [] :=
                                List.eq_nil_of_length_eq_zero (by
                                  simpa using hLengthOrdered)
                              subst orderedPre
                              apply scopedStmtRunForward_of_exact
                              apply stmtRunForward_for_empty
                              intro loopState
                              apply loopRunForward_of_components
                              · intro n hN conditionEntry
                                apply exprRunForward_of_values
                                exact
                                  hExpr 2 n (by omega)
                                    (state := conditionEntry)
                                    hLoopContext hConditionPath hCondition
                                    hConditionNormalized
                              · intro n hN postEntry
                                exact
                                  hBlock 2 n (by omega)
                                    (state := postEntry)
                                    hPostContext hPostPath hPost
                                    hPostNormalized
                              · intro n hN bodyEntry
                                exact
                                  hBlock 2 n (by omega)
                                    (state := bodyEntry)
                                    hBodyContext hBodyPath hBody
                                    hBodyNormalized
                          | cons rawHead rawTail =>
                              have hOrderedNonempty : orderedPre ≠ [] := by
                                intro hEmpty
                                subst orderedPre
                                simp at hLengthOrdered
                              have hOrderedForm :
                                  orderedForStmt orderedPre orderedCondition
                                      orderedPost orderedBody =
                                    .Block
                                      (orderedPre ++
                                        [.For orderedCondition orderedPost
                                          orderedBody]) := by
                                cases orderedPre with
                                | nil => exact (hOrderedNonempty rfl).elim
                                | cons head tail => rfl
                              rw [hOrderedForm]
                              apply scopedStmtRunForward_of_exact
                              apply stmtRunForward_for_nonempty
                                hRawScope hLengthOrdered hOrderedNonempty
                                hPreRun
                              intro loopState
                              apply loopRunForward_after_nonemptyPrefix
                              · intro n hN conditionEntry
                                apply exprRunForward_of_values
                                exact
                                  hExpr 0 n (by omega)
                                    (state := conditionEntry)
                                    hLoopContext hConditionPath hCondition
                                    hConditionNormalized
                              · intro n hN postEntry
                                exact
                                  hBlock 0 n (by omega)
                                    (state := postEntry)
                                    hPostContext hPostPath hPost
                                    hPostNormalized
                              · intro n hN bodyEntry
                                exact
                                  hBlock 0 n (by omega)
                                    (state := bodyEntry)
                                    hBodyContext hBodyPath hBody
                                    hBodyNormalized

theorem scopedStmtRunForward_for_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ∀ extra,
        ScopedBlockPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hSeq :
      ScopedSeqPathRunForwardAt
        fuel (slack + 1) builtinContext contract)
    (hInit :
      EmptyForInitPathRunForwardAt
        fuel (slack + 1) builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawPre rawPost rawBody : List Raw.Stmt}
    {rawCondition : Raw.Expr}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      FrontendCompilationPath builtinContext contract
        elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate
        (.forLoop rawPre rawCondition rawPost rawBody)).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 2) (fuel + 2 + slack)
      rawContext (.forLoop rawPre rawCondition rawPost rawBody)
      ordered contract state := by
  cases hHasFunctions :
      Elab.Stmt.List.hasImmediateFunctionDefinition rawPre with
  | false =>
      exact
        scopedStmtRunForward_for_withoutFunctions_of_path_below
          hExpr hBlock hSeq hInit
          hHasFunctions hContext hPath hElab hNormalized
  | true =>
      exact
        scopedStmtRunForward_for_withFunctions_of_path_below
          hExpr hBlock hSeq hHasFunctions hContext hPath
          hElab hNormalized

theorem scopedStmtPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedStmtPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawStmt front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  exact scopedStmtRunForward_of_exact stmtRunForward_zero

/-- Generic checked statement classifier. Ordinary structural statements are
proved here from occurrence-local expression/block paths; only the four
semantically distinct call/control families are delegated to one bundled
provider. -/
theorem scopedStmtPathRunForwardAt_succ_of_special
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ∀ extra,
        ScopedBlockPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hSpecial :
      ScopedStmtSpecialRunForwardAt
        (fuel + 1) slack builtinContext contract) :
    ScopedStmtPathRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawStmt front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  cases rawStmt with
  | block rawBody =>
      unfold Elab.Stmt.elaborate at hElab
      simp at hElab
      cases hBody :
          (Elab.Stmt.List.elaborateBlock rawBody true).run elabState with
      | error err => simp [hBody] at hElab
      | ok bodyResult =>
          rcases bodyResult with ⟨frontBody, bodyState⟩
          simp [hBody] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.block_parts hNormalized with
            ⟨orderedBody, rfl, ⟨hBodyNormalized⟩⟩
          have hBodyRun :=
            hBlock 1 fuel (by omega) (state := state)
              hContext hPath hBody hBodyNormalized
          apply scopedStmtRunForward_of_exact
          simpa [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
              (stmtRunForward_block_succ hBodyRun)
  | variableDeclaration names value? =>
      cases value? with
      | none =>
          have hRun :=
            stmtRunForward_of_elaborated_variableDeclaration_none
              (rawFuel := fuel) (orderedFuel := fuel + slack)
              (rawContext := rawContext) (contract := contract)
              (state := state) hElab hNormalized
          exact scopedStmtRunForward_of_exact
            (by simpa [Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hRun)
      | some rawValue =>
          unfold Elab.Stmt.elaborate at hElab
          simp at hElab
          cases hValue :
              (Elab.Expr.elaborate rawValue).run elabState with
          | error err => simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              simp [hValue] at hElab
              cases hDeclare :
                  (Elab.declareIdentifiers names "variable").run
                    valueState with
              | error err => simp [hDeclare] at hElab
              | ok declareResult =>
                  rcases declareResult with ⟨_, declaredState⟩
                  simp [hDeclare] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  rcases StmtNormalized.let_some_parts hNormalized with
                    ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
                  have hValueExt :=
                    Elab.Expr.elaborate_preserves_clzAllocation rawValue
                      hValue hPath.entryValid
                  have hDeclareExt :=
                    Elab.declareIdentifiers_preserves_clzAllocation
                      names "variable" hDeclare hValueExt.after_valid
                  have hValuePath :
                      ClzCompilationPath contract elabState valueState :=
                    hPath.clz.prefixPath hDeclareExt
                  have hValueRun :=
                    hExpr 0 fuel (by omega) (state := state)
                      hContext hValuePath hValue hValueNormalized
                  apply scopedStmtRunForward_of_exact
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                      (stmtRunForward_variableDeclaration_some_succ
                        hValueRun)
  | assignment names rawValue =>
      unfold Elab.Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hVisible :
          (Elab.requireIdentifiersVisible names "assignment").run
            elabState with
      | error err => simp [hVisible] at hElab
      | ok visibleResult =>
          rcases visibleResult with ⟨_, visibleState⟩
          simp [hVisible] at hElab
          cases hValue :
              (Elab.Expr.elaborate rawValue).run visibleState with
          | error err => simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              simp [hValue] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtNormalized.assign_parts hNormalized with
                ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
              have hVisibleExt :=
                Elab.requireIdentifiersVisible_preserves_clzAllocation
                  names "assignment" hVisible hPath.entryValid
              have hValuePath :
                  ClzCompilationPath contract visibleState valueState :=
                hPath.clz.suffixPath hVisibleExt
              have hVisibleScopes :
                  visibleState.functionScopes =
                    elabState.functionScopes :=
                Elab.requireIdentifiersVisible_preserves_functionScopes
                  names "assignment" hVisible
              have hValueContext :
                  PathCompiledContext builtinContext contract
                    rawContext visibleState.functionScopes := by
                simpa [hVisibleScopes] using hContext
              have hValueRun :=
                hExpr 0 fuel (by omega) (state := state)
                  hValueContext hValuePath hValue hValueNormalized
              apply scopedStmtRunForward_of_exact
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using
                  (stmtRunForward_assignment_succ hValueRun)
  | expressionStatement expr =>
      exact hSpecial (.expressionStatement expr) hCompatible hContext
        hPath hElab hNormalized
  | functionDefinition name params returns body =>
      exact hSpecial (.functionDefinition name params returns body)
        hCompatible hContext hPath hElab hNormalized
  | switch scrutinee cases default =>
      exact hSpecial (.switch scrutinee cases default)
        hCompatible hContext hPath hElab hNormalized
  | forLoop pre condition post body =>
      exact hSpecial (.forLoop pre condition post body)
        hCompatible hContext hPath hElab hNormalized
  | ifThen rawCondition rawBody =>
      unfold Elab.Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hCondition :
          (Elab.Expr.elaborate rawCondition).run elabState with
      | error err => simp [hCondition] at hElab
      | ok conditionResult =>
          rcases conditionResult with
            ⟨frontCondition, conditionState⟩
          simp [hCondition] at hElab
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawBody true).run
                conditionState with
          | error err => simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtNormalized.if_parts hNormalized with
                ⟨orderedCondition, orderedBody, rfl,
                  ⟨hConditionNormalized⟩, ⟨hBodyNormalized⟩⟩
              have hConditionExt :=
                Elab.Expr.elaborate_preserves_clzAllocation rawCondition
                  hCondition hPath.entryValid
              have hBodyExt :=
                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                  rawBody true hBody hConditionExt.after_valid
              have hConditionPath :
                  ClzCompilationPath contract
                    elabState conditionState :=
                hPath.clz.prefixPath hBodyExt
              have hBodyPath :
                  FrontendCompilationPath builtinContext contract
                    conditionState bodyState :=
                hPath.suffixPath hConditionExt
              have hConditionScopes :
                  conditionState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes
                  rawCondition hCondition
              have hBodyContext :
                  PathCompiledContext builtinContext contract
                    rawContext conditionState.functionScopes := by
                simpa [hConditionScopes] using hContext
              have hConditionRun :=
                hExpr 0 fuel (by omega) (state := state)
                  hContext hConditionPath
                  hCondition hConditionNormalized
              apply scopedStmtRunForward_of_exact
              have hIf :=
                stmtRunForward_ifThen_succ
                  (rawFuel := fuel) (orderedFuel := fuel + slack)
                  (context := rawContext) (contract := contract)
                  (state := state)
                  (exprRunForward_of_values hConditionRun)
                  (fun stateAfterCondition value _hTruthy =>
                    hBlock 0 fuel (by omega)
                      (state := stateAfterCondition)
                      hBodyContext hBodyPath hBody hBodyNormalized)
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hIf
  | «break» =>
      apply scopedStmtRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (stmtRunForward_of_elaborated_break
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (rawContext := rawContext) (contract := contract)
          (state := state) hElab hNormalized)
  | «continue» =>
      apply scopedStmtRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (stmtRunForward_of_elaborated_continue
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (rawContext := rawContext) (contract := contract)
          (state := state) hElab hNormalized)
  | «leave» =>
      apply scopedStmtRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (stmtRunForward_of_elaborated_leave
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (rawContext := rawContext) (contract := contract)
          (state := state) hElab hNormalized)

theorem scopedSeqRunForward_of_exact
    {entryStore : EvmYul.Yul.VarStore}
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExact :
      SeqRunForward rawFuel orderedFuel
        context rawCode orderedCode contract state) :
    ScopedSeqRunForward entryStore rawFuel orderedFuel
      context rawCode orderedCode contract state := by
  unfold SeqRunForward ScopedSeqRunForward at *
  apply Simulation.Interaction.ForwardRel.mono hExact
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ExceptRel.error rfl
  | ok rawState =>
      cases rawState with
      | Ok => exact Simulation.Interaction.ExceptRel.ok rfl
      | OutOfFuel => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)
      | Checkpoint => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)

theorem seqRunForward_zero
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    SeqRunForward 0 orderedFuel context rawCode orderedCode contract state := by
  unfold SeqRunForward
  rw [Raw.SourceSemantics.execSeq_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem seqRunForward_nil_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    SeqRunForward (rawFuel + 1) (orderedFuel + 1)
      context [] [] contract state := by
  unfold SeqRunForward
  rw [Raw.SourceSemantics.ExecSeq.nil_succ]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

/-- Generic list constructor for the recursive frontend proof. The head and
tail share one residual fuel on each side; only regular states enter the tail. -/
theorem seqRunForward_cons
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {rawRest : List Raw.Stmt}
    {orderedStmt : Frontend.AstStmt}
    {orderedRest : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hHead :
      StmtRunForward rawFuel orderedFuel
        context rawStmt orderedStmt contract state)
    (hTail :
      ∀ shared vars,
        SeqRunForward rawFuel orderedFuel context rawRest orderedRest contract
          (.Ok shared vars)) :
    SeqRunForward (rawFuel + 1) (orderedFuel + 1)
      context (rawStmt :: rawRest) (orderedStmt :: orderedRest)
      contract state := by
  unfold SeqRunForward StmtRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  refine Simulation.Interaction.ForwardRel.bind_custom hHead ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok stateAfterStmt =>
      cases stateAfterStmt with
      | Ok shared vars => exact hTail shared vars
      | OutOfFuel => exact Simulation.Interaction.ForwardRel.done rfl
      | Checkpoint jump => exact Simulation.Interaction.ForwardRel.done rfl

/-- Generic block-scoped list constructor. The strengthened done relation
forces exact agreement whenever the tail is entered. -/
theorem scopedSeqRunForward_cons
    {entryStore : EvmYul.Yul.VarStore}
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {rawRest : List Raw.Stmt}
    {orderedStmt : Frontend.AstStmt}
    {orderedRest : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hHead :
      ScopedStmtRunForward entryStore rawFuel orderedFuel
        context rawStmt orderedStmt contract state)
    (hTail :
      ∀ shared vars,
        ScopedSeqRunForward entryStore rawFuel orderedFuel
          context rawRest orderedRest contract (.Ok shared vars)) :
    ScopedSeqRunForward entryStore (rawFuel + 1) (orderedFuel + 1)
      context (rawStmt :: rawRest) (orderedStmt :: orderedRest)
      contract state := by
  unfold ScopedSeqRunForward ScopedStmtRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  refine Simulation.Interaction.ForwardRel.bind_custom hHead ?_
  intro rawDone orderedDone hDone
  cases hDone with
  | error hError =>
      subst_vars
      exact
        Simulation.Interaction.ForwardRel.done
          (Simulation.Interaction.ExceptRel.error rfl)
  | @ok rawState orderedState hState =>
      cases rawState with
      | Ok shared vars =>
          subst orderedState
          exact hTail shared vars
      | OutOfFuel =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok (Or.inl rfl))
          | inr hRestricted =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok (Or.inr rfl))
      | Checkpoint jump =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok (Or.inl rfl))
          | inr hRestricted =>
              subst orderedState
              cases jump <;>
                exact
                  Simulation.Interaction.ForwardRel.done
                    (Simulation.Interaction.ExceptRel.ok (Or.inr rfl))

theorem scopedSeqPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedSeqPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  exact scopedSeqRunForward_of_exact seqRunForward_zero

/-- Fuel-recursive statement-list theorem. It splits the actual checked
elaboration path at the head occurrence, carries the same lexical context into
the tail, and uses no generated-name or semantic replay premise. -/
theorem scopedSeqPathRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hStmt :
      ScopedStmtPathRunForwardAt fuel slack builtinContext contract)
    (hSeq :
      ScopedSeqPathRunForwardAt fuel slack builtinContext contract) :
    ScopedSeqPathRunForwardAt (fuel + 1) slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  cases rawCode with
  | nil =>
      simp [Elab.Stmt.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := StmtListNormalized.nil_ordered hNormalized
      subst ordered
      apply scopedSeqRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (seqRunForward_nil_succ
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state))
  | cons rawHead rawTail =>
      unfold Elab.Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Stmt.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Stmt.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              have hHeadExt :=
                Elab.Stmt.elaborate_preserves_clzAllocation rawHead
                  hHead hPath.entryValid
              have hTailExt :=
                Elab.Stmt.List.elaborate_preserves_clzAllocation rawTail
                  hTail hHeadExt.after_valid
              have hTailHoisted :
                  HoistedFunctionsExtend headElabState tailElabState := by
                intro entry hEntry
                exact
                  Elab.Stmt.List.elaborate_preserves_hoistedFunction_mem
                    rawTail hTail hEntry
              have hHeadPath :
                  FrontendCompilationPath builtinContext contract
                    elabState headElabState :=
                hPath.prefixPath hTailExt hTailHoisted
              have hTailPath :
                  FrontendCompilationPath builtinContext contract
                    headElabState tailElabState :=
                hPath.suffixPath hHeadExt
              have hHeadScopes :
                  headElabState.functionScopes =
                    elabState.functionScopes :=
                Elab.Stmt.elaborate_preserves_functionScopes rawHead hHead
              have hTailContext :
                  PathCompiledContext builtinContext contract
                    rawContext headElabState.functionScopes := by
                simpa [hHeadScopes] using hContext
              have hHeadRun :=
                hStmt hCompatible hContext hHeadPath hHead hHeadNormalized
              have hCons :=
                scopedSeqRunForward_cons
                  (entryStore := entryStore)
                  (rawFuel := fuel) (orderedFuel := fuel + slack)
                  (context := rawContext) (rawStmt := rawHead)
                  (rawRest := rawTail) (orderedStmt := orderedHead)
                  (orderedRest := orderedTail) (contract := contract)
                  (state := state) hHeadRun
                  (fun shared vars =>
                    hSeq (state := .Ok shared vars)
                      (by trivial) hTailContext hTailPath
                      hTail hTailNormalized)
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hCons

theorem seqRunForward_of_elaboration
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hStmt :
      StmtElaborationRunForward rawContext builtinContext contract) :
    ∀ {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
      {ordered : List Frontend.AstStmt}
      {elabState finalElabState : Elab.State},
      (Elab.Stmt.List.elaborate rawCode).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          ∀ (rawBase orderedBase : Nat) (state : State),
            SeqRunForward
              (rawBase + rawCode.length + 1)
              (orderedBase + rawCode.length + 1)
              rawContext rawCode ordered contract state := by
  intro rawCode
  induction rawCode with
  | nil =>
      intro front ordered elabState finalElabState hElab hNormalized
        rawBase orderedBase state
      simp [Elab.Stmt.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := StmtListNormalized.nil_ordered hNormalized
      subst ordered
      simpa using
        (seqRunForward_nil_succ
          (rawFuel := rawBase) (orderedFuel := orderedBase)
          (context := rawContext) (contract := contract) (state := state))
  | cons rawHead rawTail ih =>
      intro front ordered elabState finalElabState hElab hNormalized
        rawBase orderedBase state
      unfold Elab.Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Stmt.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Stmt.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              let rawTailFuel := rawBase + rawTail.length + 1
              let orderedTailFuel := orderedBase + rawTail.length + 1
              have hHeadRun :=
                hStmt rawTailFuel orderedTailFuel
                  (state := state) hHead hHeadNormalized
              have hCons :=
                seqRunForward_cons
                  (rawFuel := rawTailFuel)
                  (orderedFuel := orderedTailFuel)
                  (context := rawContext) (rawStmt := rawHead)
                  (rawRest := rawTail) (orderedStmt := orderedHead)
                  (orderedRest := orderedTail) (contract := contract)
                  (state := state) hHeadRun
                  (fun shared vars =>
                    ih hTail hTailNormalized rawBase orderedBase
                      (.Ok shared vars))
              simpa [rawTailFuel, orderedTailFuel, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hCons

theorem seqRunForward_cons_functionDefinition_omitted_ok
    {fuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body rest : List Raw.Stmt}
    {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract}
    {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
    (hRest :
      SeqRunForward (fuel + 1) orderedFuel
        context rest orderedCode contract (.Ok shared vars)) :
    SeqRunForward (fuel + 2) orderedFuel
      context
      (.functionDefinition name params returns body :: rest)
      orderedCode contract (.Ok shared vars) := by
  unfold SeqRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  simpa [Simulation.Interaction.bind_pure]

theorem scopedSeqRunForward_cons_functionDefinition_omitted_ok
    {fuel orderedFuel : Nat}
    {entryStore : EvmYul.Yul.VarStore}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body rest : List Raw.Stmt}
    {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract}
    {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
    (hRest :
      ScopedSeqRunForward entryStore (fuel + 1) orderedFuel
        context rest orderedCode contract (.Ok shared vars)) :
    ScopedSeqRunForward entryStore (fuel + 2) orderedFuel
      context
      (.functionDefinition name params returns body :: rest)
      orderedCode contract (.Ok shared vars) := by
  unfold ScopedSeqRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  simpa [Simulation.Interaction.bind_pure]

theorem scopedSeqRunForward_cons_one
    {orderedFuel : Nat}
    {entryStore : EvmYul.Yul.VarStore}
    {context : Raw.SourceSemantics.Context}
    {rawHead : Raw.Stmt} {rawRest : List Raw.Stmt}
    {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    ScopedSeqRunForward entryStore 1 orderedFuel
      context (rawHead :: rawRest) orderedCode contract state := by
  unfold ScopedSeqRunForward
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  simp [Raw.SourceSemantics.exec, Raw.SourceSemantics.fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

/-- Generic lexical-block constructor. A recursively preserved statement list
under the block's raw function scope yields exact block outcomes because both
semantics apply the same entry-store restriction. -/
theorem blockCodeRunForward_of_scope_seq
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hScope : Raw.SourceSemantics.functionScope? rawCode = some scope)
    (hSeq :
      SeqRunForward rawFuel orderedFuel
        (context.withFunctionScope scope)
        rawCode orderedCode contract state) :
    BlockCodeRunForward (rawFuel + 1) (orderedFuel + 1)
      context rawCode orderedCode contract state := by
  unfold BlockCodeRunForward SeqRunForward at *
  rw [Raw.SourceSemantics.ExecBlock.succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [hScope]
  refine Simulation.Interaction.ForwardRel.bind_custom hSeq ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok stateAfterBody =>
      exact Simulation.Interaction.ForwardRel.done rfl

theorem seqRunForward_immutablePatches
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {references : List Frontend.ImmutableReference}
    {rawBase rawValue : Raw.Expr} {rawStmts : List Raw.Stmt}
    {orderedBase orderedValue : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hPatch :
      Raw.SourceSemantics.patchSetImmutableStmts?
        references rawBase rawValue = some rawStmts)
    (hBase :
      ∀ extra n, n < fuel → ∀ state,
        ExprRunForward n (n + (slack + extra))
          context rawBase orderedBase contract state)
    (hValue :
      ∀ extra n, n < fuel → ∀ state,
        ExprRunForward n (n + (slack + extra))
          context rawValue orderedValue contract state) :
    SeqRunForward fuel (fuel + slack) context rawStmts
      (orderedImmutablePatchStmts references orderedBase orderedValue)
      contract state := by
  induction references generalizing fuel rawStmts state with
  | nil =>
      simp [Raw.SourceSemantics.patchSetImmutableStmts?] at hPatch
      subst rawStmts
      cases fuel with
      | zero => exact seqRunForward_zero
      | succ residual =>
          simpa [orderedImmutablePatchStmts, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using
            (seqRunForward_nil_succ
              (rawFuel := residual) (orderedFuel := residual + slack)
              (context := context) (contract := contract) (state := state))
  | cons reference rest ih =>
      unfold Raw.SourceSemantics.patchSetImmutableStmts? at hPatch
      cases hHead :
          Raw.SourceSemantics.patchSetImmutableStmt?
            reference rawBase rawValue with
      | none => simp [hHead] at hPatch
      | some rawHead =>
          cases hTail :
              Raw.SourceSemantics.patchSetImmutableStmts?
                rest rawBase rawValue with
          | none => simp [hHead, hTail] at hPatch
          | some rawTail =>
              simp [hHead, hTail] at hPatch
              subst rawStmts
              cases fuel with
              | zero => exact seqRunForward_zero
              | succ residual =>
                  have hHeadRun :=
                    stmtRunForward_immutablePatchStmt
                      (fuel := residual) (slack := slack)
                      (context := context) (reference := reference)
                      (rawBase := rawBase) (rawValue := rawValue)
                      (orderedBase := orderedBase)
                      (orderedValue := orderedValue)
                      (contract := contract) (state := state) hHead
                      (fun extra n hN state =>
                        hBase extra n (by omega) state)
                      (fun extra n hN state =>
                        hValue extra n (by omega) state)
                  have hTailRun :
                      ∀ stateAfter,
                        SeqRunForward residual (residual + slack)
                          context rawTail
                          (orderedImmutablePatchStmts
                            rest orderedBase orderedValue)
                          contract stateAfter := by
                    intro stateAfter
                    exact
                      ih (fuel := residual) (state := stateAfter) hTail
                        (fun extra n hN state =>
                          hBase extra n (by omega) state)
                        (fun extra n hN state =>
                          hValue extra n (by omega) state)
                  simpa [orderedImmutablePatchStmts, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm] using
                    (seqRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := context) (rawStmt := rawHead)
                      (rawRest := rawTail)
                      (orderedStmt :=
                        orderedImmutablePatchStmt
                          reference orderedBase orderedValue)
                      (orderedRest :=
                        orderedImmutablePatchStmts
                          rest orderedBase orderedValue)
                      (contract := contract) (state := state)
                      hHeadRun (fun shared vars =>
                        hTailRun (.Ok shared vars)))

theorem blockCodeRunForward_immutablePatches
    {fuel slack : Nat}
    {context : Raw.SourceSemantics.Context}
    {references : List Frontend.ImmutableReference}
    {rawBase rawValue : Raw.Expr} {rawStmts : List Raw.Stmt}
    {orderedBase orderedValue : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hPatch :
      Raw.SourceSemantics.patchSetImmutableStmts?
        references rawBase rawValue = some rawStmts)
    (hBase :
      ∀ extra n, n < fuel → ∀ state,
        ExprRunForward n (n + (slack + extra))
          context rawBase orderedBase contract state)
    (hValue :
      ∀ extra n, n < fuel → ∀ state,
        ExprRunForward n (n + (slack + extra))
          context rawValue orderedValue contract state) :
    BlockCodeRunForward fuel (fuel + slack) context rawStmts
      (orderedImmutablePatchStmts references orderedBase orderedValue)
      contract state := by
  cases fuel with
  | zero => exact blockCodeRunForward_zero
  | succ residual =>
      have hScope :=
        Raw.SourceSemantics.patchSetImmutableStmts?_functionScope hPatch
      have hSeq :
          SeqRunForward residual (residual + slack)
            (context.withFunctionScope []) rawStmts
            (orderedImmutablePatchStmts
              references orderedBase orderedValue) contract state :=
        seqRunForward_immutablePatches
          (fuel := residual) (slack := slack)
          (context := context.withFunctionScope [])
          (references := references) (rawBase := rawBase)
          (rawValue := rawValue) (orderedBase := orderedBase)
          (orderedValue := orderedValue) (contract := contract)
          (state := state) hPatch
          (fun extra n hN state =>
            (hBase extra n (by omega) state).withEmptyFunctionScope)
          (fun extra n hN state =>
            (hValue extra n (by omega) state).withEmptyFunctionScope)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (blockCodeRunForward_of_scope_seq
          (rawFuel := residual) (orderedFuel := residual + slack)
          (context := context) (scope := []) (rawCode := rawStmts)
          (orderedCode :=
            orderedImmutablePatchStmts
              references orderedBase orderedValue)
          (contract := contract) (state := state) hScope hSeq)

theorem stmtRunForward_setimmutable_succ
    {fuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawBase rawNameArg rawValue : Raw.Expr}
    {immutableName : Name}
    {references : List Frontend.ImmutableReference}
    {rawStmts : List Raw.Stmt}
    {orderedStmts : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hName :
      Raw.SourceSemantics.objectBuiltinNameArg? rawNameArg =
        some immutableName)
    (hRefs :
      context.objectBuiltins.findImmutableReferences? immutableName =
        some references)
    (hPatch :
      Raw.SourceSemantics.patchSetImmutableStmts?
        references rawBase rawValue = some rawStmts)
    (hBlock :
      BlockCodeRunForward fuel orderedFuel
        context rawStmts orderedStmts contract state) :
    StmtRunForward (fuel + 1) orderedFuel context
      (.expressionStatement
        (.functionCall "setimmutable" [rawBase, rawNameArg, rawValue]))
      (.Block orderedStmts) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hName, hRefs, hPatch]
  exact hBlock

theorem scopedStmtRunForward_setimmutable_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawBase rawNameArg rawValue : Raw.Expr}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath : ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate
        (.expressionStatement
          (.functionCall "setimmutable"
            [rawBase, rawNameArg, rawValue]))).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 1) (fuel + 1 + slack)
      rawContext
      (.expressionStatement
        (.functionCall "setimmutable" [rawBase, rawNameArg, rawValue]))
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  have hSupported :
      CallClass.supportedExpressionStatementCall? "setimmutable" = true :=
    rfl
  simp [hSupported, StateT.run_bind] at hElab
  cases hExprElab :
      (Elab.Expr.elaborate
        (.functionCall "setimmutable"
          [rawBase, rawNameArg, rawValue])).run elabState with
  | error err => simp [hExprElab] at hElab
  | ok exprResult =>
      rcases exprResult with ⟨frontExpr, exprState⟩
      simp [hExprElab] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases objectBuiltinCall_elaboration_parts
          (name := "setimmutable") (rawArgs := [rawBase, rawNameArg, rawValue])
          (by decide) (by decide) rfl hExprElab with
        ⟨frontArgs, argsState, hArgs, hFront, hFinal⟩
      subst argsState
      subst frontExpr
      have hLength := exprList_elaborate_length hArgs
      simp at hLength
      cases frontArgs with
      | nil => simp at hLength
      | cons frontBase frontRest =>
          cases frontRest with
          | nil => simp at hLength
          | cons frontNameArg frontRest =>
              cases frontRest with
              | nil => simp at hLength
              | cons frontValue frontRest =>
                  cases frontRest with
                  | cons extra rest => simp at hLength
                  | nil =>
                      rcases exprList_elaborate_three_parts hArgs with
                        ⟨baseState, nameState,
                          hBaseElab, hNameElab, hValueElab⟩
                      rcases StmtNormalized.setimmutable_parts
                          hNormalized with
                        ⟨immutableName, references,
                          resolvedBase, resolvedValue, frontPatch,
                          orderedBase, orderedValue,
                          hFrontName, hFrontRefs, hNonempty,
                          hFrontPatch, rfl,
                          ⟨hBaseNormalized⟩, ⟨hValueNormalized⟩⟩
                      have hRawName :=
                        rawObjectBuiltinNameArg_of_elaboration
                          hNameElab hFrontName
                      have hRawRefs :
                          rawContext.objectBuiltins.findImmutableReferences?
                              immutableName =
                            some references := by
                        rw [ObjectBuiltinContextsAgree.findImmutableReferences?_eq
                          hContext.objectBuiltins]
                        exact hFrontRefs
                      rcases
                          rawImmutablePatchStmts_exists_of_frontend
                            (rawBase := rawBase) (rawValue := rawValue)
                            hFrontPatch with
                        ⟨rawPatch, hRawPatch⟩
                      have hBaseExt :=
                        Elab.Expr.elaborate_preserves_clzAllocation rawBase
                          hBaseElab hPath.entryValid
                      have hNameExt :=
                        Elab.Expr.elaborate_preserves_clzAllocation rawNameArg
                          hNameElab hBaseExt.after_valid
                      have hValueExt :=
                        Elab.Expr.elaborate_preserves_clzAllocation rawValue
                          hValueElab hNameExt.after_valid
                      have hBasePath :
                          ClzCompilationPath contract elabState baseState :=
                        hPath.prefixPath
                          (Elab.ClzAllocationExtends.trans
                            hNameExt hValueExt)
                      have hValuePath :
                          ClzCompilationPath contract
                            nameState exprState :=
                        hPath.suffixPath
                          (Elab.ClzAllocationExtends.trans
                            hBaseExt hNameExt)
                      have hBaseScopes :
                          baseState.functionScopes =
                            elabState.functionScopes :=
                        Elab.Expr.elaborate_preserves_functionScopes
                          rawBase hBaseElab
                      have hNameScopes :
                          nameState.functionScopes =
                            baseState.functionScopes :=
                        Elab.Expr.elaborate_preserves_functionScopes
                          rawNameArg hNameElab
                      have hValueContext :
                          PathCompiledContext builtinContext contract
                            rawContext nameState.functionScopes := by
                        simpa [hNameScopes, hBaseScopes] using hContext
                      have hBlock :
                          BlockCodeRunForward fuel (fuel + (slack + 1))
                            rawContext rawPatch
                            (orderedImmutablePatchStmts
                              references orderedBase orderedValue)
                            contract state :=
                        blockCodeRunForward_immutablePatches
                          (fuel := fuel) (slack := slack + 1)
                          (context := rawContext) (references := references)
                          (rawBase := rawBase) (rawValue := rawValue)
                          (orderedBase := orderedBase)
                          (orderedValue := orderedValue)
                          (contract := contract) (state := state) hRawPatch
                          (fun extra n hN state => by
                            apply exprRunForward_of_values
                            simpa [Nat.add_assoc, Nat.add_comm,
                              Nat.add_left_comm] using
                              (hExpr (extra + 1) n (by omega) (state := state)
                                hContext hBasePath hBaseElab
                                hBaseNormalized))
                          (fun extra n hN state => by
                            apply exprRunForward_of_values
                            simpa [Nat.add_assoc, Nat.add_comm,
                              Nat.add_left_comm] using
                              (hExpr (extra + 1) n (by omega) (state := state)
                                hValueContext hValuePath hValueElab
                                hValueNormalized))
                      apply scopedStmtRunForward_of_exact
                      have hStmt :=
                        stmtRunForward_setimmutable_succ
                          (fuel := fuel)
                          (orderedFuel := fuel + (slack + 1))
                          (context := rawContext) (rawBase := rawBase)
                          (rawNameArg := rawNameArg)
                          (rawValue := rawValue)
                          (immutableName := immutableName)
                          (references := references) (rawStmts := rawPatch)
                          (orderedStmts :=
                            orderedImmutablePatchStmts
                              references orderedBase orderedValue)
                          (contract := contract) (state := state)
                          hRawName hRawRefs hRawPatch hBlock
                      simpa [Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using hStmt

theorem blockCodeRunForward_of_scope_scopedSeq
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hScope : Raw.SourceSemantics.functionScope? rawCode = some scope)
    (hSeq :
      ScopedSeqRunForward state.store rawFuel orderedFuel
        (context.withFunctionScope scope)
        rawCode orderedCode contract state) :
    BlockCodeRunForward (rawFuel + 1) (orderedFuel + 1)
      context rawCode orderedCode contract state := by
  unfold BlockCodeRunForward ScopedSeqRunForward at *
  rw [Raw.SourceSemantics.ExecBlock.succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [hScope]
  refine Simulation.Interaction.ForwardRel.bind_custom hSeq ?_
  intro rawDone orderedDone hDone
  cases hDone with
  | error hError =>
      subst_vars
      exact Simulation.Interaction.ForwardRel.done rfl
  | @ok rawState orderedState hState =>
      cases rawState with
      | Ok shared vars =>
          subst orderedState
          exact Simulation.Interaction.ForwardRel.done rfl
      | OutOfFuel =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact Simulation.Interaction.ForwardRel.done rfl
          | inr hRestricted =>
              subst orderedState
              apply Simulation.Interaction.ForwardRel.done
              unfold SameDoneRel
              congr 1
      | Checkpoint jump =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact Simulation.Interaction.ForwardRel.done rfl
          | inr hRestricted =>
              subst orderedState
              apply Simulation.Interaction.ForwardRel.done
              unfold SameDoneRel
              congr 1
              exact
                (Yul.InteractionSemantics.State.restrictStoreTo_idem
                  (.Checkpoint jump) state.store).symm

/-- Generic checked lexical-block constructor. Successful block elaboration
constructs its raw/generated local scope, the hoist path constructs every
callee binding, and recursive sequence preservation supplies body execution. -/
theorem scopedBlockPathRunForwardAt_succ_of_seq
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hSeq :
      ScopedSeqPathRunForwardAt fuel slack builtinContext contract) :
    ScopedBlockPathRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  unfold Elab.Stmt.List.elaborateBlock at hElab
  simp [StateT.run_bind] at hElab
  cases hPushIdentifier : Elab.pushIdentifierScope.run elabState with
  | error err => simp [hPushIdentifier] at hElab
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hElab
      cases hScope :
          (Elab.Stmt.List.localFunctionScope rawCode).run
            identifierPushedState with
      | error err => simp [hScope] at hElab
      | ok scopeResult =>
          rcases scopeResult with ⟨generatedScope, scopeState⟩
          simp [hScope] at hElab
          cases hPushFunction :
              (Elab.pushFunctionScope generatedScope).run scopeState with
          | error err => simp [hPushFunction] at hElab
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, functionPushedState⟩
              simp [hPushFunction] at hElab
              cases hHoist :
                  (Elab.Stmt.List.hoistLocalFunctions
                    rawCode generatedScope).run functionPushedState with
              | error err => simp [hHoist] at hElab
              | ok hoistResult =>
                  rcases hoistResult with ⟨_, hoistState⟩
                  simp [hHoist] at hElab
                  cases hCode :
                      (Elab.Stmt.List.elaborate rawCode).run hoistState with
                  | error err => simp [hCode] at hElab
                  | ok codeResult =>
                      rcases codeResult with ⟨frontCode, codeState⟩
                      simp [hCode] at hElab
                      cases hPopFunction :
                          Elab.popFunctionScope.run codeState with
                      | error err => simp [hPopFunction] at hElab
                      | ok popFunctionResult =>
                          rcases popFunctionResult with
                            ⟨_, functionPoppedState⟩
                          simp [hPopFunction] at hElab
                          cases hPopIdentifier :
                              Elab.popIdentifierScope.run
                                functionPoppedState with
                          | error err => simp [hPopIdentifier] at hElab
                          | ok popIdentifierResult =>
                              rcases popIdentifierResult with
                                ⟨_, identifierPoppedState⟩
                              simp [hPopIdentifier] at hElab
                              rcases hElab with ⟨rfl, rfl⟩
                              rcases localFunctionScope_rawFunctionScope
                                  hScope with
                                ⟨rawScope, hRawScope, _hNames⟩
                              have hPushIdentifierExt :=
                                Elab.pushIdentifierScope_preserves_clzAllocation
                                  hPushIdentifier hPath.entryValid
                              have hScopeExt :=
                                Elab.Stmt.List.localFunctionScope_preserves_clzAllocation
                                  rawCode hScope
                                  hPushIdentifierExt.after_valid
                              have hPushFunctionExt :=
                                Elab.pushFunctionScope_preserves_clzAllocation
                                  generatedScope hPushFunction
                                  hScopeExt.after_valid
                              have hHoistExt :=
                                Elab.Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                                  rawCode generatedScope hHoist
                                  hPushFunctionExt.after_valid
                              have hCodeExt :=
                                Elab.Stmt.List.elaborate_preserves_clzAllocation
                                  rawCode hCode hHoistExt.after_valid
                              have hPopFunctionExt :=
                                Elab.popFunctionScope_preserves_clzAllocation
                                  hPopFunction hCodeExt.after_valid
                              have hPopIdentifierExt :=
                                Elab.popIdentifierScope_preserves_clzAllocation
                                  hPopIdentifier hPopFunctionExt.after_valid
                              have hCodeHoisted :
                                  HoistedFunctionsExtend
                                    hoistState codeState := by
                                intro entry hEntry
                                exact
                                  Elab.Stmt.List.elaborate_preserves_hoistedFunction_mem
                                    rawCode hCode hEntry
                              have hPopFunctionHoisted :
                                  HoistedFunctionsExtend codeState
                                    functionPoppedState := by
                                intro entry hEntry
                                exact
                                  Elab.popFunctionScope_preserves_hoistedFunction_mem
                                    hPopFunction hEntry
                              have hPopIdentifierHoisted :
                                  HoistedFunctionsExtend functionPoppedState
                                    identifierPoppedState := by
                                intro entry hEntry
                                exact
                                  Elab.popIdentifierScope_preserves_hoistedFunction_mem
                                    hPopIdentifier hEntry
                              have hAfterHoistClz :
                                  Elab.ClzAllocationExtends hoistState
                                    identifierPoppedState :=
                                Elab.ClzAllocationExtends.trans hCodeExt
                                  (Elab.ClzAllocationExtends.trans
                                    hPopFunctionExt hPopIdentifierExt)
                              have hAfterHoistFunctions :
                                  HoistedFunctionsExtend hoistState
                                    identifierPoppedState :=
                                HoistedFunctionsExtend.trans hCodeHoisted
                                  (HoistedFunctionsExtend.trans
                                    hPopFunctionHoisted
                                    hPopIdentifierHoisted)
                              have hBeforeHoistClz :
                                  Elab.ClzAllocationExtends elabState
                                    functionPushedState :=
                                Elab.ClzAllocationExtends.trans
                                  hPushIdentifierExt
                                  (Elab.ClzAllocationExtends.trans hScopeExt
                                    hPushFunctionExt)
                              have hBeforeCodeClz :
                                  Elab.ClzAllocationExtends elabState
                                    hoistState :=
                                Elab.ClzAllocationExtends.trans
                                  hBeforeHoistClz hHoistExt
                              have hAfterCodeClz :
                                  Elab.ClzAllocationExtends codeState
                                    identifierPoppedState :=
                                Elab.ClzAllocationExtends.trans
                                  hPopFunctionExt hPopIdentifierExt
                              have hAfterCodeFunctions :
                                  HoistedFunctionsExtend codeState
                                    identifierPoppedState :=
                                HoistedFunctionsExtend.trans
                                  hPopFunctionHoisted hPopIdentifierHoisted
                              have hHoistPath :
                                  FrontendCompilationPath builtinContext
                                    contract functionPushedState hoistState :=
                                hPath.subpath hBeforeHoistClz
                                  hAfterHoistClz hAfterHoistFunctions
                              have hCodePath :
                                  FrontendCompilationPath builtinContext
                                    contract hoistState codeState :=
                                hPath.subpath hBeforeCodeClz
                                  hAfterCodeClz hAfterCodeFunctions
                              have hPushIdentifierScopes :
                                  identifierPushedState.functionScopes =
                                    elabState.functionScopes :=
                                Elab.pushIdentifierScope_preserves_functionScopes
                                  hPushIdentifier
                              have hScopeScopes :
                                  scopeState.functionScopes =
                                    identifierPushedState.functionScopes :=
                                Elab.Stmt.List.localFunctionScope_preserves_functionScopes
                                  rawCode hScope
                              have hPushFunctionScopes :
                                  functionPushedState.functionScopes =
                                    generatedScope ::
                                      scopeState.functionScopes :=
                                Elab.pushFunctionScope_functionScopes
                                  hPushFunction
                              have hHoistScopes :
                                  hoistState.functionScopes =
                                    functionPushedState.functionScopes :=
                                Elab.Stmt.List.hoistLocalFunctions_preserves_functionScopes
                                  rawCode generatedScope hHoist
                              have hFunctionPushedScopes :
                                  functionPushedState.functionScopes =
                                    generatedScope ::
                                      elabState.functionScopes := by
                                rw [hPushFunctionScopes, hScopeScopes,
                                  hPushIdentifierScopes]
                              have hScopeBinding :=
                                pathCompiledFunctionScope_of_localHoist
                                  hRawScope hScope hHoist
                                  hFunctionPushedScopes hHoistPath
                              have hCodeContext :
                                  PathCompiledContext builtinContext contract
                                    (rawContext.withFunctionScope rawScope)
                                    hoistState.functionScopes := by
                                refine
                                  { objectBuiltins := hContext.objectBuiltins
                                    functionScopes := ?_ }
                                rw [hHoistScopes,
                                  hFunctionPushedScopes]
                                exact
                                  .cons hScopeBinding
                                    hContext.functionScopes
                              have hCodeRun :=
                                hSeq
                                  (state := state)
                                  (entryStore := state.store)
                                  (by cases state <;>
                                    simp [BlockEntryCompatible])
                                  hCodeContext hCodePath hCode hNormalized
                              have hBlock :=
                                blockCodeRunForward_of_scope_scopedSeq
                                  (context := rawContext)
                                  (scope := rawScope)
                                  (rawCode := rawCode)
                                  (orderedCode := ordered)
                                  (contract := contract)
                                  (state := state)
                                  hRawScope hCodeRun
                              simpa [Nat.add_assoc, Nat.add_comm,
                                Nat.add_left_comm] using hBlock

/-- A non-scope-creating frontend block still creates a temporary generated
function scope while elaborating its list, then pops it before returning. When
the syntax contains no immediate function declaration, the matching raw scope
is exactly empty; this theorem packages the resulting initializer sequence. -/
theorem scopedSeqRunForward_of_elaborateBlock_false
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hSeq :
      ScopedSeqPathRunForwardAt fuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State}
    (hNoFunctions :
      Elab.Stmt.List.hasImmediateFunctionDefinition rawCode = false)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      FrontendCompilationPath builtinContext contract
        elabState finalElabState)
    (hElab :
      (Elab.Stmt.List.elaborateBlock rawCode false).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtListNormalized builtinContext front ordered) :
    ScopedSeqRunForward state.store fuel (fuel + slack)
      (rawContext.withFunctionScope []) rawCode ordered contract state := by
  unfold Elab.Stmt.List.elaborateBlock at hElab
  simp [StateT.run_bind] at hElab
  cases hScope :
      (Elab.Stmt.List.localFunctionScope rawCode).run elabState with
  | error err => simp [hScope] at hElab
  | ok scopeResult =>
      rcases scopeResult with ⟨generatedScope, scopeState⟩
      simp [hScope] at hElab
      cases hPushFunction :
          (Elab.pushFunctionScope generatedScope).run scopeState with
      | error err => simp [hPushFunction] at hElab
      | ok pushFunctionResult =>
          rcases pushFunctionResult with ⟨_, functionPushedState⟩
          simp [hPushFunction] at hElab
          cases hHoist :
              (Elab.Stmt.List.hoistLocalFunctions
                rawCode generatedScope).run functionPushedState with
          | error err => simp [hHoist] at hElab
          | ok hoistResult =>
              rcases hoistResult with ⟨_, hoistState⟩
              simp [hHoist] at hElab
              cases hCode :
                  (Elab.Stmt.List.elaborate rawCode).run hoistState with
              | error err => simp [hCode] at hElab
              | ok codeResult =>
                  rcases codeResult with ⟨frontCode, codeState⟩
                  simp [hCode] at hElab
                  cases hPopFunction :
                      Elab.popFunctionScope.run codeState with
                  | error err => simp [hPopFunction] at hElab
                  | ok popFunctionResult =>
                      rcases popFunctionResult with
                        ⟨_, functionPoppedState⟩
                      simp [hPopFunction] at hElab
                      rcases hElab with ⟨rfl, rfl⟩
                      rcases localFunctionScope_rawFunctionScope hScope with
                        ⟨rawScope, hRawScope, _hNames⟩
                      have hRawEmpty :=
                        rawFunctionScope_eq_empty_of_noImmediate
                          hNoFunctions hRawScope
                      subst rawScope
                      have hScopeExt :=
                        Elab.Stmt.List.localFunctionScope_preserves_clzAllocation
                          rawCode hScope hPath.entryValid
                      have hPushFunctionExt :=
                        Elab.pushFunctionScope_preserves_clzAllocation
                          generatedScope hPushFunction hScopeExt.after_valid
                      have hHoistExt :=
                        Elab.Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                          rawCode generatedScope hHoist
                          hPushFunctionExt.after_valid
                      have hCodeExt :=
                        Elab.Stmt.List.elaborate_preserves_clzAllocation
                          rawCode hCode hHoistExt.after_valid
                      have hPopFunctionExt :=
                        Elab.popFunctionScope_preserves_clzAllocation
                          hPopFunction hCodeExt.after_valid
                      have hCodeHoisted :
                          HoistedFunctionsExtend hoistState codeState := by
                        intro entry hEntry
                        exact
                          Elab.Stmt.List.elaborate_preserves_hoistedFunction_mem
                            rawCode hCode hEntry
                      have hPopFunctionHoisted :
                          HoistedFunctionsExtend codeState
                            functionPoppedState := by
                        intro entry hEntry
                        exact
                          Elab.popFunctionScope_preserves_hoistedFunction_mem
                            hPopFunction hEntry
                      have hBeforeHoistClz :
                          Elab.ClzAllocationExtends elabState
                            functionPushedState :=
                        Elab.ClzAllocationExtends.trans hScopeExt
                          hPushFunctionExt
                      have hAfterHoistClz :
                          Elab.ClzAllocationExtends hoistState
                            functionPoppedState :=
                        Elab.ClzAllocationExtends.trans hCodeExt
                          hPopFunctionExt
                      have hAfterHoistHoisted :
                          HoistedFunctionsExtend hoistState
                            functionPoppedState :=
                        HoistedFunctionsExtend.trans hCodeHoisted
                          hPopFunctionHoisted
                      have hHoistPath :
                          FrontendCompilationPath builtinContext contract
                            functionPushedState hoistState :=
                        hPath.subpath hBeforeHoistClz hAfterHoistClz
                          hAfterHoistHoisted
                      have hBeforeCodeClz :
                          Elab.ClzAllocationExtends elabState hoistState :=
                        Elab.ClzAllocationExtends.trans hBeforeHoistClz
                          hHoistExt
                      have hCodePath :
                          FrontendCompilationPath builtinContext contract
                            hoistState codeState :=
                        hPath.subpath hBeforeCodeClz hPopFunctionExt
                          hPopFunctionHoisted
                      have hScopeScopes :
                          scopeState.functionScopes =
                            elabState.functionScopes :=
                        Elab.Stmt.List.localFunctionScope_preserves_functionScopes
                          rawCode hScope
                      have hPushFunctionScopes :
                          functionPushedState.functionScopes =
                            generatedScope :: scopeState.functionScopes :=
                        Elab.pushFunctionScope_functionScopes hPushFunction
                      have hHoistScopes :
                          hoistState.functionScopes =
                            functionPushedState.functionScopes :=
                        Elab.Stmt.List.hoistLocalFunctions_preserves_functionScopes
                          rawCode generatedScope hHoist
                      have hFunctionPushedScopes :
                          functionPushedState.functionScopes =
                            generatedScope :: elabState.functionScopes := by
                        rw [hPushFunctionScopes, hScopeScopes]
                      have hScopeBinding :=
                        pathCompiledFunctionScope_of_localHoist
                          hRawScope hScope hHoist hFunctionPushedScopes
                          hHoistPath
                      have hCodeContext :
                          PathCompiledContext builtinContext contract
                            (rawContext.withFunctionScope [])
                            hoistState.functionScopes := by
                        refine
                          { objectBuiltins := hContext.objectBuiltins
                            functionScopes := ?_ }
                        rw [hHoistScopes, hFunctionPushedScopes]
                        exact
                          .cons hScopeBinding hContext.functionScopes
                      exact
                        hSeq
                          (entryStore := state.store)
                          (state := state)
                          (by cases state <;>
                            simp [BlockEntryCompatible])
                          hCodeContext hCodePath hCode hNormalized

theorem emptyForInitPathRunForwardAt_of_seq
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hSeq :
      ScopedSeqPathRunForwardAt fuel slack builtinContext contract) :
    EmptyForInitPathRunForwardAt fuel slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState state
    hNoFunctions hContext hPath hElab hNormalized
  exact
    scopedSeqRunForward_of_elaborateBlock_false
      hSeq hNoFunctions hContext hPath hElab hNormalized

/-- Every checked raw expression statement is routed through exactly one
frontend-owned semantic path: an ordinary classified call, generated `clz`, or
the checked `setimmutable` patch block. -/
theorem scopedStmtRunForward_expressionStatement_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hSlack : sourceFuelFrontendSlack (fuel + 1) ≤ slack)
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      FrontendCompilationPath builtinContext contract
        elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate (.expressionStatement rawExpr)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 1) (fuel + 1 + slack)
      rawContext (.expressionStatement rawExpr)
      ordered contract state := by
  cases rawExpr with
  | literal literal =>
      simp [Elab.Stmt.elaborate] at hElab
      unfold Elab.throw at hElab
      change (Except.error _ : Except String (Frontend.Stmt × Elab.State)) =
        .ok (front, finalElabState) at hElab
      cases hElab
  | identifier name =>
      simp [Elab.Stmt.elaborate] at hElab
      unfold Elab.throw at hElab
      change (Except.error _ : Except String (Frontend.Stmt × Elab.State)) =
        .ok (front, finalElabState) at hElab
      cases hElab
  | functionCall name rawArgs =>
      by_cases hClz : name = "clz"
      · subst name
        unfold Elab.Stmt.elaborate at hElab
        have hSupported :
            CallClass.supportedExpressionStatementCall? "clz" = true := by
          cases hCallSupported :
              CallClass.supportedExpressionStatementCall? "clz" with
          | false =>
              simp [hCallSupported] at hElab
              unfold Elab.throw at hElab
              change
                (Except.error _ :
                  Except String (Frontend.Stmt × Elab.State)) =
                    .ok (front, finalElabState) at hElab
              cases hElab
          | true => rfl
        simp [hSupported, StateT.run_bind] at hElab
        cases hExprElab :
            (Elab.Expr.elaborate
              (.functionCall "clz" rawArgs)).run elabState with
        | error error => simp [hExprElab] at hElab
        | ok exprResult =>
            rcases exprResult with ⟨frontExpr, exprState⟩
            simp [hExprElab] at hElab
            rcases hElab with ⟨rfl, rfl⟩
            rcases clz_elaboration_parts hExprElab with
              ⟨rawArg, frontArg, argState, generated, helperState,
                rfl, hArgElab, hEnsure, rfl, rfl⟩
            rcases
                StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                  (Or.inl (by intro hKind; cases hKind)) hNormalized with
              ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
            cases fuel with
            | zero =>
                exact scopedStmtRunForward_of_exact
                  (stmtRunForward_expressionStatement_call_one
                    (orderedFuel := 1 + slack) (by decide))
            | succ argFuel =>
                have hCall :=
                  stmtRunForward_of_path_elaborated_clz
                    (rawArgFuel := argFuel) (slack := slack)
                    (state := state)
                    (hExpr 0 argFuel (by omega)) hContext hPath.clz
                    hExprElab hExprNormalized (by
                      unfold sourceFuelFrontendSlack at hSlack
                      rw [Raw.ClzPreservation.helperBodyFuel_value] at hSlack
                      omega) (by
                      unfold sourceFuelFrontendSlack at hSlack
                      omega)
                exact scopedStmtRunForward_of_exact hCall
      · by_cases hSetimmutable : name = "setimmutable"
        · subst name
          unfold Elab.Stmt.elaborate at hElab
          have hSupported :
              CallClass.supportedExpressionStatementCall?
                "setimmutable" = true := rfl
          simp [hSupported, StateT.run_bind] at hElab
          cases hExprElab :
              (Elab.Expr.elaborate
                (.functionCall "setimmutable" rawArgs)).run elabState with
          | error error => simp [hExprElab] at hElab
          | ok exprResult =>
              rcases exprResult with ⟨frontExpr, exprState⟩
              simp [hExprElab] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases objectBuiltinCall_elaboration_parts
                  (name := "setimmutable") (rawArgs := rawArgs)
                  (by decide) (by decide) rfl hExprElab with
                ⟨frontArgs, argsState, hArgs, hFront, hFinal⟩
              subst argsState
              subst frontExpr
              rcases StmtNormalized.setimmutable_args_eq_three
                  hNormalized with
                ⟨frontBase, frontNameArg, frontValue, hFrontArgs⟩
              subst frontArgs
              have hLength := exprList_elaborate_length hArgs
              have hRawLength : rawArgs.length = 3 := by
                simpa using hLength.symm
              rcases List.length_eq_three.mp hRawLength with
                ⟨rawBase, rawNameArg, rawValue, rfl⟩
              exact
                scopedStmtRunForward_setimmutable_of_path_below
                  hExpr hContext hPath.clz (by
                    unfold Elab.Stmt.elaborate
                    simp [hSupported, hExprElab]) hNormalized
        · exact
            scopedStmtRunForward_of_path_elaborated_callStatement_below
              hExpr hBlock hContext hPath.clz hClz hSetimmutable
              hElab hNormalized

theorem scopedStmtSpecialRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedStmtSpecialRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawStmt front ordered elabState finalElabState
    entryStore state hSpecial hCompatible hContext hPath hElab hNormalized
  exact scopedStmtRunForward_of_exact stmtRunForward_zero

/-- One bundled provider for every semantically special statement family.
All recursive obligations are strictly below the current source fuel and all
frontend-generated evidence comes from the checked occurrence path. -/
theorem scopedStmtSpecialRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hSlack : sourceFuelFrontendSlack (fuel + 1) ≤ slack)
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ∀ extra,
        ScopedBlockPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hSeq :
      ScopedSeqPathRunForwardBelow
        (fuel + 1) (slack + 1) builtinContext contract) :
    ScopedStmtSpecialRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawStmt front ordered elabState finalElabState
    entryStore state hSpecial hCompatible hContext hPath hElab hNormalized
  cases hSpecial with
  | expressionStatement rawExpr =>
      exact
        scopedStmtRunForward_expressionStatement_of_path_below
          hSlack hExpr (hBlock 0) hContext hPath hElab hNormalized
  | functionDefinition name params returns body =>
      unfold Elab.Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hResolve : (Elab.resolveFunction name).run elabState with
      | error error => simp [hResolve] at hElab
      | ok resolveResult =>
          rcases resolveResult with ⟨generated, resolveState⟩
          simp [hResolve] at hElab
          cases hFunction :
              (Elab.FunctionDef.elaborate params returns body).run
                resolveState with
          | error error => simp [hFunction] at hElab
          | ok functionResult =>
              rcases functionResult with ⟨frontFunction, functionState⟩
              simp [hFunction] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              have hOrdered :=
                StmtNormalized.functionDef_ordered hNormalized
              subst ordered
              have hRun :=
                scopedStmtRunForward_functionDefinition_stub_succ
                  (rawFuel := fuel)
                  (orderedFuel := fuel + slack - 1)
                  (entryStore := entryStore)
                  (name := name) (params := params) (returns := returns)
                  (body := body)
                  (context := rawContext) (contract := contract)
                  (state := state) hCompatible
              have hPositive : 1 ≤ slack := by
                unfold sourceFuelFrontendSlack at hSlack
                rw [Raw.ClzPreservation.helperBodyFuel_value] at hSlack
                omega
              have hTargetFuel :
                  fuel + slack - 1 + 2 = fuel + 1 + slack := by
                omega
              rw [hTargetFuel] at hRun
              exact hRun
  | switch rawCondition rawCases rawDefault =>
      exact
        scopedStmtRunForward_switch_of_path_below
          (hExpr 0) (hBlock 0) hContext hPath hElab hNormalized
  | forLoop rawPre rawCondition rawPost rawBody =>
      cases fuel with
      | zero =>
          exact scopedStmtRunForward_of_exact stmtRunForward_for_one
      | succ loopFuel =>
          have hExprBelow :
              ∀ extra,
                ScopedExprPathRunForwardBelow
                  (loopFuel + 1) (slack + extra)
                  builtinContext contract := by
            intro extra childFuel hChild
            exact hExpr extra childFuel (by omega)
          have hBlockBelow :
              ∀ extra,
                ScopedBlockPathRunForwardBelow
                  (loopFuel + 1) (slack + extra)
                  builtinContext contract := by
            intro extra childFuel hChild
            exact hBlock extra childFuel (by omega)
          have hInitSeq :
              ScopedSeqPathRunForwardAt
                loopFuel (slack + 1) builtinContext contract :=
            hSeq loopFuel (by omega)
          exact
            scopedStmtRunForward_for_of_path_below
              hExprBelow hBlockBelow hInitSeq
              (emptyForInitPathRunForwardAt_of_seq hInitSeq)
              hContext hPath hElab hNormalized

structure FrontendPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop where
  expr :
    ScopedExprPathRunForwardAt rawFuel slack builtinContext contract
  stmt :
    ScopedStmtPathRunForwardAt rawFuel slack builtinContext contract
  seq :
    ScopedSeqPathRunForwardAt rawFuel slack builtinContext contract
  block :
    ScopedBlockPathRunForwardAt rawFuel slack builtinContext contract

/-- Complete path-scoped frontend preservation by strong induction on raw
semantic fuel. The target overhead is computed solely from source fuel; no
generated-name, layout, replay, loop-prefix, or syntax-occurrence premise is
exposed. -/
theorem frontendPathRunForwardAt_of_slack
    (rawFuel : Nat) :
    ∀ {slack : Nat}
      {builtinContext : Frontend.ObjectBuiltinContext}
      {contract : Frontend.AstContract},
      sourceFuelFrontendSlack rawFuel ≤ slack →
        FrontendPathRunForwardAt
          rawFuel slack builtinContext contract := by
  induction rawFuel using Nat.strong_induction_on with
  | h current ih =>
      intro slack builtinContext contract hSlack
      cases current with
      | zero =>
          exact
            { expr := scopedExprPathRunForwardAt_zero
              stmt := scopedStmtPathRunForwardAt_zero
              seq := scopedSeqPathRunForwardAt_zero
              block := scopedBlockPathRunForwardAt_zero }
      | succ predecessor =>
          have hExprBelow :
              ∀ extra,
                ScopedExprPathRunForwardBelow
                  (predecessor + 1) (slack + extra)
                  builtinContext contract := by
            intro extra childFuel hChild
            exact
              (ih childFuel (by omega)
                (slack := slack + extra) (by
                  unfold sourceFuelFrontendSlack at hSlack ⊢
                  omega)).expr
          have hBlockBelow :
              ∀ extra,
                ScopedBlockPathRunForwardBelow
                  (predecessor + 1) (slack + extra)
                  builtinContext contract := by
            intro extra childFuel hChild
            exact
              (ih childFuel (by omega)
                (slack := slack + extra) (by
                  unfold sourceFuelFrontendSlack at hSlack ⊢
                  omega)).block
          have hSeqBelowPlus :
              ScopedSeqPathRunForwardBelow
                (predecessor + 1) (slack + 1)
                builtinContext contract := by
            intro childFuel hChild
            exact
              (ih childFuel (by omega)
                (slack := slack + 1) (by
                  unfold sourceFuelFrontendSlack at hSlack ⊢
                  omega)).seq
          have hClz :
              ClzPathRunForwardAt
                (predecessor + 1) slack builtinContext contract := by
            cases predecessor with
            | zero =>
                intro rawContext rawArgs front ordered
                  elabState finalElabState state
                  hContext hPath hElab hNormalized
                rcases clz_elaboration_parts hElab with
                  ⟨rawArg, frontArg, argState, generated, helperState,
                    rfl, hArgElab, hEnsure, rfl, rfl⟩
                exact exprValuesRunForward_clz_one
            | succ argFuel =>
                apply clzPathRunForwardAt_succ_succ_of_slack hSlack
                exact
                  (ih (argFuel + 1) (by omega)
                    (slack := slack - 1) (by
                      unfold sourceFuelFrontendSlack at hSlack ⊢
                      omega)).expr
          have hExprCurrent :
              ScopedExprPathRunForwardAt
                (predecessor + 1) slack builtinContext contract :=
            scopedExprPathRunForwardAt_succ
              hExprBelow (hBlockBelow 0) hClz
          have hSpecial :
              ScopedStmtSpecialRunForwardAt
                (predecessor + 1) slack builtinContext contract :=
            scopedStmtSpecialRunForwardAt_succ
              hSlack hExprBelow hBlockBelow hSeqBelowPlus
          have hStmtCurrent :
              ScopedStmtPathRunForwardAt
                (predecessor + 1) slack builtinContext contract :=
            scopedStmtPathRunForwardAt_succ_of_special
              hExprBelow hBlockBelow hSpecial
          have hPrevious :
              FrontendPathRunForwardAt
                predecessor slack builtinContext contract :=
            ih predecessor (by omega) (slack := slack)
              (builtinContext := builtinContext) (contract := contract) (by
              unfold sourceFuelFrontendSlack at hSlack ⊢
              omega)
          exact
            { expr := hExprCurrent
              stmt := hStmtCurrent
              seq :=
                scopedSeqPathRunForwardAt_succ
                  hPrevious.stmt hPrevious.seq
              block :=
                scopedBlockPathRunForwardAt_succ_of_seq
                  hPrevious.seq }

/-- Raw block-body sequence preservation against the ordered dispatcher
sequence, before both sides apply their lexical block store restriction. -/
def DispatcherSeqRunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (scope : Raw.SourceSemantics.FunctionScope)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    (PendingBlockDoneRel state.store)
    (Raw.SourceSemantics.execSeq rawFuel
      ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
      code state)
    (Yul.InteractionSemantics.execSeq orderedFuel
      [ordered.program.contract.dispatcher]
      (some ordered.program.contract) state)

/-- Close the ordered dispatcher's lexical block around an exact raw/Yul
statement-list simulation. This is the only place where the internal sequence
relation changes from exact states to the pending block-restriction relation. -/
theorem dispatcherSeqRunForward_of_seq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {ordered : Yul.OrderedProgram} {state : State}
    (hDispatcher :
      ordered.program.contract.dispatcher = .Block orderedCode)
    (hSeq :
      SeqRunForward rawFuel orderedFuel
        ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
        rawCode orderedCode ordered.program.contract state) :
    DispatcherSeqRunForward rawFuel (orderedFuel + 2)
      context scope rawCode ordered state := by
  unfold DispatcherSeqRunForward SeqRunForward at *
  have hRestricted :=
    Simulation.Interaction.ForwardRel.bind_right
      (rightNext := fun orderedState : State =>
        pure (orderedState.restrictStoreTo state.store))
      (targetDoneRel := PendingBlockDoneRel state.store)
      hSeq (by
      intro rawDone orderedDone hDone
      unfold SameDoneRel at hDone
      subst orderedDone
      cases rawDone with
      | error error =>
          exact
            Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.error rfl)
      | ok rawState =>
          exact
            Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok rfl))
  rw [hDispatcher]
  rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [Yul.InteractionSemantics.ExecSeq.nil_succ]
  have hContinue :
      (fun stateAfterStmt : State =>
        match stateAfterStmt with
        | .Ok _ _ =>
            (Simulation.Interaction.pure stateAfterStmt : Open State)
        | .OutOfFuel | .Checkpoint _ =>
            (Simulation.Interaction.pure stateAfterStmt : Open State)) =
      (fun stateAfterStmt =>
        (Simulation.Interaction.pure stateAfterStmt : Open State)) := by
    funext stateAfterStmt
    cases stateAfterStmt <;> rfl
  have hRight :
      Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
              (some ordered.program.contract) state)
            (fun stateAfterBody =>
              pure (stateAfterBody.restrictStoreTo state.store)))
          (fun stateAfterStmt : State =>
            match stateAfterStmt with
            | .Ok _ _ =>
                (Simulation.Interaction.pure stateAfterStmt : Open State)
            | .OutOfFuel | .Checkpoint _ =>
                (Simulation.Interaction.pure stateAfterStmt : Open State)) =
        Simulation.Interaction.bind
          (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
            (some ordered.program.contract) state)
          (fun stateAfterBody =>
            pure (stateAfterBody.restrictStoreTo state.store)) := by
    rw [hContinue]
    exact Simulation.Interaction.bind_pure _
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      (PendingBlockDoneRel state.store)
      (Raw.SourceSemantics.execSeq rawFuel
        ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
        rawCode state)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
            (some ordered.program.contract) state)
          (fun stateAfterBody =>
            pure (stateAfterBody.restrictStoreTo state.store)))
        (fun stateAfterStmt : State =>
          match stateAfterStmt with
          | .Ok _ _ =>
              (Simulation.Interaction.pure stateAfterStmt : Open State)
          | .OutOfFuel | .Checkpoint _ =>
              (Simulation.Interaction.pure stateAfterStmt : Open State)))
  rw [hRight]
  exact hRestricted

/-- Close the ordered dispatcher around the generic scoped sequence relation.
Administrative function-declaration stubs may already have restricted abrupt
states; the final dispatcher restriction is idempotent in exactly those cases. -/
theorem dispatcherSeqRunForward_of_scopedSeq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {ordered : Yul.OrderedProgram} {state : State}
    (hDispatcher :
      ordered.program.contract.dispatcher = .Block orderedCode)
    (hSeq :
      ScopedSeqRunForward state.store rawFuel orderedFuel
        ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
        rawCode orderedCode ordered.program.contract state) :
    DispatcherSeqRunForward rawFuel (orderedFuel + 2)
      context scope rawCode ordered state := by
  unfold DispatcherSeqRunForward ScopedSeqRunForward at *
  have hRestricted :=
    Simulation.Interaction.ForwardRel.bind_right
      (rightNext := fun orderedState : State =>
        pure (orderedState.restrictStoreTo state.store))
      (targetDoneRel := PendingBlockDoneRel state.store)
      hSeq (by
      intro rawDone orderedDone hDone
      cases hDone with
      | error hError =>
          subst_vars
          exact
            Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.error rfl)
      | @ok rawState orderedState hState =>
          cases rawState with
          | Ok shared store =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok rfl)
          | OutOfFuel =>
              cases hState with
              | inl hExact =>
                  subst orderedState
                  exact
                    Simulation.Interaction.ForwardRel.done
                      (Simulation.Interaction.ExceptRel.ok rfl)
              | inr hRestricted =>
                  subst orderedState
                  change
                    Simulation.Interaction.ForwardRel
                      Yul.FunctionsInteractionPrimitive.Truncated
                      (PendingBlockDoneRel state.store)
                      (pure (EvmYul.Yul.State.OutOfFuel : State))
                      (pure
                        (((EvmYul.Yul.State.OutOfFuel : State).restrictStoreTo
                          state.store).restrictStoreTo state.store))
                  rw [Yul.InteractionSemantics.State.restrictStoreTo_idem]
                  exact
                    Simulation.Interaction.ForwardRel.done
                      (Simulation.Interaction.ExceptRel.ok rfl)
          | Checkpoint jump =>
              cases hState with
              | inl hExact =>
                  subst orderedState
                  exact
                    Simulation.Interaction.ForwardRel.done
                      (Simulation.Interaction.ExceptRel.ok rfl)
              | inr hRestricted =>
                  subst orderedState
                  change
                    Simulation.Interaction.ForwardRel
                      Yul.FunctionsInteractionPrimitive.Truncated
                      (PendingBlockDoneRel state.store)
                      (pure (EvmYul.Yul.State.Checkpoint jump))
                      (pure
                        (((EvmYul.Yul.State.Checkpoint jump).restrictStoreTo
                          state.store).restrictStoreTo state.store))
                  rw [Yul.InteractionSemantics.State.restrictStoreTo_idem]
                  exact
                    Simulation.Interaction.ForwardRel.done
                      (Simulation.Interaction.ExceptRel.ok rfl))
  rw [hDispatcher]
  rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [Yul.InteractionSemantics.ExecSeq.nil_succ]
  have hContinue :
      (fun stateAfterStmt : State =>
        match stateAfterStmt with
        | .Ok _ _ =>
            (Simulation.Interaction.pure stateAfterStmt : Open State)
        | .OutOfFuel | .Checkpoint _ =>
            (Simulation.Interaction.pure stateAfterStmt : Open State)) =
      (fun stateAfterStmt =>
        (Simulation.Interaction.pure stateAfterStmt : Open State)) := by
    funext stateAfterStmt
    cases stateAfterStmt <;> rfl
  have hRight :
      Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
              (some ordered.program.contract) state)
            (fun stateAfterBody =>
              pure (stateAfterBody.restrictStoreTo state.store)))
          (fun stateAfterStmt : State =>
            match stateAfterStmt with
            | .Ok _ _ =>
                (Simulation.Interaction.pure stateAfterStmt : Open State)
            | .OutOfFuel | .Checkpoint _ =>
                (Simulation.Interaction.pure stateAfterStmt : Open State)) =
        Simulation.Interaction.bind
          (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
            (some ordered.program.contract) state)
          (fun stateAfterBody =>
            pure (stateAfterBody.restrictStoreTo state.store)) := by
    rw [hContinue]
    exact Simulation.Interaction.bind_pure _
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      (PendingBlockDoneRel state.store)
      (Raw.SourceSemantics.execSeq rawFuel
        ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
        rawCode state)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
            (some ordered.program.contract) state)
          (fun stateAfterBody =>
            pure (stateAfterBody.restrictStoreTo state.store)))
        (fun stateAfterStmt : State =>
          match stateAfterStmt with
          | .Ok _ _ =>
              (Simulation.Interaction.pure stateAfterStmt : Open State)
          | .OutOfFuel | .Checkpoint _ =>
              (Simulation.Interaction.pure stateAfterStmt : Open State)))
  rw [hRight]
  exact hRestricted

theorem dispatcherSeqRunForward_zero
    {orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    {state : State} :
    DispatcherSeqRunForward 0 orderedFuel context scope code ordered state := by
  unfold DispatcherSeqRunForward
  rw [Raw.SourceSemantics.execSeq_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by
        simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem dispatcherSeqRunForward_cons_functionDefinition_ok
    {fuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {name : Name} {params returns : List Name} {body rest : List Raw.Stmt}
    {ordered : Yul.OrderedProgram}
    {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
    (hRest :
      DispatcherSeqRunForward (fuel + 1) orderedFuel
        context scope rest ordered (.Ok shared vars)) :
    DispatcherSeqRunForward (fuel + 2) orderedFuel
      context scope
      (.functionDefinition name params returns body :: rest)
      ordered (.Ok shared vars) := by
  unfold DispatcherSeqRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  simpa [Simulation.Interaction.bind_pure]

inductive TopLevelNonFunction : Raw.Stmt → Prop where
  | block (body : List Raw.Stmt) : TopLevelNonFunction (.block body)
  | variableDeclaration (names : List Name) (value : Option Raw.Expr) :
      TopLevelNonFunction (.variableDeclaration names value)
  | assignment (names : List Name) (value : Raw.Expr) :
      TopLevelNonFunction (.assignment names value)
  | expressionStatement (expr : Raw.Expr) :
      TopLevelNonFunction (.expressionStatement expr)
  | switch (scrutinee : Raw.Expr)
      (cases : List (Raw.SwitchCaseValue × List Raw.Stmt))
      (default : List Raw.Stmt) :
      TopLevelNonFunction (.switch scrutinee cases default)
  | forLoop (pre : List Raw.Stmt) (condition : Raw.Expr)
      (post body : List Raw.Stmt) :
      TopLevelNonFunction (.forLoop pre condition post body)
  | ifThen (condition : Raw.Expr) (body : List Raw.Stmt) :
      TopLevelNonFunction (.ifThen condition body)
  | «break» : TopLevelNonFunction .break
  | «continue» : TopLevelNonFunction .continue
  | «leave» : TopLevelNonFunction .leave

namespace TopLevelNonFunction

theorem elaborateTopLevel_cons
    {stmt : Raw.Stmt} (hStmt : TopLevelNonFunction stmt)
    (rest : List Raw.Stmt) (dispatcher : List Frontend.Stmt)
    (topFunctions : List (Name × Frontend.FunctionDef)) :
    Elab.elaborateTopLevel (stmt :: rest) dispatcher topFunctions =
      Elab.Stmt.elaborate stmt >>= fun front =>
        Elab.elaborateTopLevel rest (front :: dispatcher) topFunctions := by
  cases hStmt <;> rfl

end TopLevelNonFunction

/-- Source-order view of the real top-level elaborator. Function declarations
change frontend state and populate the final function table but emit no
dispatcher statement; every other source statement emits exactly one entry. -/
inductive TopLevelDispatcherElaboration :
    List Raw.Stmt → Elab.State → List Frontend.Stmt → Elab.State → Prop where
  | nil (state : Elab.State) :
      TopLevelDispatcherElaboration [] state [] state
  | functionDefinition
      {name : Name} {params returns : List Name} {body rest : List Raw.Stmt}
      {state functionState finalState : Elab.State}
      {frontFunction : Frontend.FunctionDef}
      {frontRest : List Frontend.Stmt}
      (functionElaborates :
        (Elab.FunctionDef.elaborate params returns body).run state =
          .ok (frontFunction, functionState))
      (tail :
        TopLevelDispatcherElaboration
          rest functionState frontRest finalState) :
      TopLevelDispatcherElaboration
        (.functionDefinition name params returns body :: rest)
        state frontRest finalState
  | statement
      {rawHead : Raw.Stmt} {rawRest : List Raw.Stmt}
      {state headState finalState : Elab.State}
      {frontHead : Frontend.Stmt} {frontRest : List Frontend.Stmt}
      (nonFunction : TopLevelNonFunction rawHead)
      (headElaborates :
        (Elab.Stmt.elaborate rawHead).run state =
          .ok (frontHead, headState))
      (tail :
        TopLevelDispatcherElaboration
          rawRest headState frontRest finalState) :
      TopLevelDispatcherElaboration
        (rawHead :: rawRest) state (frontHead :: frontRest) finalState

namespace TopLevelDispatcherElaboration

theorem clzExtends
    {rawCode : List Raw.Stmt} {state finalState : Elab.State}
    {front : List Frontend.Stmt}
    (view : TopLevelDispatcherElaboration rawCode state front finalState)
    (hValid : Elab.ClzAllocationValid state) :
    Elab.ClzAllocationExtends state finalState := by
  induction view with
  | nil => exact Elab.ClzAllocationExtends.refl _ hValid
  | @functionDefinition name params returns body rest state functionState
      finalState frontFunction frontRest hFunction tail ih =>
      have hHead :=
        Elab.FunctionDef.elaborate_preserves_clzAllocation
          params returns body hFunction hValid
      exact Elab.ClzAllocationExtends.trans hHead (ih hHead.after_valid)
  | @statement rawHead rawRest state headState finalState
      frontHead frontRest hNonFunction hHead tail ih =>
      have hHeadExt :=
        Elab.Stmt.elaborate_preserves_clzAllocation
          rawHead hHead hValid
      exact Elab.ClzAllocationExtends.trans hHeadExt
        (ih hHeadExt.after_valid)

theorem hoistedExtends
    {rawCode : List Raw.Stmt} {state finalState : Elab.State}
    {front : List Frontend.Stmt}
    (view : TopLevelDispatcherElaboration rawCode state front finalState) :
    HoistedFunctionsExtend state finalState := by
  induction view with
  | nil => exact HoistedFunctionsExtend.refl _
  | @functionDefinition name params returns body rest state functionState
      finalState frontFunction frontRest hFunction tail ih =>
      apply HoistedFunctionsExtend.trans
      · intro entry hEntry
        exact
          Elab.FunctionDef.elaborate_preserves_hoistedFunction_mem
            params returns body hFunction hEntry
      · exact ih
  | @statement rawHead rawRest state headState finalState
      frontHead frontRest hNonFunction hHead tail ih =>
      apply HoistedFunctionsExtend.trans
      · intro entry hEntry
        exact
          Elab.Stmt.elaborate_preserves_hoistedFunction_mem
            rawHead hHead hEntry
      · exact ih

theorem functionScopes
    {rawCode : List Raw.Stmt} {state finalState : Elab.State}
    {front : List Frontend.Stmt}
    (view : TopLevelDispatcherElaboration rawCode state front finalState) :
    finalState.functionScopes = state.functionScopes := by
  induction view with
  | nil => rfl
  | @functionDefinition name params returns body rest state functionState
      finalState frontFunction frontRest hFunction tail ih =>
      rw [ih]
      exact
        Elab.FunctionDef.elaborate_preserves_functionScopes
          params returns body hFunction
  | @statement rawHead rawRest state headState finalState
      frontHead frontRest hNonFunction hHead tail ih =>
      rw [ih]
      exact Elab.Stmt.elaborate_preserves_functionScopes rawHead hHead

/-- Compiler-derived evidence for one raw top-level function declaration.  It
ties that declaration to the actual output function table while retaining the
state path needed to reuse the generic function-body preservation theorem. -/
inductive TopLevelFunctionWitness
    (state finalState : Elab.State)
    (outFunctions : List (Name × Frontend.FunctionDef))
    (name : Name) (params returns : List Name) (body : List Raw.Stmt) : Prop where
  | mk
      (functionState finalFunctionState : Elab.State)
      (frontFunction : Frontend.FunctionDef)
      (elaborates :
        (Elab.FunctionDef.elaborate params returns body).run functionState =
          .ok (frontFunction, finalFunctionState))
      (functionScopes : functionState.functionScopes = state.functionScopes)
      (memOutput : (name, frontFunction) ∈ outFunctions)
      (prefixClz : Elab.ClzAllocationExtends state functionState)
      (suffixClz : Elab.ClzAllocationExtends finalFunctionState finalState)
      (suffixHoisted : HoistedFunctionsExtend finalFunctionState finalState) :
      TopLevelFunctionWitness state finalState outFunctions
        name params returns body

theorem topLevelFunctionWitness_of_run_mem
    {rawCode : List Raw.Stmt} {state finalState : Elab.State}
    {front : List Frontend.Stmt}
    (view : TopLevelDispatcherElaboration rawCode state front finalState)
    {dispatcher outDispatcher : List Frontend.Stmt}
    {topFunctions outFunctions : List (Name × Frontend.FunctionDef)}
    (hRun :
      (Elab.elaborateTopLevel rawCode dispatcher topFunctions).run state =
        .ok ((outDispatcher, outFunctions), finalState))
    (hValid : Elab.ClzAllocationValid state)
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hMem : .functionDefinition name params returns body ∈ rawCode) :
    Nonempty
      (TopLevelFunctionWitness state finalState outFunctions
        name params returns body) := by
  induction view generalizing dispatcher topFunctions outDispatcher outFunctions with
  | nil => simp at hMem
  | @functionDefinition headName headParams headReturns headBody rest
      state headState finalState headFunction frontRest hHead tail ih =>
      unfold Elab.elaborateTopLevel at hRun
      simp [StateT.run_bind, hHead] at hRun
      have hTailRun :
          (Elab.elaborateTopLevel rest dispatcher
            ((headName, headFunction) :: topFunctions)).run headState =
              .ok ((outDispatcher, outFunctions), finalState) := by
        simpa using hRun
      have hHeadExt :=
        Elab.FunctionDef.elaborate_preserves_clzAllocation
          headParams headReturns headBody hHead hValid
      simp only [List.mem_cons] at hMem
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl, rfl, rfl⟩
        have hOutput : (name, headFunction) ∈ outFunctions :=
          Elab.elaborateTopLevel_preserves_topFunction_mem hTailRun (by simp)
        exact ⟨TopLevelFunctionWitness.mk
          state headState headFunction hHead rfl hOutput
          (Elab.ClzAllocationExtends.refl _ hValid)
          (tail.clzExtends hHeadExt.after_valid)
          tail.hoistedExtends⟩
      · rcases ih hTailRun hHeadExt.after_valid hTail with ⟨witness⟩
        cases witness with
        | mk functionState finalFunctionState frontFunction
            hElaborates hScopes hOutput hPrefix hSuffix hHoisted =>
            exact ⟨TopLevelFunctionWitness.mk
              functionState finalFunctionState frontFunction
              hElaborates (by
                rw [hScopes]
                exact
                  Elab.FunctionDef.elaborate_preserves_functionScopes
                    headParams headReturns headBody hHead)
              hOutput
              (Elab.ClzAllocationExtends.trans hHeadExt hPrefix)
              hSuffix hHoisted⟩
  | @statement rawHead rawRest state headState finalState
      frontHead frontRest hNonFunction hHead tail ih =>
      rw [hNonFunction.elaborateTopLevel_cons] at hRun
      simp [StateT.run_bind, hHead] at hRun
      have hTailRun :
          (Elab.elaborateTopLevel rawRest (frontHead :: dispatcher)
            topFunctions).run headState =
              .ok ((outDispatcher, outFunctions), finalState) := by
        simpa using hRun
      have hHeadExt :=
        Elab.Stmt.elaborate_preserves_clzAllocation rawHead hHead hValid
      have hNe :
          rawHead ≠ .functionDefinition name params returns body := by
        cases hNonFunction <;> simp
      have hTail :
          .functionDefinition name params returns body ∈ rawRest := by
        simp only [List.mem_cons] at hMem
        rcases hMem with hHere | hTail
        · exact False.elim (hNe hHere.symm)
        · exact hTail
      rcases ih hTailRun hHeadExt.after_valid hTail with ⟨witness⟩
      cases witness with
      | mk functionState finalFunctionState frontFunction
          hElaborates hScopes hOutput hPrefix hSuffix hHoisted =>
          exact ⟨TopLevelFunctionWitness.mk
            functionState finalFunctionState frontFunction
            hElaborates (by
              rw [hScopes]
              exact Elab.Stmt.elaborate_preserves_functionScopes rawHead hHead)
            hOutput
            (Elab.ClzAllocationExtends.trans hHeadExt hPrefix)
            hSuffix hHoisted⟩

end TopLevelDispatcherElaboration

private theorem topLevelDispatcherElaboration_of_nonFunction
    {rawHead : Raw.Stmt} {rawRest : List Raw.Stmt}
    (hNonFunction : TopLevelNonFunction rawHead)
    (ih :
      ∀ {state : Elab.State} {dispatcher : List Frontend.Stmt}
        {topFunctions : List (Name × Frontend.FunctionDef)}
        {outDispatcher : List Frontend.Stmt}
        {outFunctions : List (Name × Frontend.FunctionDef)}
        {finalState : Elab.State},
        (Elab.elaborateTopLevel rawRest dispatcher topFunctions).run state =
            .ok ((outDispatcher, outFunctions), finalState) →
          ∃ emitted,
            outDispatcher = dispatcher.reverse ++ emitted ∧
              TopLevelDispatcherElaboration
                rawRest state emitted finalState)
    {state finalState : Elab.State}
    {dispatcher outDispatcher : List Frontend.Stmt}
    {topFunctions outFunctions : List (Name × Frontend.FunctionDef)}
    (hRun :
      (Elab.elaborateTopLevel
        (rawHead :: rawRest) dispatcher topFunctions).run state =
          .ok ((outDispatcher, outFunctions), finalState)) :
    ∃ emitted,
      outDispatcher = dispatcher.reverse ++ emitted ∧
        TopLevelDispatcherElaboration
          (rawHead :: rawRest) state emitted finalState := by
  rw [hNonFunction.elaborateTopLevel_cons] at hRun
  simp [StateT.run_bind] at hRun
  symm at hRun
  cases hHead : (Elab.Stmt.elaborate rawHead).run state with
  | error error => simp [hHead] at hRun
  | ok headResult =>
      rcases headResult with ⟨frontHead, headState⟩
      simp [hHead] at hRun
      cases hTail :
          (Elab.elaborateTopLevel rawRest
            (frontHead :: dispatcher) topFunctions).run headState with
      | error error => simp [hTail] at hRun
      | ok tailResult =>
          rcases tailResult with ⟨out, tailState⟩
          rcases out with ⟨tailDispatcher, tailFunctions⟩
          simp [hTail] at hRun
          rcases hRun with ⟨⟨rfl, rfl⟩, rfl⟩
          rcases ih hTail with ⟨emitted, hDispatcher, hView⟩
          refine ⟨frontHead :: emitted, ?_, .statement hNonFunction hHead hView⟩
          rw [hDispatcher]
          simp [List.reverse_cons, List.append_assoc]

theorem topLevelDispatcherElaboration_of_run
    {rawCode : List Raw.Stmt}
    {state finalState : Elab.State}
    {dispatcher outDispatcher : List Frontend.Stmt}
    {topFunctions outFunctions : List (Name × Frontend.FunctionDef)}
    (hRun :
      (Elab.elaborateTopLevel rawCode dispatcher topFunctions).run state =
        .ok ((outDispatcher, outFunctions), finalState)) :
    ∃ emitted,
      outDispatcher = dispatcher.reverse ++ emitted ∧
        TopLevelDispatcherElaboration rawCode state emitted finalState := by
  induction rawCode generalizing state dispatcher topFunctions
      outDispatcher outFunctions finalState with
  | nil =>
      unfold Elab.elaborateTopLevel at hRun
      simp [StateT.run_pure] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact ⟨[], by simp, .nil state⟩
  | cons rawHead rawRest ih =>
      cases rawHead with
      | functionDefinition name params returns body =>
          unfold Elab.elaborateTopLevel at hRun
          simp [StateT.run_bind] at hRun
          symm at hRun
          cases hFunction :
              (Elab.FunctionDef.elaborate params returns body).run state with
          | error error => simp [hFunction] at hRun
          | ok functionResult =>
              rcases functionResult with ⟨frontFunction, functionState⟩
              simp [hFunction] at hRun
              cases hTail :
                  (Elab.elaborateTopLevel rawRest dispatcher
                    ((name, frontFunction) :: topFunctions)).run
                      functionState with
              | error error => simp [hTail] at hRun
              | ok tailResult =>
                  rcases tailResult with ⟨out, tailState⟩
                  rcases out with ⟨tailDispatcher, tailFunctions⟩
                  simp [hTail] at hRun
                  rcases hRun with ⟨⟨rfl, rfl⟩, rfl⟩
                  rcases ih hTail with ⟨emitted, hDispatcher, hView⟩
                  exact
                    ⟨emitted, hDispatcher,
                      .functionDefinition hFunction hView⟩
      | block body =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.block body) ih hRun
      | variableDeclaration names value =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.variableDeclaration names value) ih hRun
      | assignment names value =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.assignment names value) ih hRun
      | expressionStatement expr =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.expressionStatement expr) ih hRun
      | switch scrutinee cases default =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.switch scrutinee cases default) ih hRun
      | forLoop pre condition post body =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.forLoop pre condition post body) ih hRun
      | ifThen condition body =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              (.ifThen condition body) ih hRun
      | «break» =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              .break ih hRun
      | «continue» =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              .continue ih hRun
      | «leave» =>
          exact
            topLevelDispatcherElaboration_of_nonFunction
              .leave ih hRun

namespace TopLevelDispatcherElaboration

/-- Preserve the dispatcher projection of a checked top-level elaboration.
Top-level function declarations consume raw administrative fuel but emit no
dispatcher statement; their runtime effect is identity on regular states. -/
theorem scopedSeqRunForward
    (rawFuel : Nat)
    {rawCode : List Raw.Stmt}
    {elabState finalElabState : Elab.State}
    {front : List Frontend.Stmt}
    (view :
      TopLevelDispatcherElaboration
        rawCode elabState front finalElabState) :
    ∀ {slack : Nat}
      {builtinContext : Frontend.ObjectBuiltinContext}
      {contract : Frontend.AstContract}
      {rawContext : Raw.SourceSemantics.Context}
      {ordered : List Frontend.AstStmt}
      {entryStore : EvmYul.Yul.VarStore}
      {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore},
      sourceFuelFrontendSlack rawFuel ≤ slack →
        PathCompiledContext builtinContext contract
          rawContext elabState.functionScopes →
        FrontendCompilationPath builtinContext contract
          elabState finalElabState →
        StmtListNormalized builtinContext front ordered →
        ScopedSeqRunForward entryStore rawFuel (rawFuel + slack)
          rawContext rawCode ordered contract (.Ok shared vars) := by
  induction rawFuel using Nat.strong_induction_on generalizing
      rawCode elabState finalElabState front with
  | h current ih =>
      intro slack builtinContext contract rawContext ordered entryStore
        shared vars hSlack hContext hPath hNormalized
      cases current with
      | zero =>
          exact scopedSeqRunForward_of_exact seqRunForward_zero
      | succ predecessor =>
          cases view with
          | nil state =>
              have hOrdered := StmtListNormalized.nil_ordered hNormalized
              subst ordered
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (scopedSeqRunForward_of_exact
                  (entryStore := entryStore)
                  (seqRunForward_nil_succ
                    (rawFuel := predecessor)
                    (orderedFuel := predecessor + slack)
                    (context := rawContext) (contract := contract)
                    (state := (.Ok shared vars : State))))
          | @functionDefinition name params returns body rest state
              functionState finalState frontFunction frontRest
              hFunction tail =>
              cases predecessor with
              | zero =>
                  exact
                    scopedSeqRunForward_cons_one
                      (orderedFuel := 1 + slack)
              | succ tailFuel =>
                  have hHeadExt :=
                    Elab.FunctionDef.elaborate_preserves_clzAllocation
                      params returns body hFunction hPath.entryValid
                  have hTailPath :
                      FrontendCompilationPath builtinContext contract
                        functionState finalElabState :=
                    hPath.suffixPath hHeadExt
                  have hFunctionScopes :
                      functionState.functionScopes =
                        elabState.functionScopes :=
                    Elab.FunctionDef.elaborate_preserves_functionScopes
                      params returns body hFunction
                  have hTailContext :
                      PathCompiledContext builtinContext contract
                        rawContext functionState.functionScopes := by
                    simpa [hFunctionScopes] using hContext
                  have hTailRun :=
                    ih (tailFuel + 1) (by omega) tail
                      (slack := slack + 1)
                      (entryStore := entryStore)
                      (shared := shared) (vars := vars) (by
                        unfold sourceFuelFrontendSlack at hSlack ⊢
                        omega) hTailContext hTailPath hNormalized
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                      (scopedSeqRunForward_cons_functionDefinition_omitted_ok
                        (name := name) (params := params) (returns := returns)
                        (body := body) hTailRun)
          | @statement rawHead rawRest state headState finalState
              frontHead frontRest hNonFunction hHead tail =>
              rcases StmtListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              have hHeadExt :=
                Elab.Stmt.elaborate_preserves_clzAllocation
                  rawHead hHead hPath.entryValid
              have hTailExt := tail.clzExtends hHeadExt.after_valid
              have hTailHoisted :
                  HoistedFunctionsExtend headState finalElabState :=
                tail.hoistedExtends
              have hHeadPath :
                  FrontendCompilationPath builtinContext contract
                    elabState headState :=
                hPath.prefixPath hTailExt hTailHoisted
              have hTailPath :
                  FrontendCompilationPath builtinContext contract
                    headState finalElabState :=
                hPath.suffixPath hHeadExt
              have hHeadScopes :
                  headState.functionScopes = elabState.functionScopes :=
                Elab.Stmt.elaborate_preserves_functionScopes rawHead hHead
              have hTailContext :
                  PathCompiledContext builtinContext contract
                    rawContext headState.functionScopes := by
                simpa [hHeadScopes] using hContext
              have hCurrent :=
                frontendPathRunForwardAt_of_slack predecessor
                  (slack := slack) (builtinContext := builtinContext)
                  (contract := contract) (by
                    unfold sourceFuelFrontendSlack at hSlack ⊢
                    omega)
              have hHeadRun :=
                hCurrent.stmt
                  (entryStore := entryStore)
                  (state := (.Ok shared vars : State))
                  (by simp [BlockEntryCompatible])
                  hContext hHeadPath hHead hHeadNormalized
              have hTailRun :
                  ∀ tailShared tailVars,
                    ScopedSeqRunForward entryStore predecessor
                      (predecessor + slack) rawContext rawRest orderedTail
                      contract (.Ok tailShared tailVars) := by
                intro tailShared tailVars
                exact
                  ih predecessor (by omega) tail
                    (slack := slack) (entryStore := entryStore)
                    (shared := tailShared) (vars := tailVars) (by
                      unfold sourceFuelFrontendSlack at hSlack ⊢
                      omega) hTailContext hTailPath hTailNormalized
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using
                  (scopedSeqRunForward_cons hHeadRun hTailRun)

end TopLevelDispatcherElaboration

theorem blockRunForward_of_scope_seq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    {state : State}
    (hScope : Raw.SourceSemantics.functionScope? code = some scope)
    (hSeq :
      DispatcherSeqRunForward rawFuel orderedFuel
        context scope code ordered state) :
    BlockRunForward (rawFuel + 1) (orderedFuel + 1)
      context code ordered state := by
  unfold BlockRunForward DispatcherSeqRunForward orderedRun at *
  rw [Raw.SourceSemantics.ExecBlock.succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [hScope]
  refine Simulation.Interaction.ForwardRel.bind_custom hSeq ?_
  intro leftDone rightDone hDone
  cases hDone with
  | error hError =>
      subst_vars
      exact Simulation.Interaction.ForwardRel.done rfl
  | @ok rawState orderedState hRestricted =>
      subst orderedState
      apply Simulation.Interaction.ForwardRel.done
      unfold SameDoneRel
      congr 1
      exact (Yul.InteractionSemantics.State.restrictStoreTo_idem
        rawState state.store).symm

theorem rawObjectRun_none_code
    {fuel : Nat} {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {state : State}
    (hCode : object.code? = none) :
    rawObjectRun fuel context object state = pure state := by
  unfold rawObjectRun
  exact Raw.SourceSemantics.ExecObjectCode.code_none
    fuel (Raw.SourceSemantics.contextForObject context) object state hCode

theorem rawObjectRun_some_code
    {fuel : Nat} {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {state : State}
    {code : List Raw.Stmt}
    (hCode : object.code? = some code) :
    rawObjectRun fuel context object state =
      Raw.SourceSemantics.execCode fuel
        (Raw.SourceSemantics.contextForObject context) code state := by
  unfold rawObjectRun
  exact Raw.SourceSemantics.ExecObjectCode.code_some
    fuel (Raw.SourceSemantics.contextForObject context) object state hCode

theorem rawObjectRun_some_code_succ
    {fuel : Nat} {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {state : State}
    {code : List Raw.Stmt}
    (hCode : object.code? = some code) :
    rawObjectRun (fuel + 1) context object state =
      Raw.SourceSemantics.execBlock (fuel + 1)
        (Raw.SourceSemantics.contextForObject context) code state := by
  unfold rawObjectRun
  exact Raw.SourceSemantics.ExecObjectCode.code_some_succ
    fuel (Raw.SourceSemantics.contextForObject context) object state hCode

/-- Finite-prefix preservation from raw solc Yul execution to ordered Yul
execution for one selected object/context/fuel pair. -/
def RunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (rawObjectRun rawFuel context object state)
    (orderedRun orderedFuel ordered state)

/-- Whole-object raw-to-ordered preservation surface.

The proof should be private to the Solidity frontend: callers get it by
successful raw decoding/elaboration/compilation, not by providing generated
names, replay traces, layouts, or certificates.
-/
structure ObjectPreserved
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel, RunForward rawFuel orderedFuel context object ordered state

theorem runForward_of_eq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    {state : State}
    (hRun :
      rawObjectRun rawFuel context object state =
        orderedRun orderedFuel ordered state) :
    RunForward rawFuel orderedFuel context object ordered state := by
  unfold RunForward
  rw [hRun]
  exact
    forward_refl Yul.FunctionsInteractionPrimitive.Truncated
      (orderedRun orderedFuel ordered state)

theorem blockRunForward_of_eq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    {state : State}
    (hRun :
      Raw.SourceSemantics.execBlock rawFuel
          (Raw.SourceSemantics.contextForObject context) code state =
        orderedRun orderedFuel ordered state) :
    BlockRunForward rawFuel orderedFuel context code ordered state := by
  unfold BlockRunForward
  rw [hRun]
  exact
    forward_refl Yul.FunctionsInteractionPrimitive.Truncated
      (orderedRun orderedFuel ordered state)

structure ObjectRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        rawObjectRun rawFuel context object state =
          orderedRun orderedFuel ordered state

namespace ObjectRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    (hEq : ObjectRunEquivalent context object ordered) :
    ObjectPreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, runForward_of_eq hRun⟩

end ObjectRunEquivalent

structure ObjectPositiveRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        rawObjectRun (rawFuel + 1) context object state =
          orderedRun (orderedFuel + 1) ordered state

structure ObjectPositivePreserved
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        RunForward (rawFuel + 1) (orderedFuel + 1)
          context object ordered state

structure CodePositiveRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        Raw.SourceSemantics.execBlock (rawFuel + 1)
            (Raw.SourceSemantics.contextForObject context) code state =
          orderedRun (orderedFuel + 1) ordered state

structure CodePositivePreserved
    (context : Frontend.ObjectBuiltinContext)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        BlockRunForward (rawFuel + 1) (orderedFuel + 1)
          context code ordered state

namespace ObjectPositiveRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    (hEq : ObjectPositiveRunEquivalent context object ordered) :
    ObjectPositivePreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, runForward_of_eq hRun⟩

end ObjectPositiveRunEquivalent

namespace CodePositiveRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    (hEq : CodePositiveRunEquivalent context code ordered) :
    CodePositivePreserved context code ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, blockRunForward_of_eq hRun⟩

end CodePositiveRunEquivalent

namespace CodePositivePreserved

theorem of_scope_dispatcher_seq
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    (hScope : Raw.SourceSemantics.functionScope? code = some scope)
    (hSeq :
      ∀ (rawFuel : Nat) (state : State),
        ∃ orderedFuel,
          DispatcherSeqRunForward rawFuel orderedFuel
            context scope code ordered state) :
    CodePositivePreserved context code ordered where
  forward := by
    intro rawFuel state
    rcases hSeq rawFuel state with ⟨orderedFuel, hForward⟩
    exact
      ⟨orderedFuel,
        blockRunForward_of_scope_seq hScope hForward⟩

theorem toObjectPositive
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    {code : List Raw.Stmt}
    (hCodeRun : CodePositivePreserved context code ordered)
    (hCode : object.code? = some code) :
    ObjectPositivePreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hCodeRun.forward rawFuel state with ⟨orderedFuel, hForward⟩
    refine ⟨orderedFuel, ?_⟩
    unfold RunForward BlockRunForward at *
    rw [rawObjectRun_some_code_succ hCode]
    exact hForward

end CodePositivePreserved

/-- The raw source scope and the elaborator's top-function scope may carry
different payloads, but they must expose the same function names. -/
def FunctionScopeNameRel
    (rawScope : Raw.SourceSemantics.FunctionScope)
    (topScope : List (Name × Name)) : Prop :=
  ∀ name,
    rawScope.any (fun entry => entry.fst == name) =
      topScope.any (fun entry => entry.fst == name)

theorem collectTopFunctions_rawFunctionScope
    {stmts : List Raw.Stmt}
    {state finalState : Elab.State}
    {topScope : List (Name × Name)}
    (hCollect :
      (Elab.collectTopFunctions stmts).run state =
        .ok (topScope, finalState)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope ∧
        FunctionScopeNameRel rawScope topScope := by
  induction stmts generalizing state finalState topScope with
  | nil =>
      unfold Elab.collectTopFunctions at hCollect
      simp [StateT.run_pure] at hCollect
      cases hCollect
      refine ⟨[], rfl, ?_⟩
      intro name
      simp
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          unfold Elab.collectTopFunctions at hCollect
          simp [StateT.run_bind] at hCollect
          cases hTail : (Elab.collectTopFunctions rest).run state with
          | error err =>
              simp [hTail] at hCollect
          | ok tailResult =>
              rcases tailResult with ⟨topTail, tailState⟩
              simp [hTail] at hCollect
              cases hDuplicate :
                  topTail.any (fun entry => entry.fst == name) with
              | true =>
                  rw [hDuplicate] at hCollect
                  unfold Elab.throw at hCollect
                  dsimp at hCollect
                  change
                    (Except.bind
                        ((fun _ : Elab.State =>
                            Except.error
                              (toString "duplicate top-level Yul function " ++
                                toString name)) tailState)
                        ?cont) =
                      Except.ok (topScope, finalState) at hCollect
                  change
                    (Except.error
                      (toString "duplicate top-level Yul function " ++
                        toString name) :
                      Except String (List (Name × Name) × Elab.State)) =
                      Except.ok (topScope, finalState) at hCollect
                  cases hCollect
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run
                        tailState with
                  | error err =>
                      simp [hDuplicate, hDeclare] at hCollect
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      simp [hDuplicate, hDeclare, StateT.run_bind] at hCollect
                      rcases hCollect with ⟨hTopScope, _hFinalState⟩
                      cases hTopScope
                      rcases ih hTail with
                        ⟨rawTail, hRawTail, hNameRel⟩
                      have hRawDuplicate :
                          rawTail.any (fun entry => entry.fst == name) =
                            false := by
                        rw [hNameRel name, hDuplicate]
                      refine
                        ⟨(name, { params, returns, body }) :: rawTail,
                          ?_, ?_⟩
                      · simp [Raw.SourceSemantics.functionScope?,
                          hRawTail, hRawDuplicate]
                      · intro query
                        simp [hNameRel query]
      | block stmts =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]

      | variableDeclaration names value? =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | assignment names value =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | expressionStatement expr =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | switch scrutinee cases default =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | forLoop pre condition post body =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | ifThen condition body =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | «break» =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | «continue» =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | «leave» =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]

private theorem collectTopFunctions_preserves_functionScopes
    (stmts : List Raw.Stmt) :
    Elab.PreservesFunctionScopes (Elab.collectTopFunctions stmts) := by
  intro state finalState scope hRun
  induction stmts generalizing state finalState scope with
  | nil =>
      simp [Elab.collectTopFunctions, StateT.run_pure] at hRun
      cases hRun
      rfl
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          unfold Elab.collectTopFunctions at hRun
          simp [StateT.run_bind] at hRun
          cases hTail : (Elab.collectTopFunctions rest).run state with
          | error err => simp [hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨tail, tailState⟩
              have hTailScopes := ih hTail
              simp [hTail] at hRun
              cases hDuplicate : tail.any fun entry => entry.fst == name with
              | true =>
                  simp [hDuplicate] at hRun
                  unfold Elab.throw at hRun
                  cases hRun
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run tailState with
                  | error err => simp [hDuplicate, hDeclare] at hRun
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      have hDeclareScopes :=
                        Elab.declareIdentifiers_preserves_functionScopes
                          [name] "function" hDeclare
                      simp [hDuplicate, hDeclare, StateT.run_bind,
                        StateT.run_modify, StateT.run_pure] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      exact hDeclareScopes.trans hTailScopes
      | block nested => exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | variableDeclaration names value =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | assignment names value =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | expressionStatement expr =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | switch scrutinee cases default =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | forLoop pre condition post body =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | ifThen condition body =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | «break» => exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | «continue» => exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | «leave» => exact ih (by simpa [Elab.collectTopFunctions] using hRun)

private theorem collectTopFunctions_preserves_clzAllocation
    (stmts : List Raw.Stmt) :
    Elab.PreservesClzAllocation (Elab.collectTopFunctions stmts) := by
  intro state finalState scope hRun hValid
  induction stmts generalizing state finalState scope with
  | nil =>
      simp [Elab.collectTopFunctions, StateT.run_pure] at hRun
      cases hRun
      exact Elab.ClzAllocationExtends.refl state hValid
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          unfold Elab.collectTopFunctions at hRun
          simp [StateT.run_bind] at hRun
          cases hTail : (Elab.collectTopFunctions rest).run state with
          | error err => simp [hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨tail, tailState⟩
              have hTailExt := ih hTail hValid
              simp [hTail] at hRun
              cases hDuplicate : tail.any fun entry => entry.fst == name with
              | true =>
                  simp [hDuplicate] at hRun
                  unfold Elab.throw at hRun
                  cases hRun
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run tailState with
                  | error err => simp [hDuplicate, hDeclare] at hRun
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      have hDeclareExt :=
                        Elab.declareIdentifiers_preserves_clzAllocation
                          [name] "function" hDeclare hTailExt.after_valid
                      simp [hDuplicate, hDeclare, StateT.run_bind,
                        StateT.run_modify, StateT.run_pure] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      exact hTailExt.trans
                        (hDeclareExt.trans
                          (Elab.ClzAllocationExtends.of_fields_eq
                            hDeclareExt.after_valid rfl rfl rfl))
      | block nested => exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | variableDeclaration names value =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | assignment names value =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | expressionStatement expr =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | switch scrutinee cases default =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | forLoop pre condition post body =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | ifThen condition body =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | «break» => exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | «continue» => exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid
      | «leave» => exact ih (by simpa [Elab.collectTopFunctions] using hRun) hValid

private def TopFunctionScopeIdentity (scope : List (Name × Name)) : Prop :=
  ∀ {source target}, (source, target) ∈ scope → target = source

private theorem collectTopFunctions_scopeIdentity
    {stmts : List Raw.Stmt} {state finalState : Elab.State}
    {scope : List (Name × Name)}
    (hRun :
      (Elab.collectTopFunctions stmts).run state = .ok (scope, finalState)) :
    TopFunctionScopeIdentity scope := by
  induction stmts generalizing state finalState scope with
  | nil =>
      simp [Elab.collectTopFunctions, StateT.run_pure] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      intro source target hMem
      simp at hMem
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          unfold Elab.collectTopFunctions at hRun
          simp [StateT.run_bind] at hRun
          cases hTail : (Elab.collectTopFunctions rest).run state with
          | error err => simp [hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨tail, tailState⟩
              have hTailIdentity : TopFunctionScopeIdentity tail := ih hTail
              simp [hTail] at hRun
              cases hDuplicate : tail.any fun entry => entry.fst == name with
              | true =>
                  simp [hDuplicate] at hRun
                  unfold Elab.throw at hRun
                  cases hRun
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run tailState with
                  | error err => simp [hDuplicate, hDeclare] at hRun
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      simp [hDuplicate, hDeclare, StateT.run_bind,
                        StateT.run_modify, StateT.run_pure] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      intro source target hMem
                      simp at hMem
                      rcases hMem with hHead | hTailMem
                      · rcases hHead with ⟨rfl, rfl⟩
                        rfl
                      · exact hTailIdentity hTailMem
      | block nested =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | variableDeclaration names value =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | assignment names value =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | expressionStatement expr =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | switch scrutinee cases default =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | forLoop pre condition post body =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | ifThen condition body =>
          exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | «break» => exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | «continue» => exact ih (by simpa [Elab.collectTopFunctions] using hRun)
      | «leave» => exact ih (by simpa [Elab.collectTopFunctions] using hRun)

/-- Checked decomposition of the real code elaborator at its only semantic
boundary: the source-order top-level run. Administrative setup and teardown are
summarized by scope, allocation, and hoisted-function invariants. -/
structure ElaborateCodeCorePath
    (code : List Raw.Stmt) (dispatcher : List Frontend.Stmt)
    (finalState : Elab.State) where
  rawScope : Raw.SourceSemantics.FunctionScope
  topScope : List (Name × Name)
  topFunctions : List (Name × Frontend.FunctionDef)
  entryState : Elab.State
  topLevelState : Elab.State
  rawScope_eq : Raw.SourceSemantics.functionScope? code = some rawScope
  scopeNames : FunctionScopeNameRel rawScope topScope
  scopeIdentity : TopFunctionScopeIdentity topScope
  entryScopes : entryState.functionScopes = [topScope]
  entryValid : Elab.ClzAllocationValid entryState
  topLevelRun :
    (Elab.elaborateTopLevel code [] []).run entryState =
      .ok ((dispatcher, topFunctions), topLevelState)
  view :
    TopLevelDispatcherElaboration code entryState dispatcher topLevelState
  suffixClz : Elab.ClzAllocationExtends topLevelState finalState
  suffixHoisted : HoistedFunctionsExtend topLevelState finalState
  topFunctionsFinal :
    ∀ {entry}, entry ∈ topFunctions → entry ∈ finalState.hoistedFunctions

theorem elaborateCodeCore_path
    {code : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {finalState : Elab.State}
    (hCore :
      Elab.elaborateCodeCore code = .ok (dispatcher, finalState)) :
    Nonempty (ElaborateCodeCorePath code dispatcher finalState) := by
  unfold Elab.elaborateCodeCore Elab.elaborateCodeAction at hCore
  simp [StateT.run_bind] at hCore
  cases hPushIdentifier : Elab.pushIdentifierScope.run ({} : Elab.State) with
  | error err => simp [hPushIdentifier] at hCore
  | ok pushIdentifierResult =>
      rcases pushIdentifierResult with ⟨_, identifierPushedState⟩
      simp [hPushIdentifier] at hCore
      cases hCollect :
          (Elab.collectTopFunctions code).run identifierPushedState with
      | error err => simp [hCollect] at hCore
      | ok collectResult =>
          rcases collectResult with ⟨topScope, collectState⟩
          simp [hCollect] at hCore
          cases hPushFunction :
              (Elab.pushFunctionScope topScope).run collectState with
          | error err => simp [hPushFunction] at hCore
          | ok pushFunctionResult =>
              rcases pushFunctionResult with ⟨_, entryState⟩
              simp [hPushFunction] at hCore
              cases hTopLevel :
                  (Elab.elaborateTopLevel code [] []).run entryState with
              | error err => simp [hTopLevel] at hCore
              | ok topLevelResult =>
                  rcases topLevelResult with ⟨topLevelValue, topLevelState⟩
                  rcases topLevelValue with ⟨topDispatcher, topFunctions⟩
                  simp [hTopLevel] at hCore
                  cases hPopFunction :
                      Elab.popFunctionScope.run topLevelState with
                  | error err => simp [hPopFunction] at hCore
                  | ok popFunctionResult =>
                      rcases popFunctionResult with ⟨_, functionPoppedState⟩
                      simp [hPopFunction] at hCore
                      cases hPopIdentifier :
                          Elab.popIdentifierScope.run functionPoppedState with
                      | error err => simp [hPopIdentifier] at hCore
                      | ok popIdentifierResult =>
                          rcases popIdentifierResult with
                            ⟨_, identifierPoppedState⟩
                          simp [hPopIdentifier, StateT.run_bind,
                            StateT.run_get, StateT.run_set] at hCore
                          rcases hCore with ⟨hDispatcher, hFinal⟩
                          cases hDispatcher
                          cases hFinal
                          rcases collectTopFunctions_rawFunctionScope hCollect with
                            ⟨rawScope, hRawScope, hScopeNames⟩
                          have hScopeIdentity :
                              TopFunctionScopeIdentity topScope :=
                            collectTopFunctions_scopeIdentity hCollect
                          have hPushIdentifierScopes :=
                            Elab.pushIdentifierScope_preserves_functionScopes
                              hPushIdentifier
                          have hCollectScopes :=
                            collectTopFunctions_preserves_functionScopes code
                              hCollect
                          have hEntryScopes :
                              entryState.functionScopes = [topScope] := by
                            have hPushed :
                                entryState.functionScopes =
                                  topScope :: collectState.functionScopes := by
                              unfold Elab.pushFunctionScope at hPushFunction
                              simp [StateT.run_modify] at hPushFunction
                              cases hPushFunction
                              rfl
                            rw [hPushed, hCollectScopes,
                              hPushIdentifierScopes]
                          have hPushIdentifierExt :=
                            Elab.pushIdentifierScope_preserves_clzAllocation
                              hPushIdentifier Elab.initial_clzAllocationValid
                          have hCollectExt :=
                            collectTopFunctions_preserves_clzAllocation code
                              hCollect hPushIdentifierExt.after_valid
                          have hPushFunctionExt :=
                            Elab.pushFunctionScope_preserves_clzAllocation
                              topScope hPushFunction hCollectExt.after_valid
                          have hEntryValid := hPushFunctionExt.after_valid
                          rcases topLevelDispatcherElaboration_of_run hTopLevel with
                            ⟨emitted, hEmitted, hView⟩
                          simp at hEmitted
                          subst emitted
                          have hTopLevelExt := hView.clzExtends hEntryValid
                          have hPopFunctionExt :=
                            Elab.popFunctionScope_preserves_clzAllocation
                              hPopFunction hTopLevelExt.after_valid
                          have hPopIdentifierExt :=
                            Elab.popIdentifierScope_preserves_clzAllocation
                              hPopIdentifier hPopFunctionExt.after_valid
                          have hFinishExt :
                              Elab.ClzAllocationExtends identifierPoppedState
                                { identifierPoppedState with
                                  hoistedFunctions :=
                                    identifierPoppedState.hoistedFunctions ++
                                      topFunctions } :=
                            Elab.ClzAllocationExtends.of_fields_eq
                              hPopIdentifierExt.after_valid rfl rfl rfl
                          have hSuffixClz :
                              Elab.ClzAllocationExtends topLevelState
                                { identifierPoppedState with
                                  hoistedFunctions :=
                                    identifierPoppedState.hoistedFunctions ++
                                      topFunctions } :=
                            hPopFunctionExt.trans
                              (hPopIdentifierExt.trans hFinishExt)
                          have hPopFunctionHoisted :
                              HoistedFunctionsExtend topLevelState
                                functionPoppedState := by
                            intro entry hEntry
                            exact
                              Elab.popFunctionScope_preserves_hoistedFunction_mem
                                hPopFunction hEntry
                          have hPopIdentifierHoisted :
                              HoistedFunctionsExtend functionPoppedState
                                identifierPoppedState := by
                            intro entry hEntry
                            exact
                              Elab.popIdentifierScope_preserves_hoistedFunction_mem
                                hPopIdentifier hEntry
                          have hFinishHoisted :
                              HoistedFunctionsExtend identifierPoppedState
                                { identifierPoppedState with
                                  hoistedFunctions :=
                                    identifierPoppedState.hoistedFunctions ++
                                      topFunctions } := by
                            intro entry hEntry
                            exact List.mem_append_left _ hEntry
                          have hSuffixHoisted :
                              HoistedFunctionsExtend topLevelState
                                { identifierPoppedState with
                                  hoistedFunctions :=
                                    identifierPoppedState.hoistedFunctions ++
                                      topFunctions } :=
                            hPopFunctionHoisted.trans
                              (hPopIdentifierHoisted.trans hFinishHoisted)
                          exact ⟨{
                            rawScope := rawScope
                            topScope := topScope
                            topFunctions := topFunctions
                            entryState := entryState
                            topLevelState := topLevelState
                            rawScope_eq := hRawScope
                            scopeNames := hScopeNames
                            scopeIdentity := hScopeIdentity
                            entryScopes := hEntryScopes
                            entryValid := hEntryValid
                            topLevelRun := hTopLevel
                            view := hView
                            suffixClz := hSuffixClz
                            suffixHoisted := hSuffixHoisted
                            topFunctionsFinal := by
                              intro entry hEntry
                              exact List.mem_append_right _ hEntry }⟩

private theorem generatedLookup_mem
    {scope : List (Name × Name)} {source target : Name}
    (hLookup : Elab.lookupFunctionInScope source scope = some target) :
    (source, target) ∈ scope := by
  induction scope with
  | nil => simp [Elab.lookupFunctionInScope] at hLookup
  | cons entry rest ih =>
      rcases entry with ⟨headSource, headTarget⟩
      by_cases hName : headSource = source
      · subst headSource
        simp [Elab.lookupFunctionInScope] at hLookup
        subst target
        simp
      · simp [Elab.lookupFunctionInScope, hName] at hLookup
        exact List.mem_cons_of_mem _ (ih hLookup)

private theorem generatedLookup_some_of_any
    {scope : List (Name × Name)} {source : Name}
    (hAny : (scope.any fun entry => entry.fst == source) = true) :
    ∃ target, Elab.lookupFunctionInScope source scope = some target := by
  induction scope with
  | nil => simp at hAny
  | cons entry rest ih =>
      rcases entry with ⟨headSource, headTarget⟩
      by_cases hName : headSource = source
      · subst headSource
        exact ⟨headTarget, by simp [Elab.lookupFunctionInScope]⟩
      · have hHeadFalse : (headSource == source) = false := by
          simp [hName]
        change
          ((headSource == source) ||
            (rest.any fun entry => entry.fst == source)) = true at hAny
        rw [hHeadFalse] at hAny
        rcases ih hAny with ⟨target, hLookup⟩
        exact ⟨target, by simp [Elab.lookupFunctionInScope, hName, hLookup]⟩

private theorem rawLookup_none_any_eq_false
    {scope : Raw.SourceSemantics.FunctionScope} {source : Name}
    (hLookup :
      Raw.SourceSemantics.lookupFunctionInScope source scope = none) :
    (scope.any fun entry => entry.fst == source) = false := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨headName, headFn⟩
      by_cases hName : headName = source
      · subst headName
        simp [Raw.SourceSemantics.lookupFunctionInScope] at hLookup
      · simp [Raw.SourceSemantics.lookupFunctionInScope, hName] at hLookup
        simp [hName, ih hLookup]

namespace ElaborateCodeCorePath

theorem topScopeCompiled
    {code : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {finalState : Elab.State}
    (core : ElaborateCodeCorePath code dispatcher finalState)
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hPath :
      FrontendCompilationPath builtinContext contract
        core.entryState finalState) :
    PathCompiledFunctionScope builtinContext contract
      core.rawScope core.topScope [core.topScope] where
  binding := by
    intro rawName generated hGeneratedLookup
    have hGeneratedMem := generatedLookup_mem hGeneratedLookup
    have hGeneratedEq : generated = rawName :=
      core.scopeIdentity hGeneratedMem
    subst generated
    have hGeneratedAny :=
      Elab.Stmt.List.lookupFunctionInScope_any_eq_true hGeneratedLookup
    have hRawAny :
        (core.rawScope.any fun entry => entry.fst == rawName) = true := by
      rw [core.scopeNames rawName]
      exact hGeneratedAny
    cases hRawLookup :
        Raw.SourceSemantics.lookupFunctionInScope rawName core.rawScope with
    | none =>
        have hImpossible :
            (core.rawScope.any fun entry => entry.fst == rawName) = false := by
          exact rawLookup_none_any_eq_false hRawLookup
        rw [hImpossible] at hRawAny
        cases hRawAny
    | some rawFn =>
        rcases
            Raw.SourceSemantics.functionScope?_lookup_functionDefinition
              core.rawScope_eq hRawLookup with
          ⟨params, returns, body, hMem, hRawFn⟩
        subst rawFn
        rcases core.view.topLevelFunctionWitness_of_run_mem
            core.topLevelRun core.entryValid hMem with
          ⟨witness⟩
        cases witness with
        | mk functionState finalFunctionState frontFunction
            hElaborates hScopes hOutput hPrefix hSuffix hHoisted =>
            rcases hPath.hoistedResolver
                (core.topFunctionsFinal hOutput) with
              ⟨hOrdered⟩
            have hFrontFields :=
              Elab.FunctionDef.elaborate_params_returns hElaborates
            have hOrderedLookup := hOrdered.orderedLookup
            rw [hFrontFields.1, hFrontFields.2] at hOrderedLookup
            refine
              ⟨{ params := params, returns := returns, body := body },
                rfl, ?_⟩
            exact ⟨{
                  frontFn := frontFunction
                  functionState := functionState
                  finalFunctionState := finalFunctionState
                  orderedBody := hOrdered.orderedBody
                  functionScopes := hScopes.trans core.entryScopes
                  elaborates := hElaborates
                  bodyNormalized := hOrdered.bodyNormalized
                  orderedLookup := hOrderedLookup
                  compilationPath :=
                    hPath.subpath hPrefix
                      (hSuffix.trans core.suffixClz)
                      (hHoisted.trans core.suffixHoisted) }⟩
  rawLookupNone := by
    intro rawName hGeneratedNone
    cases hRawLookup :
        Raw.SourceSemantics.lookupFunctionInScope rawName core.rawScope with
    | none => rfl
    | some rawFn =>
        have hRawAny :=
          Raw.SourceSemantics.lookupFunctionInScope_some_any hRawLookup
        have hGeneratedAny :
            (core.topScope.any fun entry => entry.fst == rawName) = true := by
          rw [← core.scopeNames rawName]
          exact hRawAny
        rcases generatedLookup_some_of_any hGeneratedAny with
          ⟨generated, hGenerated⟩
        rw [hGeneratedNone] at hGenerated
        cases hGenerated

end ElaborateCodeCorePath

theorem elaborateCodeCore_rawFunctionScope
    {stmts : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt} {state : Elab.State}
    (hCore :
      Elab.elaborateCodeCore stmts = .ok (dispatcher, state)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope := by
  unfold Elab.elaborateCodeCore Elab.elaborateCodeAction at hCore
  simp [StateT.run_bind] at hCore
  cases hPush : Elab.pushIdentifierScope.run {} with
  | error err =>
      simp [hPush] at hCore
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      simp [hPush] at hCore
      cases hCollect :
          (Elab.collectTopFunctions stmts).run pushedState with
      | error err =>
          simp [hCollect] at hCore
      | ok collectResult =>
          rcases collectResult with ⟨topScope, collectState⟩
          rcases collectTopFunctions_rawFunctionScope hCollect with
            ⟨rawScope, hRawScope, _hNameRel⟩
          exact ⟨rawScope, hRawScope⟩

theorem elaborateCode_rawFunctionScope
    {stmts : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    (hElab :
      Elab.elaborateCode stmts =
        .ok (dispatcher, functions, helper?, arg?, ret?)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope := by
  rcases Elab.elaborateCode_parts hElab with
    ⟨state, hCore, _hFunctions, _hHelper, _hArg, _hRet⟩
  exact elaborateCodeCore_rawFunctionScope hCore

structure ArtifactRawSourceContext
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact) where
  json : Lean.Json
  selected : SelectedIr
  program : Frontend.Program
  linkerSymbols : List (Frontend.Name × Frontend.Word)
  context : Frontend.ObjectBuiltinContext
  parse :
    Lean.Json.parse rawJson = .ok json
  selected_ok :
    decodeSelectedIr json selection = .ok selected
  decode :
    decodeAndElaborateSolcIr? rawJson selection = some program
  raw_elaborates :
    selected.root.elaborate? selected.evmVersion = .ok program.object
  linker :
    decodeLinkerSymbols? rawJson selection = some linkerSymbols
  compile :
    program.compileArtifactWithLinkerSymbols? linkerSymbols = some artifact
  codeArtifact :
    program.object.compileVerifiedStackCodeArtifactIn? context =
      some artifact.codeArtifact
  resolved :
    program.object.resolveObjectBuiltinsIn? context =
      some artifact.codeArtifact.resolved
  ordered :
    artifact.codeArtifact.resolved.toSolcYulOrderedProgram? =
      some artifact.codeArtifact.ordered
  sourceContext :
    Raw.SourceSemantics.contextForObject context =
      { objectBuiltins := context }

namespace ArtifactRawSourceContext

theorem nonempty_of_compile
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    Nonempty (ArtifactRawSourceContext rawJson selection artifact) := by
  rcases compileArtifactFromRawSolcIr?_raw_source_ordered_context hCompile with
    ⟨json, selected, program, linkerSymbols, context,
      hParse, hSelected, hDecode, hRawElab, hLinker, hProgramCompile,
      hCodeArtifact, hResolved, hOrdered, hSourceContext⟩
  exact ⟨
    { json := json
      selected := selected
      program := program
      linkerSymbols := linkerSymbols
      context := context
      parse := hParse
      selected_ok := hSelected
      decode := hDecode
      raw_elaborates := hRawElab
      linker := hLinker
      compile := hProgramCompile
      codeArtifact := hCodeArtifact
      resolved := hResolved
      ordered := hOrdered
      sourceContext := hSourceContext }⟩

theorem code_elaborates
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ helper? arg? ret?,
      Elab.elaborateCode code =
        .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
          helper?, arg?, ret?) := by
  rcases Raw.Object.elaborate?_parts ctx.raw_elaborates with
    ⟨_itemFuel, dispatcher, functions, helper?, arg?, ret?,
      _data, _objects, _items, _hFuel, hCodeElab, _hItems, hFrontend⟩
  have hElab :
      Elab.elaborateCode code =
        .ok (dispatcher, functions, helper?, arg?, ret?) := by
    simpa [hCode] using hCodeElab
  refine ⟨helper?, arg?, ret?, ?_⟩
  have hDispatcher :
      ctx.program.object.dispatcher = dispatcher := by
    rw [hFrontend]
  have hFunctions :
      ctx.program.object.functions = functions := by
    rw [hFrontend]
  rw [hDispatcher, hFunctions]
  exact hElab

/-- Successful raw compilation constructs the exact generated-`clz` resolver
for the final code-elaboration state. Name allocation, frontend validation,
object-builtin resolution, Yul conversion, and canonical lookup are all
discharged from the compiler artifact; callers supply no helper certificate. -/
theorem clzBindingResolverAt
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ coreDispatcher finalState,
      Elab.elaborateCodeCore code = .ok (coreDispatcher, finalState) ∧
        ClzBindingResolverAt
          artifact.codeArtifact.ordered.program.contract finalState := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  rcases Elab.elaborateCode_parts hElab with
    ⟨finalState, hCore, hFunctions, hHelper, hArg, hRet⟩
  refine ⟨ctx.program.object.dispatcher, finalState, hCore, ?_⟩
  intro generated allocatedArg allocatedRet hAllocated
  have hHelperOption : helper? = some generated := by
    rw [hHelper]
    exact hAllocated.helper_eq
  have hArgOption : arg? = some allocatedArg := by
    rw [hArg]
    exact hAllocated.arg_eq
  have hRetOption : ret? = some allocatedRet := by
    rw [hRet]
    exact hAllocated.ret_eq
  have hExactElab :
      Elab.elaborateCode code =
        .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
          some generated, some allocatedArg, some allocatedRet) := by
    simpa [hHelperOption, hArgOption, hRetOption] using hElab
  rcases decodeAndElaborateSolcIr?_frontendValidated ctx.decode with
    ⟨json, selected, object, hParse, hSelected, hObject,
      hValidated, hProgram⟩
  rw [ctx.parse] at hParse
  cases hParse
  rw [ctx.selected_ok] at hSelected
  cases hSelected
  have hValidatedProgram :
      Raw.Object.FrontendValidated
        ctx.selected.root ctx.program.object := by
    simpa [hProgram] using hValidated
  have hNamesBool :
      Raw.Object.clzHelperNamesDistinct? ctx.selected.root = true :=
    hValidatedProgram.2.1
  have hNames : allocatedArg ≠ allocatedRet :=
    Raw.Object.clzHelperNamesDistinct?_arg_ne
      hCode hExactElab hNamesBool
  have hHelperMem :
      (generated,
        Elab.clzHelperFunctionDef allocatedArg allocatedRet) ∈
          ctx.program.object.functions :=
    Elab.elaborateCode_clzHelper_mem hExactElab
  rcases Frontend.Object.compileVerifiedStackCodeArtifactIn?_function_entry
      ctx.codeArtifact hHelperMem with
    ⟨memoryContract, resolvedFn, yulBody, _hMemory, hResolve,
      _hResolvedMem, hParams, hReturns, hBodyYul, hEntry⟩
  have hResolveIdentity :=
    EvmCompiler.Solidity.RawAst.Raw.ClzPreservation.clzHelperFunctionDef_resolveObjectBuiltinsIn?
      allocatedArg allocatedRet
      { ctx.context with memoryContract := memoryContract }
  rw [hResolveIdentity] at hResolve
  have hResolvedFn :
      resolvedFn = Elab.clzHelperFunctionDef allocatedArg allocatedRet :=
    Option.some.inj hResolve.symm
  subst resolvedFn
  have hOrderedSource :=
    Frontend.Object.toSolcYulOrderedProgram?_source ctx.ordered
  have hLookup :
      artifact.codeArtifact.ordered.program.contract.functions.lookup
          generated =
        some
          (.Def
            (Elab.clzHelperFunctionDef allocatedArg allocatedRet).params
            (Elab.clzHelperFunctionDef allocatedArg allocatedRet).returns
            yulBody) := by
    rw [hOrderedSource.1]
    exact
      EvmCompiler.Yul.FunctionList.lookup_functionMap_of_mem
        hOrderedSource.2.1 hEntry
  refine ⟨{
    argName := allocatedArg
    returnName := allocatedRet
    yulBody := yulBody
    namesDistinct := hNames
    orderedLookup := ?_
    bodyToYul := ?_ }⟩
  · simpa [Elab.clzHelperFunctionDef] using hLookup
  · simpa [Elab.clzHelperFunctionDef] using hBodyYul

/-- Successful raw compilation resolves every frontend function accumulated by
the code elaborator to its exact normalized ordered-Yul contract entry. -/
theorem hoistedFunctionResolverAt
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ coreDispatcher finalState memoryContract,
      Elab.elaborateCodeCore code = .ok (coreDispatcher, finalState) ∧
        Frontend.MemoryGuard.Object.inferredContract? ctx.program.object =
          some memoryContract ∧
        HoistedFunctionResolverAt
          { ctx.context with memoryContract := memoryContract }
          artifact.codeArtifact.ordered.program.contract finalState := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  rcases Elab.elaborateCode_parts hElab with
    ⟨finalState, hCore, hFunctions, _hHelper, _hArg, _hRet⟩
  rcases
      Frontend.Object.resolveObjectBuiltinsIn?_dispatcher ctx.resolved with
    ⟨memoryContract, _resolvedDispatcher,
      hMemory, _hResolve, _hResolved⟩
  refine
    ⟨ctx.program.object.dispatcher, finalState, memoryContract,
      hCore, hMemory, ?_⟩
  intro generated frontFn hEntry
  have hFinalEntry :
      (generated, frontFn) ∈ Elab.finalFunctions finalState :=
    Elab.finalFunctions_hoistedFunction_mem finalState hEntry
  have hProgramEntry :
      (generated, frontFn) ∈ ctx.program.object.functions := by
    rw [hFunctions]
    exact hFinalEntry
  rcases Frontend.Object.compileVerifiedStackCodeArtifactIn?_function_entry
      ctx.codeArtifact hProgramEntry with
    ⟨entryMemoryContract, resolvedFn, yulBody, hEntryMemory,
      hResolve, _hResolvedMem, hParams, hReturns, hBodyYul, hEntryOrdered⟩
  have hMemoryEq : entryMemoryContract = memoryContract := by
    rw [hMemory] at hEntryMemory
  subst entryMemoryContract
  rcases Frontend.FunctionDef.resolveObjectBuiltinsIn?_body hResolve with
    ⟨resolvedBody, hBodyResolve, hResolvedFn⟩
  subst resolvedFn
  have hOrderedSource :=
    Frontend.Object.toSolcYulOrderedProgram?_source ctx.ordered
  have hLookup :
      artifact.codeArtifact.ordered.program.contract.functions.lookup
          generated =
        some (.Def frontFn.params frontFn.returns yulBody) := by
    rw [hOrderedSource.1]
    exact
      EvmCompiler.Yul.FunctionList.lookup_functionMap_of_mem
        hOrderedSource.2.1 hEntryOrdered
  exact ⟨{
    orderedBody := yulBody
    bodyNormalized := {
      resolved := resolvedBody
      resolve := hBodyResolve
      toYul := hBodyYul }
    orderedLookup := hLookup }⟩

/-- Recover the exact frontend and canonical dispatcher lists executed by the
artifact from successful raw-code elaboration, object-builtin resolution, and
ordered-Yul conversion. All generated memoryguard context remains internal. -/
theorem dispatcher_parts
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ helper? arg? ret? memoryContract resolvedDispatcher orderedDispatcher,
      Elab.elaborateCode code =
          .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
            helper?, arg?, ret?) ∧
        Frontend.MemoryGuard.Object.inferredContract? ctx.program.object =
          some memoryContract ∧
        Frontend.Stmt.List.resolveObjectBuiltinsIn?
            ctx.program.object.dispatcher
            { ctx.context with memoryContract := memoryContract } =
          some resolvedDispatcher ∧
        artifact.codeArtifact.resolved.dispatcher = resolvedDispatcher ∧
        Frontend.Stmt.List.toYul? resolvedDispatcher =
          some orderedDispatcher ∧
        artifact.codeArtifact.ordered.program.contract.dispatcher =
          .Block orderedDispatcher := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  rcases
      Frontend.Object.resolveObjectBuiltinsIn?_dispatcher ctx.resolved with
    ⟨memoryContract, resolvedDispatcher,
      hMemory, hResolveDispatcher, hResolvedDispatcher⟩
  rcases
      Frontend.Object.toSolcYulOrderedProgram?_dispatcher ctx.ordered with
    ⟨orderedDispatcher, hToYul, hOrderedDispatcher⟩
  have hResolvedToYul :
      Frontend.Stmt.List.toYul? resolvedDispatcher =
        some orderedDispatcher := by
    rw [← hResolvedDispatcher]
    exact hToYul
  exact
    ⟨helper?, arg?, ret?, memoryContract, resolvedDispatcher,
      orderedDispatcher, hElab, hMemory, hResolveDispatcher,
      hResolvedDispatcher, hResolvedToYul, hOrderedDispatcher⟩

theorem dispatcher_normalized
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ helper? arg? ret? memoryContract orderedDispatcher,
      Elab.elaborateCode code =
          .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
            helper?, arg?, ret?) ∧
        Frontend.MemoryGuard.Object.inferredContract? ctx.program.object =
          some memoryContract ∧
        Nonempty
          (StmtListNormalized
            { ctx.context with memoryContract := memoryContract }
            ctx.program.object.dispatcher orderedDispatcher) ∧
        artifact.codeArtifact.ordered.program.contract.dispatcher =
          .Block orderedDispatcher := by
  rcases ctx.dispatcher_parts hCode with
    ⟨helper?, arg?, ret?, memoryContract, resolvedDispatcher,
      orderedDispatcher, hElab, hMemory, hResolve, _hResolved,
      hToYul, hOrdered⟩
  exact
    ⟨helper?, arg?, ret?, memoryContract, orderedDispatcher,
      hElab, hMemory,
      ⟨{
        resolved := resolvedDispatcher
        resolve := hResolve
        toYul := hToYul }⟩,
      hOrdered⟩

theorem dispatcher_empty_of_code_none
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    (hCode : ctx.selected.root.code? = none) :
    artifact.codeArtifact.ordered.program.contract.dispatcher = .Block [] := by
  rcases Raw.Object.elaborate?_parts ctx.raw_elaborates with
    ⟨_itemFuel, dispatcher, functions, helper?, arg?, ret?,
      _data, _objects, _items, _hFuel, hCodeElab, _hItems, hFrontend⟩
  rw [hCode] at hCodeElab
  have hProgramDispatcher : ctx.program.object.dispatcher = [] := by
    rw [hFrontend]
    exact hCodeElab.1
  rcases Frontend.Object.resolveObjectBuiltinsIn?_dispatcher ctx.resolved with
    ⟨_memoryContract, resolvedDispatcher, _hMemory,
      hResolve, hResolvedDispatcher⟩
  rw [hProgramDispatcher] at hResolve
  simp [Frontend.Stmt.List.resolveObjectBuiltinsIn?] at hResolve
  subst resolvedDispatcher
  rcases Frontend.Object.toSolcYulOrderedProgram?_dispatcher ctx.ordered with
    ⟨orderedDispatcher, hToYul, hOrderedDispatcher⟩
  rw [hResolve] at hToYul
  simp [Frontend.Stmt.List.toYul?] at hToYul
  subst orderedDispatcher
  exact hOrderedDispatcher

/-- Successful raw compilation constructs the complete top-level semantic path
for every regular Yul state. Generated scopes, helper/function resolvers,
normalization, and artifact lookup are all discharged internally. -/
theorem dispatcherSeqRunForward_ok
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    {rawScope : Raw.SourceSemantics.FunctionScope}
    (hRawScope : Raw.SourceSemantics.functionScope? code = some rawScope)
    (rawFuel : Nat)
    (shared : EvmYul.SharedState .Yul) (vars : EvmYul.Yul.VarStore) :
    ∃ orderedFuel,
      DispatcherSeqRunForward rawFuel orderedFuel
        ctx.context rawScope code artifact.codeArtifact.ordered
        (.Ok shared vars) := by
  rcases ctx.dispatcher_normalized hCode with
    ⟨helper?, arg?, ret?, memoryContract, orderedDispatcher,
      hElab, hMemory, ⟨hNormalized⟩, hDispatcher⟩
  rcases Elab.elaborateCode_parts hElab with
    ⟨finalState, hCore, _hFunctions, _hHelper, _hArg, _hRet⟩
  rcases elaborateCodeCore_path hCore with ⟨core⟩
  have hScopeEq : rawScope = core.rawScope :=
    Option.some.inj (hRawScope.symm.trans core.rawScope_eq)
  subst rawScope
  rcases ctx.clzBindingResolverAt hCode with
    ⟨clzDispatcher, clzState, hClzCore, hClzResolver⟩
  have hClzParts :
      (ctx.program.object.dispatcher, finalState) =
        (clzDispatcher, clzState) :=
    Except.ok.inj (hCore.symm.trans hClzCore)
  rcases Prod.mk.inj hClzParts with ⟨hClzDispatcher, hClzState⟩
  subst clzDispatcher
  subst clzState
  rcases ctx.hoistedFunctionResolverAt hCode with
    ⟨hoistedDispatcher, hoistedState, hoistedMemoryContract,
      hHoistedCore, hHoistedMemory, hHoistedResolver⟩
  have hHoistedParts :
      (ctx.program.object.dispatcher, finalState) =
        (hoistedDispatcher, hoistedState) :=
    Except.ok.inj (hCore.symm.trans hHoistedCore)
  rcases Prod.mk.inj hHoistedParts with
    ⟨hHoistedDispatcher, hHoistedState⟩
  subst hoistedDispatcher
  subst hoistedState
  have hMemoryContract : hoistedMemoryContract = memoryContract := by
    rw [hMemory] at hHoistedMemory
  subst hoistedMemoryContract
  let builtinContext : Frontend.ObjectBuiltinContext :=
    { ctx.context with memoryContract := memoryContract }
  have hOverallPath :
      FrontendCompilationPath builtinContext
        artifact.codeArtifact.ordered.program.contract
        core.entryState finalState :=
    { entryValid := core.entryValid
      finalResolver := hClzResolver
      hoistedResolver := hHoistedResolver }
  have hTopPath :
      FrontendCompilationPath builtinContext
        artifact.codeArtifact.ordered.program.contract
        core.entryState core.topLevelState :=
    hOverallPath.prefixPath core.suffixClz core.suffixHoisted
  have hTopScope :
      PathCompiledFunctionScope builtinContext
        artifact.codeArtifact.ordered.program.contract
        core.rawScope core.topScope [core.topScope] :=
    core.topScopeCompiled hOverallPath
  let rawContext : Raw.SourceSemantics.Context :=
    (Raw.SourceSemantics.contextForObject ctx.context).withFunctionScope
      core.rawScope
  have hContext :
      PathCompiledContext builtinContext
        artifact.codeArtifact.ordered.program.contract rawContext
        [core.topScope] :=
    { objectBuiltins := by
        exact
          ObjectBuiltinContextsAgree.withMemoryContract
            ctx.context memoryContract
      functionScopes := .cons hTopScope .nil }
  have hContextAtEntry :
      PathCompiledContext builtinContext
        artifact.codeArtifact.ordered.program.contract rawContext
        core.entryState.functionScopes := by
    rw [core.entryScopes]
    exact hContext
  have hScoped :=
    core.view.scopedSeqRunForward rawFuel
      (slack := sourceFuelFrontendSlack rawFuel)
      (builtinContext := builtinContext)
      (contract := artifact.codeArtifact.ordered.program.contract)
      (rawContext := rawContext) (ordered := orderedDispatcher)
      (entryStore := vars) (shared := shared) (vars := vars)
      (by omega) hContextAtEntry hTopPath hNormalized
  subst rawContext
  exact
    ⟨rawFuel + sourceFuelFrontendSlack rawFuel + 2,
      dispatcherSeqRunForward_of_scopedSeq hDispatcher hScoped⟩

theorem code_functionScope
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? code = some rawScope := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  exact elaborateCode_rawFunctionScope hElab

end ArtifactRawSourceContext

def RawSourceBytecodePrefixDoneRel
    (artifact : Frontend.Program.Artifact) :
    Except Failure State →
      Except Assembly.EVMException Assembly.StepResult →
        Prop :=
  fun rawDone bytecodeDone =>
    ∃ orderedDone,
      SameDoneRel rawDone orderedDone ∧
        Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
          artifact orderedDone bytecodeDone

structure ArtifactRawSourceEquivalent
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact)
    extends ArtifactRawSourceContext rawJson selection artifact where
  sourceRun :
    ObjectPositiveRunEquivalent context selected.root
      artifact.codeArtifact.ordered

structure ArtifactRawSourcePreserved
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact)
    extends ArtifactRawSourceContext rawJson selection artifact where
  sourceRun :
    ObjectPositivePreserved context selected.root
      artifact.codeArtifact.ordered

namespace ArtifactRawSourceContext

def withSourceRun
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    (sourceRun :
      ObjectPositiveRunEquivalent ctx.context ctx.selected.root
        artifact.codeArtifact.ordered) :
    ArtifactRawSourceEquivalent rawJson selection artifact :=
  { ctx with
    sourceRun := sourceRun }

def withSourcePreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    (sourceRun :
      ObjectPositivePreserved ctx.context ctx.selected.root
        artifact.codeArtifact.ordered) :
    ArtifactRawSourcePreserved rawJson selection artifact :=
  { ctx with
    sourceRun := sourceRun }

def withSourceCodePreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (sourceRun :
      CodePositivePreserved ctx.context code
        artifact.codeArtifact.ordered) :
    ArtifactRawSourcePreserved rawJson selection artifact :=
  ctx.withSourcePreserved (sourceRun.toObjectPositive hCode)

theorem sourcePreserved_of_dispatcherSeq
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hSeq :
      ∀ rawScope,
        Raw.SourceSemantics.functionScope? code = some rawScope →
          ∀ (rawFuel : Nat) (state : State),
            ∃ orderedFuel,
              DispatcherSeqRunForward rawFuel orderedFuel
                ctx.context rawScope code artifact.codeArtifact.ordered state) :
    Nonempty (ArtifactRawSourcePreserved rawJson selection artifact) := by
  rcases ctx.code_functionScope hCode with ⟨rawScope, hScope⟩
  exact ⟨
    ctx.withSourceCodePreserved hCode
      (CodePositivePreserved.of_scope_dispatcher_seq
        hScope (hSeq rawScope hScope))⟩

end ArtifactRawSourceContext

namespace ArtifactRawSourceEquivalent

def preserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hSource :
      ArtifactRawSourceEquivalent rawJson selection artifact) :
    ArtifactRawSourcePreserved rawJson selection artifact :=
  { hSource.toArtifactRawSourceContext with
    sourceRun := hSource.sourceRun.preserved }

end ArtifactRawSourceEquivalent

theorem rawSourceEquivalentToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hSource :
      ArtifactRawSourceEquivalent rawJson selection artifact) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases hSource.sourceRun.run_eq rawFuel
      (Yul.EndToEnd.installedSourceState artifact baseSource) with
    ⟨orderedFuel, hRawOrdered⟩
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := hSource.program.object)
        (linkerSymbols := hSource.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := orderedFuel)
        (baseSource := baseSource)
        hSource.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  have hRawOrderedForward :
      Simulation.Interaction.ForwardRel
        Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
        (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
          (Yul.EndToEnd.installedSourceState artifact baseSource))
        (orderedRun (orderedFuel + 1) artifact.codeArtifact.ordered
          (Yul.EndToEnd.installedSourceState artifact baseSource)) :=
    runForward_of_eq hRawOrdered
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrderedForward hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

theorem rawSourcePreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hSource :
      ArtifactRawSourcePreserved rawJson selection artifact) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases hSource.sourceRun.forward rawFuel
      (Yul.EndToEnd.installedSourceState artifact baseSource) with
    ⟨orderedFuel, hRawOrderedForward⟩
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := hSource.program.object)
        (linkerSymbols := hSource.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := orderedFuel)
        (baseSource := baseSource)
        hSource.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrderedForward hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

theorem rawSourceCodePreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hCodeRun :
      CodePositivePreserved ctx.context code
        artifact.codeArtifact.ordered) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) :=
  rawSourcePreservedToRawBytecode
    (ctx.withSourceCodePreserved hCode hCodeRun)

/-- End-to-end finite-prefix preservation from the selected raw solc object,
specialized to the canonical installed source state used by the public backend
theorem. No frontend preservation premise or generated certificate is exposed. -/
theorem rawSourceCodeInstalledPreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases ctx.code_functionScope hCode with ⟨rawScope, hScope⟩
  let installedShared : EvmYul.SharedState .Yul :=
    Yul.FunctionsInteractionRelation.ScopedStateRel.installedSourceShared
      artifact.codeArtifact.ordered.program.contract
      (Assembly.Bytecode.ofList artifact.image.bytes) baseSource
  rcases ctx.dispatcherSeqRunForward_ok hCode hScope rawFuel
      installedShared (default : EvmYul.Yul.VarStore) with
    ⟨orderedSeqFuel, hSeq⟩
  have hBlock := blockRunForward_of_scope_seq hScope hSeq
  have hRawOrdered :
      RunForward (rawFuel + 1) (orderedSeqFuel + 1)
        ctx.context ctx.selected.root artifact.codeArtifact.ordered
        (Yul.EndToEnd.installedSourceState artifact baseSource) := by
    unfold RunForward BlockRunForward at *
    rw [rawObjectRun_some_code_succ hCode]
    simpa [Yul.EndToEnd.installedSourceState,
      Yul.FunctionsInteractionRelation.ScopedStateRel.installedSourceState,
      installedShared] using hBlock
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := ctx.program.object)
        (linkerSymbols := ctx.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := orderedSeqFuel)
        (baseSource := baseSource)
        ctx.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrdered hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

theorem rawSourceNoCodeInstalledPreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    (hCode : ctx.selected.root.code? = none) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  have hDispatcher := ctx.dispatcher_empty_of_code_none hCode
  let installedShared : EvmYul.SharedState .Yul :=
    Yul.FunctionsInteractionRelation.ScopedStateRel.installedSourceShared
      artifact.codeArtifact.ordered.program.contract
      (Assembly.Bytecode.ofList artifact.image.bytes) baseSource
  have hInstalled :
      Yul.EndToEnd.installedSourceState artifact baseSource =
        (.Ok installedShared default : State) := rfl
  have hPure (state : State) :
      (pure state : Open State) = .done (.ok state) := rfl
  have hRestrict :
      ((.Ok installedShared default : State).restrictStoreTo default) =
        (.Ok installedShared default : State) := rfl
  have hStore :
      (.Ok installedShared default : State).store = default := rfl
  have hOrderedRun :
      orderedRun 4 artifact.codeArtifact.ordered
          (Yul.EndToEnd.installedSourceState artifact baseSource) =
        pure (Yul.EndToEnd.installedSourceState artifact baseSource) := by
    unfold orderedRun
    rw [hDispatcher]
    rw [show 4 = 3 + 1 by omega]
    rw [Yul.InteractionSemantics.Exec.block_succ]
    rw [show 3 = 2 + 1 by omega]
    rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
    rw [show 2 = 1 + 1 by omega]
    rw [Yul.InteractionSemantics.Exec.block_succ]
    rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
    rw [hInstalled]
    simp only [hPure, Simulation.Interaction.bind_done_ok, hStore, hRestrict,
      Yul.InteractionSemantics.ExecSeq.nil_succ]
  have hRawRun :
      rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
          (Yul.EndToEnd.installedSourceState artifact baseSource) =
        pure (Yul.EndToEnd.installedSourceState artifact baseSource) :=
    rawObjectRun_none_code hCode
  have hRawOrdered :
      RunForward (rawFuel + 1) 4 ctx.context ctx.selected.root
        artifact.codeArtifact.ordered
        (Yul.EndToEnd.installedSourceState artifact baseSource) :=
    runForward_of_eq (hRawRun.trans hOrderedRun.symm)
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := ctx.program.object)
        (linkerSymbols := ctx.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := 3)
        (baseSource := baseSource)
        ctx.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrdered hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

/-- Public raw-frontend preservation theorem. Successful compilation alone
constructs the selected-object semantics and its preservation path to emitted
bytecode; code-bearing and empty-code objects are both covered internally. -/
theorem rawSourceInstalledPreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  cases hCode : ctx.selected.root.code? with
  | none => exact rawSourceNoCodeInstalledPreservedToRawBytecode ctx hCode
  | some code => exact rawSourceCodeInstalledPreservedToRawBytecode ctx hCode

/-- Raw Standard JSON entry theorem. The selected `irOptimizedAst` object and
its object-builtin context are constructed from successful checked compilation;
the semantic conclusion executes that raw object before composing with the
verified backend. -/
theorem optimizedRawSolcIrToRawSourceBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (context : Frontend.ObjectBuiltinContext) (structuredFuel : Nat),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Assembly.Accepted
            artifact.codeArtifact.compiled.certified.target ∧
            Simulation.Interaction.ForwardRel
              Yul.FunctionsInteractionPrimitive.Truncated
              (RawSourceBytecodePrefixDoneRel artifact)
              (rawObjectRun (rawFuel + 1) context selected.root
                (Yul.EndToEnd.installedSourceState artifact baseSource))
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList artifact.image.bytes)
                (2 *
                  ((Structured.InteractionStaticCost.blockBudget
                      artifact.codeArtifact.compiled.expressions.toStructured
                      structuredFuel
                      artifact.codeArtifact.compiled.expressions.toStructured.body +
                        1) *
                    TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                      artifact.codeArtifact.compiled.cfg))
                { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
                  pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases ArtifactRawSourceContext.nonempty_of_compile hCompile with ⟨ctx⟩
  rcases rawSourceInstalledPreservedToRawBytecode ctx with
    ⟨structuredFuel, hAccepted, hForward⟩
  exact
    ⟨ctx.json, ctx.selected, ctx.context, structuredFuel,
      ctx.parse, ctx.selected_ok, hAccepted, hForward⟩

theorem rawSourceDispatcherSeqPreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hSeq :
      ∀ rawScope,
        Raw.SourceSemantics.functionScope? code = some rawScope →
          ∀ (rawFuel : Nat) (state : State),
            ∃ orderedFuel,
              DispatcherSeqRunForward rawFuel orderedFuel
                ctx.context rawScope code artifact.codeArtifact.ordered state) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases ctx.code_functionScope hCode with ⟨rawScope, hScope⟩
  exact
    rawSourceCodePreservedToRawBytecode
      (rawFuel := rawFuel) (baseSource := baseSource)
      ctx hCode
      (CodePositivePreserved.of_scope_dispatcher_seq
        hScope (hSeq rawScope hScope))

theorem rawSourceCodeEquivalentToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hCodeRun :
      CodePositiveRunEquivalent ctx.context code
        artifact.codeArtifact.ordered) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) :=
  rawSourceCodePreservedToRawBytecode
    ctx hCode hCodeRun.preserved

end SourcePreservation
end Raw
end RawAst
end Solidity
end EvmCompiler
