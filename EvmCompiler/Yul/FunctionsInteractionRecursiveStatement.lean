import EvmCompiler.Yul.FunctionsInteractionRecursiveExpression
import EvmCompiler.Yul.FunctionsInteractionLoop
import EvmCompiler.Yul.FunctionsInteractionSelectedStatementCall
import EvmCompiler.Yul.FunctionsInteractionTargetCost

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveStatement

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation

/-- One compiler-selected statement at fixed source and target fuels.  The
target-fuel premise is internal proof accounting over the ordinary compiler
output; it is not part of the public compiler theorem. -/
def StmtForwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) : Prop :=
  ∀ {compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx},
    SolcValidation.StmtOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave stmt = true →
    (∀ name, name ∈ Stmt.names stmt → name ∈ before.used) →
    Stmt.toFunctionsListUncheckedFuel? compilerFuel before stmt =
      some (lower, after) →
    ScopedStateRel layout source target →
    TargetDomainWithin before.used target.vars →
    TargetScopeWithin before.used ctx →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx →
    FunctionsInteractionStaticCost.programBudget
        sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel →
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used
        (SolcValidation.StmtOutVars layout stmt) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec sourceFuel stmt
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target)

/-- Source-fuel prefix of the statement capability used in the mutual
whole-program induction. -/
def RecursiveStmtForward
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel targetFuel : Nat}, sourceFuel < bound →
    StmtForwardAt profile sourceProgram targetProgram sourceFuel targetFuel

/-- One compiler-selected statement list at fixed source and target fuels. -/
def ListForwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) : Prop :=
  ∀ {compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx},
    SolcValidation.StmtsOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave stmts = true →
    (∀ name, name ∈ Stmt.List.names stmts → name ∈ before.used) →
    Stmt.List.toFunctionsUncheckedFuel? compilerFuel before stmts =
      some (lower, after) →
    ScopedStateRel layout source target →
    TargetDomainWithin before.used target.vars →
    TargetScopeWithin before.used ctx →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx →
    FunctionsInteractionStaticCost.programBudget
        sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel →
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used
        (SolcValidation.StmtsOutVars layout stmts) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.execSeq sourceFuel stmts
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target)

def RecursiveListForward
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel targetFuel : Nat}, sourceFuel < bound →
    ListForwardAt profile sourceProgram targetProgram sourceFuel targetFuel

private theorem stmtOutVarsWithin
    {before after : Fresh.State} {layout : List Functions.Name}
    {stmt : AstStmt}
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hNames : ∀ name, name ∈ Stmt.names stmt → name ∈ before.used)
    (hExtends : Fresh.Extends before after) :
    ∀ name, name ∈ SolcValidation.StmtOutVars layout stmt →
      name ∈ after.used := by
  intro name hName
  cases stmt with
  | Let vars value? =>
      rcases List.mem_append.mp hName with hDeclared | hOuter
      · apply hExtends name
        apply hNames name
        cases value? <;> simp [Stmt.names, hDeclared]
      · exact hExtends name (hLayout name hOuter)
  | Block body => exact hExtends name (hLayout name hName)
  | Assign vars value => exact hExtends name (hLayout name hName)
  | ExprStmtCall value => exact hExtends name (hLayout name hName)
  | Switch value cases defaultBody =>
      exact hExtends name (hLayout name hName)
  | For value post body => exact hExtends name (hLayout name hName)
  | If value body => exact hExtends name (hLayout name hName)
  | Continue => exact hExtends name (hLayout name hName)
  | Break => exact hExtends name (hLayout name hName)
  | Leave => exact hExtends name (hLayout name hName)

private theorem layoutWithinStmtOutVars
    (layout : List Functions.Name) (stmt : AstStmt) :
    ∀ name, name ∈ layout →
      name ∈ SolcValidation.StmtOutVars layout stmt := by
  intro name hName
  cases stmt <;> simp [SolcValidation.StmtOutVars, hName]

theorem layoutWithinStmtsOutVars
    (layout : List Functions.Name) (stmts : List AstStmt) :
    ∀ name, name ∈ layout →
      name ∈ SolcValidation.StmtsOutVars layout stmts := by
  induction stmts generalizing layout with
  | nil => exact fun _name hName => hName
  | cons head tail ih =>
      intro name hName
      apply ih (SolcValidation.StmtOutVars layout head)
      exact layoutWithinStmtOutVars layout head name hName

namespace CompoundForward

/-- Ordinary compiler-selected initialized single-name declaration. Expression
evaluation is delegated to the adjacent exact-value condition theorem. -/
theorem letOne
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {name : EvmYul.Identifier}
    {expr : AstExpr} {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hCondition :
      FunctionsInteractionRecursiveExpression.ConditionForwardAt
        profile sourceProgram targetProgram fuel targetFuel layout)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave
        (.Let [name] (some expr)) = true)
    (hNames : ∀ candidate,
      candidate ∈ Stmt.names (.Let [name] (some expr)) →
        candidate ∈ before.used)
    (hNotFunctionCall : ∀ functionName functionArgs,
      expr ≠ .Call (.inr functionName) functionArgs)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Let [name] (some expr)) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ candidate, candidate ∈ layout → candidate ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used (identName name :: layout) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (fuel + 1)
        (.Let [name] (some expr)) (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨pre, lowerExpr, hLowerExpr, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_one_parts
      hNotFunctionCall hLower
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true :=
    hOkParts.2
  have hFresh : identName name ∉ layout := by
    have hBindable := hOkParts.1
    simp [SolcValidation.bindableList?, SolcValidation.nonemptyNames?,
      SolcValidation.bindingNames?, SolcValidation.namesNodup?,
      SolcValidation.namesFresh?, identNames] at hBindable
    exact hBindable.2.2
  have hExtends : Fresh.Extends before after :=
    Expr.lower1Unchecked?_stateExtends hLowerExpr
  have hNameBefore : identName name ∈ before.used := by
    apply hNames (identName name)
    simp [Stmt.names, identNames, identName]
  have hNameAfter : identName name ∈ after.used :=
    hExtends _ hNameBefore
  have hProgramMono :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
        FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) := by
    unfold FunctionsInteractionStaticCost.programBudget
    exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
  have hPreCost := FunctionsInteractionTargetCost.length_le_list pre
  have hConditionBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          pre.length + 2 ≤ targetFuel := by
    rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt] at hTargetFuel
    omega
  have hPrepared := hCondition hExprOk hLowerExpr hConditionBudget
    hLayout hRel hDomain hTargetScope
  simpa using
    (FunctionsInteractionPreparedStatement.letOneOfCondition
      hFresh hNameAfter hRel hControl (by
        rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
        simp [FunctionsInteractionTargetCost.list,
          FunctionsInteractionTargetCost.stmt] at hTargetFuel
        omega) hPrepared)

/-- Ordinary compiler-selected initialized single-name assignment. Direct
lowering reuses the exact-value condition interface; bounded primitive lowering
factors at its compiler-generated argument prelude. -/
theorem assignOne
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {name : EvmYul.Identifier}
    {expr : AstExpr} {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hCondition :
      FunctionsInteractionRecursiveExpression.ConditionForwardAt
        profile sourceProgram targetProgram fuel targetFuel layout)
    (hHeads :
      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
        profile sourceProgram (fuel - 1) targetFuel
        (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave
        (.Assign [name] expr) = true)
    (hNames : ∀ candidate,
      candidate ∈ Stmt.names (.Assign [name] expr) →
        candidate ∈ before.used)
    (hNotFunctionCall : ∀ functionName functionArgs,
      expr ≠ .Call (.inr functionName) functionArgs)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Assign [name] expr) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ candidate, candidate ∈ layout → candidate ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (fuel + 1)
        (.Assign [name] expr) (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨pre, lowerExpr, hLowerExpr, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_one_parts
      hNotFunctionCall hLower
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hName : identName name ∈ layout := by
    have hAssignable := hOkParts.1
    simp [SolcValidation.assignableList?, SolcValidation.nonemptyNames?,
      SolcValidation.namesNodup?, SolcValidation.namesIn?, identNames]
      at hAssignable
    exact hAssignable
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true :=
    hOkParts.2
  have hExtends : Fresh.Extends before after :=
    Expr.lower1Unchecked?_stateExtends hLowerExpr
  have hNameBefore : identName name ∈ before.used := hLayout _ hName
  have hNameAfter : identName name ∈ after.used := hExtends _ hNameBefore
  have hProgramFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
        FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) := by
    unfold FunctionsInteractionStaticCost.programBudget
    exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
  have hTailFuel : pre.length + 1 < targetFuel := by
    rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt] at hTargetFuel
    have hPreCost := FunctionsInteractionTargetCost.length_le_list pre
    omega
  have hConditionBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          pre.length + 2 ≤ targetFuel := by
    rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt] at hTargetFuel
    have hPreCost := FunctionsInteractionTargetCost.length_le_list pre
    omega
  cases fuel with
  | zero =>
      rw [Yul.InteractionSemantics.Exec.assign_one_succ
        0 name expr (some sourceProgram.contract) source
        (hRel.assignmentCheck hName)]
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.evalValues,
        Yul.Source.Canonical.evalValues,
        Yul.Source.Effectful.evalValues,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.Source.Effectful.Control.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ControlDoneRel after.used layout sourceScopes
            canBreak canContinue canLeave)
          (right := Functions.InteractionSemantics.Block.openRun
            targetProgram.toFunctions ctx targetFuel
            { stmts := pre ++ [.assign (identName name) lowerExpr] } target)
          hTruncated)
  | succ argsFuel =>
      cases expr with
      | Lit value =>
          obtain ⟨rfl, rfl, _hDirect⟩ :=
            Expr.lower1Unchecked?_deferred_parts
              (by simp [Expr.deferredBoundArgSafe?]) hLowerExpr
          have hPrepared := hCondition hExprOk hLowerExpr
            hConditionBudget hLayout hRel hDomain hTargetScope
          simpa using
            (FunctionsInteractionPreparedStatement.assignOneOfConditionDirect
              hName hNameAfter hRel hControl (by omega) hPrepared)
      | Var varName =>
          obtain ⟨rfl, rfl, _hDirect⟩ :=
            Expr.lower1Unchecked?_deferred_parts
              (by simp [Expr.deferredBoundArgSafe?]) hLowerExpr
          have hPrepared := hCondition hExprOk hLowerExpr
            hConditionBudget hLayout hRel hDomain hTargetScope
          simpa using
            (FunctionsInteractionPreparedStatement.assignOneOfConditionDirect
              hName hNameAfter hRel hControl (by omega) hPrepared)
      | Call callee args =>
          cases callee with
          | inr functionName => exact (hNotFunctionCall functionName args rfl).elim
          | inl prim =>
              have hPrimitiveLower :
                  Expr.UncheckedPrimitiveLowering 1 before prim args
                    pre lowerExpr after :=
                Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
                  (by simpa [Expr.lower1Unchecked?] using hLowerExpr)
              cases hPrimitiveLower with
              | direct hDirect hOp hArgs hSeq hOutputs =>
                  have hPrepared := hCondition hExprOk hLowerExpr
                    hConditionBudget hLayout hRel hDomain
                    hTargetScope
                  simpa using
                    (FunctionsInteractionPreparedStatement.assignOneOfConditionDirect
                      hName hNameAfter hRel hControl (by omega) hPrepared)
              | bound hBound hOp hArgs hSeq hOutputs =>
                  have hArgsOk :=
                    SolcValidation.exprsOk_of_exprOk_primitive hExprOk
                  have hProgramArgs :
                      FunctionsInteractionStaticCost.programBudget
                          sourceProgram argsFuel ≤
                        FunctionsInteractionStaticCost.programBudget
                          sourceProgram (argsFuel + 1 + 1) := by
                    unfold FunctionsInteractionStaticCost.programBudget
                    exact FunctionsInteractionFuel.executionBudgetFor_mono
                      _ _ (by omega)
                  have hArgsBudget :
                      FunctionsInteractionStaticCost.programBudget
                            sourceProgram argsFuel +
                          pre.length + 2 ≤ targetFuel := by
                    rw [FunctionsInteractionTargetCost.list_append]
                      at hTargetFuel
                    simp [FunctionsInteractionTargetCost.list,
                      FunctionsInteractionTargetCost.stmt] at hTargetFuel
                    have hPreCost :=
                      FunctionsInteractionTargetCost.length_le_list pre
                    omega
                  have hPrepared :=
                    FunctionsInteractionPreparedArgs.ofUncheckedLowering
                      hArgsOk hArgs hHeads hArgsBudget hRel hDomain
                      hTargetScope hLayout (by omega)
                  simpa using
                    (FunctionsInteractionPreparedStatement.assignOneOfPreparedPrimitive
                      FunctionsInteractionClosedPrimitive.compilerSelected
                      hName hNameAfter hRel hControl hTailFuel
                      hOp hSeq hOutputs hPrepared)

/-- Ordinary compiler-selected nonterminal primitive expression statement.
Direct and generated-argument lowering are discharged by the prepared primitive
owner; this wrapper contributes only compiler decomposition and recursive budget
selection. -/
theorem exprPrimitive
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hNonterminal : Prim.terminal? prim = none)
    (hHeads : ∀ argsFuel, argsFuel < fuel →
      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
        profile sourceProgram argsFuel targetFuel
        (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave
        (.ExprStmtCall (.Call (.inl prim) args)) = true)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.ExprStmtCall (.Call (.inl prim) args)) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ candidate, candidate ∈ layout → candidate ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec fuel
        (.ExprStmtCall (.Call (.inl prim) args))
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨pre, lowerExpr, hLowerExpr, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_primitive_parts
      hNonterminal hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inl prim) args) = true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hPrimitiveLower :
      Expr.UncheckedPrimitiveLowering 0 before prim args
        pre lowerExpr after :=
    Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
      (by simpa [Expr.lower0Unchecked?] using hLowerExpr)
  have hProgramBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          pre.length + 2 ≤ targetFuel := by
    rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt] at hTargetFuel
    have hPreCost := FunctionsInteractionTargetCost.length_le_list pre
    omega
  exact FunctionsInteractionPreparedPrimitive.zeroOfLowering
    FunctionsInteractionClosedPrimitive.compilerSelected
    hPrimitiveLower hExprOk
    (fun argsFuel hFuelEq => hHeads argsFuel (by omega))
    hProgramBudget hRel hDomain hTargetScope hLayout hControl

/-- Ordinary compiler-selected terminal primitive statement, including its
generated argument prelude and control-indexed terminal result. -/
theorem terminalPrimitive
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hTerminal : Prim.terminal? prim = some kind)
    (hHeads : ∀ argsFuel, argsFuel < fuel →
      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
        profile sourceProgram argsFuel targetFuel
        (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave
        (.ExprStmtCall (.Call (.inl prim) args)) = true)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.ExprStmtCall (.Call (.inl prim) args)) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ candidate, candidate ∈ layout → candidate ∈ before.used)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec fuel
        (.ExprStmtCall (.Call (.inl prim) args))
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨pre, lowerArgs, seq, hArgsLowering, hSeq, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_terminal_parts
      hTerminal hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inl prim) args) = true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hArgsOk := SolcValidation.exprsOk_of_exprOk_primitive hExprOk
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      exact Simulation.Interaction.ForwardRel.truncated hTruncated
  | succ argsFuel =>
      have hProgramLe :
          FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel ≤
            FunctionsInteractionStaticCost.programBudget sourceProgram
              (argsFuel + 1) := by
        unfold FunctionsInteractionStaticCost.programBudget
        exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
      have hProgramBudget :
          FunctionsInteractionStaticCost.programBudget sourceProgram argsFuel +
              pre.length + 2 ≤ targetFuel := by
        rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
        simp [FunctionsInteractionTargetCost.list,
          FunctionsInteractionTargetCost.stmt] at hTargetFuel
        have hPreCost := FunctionsInteractionTargetCost.length_le_list pre
        omega
      exact FunctionsInteractionPreparedPrimitive.terminalOfLowering
        hTerminal
        (Expr.List.uncheckedBoundLowering_of_lowerBound1Unchecked?
          hArgsLowering)
        hSeq hArgsOk
        (hHeads argsFuel (by omega)) hProgramBudget
        hRel hDomain hTargetScope hLayout

/-- Compose a checked prepared condition with the adjacent lexical-body
theorem. The target equation is the ordinary compiler output factored by
`PreparedCondition.run_if`; no condition evaluator is reproduced here. -/
theorem ifFromCondition
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {conditionFuel targetFuel : Nat}
    {layout conditionUsed finalUsed : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {cond : AstExpr} {body : List AstStmt}
    {pre : List Functions.Stmt} {lowerCond : Locals.Expr 1}
    {lowerBody : Functions.Block}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hUsedSubset : ∀ name, name ∈ conditionUsed → name ∈ finalUsed)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedCondition.DoneRel
          layout conditionUsed ctx)
        (Yul.InteractionSemantics.evalValues conditionFuel cond
          (some sourceProgram.contract) source)
        (FunctionsInteractionPreparedCondition.run targetProgram.toFunctions
          ctx targetFuel pre lowerCond target))
    (hBody :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State}
        {ctxAfter : Functions.Source.Ctx},
        ScopedStateRel layout sourceAfter targetAfter →
        TargetDomainWithin conditionUsed targetAfter.vars →
        ControlContextRel sourceScopes layout
            canBreak canContinue canLeave ctxAfter →
        TargetScopeWithin conditionUsed ctxAfter →
        Simulation.Interaction.ForwardRel Truncated
          (ControlDoneRel finalUsed layout sourceScopes
            canBreak canContinue canLeave)
          (Yul.InteractionSemantics.exec conditionFuel (.Block body)
            (some sourceProgram.contract) sourceAfter)
          (Functions.InteractionSemantics.Stmt.openRun
            targetProgram.toFunctions ctxAfter
            (targetFuel - pre.length - 2) (.block lowerBody) targetAfter)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel finalUsed layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (conditionFuel + 1) (.If cond body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel
        { stmts := pre ++ [.if_ lowerCond lowerBody] } target) := by
  rw [Yul.InteractionSemantics.Exec.if_succ]
  rw [Yul.InteractionSemantics.eval_eq_bind,
    Simulation.Interaction.bind_assoc]
  rw [FunctionsInteractionPreparedCondition.run_if
    targetProgram.toFunctions ctx targetFuel pre lowerCond lowerBody target
    hTargetFuel]
  apply Simulation.Interaction.ForwardRel.bind_custom hCondition
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.revert hState))
  | @regular sourceAfter values targetAfter truth ctxAfter value
      hValues hTruth hScoped hDomain hScope hSameControl hTargetScopeAfter =>
      have hControlAfter : ControlContextRel sourceScopes layout
          canBreak canContinue canLeave ctxAfter := by
        apply ControlContextRel.transport hControl
        · exact fun _name hName => hName
        · exact hSameControl
        · intro name hName
          exact hScope name (hControl.scope name hName)
      subst values
      simp only [List.head!_cons, Simulation.Interaction.bind_done_ok]
      by_cases hNonzero : value ≠ EvmYul.UInt256.ofNat 0
      · have hTruthTrue : truth = true := by
          exact
            FunctionsInteractionPreparedCondition.DoneRel.truth_eq_true_of_ne
              hTruth hNonzero
        have hBne :
            (value != EvmYul.UInt256.ofNat 0) = true :=
          hTruth.symm.trans hTruthTrue
        subst truth
        simp only [Simulation.Interaction.bind_done_ok, pure_bind,
          hNonzero, hBne, ↓reduceIte]
        rw [show
          (pure (sourceAfter, value) :
              Yul.InteractionSemantics.Open
                (Yul.InteractionSemantics.State × Word)) =
            Simulation.Interaction.pure (sourceAfter, value) by rfl]
        unfold Simulation.Interaction.pure
        rw [Simulation.Interaction.bind_done_ok]
        rw [if_pos hNonzero]
        change
          Simulation.Interaction.ForwardRel Truncated
            (ControlDoneRel finalUsed layout sourceScopes
              canBreak canContinue canLeave)
            (Yul.InteractionSemantics.exec conditionFuel (.Block body)
              (some sourceProgram.contract) sourceAfter)
            (Functions.InteractionSemantics.Stmt.openRun
              targetProgram.toFunctions ctxAfter
              (targetFuel - pre.length - 2) (.block lowerBody) targetAfter)
        exact hBody hScoped hDomain hControlAfter hTargetScopeAfter
      · have hZero : value = EvmYul.UInt256.ofNat 0 := by
          simpa using hNonzero
        subst value
        have hTruthFalse : truth = false := by
          simpa using hTruth
        subst truth
        simp only [ne_eq, not_true_eq_false, ↓reduceIte,
          Bool.false_eq_true, Simulation.Interaction.bind_done_ok]
        exact Simulation.Interaction.ForwardRel.done
          (.regular hScoped (hDomain.mono hUsedSubset) hControlAfter
            (hTargetScopeAfter.mono hUsedSubset))

/-- Compose a checked prepared scrutinee with one adjacent selected-body
capability. Selection remains owned by the ordinary source and target
semantics; the caller only proves that the two selected branches are related. -/
theorem switchFromCondition
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {conditionFuel targetFuel : Nat}
    {layout conditionUsed finalUsed : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {cond : AstExpr} {cases : List (Word × List AstStmt)}
    {defaultBody : List AstStmt}
    {pre : List Functions.Stmt} {lowerCond : Locals.Expr 1}
    {lowerCases : List (Word × Functions.Block)}
    {lowerDefault : Option Functions.Block}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedCondition.DoneRel
          layout conditionUsed ctx)
        (Yul.InteractionSemantics.evalValues conditionFuel cond
          (some sourceProgram.contract) source)
        (FunctionsInteractionPreparedCondition.run targetProgram.toFunctions
          ctx targetFuel pre lowerCond target))
    (hSelected :
      ∀ (value : Word)
        {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State}
        {ctxAfter : Functions.Source.Ctx},
        ScopedStateRel layout sourceAfter targetAfter →
        TargetDomainWithin conditionUsed targetAfter.vars →
        ControlContextRel sourceScopes layout
            canBreak canContinue canLeave ctxAfter →
        TargetScopeWithin conditionUsed ctxAfter →
        Simulation.Interaction.ForwardRel Truncated
          (ControlDoneRel finalUsed layout sourceScopes
            canBreak canContinue canLeave)
          (Yul.InteractionSemantics.exec conditionFuel
            (.Block
              (EvmYul.Yul.selectSwitchCase value defaultBody cases))
            (some sourceProgram.contract) sourceAfter)
          (match Functions.Source.Switch.select
              value lowerCases lowerDefault with
            | some body =>
                Functions.InteractionSemantics.Stmt.openRun
                  targetProgram.toFunctions ctxAfter
                  (targetFuel - pre.length - 2) (.block body) targetAfter
            | none =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular targetAfter,
                    ctxAfter))) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel finalUsed layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (conditionFuel + 1)
        (.Switch cond cases defaultBody)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel
        { stmts := pre ++
            [.switch lowerCond lowerCases lowerDefault] } target) := by
  rw [Yul.InteractionSemantics.Exec.switch_succ]
  rw [Yul.InteractionSemantics.eval_eq_bind,
    Simulation.Interaction.bind_assoc]
  rw [FunctionsInteractionPreparedCondition.run_switch
    targetProgram.toFunctions ctx targetFuel pre lowerCond lowerCases
    lowerDefault target hTargetFuel]
  apply Simulation.Interaction.ForwardRel.bind_custom hCondition
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.revert hState))
  | @regular sourceAfter values targetAfter truth ctxAfter value
      hValues _hTruth hScoped hDomain hScope hSameControl hTargetScopeAfter =>
      have hControlAfter : ControlContextRel sourceScopes layout
          canBreak canContinue canLeave ctxAfter := by
        apply ControlContextRel.transport hControl
        · exact fun _name hName => hName
        · exact hSameControl
        · intro name hName
          exact hScope name (hControl.scope name hName)
      subst values
      simp only [List.head!_cons, Simulation.Interaction.bind_done_ok]
      rw [show
        (pure (sourceAfter, value) :
            Yul.InteractionSemantics.Open
              (Yul.InteractionSemantics.State × Word)) =
          Simulation.Interaction.pure (sourceAfter, value) by rfl]
      unfold Simulation.Interaction.pure
      rw [Simulation.Interaction.bind_done_ok]
      exact hSelected value hScoped hDomain hControlAfter hTargetScopeAfter

/-- Compiler-selected lexical block from the adjacent recursive list theorem.
The outer source/target cleanup is owned by `ControlDoneRel.block`; this wrapper
only decomposes the ordinary Yul compiler and discharges private target fuel. -/
theorem block
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hLists : ∀ recursiveTargetFuel,
      ListForwardAt profile sourceProgram targetProgram
        fuel recursiveTargetFuel)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave (.Block body) = true)
    (hNames : ∀ name, name ∈ Stmt.names (.Block body) →
      name ∈ before.used)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Block body) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (fuel + 1) (.Block body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨previous, lowerBody, rfl, hLowerBody, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_block_parts hLower
  obtain ⟨bodyCompilerFuel, lowerBodyStmts, rfl,
      hLowerList, rfl⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  have hBodyOk : SolcValidation.StmtsOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave body = true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hBodyNames : ∀ name, name ∈ Stmt.List.names body →
      name ∈ before.used := by
    simpa [Stmt.names] using hNames
  have hProgramMono :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
        FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) := by
    unfold FunctionsInteractionStaticCost.programBudget
    exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
  have hTargetPositive : 2 ≤ targetFuel := by
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt,
      FunctionsInteractionTargetCost.block] at hTargetFuel
    omega
  have hBodyFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          FunctionsInteractionTargetCost.list lowerBodyStmts + 1 <
        targetFuel - 1 := by
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt,
      FunctionsInteractionTargetCost.block] at hTargetFuel
    omega
  have hBody := hLists (targetFuel - 1)
    hBodyOk hBodyNames hLowerList hRel hDomain hTargetScope hLayout hControl
    hBodyFuel
  have hBodyExtends : Fresh.Extends before after :=
    Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerList
  have hBlock := FunctionsInteractionStatement.ControlDoneRel.block
    hRel hControl (hTargetScope.mono hBodyExtends)
    (layoutWithinStmtsOutVars layout body) hBody
  have hStmtFuelEq : targetFuel - 2 + 1 = targetFuel - 1 := by omega
  have hBlock' :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel after.used layout sourceScopes
          canBreak canContinue canLeave)
        (Yul.InteractionSemantics.exec (fuel + 1) (.Block body)
          (some sourceProgram.contract) source)
        (Functions.InteractionSemantics.Stmt.openRun
          targetProgram.toFunctions ctx (targetFuel - 2 + 1)
          (.block { stmts := lowerBodyStmts }) target) := by
    rw [hStmtFuelEq]
    exact hBlock
  have hFuelEq : targetFuel - 2 + 2 = targetFuel := by omega
  have hSingleton :=
    FunctionsInteractionStatement.ControlDoneRel.singleton
      (targetFuel := targetFuel - 2) hBlock'
  simpa [hFuelEq, SolcValidation.StmtOutVars] using hSingleton

/-- Ordinary compiler-selected `if`, assembled only from the prepared
condition capability and the strictly smaller recursive lexical body. -/
theorem ifThen
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {cond : AstExpr} {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hCondition :
      FunctionsInteractionRecursiveExpression.ConditionForwardAt
        profile sourceProgram targetProgram fuel targetFuel layout)
    (hLists : RecursiveListForward
      profile sourceProgram targetProgram fuel)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave (.If cond body) = true)
    (hNames : ∀ name, name ∈ Stmt.names (.If cond body) →
      name ∈ before.used)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.If cond body) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (fuel + 1) (.If cond body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨previous, preCond, lowerCond, middle, lowerBody,
      rfl, hLowerCond, hLowerBody, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_if_parts hLower
  obtain ⟨bodyCompilerFuel, lowerBodyStmts, rfl,
      hLowerBodyList, rfl⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  have hOkParts :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 cond = true ∧
        SolcValidation.StmtsOk? profile sourceProgram.contract functionNames
          layout canBreak canContinue canLeave body = true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hCondExtends : Fresh.Extends before middle :=
    Expr.lower1Unchecked?_stateExtends hLowerCond
  have hBodyExtends : Fresh.Extends middle after :=
    Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerBodyList
  have hBodyNames : ∀ name, name ∈ Stmt.List.names body →
      name ∈ middle.used := by
    intro name hName
    apply hCondExtends name
    exact hNames name (by simp [Stmt.names, hName])
  have hMiddleLayout : ∀ name, name ∈ layout → name ∈ middle.used := by
    intro name hName
    exact hCondExtends name (hLayout name hName)
  have hProgramCond :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
        FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) := by
    unfold FunctionsInteractionStaticCost.programBudget
    exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
  have hPreLength := FunctionsInteractionTargetCost.length_le_list preCond
  have hCost := hTargetFuel
  rw [FunctionsInteractionTargetCost.list_append] at hCost
  simp [FunctionsInteractionTargetCost.list,
    FunctionsInteractionTargetCost.stmt,
    FunctionsInteractionTargetCost.block] at hCost
  have hCondBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          preCond.length + 2 ≤ targetFuel := by
    omega
  have hTargetSplit :
      targetFuel =
        (targetFuel - preCond.length - 2) + preCond.length + 2 := by
    omega
  have hPrepared := hCondition (ctx := ctx) hOkParts.1 hLowerCond hCondBudget
    hLayout hRel hDomain hTargetScope
  apply ifFromCondition
    (conditionUsed := middle.used) (finalUsed := after.used)
    (lowerBody := { stmts := lowerBodyStmts })
    (hTargetFuel := by omega) hBodyExtends hControl hPrepared
  intro sourceAfter targetAfter ctxAfter hScopedAfter hDomainAfter hControlAfter
    hTargetScopeAfter
  cases fuel with
  | zero =>
      rw [Yul.InteractionSemantics.Exec.zero]
      exact Simulation.Interaction.ForwardRel.truncated
        (right := Functions.InteractionSemantics.Stmt.openRun
          targetProgram.toFunctions ctxAfter
          (targetFuel - preCond.length - 2)
          (.block { stmts := lowerBodyStmts }) targetAfter)
        (by trivial)
  | succ bodyFuel =>
      have hProgramBody :
          FunctionsInteractionStaticCost.programBudget sourceProgram bodyFuel ≤
            FunctionsInteractionStaticCost.programBudget sourceProgram
              (bodyFuel + 1 + 1) := by
        unfold FunctionsInteractionStaticCost.programBudget
        exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
      have hBodyBudget :
          FunctionsInteractionStaticCost.programBudget sourceProgram bodyFuel +
              FunctionsInteractionTargetCost.list lowerBodyStmts + 1 <
            targetFuel - preCond.length - 2 := by
        omega
      have hBodyList := hLists
        (sourceFuel := bodyFuel)
        (targetFuel := targetFuel - preCond.length - 2) (by omega)
        hOkParts.2 hBodyNames hLowerBodyList hScopedAfter hDomainAfter
        hTargetScopeAfter hMiddleLayout hControlAfter hBodyBudget
      exact FunctionsInteractionStatement.ControlDoneRel.block
        hScopedAfter hControlAfter (hTargetScopeAfter.mono hBodyExtends)
        (layoutWithinStmtsOutVars layout body) hBodyList

/-- Ordinary compiler-selected switch. The prepared scrutinee exposes its
exact value, the compiler-owned selection artifact identifies the same source
and target branch, and only that strictly smaller branch uses recursion. -/
theorem switch
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {cond : AstExpr}
    {cases : List (Word × List AstStmt)} {defaultBody : List AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hCondition :
      FunctionsInteractionRecursiveExpression.ConditionForwardAt
        profile sourceProgram targetProgram fuel targetFuel layout)
    (hLists : RecursiveListForward
      profile sourceProgram targetProgram fuel)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave
        (.Switch cond cases defaultBody) = true)
    (hNames : ∀ name,
      name ∈ Stmt.names (.Switch cond cases defaultBody) →
        name ∈ before.used)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Switch cond cases defaultBody) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (fuel + 1)
        (.Switch cond cases defaultBody)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨previous, preCond, lowerCond, afterCond,
      lowerCases, afterCases, lowerDefault, rfl,
      hLowerCond, hLowerCases, hLowerDefault, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_switch_parts hLower
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hCondExtends : Fresh.Extends before afterCond :=
    Expr.lower1Unchecked?_stateExtends hLowerCond
  have hProgramCond :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
        FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) := by
    unfold FunctionsInteractionStaticCost.programBudget
    exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
  have hPreLength := FunctionsInteractionTargetCost.length_le_list preCond
  have hCost := hTargetFuel
  rw [FunctionsInteractionTargetCost.list_append] at hCost
  simp [FunctionsInteractionTargetCost.list,
    FunctionsInteractionTargetCost.stmt,
    FunctionsInteractionTargetCost.block] at hCost
  have hCondBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          preCond.length + 2 ≤ targetFuel := by
    omega
  have hPrepared := hCondition (ctx := ctx) hOkParts.1 hLowerCond hCondBudget
    hLayout hRel hDomain hTargetScope
  apply switchFromCondition
    (conditionUsed := afterCond.used) (finalUsed := after.used)
    (hTargetFuel := by omega) hControl hPrepared
  intro value sourceAfter targetAfter ctxAfter
    hScopedAfter hDomainAfter hControlAfter hTargetScopeAfter
  have hSelection :=
    Stmt.SwitchSelectionLowering.of_compilers
      (value := value) hLowerCases hLowerDefault
  cases hSelection with
  | none hSourceSelection hTargetSelection hFresh =>
      rw [hSourceSelection, hTargetSelection]
      cases fuel with
      | zero =>
          rw [Yul.InteractionSemantics.Exec.zero]
          exact Simulation.Interaction.ForwardRel.truncated (by trivial)
      | succ previous =>
          rw [Yul.InteractionSemantics.Exec.block_succ]
          cases previous with
          | zero =>
              rw [Yul.InteractionSemantics.ExecSeq.zero]
              exact Simulation.Interaction.ForwardRel.truncated (by trivial)
          | succ bodyFuel =>
              rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
              simp only [Simulation.Interaction.bind_done_ok]
              rcases hScopedAfter.state with
                ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
              subst sourceAfter
              have hRestricted :
                  ScopedStateRel layout
                    ((EvmYul.Yul.State.Ok sourceShared sourceVars).restrictStoreTo
                      sourceVars)
                    targetAfter := by
                simpa [EvmYul.Yul.State.restrictStoreTo,
                  VarStoreRestriction.restrict_self] using hScopedAfter
              exact Simulation.Interaction.ForwardRel.done
                (.regular hRestricted (hDomainAfter.mono hFresh)
                  hControlAfter (hTargetScopeAfter.mono hFresh))
  | @some sourceBody lowerBody bodyCompilerFuel bodyBefore bodyAfter
      hSourceSelection hTargetSelection hLowerBody hBefore hAfter =>
      rw [hSourceSelection, hTargetSelection]
      cases fuel with
      | zero =>
          rw [Yul.InteractionSemantics.Exec.zero]
          exact Simulation.Interaction.ForwardRel.truncated (by trivial)
      | succ bodyFuel =>
          obtain ⟨listCompilerFuel, lowerBodyStmts, rfl,
              hLowerBodyList, rfl⟩ :=
            Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
          have hSelectedOk :
              SolcValidation.StmtsOk? profile sourceProgram.contract
                  functionNames layout canBreak canContinue canLeave
                  sourceBody = true := by
            rw [← hSourceSelection]
            exact Stmt.stmtsOk_selectSwitchCase
              hOkParts.2.2.1 hOkParts.2.2.2
          have hSelectedNamesBefore :
              ∀ name, name ∈ Stmt.List.names sourceBody →
                name ∈ before.used := by
            intro name hName
            apply hNames name
            have hCanonical :
                name ∈ Stmt.List.names
                  (EvmYul.Yul.selectSwitchCase
                    value defaultBody cases) := by
              rw [hSourceSelection]
              exact hName
            simpa [Stmt.names] using
              List.mem_append_right (Expr.names cond)
                (Stmt.selectedSwitchNames name hCanonical)
          have hSelectedFresh : Fresh.Extends before bodyBefore :=
            Fresh.Extends.trans hCondExtends hBefore
          have hSelectedNames :
              ∀ name, name ∈ Stmt.List.names sourceBody →
                name ∈ bodyBefore.used := by
            intro name hName
            exact hSelectedFresh name (hSelectedNamesBefore name hName)
          have hSelectedLayout :
              ∀ name, name ∈ layout → name ∈ bodyBefore.used := by
            intro name hName
            exact hSelectedFresh name (hLayout name hName)
          have hProgramBody :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram bodyFuel ≤
                FunctionsInteractionStaticCost.programBudget
                  sourceProgram (bodyFuel + 1 + 1) := by
            unfold FunctionsInteractionStaticCost.programBudget
            exact FunctionsInteractionFuel.executionBudgetFor_mono
              _ _ (by omega)
          have hSelectedTargetCost :=
            FunctionsInteractionTargetCost.block_le_switchBranches_of_select_eq_some
              hTargetSelection
          have hSelectedListCost :
              FunctionsInteractionTargetCost.list lowerBodyStmts ≤
                FunctionsInteractionTargetCost.caseList lowerCases +
                  FunctionsInteractionTargetCost.optionBlock lowerDefault := by
            simpa [FunctionsInteractionTargetCost.block] using
              hSelectedTargetCost
          have hBodyBudget :
              FunctionsInteractionStaticCost.programBudget
                    sourceProgram bodyFuel +
                  FunctionsInteractionTargetCost.list lowerBodyStmts + 1 <
                targetFuel - preCond.length - 2 := by
            omega
          have hBodyList := hLists
            (sourceFuel := bodyFuel)
            (targetFuel := targetFuel - preCond.length - 2) (by omega)
            hSelectedOk hSelectedNames hLowerBodyList hScopedAfter
            (hDomainAfter.mono hBefore) (hTargetScopeAfter.mono hBefore)
            hSelectedLayout hControlAfter hBodyBudget
          have hSelectedScope := hTargetScopeAfter.mono hBefore
          have hBodyExtends : Fresh.Extends bodyBefore bodyAfter :=
            Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerBodyList
          have hBlock := FunctionsInteractionStatement.ControlDoneRel.block
            hScopedAfter hControlAfter (hSelectedScope.mono hBodyExtends)
            (layoutWithinStmtsOutVars layout sourceBody) hBodyList
          exact Simulation.Interaction.ForwardRel.mono hBlock
            (fun _sourceDone _targetDone hDone => hDone.monoUsed hAfter)

/-- Ordinary compiler-selected `for`, assembled from the prepared condition,
recursive body/post lists, and the generic adjacent loop kernel. -/
theorem forLoop
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {cond : AstExpr}
    {post body : List AstStmt} {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hConditions :
      ∀ {childFuel childTargetFuel : Nat}, childFuel < sourceFuel →
        FunctionsInteractionRecursiveExpression.ConditionForwardAt
          profile sourceProgram targetProgram childFuel childTargetFuel layout)
    (hLists : RecursiveListForward
      profile sourceProgram targetProgram sourceFuel)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave
        (.For cond post body) = true)
    (hNames : ∀ name, name ∈ Stmt.names (.For cond post body) →
      name ∈ before.used)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.For cond post body) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec sourceFuel (.For cond post body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨compilerPrevious, preCond, lowerCond, afterCond,
      lowerPost, afterPost, lowerBody, _hCompilerFuel,
      hLowerCond, hLowerPost, hLowerBody, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_for_parts hLower
  obtain ⟨postCompilerFuel, lowerPostStmts, _hPostCompilerFuel,
      hLowerPostList, rfl⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerPost
  obtain ⟨bodyCompilerFuel, lowerBodyStmts, _hBodyCompilerFuel,
      hLowerBodyList, rfl⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  have hOkParts :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 1 cond = true ∧
        SolcValidation.StmtsOk? profile sourceProgram.contract functionNames
            layout false false canLeave post = true ∧
        SolcValidation.StmtsOk? profile sourceProgram.contract functionNames
            layout true true canLeave body = true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hCondExtends : Fresh.Extends before afterCond :=
    Expr.lower1Unchecked?_stateExtends hLowerCond
  have hPostExtends : Fresh.Extends afterCond afterPost :=
    Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerPostList
  have hBodyExtends : Fresh.Extends afterPost after :=
    Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerBodyList
  have hFinalExtends : Fresh.Extends before after :=
    Fresh.Extends.trans hCondExtends
      (Fresh.Extends.trans hPostExtends hBodyExtends)
  have hCondNames : ∀ name, name ∈ Expr.names cond → name ∈ before.used := by
    intro name hName
    exact hNames name (by simp [Stmt.names, hName])
  have hPostNames : ∀ name, name ∈ Stmt.List.names post →
      name ∈ afterCond.used := by
    intro name hName
    apply hCondExtends name
    exact hNames name (by simp [Stmt.names, hName])
  have hBodyNames : ∀ name, name ∈ Stmt.List.names body →
      name ∈ afterPost.used := by
    intro name hName
    apply hPostExtends name
    apply hCondExtends name
    exact hNames name (by simp [Stmt.names, hName])
  have hCondLayout : ∀ name, name ∈ layout → name ∈ afterCond.used := by
    intro name hName
    exact hCondExtends name (hLayout name hName)
  have hPostLayout : ∀ name, name ∈ layout → name ∈ afterPost.used := by
    intro name hName
    exact hPostExtends name (hCondLayout name hName)
  let lowerGuarded : Functions.Block :=
    { stmts :=
        preCond ++
          .if_
            (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
            { stmts := [.brk] } ::
          lowerBodyStmts }
  let lowerLoop : Functions.Stmt :=
    .for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
      { stmts := lowerPostStmts } lowerGuarded
  have hKernel :
      ∀ (iterationFuel kernelTargetFuel : Nat)
        {sourceEntry : Yul.InteractionSemantics.State}
        {targetEntry : Functions.InteractionSemantics.State},
        iterationFuel ≤ sourceFuel →
        FunctionsInteractionStaticCost.programBudget sourceProgram
              iterationFuel +
            FunctionsInteractionTargetCost.stmt lowerLoop < kernelTargetFuel →
        ScopedStateRel layout sourceEntry targetEntry →
        TargetDomainWithin before.used targetEntry.vars →
        Simulation.Interaction.ForwardRel Truncated
          (FunctionsInteractionLoop.KernelDoneRel
            before.used layout sourceScopes canLeave)
          (Yul.InteractionSemantics.exec iterationFuel
            (.For cond post body) (some sourceProgram.contract) sourceEntry)
          (Functions.InteractionSemantics.Stmt.openRunForLoop
            targetProgram.toFunctions ctx.withoutLoopControl
            (.lit (EvmYul.UInt256.ofNat 1)) ctx.withoutLoopControl
            { stmts := lowerPostStmts }
            (ctx.withLoopControl ctx.scope ctx.scope) lowerGuarded
            kernelTargetFuel targetEntry) := by
    intro iterationFuel
    induction iterationFuel using Nat.strong_induction_on with
    | h iterationFuel ih =>
        intro kernelTargetFuel sourceEntry targetEntry hWithin
          hKernelFuel hScoped hEntryDomain
        cases iterationFuel with
        | zero =>
            rw [Yul.InteractionSemantics.Exec.zero]
            exact Simulation.Interaction.ForwardRel.truncated (by trivial)
        | succ previous =>
            rw [Yul.InteractionSemantics.Exec.for_succ]
            cases previous with
            | zero =>
                rw [Yul.InteractionSemantics.Exec.loop_zero]
                exact Simulation.Interaction.ForwardRel.truncated (by trivial)
            | succ loopFuel =>
                cases loopFuel with
                | zero =>
                    rw [Yul.InteractionSemantics.Exec.loop_one]
                    exact Simulation.Interaction.ForwardRel.truncated (by trivial)
                | succ iterationFuel =>
                    rcases hScoped.state with
                      ⟨entryShared, entryVars, hSource, _hShared, _hVars⟩
                    subst sourceEntry
                    have hKernelPositive : 0 < kernelTargetFuel := by
                      have hBudgetPositive :=
                        FunctionsInteractionFuel.executionBudgetFor_ge_sixteen
                          (FunctionsInteractionStaticCost.program sourceProgram)
                          (FunctionsInteractionStaticCost.program sourceProgram)
                          (iterationFuel + 3)
                      unfold FunctionsInteractionStaticCost.programBudget
                        at hKernelFuel
                      omega
                    obtain ⟨kernelRemaining, hKernelEq⟩ :
                        ∃ remaining, kernelTargetFuel = remaining + 1 :=
                      ⟨kernelTargetFuel - 1, by omega⟩
                    have hKernelFuel' :
                        FunctionsInteractionStaticCost.programBudget sourceProgram
                              (iterationFuel + 3) +
                            FunctionsInteractionTargetCost.stmt lowerLoop <
                          kernelRemaining + 1 := by
                      rw [← hKernelEq]
                      simpa [Nat.add_assoc] using hKernelFuel
                    have hChildGap :
                        FunctionsInteractionStaticCost.programBudget sourceProgram
                              iterationFuel + 8 ≤
                          FunctionsInteractionStaticCost.programBudget sourceProgram
                            (iterationFuel + 3) :=
                      FunctionsInteractionStaticCost.programBudget_child_add_eight_le
                        sourceProgram (by omega)
                    have hPreLength :=
                      FunctionsInteractionTargetCost.length_le_list preCond
                    have hCost := hKernelFuel'
                    dsimp [lowerLoop, lowerGuarded] at hCost
                    simp [FunctionsInteractionTargetCost.stmt,
                      FunctionsInteractionTargetCost.block,
                      FunctionsInteractionTargetCost.list,
                      FunctionsInteractionTargetCost.list_append] at hCost
                    have hCondBudget :
                        FunctionsInteractionStaticCost.programBudget sourceProgram
                              iterationFuel + preCond.length + 2 ≤
                            kernelRemaining := by
                      omega
                    have hGuardFuel : preCond.length + 2 < kernelRemaining := by
                      omega
                    have hRecurseBudget :
                        FunctionsInteractionStaticCost.programBudget sourceProgram
                                iterationFuel +
                              FunctionsInteractionTargetCost.stmt lowerLoop <
                            kernelRemaining := by
                      dsimp [lowerLoop, lowerGuarded]
                      dsimp [lowerLoop, lowerGuarded] at hKernelFuel'
                      omega
                    have hLoopTargetScope :
                        TargetScopeWithin before.used
                          (ctx.withLoopControl ctx.scope ctx.scope) := by
                      simpa [Functions.Source.Ctx.withLoopControl] using
                        hTargetScope
                    have hCondition :=
                      hConditions (childFuel := iterationFuel)
                        (childTargetFuel := kernelRemaining) (by omega)
                        hOkParts.1 hLowerCond hCondBudget hLayout
                        (by
                          simpa [Functions.Source.Ctx.withLoopControl] using
                            (show ScopedStateRel layout
                              (.Ok entryShared entryVars) targetEntry from
                                hScoped))
                        hEntryDomain hLoopTargetScope
                    have hGuarded :
                        Simulation.Interaction.ForwardRel Truncated
                          (FunctionsInteractionLoop.GuardedBodyDoneRel
                            before.used layout sourceScopes canLeave)
                          (Simulation.Interaction.bind
                            (Yul.InteractionSemantics.evalValues iterationFuel
                              cond (some sourceProgram.contract)
                              (.Ok entryShared entryVars))
                            (fun result =>
                              if result.2.head! = EvmYul.UInt256.ofNat 0 then
                                Simulation.Interaction.pure (.inl result.1)
                              else
                                Simulation.Interaction.map Sum.inr
                                  (Yul.InteractionSemantics.exec iterationFuel
                                    (.Block body)
                                    (some sourceProgram.contract) result.1)))
                          (Functions.InteractionSemantics.Block.openRunScoped
                            targetProgram.toFunctions
                            (ctx.withLoopControl ctx.scope ctx.scope)
                            lowerGuarded kernelRemaining targetEntry) := by
                      cases iterationFuel with
                      | zero =>
                          have hTruncated : Truncated
                              ({ exception := .OutOfFuel,
                                  state := .Ok entryShared entryVars } :
                                Yul.InteractionSemantics.Failure) := by
                            trivial
                          simpa [Yul.InteractionSemantics.evalValues,
                            Yul.Source.Canonical.evalValues,
                            Yul.Source.Effectful.evalValues,
                            Yul.InteractionSemantics.Primitive.fail,
                            Yul.Source.Effectful.Control.fail] using
                            (Simulation.Interaction.ForwardRel.truncated
                              (doneRel :=
                                FunctionsInteractionLoop.GuardedBodyDoneRel
                                  before.used layout sourceScopes canLeave)
                              (right :=
                                Functions.InteractionSemantics.Block.openRunScoped
                                  targetProgram.toFunctions
                                  (ctx.withLoopControl ctx.scope ctx.scope)
                                  lowerGuarded kernelRemaining targetEntry)
                              hTruncated)
                      | succ bodyFuel =>
                          have hBodyFuelLe :
                              FunctionsInteractionStaticCost.programBudget
                                    sourceProgram bodyFuel ≤
                                FunctionsInteractionStaticCost.programBudget
                                  sourceProgram (bodyFuel + 1) := by
                            unfold FunctionsInteractionStaticCost.programBudget
                            exact FunctionsInteractionFuel.executionBudgetFor_mono
                              _ _ (by omega)
                          have hBodyBudget :
                              FunctionsInteractionStaticCost.programBudget
                                      sourceProgram bodyFuel +
                                    FunctionsInteractionTargetCost.list
                                      lowerBodyStmts + 1 <
                                  kernelRemaining - preCond.length - 1 := by
                            omega
                          exact FunctionsInteractionLoop.guardedBody
                            (entryUsed := before.used)
                            (conditionUsed := afterCond.used)
                            (finalUsed := after.used)
                            (bodyLayout :=
                              SolcValidation.StmtsOutVars layout body)
                            (bodyFuel := bodyFuel)
                            (hTargetFuel := hGuardFuel)
                            hControl hTargetScope hCondition
                            (layoutWithinStmtsOutVars layout body)
                            (by
                              intro sourceAfter targetAfter ctxAfter sourceScope
                                hBodyScoped hBodyDomain hBodyControl
                                hBodyTargetScope
                              exact hLists (sourceFuel := bodyFuel)
                                (targetFuel :=
                                  kernelRemaining - preCond.length - 1)
                                (by omega) hOkParts.2.2 hBodyNames
                                hLowerBodyList hBodyScoped
                                (hBodyDomain.mono hPostExtends)
                                (hBodyTargetScope.mono hPostExtends)
                                hPostLayout hBodyControl hBodyBudget)
                    have hPost :
                        ∀ {sourceAfter : Yul.InteractionSemantics.State}
                          {targetAfter : Functions.InteractionSemantics.State},
                        ScopedStateRel layout sourceAfter targetAfter →
                        TargetDomainWithin before.used targetAfter.vars →
                        Simulation.Interaction.ForwardRel Truncated
                          (FunctionsInteractionLoop.KernelDoneRel
                            before.used layout sourceScopes canLeave)
                          (Yul.InteractionSemantics.exec iterationFuel
                            (.Block post) (some sourceProgram.contract)
                            sourceAfter)
                          (Functions.InteractionSemantics.Block.openRunScoped
                            targetProgram.toFunctions ctx.withoutLoopControl
                            { stmts := lowerPostStmts } kernelRemaining
                            targetAfter) := by
                      intro sourceAfter targetAfter hPostScoped hPostDomain
                      cases iterationFuel with
                      | zero =>
                          rw [Yul.InteractionSemantics.Exec.zero]
                          exact Simulation.Interaction.ForwardRel.truncated
                            (by trivial)
                      | succ postFuel =>
                          have hPostFuelLe :
                              FunctionsInteractionStaticCost.programBudget
                                    sourceProgram postFuel ≤
                                FunctionsInteractionStaticCost.programBudget
                                  sourceProgram (postFuel + 1) := by
                            unfold FunctionsInteractionStaticCost.programBudget
                            exact FunctionsInteractionFuel.executionBudgetFor_mono
                              _ _ (by omega)
                          have hPostBudget :
                              FunctionsInteractionStaticCost.programBudget
                                      sourceProgram postFuel +
                                    FunctionsInteractionTargetCost.list
                                      lowerPostStmts + 1 < kernelRemaining := by
                            omega
                          have hPostControl :=
                            ControlContextRel.forPost hControl
                          have hPostTargetScope :
                              TargetScopeWithin afterCond.used
                                ctx.withoutLoopControl := by
                            have hExtended := hTargetScope.mono hCondExtends
                            simpa [Functions.Source.Ctx.withoutLoopControl] using
                              hExtended
                          have hPostOutputScope :
                              TargetScopeWithin before.used
                                ctx.withoutLoopControl := by
                            simpa [Functions.Source.Ctx.withoutLoopControl] using
                              hTargetScope
                          have hPostRaw := hLists (sourceFuel := postFuel)
                            (targetFuel := kernelRemaining) (by omega)
                            hOkParts.2.1 hPostNames hLowerPostList hPostScoped
                            (hPostDomain.mono hCondExtends) hPostTargetScope
                            hCondLayout hPostControl hPostBudget
                          exact
                            FunctionsInteractionStatement.ControlDoneRel.blockScopedToUsed
                              (outputUsed := before.used) hPostScoped hPostControl
                              hPostOutputScope
                              (layoutWithinStmtsOutVars layout post) hPostRaw
                    have hRecurse :
                        ∀ {sourceAfter : Yul.InteractionSemantics.State}
                          {targetAfter : Functions.InteractionSemantics.State},
                        ScopedStateRel layout sourceAfter targetAfter →
                        TargetDomainWithin before.used targetAfter.vars →
                        Simulation.Interaction.ForwardRel Truncated
                          (FunctionsInteractionLoop.KernelDoneRel
                            before.used layout sourceScopes canLeave)
                          (Yul.InteractionSemantics.exec iterationFuel
                            (.For cond post body) (some sourceProgram.contract)
                            sourceAfter)
                          (Functions.InteractionSemantics.Stmt.openRunForLoop
                            targetProgram.toFunctions ctx.withoutLoopControl
                            (.lit (EvmYul.UInt256.ofNat 1))
                            ctx.withoutLoopControl { stmts := lowerPostStmts }
                            (ctx.withLoopControl ctx.scope ctx.scope) lowerGuarded
                            kernelRemaining targetAfter) := by
                      intro sourceAfter targetAfter hRecursiveScoped
                        hRecursiveDomain
                      exact ih iterationFuel (by omega) kernelRemaining
                        (by omega) hRecurseBudget hRecursiveScoped
                        hRecursiveDomain
                    rw [hKernelEq]
                    exact FunctionsInteractionLoop.iteration
                      (fuel := iterationFuel) (used := before.used)
                      (lowerPost := { stmts := lowerPostStmts })
                      (lowerGuarded := lowerGuarded)
                      hGuarded hPost hRecurse
  have hTargetPositive : 3 ≤ targetFuel := by
    have hBudgetPositive :=
      FunctionsInteractionFuel.executionBudgetFor_ge_sixteen
        (FunctionsInteractionStaticCost.program sourceProgram)
        (FunctionsInteractionStaticCost.program sourceProgram) sourceFuel
    unfold FunctionsInteractionStaticCost.programBudget at hTargetFuel
    omega
  have hOuterKernelBudget :
      FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.stmt lowerLoop < targetFuel - 2 := by
    dsimp [lowerLoop, lowerGuarded]
    simp only [FunctionsInteractionTargetCost.list] at hTargetFuel
    omega
  have hKernelRel := hKernel sourceFuel (targetFuel - 2)
    (by rfl) hOuterKernelBudget hRel hDomain
  have hStmtRel :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel after.used layout sourceScopes
          canBreak canContinue canLeave)
        (Yul.InteractionSemantics.exec sourceFuel (.For cond post body)
          (some sourceProgram.contract) source)
        (Functions.InteractionSemantics.Stmt.openRun
          targetProgram.toFunctions ctx (targetFuel - 1) lowerLoop target) := by
    rw [show targetFuel - 1 = (targetFuel - 3) + 2 by omega,
      Functions.InteractionSemantics.Stmt.openRun_for_empty_true]
    rw [show targetFuel - 3 + 1 = targetFuel - 2 by omega]
    apply Simulation.Interaction.ForwardRel.bind_right hKernelRel
    intro sourceDone targetDone hDone
    have hClosed :=
      (ControlOutcomeDoneRel.closeFor hControl hTargetScope hDone).monoUsed
        hFinalExtends
    cases targetDone with
    | error targetError =>
        simpa using
          (Simulation.Interaction.ForwardRel.done
            (truncated := Truncated) hClosed)
    | ok targetOutcome =>
        cases hMode : targetOutcome.mode <;>
          simpa [hMode] using
            (Simulation.Interaction.ForwardRel.done
              (truncated := Truncated) hClosed)
  have hFuelEq : targetFuel - 2 + 2 = targetFuel := by omega
  have hStmtFuelEq : targetFuel - 2 + 1 = targetFuel - 1 := by omega
  have hStmtRel' :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel after.used layout sourceScopes
          canBreak canContinue canLeave)
        (Yul.InteractionSemantics.exec sourceFuel (.For cond post body)
          (some sourceProgram.contract) source)
        (Functions.InteractionSemantics.Stmt.openRun
          targetProgram.toFunctions ctx (targetFuel - 2 + 1)
          lowerLoop target) := by
    rw [hStmtFuelEq]
    exact hStmtRel
  have hSingleton := FunctionsInteractionStatement.ControlDoneRel.singleton
    (targetFuel := targetFuel - 2) hStmtRel'
  simpa [lowerLoop, lowerGuarded, hFuelEq] using hSingleton

end CompoundForward

namespace RecursiveListForward

/-- Generic exact-tail sequencing.  This is the list edge of the historical
five-way recursion graph, rebuilt over the canonical open-interaction result
instead of observer replay state. -/
theorem ofStmt
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {bound : Nat}
    (hStmt : RecursiveStmtForward
      profile sourceProgram targetProgram bound) :
    RecursiveListForward profile sourceProgram targetProgram (bound + 1) := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro targetFuel hFuel
      intro compilerFuel functionNames layout sourceScopes
        canBreak canContinue canLeave before after stmts lower source target ctx
        hOk hNames hLower hRel hDomain hTargetScope hLayout hControl hTargetFuel
      rw [Yul.InteractionSemantics.ExecSeq.zero]
      exact Simulation.Interaction.ForwardRel.truncated
        (right := Functions.InteractionSemantics.Block.openRun
          targetProgram.toFunctions ctx targetFuel { stmts := lower } target)
        (by trivial)
  | succ fuel ih =>
      intro targetFuel hFuel
      intro compilerFuel functionNames layout sourceScopes
        canBreak canContinue canLeave before after stmts lower source target ctx
        hOk hNames hLower hRel hDomain hTargetScope hLayout hControl hTargetFuel
      cases stmts with
      | nil =>
          obtain ⟨previous, rfl, rfl, rfl⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLower
          have hPositive : 0 < targetFuel := by
            simp only [FunctionsInteractionTargetCost.list] at hTargetFuel
            omega
          have hTargetEq : targetFuel = (targetFuel - 1) + 1 := by omega
          rw [hTargetEq]
          simpa using
            (FunctionsInteractionStatement.ControlDoneRel.nil
              (sourceFuel := fuel) (targetFuel := targetFuel - 1)
              hRel hDomain hControl hTargetScope)
      | cons head tail =>
          obtain ⟨previous, lowerHead, middle, lowerTail,
              rfl, hLowerHead, hLowerTail, rfl⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_cons_parts hLower
          obtain ⟨hHeadOk, hTailOk⟩ :=
            SolcValidation.stmtsOk_cons_parts hOk
          have hNameParts :
              (∀ name, name ∈ Stmt.names head → name ∈ before.used) ∧
              (∀ name, name ∈ Stmt.List.names tail →
                name ∈ before.used) := by
            constructor <;> intro name hName
            · exact hNames name (by simp [Stmt.List.names, hName])
            · exact hNames name (by simp [Stmt.List.names, hName])
          have hMiddleExtends : Fresh.Extends before middle :=
            Stmt.toFunctionsListUncheckedFuel?_stateExtends hLowerHead
          have hTailNames : ∀ name, name ∈ Stmt.List.names tail →
              name ∈ middle.used := by
            intro name hName
            exact hMiddleExtends name (hNameParts.2 name hName)
          have hMiddleLayout : ∀ name,
              name ∈ SolcValidation.StmtOutVars layout head →
                name ∈ middle.used :=
            stmtOutVarsWithin hLayout hNameParts.1 hMiddleExtends
          have hProgramMono :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram fuel ≤
                FunctionsInteractionStaticCost.programBudget
                  sourceProgram (fuel + 1) := by
            unfold FunctionsInteractionStaticCost.programBudget
            exact FunctionsInteractionFuel.executionBudgetFor_mono
              _ _ (by omega)
          have hHeadFuel :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram fuel +
                    FunctionsInteractionTargetCost.list lowerHead + 1 <
                targetFuel := by
            rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
            omega
          have hTailFuel :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram fuel +
                    FunctionsInteractionTargetCost.list lowerTail + 1 <
                targetFuel - lowerHead.length := by
            rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
            have hLength :=
              FunctionsInteractionTargetCost.length_le_list lowerHead
            omega
          have hHead := hStmt (sourceFuel := fuel)
            (targetFuel := targetFuel) (by omega)
            hHeadOk hNameParts.1 hLowerHead hRel hDomain hTargetScope hLayout
            hControl hHeadFuel
          apply FunctionsInteractionStatement.ControlDoneRel.cons hHead
          intro sourceMid targetMid ctxMid hMidRel hMidDomain hMidControl
            hMidTargetScope
          exact ih (targetFuel := targetFuel - lowerHead.length) (by omega)
            hTailOk hTailNames hLowerTail hMidRel hMidDomain hMidTargetScope
            hMiddleLayout hMidControl hTailFuel

end RecursiveListForward

/-- Exhaustive ordinary-compiler statement dispatcher. Every recursive child
is supplied by a strictly smaller source-fuel statement capability; expression,
call, and compound cases delegate to their adjacent semantic owners. -/
theorem recursiveStmtOfEarlier
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    (hDecomposition :
      FunctionsCompilerArtifact.PassDecomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
    {bound : Nat}
    (hEarlier : ∀ childBound, childBound < bound →
      RecursiveStmtForward profile sourceProgram targetProgram childBound)
    (hBodies : ∀ {bodyFuel bodyTargetFuel : Nat}, bodyFuel < bound →
      FunctionsInteractionSelectedCall.BodyForwardAt
        profile sourceProgram targetProgram bodyFuel bodyTargetFuel) :
    RecursiveStmtForward profile sourceProgram targetProgram bound := by
  intro sourceFuel targetFuel hSourceFuel
  intro compilerFuel functionNames layout sourceScopes canBreak canContinue
    canLeave before after stmt lower source target ctx hOk hNames hLower hRel
    hDomain hTargetScope hLayout hControl hTargetFuel
  cases sourceFuel with
  | zero =>
      rw [Yul.InteractionSemantics.Exec.zero]
      exact Simulation.Interaction.ForwardRel.truncated
        (right := Functions.InteractionSemantics.Block.openRun
          targetProgram.toFunctions ctx targetFuel { stmts := lower } target)
        (by trivial)
  | succ fuel =>
      have hPrior : RecursiveStmtForward profile sourceProgram targetProgram
          (fuel + 1) :=
        hEarlier (fuel + 1) hSourceFuel
      have hListsNext : RecursiveListForward
          profile sourceProgram targetProgram (fuel + 2) :=
        RecursiveListForward.ofStmt hPrior
      have hListsFuel : RecursiveListForward
          profile sourceProgram targetProgram fuel := by
        intro childFuel childTargetFuel hChild
        exact hListsNext (lt_trans hChild (by omega))
      have hListsSucc : RecursiveListForward
          profile sourceProgram targetProgram (fuel + 1) := by
        intro childFuel childTargetFuel hChild
        exact hListsNext (lt_trans hChild (by omega))
      have hCondition :
          FunctionsInteractionRecursiveExpression.ConditionForwardAt
            profile sourceProgram targetProgram fuel targetFuel layout :=
        FunctionsInteractionRecursiveExpression.recursiveCondition
          hDecomposition hProgramOk fuel targetFuel layout
          (fun hBodyLt => hBodies (by omega))
      cases stmt with
      | Block body =>
          exact CompoundForward.block
            (fun recursiveTargetFuel =>
              hListsNext (sourceFuel := fuel)
                (targetFuel := recursiveTargetFuel) (by omega))
            hOk hNames hLower hRel hDomain
            hTargetScope hLayout hControl hTargetFuel
      | If cond body =>
          exact CompoundForward.ifThen hCondition hListsFuel hOk hNames hLower
            hRel hDomain hTargetScope hLayout hControl hTargetFuel
      | Switch cond cases defaultBody =>
          exact CompoundForward.switch hCondition hListsFuel hOk hNames hLower
            hRel hDomain hTargetScope hLayout hControl hTargetFuel
      | For cond post body =>
          exact CompoundForward.forLoop
            (hConditions := fun {_childFuel _childTargetFuel} hChild =>
              FunctionsInteractionRecursiveExpression.recursiveCondition
                hDecomposition hProgramOk _childFuel _childTargetFuel layout
                (fun hBodyLt => hBodies (by omega)))
            (hLists := hListsSucc) hOk hNames hLower hRel hDomain
            hTargetScope hLayout hControl hTargetFuel
      | Let names value? =>
          cases value? with
          | none =>
              have hBindable :
                  SolcValidation.bindableList? (functionNames ++ layout)
                      (identNames names) = true := by
                simpa [SolcValidation.StmtOk?] using hOk
              have hBindParts := hBindable
              simp [SolcValidation.bindableList?,
                SolcValidation.nonemptyNames?,
                SolcValidation.bindingNames?,
                SolcValidation.namesNodup?,
                SolcValidation.namesFresh?] at hBindParts
              have hNoDup : (identNames names).Nodup := hBindParts.2.2.1
              have hFresh : ∀ name, name ∈ identNames names →
                  name ∉ layout := by
                intro name hName
                exact (hBindParts.2.2.2 name hName).2
              have hDeclared : ∀ name, name ∈ identNames names →
                  name ∈ before.used := by
                intro name hName
                exact hNames name (by
                  simpa [Stmt.names] using hName)
              have hLowerParts :=
                Stmt.toFunctionsListUncheckedFuel?_let_none_parts hLower
              have hEnough : names.length + 1 ≤ targetFuel := by
                have hCost := hTargetFuel
                rw [hLowerParts.1] at hCost
                have hLength :=
                  FunctionsInteractionTargetCost.length_le_list
                    (Stmt.initNames (identNames names))
                have hInitLength :
                    (Stmt.initNames (identNames names)).length =
                      names.length := by
                  simp [Stmt.initNames, identNames_eq_self]
                rw [hInitLength] at hLength
                omega
              simpa [SolcValidation.StmtOutVars] using
                (FunctionsInteractionStatement.compiled_let_none_control_extra
                  hLower hNoDup hFresh hRel hDomain hDeclared hControl
                  hTargetScope hEnough)
          | some value =>
              by_cases hFunctionCall : ∃ functionName functionArgs,
                  value = .Call (.inr functionName) functionArgs
              · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
                cases fuel with
                | zero =>
                    have hCheck :
                        EvmYul.Yul.checkDeclaration source names = .ok () := by
                      have hOkParts := hOk
                      simp [SolcValidation.StmtOk?] at hOkParts
                      have hBindable := hOkParts.1
                      simp [SolcValidation.bindableList?,
                        SolcValidation.nonemptyNames?,
                        SolcValidation.bindingNames?,
                        SolcValidation.namesNodup?,
                        SolcValidation.namesFresh?] at hBindable
                      simpa [identNames_eq_self] using
                        hRel.declarationCheck_many hBindable.2.2.1
                          (fun name hName =>
                            (hBindable.2.2.2 name hName).2)
                    rw [Yul.InteractionSemantics.Exec.let_internal_one
                      names functionName functionArgs
                      (some sourceProgram.contract) source hCheck]
                    exact Simulation.Interaction.ForwardRel.truncated
                      (right := Functions.InteractionSemantics.Block.openRun
                        targetProgram.toFunctions ctx targetFuel
                        { stmts := lower } target) (by trivial)
                | succ callFuel =>
                    cases callFuel with
                    | zero =>
                        have hCheck :
                            EvmYul.Yul.checkDeclaration source names =
                              .ok () := by
                          have hOkParts := hOk
                          simp [SolcValidation.StmtOk?] at hOkParts
                          have hBindable := hOkParts.1
                          simp [SolcValidation.bindableList?,
                            SolcValidation.nonemptyNames?,
                            SolcValidation.bindingNames?,
                            SolcValidation.namesNodup?,
                            SolcValidation.namesFresh?] at hBindable
                          simpa [identNames_eq_self] using
                            hRel.declarationCheck_many hBindable.2.2.1
                              (fun name hName =>
                                (hBindable.2.2.2 name hName).2)
                        rw [Yul.InteractionSemantics.Exec.let_internal_two
                          names functionName functionArgs
                          (some sourceProgram.contract) source hCheck]
                        exact Simulation.Interaction.ForwardRel.truncated
                          (right :=
                            Functions.InteractionSemantics.Block.openRun
                              targetProgram.toFunctions ctx targetFuel
                              { stmts := lower } target) (by trivial)
                    | succ bodyFuel =>
                        have hLength :=
                          FunctionsInteractionTargetCost.length_le_list lower
                        have hProgramLe :
                            FunctionsInteractionStaticCost.programBudget
                                sourceProgram (bodyFuel + 1) ≤
                              FunctionsInteractionStaticCost.programBudget
                                sourceProgram (bodyFuel + 1 + 1 + 1) := by
                          unfold FunctionsInteractionStaticCost.programBudget
                          exact FunctionsInteractionFuel.executionBudgetFor_mono
                            _ _ (by omega)
                        have hTargetsUsed : ∀ name,
                            name ∈ identNames names → name ∈ before.used := by
                          intro name hName
                          exact hNames name (by
                            exact List.mem_append_left _ hName)
                        simpa [SolcValidation.StmtOutVars] using
                          (FunctionsInteractionSelectedStatementCall.compiledLetCall
                            hDecomposition hProgramOk hOk hLower
                            (fun recursiveTargetFuel =>
                              FunctionsInteractionRecursiveExpression.recursiveBoundHeads
                                hDecomposition hProgramOk (bodyFuel + 1)
                                recursiveTargetFuel layout
                                (fun hBodyLt =>
                                  hBodies (by omega)))
                            (fun bodyTargetFuel =>
                              hBodies (bodyTargetFuel := bodyTargetFuel)
                                (by omega))
                            hRel hDomain hTargetScope hLayout hControl
                            hTargetsUsed (by omega))
              · have hNotFunctionCall : ∀ functionName functionArgs,
                    value ≠ .Call (.inr functionName) functionArgs := by
                  intro functionName functionArgs hEq
                  exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
                obtain ⟨name, rfl⟩ :=
                  Stmt.toFunctionsListUncheckedFuel?_let_noncall_singleton
                    hNotFunctionCall hLower
                exact CompoundForward.letOne hCondition hOk hNames
                  hNotFunctionCall hLower hRel hDomain hTargetScope hLayout
                  hControl hTargetFuel
      | Assign names value =>
          by_cases hFunctionCall : ∃ functionName functionArgs,
              value = .Call (.inr functionName) functionArgs
          · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
            cases fuel with
            | zero =>
                have hOkParts := hOk
                simp [SolcValidation.StmtOk?] at hOkParts
                have hAssignable := hOkParts.1
                simp [SolcValidation.assignableList?,
                  SolcValidation.nonemptyNames?, SolcValidation.namesNodup?,
                  SolcValidation.namesIn?] at hAssignable
                have hCheck : EvmYul.Yul.checkAssignment source names =
                    .ok () := by
                  simpa [identNames_eq_self] using
                    hRel.assignmentCheck_many hAssignable.2.1
                      hAssignable.2.2
                rw [Yul.InteractionSemantics.Exec.assign_internal_one
                  names functionName functionArgs
                  (some sourceProgram.contract) source hCheck]
                exact Simulation.Interaction.ForwardRel.truncated
                  (right := Functions.InteractionSemantics.Block.openRun
                    targetProgram.toFunctions ctx targetFuel
                    { stmts := lower } target) (by trivial)
            | succ callFuel =>
                cases callFuel with
                | zero =>
                    have hOkParts := hOk
                    simp [SolcValidation.StmtOk?] at hOkParts
                    have hAssignable := hOkParts.1
                    simp [SolcValidation.assignableList?,
                      SolcValidation.nonemptyNames?,
                      SolcValidation.namesNodup?, SolcValidation.namesIn?]
                      at hAssignable
                    have hCheck : EvmYul.Yul.checkAssignment source names =
                        .ok () := by
                      simpa [identNames_eq_self] using
                        hRel.assignmentCheck_many hAssignable.2.1
                          hAssignable.2.2
                    rw [Yul.InteractionSemantics.Exec.assign_internal_two
                      names functionName functionArgs
                      (some sourceProgram.contract) source hCheck]
                    exact Simulation.Interaction.ForwardRel.truncated
                      (right := Functions.InteractionSemantics.Block.openRun
                        targetProgram.toFunctions ctx targetFuel
                        { stmts := lower } target) (by trivial)
                | succ bodyFuel =>
                    have hLength :=
                      FunctionsInteractionTargetCost.length_le_list lower
                    have hProgramLe :
                        FunctionsInteractionStaticCost.programBudget
                            sourceProgram (bodyFuel + 1) ≤
                          FunctionsInteractionStaticCost.programBudget
                            sourceProgram (bodyFuel + 1 + 1 + 1) := by
                      unfold FunctionsInteractionStaticCost.programBudget
                      exact FunctionsInteractionFuel.executionBudgetFor_mono
                        _ _ (by omega)
                    simpa [SolcValidation.StmtOutVars] using
                      (FunctionsInteractionSelectedStatementCall.compiledAssignCall
                        hDecomposition hProgramOk hOk hLower
                        (FunctionsInteractionRecursiveExpression.recursiveBoundHeads
                          hDecomposition hProgramOk (bodyFuel + 1) targetFuel
                          layout (fun hBodyLt =>
                            hBodies (by omega)))
                        (fun bodyTargetFuel =>
                          hBodies (bodyTargetFuel := bodyTargetFuel) (by omega))
                        hRel hDomain hTargetScope hLayout hControl (by omega))
          · have hNotFunctionCall : ∀ functionName functionArgs,
                value ≠ .Call (.inr functionName) functionArgs := by
              intro functionName functionArgs hEq
              exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
            obtain ⟨name, rfl⟩ :=
              Stmt.toFunctionsListUncheckedFuel?_assign_noncall_singleton
                hNotFunctionCall hLower
            exact CompoundForward.assignOne hCondition
              (FunctionsInteractionRecursiveExpression.recursiveBoundHeads
                hDecomposition hProgramOk (fuel - 1) targetFuel layout
                (fun hBodyLt =>
                  hBodies (by omega)))
              hOk hNames hNotFunctionCall hLower hRel hDomain hTargetScope
              hLayout hControl hTargetFuel
      | ExprStmtCall value =>
          cases value with
          | Lit literal =>
              simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
          | Var name =>
              simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
          | Call callee args =>
              cases callee with
              | inl prim =>
                  cases hTerminal : Prim.terminal? prim with
                  | none =>
                      exact CompoundForward.exprPrimitive hTerminal
                        (fun argsFuel hArgsFuel =>
                          FunctionsInteractionRecursiveExpression.recursiveBoundHeads
                            hDecomposition hProgramOk argsFuel targetFuel layout
                            (fun hBodyLt => hBodies
                              (lt_trans hBodyLt
                                (lt_trans hArgsFuel hSourceFuel))))
                        hOk hLower hRel hDomain hTargetScope hLayout hControl
                        hTargetFuel
                  | some kind =>
                      exact CompoundForward.terminalPrimitive hTerminal
                        (fun argsFuel hArgsFuel =>
                          FunctionsInteractionRecursiveExpression.recursiveBoundHeads
                            hDecomposition hProgramOk argsFuel targetFuel layout
                            (fun hBodyLt => hBodies
                              (lt_trans hBodyLt
                                (lt_trans hArgsFuel hSourceFuel))))
                        hOk hLower hRel hDomain hTargetScope hLayout hTargetFuel
              | inr functionName =>
                  cases fuel with
                  | zero =>
                      rw [Yul.InteractionSemantics.Exec.expr_internal_one]
                      exact Simulation.Interaction.ForwardRel.truncated
                        (right := Functions.InteractionSemantics.Block.openRun
                          targetProgram.toFunctions ctx targetFuel
                          { stmts := lower } target) (by trivial)
                  | succ callFuel =>
                      cases callFuel with
                      | zero =>
                          rw [Yul.InteractionSemantics.Exec.expr_internal_two]
                          exact Simulation.Interaction.ForwardRel.truncated
                            (right :=
                              Functions.InteractionSemantics.Block.openRun
                                targetProgram.toFunctions ctx targetFuel
                                { stmts := lower } target) (by trivial)
                      | succ bodyFuel =>
                          have hLength :=
                            FunctionsInteractionTargetCost.length_le_list lower
                          have hProgramLe :
                              FunctionsInteractionStaticCost.programBudget
                                  sourceProgram (bodyFuel + 2) ≤
                                FunctionsInteractionStaticCost.programBudget
                                  sourceProgram (bodyFuel + 1 + 1 + 1) := by
                            unfold
                              FunctionsInteractionStaticCost.programBudget
                            exact
                              FunctionsInteractionFuel.executionBudgetFor_mono
                                _ _ (by omega)
                          exact
                            FunctionsInteractionSelectedStatementCall.compiledExprCall
                              hDecomposition hProgramOk hOk hLower
                              (FunctionsInteractionRecursiveExpression.recursiveBoundHeads
                                hDecomposition hProgramOk (bodyFuel + 2)
                                targetFuel layout (fun hBodyLt =>
                                  hBodies (by omega)))
                              (fun bodyTargetFuel =>
                                hBodies (bodyTargetFuel := bodyTargetFuel)
                                  (by omega))
                              hRel hDomain hTargetScope hLayout hControl
                              (by omega)
      | Break =>
          have hEnabled : canBreak = true := by
            simpa [SolcValidation.StmtOk?] using hOk
          have hFuelEq : targetFuel = (targetFuel - 2) + 2 := by
            have hLength :=
              FunctionsInteractionTargetCost.length_le_list lower
            omega
          rw [hFuelEq]
          exact FunctionsInteractionStatement.compiled_brk_control
            hLower hEnabled hControl hRel
      | Continue =>
          have hEnabled : canContinue = true := by
            simpa [SolcValidation.StmtOk?] using hOk
          have hFuelEq : targetFuel = (targetFuel - 2) + 2 := by
            have hLength :=
              FunctionsInteractionTargetCost.length_le_list lower
            omega
          rw [hFuelEq]
          exact FunctionsInteractionStatement.compiled_cont_control
            hLower hEnabled hControl hRel
      | Leave =>
          have hEnabled : canLeave = true := by
            simpa [SolcValidation.StmtOk?] using hOk
          have hFuelEq : targetFuel = (targetFuel - 2) + 2 := by
            have hLength :=
              FunctionsInteractionTargetCost.length_le_list lower
            omega
          rw [hFuelEq]
          exact FunctionsInteractionStatement.compiled_leave_control
            hLower hEnabled hControl hRel

end FunctionsInteractionRecursiveStatement
end Yul
end EvmCompiler
