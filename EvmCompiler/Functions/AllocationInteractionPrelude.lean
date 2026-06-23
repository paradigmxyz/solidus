import EvmCompiler.Functions.AllocationInteractionLeaf
import EvmCompiler.Functions.AllocationInteractionSafeSuccessful
import EvmCompiler.Functions.AllocationInteractionSuccessful

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionPrelude

open AllocationInteractionComposition
open AllocationInteractionRelation
open AllocationInteractionSuccessful

/-- Ordinary Locals compilation of a lowered source prelude emits exactly one
flat code statement per source statement and leaves the Locals context
unchanged. -/
theorem compile_shape
    {sourcePrefix : List Functions.Stmt}
    {loweredPrefix : List Locals.Stmt}
    (hPrelude :
      AllocationLowering.PreludeLowered sourcePrefix loweredPrefix)
    {localsCtx finalLocals : Locals.Ctx}
    {compiledPrefix : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredPrefix } =
        some (compiledPrefix, finalLocals)) :
    finalLocals = localsCtx ∧
      compiledPrefix.length = sourcePrefix.length ∧
      (∀ stmt, stmt ∈ compiledPrefix → ∃ code, stmt = .code code) := by
  induction hPrelude generalizing compiledPrefix finalLocals with
  | nil =>
      have hPair :
          ([], localsCtx) = (compiledPrefix, finalLocals) := by
        simpa [Locals.Block.compileOpen] using hCompile
      cases hPair
      exact ⟨rfl, rfl, by simp⟩
  | @cons stmt rest code lowered head tail ih =>
      cases stmt with
      | expr expr =>
          cases hTailCompile :
              Locals.Block.compileOpen localsCtx { stmts := lowered } with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.Expr.compileCode, Locals.codeStmt, hTailCompile]
                at hCompile
          | some tailResult =>
              rcases tailResult with ⟨compiledTail, tailLocals⟩
              have hPair :
                  (Expressions.Stmt.code code :: compiledTail, tailLocals) =
                    (compiledPrefix, finalLocals) := by
                simpa [Locals.Block.compileOpen, Locals.Stmt.compile,
                  Locals.Expr.compileCode, Locals.codeStmt, hTailCompile]
                  using hCompile
              cases hPair
              obtain ⟨hLocals, hLength, hCodeOnly⟩ := ih hTailCompile
              exact
                ⟨hLocals, by simp [hLength], by
                  intro compiledStmt hMem
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst compiledStmt
                    exact ⟨code, rfl⟩
                  · exact hCodeOnly compiledStmt hTail⟩
      | let_ name value | assign name value | block block
      | if_ cond block | switch scrutinee cases defaultBody
      | for_ init cond post loopBody | brk | cont | leave
      | call targets functionName args | terminal kind
      | terminalArgs kind args =>
          simp [AllocationSupport.compilePreludeStmt?] at head

/-- A scoped whole statement list has a scoped compiler-selected prelude. -/
theorem scopedPrefix
    {sourcePrefix rest : List Functions.Stmt}
    {loweredPrefix : List Locals.Stmt}
    (hPrelude :
      AllocationLowering.PreludeLowered sourcePrefix loweredPrefix)
    {env : List Functions.Name}
    (hScoped :
      Functions.Scope.StmtList.Scoped env (sourcePrefix ++ rest)) :
    Functions.Scope.StmtList.Scoped env sourcePrefix := by
  induction hPrelude generalizing env with
  | nil => trivial
  | @cons stmt sourceRest code lowered head tail ih =>
      cases stmt with
      | expr expr =>
          exact ⟨hScoped.1, ih hScoped.2⟩
      | let_ name value | assign name value | block block
      | if_ cond block | switch scrutinee cases defaultBody
      | for_ init cond post loopBody | brk | cont | leave
      | call targets functionName args | terminal kind
      | terminalArgs kind args =>
          simp [AllocationSupport.compilePreludeStmt?] at head

/-- The compiler-owned no-variable source prelude preserves the ordinary
allocation boundary and leaves allocation/Locals contexts unchanged.  The
target fuel is arbitrary above the exact one-statement-per-prefix bound, so
later program composition may retain setup, body, and cleanup suffixes. -/
theorem forward
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourcePrefix : List Functions.Stmt}
    {loweredPrefix : List Locals.Stmt}
    (hPrelude :
      AllocationLowering.PreludeLowered sourcePrefix loweredPrefix)
    {compiledPrefix : List Expressions.Stmt}
    {finalLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Locals.Allocation.Plan}
    {frameBase : Nat} {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat} {mode : ActivationMode}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredPrefix } =
        some (compiledPrefix, finalLocals))
    (hScoped : Functions.Scope.StmtList.Scoped [] sourcePrefix)
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan [] frameBase mode source target)
    (hTargetFuel : sourcePrefix.length + 1 ≤ targetFuel)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        sourceProgram sourceCtx sourceFuel { stmts := sourcePrefix } source) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan [] []
        frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Block.openRun sourceProgram sourceCtx
        sourceFuel { stmts := sourcePrefix } source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := compiledPrefix } target) := by
  induction hPrelude generalizing compiledPrefix finalLocals sourceFuel
      targetFuel mode source target with
  | nil =>
      have hCompiled :
          ([], localsCtx) = (compiledPrefix, finalLocals) := by
        simpa [Locals.Block.compileOpen] using hCompile
      have hCode := congrArg Prod.fst hCompiled
      have hLocals := congrArg Prod.snd hCompiled
      simp only [Prod.fst] at hCode
      simp only [Prod.snd] at hLocals
      subst compiledPrefix
      subst finalLocals
      have hSourceFuel :=
        Functions.InteractionSemantics.Block.successful_openRun_fuel_pos
          hExecutionSafe.ordinarySuccessful
      obtain ⟨sourceExtra, hSourceFuelEq⟩ :=
        Nat.exists_eq_add_of_le hSourceFuel
      obtain ⟨targetExtra, hTargetFuelEq⟩ :=
        Nat.exists_eq_add_of_le hTargetFuel
      rw [hSourceFuelEq, hTargetFuelEq]
      simpa [Nat.add_comm] using
        (AllocationInteractionComposition.block_nil
          (sourceProgram := sourceProgram)
          (targetProgram := targetProgram)
          (sourceFuel := sourceExtra) (targetFuel := targetExtra)
          (returns := []) (ctx := sourceCtx) hInvariant)
  | @cons stmt rest code lowered head tail ih =>
      cases stmt with
      | expr expr =>
          have hNoVar :
              AllocationSupport.compileNoVarExprCode? expr = some code := by
            cases hActual :
                AllocationSupport.compileNoVarExprCode? expr with
            | none =>
                simp [AllocationSupport.compilePreludeStmt?, hActual] at head
            | some actual =>
                have hCode : actual = code := by
                  simpa [AllocationSupport.compilePreludeStmt?, hActual]
                    using head
                subst actual
                rfl
          cases hTailCompile :
              Locals.Block.compileOpen localsCtx { stmts := lowered } with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.Expr.compileCode, Locals.codeStmt, hTailCompile]
                at hCompile
          | some tailResult =>
              rcases tailResult with ⟨compiledTail, tailLocals⟩
              have hCompiled :
                  (Expressions.Stmt.code code :: compiledTail, tailLocals) =
                    (compiledPrefix, finalLocals) := by
                simpa [Locals.Block.compileOpen, Locals.Stmt.compile,
                  Locals.Expr.compileCode, Locals.codeStmt, hTailCompile]
                  using hCompile
              have hCode := congrArg Prod.fst hCompiled
              have hLocals := congrArg Prod.snd hCompiled
              simp only [Prod.fst] at hCode
              simp only [Prod.snd] at hLocals
              subst compiledPrefix
              subst finalLocals
              have hSourceFuel :=
                Functions.InteractionSemantics.Block.successful_openRun_fuel_pos
                  hExecutionSafe.ordinarySuccessful
              have hHeadSafe :=
                AllocationInteractionSafeSuccessful.successful_head
                  hSourceFuel hExecutionSafe
              have hExprScoped : Functions.Scope.ExprScoped [] expr := by
                simpa [Functions.Scope.Stmt.Scoped] using hScoped.1
              have hSafe :=
                (AllocationInteractionSafeExpression.exprChecked_of_successful
                  hExprScoped hInvariant.defined
                  (AllocationInteractionSafeSuccessful.successful_expr_eval
                    hHeadSafe)).safety
              obtain ⟨loweredExpr, hLowerExpr, hCompileExpr⟩ :=
                AllocationLowering.compileNoVarExprCode?_of_lowerExpr
                  hNoVar lowerCtx lowerState localsCtx 0
              have hLowerStmt :
                  AllocationLowering.lowerStmt lowerCtx [] lowerState
                      (.expr expr) =
                    some ([.expr loweredExpr], lowerState) := by
                simp [AllocationLowering.lowerStmt, hLowerExpr]
              have hCompileStmt :
                  Locals.Block.compileOpen localsCtx
                      { stmts := [.expr loweredExpr] } =
                    some ([.code code], localsCtx) := by
                simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                  hCompileExpr, Locals.codeStmt]
              have hHead :=
                AllocationInteractionLeaf.expr_of_lower_compile
                  (sourceProgram := sourceProgram)
                  (sourceCtx := sourceCtx)
                  (targetProgram := targetProgram)
                  (sourceFuel := sourceFuel - 1)
                  (targetExtra := targetFuel - 2)
                  hSafe hExprScoped hLowerStmt hCompileStmt hInvariant
              have hHead' :
                  Simulation.Interaction.Rel
                    (OpenControlResultRel contract lowerCtx lowerState
                      localsCtx plan [] [] frameBase mode sourceCtx sourceCtx)
                    (Functions.InteractionSemantics.Stmt.openRun sourceProgram
                      sourceCtx (sourceFuel - 1) (.expr expr) source)
                    (Expressions.InteractionSemantics.Block.openRun
                      targetProgram targetFuel
                      { stmts := [.code code] } target) := by
                have hTargetFuel' : rest.length + 2 ≤ targetFuel := by
                  simpa using hTargetFuel
                have hTwo : 2 ≤ targetFuel := by omega
                simpa only [Nat.sub_add_cancel hTwo] using hHead
              have hSourceFuelEq : sourceFuel - 1 + 1 = sourceFuel := by
                omega
              have hResult :=
                AllocationInteractionComposition.block_cons_executionSafe
                  (sourceFuel := sourceFuel - 1)
                  (targetFuel := targetFuel)
                  (headCode := [.code code])
                  (tailCode := compiledTail)
                  (midLowerCtx := lowerCtx)
                  (finalLowerCtx := lowerCtx)
                  (midLowerState := lowerState)
                  (finalLowerState := lowerState)
                  (midLocals := localsCtx)
                  (finalLocals := localsCtx)
                  (plan := plan) (returns := [])
                  (midLive := []) (finalLive := [])
                  (frameBase := frameBase) (entryMode := mode)
                  (controlCtx := sourceCtx) (midCtx := sourceCtx)
                  (finalCtx := sourceCtx) hHead'
                  (by simpa [hSourceFuelEq] using hExecutionSafe)
                  (fun {sourceMid targetMid tailMode} hTailInvariant
                      hSameFrame hReturns hTailSuccess hTailSafe => by
                    have hTailTargetFuel :
                        rest.length + 1 ≤ targetFuel - 1 := by
                      have hTargetFuel' : rest.length + 2 ≤ targetFuel := by
                        simpa using hTargetFuel
                      omega
                    exact ih hTailCompile hScoped.2 hTailInvariant
                      hTailTargetFuel hTailSafe)
              simpa [hSourceFuelEq] using hResult
      | let_ name value | assign name value | block block
      | if_ cond block | switch scrutinee cases defaultBody
      | for_ init cond post loopBody | brk | cont | leave
      | call targets functionName args | terminal kind
      | terminalArgs kind args =>
          simp [AllocationSupport.compilePreludeStmt?] at head

end AllocationInteractionPrelude
end Functions
end EvmCompiler
