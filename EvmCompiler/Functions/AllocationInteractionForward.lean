import EvmCompiler.Functions.AllocationInteractionCursor
import EvmCompiler.Functions.AllocationInteractionComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionForward

open AllocationInteractionRelation
open AllocationInteractionCursor
open AllocationInteractionComposition

/-- The empty canonical cursor preserves its complete activation invariant. -/
theorem CoreCursor.nil
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetFuel frameBase : Nat}
    {mode : ActivationMode}
    {ctx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := [] } lowerState localsCtx)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract root.lowerCtx cursor.finalState
        cursor.finalLocals cursor.plan root.returns live frameBase ctx ctx)
      (Functions.InteractionSemantics.Block.openRun program ctx
        (sourceFuel + 1) { stmts := [] } source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetFuel + 1) { stmts := cursor.compiled } target) := by
  have hLower := cursor.lower
  simp [AllocationLowering.lowerBlockOpen,
    AllocationLowering.lowerStmtList] at hLower
  obtain ⟨hLowered, hFinalState⟩ := hLower
  have hCompile := cursor.compile
  rw [← hLowered] at hCompile
  simp [Locals.Block.compileOpen] at hCompile
  obtain ⟨hCompiled, hFinalLocals⟩ := hCompile
  simpa [hFinalState, hFinalLocals, hCompiled] using
    (AllocationInteractionComposition.block_nil
      (sourceProgram := program)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel)
      (targetFuel := targetFuel)
      (returns := root.returns)
      (ctx := ctx)
      hInvariant)

/-- Compose one cursor head with its exact recursively preserved tail. -/
theorem CoreCursor.cons_of_parts
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live finalLive : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetFuel frameBase : Nat}
    {sourceCtx midCtx finalCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    {headCode : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hTail : ExactTail cursor tail)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns
          (Functions.Scope.Stmt.outEnv live stmt) frameBase sourceCtx midCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel { stmts := headCode } target))
    (hTailForward :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase mode sourceMid targetMid →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx tail.finalState
              tail.finalLocals tail.plan root.returns finalLive frameBase
              midCtx finalCtx)
            (Functions.InteractionSemantics.Block.openRun
              program midCtx sourceFuel { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetFuel - headCode.length)
                { stmts := tail.compiled } targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract root.lowerCtx cursor.finalState
        cursor.finalLocals cursor.plan root.returns finalLive frameBase
        sourceCtx finalCtx)
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        (sourceFuel + 1) { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := cursor.compiled } target) := by
  rcases hTail with ⟨hPlan, hFinalState, hFinalLocals⟩
  rw [hPlan, hFinalState, hFinalLocals] at hTailForward
  rw [hCompiled]
  exact AllocationInteractionComposition.block_cons hHead hTailForward

end AllocationInteractionForward
end Functions
end EvmCompiler
