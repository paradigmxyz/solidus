import EvmCompiler.Functions.AllocationInteractionCursor
import EvmCompiler.Functions.AllocationInteractionComposition
import EvmCompiler.Functions.AllocationInteractionLeaf
import EvmCompiler.Functions.AllocationInteractionAbrupt
import EvmCompiler.Functions.AllocationInteractionLeave
import EvmCompiler.Functions.AllocationInteractionTerminal

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionForward

open AllocationInteractionRelation
open AllocationInteractionCursor
open AllocationInteractionComposition

/-- A runtime activation has at least the scratch capacity selected by the pass. -/
def FrameCapacity
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions) :
    ActivationMode → Prop
  | .stack => True
  | .scratch _ frameWords => compilation.recipe.frameWords ≤ frameWords

namespace FrameCapacity

theorem declaration
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {plan : Locals.Allocation.Plan} {name : Locals.Name}
    {before after : ActivationMode}
    (hBefore : FrameCapacity compilation before)
    (hTransition :
      AllocationContext.DeclarationModeTransition
        plan name before after) :
    FrameCapacity compilation after := by
  cases hTransition with
  | @stack before planDepth hLocation =>
      cases before <;> exact hBefore
  | scratch frameDepth frameWords slot hLocation =>
      exact hBefore

theorem cleanup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {finalStackDepth targetDepth : Nat}
    {before after : ActivationMode}
    (hBefore : FrameCapacity compilation before)
    (hTransition :
      AllocationInteractionCleanup.ModeTransition
        finalStackDepth targetDepth before after) :
    FrameCapacity compilation after := by
  cases hTransition with
  | stack target => exact hBefore
  | scratch beforeDepth afterDepth frameWords afterDepthEq target =>
      exact hBefore

end FrameCapacity

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
        cursor.finalLocals cursor.plan root.returns live frameBase mode ctx ctx)
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
    {entryMode : ActivationMode}
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
          (Functions.Scope.Stmt.outEnv live stmt) frameBase entryMode
          sourceCtx midCtx)
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
              mode midCtx finalCtx)
            (Functions.InteractionSemantics.Block.openRun
              program midCtx sourceFuel { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetFuel - headCode.length)
                { stmts := tail.compiled } targetMid)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract root.lowerCtx cursor.finalState
        cursor.finalLocals cursor.plan root.returns finalLive frameBase
        entryMode sourceCtx finalCtx)
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        (sourceFuel + 1) { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := cursor.compiled } target) := by
  rcases hTail with ⟨hPlan, hFinalState, hFinalLocals, _hCompiledTail⟩
  rw [hPlan, hFinalState, hFinalLocals] at hTailForward
  rw [hCompiled]
  exact AllocationInteractionComposition.block_cons hHead hTailForward

/-- Derive an expression head theorem and exact tail from its cursor. -/
theorem CoreCursor.expr_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.expr expr) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  have hExprScoped : Functions.Scope.ExprScoped live expr := by
    simpa [Functions.Scope.Stmt.Scoped] using hScoped
  have hHead :=
    AllocationInteractionLeaf.expr_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSafe hExprScoped hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive an assignment head theorem and exact tail from its cursor. -/
theorem CoreCursor.assign_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.assign name value) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  have hHead :=
    AllocationInteractionLeaf.assign_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSafe hScoped.2 hScoped.1 hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive a declaration head theorem in stack or scratch representation. -/
theorem CoreCursor.let_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hCapacity : FrameCapacity compilation mode)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope (name :: live) { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns (name :: live) frameBase
              mode sourceCtx
              { sourceCtx with scope := name :: sourceCtx.scope })
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.let_ name value) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨afterMode, hAfter, hTransition⟩ :=
    cursor.letContext tail hPlanning hPlan hInvariant.compiler
      hLower hCompile
  have hNameFrame : name ≠ root.lowerCtx.frameName := by
    intro hEq
    apply tail.frameName_not_mem_live
    change compilation.frameName ∈ name :: live
    have hNameCompilation : name = compilation.frameName :=
      hEq.trans root.lowerCtxShared.frameName
    simp [hNameCompilation]
  have hScratchBound :
      ∀ {frameDepth frameWords slot},
        mode = .scratch frameDepth frameWords →
        cursor.plan.location? name = some (.scratch slot) →
        slot < frameWords := by
    intro frameDepth frameWords slot hMode hLocation
    rw [hMode] at hCapacity
    exact
      lt_of_lt_of_le
        (cursor.scratch_bound_of_location hLocation) hCapacity
  have hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState
          afterLocals cursor.plan root.returns (name :: live) frameBase
          mode sourceCtx
          { sourceCtx with scope := name :: sourceCtx.scope })
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx sourceFuel (.let_ name value) source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (targetExtra + 2) { stmts := headCode } target) := by
    cases mode with
    | stack =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | stack hAfterStack =>
                exact
                  AllocationInteractionLeaf.stack_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterStack hScoped.2 hLower hCompile hInvariant
    | scratch frameDepth frameWords =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionLeaf.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterScratch hScoped.2 rfl hNameFrame
                    (fun slot hLocation =>
                      hScratchBound rfl hLocation)
                    hLower hCompile hInvariant
        | scratch frameDepth frameWords slot hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionLeaf.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterScratch hScoped.2 rfl hNameFrame
                    (fun slot hLocation =>
                      hScratchBound rfl hLocation)
                    hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive a `break` head theorem from its loop-destination transition. -/
theorem CoreCursor.brk_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              beforeMode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .brk source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  have hHead :=
    AllocationInteractionAbrupt.brk_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive a `continue` head theorem from its loop-destination transition. -/
theorem CoreCursor.cont_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              beforeMode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .cont source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  have hHead :=
    AllocationInteractionAbrupt.cont_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive a `leave` head theorem and exact unreachable tail. -/
theorem CoreCursor.leave_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live functionScope : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .leave :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ root.returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ root.returns → name ∈ functionScope)
    (hTargetDepth : beforeLocals.leaveDepth? = some 0)
    (hRetc : beforeLocals.leaveRetc = root.returns.length)
    (hReturnFrame : target.returns ≠ [])
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .leave source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 4)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  have hHead :=
    AllocationInteractionLeave.leave_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hReturnsLive hReturnsScope hTargetDepth hRetc
      hReturnFrame hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive a plain terminal head theorem and exact unreachable tail. -/
theorem CoreCursor.terminal_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hMemory :
      Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.terminal kind) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  have hHead :=
    AllocationInteractionTerminal.terminal_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hMemory hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- Derive an argument-bearing terminal head and exact unreachable tail. -/
theorem CoreCursor.terminalArgs_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hArgsSafe :
      AllocationInteractionSafety.ExprSeqSafe contract args source)
    (hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe
                contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source))
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              afterLocals cursor.plan root.returns live frameBase
              mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.terminalArgs kind args) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3)
                { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  have hArgsScoped : Functions.Scope.ExprSeqScoped live args := by
    simpa [Functions.Scope.Stmt.Scoped] using hScoped
  have hHead :=
    AllocationInteractionTerminal.terminalArgs_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hArgsSafe hTerminalSafe hArgsScoped hLower hCompile hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

end AllocationInteractionForward
end Functions
end EvmCompiler
