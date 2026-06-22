import EvmCompiler.Functions.AllocationInteractionRecursiveResource
import EvmCompiler.Functions.AllocationInteractionSafeSuccessful

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionExecutionRuntime

open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionRecursive
open AllocationInteractionRecursiveResource
open AllocationInteractionResourceComposition
open AllocationInteractionRecursiveResource.CursorRuntimeAt

theorem expr
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .expr expr :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.expr_runtime_head cursor
      (sourceFuel := childFuel) (targetExtra := headExtra)
      hSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.expr expr) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.expr expr) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement := by
              have hAfterMatches := hInvariant.compiler.mode_matches
              rw [hExact.plan] at hAfterMatches
              have hModeEq := hSame.eq_of_matches
                hBoundary.semantic.invariant.compiler.mode_matches
                hAfterMatches
              subst tailMode
              rw [hExact.plan]
              exact
                (hBoundary.controlAgreement.transport_context
                  (Functions.Source.Ctx.SameControl.refl sourceCtx)
                  (hExact.locals_sameControl cursor tail)).transport_target
                    hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive assignment with semantic and allocator preservation. -/
theorem assign
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .assign name value :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.assign_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.assign name value) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.assign name value) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement := by
              have hAfterMatches := hInvariant.compiler.mode_matches
              rw [hExact.plan] at hAfterMatches
              have hModeEq := hSame.eq_of_matches
                hBoundary.semantic.invariant.compiler.mode_matches
                hAfterMatches
              subst tailMode
              rw [hExact.plan]
              exact
                (hBoundary.controlAgreement.transport_context
                  (Functions.Source.Ctx.SameControl.refl sourceCtx)
                  (hExact.locals_sameControl cursor tail)).transport_target
                    hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive declaration with semantic and allocator preservation. -/
theorem let_
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .let_ name value :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope (name :: live) { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program
                { sourceCtx with scope := name :: sourceCtx.scope }
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program { sourceCtx with scope := name :: sourceCtx.scope }
                (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions) tailMode
              { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  let nextCtx := { sourceCtx with scope := name :: sourceCtx.scope }
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hPlacement, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.let_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase mode sourceCtx
          nextCtx config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.let_ name value) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [nextCtx, hHeadFuel] using hHead
  have hMidCtx :
      nextCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.let_ name value) } := by
    cases sourceCtx
    have hScope := hBoundary.semantic.sourceScope
    simp only at hScope
    cases hScope
    rfl
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := by
                  simp [nextCtx, hBoundary.semantic.sourceScope]
                control :=
                  (hBoundary.semantic.control.mono
                    (fun other hOther => by simp [hOther])).scopeUpdate
                    (name :: sourceCtx.scope)
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement := by
              have hAfterMatches := hInvariant.compiler.mode_matches
              rw [hExact.plan] at hAfterMatches
              have hSourceControl :
                  Functions.Source.Ctx.SameControl sourceCtx nextCtx := by
                simpa [nextCtx] using
                  Functions.Source.Ctx.SameControl.scopeUpdate sourceCtx
                    (name :: sourceCtx.scope)
              have hLocalsControl := hExact.locals_sameControl cursor tail
              cases hPlacement with
              | stack slot planDepth hSlot hStack hLocation hOrder =>
                  have hExpectedMatches :=
                    hBoundary.semantic.invariant.compiler.mode_matches
                      |>.after_stack_declaration hOrder
                  have hExpectedSame :
                      SameFrame mode.afterStackDeclaration tailMode :=
                    (SameFrame.afterStackDeclaration mode).symm.trans hSame
                  have hModeEq := hExpectedSame.eq_of_matches
                    hExpectedMatches hAfterMatches
                  subst tailMode
                  rw [hExact.plan]
                  exact
                    (hBoundary.controlAgreement.after_stack_declaration
                      hSourceControl hLocalsControl rfl hOrder)
                      |>.transport_target hReturns
              | scratch slot hSlot hStack hLocation hOrder =>
                  have hExpectedMatches :=
                    hBoundary.semantic.invariant.compiler.mode_matches
                      |>.after_scratch_declaration hOrder
                  have hModeEq := hSame.eq_of_matches
                    hExpectedMatches hAfterMatches
                  subst tailMode
                  rw [hExact.plan]
                  exact
                    (hBoundary.controlAgreement.after_scratch_declaration
                      hSourceControl hLocalsControl hOrder)
                      |>.transport_target hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

theorem brk
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra
      targetDepth : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .brk :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.brk_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSourceScope hTargetDepth hTransition hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase beforeMode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .brk source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx = { sourceCtx with
        scope := Functions.Scope.Stmt.outEnv live .brk } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `continue` with semantic and allocator preservation. -/
theorem cont
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra
      targetDepth : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .cont :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.cont_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSourceScope hTargetDepth hTransition hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase beforeMode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .cont source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx = { sourceCtx with
        scope := Functions.Scope.Stmt.outEnv live .cont } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive function leave with ordered return-resource preservation. -/
theorem leave
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .leave :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ root.returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ root.returns → name ∈ functionScope)
    (hTargetDepth : beforeLocals.leaveDepth? = some 0)
    (hRetc : beforeLocals.leaveRetc = root.returns.length)
    (hReturnFrame : target.returns ≠ [])
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .leave :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 4
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 4 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.leave_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSourceScope hReturnsLive hReturnsScope hTargetDepth hRetc
      hReturnFrame hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .leave source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with scope := Functions.Scope.Stmt.outEnv live .leave } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive plain terminal with allocator-safe terminal growth. -/
theorem terminal
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hMemory : Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .terminal kind :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.terminal_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hMemory hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.terminal kind) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.terminal kind) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive argument-bearing terminal with allocator-safe growth. -/
theorem terminalArgs
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
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hArgsSafe : AllocationInteractionSafety.ExprSeqSafe contract args source)
    (hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe
                contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source))
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .terminalArgs kind args :: rest } source)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.terminalArgs_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hArgsSafe hTerminalSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.terminalArgs kind args) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.terminalArgs kind args) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_executionSafe cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hExecutionSafe)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess hTailSafe =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess hTailSafe)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult


end AllocationInteractionExecutionRuntime
end Functions
end EvmCompiler
