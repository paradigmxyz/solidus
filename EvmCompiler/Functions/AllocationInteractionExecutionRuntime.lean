import EvmCompiler.Functions.AllocationInteractionRecursiveResource
import EvmCompiler.Functions.AllocationInteractionRecursiveCallResource
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

/-- A reached lexical block carries reservation safety into both its body and
its regular continuation. No safety fact is requested for an unrelated body,
state, or open-world response. -/
theorem block
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .block body :: rest } beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hReserve : AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .block body :: rest } source)
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        (bodyExtra : Nat),
        AllocationInteractionTargetFuel.Reserve bodyCursor bodyExtra →
          Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx source target →
          AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
            program sourceCtx (sourceFuel - 1) body source →
          CursorRuntimeAt bodyCursor contract config allocatorDepth frameBase
            (sourceFuel - 1) bodyExtra mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth
              frameBase tailMode sourceCtx sourceMid targetMid →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  exact CursorRuntimeAt.block cursor hSourceFuel hReserve hBoundary
    hExecutionSafe.ordinarySuccessful hExecutionSafe
    (fun bodyCursor bodyExtra hBodyReserve hBodyBoundary hBodySuccess
        hBodySafe =>
      hBodyForward bodyCursor bodyExtra hBodyReserve hBodyBoundary hBodySafe)
    (fun {afterState} tail hExact {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess hTailSafe =>
      hTailForward tail hExact hTailBoundary hTailSafe)

/-- Conditional preservation follows the guarded condition outcome that
actually selects the body and then carries safety through the reached tail. -/
theorem if_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .if_ cond body :: rest } beforeState beforeLocals)
    (hSourceFuel : 1 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hReserve : AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel { stmts := .if_ cond body :: rest } source)
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        {sourceAfter targetAfter},
        targetBudget bodyCursor (sourceFuel - 2)
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
            targetBudget cursor sourceFuel targetExtra - 2 →
          Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx sourceAfter targetAfter →
          AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
            program sourceCtx (sourceFuel - 2) body sourceAfter →
          2 ≤
              (targetBudget cursor sourceFuel targetExtra - 2) -
                bodyCursor.compiled.length ∧
            Simulation.Interaction.Rel
              (RuntimeResultRel contract root.lowerCtx
                bodyCursor.finalState bodyCursor.finalLocals bodyCursor.plan
                root.returns (Functions.Scope.Block.outEnv live body)
                frameBase mode sourceCtx
                { sourceCtx with
                  scope := Functions.Scope.Block.outEnv live body }
                config allocatorDepth targetAfter)
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 2) body sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetBudget cursor sourceFuel targetExtra - 2)
                { stmts := bodyCursor.compiled } targetAfter))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth
              frameBase tailMode sourceCtx sourceMid targetMid →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  exact CursorRuntimeAt.if_ cursor hSourceFuel hReserve hBoundary
    hExecutionSafe.ordinarySuccessful hExecutionSafe
    (fun bodyCursor {sourceAfter targetAfter} hTargetCapacity hBodyBoundary
        hBodySuccess hBodySafe =>
      hBodyForward bodyCursor hTargetCapacity hBodyBoundary hBodySafe)
    (fun {afterState} tail hExact {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess hTailSafe =>
      hTailForward tail hExact hTailBoundary hTailSafe)

/-- Switch preservation carries guarded success only into the compiler-selected
source branch and its reached regular continuation. -/
theorem switch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .switch scrutinee cases defaultBody :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 1 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hReserve : AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel
          { stmts := .switch scrutinee cases defaultBody :: rest } source)
    (hBodyForward :
      ∀ {value : Word} {selected : Functions.Block}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (hSelect :
          Functions.Source.Switch.select value cases defaultBody =
            some selected)
        (bodyCursor :
          CoreCursor root (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart beforeLocals)
        {sourceAfter targetAfter},
        targetBudget bodyCursor (sourceFuel - 2)
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
            targetBudget cursor sourceFuel targetExtra - 2 →
          Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx sourceAfter targetAfter →
          AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
            program sourceCtx (sourceFuel - 2) selected sourceAfter →
          2 ≤
              (targetBudget cursor sourceFuel targetExtra - 2) -
                bodyCursor.compiled.length ∧
            Simulation.Interaction.Rel
              (RuntimeResultRel contract root.lowerCtx
                bodyCursor.finalState bodyCursor.finalLocals bodyCursor.plan
                root.returns (Functions.Scope.Block.outEnv live selected)
                frameBase mode sourceCtx
                { sourceCtx with
                  scope := Functions.Scope.Block.outEnv live selected }
                config allocatorDepth targetAfter)
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 2) selected sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetBudget cursor sourceFuel targetExtra - 2)
                { stmts := bodyCursor.compiled } targetAfter))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth
              frameBase tailMode sourceCtx sourceMid targetMid →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  exact CursorRuntimeAt.switch cursor hSourceFuel hReserve hBoundary
    hExecutionSafe.ordinarySuccessful hExecutionSafe
    (fun {value selected selectedStart selectedPlanning} hSelect bodyCursor
        {sourceAfter targetAfter} hTargetCapacity hBodyBoundary hBodySuccess
        hBodySafe =>
      hBodyForward hSelect bodyCursor hTargetCapacity hBodyBoundary hBodySafe)
    (fun {afterState} tail hExact {sourceMid targetMid tailMode} hTailBoundary
        hTailSuccess hTailSafe =>
      hTailForward tail hExact hTailBoundary hTailSafe)

/-- A reached `for` carries guarded success through initializer, condition,
body, post, recursive iterations, and its regular continuation using the shared
parameterized loop owner. -/
theorem for_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .for_ init cond post body :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 2 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
        program sourceCtx sourceFuel
          { stmts := .for_ init cond post body :: rest } source)
    (hRecursive :
      ExecutionSafeRecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (hCapacity :
      ForFuelCapacity cursor.forArtifact (sourceFuel - 2)
        ((targetBudget cursor sourceFuel targetExtra - 2) -
          (sourceFuel - 2)))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth
              frameBase tailMode sourceCtx sourceMid targetMid →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe contract
              program sourceCtx (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  exact CursorRuntimeAt.for_ cursor hSourceFuel hBoundary hFuelBudget
    hExecutionSafe hRecursive hCapacity
    (fun {afterState} tail hExact {sourceMid targetMid tailMode} hTailBoundary
        hTailSafe =>
      hTailForward tail hExact hTailBoundary hTailSafe)

/-- A reached internal call derives local argument safety from its guarded
execution, preserves the compiler-selected stack or scratch callee frame, and
restores the dormant caller frame before its regular continuation. -/
theorem call
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx)
    (hProgramScoped : program.Scoped)
    (hSourceFuel : 2 < sourceFuel)
    (hBoundary :
      Boundary cursor program.memoryContract compilation.recipe.frameWords config
        allocatorDepth frameBase mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config
        (allocatorDepth + sourceFuel))
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe
        program.memoryContract program sourceCtx sourceFuel
          { stmts := .call targets functionName args :: rest } source)
    (hRecursive :
      ExecutionSafeRecursiveOpenRuntime (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords sourceFuel)
    (hTailForward :
      ∀ (tail : CoreCursor root scope live { stmts := rest }
          lowerState localsCtx),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail program.memoryContract compilation.recipe.frameWords config
              allocatorDepth frameBase tailMode sourceCtx sourceMid
              targetMid →
            AllocationInteractionSafeSemantics.Block.ExecutionSafe
              program.memoryContract program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid →
            CursorRuntimeAt tail program.memoryContract config allocatorDepth
              frameBase (sourceFuel - 1)
                (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    CursorRuntimeAt cursor program.memoryContract config allocatorDepth
      frameBase sourceFuel targetExtra mode sourceCtx source target := by
  have hHeadSafe :=
    AllocationInteractionSafeSuccessful.successful_head
      (contract := program.memoryContract) (program := program)
      (stmt := .call targets functionName args) (rest := rest)
      (by omega) hExecutionSafe
  have hTargets : targets.Nodup := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.1
  have hHeadFuelEq : sourceFuel - 2 + 1 = sourceFuel - 1 := by omega
  have hCallContinuations :=
    AllocationInteractionSafeSemantics.Stmt.successful_openRun_call_continuations
      program.memoryContract program sourceCtx (sourceFuel - 2) targets
      functionName args source hTargets
      (by simpa [hHeadFuelEq] using hHeadSafe)
  have hArgSuccess :
      Simulation.Interaction.Successful
        (AllocationInteractionSafeSemantics.ArgList.openEval
          program.memoryContract args source) := by
    apply Simulation.Interaction.AllDone.mono hCallContinuations
    intro outcome hOutcome
    cases outcome with
    | error _ => exact hOutcome
    | ok _ => trivial
  have hArgsScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg := by
    simpa [Functions.Scope.Stmt.Scoped] using cursor.headScoped.2.2
  have hArgSafe :=
    AllocationInteractionSafety.argList_of_successful hArgsScoped
      hBoundary.semantic.invariant.defined hArgSuccess
  exact
    AllocationInteractionRecursiveCallResource.CursorRuntimeAt.call
      cursor hProgramScoped hSourceFuel hArgSafe hBoundary hFuelBudget
      hHeadSafe hExecutionSafe hRecursive
      (fun tail hExact {sourceMid targetMid tailMode} hTailBoundary
          _hTailSuccess hTailSafe =>
        hTailForward tail hExact hTailBoundary hTailSafe)


end AllocationInteractionExecutionRuntime
end Functions
end EvmCompiler
