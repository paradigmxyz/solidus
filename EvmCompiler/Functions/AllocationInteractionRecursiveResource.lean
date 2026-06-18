import EvmCompiler.Functions.AllocationInteractionResourceComposition
import EvmCompiler.Functions.AllocationInteractionRecursive
import EvmCompiler.Functions.AllocationInteractionStatementResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursiveResource

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionRecursive
open AllocationInteractionResource
open AllocationInteractionResourceComposition

/-- Orthogonal allocator theorem for one canonical allocation cursor. -/
def CursorResourceAt
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (config : Config) (allocatorDepth sourceFuel targetExtra : Nat)
    (entryMode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  Simulation.Interaction.Rel
    (OpenResultRel config allocatorDepth entryMode target)
    (Functions.InteractionSemantics.Block.openRun program sourceCtx
      sourceFuel sourceBlock source)
    (Expressions.InteractionSemantics.Block.openRun expressions
      (targetBudget cursor sourceFuel targetExtra)
      { stmts := cursor.compiled } target)

/-- Semantic and allocator preservation over one shared interaction tree. -/
def CursorRuntimeAt
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (contract : MemoryContract.Contract)
    (config : Config) (allocatorDepth frameBase sourceFuel targetExtra : Nat)
    (entryMode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  let regularLive := Functions.Scope.Block.outEnv live sourceBlock
  let regularCtx := { sourceCtx with scope := regularLive }
  Simulation.Interaction.Rel
    (fun sourceDone targetDone =>
      OpenControlResultRel contract root.lowerCtx cursor.finalState
          cursor.finalLocals cursor.plan root.returns regularLive frameBase
          entryMode sourceCtx regularCtx sourceDone targetDone ∧
        OpenResultRel config allocatorDepth entryMode target
          sourceDone targetDone)
    (Functions.InteractionSemantics.Block.openRun program sourceCtx
      sourceFuel sourceBlock source)
    (Expressions.InteractionSemantics.Block.openRun expressions
      (targetBudget cursor sourceFuel targetExtra)
      { stmts := cursor.compiled } target)

namespace CursorRuntimeAt

theorem combine
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx}
    {contract : MemoryContract.Contract}
    {config : Config}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {entryMode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSemantic :
      CursorForwardAt cursor contract frameBase sourceFuel targetExtra
        entryMode sourceCtx source target)
    (hResource :
      CursorResourceAt cursor config allocatorDepth sourceFuel targetExtra
        entryMode sourceCtx source target) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra entryMode sourceCtx source target := by
  exact Simulation.Interaction.Rel.inter hSemantic hResource

theorem semantic
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {entryMode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRuntime :
      CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
        targetExtra entryMode sourceCtx source target) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      entryMode sourceCtx source target :=
  Simulation.Interaction.Rel.mono hRuntime (fun _ _ hDone => hDone.1)

theorem resource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {entryMode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRuntime :
      CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
        targetExtra entryMode sourceCtx source target) :
    CursorResourceAt cursor config allocatorDepth sourceFuel targetExtra
      entryMode sourceCtx source target :=
  Simulation.Interaction.Rel.mono hRuntime (fun _ _ hDone => hDone.2)

/-- Compose one exact runtime cursor head with its recursive tail. -/
theorem cons_of_parts
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth childFuel targetExtra frameBase : Nat}
    {entryMode : ActivationMode}
    {sourceCtx midCtx : Functions.Source.Ctx}
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
    (hMidCtx :
      midCtx =
        { sourceCtx with scope := Functions.Scope.Stmt.outEnv live stmt })
    (hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (Functions.Scope.Stmt.outEnv live stmt)
          frameBase entryMode sourceCtx midCtx config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor (childFuel + 1) targetExtra)
          { stmts := headCode } target))
    (hTailForward :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase mode sourceMid targetMid →
          AllocatorReady config allocatorDepth targetMid →
          SameFrame entryMode mode →
          CursorRuntimeAt tail contract config allocatorDepth frameBase
            childFuel (targetExtra + 8) mode midCtx sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase
      (childFuel + 1) targetExtra entryMode sourceCtx source target := by
  let finalLive :=
    Functions.Scope.Block.outEnv
      (Functions.Scope.Stmt.outEnv live stmt) { stmts := rest }
  rcases hTail with ⟨hPlan, hFinalState, hFinalLocals⟩
  have hComposed :=
    AllocationInteractionResourceComposition.block_cons
      (rest := rest) (headCode := headCode) (tailCode := tail.compiled)
      (plan := cursor.plan)
      (finalLowerCtx := root.lowerCtx)
      (finalLowerState := cursor.finalState)
      (finalLocals := cursor.finalLocals)
      (finalLive := finalLive)
      (finalCtx := { sourceCtx with scope := finalLive })
      (sourceFuel := childFuel)
      (targetFuel := targetBudget cursor (childFuel + 1) targetExtra)
      hHead
      (fun {sourceMid targetMid mode} hInvariant hReady hSame => by
        have hInvariantTail :
            AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan
              (Functions.Scope.Stmt.outEnv live stmt)
              frameBase mode sourceMid targetMid := by
          simpa [hPlan] using hInvariant
        have hRecursive := hTailForward hInvariantTail hReady hSame
        unfold CursorRuntimeAt at hRecursive
        rw [hPlan, hFinalState, hFinalLocals] at hRecursive
        have hTargetFuel :
            targetBudget cursor (childFuel + 1) targetExtra -
                headCode.length =
              targetBudget tail childFuel (targetExtra + 8) := by
          simp [targetBudget, hCompiled]
          omega
        have hFinalCtx :
            { midCtx with scope := finalLive } =
              { sourceCtx with scope := finalLive } := by
          rw [hMidCtx]
        simpa [CursorRuntimeAt, finalLive,
          hTargetFuel, hFinalCtx] using hRecursive)
  unfold CursorRuntimeAt
  rw [hCompiled]
  simpa [finalLive] using hComposed

end CursorRuntimeAt

/--
Dynamic allocator facts paired with the existing semantic recursive boundary.
This is internal proof state derived from the compiler's frame configuration;
it is not source semantics or public generated evidence.
-/
structure Boundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor : CoreCursor root scope live sourceBlock lowerState localsCtx)
    (contract : MemoryContract.Contract)
    (globalFrameWords : Nat) (config : Config) (allocatorDepth frameBase : Nat)
    (mode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop where
  semantic :
    AllocationInteractionRecursive.Boundary cursor contract frameBase mode
      sourceCtx source target
  configEq :
    AllocationSupport.scratchFrameConfig? contract globalFrameWords =
      some config
  ready : AllocatorReady config allocatorDepth target
  owned : ActivationOwned config allocatorDepth frameBase mode
  budget : AllocationInteractionFrame.Budget config allocatorDepth

/-- One compiler decomposition supplies both expression-head capabilities. -/
theorem CoreCursor.expr_runtime_head
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
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.expr expr) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  have hExprScoped : Functions.Scope.ExprScoped live expr := by
    simpa [Functions.Scope.Stmt.Scoped] using hScoped
  have hSemantic :=
    AllocationInteractionLeaf.expr_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSafe hExprScoped hLower hCompile hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionStatementResource.expr_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hBoundary.configEq hSafe hExprScoped hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/-- One compiler decomposition supplies both assignment-head capabilities. -/
theorem CoreCursor.assign_runtime_head
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
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.assign name value) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionLeaf.assign_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSafe hScoped.2 hScoped.1 hLower hCompile hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionStatementResource.assign_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hBoundary.configEq hSafe hScoped.2 hScoped.1 hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready hBoundary.owned
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

namespace CursorRuntimeAt

/-- Recursive expression statement with semantic and allocator preservation. -/
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
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + 8) tailMode sourceCtx
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
    simp [headExtra, totalFuel, targetBudget]
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
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget })
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
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + 8) tailMode sourceCtx
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
    simp [headExtra, totalFuel, targetBudget]
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
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget })
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

end CursorRuntimeAt

namespace CursorResourceAt

/-- The empty cursor is allocator-neutral. -/
theorem nil
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Config} {allocatorDepth sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := [] } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hReady : AllocatorReady config allocatorDepth target) :
    CursorResourceAt cursor config allocatorDepth sourceFuel targetExtra mode
      sourceCtx source target := by
  have hLower := cursor.lower
  simp [AllocationLowering.lowerBlockOpen,
    AllocationLowering.lowerStmtList] at hLower
  obtain ⟨hLowered, _hFinalState⟩ := hLower
  have hCompile := cursor.compile
  rw [← hLowered] at hCompile
  simp [Locals.Block.compileOpen] at hCompile
  obtain ⟨hCompiled, _hFinalLocals⟩ := hCompile
  have hTargetFuel :
      0 < targetBudget cursor sourceFuel targetExtra := by
    simp [targetBudget]
  have hSourceEq : sourceFuel - 1 + 1 = sourceFuel := by omega
  have hTargetEq :
      targetBudget cursor sourceFuel targetExtra - 1 + 1 =
        targetBudget cursor sourceFuel targetExtra := by omega
  have hSourceRun :=
    Functions.InteractionSemantics.Block.openRun_nil
      program sourceCtx (sourceFuel - 1) source
  rw [hSourceEq] at hSourceRun
  have hTargetRun :=
    Expressions.InteractionSemantics.Block.openRun_nil
      expressions (targetBudget cursor sourceFuel targetExtra - 1) target
  rw [hTargetEq] at hTargetRun
  unfold CursorResourceAt
  rw [hSourceRun, hCompiled, hTargetRun]
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok
      (ActivationEffect.refl hReady))

end CursorResourceAt

end AllocationInteractionRecursiveResource
end Functions
end EvmCompiler
