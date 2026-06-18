import EvmCompiler.Functions.AllocationInteractionResourceComposition
import EvmCompiler.Functions.AllocationInteractionRecursive
import EvmCompiler.Functions.AllocationInteractionStatementResource
import EvmCompiler.Functions.AllocationInteractionAbruptResource
import EvmCompiler.Functions.AllocationInteractionControlResource

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

/-- One compiler decomposition supplies both declaration-head capabilities. -/
theorem CoreCursor.let_runtime_head
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
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope (name :: live) { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns (name :: live) frameBase mode
              sourceCtx { sourceCtx with scope := name :: sourceCtx.scope }
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.let_ name value) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  obtain ⟨afterMode, hAfter, hTransition⟩ :=
    cursor.letContext tail hPlanning hPlan
      hBoundary.semantic.invariant.compiler hLower hCompile
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
    have hCapacity := hBoundary.semantic.capacity
    rw [hMode] at hCapacity
    exact
      lt_of_lt_of_le
        (cursor.scratch_bound_of_location hLocation)
        hCapacity
  have hSemantic :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase mode sourceCtx
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
                    hSafe hAfterStack hScoped.2 hLower hCompile
                    hBoundary.semantic.invariant
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
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
        | scratch frameDepth frameWords slot hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionLeaf.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterScratch hScoped.2 rfl hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
  have hResource :
      Simulation.Interaction.Rel
        (OpenResultRel config allocatorDepth mode target)
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
                  AllocationInteractionStatementResource.stack_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hBoundary.configEq hSafe hAfterStack hScoped.2 hLower
                    hCompile hBoundary.semantic.invariant hBoundary.ready
    | scratch frameDepth frameWords =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionStatementResource.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hBoundary.configEq hSafe hAfterScratch hScoped.2 rfl
                    hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
                    hBoundary.ready hBoundary.owned
        | scratch frameDepth frameWords slot hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionStatementResource.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hBoundary.configEq hSafe hAfterScratch hScoped.2 rfl
                    hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
                    hBoundary.ready hBoundary.owned
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/-- One cursor decomposition supplies both `break` head capabilities. -/
theorem CoreCursor.brk_runtime_head
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
    {globalFrameWords allocatorDepth sourceFuel targetExtra targetDepth
      frameBase : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
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
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase beforeMode sourceCtx
              sourceCtx config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .brk source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionAbrupt.brk_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionAbruptResource.brk_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/-- One cursor decomposition supplies both `continue` head capabilities. -/
theorem CoreCursor.cont_runtime_head
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
    {globalFrameWords allocatorDepth sourceFuel targetExtra targetDepth
      frameBase : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
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
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase beforeMode sourceCtx
              sourceCtx config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .cont source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionAbrupt.cont_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionAbruptResource.cont_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
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
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + 8) tailMode
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
    simp [headExtra, totalFuel, targetBudget]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
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
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame =>
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
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget })
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive lexical block with exact cleanup and allocator preservation. -/
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
    (cursor :
      CoreCursor root scope live { stmts := .block body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        (bodyExtra : Nat),
        Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx source target →
          CursorRuntimeAt bodyCursor contract config allocatorDepth frameBase
            (sourceFuel - 1) bodyExtra mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
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
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  obtain
      ⟨afterState, headCode, tail, targetBlock, bodyCursor,
        hCompiled, hHeadCode, hFinish, hAfterEnv, hAfterLayout,
        _hTransport, hExact⟩ := cursor.blockCursors
  have hBodyAgree :
      PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hBodyInvariant :=
    hBoundary.semantic.invariant.transport_plan
      hBodyAgree.symm bodyCursor.planWF
  have hBodyBoundary :
      Boundary bodyCursor contract globalFrameWords config allocatorDepth
        frameBase mode sourceCtx source target :=
    { semantic :=
        { invariant := hBodyInvariant
          sourceScope := hBoundary.semantic.sourceScope
          control := hBoundary.semantic.control
          capacity := hBoundary.semantic.capacity }
      configEq := hBoundary.configEq
      ready := hBoundary.ready
      owned := hBoundary.owned
      budget := hBoundary.budget }
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
  have hHeadLength :
      headCode.length = bodyCursor.compiled.length + 1 := by
    rw [hHeadCode, hTargetShape, List.length_append]
    simp
  have hCompiledLength := congrArg List.length hCompiled
  simp only [List.length_append] at hCompiledLength
  let bodyBase := bodyCursor.compiled.length + 8 * (childFuel + 1)
  let bodyExtra := totalFuel - bodyBase
  have hBodyBase : bodyBase ≤ totalFuel := by
    simp [bodyBase, totalFuel, targetBudget]
    omega
  have hBodyBudget :
      targetBudget bodyCursor childFuel bodyExtra = totalFuel := by
    simp [targetBudget, bodyExtra, bodyBase]
    omega
  have hBodyRecursive :=
    hBodyForward bodyCursor bodyExtra hBodyBoundary
  have hBodyRel :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx bodyCursor.finalState
          bodyCursor.finalLocals bodyCursor.plan root.returns
          (Functions.Scope.Block.outEnv live body) frameBase mode sourceCtx
          { sourceCtx with scope := Functions.Scope.Block.outEnv live body }
          config allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx childFuel body source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := bodyCursor.compiled } target) := by
    simpa [CursorRuntimeAt, childFuel, hBodyBudget] using hBodyRecursive
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state hAfterEnv hAfterLayout
  have hExtends :
      AllocationLowering.StateExtends live beforeState bodyCursor.finalState :=
    AllocationLowering.lowerBlockOpen_stateExtends
      bodyCursor.sourceScoped bodyCursor.lower
  have hExtendsAfter :
      AllocationLowering.StateExtends live afterState bodyCursor.finalState := by
    rcases hExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
    refine ⟨dropped, ?_, hFresh, ?_⟩
    · rw [hLayout, hAfterLayout]
    · intro name hLive
      exact (hSlots name hLive).trans
        (congrArg (AllocationSupport.lookupSlot? name) hAfterEnv.symm)
  have hCleanupFuel :
      2 ≤ totalFuel - bodyCursor.compiled.length := by
    simp [totalFuel, targetBudget]
    omega
  have hSemantic :=
    AllocationInteractionControl.block_of_components
      (bodyLive := Functions.Scope.Block.outEnv live body)
      hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
      hAfterInvariant hExtendsAfter hBodyAgree hFinish hCleanupFuel
      (Simulation.Interaction.Rel.mono hBodyRel
        (fun _ _ hDone => hDone.1))
  have hResource :=
    AllocationInteractionControlResource.block_of_components
      hBoundary.semantic.sourceScope hFinish hCleanupFuel hBodyRel
  have hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          targetBlock target) :=
    Simulation.Interaction.Rel.inter hSemantic hResource
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    cases targetBlock
    simpa [hHeadCode] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.block body) } := by
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

/-- Recursive `break` with semantic and allocator preservation. -/
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
      targetExtra beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
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
      targetExtra beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
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
