import EvmCompiler.Functions.AllocationInteractionCall
import EvmCompiler.Functions.AllocationInteractionForward

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursive

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCursor
open AllocationInteractionCall

/-- Uniform target budget used by the recursive allocation proof. -/
def targetBudget
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
    (sourceFuel targetExtra : Nat) : Nat :=
  targetExtra + cursor.compiled.length + 8 * (sourceFuel + 1)

/-- Exact adjacent preservation statement for one canonical allocation cursor. -/
def CursorForwardAt
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
    (frameBase sourceFuel targetExtra : Nat)
    (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  let regularLive := Functions.Scope.Block.outEnv live sourceBlock
  let regularCtx := { sourceCtx with scope := regularLive }
  Simulation.Interaction.Rel
    (OpenControlResultRel contract root.lowerCtx cursor.finalState
      cursor.finalLocals cursor.plan root.returns regularLive frameBase
      sourceCtx regularCtx)
    (Functions.InteractionSemantics.Block.openRun program sourceCtx
      sourceFuel sourceBlock source)
    (Expressions.InteractionSemantics.Block.openRun expressions
      (targetBudget cursor sourceFuel targetExtra)
      { stmts := cursor.compiled } target)

/-- Runtime facts shared by every recursive cursor constructor. -/
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
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (contract : MemoryContract.Contract)
    (frameBase : Nat) (mode : ActivationMode)
    (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop where
  invariant :
    AllocationContext.ActivationInvariant contract root.lowerCtx lowerState
      localsCtx cursor.plan live frameBase mode source target
  sourceScope : sourceCtx.scope = live
  capacity : AllocationInteractionForward.FrameCapacity compilation mode

namespace CursorForwardAt

/-- The empty canonical cursor preserves the boundary at every target slack. -/
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
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := [] } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
  have hLower := cursor.lower
  simp [AllocationLowering.lowerBlockOpen,
    AllocationLowering.lowerStmtList] at hLower
  obtain ⟨hLowered, _hFinalState⟩ := hLower
  have hCompile := cursor.compile
  rw [← hLowered] at hCompile
  simp [Locals.Block.compileOpen] at hCompile
  obtain ⟨hCompiled, _hFinalLocals⟩ := hCompile
  have hCtx : { sourceCtx with scope := live } = sourceCtx := by
    cases sourceCtx
    have hScope := hBoundary.sourceScope
    simp only at hScope
    cases hScope
    rfl
  have hFuel : sourceFuel - 1 + 1 = sourceFuel := by omega
  have hLive :
      Functions.Scope.Block.outEnv live { stmts := [] } = live := rfl
  have hForward :=
    AllocationInteractionForward.CoreCursor.nil
      (sourceFuel := sourceFuel - 1)
      (targetFuel := targetBudget cursor sourceFuel targetExtra - 1)
      (ctx := sourceCtx) cursor hBoundary.invariant
  have hTargetFuel :
      targetBudget cursor sourceFuel targetExtra - 1 + 1 =
        targetBudget cursor sourceFuel targetExtra := by
    simp [targetBudget, hCompiled]
    omega
  simpa [CursorForwardAt, hCompiled, hCtx, hFuel, hLive,
    hTargetFuel] using hForward

/-- Compose one exact cursor head with a uniformly budgeted recursive tail. -/
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
    {contract : MemoryContract.Contract}
    {childFuel targetExtra frameBase : Nat}
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
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live stmt })
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns
          (Functions.Scope.Stmt.outEnv live stmt) frameBase sourceCtx midCtx)
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
          CursorForwardAt tail contract frameBase childFuel
            (targetExtra + 8) midCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase (childFuel + 1) targetExtra
      sourceCtx source target := by
  let finalLive :=
    Functions.Scope.Block.outEnv
      (Functions.Scope.Stmt.outEnv live stmt) { stmts := rest }
  have hComposed :=
    AllocationInteractionForward.CoreCursor.cons_of_parts
      (finalLive := finalLive)
      (sourceCtx := sourceCtx) (midCtx := midCtx)
      (finalCtx := { sourceCtx with scope := finalLive })
      (sourceFuel := childFuel)
      (targetFuel := targetBudget cursor (childFuel + 1) targetExtra)
      cursor tail hTail hCompiled hHead
      (fun {sourceMid targetMid mode} hInvariant => by
        have hRecursive := hTailForward hInvariant
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
        simpa [CursorForwardAt, finalLive, hTargetFuel, hFinalCtx] using
          hRecursive)
  simpa [CursorForwardAt, finalLive] using hComposed

/-- Recursive expression-statement constructor over the canonical cursor. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
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
    AllocationInteractionForward.CoreCursor.expr_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
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
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive assignment constructor over the canonical cursor. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
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
    AllocationInteractionForward.CoreCursor.assign_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
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
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive declaration constructor in stack or scratch representation. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope (name :: live) { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan (name :: live) frameBase
              tailMode sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8)
              { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
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
    AllocationInteractionForward.CoreCursor.let_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.capacity hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase
          sourceCtx nextCtx)
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
    have hScope := hBoundary.sourceScope
    simp only at hScope
    cases hScope
    rfl
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `break` constructor with loop-destination cleanup. -/
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
    {frameBase sourceFuel targetExtra targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
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
      Boundary cursor contract frameBase beforeMode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.brk_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSourceScope hTargetDepth hTransition hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .brk source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live .brk } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `continue` constructor with loop-destination cleanup. -/
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
    {frameBase sourceFuel targetExtra targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
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
      Boundary cursor contract frameBase beforeMode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.cont_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSourceScope hTargetDepth hTransition hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .cont source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live .cont } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive plain-terminal constructor with source-facing memory safety. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hMemory :
      Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.terminal_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hMemory hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
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
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive argument-bearing terminal constructor. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
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
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.terminalArgs_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hArgsSafe hTerminalSafe hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
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
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive function `leave` constructor with ordered return emission. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
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
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + 8) sourceCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 4
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 4 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.leave_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSourceScope hReturnsLive hReturnsScope hTargetDepth hRetc
      hReturnFrame hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .leave source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live .leave } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail hExact hCompiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail hExact hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

end CursorForwardAt

namespace SelectedCallee

/--
Compose compiler-selected callee setup with preservation of its canonical body
cursor. The body premise is the strictly smaller source-fuel induction use;
it is not a public call oracle and mentions no alternate compiler artifact.
-/
theorem body_of_cursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared :
      AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel fuelBound : Nat}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase artifact.mode source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation)
    (hSourceFuel : sourceFuel < fuelBound)
    (hBodyForward :
      ∀ {bodyTarget : Structured.RunState},
        sourceFuel < fuelBound →
        AllocationContext.ActivationInvariant contract artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase prepared.bodyMode source bodyTarget →
          CursorForwardAt (prepared.rootCursor hProgramScoped) contract
            frameBase sourceFuel 0 sourceCtx source bodyTarget) :
    ∃ targetFuel,
      0 < targetFuel ∧
      Simulation.Interaction.Rel
        (OpenControlResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            fn.body)
          frameBase sourceCtx
          { sourceCtx with
            scope :=
              Functions.Scope.Block.outEnv
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)
                fn.body })
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          { stmts :=
              prepared.markerCode ++ prepared.paramCode ++
                prepared.returnCode ++ prepared.bodyCode }
          target) := by
  let live :=
    (artifact.slots.returns.map Prod.fst).reverse ++
      (artifact.slots.params.map Prod.fst).reverse
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hScratchEntry :
        ActivationCalleeEntryRel contract prepared.plan []
          artifact.slots.params frameBase
          (.scratch 0 compilation.recipe.frameWords) source target := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrame] using hEntry
    obtain
        ⟨_afterParams, bodyTarget, _paramFuel, _returnFuel, _preludeFuel,
          _hParamFuel, _hReturnFuel, _hMarkers, _hParams, _hReturns,
          _hPreludeFuel, _hPreludeLength, _hPrelude,
          hPreludeAt, hInvariant⟩ :=
      prepared.body_entry_scratch hNeedsFrame hScratchEntry hZero
        hStackLength hReservation
    have hBody := hBodyForward hSourceFuel hInvariant
    let bodyFuel :=
      targetBudget (prepared.rootCursor hProgramScoped) sourceFuel 0
    have hBodyFuel : 0 < bodyFuel := by
      simp [bodyFuel, targetBudget]
    let targetFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨targetFuel, by simp [targetFuel]; omega, ?_⟩
    exact
      prepared.prelude_then_body hBodyFuel hPreludeAt
        (by simpa [CursorForwardAt, bodyFuel] using hBody)
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hStackEntry :
        ActivationCalleeEntryRel contract prepared.plan []
          artifact.slots.params frameBase .stack source target := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrameFalse] using hEntry
    obtain
        ⟨_afterParams, bodyTarget, _paramFuel, _returnFuel, _preludeFuel,
          _hParamFuel, _hReturnFuel, _hMarkers, _hParams, _hReturns,
          _hPreludeFuel, _hPreludeLength, _hPrelude,
          hPreludeAt, hInvariant⟩ :=
      prepared.body_entry_stack hNeedsFrameFalse hStackEntry hZero
        hStackLength
    have hBody := hBodyForward hSourceFuel hInvariant
    let bodyFuel :=
      targetBudget (prepared.rootCursor hProgramScoped) sourceFuel 0
    have hBodyFuel : 0 < bodyFuel := by
      simp [bodyFuel, targetBudget]
    let targetFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨targetFuel, by simp [targetFuel]; omega, ?_⟩
    exact
      prepared.prelude_then_body hBodyFuel hPreludeAt
        (by simpa [CursorForwardAt, bodyFuel] using hBody)

end SelectedCallee

end AllocationInteractionRecursive
end Functions
end EvmCompiler
