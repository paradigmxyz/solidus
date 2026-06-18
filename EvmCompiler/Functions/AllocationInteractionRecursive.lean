import EvmCompiler.Functions.AllocationInteractionSelectedCallEntry
import EvmCompiler.Functions.AllocationInteractionFor
import EvmCompiler.Functions.AllocationInteractionForward
import EvmCompiler.Functions.AllocationInteractionTargetFuel

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursive

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCursor
open AllocationInteractionCall

/-- Whole-program target fuel reserved for one source-level recursive step.
The fixed administrative allowance covers local statement plumbing; the
procedure-body sum covers any compiler-selected internal callee. -/
def callStride (program : Expressions.Program) : Nat :=
  8 +
    (program.toStructured.procs.map fun proc => proc.body.stmts.length).sum +
    (program.toStructured.procs.map fun proc =>
      AllocationInteractionTargetFuel.structuredBlockSize proc.body).sum

theorem eight_le_callStride (program : Expressions.Program) :
    8 ≤ callStride program := by
  unfold callStride
  omega

private theorem proc_body_length_le_sum
    {proc : Structured.Proc} {procs : List Structured.Proc}
    (hMem : proc ∈ procs) :
    proc.body.stmts.length ≤
      (procs.map fun candidate => candidate.body.stmts.length).sum := by
  induction procs with
  | nil => simp at hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      simp only [List.map_cons, List.sum_cons]
      cases hMem with
      | inl hHead => subst head; omega
      | inr hTail =>
          have hBound := ih hTail
          omega

/-- Every procedure selected by the real target lookup fits in one stride. -/
theorem proc_body_length_add_eight_le_callStride
    {program : Expressions.Program} {name : Expressions.Name}
    {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name program.toStructured.procs =
        some proc) :
    proc.body.stmts.length + 8 ≤ callStride program := by
  have hMem := Structured.ProcList.mem_of_lookup? hLookup
  have hBody := proc_body_length_le_sum hMem
  simp only [callStride]
  omega

/-- A compiler-selected procedure body, including retained nested blocks, fits
inside one global recursive stride. -/
theorem proc_body_size_add_eight_le_callStride
    {program : Expressions.Program} {name : Expressions.Name}
    {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name program.toStructured.procs =
        some proc) :
    AllocationInteractionTargetFuel.structuredBlockSize proc.body + 8 ≤
      callStride program := by
  have hSize :=
    AllocationInteractionTargetFuel.structured_block_size_le_program hLookup
  unfold callStride
  omega

/-- Any contiguous body segment of a selected Expressions procedure fits in
the recursive stride. -/
theorem selected_body_code_size_le_callStride
    {program : Expressions.Program} {name : Expressions.Name}
    {proc : Expressions.Proc}
    {bodyPrefix bodyCode bodySuffix : List Expressions.Stmt}
    (hLookup :
      Structured.ProcList.lookup? name program.toStructured.procs =
        some proc.toStructured)
    (hBody :
      proc.body.stmts = bodyPrefix ++ bodyCode ++ bodySuffix) :
    AllocationInteractionTargetFuel.stmtListSize bodyCode ≤
      callStride program := by
  have hSegment :
      AllocationInteractionTargetFuel.stmtListSize bodyCode ≤
        AllocationInteractionTargetFuel.stmtListSize proc.body.stmts := by
    rw [hBody, AllocationInteractionTargetFuel.stmtListSize_append,
      AllocationInteractionTargetFuel.stmtListSize_append]
    omega
  have hStructured :=
    proc_body_size_add_eight_le_callStride (program := program) hLookup
  have hProcPreserved :
      AllocationInteractionTargetFuel.structuredBlockSize
          proc.toStructured.body =
        AllocationInteractionTargetFuel.stmtListSize proc.body.stmts := by
    change
      AllocationInteractionTargetFuel.structuredBlockSize
          proc.body.toStructured =
        AllocationInteractionTargetFuel.stmtListSize proc.body.stmts
    rw [AllocationInteractionTargetFuel.blockSize_toStructured]
    cases proc.body
    rfl
  omega

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
  targetExtra + cursor.compiled.length +
    callStride expressions * (sourceFuel + 1)

theorem targetBudget_mono_extra
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
    (sourceFuel : Nat) {beforeExtra afterExtra : Nat}
    (hExtra : beforeExtra ≤ afterExtra) :
    targetBudget cursor sourceFuel beforeExtra ≤
      targetBudget cursor sourceFuel afterExtra := by
  unfold targetBudget
  omega

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
    (entryMode : ActivationMode)
    (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  let regularLive := Functions.Scope.Block.outEnv live sourceBlock
  let regularCtx := { sourceCtx with scope := regularLive }
  Simulation.Interaction.Rel
    (OpenControlResultRel contract root.lowerCtx cursor.finalState
      cursor.finalLocals cursor.plan root.returns regularLive frameBase
      entryMode sourceCtx regularCtx)
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
  control :
    AllocationInteractionStatement.ControlScopesWithin
      root.returns live sourceCtx
  capacity : AllocationInteractionForward.FrameCapacity compilation mode

/--
Fuel-bounded recursive capability used internally by compound cursor
constructors. The whole-block owner constructs it by source-fuel induction;
it is not a public callee oracle or compiler premise.
-/
def RecursiveOpenForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    (contract : MemoryContract.Contract)
    (frameBase fuelBound : Nat) : Prop :=
  ∀ {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx),
    sourceFuel < fuelBound →
    Boundary cursor contract frameBase mode sourceCtx source target →
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        sourceFuel sourceBlock source) →
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target

namespace RecursiveOpenForward

/-- Instantiate the recursive capability at any sufficiently large exact fuel. -/
theorem at_targetFuel
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {contract : MemoryContract.Contract}
    {frameBase fuelBound : Nat}
    (hRecursive :
      RecursiveOpenForward (root := root) contract frameBase fuelBound)
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {sourceFuel targetFuel : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (hFuel : sourceFuel < fuelBound)
    (hTargetFuel : targetBudget cursor sourceFuel 0 ≤ targetFuel)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel sourceBlock source)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract root.lowerCtx cursor.finalState
        cursor.finalLocals cursor.plan root.returns
        (Functions.Scope.Block.outEnv live sourceBlock) frameBase mode
        sourceCtx
        { sourceCtx with
          scope := Functions.Scope.Block.outEnv live sourceBlock })
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        sourceFuel sourceBlock source)
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := cursor.compiled } target) := by
  let targetExtra := targetFuel - targetBudget cursor sourceFuel 0
  have hForward :=
    hRecursive cursor hFuel hBoundary hSuccess
      (targetExtra := targetExtra)
  have hExact :
      targetBudget cursor sourceFuel targetExtra = targetFuel := by
    simp [targetBudget, targetExtra, callStride, Nat.mul_succ]
      at hTargetFuel ⊢
    omega
  simpa [CursorForwardAt, hExact] using hForward

end RecursiveOpenForward

/-- Exact nested target-fuel obligations for one checked `for` artifact. -/
structure ForFuelCapacity
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx}
    (components : cursor.ForComponents)
    (loopFuel slack : Nat) : Prop where
  init :
    targetBudget components.initCursor loopFuel
        (AllocationInteractionTargetFuel.stmtListNestedSize
          components.initCursor.compiled) ≤
      loopFuel + slack
  post :
    ∀ fuel, fuel < loopFuel →
      targetBudget components.postCursor fuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            components.postCursor.compiled) ≤
        fuel + slack
  body :
    ∀ fuel, fuel < loopFuel →
      targetBudget components.bodyCursor fuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            components.bodyCursor.compiled) ≤
        fuel + slack

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
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra mode
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
    simp [targetBudget, hCompiled, callStride, Nat.mul_succ]
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
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live stmt })
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns
          (Functions.Scope.Stmt.outEnv live stmt) frameBase entryMode
          sourceCtx midCtx)
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
            (targetExtra + callStride expressions) mode
            midCtx sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase (childFuel + 1) targetExtra
      entryMode
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
              targetBudget tail childFuel
                (targetExtra + callStride expressions) := by
          simp [targetBudget, hCompiled, callStride, Nat.mul_succ]
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      mode sourceCtx source target := by
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
    AllocationInteractionForward.CoreCursor.expr_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      mode sourceCtx source target := by
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
    AllocationInteractionForward.CoreCursor.assign_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
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
              (targetExtra + callStride expressions) tailMode
              { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      mode sourceCtx source target := by
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
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.let_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.capacity hBoundary.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase
          mode sourceCtx nextCtx)
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

/-- Recursive lexical-block constructor with exact scoped cleanup. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .block body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        (bodyExtra : Nat),
        Boundary bodyCursor contract frameBase mode sourceCtx source target →
          CursorForwardAt bodyCursor contract frameBase (sourceFuel - 1)
            bodyExtra mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState beforeLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  obtain
      ⟨afterState, headCode, tail, targetBlock, bodyCursor,
        hCompiled, hHeadCode, hFinish, hAfterEnv, hAfterLayout,
        _hTransport, hExact⟩ :=
    cursor.blockCursors
  have hBodyAgree :
      PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hBodyInvariant :=
    hBoundary.invariant.transport_plan hBodyAgree.symm bodyCursor.planWF
  have hBodyBoundary :
      Boundary bodyCursor contract frameBase mode sourceCtx source target :=
    { invariant := hBodyInvariant
      sourceScope := hBoundary.sourceScope
      control := hBoundary.control
      capacity := hBoundary.capacity }
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
  have hHeadLength :
      headCode.length = bodyCursor.compiled.length + 1 := by
    rw [hHeadCode, hTargetShape, List.length_append]
    simp
  have hCompiledLength := congrArg List.length hCompiled
  simp only [List.length_append] at hCompiledLength
  let bodyBase :=
    bodyCursor.compiled.length + callStride expressions * (childFuel + 1)
  let bodyExtra := totalFuel - bodyBase
  have hBodyBase : bodyBase ≤ totalFuel := by
    simp only [totalFuel]
    rw [← hFuel]
    simp [bodyBase, targetBudget, callStride, Nat.mul_succ]
    omega
  have hBodyBudget :
      targetBudget bodyCursor childFuel bodyExtra = totalFuel := by
    calc
      targetBudget bodyCursor childFuel bodyExtra = bodyExtra + bodyBase := by
        simp [targetBudget, bodyBase]
        omega
      _ = totalFuel := by
        exact Nat.sub_add_cancel hBodyBase
  have hBodyRecursive :=
    hBodyForward bodyCursor bodyExtra hBodyBoundary
  have hBodyRel :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx bodyCursor.finalState
          bodyCursor.finalLocals bodyCursor.plan root.returns
          (Functions.Scope.Block.outEnv live body) frameBase mode sourceCtx
          { sourceCtx with
            scope := Functions.Scope.Block.outEnv live body })
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx childFuel body source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := bodyCursor.compiled } target) := by
    simpa [CursorForwardAt, childFuel, hBodyBudget] using hBodyRecursive
  have hAfterInvariant :=
    hBoundary.invariant.transport_state hAfterEnv hAfterLayout
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
    simp [totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  have hHead :=
    AllocationInteractionControl.block_of_components
      (bodyLive := Functions.Scope.Block.outEnv live body)
      hBoundary.sourceScope rfl rfl hBoundary.control hAfterInvariant
      hExtendsAfter hBodyAgree hFinish hCleanupFuel hBodyRel
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
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

/-- Recursive conditional constructor over one compiler-selected body cursor. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .if_ cond body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 2 < sourceFuel)
    (hCondSafe : AllocationInteractionSafety.ExprSafe contract cond source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        {sourceAfter targetAfter},
        Boundary bodyCursor contract frameBase mode sourceCtx
            sourceAfter targetAfter →
          2 ≤
              (targetBudget cursor sourceFuel targetExtra - 2) -
                bodyCursor.compiled.length ∧
            Simulation.Interaction.Rel
              (OpenControlResultRel contract root.lowerCtx
                bodyCursor.finalState bodyCursor.finalLocals bodyCursor.plan
                root.returns (Functions.Scope.Block.outEnv live body)
                frameBase mode sourceCtx
                { sourceCtx with
                  scope := Functions.Scope.Block.outEnv live body })
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 2) body sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetBudget cursor sourceFuel targetExtra - 2)
                { stmts := bodyCursor.compiled } targetAfter))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState beforeLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let bodyFuel := sourceFuel - 2
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let targetBodyFuel := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hBodyFuel : bodyFuel + 1 = childFuel := by
    simp [bodyFuel, childFuel]
    omega
  have hTargetFuel : targetBodyFuel + 2 = totalFuel := by
    simp [targetBodyFuel, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, headLower, headCode, tail, loweredCond, condCode,
        targetBody, bodyCursor, hCompiled, _hLower, _hCompile,
        hHeadCode, hLowerCond, hCompileCond, hFinish, hAfterEnv,
        hAfterLayout, hCondScoped, hExact⟩ :=
    cursor.ifCursors
  have hBodyAgree : PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hAfterInvariant :=
    hBoundary.invariant.transport_state hAfterEnv hAfterLayout
  have hCond :=
    AllocationInteractionExpressionRecursive.forwardCondition
      hCondSafe hBoundary.invariant.compiler hCondScoped hLowerCond
      hCompileCond hBoundary.invariant.state
  have hVars :=
    Locals.InteractionStatePreservation.expr_openEvalCondition_vars
      cond source
  have hExtendsBefore :
      AllocationLowering.StateExtends live beforeState bodyCursor.finalState :=
    AllocationLowering.lowerBlockOpen_stateExtends
      bodyCursor.sourceScoped bodyCursor.lower
  have hExtendsAfter :
      AllocationLowering.StateExtends live afterState bodyCursor.finalState := by
    rcases hExtendsBefore with ⟨dropped, hLayout, hFresh, hSlots⟩
    refine ⟨dropped, ?_, hFresh, ?_⟩
    · rw [hLayout, hAfterLayout]
    · intro name hLive
      exact (hSlots name hLive).trans
        (congrArg (AllocationSupport.lookupSlot? name) hAfterEnv.symm)
  have hTrue :
      ∀ {sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState beforeLocals cursor.plan live frameBase mode
            sourceAfter targetAfter →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              beforeLocals cursor.plan root.returns live frameBase mode
              sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter) := by
    intro sourceAfter targetAfter hAfter
    have hBefore :=
      hAfter.transport_state hAfterEnv.symm hAfterLayout.symm
    have hNestedInvariant :=
      hBefore.transport_plan hBodyAgree.symm bodyCursor.planWF
    have hNestedBoundary :
        Boundary bodyCursor contract frameBase mode sourceCtx
          sourceAfter targetAfter :=
      { invariant := hNestedInvariant
        sourceScope := hBoundary.sourceScope
        control := hBoundary.control
        capacity := hBoundary.capacity }
    obtain ⟨hCleanupFuel, hBody⟩ :=
      hBodyForward bodyCursor hNestedBoundary
    apply AllocationInteractionControl.block_of_components
      (bodyLive := Functions.Scope.Block.outEnv live body)
      hBoundary.sourceScope rfl rfl hBoundary.control hAfter
      hExtendsAfter hBodyAgree hFinish hCleanupFuel
    simpa [bodyFuel, targetBodyFuel, totalFuel] using hBody
  have hHead :=
    AllocationInteractionControl.if_of_components
      (sourceBodyFuel := bodyFuel) (targetBodyFuel := targetBodyFuel)
      hAfterInvariant hCond hVars hTrue
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.if_ cond body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hBodyFuel, hTargetFuel, hHeadCode] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.if_ cond body) } := by
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

/-- Recursive switch constructor over the compiler-selected branch cursor. -/
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 2 < sourceFuel)
    (hScrutineeSafe :
      AllocationInteractionSafety.ExprSafe contract scrutinee source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hBodyForward :
      ∀ {value} {selected : Functions.Block}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (hSelect :
          Functions.Source.Switch.select value cases defaultBody =
            some selected)
        (bodyCursor :
          CoreCursor root (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart beforeLocals)
        {sourceAfter targetAfter},
        Boundary bodyCursor contract frameBase mode sourceCtx
            sourceAfter targetAfter →
          2 ≤
              (targetBudget cursor sourceFuel targetExtra - 2) -
                bodyCursor.compiled.length ∧
            Simulation.Interaction.Rel
              (OpenControlResultRel contract root.lowerCtx
                bodyCursor.finalState bodyCursor.finalLocals bodyCursor.plan
                root.returns (Functions.Scope.Block.outEnv live selected)
                frameBase mode sourceCtx
                { sourceCtx with
                  scope := Functions.Scope.Block.outEnv live selected })
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 2) selected sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetBudget cursor sourceFuel targetExtra - 2)
                { stmts := bodyCursor.compiled } targetAfter))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState beforeLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let bodyFuel := sourceFuel - 2
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let targetBodyFuel := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hBodyFuel : bodyFuel + 1 = childFuel := by
    simp [bodyFuel, childFuel]
    omega
  have hTargetFuel : targetBodyFuel + 2 = totalFuel := by
    simp [targetBodyFuel, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, headLower, headCode, tail, loweredScrutinee,
        loweredCases, afterCases, loweredDefault, scrutineeCode,
        compiledCases, compiledDefault, components⟩ :=
    cursor.switchCursors
  have hAfterInvariant :=
    hBoundary.invariant.transport_state
      components.afterEnv components.afterLayout
  have hScrutinee :=
    AllocationInteractionExpressionRecursive.forwardOne
      hScrutineeSafe hBoundary.invariant.compiler
      components.scrutineeScoped components.lowerScrutinee
      components.compileScrutinee hBoundary.invariant.state
  have hVars :=
    Locals.InteractionStatePreservation.expr_openEvalOne_vars
      scrutinee source
  have hSelection :
      ∀ value,
        AllocationInteractionControl.SwitchSelection cases defaultBody
          compiledCases compiledDefault value := by
    intro value
    have hCompiledSelection :=
      Locals.InteractionPreservation.Stmt.SwitchCompile.selectedRel_of_compile
        beforeLocals value components.compileCases
          components.compileDefault
    cases hSourceSelect :
        Functions.Source.Switch.select value cases defaultBody with
    | none =>
        have hLowerSelect :=
          AllocationLowering.lowerSwitch_select_none components.lowerCases
            components.lowerDefault hSourceSelect
        rw [hLowerSelect] at hCompiledSelection
        exact .none hSourceSelect hCompiledSelection.none_target
    | some selected =>
        obtain
            ⟨selectedLowered, selectedStart, selectedFinal,
              hLowerSelect, _hLowerBody, _hSelectedEnv,
              _hSelectedLayout⟩ :=
          AllocationLowering.lowerSwitch_select_some
            components.lowerCases components.lowerDefault hSourceSelect
        rw [hLowerSelect] at hCompiledSelection
        obtain
            ⟨selectedTarget, _selectedCode, _selectedLocals,
              hTargetSelect, _hCompileSelected, _hFinishSelected⟩ :=
          hCompiledSelection.some_parts
        exact .some selected selectedTarget hSourceSelect hTargetSelect
  have hSelected :
      ∀ {value selected selectedTarget sourceAfter targetAfter},
        Functions.Source.Switch.select value cases defaultBody =
            some selected →
        Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault =
          some selectedTarget →
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState beforeLocals cursor.plan live frameBase mode
            sourceAfter targetAfter →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              beforeLocals cursor.plan root.returns live frameBase mode
              sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block selected) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel selectedTarget targetAfter) := by
    intro value selected selectedTarget sourceAfter targetAfter
      hSourceSelect hTargetSelect hAfter
    obtain
        ⟨selectedAfter, selectedHeadLower, selectedHeadCode, selectedTail,
          selectedScrutineeCode, selectedCases, selectedDefault,
          selectedStart, selectedPlanning, actualTarget, bodyCursor,
          _hSelectedCompiled, hSelectedLower, hSelectedCompile,
          hSelectedHeadCode, hActualTargetSelect, hFinish,
          hSelectedEnv, hSelectedLayout, _hSelectedAfterEnv,
          _hSelectedAfterLayout, _hSelectedScrutineeScoped,
          _hSelectedScoped, _hSelectedExact⟩ :=
      cursor.switchSelectedCursors hSourceSelect
    rw [components.lower] at hSelectedLower
    cases hSelectedLower
    rw [components.compile] at hSelectedCompile
    cases hSelectedCompile
    rw [components.codeHead] at hSelectedHeadCode
    cases hSelectedHeadCode
    rw [hTargetSelect] at hActualTargetSelect
    cases hActualTargetSelect
    have hBefore :=
      hAfter.transport_state components.afterEnv.symm
        components.afterLayout.symm
    have hSelectedInvariant :=
      hBefore.transport_state hSelectedEnv hSelectedLayout
    have hBodyAgree : PlanAgreesOn bodyCursor.plan cursor.plan live :=
      bodyCursor.planAgreesOn cursor hSelectedEnv
    have hNestedInvariant :=
      hSelectedInvariant.transport_plan hBodyAgree.symm bodyCursor.planWF
    have hNestedBoundary :
        Boundary bodyCursor contract frameBase mode sourceCtx
          sourceAfter targetAfter :=
      { invariant := hNestedInvariant
        sourceScope := hBoundary.sourceScope
        control := hBoundary.control
        capacity := hBoundary.capacity }
    have hExtendsSelected :
        AllocationLowering.StateExtends live selectedStart
          bodyCursor.finalState :=
      AllocationLowering.lowerBlockOpen_stateExtends
        bodyCursor.sourceScoped bodyCursor.lower
    have hExtendsAfter :
        AllocationLowering.StateExtends live afterState
          bodyCursor.finalState := by
      rcases hExtendsSelected with ⟨dropped, hLayout, hFresh, hSlots⟩
      refine ⟨dropped, ?_, hFresh, ?_⟩
      · rw [hLayout, hSelectedLayout, components.afterLayout]
      · intro name hLive
        exact (hSlots name hLive).trans
          (congrArg (AllocationSupport.lookupSlot? name)
            (hSelectedEnv.trans components.afterEnv.symm))
    obtain ⟨hCleanupFuel, hBody⟩ :=
      hBodyForward hSourceSelect bodyCursor hNestedBoundary
    apply AllocationInteractionControl.block_of_components
      (bodyLive := Functions.Scope.Block.outEnv live selected)
      hBoundary.sourceScope rfl rfl hBoundary.control hAfter
      hExtendsAfter hBodyAgree hFinish hCleanupFuel
    simpa [bodyFuel, targetBodyFuel, totalFuel] using hBody
  have hHead :=
    AllocationInteractionControl.switch_of_components
      (sourceBodyFuel := bodyFuel) (targetBodyFuel := targetBodyFuel)
      hAfterInvariant hScrutinee hVars hSelection hSelected
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.switch scrutinee cases defaultBody) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hBodyFuel, hTargetFuel, components.codeHead] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.switch scrutinee cases defaultBody) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor tail components.exactTail components.compiled hMidCtx
      (by
        simpa [childFuel, hFuel, totalFuel,
          Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward tail components.exactTail hInvariant)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `for` constructor over the ordinary compiler-owned artifact. -/
theorem for_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
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
        { stmts := .for_ init cond post body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 2 < sourceFuel)
    (hCondSafe :
      ∀ sourceState,
        AllocationInteractionSafety.ExprSafe contract cond sourceState)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.for_ init cond post body) source))
    (hRecursive :
      RecursiveOpenForward (root := root) contract frameBase sourceFuel)
    (hCapacity :
      ForFuelCapacity cursor.forArtifact (sourceFuel - 2)
        ((targetBudget cursor sourceFuel targetExtra - 2) -
          (sourceFuel - 2)))
    (hFrameCapacity :
      ∀ {nextMode nextSource nextTarget},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            cursor.forArtifact.loopState cursor.forArtifact.initLocals
            cursor.forArtifact.initCursor.plan cursor.forArtifact.loopLive
            frameBase nextMode nextSource nextTarget →
          AllocationInteractionForward.FrameCapacity compilation nextMode)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail :
          CoreCursor root scope live { stmts := rest }
            afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState beforeLocals tail.plan live frameBase tailMode
              sourceMid targetMid →
            CursorForwardAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  classical
  let components := cursor.forArtifact
  let childFuel := sourceFuel - 1
  let loopFuel := sourceFuel - 2
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let nestedFuel := totalFuel - 2
  let slack := nestedFuel - loopFuel
  have hChildFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hLoopFuel : loopFuel + 1 = childFuel := by
    simp [loopFuel, childFuel]
    omega
  have hSourceLeTotal : sourceFuel ≤ totalFuel := by
    have hStride : 1 ≤ callStride expressions := by
      exact le_trans (by omega) (eight_le_callStride expressions)
    have hMul :
        sourceFuel ≤ callStride expressions * sourceFuel := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right sourceFuel hStride
    simp [totalFuel, targetBudget, Nat.mul_succ]
    omega
  have hNestedFuel : loopFuel + slack = nestedFuel := by
    simp only [loopFuel, slack, nestedFuel]
    omega
  have hTotalFuel : nestedFuel + 2 = totalFuel := by
    simp only [nestedFuel]
    omega
  change ForFuelCapacity components loopFuel slack at hCapacity
  change (∀ {nextMode : ActivationMode} {nextSource : SourceState}
      {nextTarget : TargetState},
    AllocationContext.ActivationInvariant contract root.lowerCtx
        components.loopState components.initLocals
        components.initCursor.plan components.loopLive frameBase
        nextMode nextSource nextTarget →
      AllocationInteractionForward.FrameCapacity compilation nextMode) at hFrameCapacity
  let initCtx := sourceCtx.withoutLoopControl
  let loopCtx : Functions.Source.Ctx :=
    { initCtx with scope := components.loopLive }
  let postCtx := loopCtx.withoutLoopControl
  let bodyCtx :=
    loopCtx.withLoopControl components.loopLive components.loopLive
  have hOuterSubset :
      ∀ name, name ∈ live → name ∈ components.loopLive := by
    rw [components.loopLive_eq]
    intro name hName
    exact Functions.Scope.Block.mem_outEnv hName
  have hOuterControl :
      AllocationInteractionStatement.ControlScopesWithin root.returns
        components.loopLive loopCtx := by
    have hLiveControl := hBoundary.control.mono hOuterSubset
    simpa [loopCtx, initCtx] using
      hLiveControl.withoutLoopControl.scopeUpdate components.loopLive
  have hInitSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program initCtx
          loopFuel init source) := by
    have hSuccess := hHeadSuccess
    have hFuelEq : loopFuel + 1 = sourceFuel - 1 := by
      simpa [childFuel] using hLoopFuel
    rw [← hFuelEq] at hSuccess
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run at hSuccess
    simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
    have hInitDone :=
      Simulation.Interaction.Successful.bind_inv hSuccess
    apply Simulation.Interaction.AllDone.mono hInitDone
    intro outcome hOutcome
    cases outcome with
    | error err => exact hOutcome
    | ok value => trivial
  have hInitBoundary :
      Boundary components.initCursor contract frameBase mode initCtx
        source target :=
    { invariant := by
        have hTransported :=
          hBoundary.invariant.transport_plan
            (components.initCursor.planAgreesOn cursor rfl).symm
            components.initCursor.planWF
        exact hTransported.transport_locals rfl
      sourceScope := by
        simpa [initCtx, Functions.Source.Ctx.withoutLoopControl] using
          hBoundary.sourceScope
      control := by
        simpa [initCtx] using hBoundary.control.withoutLoopControl
      capacity := hBoundary.capacity }
  have hInitRaw :=
    RecursiveOpenForward.at_targetFuel hRecursive components.initCursor
      (sourceFuel := loopFuel) (targetFuel := nestedFuel)
      (by simp [loopFuel]; omega)
      (by
        exact
          (targetBudget_mono_extra components.initCursor loopFuel
            (Nat.zero_le _)).trans
            (by simpa [hNestedFuel] using hCapacity.init))
      hInitBoundary hInitSuccess
  have hInit :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx components.loopState
          components.initLocals components.initCursor.plan root.returns
          components.loopLive frameBase mode initCtx loopCtx)
        (Functions.InteractionSemantics.Block.openRun program initCtx
          loopFuel init source)
        (Expressions.InteractionSemantics.Block.openRun expressions nestedFuel
          { stmts := components.initCursor.compiled } target) := by
    simpa [components.initFinalState, components.initFinalLocals,
      components.loopLive_eq, loopCtx, initCtx] using hInitRaw
  have hInitOuterAgree :
      PlanAgreesOn components.initCursor.plan cursor.plan live :=
    components.initCursor.planAgreesOn cursor rfl
  have hPostShape :=
    AllocationLowering.lowerBlockScoped_state_shape components.lowerPost
  have hPostAgree :
      PlanAgreesOn components.postCursor.plan
        components.initCursor.plan components.loopLive :=
    components.postPlanAgree
  have hBodyAgree :
      PlanAgreesOn components.bodyCursor.plan
        components.initCursor.plan components.loopLive :=
    components.bodyPlanAgree
  have hLoop :
      ∀ {loopMode sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            components.loopState components.initLocals
            components.initCursor.plan components.loopLive frameBase
            loopMode sourceAfter targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRunForLoop program
              loopCtx cond postCtx post bodyCtx body loopFuel sourceAfter) →
            Simulation.Interaction.Rel
              (AllocationInteractionLoop.OpenLoopResultRel contract
                root.lowerCtx components.loopState components.initLocals
                components.initCursor.plan root.returns components.loopLive
                frameBase loopMode loopCtx)
              (Functions.InteractionSemantics.Stmt.openRunForLoop program
                loopCtx cond postCtx post bodyCtx body loopFuel sourceAfter)
              (Expressions.InteractionSemantics.Stmt.openRunForLoop
                expressions (loopFuel + slack) (.code components.condCode)
                  components.compiledPost components.compiledBody
                  targetAfter) := by
    intro loopMode sourceAfter targetAfter hInvariant hSuccess
    apply AllocationInteractionLoop.forward
      (program := program) (expressions := expressions)
      (returns := root.returns) (live := components.loopLive)
      (loopCtx := loopCtx) (postCtx := postCtx) (bodyCtx := bodyCtx)
      (cond := cond) (post := post) (body := body)
      (targetCond := .code components.condCode)
      (targetPost := components.compiledPost)
      (targetBody := components.compiledBody)
      (slack := slack) (fuelBound := loopFuel) (fuel := loopFuel)
      (hLoopScope := rfl) (hBodyBreak := rfl) (hBodyContinue := rfl)
      (hCond := ?_) (hBody := ?_) (hPost := ?_)
      (by rfl) hInvariant hSuccess
    · intro nextMode nextSource nextTarget hNext _hCondSuccess
      exact AllocationInteractionExpressionRecursive.forwardCondition
        (hCondSafe nextSource) hNext.compiler components.condScoped
        components.lowerCond components.compileCond hNext.state
    · intro fuel nextMode nextSource nextTarget hFuelLt hNext hBodySuccess
      have hBodyOpenSuccess :
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program bodyCtx
              fuel body nextSource) := by
        unfold Functions.InteractionSemantics.Block.openRunScoped
          Functions.Source.Canonical.Block.runScoped
          Functions.Source.Effectful.Control.Block.runScoped at hBodySuccess
        have hDone :=
          Simulation.Interaction.Successful.bind_inv hBodySuccess
        apply Simulation.Interaction.AllDone.mono hDone
        intro outcome hOutcome
        cases outcome with
        | error err => exact hOutcome
        | ok value => trivial
      have hAtBodyState :=
        hNext.transport_state hPostShape.1 hPostShape.2
      have hBodyInvariant :=
        (by
          exact
            (hAtBodyState.transport_plan hBodyAgree.symm
              components.bodyCursor.planWF).transport_locals rfl :
          AllocationContext.ActivationInvariant contract root.lowerCtx
            components.afterPost
            (components.initLocals.withLoopControl
              components.initLocals.layout.length)
            components.bodyCursor.plan components.loopLive frameBase
            nextMode nextSource nextTarget)
      have hBodyBoundary :
          Boundary components.bodyCursor contract frameBase nextMode bodyCtx
            nextSource nextTarget :=
        { invariant := hBodyInvariant
          sourceScope := rfl
          control := by
            simpa [bodyCtx] using hOuterControl.withLoopControl
          capacity := hFrameCapacity hNext }
      have hBodyRaw :=
        RecursiveOpenForward.at_targetFuel hRecursive
          components.bodyCursor (sourceFuel := fuel)
          (targetFuel := fuel + slack)
          (by simp [loopFuel] at *; omega)
          ((targetBudget_mono_extra components.bodyCursor fuel
            (Nat.zero_le _)).trans (hCapacity.body fuel hFuelLt))
          hBodyBoundary hBodyOpenSuccess
      have hExtends :
          AllocationLowering.StateExtends components.loopLive
            components.afterPost components.bodyCursor.finalState :=
        AllocationLowering.lowerBlockOpen_stateExtends
          components.bodyCursor.sourceScoped components.bodyCursor.lower
      have hExtendsLoop :
          AllocationLowering.StateExtends components.loopLive
            components.loopState components.bodyCursor.finalState := by
        rcases hExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
        refine ⟨dropped, ?_, hFresh, ?_⟩
        · rw [hLayout, hPostShape.2]
        · intro name hLive
          exact (hSlots name hLive).trans
            (congrArg (AllocationSupport.lookupSlot? name)
              hPostShape.1)
      have hCleanupFuel :
          2 ≤ fuel + slack - components.bodyCursor.compiled.length := by
        have hBudget := hCapacity.body fuel hFuelLt
        simp [targetBudget, callStride, Nat.mul_succ] at hBudget
        omega
      exact AllocationInteractionControl.blockScoped_of_components
        rfl rfl rfl hOuterControl.withLoopControl hNext hExtendsLoop
        hBodyAgree components.finishBody hCleanupFuel hBodyRaw
    · intro fuel nextMode nextSource nextTarget hFuelLt hNext hPostSuccess
      have hPostOpenSuccess :
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program postCtx
              fuel post nextSource) := by
        unfold Functions.InteractionSemantics.Block.openRunScoped
          Functions.Source.Canonical.Block.runScoped
          Functions.Source.Effectful.Control.Block.runScoped at hPostSuccess
        have hDone :=
          Simulation.Interaction.Successful.bind_inv hPostSuccess
        apply Simulation.Interaction.AllDone.mono hDone
        intro outcome hOutcome
        cases outcome with
        | error err => exact hOutcome
        | ok value => trivial
      have hPostInvariant :=
        (by
          exact
            (hNext.transport_plan hPostAgree.symm
              components.postCursor.planWF).transport_locals rfl :
          AllocationContext.ActivationInvariant contract root.lowerCtx
            components.loopState components.initLocals.withoutLoopControl
            components.postCursor.plan components.loopLive frameBase
            nextMode nextSource nextTarget)
      have hPostBoundary :
          Boundary components.postCursor contract frameBase nextMode postCtx
            nextSource nextTarget :=
        { invariant := hPostInvariant
          sourceScope := rfl
          control := by
            simpa [postCtx] using hOuterControl.withoutLoopControl
          capacity := hFrameCapacity hNext }
      have hPostRaw :=
        RecursiveOpenForward.at_targetFuel hRecursive
          components.postCursor (sourceFuel := fuel)
          (targetFuel := fuel + slack)
          (by simp [loopFuel] at *; omega)
          ((targetBudget_mono_extra components.postCursor fuel
            (Nat.zero_le _)).trans (hCapacity.post fuel hFuelLt))
          hPostBoundary hPostOpenSuccess
      have hExtends :
          AllocationLowering.StateExtends components.loopLive
            components.loopState components.postCursor.finalState :=
        AllocationLowering.lowerBlockOpen_stateExtends
          components.postCursor.sourceScoped components.postCursor.lower
      have hCleanupFuel :
          2 ≤ fuel + slack - components.postCursor.compiled.length := by
        have hBudget := hCapacity.post fuel hFuelLt
        simp [targetBudget, callStride, Nat.mul_succ] at hBudget
        omega
      exact AllocationInteractionControl.blockScoped_of_components
        rfl rfl rfl hOuterControl.withoutLoopControl hNext hExtends
        hPostAgree components.finishPost hCleanupFuel hPostRaw
  have hBeforeExtends :
      AllocationLowering.StateExtends live beforeState
        components.loopState := by
    have hExtends := AllocationLowering.lowerBlockOpen_stateExtends
      components.initCursor.sourceScoped components.initCursor.lower
    simpa [components.initFinalState] using hExtends
  have hAfterEnv :
      components.afterState.allocation.env = beforeState.allocation.env := by
    rw [components.afterState_eq]
  have hAfterLayout : components.afterState.layout = beforeState.layout := by
    rw [components.afterState_eq]
  have hAfterInvariant :=
    hBoundary.invariant.transport_state hAfterEnv hAfterLayout
  have hAfterExtends :
      AllocationLowering.StateExtends live components.afterState
        components.loopState := by
    rcases hBeforeExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
    refine ⟨dropped, ?_, hFresh, ?_⟩
    · rw [hLayout, hAfterLayout]
    · intro name hLive
      exact (hSlots name hLive).trans
        (congrArg (AllocationSupport.lookupSlot? name) hAfterEnv.symm)
  have hHeadSuccess' :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (loopFuel + 1) (.for_ init cond post body) source) := by
    rw [hLoopFuel]
    exact hHeadSuccess
  have hInit' := hInit
  rw [← hNestedFuel] at hInit'
  have hHead :=
    AllocationInteractionFor.forward
      (sourceFuel := loopFuel) (slack := slack)
      (hSourceScope := hBoundary.sourceScope)
      (hLoopLive := components.loopLive_eq)
      (hInitCtx := rfl) (hLoopCtx := rfl)
      (hPostCtx := rfl) (hBodyCtx := rfl)
      hAfterInvariant hAfterExtends hInitOuterAgree components.cleanupTo
      (by
        have hPositive :
            0 < targetBudget components.initCursor loopFuel 0 := by
          simp [targetBudget, callStride, Nat.mul_succ]
        change 0 < loopFuel + slack
        exact lt_of_lt_of_le hPositive
          ((targetBudget_mono_extra components.initCursor loopFuel
            (Nat.zero_le _)).trans hCapacity.init))
      hInit' hLoop hHeadSuccess'
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx components.afterState
          beforeLocals cursor.plan root.returns live frameBase mode sourceCtx
          sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.for_ init cond post body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := components.headCode } target) := by
    simpa [childFuel, loopFuel, nestedFuel, slack, totalFuel,
      hLoopFuel, hNestedFuel, hTotalFuel, components.headCode_eq,
      Locals.codeStmt] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.for_ init cond post body) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts cursor components.tail components.exactTail
      components.compiled hMidCtx
      (by simpa [childFuel, hChildFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (fun {sourceMid targetMid tailMode} hInvariant =>
        hTailForward components.tail components.exactTail hInvariant)
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
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
          cursor.plan root.returns live frameBase beforeMode
          sourceCtx sourceCtx)
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
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
          cursor.plan root.returns live frameBase beforeMode
          sourceCtx sourceCtx)
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
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
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
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
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
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
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 4
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 4 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
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
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
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
            frameBase sourceFuel 0 prepared.bodyMode sourceCtx source
            bodyTarget) :
    ∃ targetFuel,
      0 < targetFuel ∧
      Simulation.Interaction.Rel
        (OpenControlResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            fn.body)
          frameBase artifact.mode sourceCtx
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
  have hSetupFrame : SameFrame artifact.mode prepared.bodyMode := by
    exact SameFrame.atStackDepth artifact.mode
      (currentStackOrder prepared.plan live).length
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
    have hBody' :=
      AllocationInteractionComposition.prepend_frame hSetupFrame hBody
    let bodyFuel :=
      targetBudget (prepared.rootCursor hProgramScoped) sourceFuel 0
    have hBodyFuel : 0 < bodyFuel := by
      simp [bodyFuel, targetBudget, callStride, Nat.mul_succ]
    let targetFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨targetFuel, by simp [targetFuel]; omega, ?_⟩
    exact
      prepared.prelude_then_body hBodyFuel hPreludeAt
        (by simpa [CursorForwardAt, bodyFuel] using hBody')
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
    have hBody' :=
      AllocationInteractionComposition.prepend_frame hSetupFrame hBody
    let bodyFuel :=
      targetBudget (prepared.rootCursor hProgramScoped) sourceFuel 0
    have hBodyFuel : 0 < bodyFuel := by
      simp [bodyFuel, targetBudget, callStride, Nat.mul_succ]
    let targetFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨targetFuel, by simp [targetFuel]; omega, ?_⟩
    exact
      prepared.prelude_then_body hBodyFuel hPreludeAt
        (by simpa [CursorForwardAt, bodyFuel] using hBody')

end SelectedCallee

end AllocationInteractionRecursive
end Functions
end EvmCompiler
