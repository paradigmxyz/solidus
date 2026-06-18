import EvmCompiler.Functions.AllocationInteractionRecursive
import EvmCompiler.Functions.AllocationInteractionControlAgreement
import EvmCompiler.Functions.AllocationInteractionTargetFuel
import EvmCompiler.Functions.AllocationInteractionCallResult
import EvmCompiler.Functions.AllocationInteractionCallStatement

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStackRuntime

open AllocationInteractionCursor
open AllocationInteractionComposition
open AllocationInteractionRelation
open AllocationInteractionRecursive

private theorem toStructured_length (stmts : List Expressions.Stmt) :
    (Expressions.StmtList.toStructured stmts).length = stmts.length := by
  induction stmts with
  | nil => rfl
  | cons stmt rest ih =>
      simp [Expressions.StmtList.toStructured, ih]

private theorem openRun_code_prefix
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code) (rest : List Expressions.Stmt)
    (state : Structured.RunState)
    (hFuel : 2 <= fuel) :
    Expressions.InteractionSemantics.Block.openRun program fuel
        { stmts := Locals.codeStmt code ++ rest } state =
      Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun code state)
        (fun after =>
          Expressions.InteractionSemantics.Block.openRun program (fuel - 1)
            { stmts := rest } after) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  simp only [Locals.codeStmt, List.singleton_append]
  rw [show 2 + extra = (1 + extra) + 1 by omega,
    Expressions.InteractionSemantics.Block.openRun_cons]
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun code state)
          (fun after =>
            Simulation.Interaction.pure
              (Structured.EffectSemantics.Outcome.regular after))) _ = _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Structured.InteractionSemantics.Code.openRun code state))
  intro after _
  rfl

/-- The recursive stride leaves a selected procedure enough target fuel for
its return epilogue and caller continuation. -/
theorem selected_call_extra
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx}
    {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation functionName fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    {sourceFuel targetExtra : Nat}
    (hSourceFuel : 2 < sourceFuel) :
    let bodyFuel := sourceFuel - 3
    let callTargetFuel := targetBudget cursor sourceFuel targetExtra - 3
    let callBase :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + prepared.bodyCode.length +
          callStride expressions * (bodyFuel + 1)
    2 * callStride expressions + 3 <= callTargetFuel - callBase ∧
      callBase + (callTargetFuel - callBase) = callTargetFuel := by
  dsimp only
  have hProc :=
    proc_body_length_add_eight_le_callStride artifact.targetLookup
  have hStructuredLength :
      artifact.lowerProc.toStructured.body.stmts.length =
        artifact.lowerProc.body.stmts.length := by
    simp only [Expressions.Proc.toStructured]
    cases artifact.lowerProc.body with
    | mk stmts =>
        change (Expressions.StmtList.toStructured stmts).length = stmts.length
        exact toStructured_length stmts
  rw [hStructuredLength] at hProc
  have hProcLength :
      artifact.lowerProc.body.stmts.length =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + prepared.bodyCode.length + 2 := by
    rw [prepared.procBody]
    simp [Locals.codeStmt]
    omega
  rw [hProcLength] at hProc
  have hFuelEq : sourceFuel + 1 = (sourceFuel - 3 + 1) + 3 := by omega
  have hStride : 8 <= callStride expressions :=
    eight_le_callStride expressions
  unfold targetBudget
  rw [hFuelEq]
  simp only [Nat.mul_add]
  omega

/-- Static compiler fact characterizing a program whose selected function
activations are all stack-backed. -/
def AllFunctionsStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions) : Prop :=
  AllocationLowering.frameFunctions compilation.recipe
    compilation.stackSlots = []

/-- Every real call-site lookup in an all-stack compilation selects a callee
whose ordinary compiler artifact emits no scratch frame. -/
theorem selectedCallee_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx}
    (components : AllocationInteractionCall.CallComponents cursor)
    (hAllStack : AllFunctionsStack compilation) :
    ∃ fn,
      Functions.Source.FunList.find? functionName program.functions =
          some fn ∧
        ∃ artifact :
            AllocationInteractionCall.SelectedCallee.Artifact
              compilation functionName fn,
          Nonempty
              (AllocationInteractionCall.SelectedCallee.Prepared artifact) ∧
            components.fn = artifact.slots ∧
            artifact.needsFrame = false := by
  obtain ⟨fn, hFind, artifact, hPrepared, hSlots⟩ :=
    components.selectedCallee
  have hNotMem : functionName ∉ root.lowerCtx.frameFunctions := by
    rw [root.lowerCtxShared.frameFunctions, hAllStack]
    simp
  have hNotTrue : artifact.needsFrame ≠ true := by
    intro hNeeds
    exact hNotMem
      ((artifact.mem_frameFunctions_iff root.lowerCtxShared).2 hNeeds)
  exact
    ⟨fn, hFind, artifact, hPrepared, hSlots,
      Bool.eq_false_of_not_eq_true hNotTrue⟩

namespace CallComponents

/-- Exact ordinary argument code for an all-stack selected callee. -/
theorem stack_compileArgs
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live targets : List Functions.Name}
    {functionName : Functions.Name} {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx}
    (components : AllocationInteractionCall.CallComponents cursor)
    {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation functionName fn}
    (hNeedsFrame : artifact.needsFrame = false) :
    Locals.ExprSeq.compileCode localsCtx 0
        (AllocationLowering.exprSeqOfList components.loweredArgs) =
      some components.argsCode := by
  have hNotMem : functionName ∉ root.lowerCtx.frameFunctions := by
    intro hMem
    have hNeeds :=
      (artifact.mem_frameFunctions_iff root.lowerCtxShared).mp hMem
    simp [hNeedsFrame] at hNeeds
  have hArgs := components.callArgs_eq
  simp only [hNotMem, ↓reduceIte] at hArgs
  have hCallArgs : components.callArgs = components.loweredArgs :=
    (Option.some.inj hArgs).symm
  have hCompile := components.compileArgs
  rw [hCallArgs] at hCompile
  exact hCompile

theorem stack_releaseCode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live targets : List Functions.Name}
    {functionName : Functions.Name} {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx}
    (components : AllocationInteractionCall.CallComponents cursor)
    {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation functionName fn}
    (hNeedsFrame : artifact.needsFrame = false) :
    components.releaseCode = [] := by
  have hNotMem : functionName ∉ root.lowerCtx.frameFunctions := by
    intro hMem
    have hNeeds :=
      (artifact.mem_frameFunctions_iff root.lowerCtxShared).mp hMem
    simp [hNeedsFrame] at hNeeds
  have hRelease := components.release_eq
  simp only [hNotMem, ↓reduceIte] at hRelease
  have hReleaseNil : components.release = [] :=
    (Option.some.inj hRelease).symm
  simpa [hReleaseNil, Locals.Block.compileOpen] using
    components.compileRelease

end CallComponents

/-- Runtime boundary for compiler-selected programs whose entire allocation
plan is stack-backed.  It shares the canonical semantic boundary and adds only
the control-destination agreement needed by the recursive dispatcher. -/
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
    (frameBase : Nat) (mode : ActivationMode)
    (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop where
  semantic :
    AllocationInteractionRecursive.Boundary cursor contract frameBase mode
      sourceCtx source target
  controlAgreement :
    AllocationInteractionControlAgreement.Agreement cursor.plan root.returns
      live mode sourceCtx localsCtx target
  stackMode : mode = .stack

namespace Boundary

/-- Transport exact control destinations through an ordinary stack-only
statement whose source live set is unchanged. -/
def controlAgreement_same_live
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
    {frameBase : Nat}
    {mode tailMode : ActivationMode}
    {sourceCtx nextCtx : Functions.Source.Ctx}
    {source sourceMid : SourceState} {target targetMid : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hExact : ExactTail cursor tail)
    (hOut : Functions.Scope.Stmt.outEnv live stmt = live)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx afterState
        afterLocals tail.plan (Functions.Scope.Stmt.outEnv live stmt)
        frameBase tailMode sourceMid targetMid)
    (hSame : SameFrame mode tailMode)
    (hSource : Functions.Source.Ctx.SameControl sourceCtx nextCtx)
    (hReturns : targetMid.returns = target.returns) :
    AllocationInteractionControlAgreement.Agreement tail.plan root.returns
      (Functions.Scope.Stmt.outEnv live stmt) tailMode nextCtx afterLocals
      targetMid := by
  have hAfterMatches := hInvariant.compiler.mode_matches
  have hAfterMatchesLive : tailMode.Matches tail.plan live :=
    hAfterMatches.transport_live fun name => by rw [hOut]
  rw [hExact.plan] at hAfterMatchesLive
  have hModeEq := hSame.eq_of_matches
    hBoundary.semantic.invariant.compiler.mode_matches hAfterMatchesLive
  subst tailMode
  have hLocals := hExact.locals_sameControl cursor tail
  rw [hExact.plan]
  simpa [hOut] using
    (hBoundary.controlAgreement.transport_context hSource hLocals)
      |>.transport_target hReturns

/-- Rebuild the complete stack-only recursive boundary at an exact same-live
tail after a successful regular head. -/
def tail_same_live
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
    {contract : MemoryContract.Contract} {frameBase : Nat}
    {mode tailMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceMid : SourceState} {target targetMid : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hExact : ExactTail cursor tail)
    (hOut : Functions.Scope.Stmt.outEnv live stmt = live)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx afterState
        afterLocals tail.plan (Functions.Scope.Stmt.outEnv live stmt)
        frameBase tailMode sourceMid targetMid)
    (hSame : SameFrame mode tailMode)
    (hReturns : targetMid.returns = target.returns) :
    Boundary tail contract frameBase tailMode sourceCtx sourceMid targetMid := by
  have hMode : mode = .stack := hBoundary.stackMode
  subst mode
  have hTailStack : tailMode = .stack := by
    cases hSame
    rfl
  subst tailMode
  exact
    { semantic :=
        { invariant := hInvariant
          sourceScope := by
            rw [hOut]
            exact hBoundary.semantic.sourceScope
          control := by
            rw [hOut]
            exact hBoundary.semantic.control
          capacity := hBoundary.semantic.capacity }
      controlAgreement :=
        controlAgreement_same_live cursor tail hBoundary hExact hOut
          hInvariant hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
          hReturns
      stackMode := rfl }

/-- Rebuild the stack-only boundary after one compiler-selected declaration. -/
def tail_after_declaration
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {contract : MemoryContract.Contract} {frameBase : Nat}
    {mode tailMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceMid : SourceState} {target targetMid : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .let_ name value :: rest } beforeState beforeLocals)
    (tail : CoreCursor root scope (name :: live) { stmts := rest }
      afterState afterLocals)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hExact : ExactTail cursor tail)
    (hPlacement :
      DeclarationPlacement root.lowerCtx beforeState cursor.plan live name)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx afterState
        afterLocals tail.plan (name :: live) frameBase tailMode sourceMid
        targetMid)
    (hSame : SameFrame mode tailMode)
    (hReturns : targetMid.returns = target.returns) :
    Boundary tail contract frameBase tailMode
      { sourceCtx with scope := name :: sourceCtx.scope }
      sourceMid targetMid := by
  have hMode : mode = .stack := hBoundary.stackMode
  subst mode
  have hTailStack : tailMode = .stack := by
    cases hSame
    rfl
  subst tailMode
  let nextCtx := { sourceCtx with scope := name :: sourceCtx.scope }
  have hSourceControl :
      Functions.Source.Ctx.SameControl sourceCtx nextCtx := by
    simpa [nextCtx] using
      Functions.Source.Ctx.SameControl.scopeUpdate sourceCtx
        (name :: sourceCtx.scope)
  have hLocalsControl := hExact.locals_sameControl cursor tail
  have hAgreement :
      AllocationInteractionControlAgreement.Agreement tail.plan root.returns
        (name :: live) .stack nextCtx afterLocals targetMid := by
    cases hPlacement with
    | stack slot planDepth hSlot hStack hLocation hOrder =>
        rw [hExact.plan]
        exact
          (hBoundary.controlAgreement.after_stack_declaration
            hSourceControl hLocalsControl rfl hOrder)
            |>.transport_target hReturns
    | scratch slot hSlot hStack hLocation hOrder =>
        rw [hExact.plan]
        exact
          (hBoundary.controlAgreement.after_scratch_declaration
            hSourceControl hLocalsControl hOrder)
            |>.transport_target hReturns
  exact
    { semantic :=
        { invariant := hInvariant
          sourceScope := by
            simp [nextCtx, hBoundary.semantic.sourceScope]
          control :=
            (hBoundary.semantic.control.mono
              (fun other hOther => by simp [hOther])).scopeUpdate
              (name :: sourceCtx.scope)
          capacity := hBoundary.semantic.capacity }
      controlAgreement := by simpa [nextCtx] using hAgreement
      stackMode := rfl }

end Boundary

/-- Exact stack-only recursive result at one canonical compiler cursor. -/
abbrev CursorRuntimeAt
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
    (frameBase sourceFuel targetExtra : Nat)
    (mode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  AllocationInteractionRecursive.CursorForwardAt cursor contract frameBase
    sourceFuel targetExtra mode sourceCtx source target

/-- Fuel-bounded stack-only recursive capability.  This is a proof fixed point
over the canonical Functions semantics, not a second evaluator. -/
def RecursiveOpenRuntime
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (contract : MemoryContract.Contract) (fuelBound : Nat) : Prop :=
  ∀ {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live sourceBlock lowerState localsCtx),
    sourceFuel < fuelBound ->
    Boundary cursor contract frameBase mode sourceCtx source target ->
    AllocationInteractionTargetFuel.Reserve cursor targetExtra ->
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        sourceFuel sourceBlock source) ->
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target

namespace RecursiveOpenRuntime

/-- Instantiate the stack-only recursive capability at any sufficiently large
exact target fuel. -/
theorem at_targetFuel
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {contract : MemoryContract.Contract}
    {fuelBound : Nat}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation) contract fuelBound)
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {frameBase sourceFuel targetFuel : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live sourceBlock lowerState localsCtx)
    (hFuel : sourceFuel < fuelBound)
    (hTargetFuel :
      targetBudget cursor sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            cursor.compiled) <= targetFuel)
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
  have hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra := by
    change
      AllocationInteractionTargetFuel.stmtListNestedSize cursor.compiled <=
        targetExtra
    simp only [targetExtra, targetBudget] at hTargetFuel ⊢
    omega
  have hForward :=
    hRecursive cursor hFuel hBoundary hReserve hSuccess
      (targetExtra := targetExtra)
  have hExact : targetBudget cursor sourceFuel targetExtra = targetFuel := by
    simp [targetBudget, targetExtra, callStride, Nat.mul_succ]
      at hTargetFuel ⊢
    omega
  simpa [CursorRuntimeAt, CursorForwardAt, hExact] using hForward

end RecursiveOpenRuntime

namespace CursorRuntimeAt

/-- Empty canonical stack-only cursor. -/
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
    (cursor : CoreCursor root scope live { stmts := [] } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  exact
    AllocationInteractionRecursive.CursorForwardAt.nil
      (targetExtra := targetExtra) cursor hSourceFuel hBoundary.semantic

/-- Compose a checked stack-only head with its exact successful same-live
tail.  Statement-specific theorems only need to construct the head relation. -/
theorem cons_same_live
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
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    {headCode : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hExact : ExactTail cursor tail)
    (hOut : Functions.Scope.Stmt.outEnv live stmt = live)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hHead :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) stmt source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target))
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := stmt :: rest } source))
    (hTailForward :
      ∀ {sourceMid targetMid tailMode},
        Boundary tail contract frameBase tailMode sourceCtx sourceMid
            targetMid →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 1) { stmts := rest } sourceMid) →
          CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
            (targetExtra + callStride expressions) tailMode sourceCtx
            sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  have hFuel : sourceFuel - 1 + 1 = sourceFuel := by
    have hPositive :=
      Functions.InteractionSemantics.Block.successful_openRun_fuel_pos
        hSuccessful
    omega
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live stmt } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    rw [hOut]
    exact hCtx.symm
  have hResult :=
    AllocationInteractionRecursive.CursorForwardAt.cons_of_parts_successful
      (contract := contract) (childFuel := sourceFuel - 1)
      (targetExtra := targetExtra) (frameBase := frameBase)
      (entryMode := mode) (source := source) (target := target)
      cursor tail hExact hCompiled hMidCtx
      (by simpa [hFuel, hOut] using hHead)
      (by simpa [hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hSame hReturns
          hTailSuccess =>
        hTailForward
          (Boundary.tail_same_live cursor tail hBoundary hExact hOut
            hInvariant hSame hReturns)
          hTailSuccess)
  simpa [CursorRuntimeAt, hFuel] using hResult

/-- Successful resource-free expression statement followed by its exact tail. -/
theorem expr
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .expr expr :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .expr expr :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.expr_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.expr expr) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful resource-free assignment followed by its exact tail. -/
theorem assign
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .assign name value :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .assign name value :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.assign_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.assign name value) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful stack-only declaration followed by its exact enlarged-scope
tail. -/
theorem let_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .let_ name value :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .let_ name value :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope (name :: live) { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode
              { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program
                { sourceCtx with scope := name :: sourceCtx.scope }
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode
              { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  let nextCtx := { sourceCtx with scope := name :: sourceCtx.scope }
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail, hCompiled, hHead,
      hPlacement, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.let_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSafe hBoundary.semantic.capacity hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase mode sourceCtx
          nextCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.let_ name value) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, nextCtx, hHeadFuel] using hHead
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
    AllocationInteractionRecursive.CursorForwardAt.cons_of_parts_successful
      (contract := contract) (childFuel := sourceFuel - 1)
      (targetExtra := targetExtra) (frameBase := frameBase)
      (entryMode := mode) (source := source) (target := target)
      cursor tail hExact hCompiled hMidCtx
      (by simpa [hFuel', nextCtx, Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [hFuel'] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          (Boundary.tail_after_declaration cursor tail hBoundary hExact
            hPlacement hInvariant hSame hReturns)
          hTailSuccess)
  simpa [CursorRuntimeAt, hFuel'] using hResult

/-- Successful stack-only `break` followed by its statically present tail. -/
theorem brk
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .brk :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract frameBase beforeMode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .brk :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra beforeMode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.brk_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSourceScope hTargetDepth hTransition
      hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase beforeMode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) .brk source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful stack-only `continue` followed by its statically present tail. -/
theorem cont
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .cont :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract frameBase beforeMode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .cont :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra beforeMode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.cont_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSourceScope hTargetDepth hTransition
      hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase beforeMode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) .cont source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful stack-only function `leave` with exact return cleanup. -/
theorem leave
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live functionScope : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .leave :: rest }
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
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .leave :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 4
  have hHeadFuel : headExtra + 4 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.leave_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hSourceScope hReturnsLive hReturnsScope hTargetDepth hRetc
      hReturnFrame hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) .leave source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful plain terminal statement with an unreachable exact tail. -/
theorem terminal
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {kind : Assembly.HaltKind} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .terminal kind :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hMemory : Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .terminal kind :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.terminal_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hMemory hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.terminal kind) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful argument-bearing terminal statement with exact memory safety. -/
theorem terminalArgs
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {kind : Assembly.HaltKind} {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .terminalArgs kind args :: rest } beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hArgsSafe : AllocationInteractionSafety.ExprSeqSafe contract args source)
    (hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source))
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .terminalArgs kind args :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State} {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain ⟨afterState, afterLocals, headCode, tail,
      hCompiled, hHead, hExact⟩ :=
    AllocationInteractionForward.CoreCursor.terminalArgs_head
      (sourceFuel := childFuel) (targetExtra := headExtra)
      cursor hArgsSafe hTerminalSafe hBoundary.semantic.invariant
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.terminalArgs kind args) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor sourceFuel targetExtra)
          { stmts := headCode } target) := by
    simpa [childFuel, totalFuel, hHeadFuel] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary hHead'
    hSuccessful (hTailForward tail hExact)

/-- Successful lexical block using the same stack-only recursive capability
for its selected body and exact outer tail. -/
theorem block
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {body : Functions.Block} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := .block body :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hTargetReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .block body :: rest } source))
    (hBodyForward :
      ∀ (bodyCursor : CoreCursor root
          (.lexical scope cursor.planning.nextScope) live body
          beforeState beforeLocals)
        (bodyExtra : Nat),
        AllocationInteractionTargetFuel.Reserve bodyCursor bodyExtra →
          Boundary bodyCursor contract frameBase mode sourceCtx source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 1) body source) →
          CursorRuntimeAt bodyCursor contract frameBase (sourceFuel - 1)
            bodyExtra mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
      sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  obtain ⟨afterState, headCode, tail, targetBlock, bodyCursor,
      hCompiled, hHeadCode, hFinish, hAfterEnv, hAfterLayout,
      _hTransport, hExact⟩ := cursor.blockCursors
  have hBodyAgree : PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hBodyInvariant :=
    hBoundary.semantic.invariant.transport_plan hBodyAgree.symm
      bodyCursor.planWF
  have hBodyBoundary :
      Boundary bodyCursor contract frameBase mode sourceCtx source target :=
    { semantic :=
        { invariant := hBodyInvariant
          sourceScope := hBoundary.semantic.sourceScope
          control := hBoundary.semantic.control
          capacity := hBoundary.semantic.capacity }
      controlAgreement :=
        hBoundary.controlAgreement.transport_plan hBodyAgree.symm
      stackMode := hBoundary.stackMode }
  have hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.block body) source) := by
    have hWhole :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            (childFuel + 1) { stmts := .block body :: rest } source) := by
      rw [hFuel]
      exact hSuccessful
    have hHead :=
      Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead
  have hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          childFuel body source) := by
    rw [Functions.InteractionSemantics.Stmt.openRun_block] at hHeadSuccess
    exact Simulation.Interaction.Successful.bind_left hHeadSuccess
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
  have hHeadLength : headCode.length = bodyCursor.compiled.length + 1 := by
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
      _ = totalFuel := Nat.sub_add_cancel hBodyBase
  have hBodyNestedSize :
      AllocationInteractionTargetFuel.stmtListNestedSize
          bodyCursor.compiled ≤
        AllocationInteractionTargetFuel.stmtListNestedSize
          cursor.compiled := by
    rw [hCompiled,
      AllocationInteractionTargetFuel.stmtListNestedSize_append,
      hHeadCode, hTargetShape,
      AllocationInteractionTargetFuel.stmtListNestedSize_append]
    omega
  have hStrideFuel :
      callStride expressions * (sourceFuel + 1) =
        callStride expressions * (childFuel + 1) +
          callStride expressions := by
    rw [← hFuel, show childFuel + 1 + 1 = (childFuel + 1) + 1 by rfl,
      Nat.mul_add]
    simp
  have hExtraLe : targetExtra ≤ bodyExtra := by
    unfold bodyExtra bodyBase totalFuel targetBudget
    rw [hStrideFuel]
    omega
  have hBodyReserve :
      AllocationInteractionTargetFuel.Reserve bodyCursor bodyExtra := by
    unfold AllocationInteractionTargetFuel.Reserve at hTargetReserve ⊢
    omega
  have hBodyRecursive :=
    hBodyForward bodyCursor bodyExtra hBodyReserve hBodyBoundary
      (by simpa [childFuel] using hBodySuccess)
  have hBodyRel :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx bodyCursor.finalState
          bodyCursor.finalLocals bodyCursor.plan root.returns
          (Functions.Scope.Block.outEnv live body) frameBase mode sourceCtx
          { sourceCtx with scope := Functions.Scope.Block.outEnv live body })
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          childFuel body source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := bodyCursor.compiled } target) := by
    simpa [CursorRuntimeAt, CursorForwardAt, childFuel, hBodyBudget] using
      hBodyRecursive
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
    simp [totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  have hHead :=
    AllocationInteractionControl.block_of_components
      (bodyLive := Functions.Scope.Block.outEnv live body)
      hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
      hAfterInvariant hExtendsAfter hBodyAgree hFinish hCleanupFuel hBodyRel
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    cases targetBlock
    simpa [hHeadCode] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary
    (by simpa [childFuel, totalFuel] using hHead') hSuccessful
    (hTailForward tail hExact)

/-- Successful conditional with recursion only through the selected true
branch. -/
theorem if_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .if_ cond body :: rest } beforeState beforeLocals)
    (hSourceFuel : 1 < sourceFuel)
    (hTargetReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hCondSafe : AllocationInteractionSafety.ExprSafe contract cond source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .if_ cond body :: rest } source))
    (hBodyForward :
      ∀ (bodyCursor : CoreCursor root
          (.lexical scope cursor.planning.nextScope) live body
          beforeState beforeLocals)
        {sourceAfter targetAfter},
        targetBudget bodyCursor (sourceFuel - 2)
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
            targetBudget cursor sourceFuel targetExtra - 2 →
          Boundary bodyCursor contract frameBase mode sourceCtx sourceAfter
            targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 2) body sourceAfter) →
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
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
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
  have hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.if_ cond body) source) := by
    have hWhole :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            (childFuel + 1) { stmts := .if_ cond body :: rest } source) := by
      rw [hFuel]
      exact hSuccessful
    have hHead :=
      Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead
  obtain ⟨afterState, headLower, headCode, tail, loweredCond, condCode,
      targetBody, bodyCursor, hCompiled, _hLower, _hCompile,
      hHeadCode, hLowerCond, hCompileCond, hFinish, hAfterEnv,
      hAfterLayout, hCondScoped, hExact⟩ := cursor.ifCursors
  have hBodyAgree : PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state hAfterEnv hAfterLayout
  have hCond :=
    AllocationInteractionExpressionRecursive.forwardCondition
      hCondSafe hBoundary.semantic.invariant.compiler hCondScoped hLowerCond
      hCompileCond hBoundary.semantic.invariant.state
  have hVars :=
    Locals.InteractionStatePreservation.expr_openEvalCondition_vars cond source
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
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
  have hTargetBlockSize :
      AllocationInteractionTargetFuel.blockSize targetBody =
        AllocationInteractionTargetFuel.stmtListSize targetBody.stmts := by
    cases targetBody
    rfl
  have hBodyWithinParent :
      AllocationInteractionTargetFuel.stmtListSize bodyCursor.compiled ≤
        AllocationInteractionTargetFuel.stmtListNestedSize cursor.compiled := by
    rw [hCompiled,
      AllocationInteractionTargetFuel.stmtListNestedSize_append, hHeadCode]
    simp only [AllocationInteractionTargetFuel.stmtListNestedSize,
      AllocationInteractionTargetFuel.stmtNestedSize]
    rw [hTargetBlockSize, hTargetShape,
      AllocationInteractionTargetFuel.stmtListSize_append]
    omega
  have hFuelGap : sourceFuel + 1 = (bodyFuel + 1) + 2 := by
    simp [bodyFuel]
    omega
  have hStrideFuel :
      callStride expressions * (sourceFuel + 1) =
        callStride expressions * (bodyFuel + 1) +
          callStride expressions * 2 := by
    rw [hFuelGap, Nat.mul_add]
  have hBodySizeEq :=
    AllocationInteractionTargetFuel.stmtListSize_eq bodyCursor.compiled
  have hBodyTargetCapacity :
      targetBudget bodyCursor bodyFuel
            (AllocationInteractionTargetFuel.stmtListNestedSize
              bodyCursor.compiled) ≤
        targetBodyFuel := by
    unfold AllocationInteractionTargetFuel.Reserve at hTargetReserve
    unfold targetBodyFuel totalFuel targetBudget
    rw [hStrideFuel]
    have hStride := eight_le_callStride expressions
    omega
  have hTrue :
      ∀ {sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState beforeLocals cursor.plan live frameBase mode
            sourceAfter targetAfter →
          targetAfter.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block body) sourceAfter) →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract root.lowerCtx afterState
              beforeLocals cursor.plan root.returns live frameBase mode
              sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter) := by
    intro sourceAfter targetAfter hAfter hReturns hSelectedSuccess
    have hBefore := hAfter.transport_state hAfterEnv.symm hAfterLayout.symm
    have hNestedInvariant :=
      hBefore.transport_plan hBodyAgree.symm bodyCursor.planWF
    have hNestedBoundary :
        Boundary bodyCursor contract frameBase mode sourceCtx sourceAfter
          targetAfter :=
      { semantic :=
          { invariant := hNestedInvariant
            sourceScope := hBoundary.semantic.sourceScope
            control := hBoundary.semantic.control
            capacity := hBoundary.semantic.capacity }
        controlAgreement :=
          (hBoundary.controlAgreement.transport_plan hBodyAgree.symm)
            |>.transport_target hReturns
        stackMode := hBoundary.stackMode }
    have hBodySuccess :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            bodyFuel body sourceAfter) := by
      rw [Functions.InteractionSemantics.Stmt.openRun_block]
        at hSelectedSuccess
      exact Simulation.Interaction.Successful.bind_left hSelectedSuccess
    obtain ⟨hCleanupFuel, hBody⟩ :=
      hBodyForward bodyCursor hBodyTargetCapacity hNestedBoundary
        (by simpa [bodyFuel] using hBodySuccess)
    exact
      AllocationInteractionControl.block_of_components
        (bodyLive := Functions.Scope.Block.outEnv live body)
        hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
        hAfter hExtendsAfter hBodyAgree hFinish hCleanupFuel
        (by simpa [bodyFuel, targetBodyFuel, totalFuel] using hBody)
  have hHead :=
    AllocationInteractionControl.if_of_components_successful
      (sourceBodyFuel := bodyFuel) (targetBodyFuel := targetBodyFuel)
      hAfterInvariant hCond hVars
      (by simpa [bodyFuel, hBodyFuel] using hHeadSuccess) hTrue
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.if_ cond body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hBodyFuel, hTargetFuel, hHeadCode] using hHead
  exact cons_same_live cursor tail hExact
    (by simp [Functions.Scope.Stmt.outEnv]) hCompiled hBoundary
    (by simpa [childFuel, totalFuel] using hHead') hSuccessful
    (hTailForward tail hExact)

/-- Successful switch with recursion only through the exact selected branch. -/
theorem switch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State} {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel targetExtra : Nat} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live
      { stmts := .switch scrutinee cases defaultBody :: rest }
      beforeState beforeLocals)
    (hSourceFuel : 1 < sourceFuel)
    (hTargetReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hScrutineeSafe :
      AllocationInteractionSafety.ExprSafe contract scrutinee source)
    (hBoundary :
      Boundary cursor contract frameBase mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .switch scrutinee cases defaultBody :: rest } source))
    (hBodyForward :
      ∀ {value} {selected : Functions.Block}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (hSelect :
          Functions.Source.Switch.select value cases defaultBody =
            some selected)
        (bodyCursor : CoreCursor root
          (.lexical scope selectedPlanning.nextScope) live selected
          selectedStart beforeLocals)
        {sourceAfter targetAfter},
        targetBudget bodyCursor (sourceFuel - 2)
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
            targetBudget cursor sourceFuel targetExtra - 2 →
          Boundary bodyCursor contract frameBase mode sourceCtx sourceAfter
            targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 2) selected sourceAfter) →
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
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract frameBase (sourceFuel - 1)
              (targetExtra + callStride expressions) tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract frameBase sourceFuel targetExtra mode
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
  have hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.switch scrutinee cases defaultBody) source) := by
    have hWhole :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            (childFuel + 1)
            { stmts := .switch scrutinee cases defaultBody :: rest }
            source) := by
      rw [hFuel]
      exact hSuccessful
    have hHead :=
      Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead
  obtain ⟨afterState, headLower, headCode, tail, loweredScrutinee,
      loweredCases, afterCases, loweredDefault, scrutineeCode,
      compiledCases, compiledDefault, components⟩ := cursor.switchCursors
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state
      components.afterEnv components.afterLayout
  have hScrutinee :=
    AllocationInteractionExpressionRecursive.forwardOne hScrutineeSafe
      hBoundary.semantic.invariant.compiler components.scrutineeScoped
      components.lowerScrutinee components.compileScrutinee
      hBoundary.semantic.invariant.state
  have hVars :=
    Locals.InteractionStatePreservation.expr_openEvalOne_vars scrutinee source
  have hSelection :
      ∀ value,
        AllocationInteractionControl.SwitchSelection cases defaultBody
          compiledCases compiledDefault value := by
    intro value
    have hCompiledSelection :=
      Locals.InteractionPreservation.Stmt.SwitchCompile.selectedRel_of_compile
        beforeLocals value components.compileCases components.compileDefault
    cases hSourceSelect :
        Functions.Source.Switch.select value cases defaultBody with
    | none =>
        have hLowerSelect :=
          AllocationLowering.lowerSwitch_select_none components.lowerCases
            components.lowerDefault hSourceSelect
        rw [hLowerSelect] at hCompiledSelection
        exact .none hSourceSelect hCompiledSelection.none_target
    | some selected =>
        obtain ⟨selectedLowered, selectedStart, selectedFinal,
            hLowerSelect, _hLowerBody, _hSelectedEnv,
            _hSelectedLayout⟩ :=
          AllocationLowering.lowerSwitch_select_some
            components.lowerCases components.lowerDefault hSourceSelect
        rw [hLowerSelect] at hCompiledSelection
        obtain ⟨selectedTarget, _selectedCode, _selectedLocals,
            hTargetSelect, _hCompileSelected, _hFinishSelected⟩ :=
          hCompiledSelection.some_parts
        exact .some selected selectedTarget hSourceSelect hTargetSelect
  have hSelected :
      ∀ {value selected selectedTarget sourceAfter targetAfter},
        Functions.Source.Switch.select value cases defaultBody =
            some selected →
        Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault = some selectedTarget →
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState beforeLocals cursor.plan live frameBase mode
            sourceAfter targetAfter →
        targetAfter.returns = target.returns →
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            bodyFuel (.block selected) sourceAfter) →
        Simulation.Interaction.Rel
          (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
            cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            bodyFuel (.block selected) sourceAfter)
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetBodyFuel selectedTarget targetAfter) := by
    intro value selected selectedTarget sourceAfter targetAfter
      hSourceSelect hTargetSelect hAfter hReturns hSelectedSuccess
    obtain ⟨selectedAfter, selectedHeadLower, selectedHeadCode, selectedTail,
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
        Boundary bodyCursor contract frameBase mode sourceCtx sourceAfter
          targetAfter :=
      { semantic :=
          { invariant := hNestedInvariant
            sourceScope := hBoundary.semantic.sourceScope
            control := hBoundary.semantic.control
            capacity := hBoundary.semantic.capacity }
        controlAgreement :=
          (hBoundary.controlAgreement.transport_plan hBodyAgree.symm)
            |>.transport_target hReturns
        stackMode := hBoundary.stackMode }
    have hExtendsSelected :
        AllocationLowering.StateExtends live selectedStart
          bodyCursor.finalState :=
      AllocationLowering.lowerBlockOpen_stateExtends
        bodyCursor.sourceScoped bodyCursor.lower
    have hExtendsAfter :
        AllocationLowering.StateExtends live afterState bodyCursor.finalState := by
      rcases hExtendsSelected with ⟨dropped, hLayout, hFresh, hSlots⟩
      refine ⟨dropped, ?_, hFresh, ?_⟩
      · rw [hLayout, hSelectedLayout, components.afterLayout]
      · intro name hLive
        exact (hSlots name hLive).trans
          (congrArg (AllocationSupport.lookupSlot? name)
            (hSelectedEnv.trans components.afterEnv.symm))
    have hBodySuccess :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            bodyFuel selected sourceAfter) := by
      rw [Functions.InteractionSemantics.Stmt.openRun_block]
        at hSelectedSuccess
      exact Simulation.Interaction.Successful.bind_left hSelectedSuccess
    obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
      AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
    have hActualTargetSize :
        AllocationInteractionTargetFuel.blockSize selectedTarget =
          AllocationInteractionTargetFuel.stmtListSize selectedTarget.stmts := by
      cases selectedTarget
      rfl
    have hBodyWithinTarget :
        AllocationInteractionTargetFuel.stmtListSize bodyCursor.compiled ≤
          AllocationInteractionTargetFuel.blockSize selectedTarget := by
      rw [hActualTargetSize, hTargetShape,
        AllocationInteractionTargetFuel.stmtListSize_append]
      omega
    have hTargetWithinSwitch :=
      AllocationInteractionTargetFuel.selected_block_size_le hTargetSelect
    have hSwitchWithinParent :
        AllocationInteractionTargetFuel.caseListSize compiledCases +
            AllocationInteractionTargetFuel.defaultSize compiledDefault ≤
          AllocationInteractionTargetFuel.stmtListNestedSize
            cursor.compiled := by
      rw [components.compiled,
        AllocationInteractionTargetFuel.stmtListNestedSize_append,
        components.codeHead]
      simp only [AllocationInteractionTargetFuel.stmtListNestedSize,
        AllocationInteractionTargetFuel.stmtNestedSize]
      omega
    have hBodyWithinParent :
        AllocationInteractionTargetFuel.stmtListSize bodyCursor.compiled ≤
          AllocationInteractionTargetFuel.stmtListNestedSize cursor.compiled :=
      hBodyWithinTarget.trans (hTargetWithinSwitch.trans hSwitchWithinParent)
    have hFuelGap : sourceFuel + 1 = (bodyFuel + 1) + 2 := by
      simp [bodyFuel]
      omega
    have hStrideFuel :
        callStride expressions * (sourceFuel + 1) =
          callStride expressions * (bodyFuel + 1) +
            callStride expressions * 2 := by
      rw [hFuelGap, Nat.mul_add]
    have hBodySizeEq :=
      AllocationInteractionTargetFuel.stmtListSize_eq bodyCursor.compiled
    have hBodyTargetCapacity :
        targetBudget bodyCursor bodyFuel
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
          targetBodyFuel := by
      unfold AllocationInteractionTargetFuel.Reserve at hTargetReserve
      unfold targetBodyFuel totalFuel targetBudget
      rw [hStrideFuel]
      have hStride := eight_le_callStride expressions
      omega
    obtain ⟨hCleanupFuel, hBody⟩ :=
      hBodyForward hSourceSelect bodyCursor hBodyTargetCapacity
        hNestedBoundary (by simpa [bodyFuel] using hBodySuccess)
    exact
      AllocationInteractionControl.block_of_components
        (bodyLive := Functions.Scope.Block.outEnv live selected)
        hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
        hAfter hExtendsAfter hBodyAgree hFinish hCleanupFuel
        (by simpa [bodyFuel, targetBodyFuel, totalFuel] using hBody)
  have hHead :=
    AllocationInteractionControl.switch_of_components_successful
      (sourceBodyFuel := bodyFuel) (targetBodyFuel := targetBodyFuel)
      hAfterInvariant hScrutinee hVars
      (by simpa [bodyFuel, hBodyFuel] using hHeadSuccess)
      hSelection hSelected
  have hHead' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.switch scrutinee cases defaultBody) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hBodyFuel, hTargetFuel, components.codeHead] using hHead
  exact cons_same_live cursor tail components.exactTail
    (by simp [Functions.Scope.Stmt.outEnv]) components.compiled hBoundary
    (by simpa [childFuel, totalFuel] using hHead') hSuccessful
    (hTailForward tail components.exactTail)

end CursorRuntimeAt

namespace SelectedCallee

theorem bodyCode_size_le_callStride
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact) :
    AllocationInteractionTargetFuel.stmtListSize prepared.bodyCode <=
      callStride expressions := by
  apply selected_body_code_size_le_callStride
    (program := expressions) (name := name)
    (proc := artifact.lowerProc)
    (bodyPrefix :=
      prepared.markerCode ++ prepared.paramCode ++ prepared.returnCode)
    (bodySuffix :=
      Locals.codeStmt prepared.returnValueCode ++
        Locals.codeStmt prepared.cleanup)
    artifact.targetLookup
  simpa [List.append_assoc] using prepared.procBody

/-- Compose the exact all-stack callee prelude with its canonical recursively
preserved body. -/
theorem body_of_cursor_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel fuelBound targetExtra : Nat}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hZero :
      forall localName,
        localName ∈ artifact.slots.returns.map Prod.fst ->
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hSourceFuel : sourceFuel < fuelBound)
    (hBodyForward :
      forall {bodyTarget : Structured.RunState},
        sourceFuel < fuelBound ->
        AllocationContext.ActivationInvariant contract artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase prepared.bodyMode source bodyTarget ->
          CursorRuntimeAt (prepared.rootCursor hProgramScoped) contract
            frameBase sourceFuel targetExtra prepared.bodyMode sourceCtx source
            bodyTarget) :
    ∃ targetFuel,
      0 < targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            targetBudget (prepared.rootCursor hProgramScoped) sourceFuel
              targetExtra ∧
      Simulation.Interaction.Rel
        (OpenControlResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            fn.body)
          frameBase artifact.mode sourceCtx
          { sourceCtx with
            scope := Functions.Scope.Block.outEnv
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
  obtain
      ⟨_afterParams, bodyTarget, _paramFuel, _returnFuel, _preludeFuel,
        _hParamFuel, _hReturnFuel, _hMarkers, _hParams, _hReturns,
        _hPreludeFuel, _hPreludeLength, _hPrelude,
        hPreludeAt, hInvariant⟩ :=
    prepared.body_entry_stack hNeedsFrame hEntry hZero hStackLength
  have hBody := hBodyForward hSourceFuel hInvariant
  have hBody' :=
    AllocationInteractionComposition.prepend_frame hSetupFrame hBody
  let bodyFuel :=
    targetBudget (prepared.rootCursor hProgramScoped) sourceFuel targetExtra
  have hBodyFuel : 0 < bodyFuel := by
    simp [bodyFuel, targetBudget, callStride, Nat.mul_succ]
  let targetFuel :=
    prepared.markerCode.length + prepared.paramCode.length +
      prepared.returnCode.length + bodyFuel
  refine ⟨targetFuel, by simp [targetFuel]; omega, rfl, ?_⟩
  exact
    prepared.prelude_then_body hBodyFuel hPreludeAt
      (by simpa [CursorRuntimeAt, CursorForwardAt, bodyFuel] using hBody')

/-- Canonical `runBody` context for an all-stack selected callee. -/
theorem body_of_function_context
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel fuelBound targetExtra : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hZero :
      forall localName,
        localName ∈ artifact.slots.returns.map Prod.fst ->
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReturnFrame : target.returns ≠ [])
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode <=
        targetExtra)
    (hSourceFuel : sourceFuel < fuelBound)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation) contract fuelBound) :
    ∃ targetFuel,
      0 < targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (OpenControlResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv (fn.returns ++ fn.params) fn.body)
          frameBase artifact.mode
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          { Functions.Source.Effectful.FunDef.bodyCtx fn with
            scope := Functions.Scope.Block.outEnv
              (fn.returns ++ fn.params) fn.body })
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          { stmts :=
              prepared.markerCode ++ prepared.paramCode ++
                prepared.returnCode ++ prepared.bodyCode }
          target) := by
  let compilerLive :=
    (artifact.slots.returns.map Prod.fst).reverse ++
      (artifact.slots.params.map Prod.fst).reverse
  let sourceLive := fn.returns ++ fn.params
  have hLive :
      forall localName,
        localName ∈ compilerLive ↔ localName ∈ sourceLive := by
    intro localName
    simp [compilerLive, sourceLive, artifact.slotsMatch.2.1,
      artifact.slotsMatch.2.2]
  let bodyCursor :=
    (prepared.rootCursor hProgramScoped).transport_live hLive
  have hSetupFrame : SameFrame artifact.mode prepared.bodyMode := by
    exact SameFrame.atStackDepth artifact.mode
      (currentStackOrder prepared.plan compilerLive).length
  have hEntryToReturnControl :
      Locals.Ctx.SameControl artifact.entryCtx prepared.returnCtx :=
    (Locals.Block.compileOpen_sameControl prepared.compileParams).trans
      (Locals.Block.compileOpen_sameControl prepared.compileReturns)
  have hLeaveDepth : prepared.returnCtx.leaveDepth? = some 0 := by
    simpa [AllocationInteractionCall.SelectedCallee.Artifact.entryCtx,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial] using hEntryToReturnControl.leaveDepth.symm
  have hLeaveRetc : prepared.returnCtx.leaveRetc = fn.returns.length := by
    simpa [AllocationInteractionCall.SelectedCallee.Artifact.entryCtx,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial] using hEntryToReturnControl.leaveRetc.symm
  obtain
      ⟨_afterParams, bodyTarget, _paramFuel, _returnFuel, _preludeFuel,
        _hParamFuel, _hReturnFuel, _hMarkers, _hParams, _hReturns,
        _hPreludeFuel, _hPreludeLength, _hPrelude, hPreludeAt,
        hInvariant⟩ :=
    prepared.body_entry_stack hNeedsFrame hEntry hZero hStackLength
  have hBodyReturns : bodyTarget.returns = target.returns := by
    have hAll :=
      Expressions.InteractionReturns.Block.openRun_returns expressions
        (prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + 1)
        { stmts :=
            prepared.markerCode ++
              (prepared.paramCode ++ prepared.returnCode) }
        target
    rw [hPreludeAt 1 (by omega)] at hAll
    cases hAll with
    | done hDone =>
        simpa [Structured.InteractionReturns.OutcomeReturnsEq] using hDone
  have hBodyReturnFrame : bodyTarget.returns ≠ [] := by
    intro hEmpty
    apply hReturnFrame
    rw [← hBodyReturns, hEmpty]
  have hBodyBoundary :
      Boundary bodyCursor contract frameBase prepared.bodyMode
        (Functions.Source.Effectful.FunDef.bodyCtx fn) source bodyTarget :=
    { semantic :=
        { invariant := hInvariant.transport_live hLive
          sourceScope := rfl
          control :=
            AllocationInteractionStatement.ControlScopesWithin.functionBody fn
          capacity := by
            have hBodyMode : prepared.bodyMode = .stack := by
              simp [AllocationInteractionCall.SelectedCallee.Prepared.bodyMode,
                AllocationInteractionCall.SelectedCallee.Artifact.mode,
                ActivationMode.atStackDepth, hNeedsFrame]
            rw [hBodyMode]
            trivial }
      controlAgreement :=
        AllocationInteractionControlAgreement.Agreement.functionBody
          (by simp [Functions.Source.Effectful.FunDef.bodyCtx,
            Functions.Source.Ctx.initial,
            Functions.Source.Ctx.withLeaveScope])
          (by simp [Functions.Source.Effectful.FunDef.bodyCtx,
            Functions.Source.Ctx.initial,
            Functions.Source.Ctx.withLeaveScope])
          hLeaveDepth hLeaveRetc hBodyReturnFrame
      stackMode := by
        simp [AllocationInteractionCall.SelectedCallee.Prepared.bodyMode,
          AllocationInteractionCall.SelectedCallee.Artifact.mode,
          ActivationMode.atStackDepth, hNeedsFrame] }
  have hBodyRaw :=
    hRecursive bodyCursor hSourceFuel hBodyBoundary
      (by
        simpa [AllocationInteractionTargetFuel.Reserve, bodyCursor] using
          hTargetReserve)
      hSuccess (targetExtra := targetExtra)
  let bodyFuel := targetBudget bodyCursor sourceFuel targetExtra
  have hBodyFuel : 0 < bodyFuel := by
    simp [bodyFuel, targetBudget, callStride, Nat.mul_succ]
  have hBody :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv sourceLive fn.body)
          frameBase prepared.bodyMode
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          { Functions.Source.Effectful.FunDef.bodyCtx fn with
            scope := Functions.Scope.Block.outEnv sourceLive fn.body })
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
          { stmts := prepared.bodyCode } bodyTarget) := by
    simpa [CursorRuntimeAt, bodyFuel, bodyCursor, sourceLive] using hBodyRaw
  have hBodyFromEntry :=
    AllocationInteractionComposition.prepend_frame hSetupFrame hBody
  let totalFuel :=
    prepared.markerCode.length + prepared.paramCode.length +
      prepared.returnCode.length + bodyFuel
  refine ⟨totalFuel, by simp [totalFuel]; omega, ?_, ?_⟩
  · simp [totalFuel, bodyFuel, bodyCursor, targetBudget,
      AllocationInteractionCall.SelectedCallee.Prepared.rootCursor,
      AllocationInteractionCall.SelectedCallee.Prepared.rootArtifact,
      RootArtifact.cursor, CoreCursor.transport_live]
  · simpa [totalFuel, sourceLive] using
      prepared.prelude_then_body hBodyFuel hPreludeAt hBodyFromEntry

/-- Complete the emitted body and return epilogue of an all-stack selected
callee. -/
theorem complete_body
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {frameBase sourceFuel fuelBound targetExtra : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hZero :
      forall localName,
        localName ∈ artifact.slots.returns.map Prod.fst ->
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReturnFrame : target.returns ≠ [])
    (hTargetExtra : 3 <= targetExtra)
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode <=
        targetExtra)
    (hSourceFuel : sourceFuel < fuelBound)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation) contract fuelBound) :
    ∃ targetFuel,
      0 < targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (AllocationInteractionCallResult.OpenBodyResultRel
          contract fn.returns target)
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          artifact.lowerProc.body target) := by
  obtain ⟨targetFuel, hTargetFuel, hTargetFuelEq, hBody⟩ :=
    body_of_function_context prepared hProgramScoped hNeedsFrame hEntry hZero
      hStackLength hReturnFrame hTargetReserve hSourceFuel hSuccess hRecursive
  have hReturnsLive :
      forall localName,
        localName ∈ fn.returns ->
          localName ∈
            Functions.Scope.Block.outEnv
              (fn.returns ++ fn.params) fn.body := by
    intro localName hName
    exact Functions.Scope.Block.mem_outEnv (by simp [hName])
  refine ⟨targetFuel, hTargetFuel, hTargetFuelEq, ?_⟩
  exact
    AllocationInteractionCallResult.SelectedCallee.complete_body_of_rel
      prepared hReturnsLive (by
        rw [hTargetFuelEq]
        omega) hBody

/-- Run an all-stack compiler-selected callee through the canonical internal
call wrappers. -/
theorem complete_call
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {sourceFuel fuelBound targetExtra : Nat}
    {args callerStack : List Word}
    {paramStore : Locals.Source.Store}
    {sourceAfterArgs : SourceState} {targetCaller : TargetState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hSplit :
      Structured.StackFrame.splitArgs? artifact.lowerProc.argc
          targetCaller.evm.stack =
        some (args.reverse, callerStack))
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params 0 .stack
        (AllocationInteractionCall.CalleeEntry.sourceState
          sourceAfterArgs fn.returns paramStore)
        (AllocationInteractionCall.CalleeEntry.structuredState
          targetCaller args.reverse callerStack fn.returns.length))
    (hZero :
      forall localName,
        localName ∈ artifact.slots.returns.map Prod.fst ->
        (AllocationInteractionCall.CalleeEntry.sourceState
          sourceAfterArgs fn.returns paramStore).vars localName =
            some AllocationSupport.zeroWord)
    (hStackLength :
      (AllocationInteractionCall.CalleeEntry.structuredState
        targetCaller args.reverse callerStack fn.returns.length).evm.stack.length =
        artifact.entryCtx.layout.length)
    (hTargetExtra : 3 <= targetExtra)
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode <=
        targetExtra)
    (hSourceFuel : sourceFuel < fuelBound)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation) contract fuelBound) :
    ∃ targetFuel,
      0 < targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (AllocationInteractionCallResult.OpenCallResultRel
          contract targetCaller callerStack)
        (Functions.InteractionSemantics.FunDef.openRunBody
          program fn args (sourceFuel + 1) sourceAfterArgs)
        (Expressions.InteractionSemantics.Stmt.openRun
          expressions (targetFuel + 1) (.call name) targetCaller) := by
  let targetEntry :=
    AllocationInteractionCall.CalleeEntry.structuredState
      targetCaller args.reverse callerStack fn.returns.length
  obtain ⟨targetFuel, hTargetFuel, hTargetFuelEq, hBody⟩ :=
    complete_body prepared hProgramScoped hNeedsFrame hEntry hZero
      hStackLength
      (by
        simp [targetEntry,
          AllocationInteractionCall.CalleeEntry.structuredState,
          Structured.RunState.pushReturn])
      hTargetExtra hTargetReserve hSourceFuel hSuccess hRecursive
  refine ⟨targetFuel, hTargetFuel, hTargetFuelEq, ?_⟩
  exact
    AllocationInteractionCallResult.CallAttachment.of_body
      hInsert artifact.targetLookup prepared.procRetc hSplit
      (by simpa [targetEntry] using hBody)

/-- Realize one all-stack selected callee from a completed canonical argument
phase, including suspended-caller recovery and exact recursive execution. -/
theorem stack_after_arguments
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {callerFrameBase bodyFuel fuelBound targetExtra : Nat}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterArgs : TargetState}
    {argValues : List Word} {paramStore : Locals.Source.Store}
    (hNeedsFrame : artifact.needsFrame = false)
    (hArgs :
      ActivationExprResultRel contract callerPlan callerLive 0
        callerFrameBase argValues.length .stack sourceAfterArgs targetInitial
        targetAfterArgs argValues)
    (hInsert :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (hTargetExtra : 3 <= targetExtra)
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode <=
        targetExtra)
    (hBodyFuel : bodyFuel < fuelBound)
    (hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation) contract fuelBound) :
    ∃ callerBase : TargetState,
      ∃ targetEntry : TargetState,
      ∃ targetFuel : Nat,
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
          .stack sourceAfterArgs callerBase ∧
        callerBase.evm.stack = targetInitial.evm.stack ∧
        targetFuel =
          prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length +
              (targetExtra + prepared.bodyCode.length +
                callStride expressions * (bodyFuel + 1)) ∧
        Simulation.Interaction.Rel
          (AllocationInteractionCallResult.OpenCallResultRel
            contract targetAfterArgs targetInitial.evm.stack)
          (Functions.InteractionSemantics.FunDef.openRunBody
            program fn argValues (bodyFuel + 1) sourceAfterArgs)
          (Expressions.InteractionSemantics.Stmt.openRun
            expressions (targetFuel + 1) (.call name) targetAfterArgs) := by
  let targetEntry :=
    AllocationInteractionCall.CalleeEntry.structuredState targetAfterArgs
      argValues.reverse targetInitial.evm.stack fn.returns.length
  obtain ⟨hEntry, hZero, _hDefined, hEntryStackLength⟩ :=
    prepared.stack_entry_of_arguments hNeedsFrame hArgs hInsert
  have hArgLength : argValues.length = fn.params.length :=
    Functions.Source.Store.insertMany_length hInsert
  have hSplit :
      Structured.StackFrame.splitArgs? artifact.lowerProc.argc
          targetAfterArgs.evm.stack =
        some (argValues.reverse, targetInitial.evm.stack) := by
    apply AllocationInteractionCall.CalleeEntry.splitArgs_of_arguments hArgs
    rw [prepared.procArgc, hArgLength]
    simp [hNeedsFrame]
  obtain ⟨targetFuel, _hPositive, hTargetFuel, hCall⟩ :=
    complete_call prepared hProgramScoped hNeedsFrame hInsert hSplit
      (by simpa [targetEntry] using hEntry) hZero hEntryStackLength
      hTargetExtra hTargetReserve hBodyFuel hBodySuccess hRecursive
  let callerBase :=
    AllocationInteractionCall.PreparedArguments.callerState
      targetAfterArgs targetInitial
  obtain ⟨hCallerRel, hCallerStack⟩ :=
    AllocationInteractionCall.PreparedArguments.caller_state_of_semantic_result
      hArgs
  exact
    ⟨callerBase, targetEntry, targetFuel,
      by simpa [callerBase] using hCallerRel,
      by simpa [callerBase] using hCallerStack,
      hTargetFuel, hCall⟩

end SelectedCallee

namespace CallComponents

/-- One real all-stack call cursor preserves its complete source statement and
compiler-emitted target head. -/
theorem stack_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live targets : List Functions.Name}
    {functionName : Functions.Name} {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx}
    (components : AllocationInteractionCall.CallComponents cursor)
    {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation functionName fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions = some fn)
    (hNeedsFrame : artifact.needsFrame = false)
    {frameBase sourceFuel targetExtra : Nat}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe :
      AllocationInteractionSafety.ArgListSafe
        program.memoryContract args source)
    (hBoundary :
      Boundary cursor program.memoryContract frameBase .stack sourceCtx
        source target)
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.call targets functionName args) source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        program.memoryContract sourceFuel) :
    Simulation.Interaction.Rel
      (OpenControlResultRel program.memoryContract root.lowerCtx lowerState
        localsCtx cursor.plan root.returns live frameBase .stack sourceCtx
        sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceFuel - 1) (.call targets functionName args) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetBudget cursor sourceFuel targetExtra)
        { stmts := components.headCode } target) := by
  classical
  let callFuel := sourceFuel - 2
  let bodyFuel := sourceFuel - 3
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let callTargetFuel := totalFuel - 3
  let callBase :=
    prepared.markerCode.length + prepared.paramCode.length +
      prepared.returnCode.length + prepared.bodyCode.length +
        callStride expressions * (bodyFuel + 1)
  let selectedExtra := callTargetFuel - callBase
  have hChildFuel : callFuel + 1 = sourceFuel - 1 := by
    simp [callFuel]
    omega
  have hBodyFuel : bodyFuel + 1 = callFuel := by
    simp [bodyFuel, callFuel]
    omega
  have hStmtScoped :
      Functions.Scope.Stmt.Scoped live
        (.call targets functionName args) :=
    cursor.sourceScoped.1
  have hTargetsNodup : targets.Nodup := hStmtScoped.1
  have hTargetsLive : forall target, target ∈ targets -> target ∈ live :=
    hStmtScoped.2.1
  have hArgsScoped :
      forall arg, arg ∈ args -> Functions.Scope.ExprScoped live arg :=
    hStmtScoped.2.2
  have hHeadSuccess' :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (callFuel + 1) (.call targets functionName args) source) := by
    rw [hChildFuel]
    exact hHeadSuccess
  have hContinuations :=
    Functions.InteractionSemantics.Stmt.successful_openRun_call_continuations
      program sourceCtx callFuel targets functionName args source
      hTargetsNodup hHeadSuccess'
  have hVars :=
    Functions.InteractionSemantics.ArgList.openEval_vars_eq args source
  have hArgsCompile := stack_compileArgs components hNeedsFrame
  have hArgsRel :=
    AllocationInteractionCall.ArgList.forward hSafe
      hBoundary.semantic.invariant.compiler hArgsScoped
      components.lowerArgs hArgsCompile hBoundary.semantic.invariant.state
  have hArgsWithContinuations :=
    Simulation.Interaction.Rel.strengthen_left hArgsRel hContinuations
  have hArgsStrong :=
    Simulation.Interaction.Rel.strengthen_left hArgsWithContinuations hVars
  have hExtra := selected_call_extra (cursor := cursor)
    (targetExtra := targetExtra) prepared hSourceFuel
  change 2 * callStride expressions + 3 <= selectedExtra ∧
    callBase + selectedExtra = callTargetFuel at hExtra
  have hBodyCodeSize := SelectedCallee.bodyCode_size_le_callStride prepared
  have hSelectedReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode <=
        selectedExtra :=
    (AllocationInteractionTargetFuel.nestedSize_le_size prepared.bodyCode).trans
      (hBodyCodeSize.trans (by omega))
  have hTotalFuel : 2 <= totalFuel := by
    have hStride := eight_le_callStride expressions
    change 2 <= targetExtra + cursor.compiled.length +
      callStride expressions * (sourceFuel + 1)
    have hMul := Nat.mul_le_mul hStride (show 1 <= sourceFuel + 1 by omega)
    omega
  let callRest : List Expressions.Stmt :=
    [.call functionName] ++ Locals.codeStmt components.stores
  have hCore :
      Simulation.Interaction.Rel
        (OpenControlResultRel program.memoryContract root.lowerCtx lowerState
          localsCtx cursor.plan root.returns live frameBase .stack sourceCtx
          sourceCtx)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.ArgList.openEval args source)
          (fun result =>
            Simulation.Interaction.bind
              (Functions.InteractionSemantics.FunDef.openRunBody
                program fn result.2 callFuel result.1)
              (Functions.InteractionSemantics.Stmt.finishCall targets
                sourceCtx result.1)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            components.argsCode target)
          (fun targetAfterArgs =>
            Expressions.InteractionSemantics.Block.openRun expressions
              (totalFuel - 1) { stmts := callRest } targetAfterArgs)) := by
    apply Simulation.Interaction.Rel.bind_custom hArgsStrong
    intro sourceDone targetDone hDone
    rcases hDone with ⟨⟨hArgsDone, hContinuation⟩, hVarsDone⟩
    cases hArgsDone with
    | error _ => exact False.elim hContinuation
    | @ok sourceResult targetAfterArgs hArgRel =>
        rcases sourceResult with ⟨sourceAfterArgs, argValues⟩
        obtain ⟨selectedFn, hSelectedFind, hFinish⟩ := hContinuation
        have hFn : selectedFn = fn := by
          rw [hFind] at hSelectedFind
          exact (Option.some.inj hSelectedFind).symm
        subst selectedFn
        have hRunBodySuccess :
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.FunDef.openRunBody
                program fn argValues callFuel sourceAfterArgs) := by
          apply Simulation.Interaction.AllDone.mono hFinish
          intro callDone hDone
          cases callDone with
          | error _ => exact hDone
          | ok _ => trivial
        obtain ⟨paramStore, hInsert, hBodySuccess⟩ :=
          Functions.InteractionSemantics.FunDef.successful_openRunBody_parts
            program fn argValues bodyFuel sourceAfterArgs (by
              rw [hBodyFuel]
              exact hRunBodySuccess)
        have hValuesLength : argValues.length = args.length :=
          hArgRel.valuesLength
        have hArgRel' :
            ActivationExprResultRel program.memoryContract cursor.plan live 0
              frameBase argValues.length .stack sourceAfterArgs target
              targetAfterArgs argValues := by
          simpa [hValuesLength] using hArgRel
        have hArgsVars : sourceAfterArgs.vars = source.vars := hVarsDone
        obtain
            ⟨callerBase, _targetEntry, selectedTargetFuel, hCallerRel,
              hCallerStack, hSelectedFuel, hBranch⟩ :=
          SelectedCallee.stack_after_arguments
            (targetExtra := selectedExtra) prepared hProgramScoped
            hNeedsFrame hArgRel' hInsert (by omega) hSelectedReserve
            (by omega) hBodySuccess hRecursive
        have hSelectedTargetFuel : selectedTargetFuel = callTargetFuel := by
          rw [hSelectedFuel]
          dsimp [callBase] at hExtra
          omega
        rw [hSelectedTargetFuel] at hBranch
        have hCallerStack' : callerBase.evm.stack = target.evm.stack :=
          hCallerStack
        have hResult :=
          AllocationInteractionCallStatement.finish
            (expressions := expressions) (storesFuel := callTargetFuel + 1)
            (returns := root.returns) (controlCtx := sourceCtx)
            hBoundary.semantic.invariant hArgsVars hCallerRel rfl
            hCallerStack' hBranch (by simpa [hBodyFuel] using hFinish)
            hTargetsLive hTargetsNodup
            components.stores_eq (by omega)
        have hRemainderFuel : callTargetFuel + 2 = totalFuel - 1 := by
          simp [callTargetFuel]
          have hEnough : 3 <= totalFuel := by omega
          omega
        simp only [Simulation.Interaction.bind_done_ok]
        simp only [callRest, List.singleton_append, List.cons_append,
          List.nil_append]
        rw [show totalFuel - 1 = callTargetFuel + 2 from
          hRemainderFuel.symm,
          Expressions.InteractionSemantics.Block.openRun_cons]
        unfold Expressions.InteractionSemantics.Stmt.openRun at hBranch
        simpa [hBodyFuel] using hResult
  have hHeadCode :
      components.headCode =
        Locals.codeStmt components.argsCode ++ callRest := by
    rw [components.headCode_eq, stack_releaseCode components hNeedsFrame]
    simp [callRest, List.append_assoc]
  rw [hHeadCode, show targetBudget cursor sourceFuel targetExtra = totalFuel
    from rfl]
  rw [openRun_code_prefix expressions totalFuel components.argsCode callRest
    target hTotalFuel]
  rw [← hChildFuel, Functions.InteractionSemantics.Stmt.openRun_call]
  simp only [hTargetsNodup, if_pos, hFind, Option.elim_some,
    Simulation.Interaction.bind_done_ok]
  simpa [callFuel, bodyFuel, totalFuel, callRest] using hCore

end CallComponents

namespace CoreCursor

/-- Extract one compiler-selected all-stack call head and its exact tail. -/
theorem call_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live targets : List Functions.Name}
    {functionName : Functions.Name} {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    (cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx)
    (hAllStack : AllFunctionsStack compilation)
    (hProgramScoped : program.Scoped)
    {frameBase sourceFuel targetExtra : Nat}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ArgListSafe
      program.memoryContract args source)
    (hBoundary :
      Boundary cursor program.memoryContract frameBase .stack sourceCtx
        source target)
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.call targets functionName args) source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        program.memoryContract sourceFuel) :
    ∃ (headCode : List Expressions.Stmt)
      (tail : CoreCursor root scope live { stmts := rest }
        lowerState localsCtx),
      cursor.compiled = headCode ++ tail.compiled ∧
        ExactTail cursor tail ∧
        Simulation.Interaction.Rel
          (OpenControlResultRel program.memoryContract root.lowerCtx
            lowerState localsCtx cursor.plan root.returns live frameBase
            .stack sourceCtx sourceCtx)
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            (sourceFuel - 1) (.call targets functionName args) source)
          (Expressions.InteractionSemantics.Block.openRun expressions
            (targetBudget cursor sourceFuel targetExtra)
            { stmts := headCode } target) := by
  classical
  let components := Classical.choice
    (AllocationInteractionCall.CoreCursor.callComponents cursor)
  obtain ⟨fn, hFind, artifact, ⟨prepared⟩, _hSlots, hNeedsFrame⟩ :=
    selectedCallee_stack components hAllStack
  have hHead :=
    CallComponents.stack_runtime_head components prepared hProgramScoped
      hFind hNeedsFrame hSourceFuel hSafe hBoundary hHeadSuccess hRecursive
      (targetExtra := targetExtra)
  exact
    ⟨components.headCode, components.tail, components.compiled,
      components.exactTail, hHead⟩

end CoreCursor

namespace CursorRuntimeAt

/-- Recursive compiler-selected all-stack call followed by its exact tail. -/
theorem call
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live targets : List Functions.Name}
    {functionName : Functions.Name} {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    (cursor : CoreCursor root scope live
      { stmts := .call targets functionName args :: rest }
      lowerState localsCtx)
    (hAllStack : AllFunctionsStack compilation)
    (hProgramScoped : program.Scoped)
    {frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ArgListSafe
      program.memoryContract args source)
    (hBoundary :
      Boundary cursor program.memoryContract frameBase mode sourceCtx
        source target)
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.call targets functionName args) source))
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .call targets functionName args :: rest } source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        program.memoryContract sourceFuel)
    (hTailForward :
      ∀ (tail : CoreCursor root scope live { stmts := rest }
          lowerState localsCtx),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail program.memoryContract frameBase tailMode sourceCtx
              sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail program.memoryContract frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    CursorRuntimeAt cursor program.memoryContract frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hMode : mode = .stack := hBoundary.stackMode
  subst mode
  obtain ⟨headCode, tail, hCompiled, hExact, hHead⟩ :=
    CoreCursor.call_runtime_head cursor hAllStack hProgramScoped hSourceFuel
      hSafe hBoundary hHeadSuccess hRecursive (targetExtra := targetExtra)
  have hFuel : sourceFuel - 1 + 1 = sourceFuel := by omega
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.call targets functionName args) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    AllocationInteractionRecursive.CursorForwardAt.cons_of_parts_successful
      (contract := program.memoryContract)
      (childFuel := sourceFuel - 1) (targetExtra := targetExtra)
      (frameBase := frameBase) (entryMode := .stack)
      (source := source) (target := target)
      cursor tail hExact hCompiled hMidCtx
      (by simpa [hFuel, Functions.Scope.Stmt.outEnv] using hHead)
      (by simpa [hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hSame hReturns
          hTailSuccess => by
        have hTailStack : tailMode = .stack := by
          cases hSame
          rfl
        exact hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame
                  exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            stackMode := hTailStack }
          hTailSuccess)
  simpa [CursorRuntimeAt, hFuel] using hResult

end CursorRuntimeAt

end AllocationInteractionStackRuntime
end Functions
end EvmCompiler
