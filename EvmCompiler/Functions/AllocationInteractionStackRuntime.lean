import EvmCompiler.Functions.AllocationInteractionRecursive
import EvmCompiler.Functions.AllocationInteractionControlAgreement
import EvmCompiler.Functions.AllocationInteractionTargetFuel

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStackRuntime

open AllocationInteractionCursor
open AllocationInteractionComposition
open AllocationInteractionRelation
open AllocationInteractionRecursive

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
theorem AllocationInteractionCall.CallComponents.selectedCallee_stack
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

end CursorRuntimeAt

end AllocationInteractionStackRuntime
end Functions
end EvmCompiler
