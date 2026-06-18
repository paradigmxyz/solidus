import EvmCompiler.Functions.AllocationInteractionCall
import EvmCompiler.Functions.AllocationInteractionForward

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursive

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCursor
open AllocationInteractionCall

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
    (frameBase sourceFuel : Nat)
    (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  let regularLive := Functions.Scope.Block.outEnv live sourceBlock
  let regularCtx := { sourceCtx with scope := regularLive }
  ∃ targetFuel,
    0 < targetFuel ∧
    Simulation.Interaction.Rel
      (OpenControlResultRel contract root.lowerCtx cursor.finalState
        cursor.finalLocals cursor.plan root.returns regularLive frameBase
        sourceCtx regularCtx)
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        sourceFuel sourceBlock source)
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := cursor.compiled } target)

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
            frameBase sourceFuel sourceCtx source bodyTarget) :
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
    obtain ⟨bodyFuel, hBodyFuel, hBody⟩ :=
      hBodyForward hSourceFuel hInvariant
    let targetFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨targetFuel, by simp [targetFuel]; omega, ?_⟩
    exact
      prepared.prelude_then_body hBodyFuel hPreludeAt
        (by simpa [CursorForwardAt, live] using hBody)
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
    obtain ⟨bodyFuel, hBodyFuel, hBody⟩ :=
      hBodyForward hSourceFuel hInvariant
    let targetFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨targetFuel, by simp [targetFuel]; omega, ?_⟩
    exact
      prepared.prelude_then_body hBodyFuel hPreludeAt
        (by simpa [CursorForwardAt, live] using hBody)

end SelectedCallee

end AllocationInteractionRecursive
end Functions
end EvmCompiler
