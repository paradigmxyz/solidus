import EvmCompiler.Expressions.InteractionReturns
import EvmCompiler.Functions.AllocationInteractionFunctionReturnResource
import EvmCompiler.Functions.AllocationInteractionRecursiveResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallResultResource

open AllocationInteractionComposition
open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionResourceComposition

/-- Completed compiler-owned callee body before caller-frame attachment. -/
inductive BodyResultRel
    (contract : MemoryContract.Contract) (returns : List Locals.Name)
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetInitial : TargetState) :
    (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) ->
      Expressions.InteractionSemantics.Outcome -> Prop where
  | regular {source : SourceState} {sourceCtx : Functions.Source.Ctx}
      {target : TargetState}
      (state : LeaveStateRel contract returns source target)
      (returnStack : target.returns = targetInitial.returns)
      (effect :
        ActivationEffect config allocatorDepth entryMode targetInitial target) :
      BodyResultRel contract returns config allocatorDepth entryMode
        targetInitial
        (Functions.Source.Effectful.Outcome.regular source, sourceCtx)
        (Structured.EffectSemantics.Outcome.regular target)
  | leave {source : SourceState} {sourceCtx : Functions.Source.Ctx}
      {target : TargetState}
      (state : LeaveStateRel contract returns source target)
      (returnStack : target.returns = targetInitial.returns)
      (effect :
        ActivationEffect config allocatorDepth entryMode targetInitial target) :
      BodyResultRel contract returns config allocatorDepth entryMode
        targetInitial
        (Functions.Source.Effectful.Outcome.leave source, sourceCtx)
        (Structured.EffectSemantics.Outcome.leave target)
  | brk {source : SourceState} {sourceCtx : Functions.Source.Ctx}
      {target : TargetState}
      (returnStack : target.returns = targetInitial.returns)
      (effect :
        ActivationEffect config allocatorDepth entryMode targetInitial target) :
      BodyResultRel contract returns config allocatorDepth entryMode
        targetInitial
        (Functions.Source.Effectful.Outcome.brk source, sourceCtx)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont {source : SourceState} {sourceCtx : Functions.Source.Ctx}
      {target : TargetState}
      (returnStack : target.returns = targetInitial.returns)
      (effect :
        ActivationEffect config allocatorDepth entryMode targetInitial target) :
      BodyResultRel contract returns config allocatorDepth entryMode
        targetInitial
        (Functions.Source.Effectful.Outcome.cont source, sourceCtx)
        (Structured.EffectSemantics.Outcome.cont target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState} {sourceCtx : Functions.Source.Ctx}
      {target : TargetState}
      (state : SharedRel contract source.shared target.evm.toSharedState)
      (effect :
        ActivationEffect config allocatorDepth entryMode targetInitial target) :
      BodyResultRel contract returns config allocatorDepth entryMode
        targetInitial
        (Functions.Source.Effectful.Outcome.halt kind source, sourceCtx)
        (Structured.EffectSemantics.Outcome.halt kind target)

abbrev OpenBodyResultRel
    (contract : MemoryContract.Contract) (returns : List Locals.Name)
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetInitial : TargetState) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (BodyResultRel contract returns config allocatorDepth entryMode
      targetInitial)

private theorem code_pair_openRun
    (program : Expressions.Program)
    {first second : Structured.Code}
    {source middle final : Structured.RunState}
    {fuel : Nat}
    (hFuel : 3 <= fuel)
    (hFirst :
      Structured.InteractionSemantics.Code.openRun first source =
        .done (.ok middle))
    (hSecond :
      Structured.InteractionSemantics.Code.openRun second middle =
        .done (.ok final)) :
    Expressions.InteractionSemantics.Block.openRun program fuel
        { stmts := Locals.codeStmt first ++ Locals.codeStmt second } source =
      .done (.ok (Structured.EffectSemantics.Outcome.regular final)) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  simp only [Locals.codeStmt, List.singleton_append]
  rw [show 3 + extra = (2 + extra) + 1 by omega,
    Expressions.InteractionSemantics.Block.openRun_cons]
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  unfold Structured.InteractionSemantics.Code.openRun at hFirst hSecond
  rw [hFirst]
  simp only [Simulation.Interaction.instMonad,
    Simulation.Interaction.bind, Simulation.Interaction.pure]
  rw [show 2 + extra = extra + 2 by omega,
    Expressions.InteractionSemantics.Block.openRun_single_stmt]
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.bind
        (Structured.EffectSemantics.Control.Code.run
          Structured.InteractionSemantics.handler second middle)
        (fun state' =>
          Simulation.Interaction.pure
            (Structured.EffectSemantics.Outcome.regular state')) = _
  rw [hSecond]
  rfl

namespace SelectedCallee

/--
Append the ordinary compiler's return epilogue to one related selected-callee
body. The theorem consumes only the adjacent recursive result and the exact
compiler artifact; no call oracle or generated execution premise is exposed.
-/
theorem complete_body_of_rel
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : AllocationInteractionCursor.Compilation
      allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase targetFuel : Nat}
    {config : Config}
    {sourceRun :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {regularLive : List Functions.Name}
    {controlCtx regularCtx : Functions.Source.Ctx}
    {target : Structured.RunState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReturnsLive :
      forall localName, localName ∈ fn.returns -> localName ∈ regularLive)
    (hFuel :
      prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + prepared.bodyCode.length + 3 <=
        targetFuel)
    (hBody :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns regularLive frameBase
          artifact.mode controlCtx regularCtx config allocatorDepth target)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          { stmts :=
              prepared.markerCode ++ prepared.paramCode ++
                prepared.returnCode ++ prepared.bodyCode }
          target)) :
    Simulation.Interaction.Rel
      (OpenBodyResultRel contract fn.returns config allocatorDepth
        artifact.mode target)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        artifact.lowerProc.body target) := by
  let bodyPrefix :=
    prepared.markerCode ++ prepared.paramCode ++ prepared.returnCode ++
      prepared.bodyCode
  let bodySuffix :=
    Locals.codeStmt prepared.returnValueCode ++
      Locals.codeStmt prepared.cleanup
  have hReturns :=
    Expressions.InteractionReturns.Block.openRun_returns expressions
      targetFuel { stmts := bodyPrefix } target
  have hBody' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns regularLive frameBase
          artifact.mode controlCtx regularCtx config allocatorDepth target)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          { stmts := bodyPrefix } target) := by
    simpa [bodyPrefix] using hBody
  have hStrong :=
    (Simulation.Interaction.Rel.strengthen_left hBody'.symm hReturns).symm
  have hResidual : 3 <= targetFuel - bodyPrefix.length := by
    simp [bodyPrefix, List.length_append] at hFuel ⊢
    omega
  have hComposed :=
    Simulation.Interaction.Rel.bind_custom hStrong
      (targetDoneRel :=
        OpenBodyResultRel contract fn.returns config allocatorDepth
          artifact.mode target)
      (leftNext := fun result => Simulation.Interaction.pure result)
      (rightNext := fun outcome =>
        match outcome.mode with
        | .regular =>
            Expressions.InteractionSemantics.Block.openRun expressions
              (targetFuel - bodyPrefix.length) { stmts := bodySuffix }
                outcome.state
        | .brk | .cont | .leave | .halt _ =>
            Simulation.Interaction.pure outcome)
      (fun sourceDone targetDone hDone => by
        rcases hDone with ⟨hRuntime, hTargetReturns⟩
        rcases hRuntime with ⟨hControl, hEffect⟩
        cases hControl with
        | error hError =>
            cases hEffect with
            | error _ =>
                exact Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.error hError)
        | ok hControl =>
            cases hEffect with
            | ok hEffect =>
                cases hControl with
                | @regular sourceBody targetBody finalMode hInvariant
                    hSameFrame _hControl =>
                    obtain ⟨values, hLookup⟩ :=
                      lookupMany_of_liveDefined hInvariant.defined
                        hReturnsLive
                    obtain
                        ⟨_afterValues, final, hReturnRun, hCleanupRun,
                          _hCombined, hLeave, hFinalReturns,
                          hReturnEffect⟩ :=
                      AllocationInteractionFunctionReturnResource.forward_regular
                        hConfig hInvariant hReturnsLive
                        hLookup prepared.lowerReturnValues
                        prepared.compileReturnValues prepared.compileCleanup
                        hEffect.ready
                    have hTail :=
                      code_pair_openRun expressions hResidual hReturnRun
                        hCleanupRun
                    have hBodyReturns :
                        targetBody.returns = target.returns := by
                      simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                        using hTargetReturns
                    have hFinalReturnStack : final.returns = target.returns :=
                      hFinalReturns.trans hBodyReturns
                    have hFinalEffect :
                        ActivationEffect config allocatorDepth artifact.mode
                          target final :=
                      hEffect.trans
                        (hReturnEffect.sameFrame hSameFrame.symm)
                    change
                      Simulation.Interaction.Rel
                        (OpenBodyResultRel contract fn.returns config
                          allocatorDepth artifact.mode target)
                        (Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            sourceBody, regularCtx))
                        (Expressions.InteractionSemantics.Block.openRun
                          expressions (targetFuel - bodyPrefix.length)
                          { stmts := bodySuffix } targetBody)
                    rw [show bodySuffix =
                        Locals.codeStmt prepared.returnValueCode ++
                          Locals.codeStmt prepared.cleanup by rfl,
                      hTail]
                    exact Simulation.Interaction.Rel.done
                      (Simulation.Interaction.ExceptRel.ok
                        (BodyResultRel.regular hLeave hFinalReturnStack
                          hFinalEffect))
                | nonregular hNonregular _hSameFrame _hControl hState =>
                    cases hState with
                    | regular _ => exact False.elim (hNonregular rfl)
                    | brk _ _ _ _ =>
                        exact Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok
                            (BodyResultRel.brk (by
                            simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                              using hTargetReturns) hEffect))
                    | cont _ _ _ _ =>
                        exact Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok
                            (BodyResultRel.cont (by
                            simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                              using hTargetReturns) hEffect))
                    | leave hLeave =>
                        exact Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok
                            (BodyResultRel.leave (by simpa [
                              AllocationInteractionStatement.outcomeLive]
                            using hLeave) (by
                              simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                                using hTargetReturns) hEffect))
                    | halt kind hHalt =>
                        exact Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok
                            (BodyResultRel.halt kind hHalt.shared hEffect)))
  cases hProc : artifact.lowerProc.body with
  | mk stmts =>
      have hStmts : stmts = bodyPrefix ++ bodySuffix := by
        simpa [hProc, bodyPrefix, bodySuffix, List.append_assoc] using
          prepared.procBody
      subst stmts
      rw [Expressions.InteractionSemantics.Block.openRun_append]
      simpa [bodyPrefix, bodySuffix] using hComposed

/-- Construct the complete selected-callee procedure body from source facts. -/
theorem complete_body
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : AllocationInteractionCursor.Compilation
      allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel fuelBound : Nat}
    {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase artifact.mode source target)
    (hZero :
      forall localName,
        localName ∈ artifact.slots.returns.map Prod.fst ->
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase artifact.mode)
    (hBudget : AllocationInteractionFrame.Budget config allocatorDepth)
    (hSourceFuel : sourceFuel < fuelBound)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (root := prepared.rootArtifact hProgramScoped)
        contract globalFrameWords fuelBound) :
    exists targetFuel,
      0 < targetFuel ∧
      Simulation.Interaction.Rel
        (OpenBodyResultRel contract fn.returns config allocatorDepth
          artifact.mode target)
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          artifact.lowerProc.body target) := by
  obtain ⟨targetFuel, hTargetFuel, hEpilogueFuel, hBody⟩ :=
    AllocationInteractionRecursiveResource.SelectedCallee.body_of_function_context
      (targetExtra := 3) prepared hProgramScoped hEntry hZero hStackLength
      hReservation hConfig hReady hOwned hBudget hSourceFuel hSuccess
      hRecursive
  have hReturnsLive :
      forall localName,
        localName ∈ fn.returns ->
          localName ∈
            Functions.Scope.Block.outEnv
              (fn.returns ++ fn.params) fn.body := by
    intro localName hName
    exact Functions.Scope.Block.mem_outEnv (by simp [hName])
  refine ⟨targetFuel, hTargetFuel, ?_⟩
  exact complete_body_of_rel prepared hConfig hReturnsLive hEpilogueFuel hBody

end SelectedCallee

end AllocationInteractionCallResultResource
end Functions
end EvmCompiler
