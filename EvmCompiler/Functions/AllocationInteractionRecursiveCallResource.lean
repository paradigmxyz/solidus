import EvmCompiler.Functions.AllocationInteractionCallStatementResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursiveCallResource

open AllocationInteractionCall
open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionRecursive

private theorem toStructured_length (stmts : List Expressions.Stmt) :
    (Expressions.StmtList.toStructured stmts).length = stmts.length := by
  induction stmts with
  | nil => rfl
  | cons stmt rest ih =>
      simp [Expressions.StmtList.toStructured, ih]

/-- One compiler-emitted code wrapper exposes the underlying Structured run
before continuing with the exact residual Expressions block. -/
theorem openRun_code_prefix
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code) (rest : List Expressions.Stmt)
    (state : Structured.RunState) (hFuel : 2 ≤ fuel) :
    Expressions.InteractionSemantics.Block.openRun program fuel
        { stmts := Locals.codeStmt code ++ rest } state =
      Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun code state)
        (fun after =>
          Expressions.InteractionSemantics.Block.openRun program (fuel - 1)
            { stmts := rest } after) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  have hSingle :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_stmt_of_fuel
      program fuel (.code code) state hFuel
  simp only [Locals.codeStmt, List.length_singleton]
  rw [hSingle]
  unfold Expressions.InteractionSemantics.Stmt.openRun
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  change Simulation.Interaction.bind
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

/-- The uniform recursive stride leaves the selected procedure enough room
for its two-statement return epilogue and the caller continuation. -/
theorem selected_call_extra
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live
        { stmts := .call targets functionName args :: rest }
        lowerState localsCtx}
    {fn : Functions.FunDef}
    {artifact : SelectedCallee.Artifact compilation functionName fn}
    (prepared : SelectedCallee.Prepared artifact)
    {sourceFuel targetExtra : Nat}
    (hSourceFuel : 2 < sourceFuel) :
    let bodyFuel := sourceFuel - 3
    let callTargetFuel := targetBudget cursor sourceFuel targetExtra - 3
    let callBase :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + prepared.bodyCode.length +
          callStride expressions * (bodyFuel + 1)
    2 * callStride expressions + 3 ≤ callTargetFuel - callBase ∧
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
  have hFuelEq :
      sourceFuel + 1 = (sourceFuel - 3 + 1) + 3 := by
    omega
  have hStride : 8 ≤ callStride expressions :=
    eight_le_callStride expressions
  unfold targetBudget
  rw [hFuelEq]
  simp only [Nat.mul_add]
  omega

namespace CallComponents

/-- The ordinary call artifact exposes the exact stack-only argument code. -/
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
    {artifact : SelectedCallee.Artifact compilation functionName fn}
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

/-- The ordinary call artifact exposes the synthetic frame argument selected
by the checked scratch configuration. -/
theorem scratch_compileArgs
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
    {artifact : SelectedCallee.Artifact compilation functionName fn}
    {config : Config}
    (hConfig : compilation.frameConfig? = some config)
    (hNeedsFrame : artifact.needsFrame = true) :
    Locals.ExprSeq.compileCode localsCtx 0
        (AllocationLowering.exprSeqOfList
          (AllocationLowering.frameExpr config :: components.loweredArgs)) =
      some components.argsCode := by
  have hMem : functionName ∈ root.lowerCtx.frameFunctions :=
    (artifact.mem_frameFunctions_iff root.lowerCtxShared).mpr hNeedsFrame
  have hCtxConfig : root.lowerCtx.frameConfig? = some config :=
    root.lowerCtxShared.frameConfig.trans hConfig
  have hArgs := components.callArgs_eq
  simp only [hMem, hCtxConfig, Option.bind_some, ↓reduceIte] at hArgs
  have hCallArgs :
      components.callArgs =
        AllocationLowering.frameExpr config :: components.loweredArgs :=
    (Option.some.inj hArgs).symm
  have hCompile := components.compileArgs
  rw [hCallArgs] at hCompile
  exact hCompile

/-- Stack-backed calls have no compiler-emitted release suffix. -/
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
    {artifact : SelectedCallee.Artifact compilation functionName fn}
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
  simpa [hReleaseNil, Locals.Block.compileOpen] using components.compileRelease

/-- Scratch-backed calls emit exactly the canonical allocator release code. -/
theorem scratch_releaseCode
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
    {artifact : SelectedCallee.Artifact compilation functionName fn}
    {config : Config}
    (hConfig : compilation.frameConfig? = some config)
    (hNeedsFrame : artifact.needsFrame = true) :
    components.releaseCode =
      Locals.codeStmt (AllocationSupport.scratchFrameReleaseCode config) := by
  have hMem : functionName ∈ root.lowerCtx.frameFunctions :=
    (artifact.mem_frameFunctions_iff root.lowerCtxShared).mpr hNeedsFrame
  have hCtxConfig : root.lowerCtx.frameConfig? = some config :=
    root.lowerCtxShared.frameConfig.trans hConfig
  have hRelease := components.release_eq
  simp only [hMem, hCtxConfig, Option.bind_some, ↓reduceIte] at hRelease
  have hReleaseOne :
      components.release =
        [.expr
          (.code (results := 0)
            (AllocationSupport.scratchFrameReleaseCode config))] :=
    (Option.some.inj hRelease).symm
  have hCompile := components.compileRelease
  rw [hReleaseOne] at hCompile
  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
    Locals.Expr.compileCode, Locals.codeStmt] at hCompile
  exact hCompile.symm

end CallComponents

namespace SelectedCallee

/-- Complete a stack-backed selected call from an already related argument
branch through caller return writeback or halt. -/
theorem stack_after_arguments_and_finish
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {config : Config} {allocatorDepth callerFrameBase bodyFuel fuelBound
      targetExtra storesFuel : Nat}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {callerLive returns targets : List Locals.Name}
    {callerMode : ActivationMode} {controlCtx : Functions.Source.Ctx}
    {sourceInitial sourceAfterArgs : AllocationInteractionRelation.SourceState}
    {targetInitial targetAfterArgs : AllocationInteractionRelation.TargetState}
    {argValues : List Assembly.Word}
    {paramStore : Locals.Source.Store} {stores : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hNeedsFrame : artifact.needsFrame = false)
    (hInitial :
      AllocationContext.ActivationInvariant program.memoryContract
        callerLowerCtx callerLowerState callerLocalsCtx callerPlan callerLive
        callerFrameBase callerMode sourceInitial targetInitial)
    (hArgs :
      AllocationInteractionCallArgumentResources.ResultRel
        program.memoryContract config allocatorDepth callerPlan callerLive 0
        callerFrameBase argValues.length callerMode targetInitial
        (sourceAfterArgs, argValues) targetAfterArgs)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hInsert :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (hReservation : program.memoryContract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? program.memoryContract
          compilation.recipe.frameWords =
        some config)
    (hCallerOwned :
      ActivationOwned config allocatorDepth callerFrameBase callerMode)
    (hBudget : Budget config allocatorDepth)
    (hFuelBudget : Budget config (allocatorDepth + bodyFuel))
    (hTargetExtra : 3 ≤ targetExtra)
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode ≤
        targetExtra)
    (hBodyFuel : bodyFuel < fuelBound)
    (hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords fuelBound)
    (hFinish :
      Simulation.Interaction.AllDone
        (fun callDone =>
          match callDone with
          | .error _ => False
          | .ok callResult =>
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.Stmt.finishCall targets
                  controlCtx sourceAfterArgs callResult))
        (Functions.InteractionSemantics.FunDef.openRunBody
          program fn argValues (bodyFuel + 1) sourceAfterArgs))
    (hTargetsLive : ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores)
    (hStoresFuel : 2 ≤ storesFuel) :
    ∃ targetFuel,
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (bodyFuel + 1)) ∧
      Simulation.Interaction.Rel
        (AllocationInteractionResourceComposition.RuntimeResultRel
          program.memoryContract callerLowerCtx callerLowerState
          callerLocalsCtx callerPlan returns callerLive callerFrameBase
          callerMode controlCtx controlCtx config allocatorDepth targetInitial)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.FunDef.openRunBody
            program fn argValues (bodyFuel + 1) sourceAfterArgs)
          (Functions.InteractionSemantics.Stmt.finishCall targets controlCtx
            sourceAfterArgs))
        (Simulation.Interaction.bind
          (Expressions.InteractionSemantics.Stmt.openRun expressions
            (targetFuel + 1) (.call name) targetAfterArgs)
          (fun outcome =>
            match outcome.mode with
            | .regular =>
                Expressions.InteractionSemantics.Block.openRun expressions
                  storesFuel { stmts := Locals.codeStmt stores } outcome.state
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure outcome)) := by
  obtain ⟨callerBase, targetEntry, targetFuel, hCallerRel, _hReady,
      hCallerStack, hInitialToBase, hBaseToEntry, hTargetFuel, hCall⟩ :=
    AllocationInteractionCallStatementResource.SelectedCallee.stack_after_arguments
      (targetExtra := targetExtra) prepared hProgramScoped hNeedsFrame hArgs
      hInsert hReservation hConfig hCallerOwned hBudget hFuelBudget
      hTargetExtra hTargetReserve hBodyFuel hBodySuccess hRecursive
  have hCallerStackLength :
      callerBase.evm.stack.length = callerLocalsCtx.layout.length := by
    rw [hCallerStack]
    exact hInitial.stackLength
  have hResult :=
    AllocationInteractionCallStatementResource.CallResultRel.finish_without_release
      (expressions := expressions) (storesFuel := storesFuel)
      (returns := returns) (controlCtx := controlCtx)
      hConfig hInitial hArgsVars hCallerRel hCallerOwned rfl hBudget
      hCallerStack hCallerStackLength hInitialToBase hBaseToEntry
      (by
        simp [AllocationInteractionCall.SelectedCallee.Artifact.mode,
          hNeedsFrame,
          AllocationInteractionFrame.activationProtectedBound])
      hCall hFinish hTargetsLive hTargetsNodup hStores hStoresFuel
  exact ⟨targetFuel, hTargetFuel, hResult⟩

/-- Complete a scratch-backed selected call from an already related argument
branch through writeback and release, or through a suffix-skipping halt. -/
theorem scratch_after_arguments_and_finish
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {config : Config} {allocatorDepth callerFrameBase bodyFuel fuelBound
      targetExtra storesFuel : Nat}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {callerLive returns targets : List Locals.Name}
    {callerMode : ActivationMode} {controlCtx : Functions.Source.Ctx}
    {sourceInitial sourceAfterArgs : SourceState}
    {targetInitial targetAfterAcquire targetAfterArgs : TargetState}
    {argValues : List Assembly.Word}
    {paramStore : Locals.Source.Store} {stores : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hNeedsFrame : artifact.needsFrame = true)
    (hInitial :
      AllocationContext.ActivationInvariant program.memoryContract
        callerLowerCtx callerLowerState callerLocalsCtx callerPlan callerLive
        callerFrameBase callerMode sourceInitial targetInitial)
    (hAcquire :
      AllocationInteractionFramePreservation.ScratchFrameAcquireCorrect
        program.memoryContract config allocatorDepth
        sourceInitial.shared.toMachineState targetInitial targetAfterAcquire)
    (hArgs :
      AllocationInteractionCallArgumentResources.ResultRel
        program.memoryContract config (allocatorDepth + 1) callerPlan
        callerLive 1 callerFrameBase argValues.length callerMode
        targetAfterAcquire (sourceAfterArgs, argValues) targetAfterArgs)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hInsert :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (hReservation : program.memoryContract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? program.memoryContract
          compilation.recipe.frameWords =
        some config)
    (hCallerOwned :
      ActivationOwned config allocatorDepth callerFrameBase callerMode)
    (hBudget : Budget config allocatorDepth)
    (hFuelBudget : Budget config ((allocatorDepth + 1) + bodyFuel))
    (hTargetExtra : 3 ≤ targetExtra)
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode ≤
        targetExtra)
    (hBodyFuel : bodyFuel < fuelBound)
    (hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords fuelBound)
    (hFinish :
      Simulation.Interaction.AllDone
        (fun callDone =>
          match callDone with
          | .error _ => False
          | .ok callResult =>
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.Stmt.finishCall targets
                  controlCtx sourceAfterArgs callResult))
        (Functions.InteractionSemantics.FunDef.openRunBody
          program fn argValues (bodyFuel + 1) sourceAfterArgs))
    (hTargetsLive : ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores)
    (hStoresFuel : 3 ≤ storesFuel) :
    ∃ targetFuel,
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (bodyFuel + 1)) ∧
      Simulation.Interaction.Rel
        (AllocationInteractionResourceComposition.RuntimeResultRel
          program.memoryContract callerLowerCtx callerLowerState
          callerLocalsCtx callerPlan returns callerLive callerFrameBase
          callerMode controlCtx controlCtx config allocatorDepth targetInitial)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.FunDef.openRunBody
            program fn argValues (bodyFuel + 1) sourceAfterArgs)
          (Functions.InteractionSemantics.Stmt.finishCall targets controlCtx
            sourceAfterArgs))
        (Simulation.Interaction.bind
          (Expressions.InteractionSemantics.Stmt.openRun expressions
            (targetFuel + 1) (.call name) targetAfterArgs)
          (fun outcome =>
            match outcome.mode with
            | .regular =>
                Expressions.InteractionSemantics.Block.openRun expressions
                  storesFuel
                  { stmts :=
                      Locals.codeStmt stores ++
                        Locals.codeStmt
                          (AllocationSupport.scratchFrameReleaseCode config) }
                  outcome.state
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure outcome)) := by
  obtain ⟨callerBase, targetEntry, targetFuel, hCallerRel, _hReady,
      hCallerStack, hInitialToBase, hBaseToEntry, hTargetFuel, hCall⟩ :=
    AllocationInteractionCallStatementResource.SelectedCallee.scratch_after_arguments
      (targetExtra := targetExtra) prepared hProgramScoped hNeedsFrame hAcquire
      hArgs hInsert hReservation hConfig hBudget hFuelBudget hTargetExtra
      hTargetReserve hBodyFuel hBodySuccess hRecursive
  have hCallerStackLength :
      callerBase.evm.stack.length = callerLocalsCtx.layout.length := by
    rw [hCallerStack]
    exact hInitial.stackLength
  have hResult :=
    AllocationInteractionCallStatementResource.CallResultRel.finish_with_release
      (expressions := expressions) (storesFuel := storesFuel)
      (returns := returns) (controlCtx := controlCtx)
      hConfig hInitial hArgsVars hCallerRel hCallerOwned rfl hBudget
      hCallerStack hCallerStackLength hInitialToBase hBaseToEntry
      (by
        simp [AllocationInteractionCall.SelectedCallee.Artifact.mode,
          hNeedsFrame,
          AllocationInteractionFrame.activationProtectedBound])
      hCall hFinish hTargetsLive hTargetsNodup hStores hStoresFuel
  exact ⟨targetFuel, hTargetFuel, hResult⟩

end SelectedCallee

namespace CallComponents

/-- One real stack-backed call cursor preserves its complete source statement
and compiler-emitted target head. -/
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
    {artifact : SelectedCallee.Artifact compilation functionName fn}
    (prepared : SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions = some fn)
    (hNeedsFrame : artifact.needsFrame = false)
    {config : Config} {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ArgListSafe
      program.memoryContract args source)
    (hBoundary :
      AllocationInteractionRecursiveResource.Boundary cursor
        program.memoryContract compilation.recipe.frameWords config
        allocatorDepth frameBase mode sourceCtx source target)
    (hFuelBudget : Budget config (allocatorDepth + sourceFuel))
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.call targets functionName args) source))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords
        sourceFuel) :
    Simulation.Interaction.Rel
      (AllocationInteractionResourceComposition.RuntimeResultRel
        program.memoryContract root.lowerCtx lowerState localsCtx cursor.plan
        root.returns live frameBase mode sourceCtx sourceCtx config
        allocatorDepth target)
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
  have hTargetsLive : ∀ target, target ∈ targets → target ∈ live :=
    hStmtScoped.2.1
  have hArgsScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg :=
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
  have hArgsCompile :=
    stack_compileArgs components hNeedsFrame
  have hArgsRel :=
    AllocationInteractionCall.PreparedArguments.stack
      hBoundary.configEq hSafe hBoundary.semantic.invariant.compiler
      hArgsScoped components.lowerArgs hArgsCompile
      hBoundary.semantic.invariant.state hBoundary.ready
  have hArgsWithContinuations :=
    Simulation.Interaction.Rel.strengthen_left hArgsRel hContinuations
  have hArgsStrong :=
    Simulation.Interaction.Rel.strengthen_left hArgsWithContinuations hVars
  have hExtra := selected_call_extra (cursor := cursor)
    (targetExtra := targetExtra) prepared hSourceFuel
  change 2 * callStride expressions + 3 ≤ selectedExtra ∧
    callBase + selectedExtra = callTargetFuel at hExtra
  have hBodyCodeSize :=
    AllocationInteractionRecursiveResource.SelectedCallee.bodyCode_size_le_callStride
      prepared
  have hSelectedReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode ≤
        selectedExtra := by
    exact
      (AllocationInteractionTargetFuel.nestedSize_le_size
        prepared.bodyCode).trans (hBodyCodeSize.trans (by omega))
  have hTotalFuel : 2 ≤ totalFuel := by
    have hStride := eight_le_callStride expressions
    change 2 ≤ targetExtra + cursor.compiled.length +
      callStride expressions * (sourceFuel + 1)
    have hMul := Nat.mul_le_mul hStride (show 1 ≤ sourceFuel + 1 by omega)
    omega
  let callRest : List Expressions.Stmt :=
    [.call functionName] ++ Locals.codeStmt components.stores
  have hCore :
      Simulation.Interaction.Rel
        (AllocationInteractionResourceComposition.RuntimeResultRel
          program.memoryContract root.lowerCtx lowerState localsCtx cursor.plan
          root.returns live frameBase mode sourceCtx sourceCtx config
          allocatorDepth target)
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
          hArgRel.1.valuesLength
        have hArgRel' :
            AllocationInteractionCallArgumentResources.ResultRel
              program.memoryContract config allocatorDepth cursor.plan live 0
              frameBase argValues.length mode target
              (sourceAfterArgs, argValues) targetAfterArgs := by
          simpa [hValuesLength] using hArgRel
        have hArgsVars : sourceAfterArgs.vars = source.vars := by
          exact hVarsDone
        have hBodyBudget : Budget config (allocatorDepth + bodyFuel) :=
          Budget.mono (by simp [bodyFuel]) hFuelBudget
        obtain ⟨reservation, hReservation, _⟩ :=
          AllocationSupport.scratchFrameConfig?_sound hBoundary.configEq
        obtain ⟨selectedTargetFuel, hSelectedFuel, hBranch⟩ :=
          SelectedCallee.stack_after_arguments_and_finish
            (storesFuel := callTargetFuel + 1)
            (returns := root.returns)
            (reservation := reservation)
            prepared hProgramScoped hNeedsFrame
            hBoundary.semantic.invariant hArgRel' hArgsVars hInsert
            hReservation
            hBoundary.configEq hBoundary.owned hBoundary.budget hBodyBudget
            (by omega) hSelectedReserve (by omega) hBodySuccess hRecursive
            (by simpa [hBodyFuel] using hFinish)
            hTargetsLive hTargetsNodup components.stores_eq (by omega)
        have hSelectedTargetFuel : selectedTargetFuel = callTargetFuel := by
          rw [hSelectedFuel]
          dsimp [callBase] at hExtra
          omega
        rw [hSelectedTargetFuel] at hBranch
        have hRemainderFuel : callTargetFuel + 2 = totalFuel - 1 := by
          simp [callTargetFuel]
          have hEnough : 3 ≤ totalFuel := by omega
          omega
        simp only [Simulation.Interaction.bind_done_ok]
        simp only [callRest, List.singleton_append, List.cons_append,
          List.nil_append]
        rw [show totalFuel - 1 = callTargetFuel + 2 from hRemainderFuel.symm,
          Expressions.InteractionSemantics.Block.openRun_cons]
        unfold Expressions.InteractionSemantics.Stmt.openRun at hBranch
        simpa [hBodyFuel] using hBranch
  have hHeadCode :
      components.headCode =
        Locals.codeStmt components.argsCode ++ callRest := by
    rw [components.headCode_eq,
      CallComponents.stack_releaseCode components hNeedsFrame]
    simp [callRest, List.append_assoc]
  rw [hHeadCode, show targetBudget cursor sourceFuel targetExtra = totalFuel
    from rfl]
  rw [openRun_code_prefix expressions totalFuel components.argsCode callRest
    target hTotalFuel]
  rw [← hChildFuel,
    Functions.InteractionSemantics.Stmt.openRun_call]
  simp only [hTargetsNodup, if_pos, hFind, Option.elim_some,
    Simulation.Interaction.bind_done_ok]
  simpa [callFuel, bodyFuel, totalFuel, callRest] using hCore

/-- One real scratch-backed call cursor preserves its complete source
statement and compiler-emitted target head. -/
theorem scratch_runtime_head
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
    {artifact : SelectedCallee.Artifact compilation functionName fn}
    (prepared : SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions = some fn)
    (hNeedsFrame : artifact.needsFrame = true)
    {config : Config} {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ArgListSafe
      program.memoryContract args source)
    (hBoundary :
      AllocationInteractionRecursiveResource.Boundary cursor
        program.memoryContract compilation.recipe.frameWords config
        allocatorDepth frameBase mode sourceCtx source target)
    (hFuelBudget : Budget config (allocatorDepth + sourceFuel))
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.call targets functionName args) source))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords sourceFuel) :
    Simulation.Interaction.Rel
      (AllocationInteractionResourceComposition.RuntimeResultRel
        program.memoryContract root.lowerCtx lowerState localsCtx cursor.plan
        root.returns live frameBase mode sourceCtx sourceCtx config
        allocatorDepth target)
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
  have hTargetsLive : ∀ target, target ∈ targets → target ∈ live :=
    hStmtScoped.2.1
  have hArgsScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg :=
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
  obtain
      ⟨reservation, hReservation, _hAllocator, _hFirst, _hLimit,
        _hFrameWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hBoundary.configEq
  have hArgsCompile :=
    scratch_compileArgs components hBoundary.configEq hNeedsFrame
  have hConfigPositive : 0 < config.frameWords :=
    artifact.config_frameWords_pos hBoundary.configEq hNeedsFrame
  obtain ⟨hAcquire, hArgsRel⟩ :=
    AllocationInteractionCall.PreparedArguments.scratch
      hBoundary.configEq hConfigPositive hBoundary.budget hSafe
      hBoundary.semantic.invariant.compiler hArgsScoped components.lowerArgs
      hArgsCompile hBoundary.semantic.invariant.state hBoundary.ready
      hBoundary.owned
  have hArgsWithContinuations :=
    Simulation.Interaction.Rel.strengthen_left hArgsRel hContinuations
  have hArgsStrong :=
    Simulation.Interaction.Rel.strengthen_left hArgsWithContinuations hVars
  have hExtra := selected_call_extra (cursor := cursor)
    (targetExtra := targetExtra) prepared hSourceFuel
  change 2 * callStride expressions + 3 ≤ selectedExtra ∧
    callBase + selectedExtra = callTargetFuel at hExtra
  have hBodyCodeSize :=
    AllocationInteractionRecursiveResource.SelectedCallee.bodyCode_size_le_callStride
      prepared
  have hSelectedReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode ≤
        selectedExtra := by
    exact
      (AllocationInteractionTargetFuel.nestedSize_le_size
        prepared.bodyCode).trans (hBodyCodeSize.trans (by omega))
  have hTotalFuel : 2 ≤ totalFuel := by
    have hStride := eight_le_callStride expressions
    change 2 ≤ targetExtra + cursor.compiled.length +
      callStride expressions * (sourceFuel + 1)
    have hMul := Nat.mul_le_mul hStride (show 1 ≤ sourceFuel + 1 by omega)
    omega
  let callRest : List Expressions.Stmt :=
    [.call functionName] ++ Locals.codeStmt components.stores ++
      Locals.codeStmt (AllocationSupport.scratchFrameReleaseCode config)
  have hCore :
      Simulation.Interaction.Rel
        (AllocationInteractionResourceComposition.RuntimeResultRel
          program.memoryContract root.lowerCtx lowerState localsCtx cursor.plan
          root.returns live frameBase mode sourceCtx sourceCtx config
          allocatorDepth target)
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
          hArgRel.1.valuesLength
        have hArgRel' :
            AllocationInteractionCallArgumentResources.ResultRel
              program.memoryContract config (allocatorDepth + 1) cursor.plan
              live 1 frameBase argValues.length mode
              (AllocationInteractionFrameExecution.scratchFrameAcquireTarget
                config allocatorDepth target)
              (sourceAfterArgs, argValues) targetAfterArgs := by
          simpa [hValuesLength] using hArgRel
        have hArgsVars : sourceAfterArgs.vars = source.vars := hVarsDone
        have hBodyBudget :
            Budget config ((allocatorDepth + 1) + bodyFuel) :=
          Budget.mono (by simp [bodyFuel]; omega) hFuelBudget
        obtain ⟨selectedTargetFuel, hSelectedFuel, hBranch⟩ :=
          SelectedCallee.scratch_after_arguments_and_finish
            (storesFuel := callTargetFuel + 1)
            (returns := root.returns) (reservation := reservation)
            prepared hProgramScoped hNeedsFrame
            hBoundary.semantic.invariant hAcquire hArgRel' hArgsVars hInsert
            hReservation hBoundary.configEq hBoundary.owned
            hBoundary.budget hBodyBudget (by omega) hSelectedReserve (by omega)
            hBodySuccess hRecursive (by simpa [hBodyFuel] using hFinish)
            hTargetsLive hTargetsNodup components.stores_eq (by omega)
        have hSelectedTargetFuel : selectedTargetFuel = callTargetFuel := by
          rw [hSelectedFuel]
          dsimp [callBase] at hExtra
          omega
        rw [hSelectedTargetFuel] at hBranch
        have hRemainderFuel : callTargetFuel + 2 = totalFuel - 1 := by
          simp [callTargetFuel]
          have hEnough : 3 ≤ totalFuel := by omega
          omega
        simp only [Simulation.Interaction.bind_done_ok]
        simp only [callRest, List.singleton_append, List.cons_append,
          List.nil_append]
        rw [show totalFuel - 1 = callTargetFuel + 2 from hRemainderFuel.symm,
          show callTargetFuel + 2 = (callTargetFuel + 1) + 1 by omega]
        rw [Expressions.InteractionSemantics.Block.openRun_cons expressions
          (callTargetFuel + 1) (.call functionName)
          (Locals.codeStmt components.stores ++
            Locals.codeStmt
              (AllocationSupport.scratchFrameReleaseCode config))
          targetAfterArgs]
        unfold Expressions.InteractionSemantics.Stmt.openRun at hBranch
        simpa [hBodyFuel, List.append_assoc] using hBranch
  have hHeadCode :
      components.headCode =
        Locals.codeStmt components.argsCode ++ callRest := by
    rw [components.headCode_eq,
      CallComponents.scratch_releaseCode components hBoundary.configEq
        hNeedsFrame]
    simp [callRest, List.append_assoc]
  rw [hHeadCode, show targetBudget cursor sourceFuel targetExtra = totalFuel
    from rfl]
  rw [openRun_code_prefix expressions totalFuel components.argsCode callRest
    target hTotalFuel]
  rw [← hChildFuel,
    Functions.InteractionSemantics.Stmt.openRun_call]
  simp only [hTargetsNodup, if_pos, hFind, Option.elim_some,
    Simulation.Interaction.bind_done_ok]
  simpa [callFuel, bodyFuel, totalFuel, callRest] using hCore

end CallComponents

namespace CoreCursor

/-- The ordinary compiler selects and proves the correct stack or scratch call
head without exposing allocation evidence to the recursive dispatcher. -/
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
    (hProgramScoped : program.Scoped)
    {config : Config} {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ArgListSafe
      program.memoryContract args source)
    (hBoundary :
      AllocationInteractionRecursiveResource.Boundary cursor
        program.memoryContract compilation.recipe.frameWords config
        allocatorDepth frameBase mode sourceCtx source target)
    (hFuelBudget : Budget config (allocatorDepth + sourceFuel))
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.call targets functionName args) source))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords sourceFuel) :
    ∃ (headCode : List Expressions.Stmt)
      (tail : CoreCursor root scope live { stmts := rest }
        lowerState localsCtx),
      cursor.compiled = headCode ++ tail.compiled ∧
        ExactTail cursor tail ∧
        Simulation.Interaction.Rel
          (AllocationInteractionResourceComposition.RuntimeResultRel
            program.memoryContract root.lowerCtx lowerState localsCtx
            cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
            config allocatorDepth target)
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            (sourceFuel - 1) (.call targets functionName args) source)
          (Expressions.InteractionSemantics.Block.openRun expressions
            (targetBudget cursor sourceFuel targetExtra)
            { stmts := headCode } target) := by
  classical
  let components := Classical.choice
    (AllocationInteractionCall.CoreCursor.callComponents cursor)
  obtain ⟨fn, hFind, artifact, ⟨prepared⟩, _hSlots⟩ :=
    components.selectedCallee
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hHead :=
      CallComponents.scratch_runtime_head components prepared hProgramScoped
        hFind hNeedsFrame hSourceFuel hSafe hBoundary hFuelBudget
        hHeadSuccess hRecursive (targetExtra := targetExtra)
    exact
      ⟨components.headCode, components.tail, components.compiled,
        components.exactTail, hHead⟩
  · have hNeedsFrameFalse : artifact.needsFrame = false := by
      exact Bool.eq_false_of_not_eq_true hNeedsFrame
    have hHead :=
      CallComponents.stack_runtime_head components prepared hProgramScoped
        hFind hNeedsFrameFalse hSourceFuel hSafe hBoundary hFuelBudget
        hHeadSuccess hRecursive (targetExtra := targetExtra)
    exact
      ⟨components.headCode, components.tail, components.compiled,
        components.exactTail, hHead⟩

end CoreCursor

namespace CursorRuntimeAt

/-- Recursive compiler-selected call followed by its exact source/target
tail. The recursive capability remains root-polymorphic and internal. -/
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
    (hProgramScoped : program.Scoped)
    {config : Config} {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSourceFuel : 2 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ArgListSafe
      program.memoryContract args source)
    (hBoundary :
      AllocationInteractionRecursiveResource.Boundary cursor
        program.memoryContract compilation.recipe.frameWords config
        allocatorDepth frameBase mode sourceCtx source target)
    (hFuelBudget : Budget config (allocatorDepth + sourceFuel))
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
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation)
        program.memoryContract compilation.recipe.frameWords sourceFuel)
    (hTailForward :
      ∀ (tail : CoreCursor root scope live { stmts := rest }
          lowerState localsCtx),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          AllocationInteractionRecursiveResource.Boundary tail
              program.memoryContract compilation.recipe.frameWords config
              allocatorDepth frameBase tailMode sourceCtx sourceMid
              targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            AllocationInteractionRecursiveResource.CursorRuntimeAt tail
              program.memoryContract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid targetMid) :
    AllocationInteractionRecursiveResource.CursorRuntimeAt cursor
      program.memoryContract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  obtain ⟨headCode, tail, hCompiled, hExact, hHead⟩ :=
    CoreCursor.call_runtime_head cursor hProgramScoped hSourceFuel hSafe
      hBoundary hFuelBudget hHeadSuccess hRecursive
      (targetExtra := targetExtra)
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
    AllocationInteractionRecursiveResource.CursorRuntimeAt.cons_of_parts_successful
      cursor tail hExact hCompiled hMidCtx
      (by simpa [hFuel, Functions.Scope.Stmt.outEnv] using hHead)
      (by simpa [hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              AllocationInteractionRecursiveResource.Boundary.controlAgreement_same_live
                cursor tail hBoundary hExact
                (by simp [Functions.Scope.Stmt.outEnv]) hInvariant hSame
                (Functions.Source.Ctx.SameControl.refl sourceCtx) hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  rw [hFuel] at hResult
  exact hResult

end CursorRuntimeAt

end AllocationInteractionRecursiveCallResource
end Functions
end EvmCompiler
