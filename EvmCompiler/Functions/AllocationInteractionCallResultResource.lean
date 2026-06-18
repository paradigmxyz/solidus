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
        OutcomeEffect config allocatorDepth entryMode targetInitial target
          (.halt kind)) :
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

/-- Canonical function-call result after the target return frame is attached. -/
inductive CallResultRel
    (contract : MemoryContract.Contract)
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetCaller targetEntry : TargetState) (callerStack : List Word) :
    Functions.InteractionSemantics.CallResult ->
      Expressions.InteractionSemantics.Outcome -> Prop where
  | returned {source : SourceState} {values : List Word}
      {target : TargetState}
      (shared : SharedRel contract source.shared target.evm.toSharedState)
      (stack : target.evm.stack = values.reverse ++ callerStack)
      (returnStack : target.returns = targetCaller.returns)
      (effect :
        ActivationEffect config allocatorDepth entryMode targetEntry target) :
      CallResultRel contract config allocatorDepth entryMode
        targetCaller targetEntry callerStack
        (.returned source values)
        (Structured.EffectSemantics.Outcome.regular target)
  | halted (kind : Assembly.HaltKind)
      {source : SourceState} {target : TargetState}
      (shared : SharedRel contract source.shared target.evm.toSharedState)
      (effect :
        OutcomeEffect config allocatorDepth entryMode targetEntry target
          (.halt kind)) :
      CallResultRel contract config allocatorDepth entryMode
        targetCaller targetEntry callerStack
        (.halted kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

abbrev OpenCallResultRel
    (contract : MemoryContract.Contract)
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetCaller targetEntry : TargetState) (callerStack : List Word) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (CallResultRel contract config allocatorDepth entryMode
      targetCaller targetEntry callerStack)

namespace CallResultRel

/-- A halting callee skips caller writeback and frame release, but still
protects every caller-owned frame through the exact argument/call prefix. -/
theorem halt_to_caller
    {contract : MemoryContract.Contract}
    {config : Config} {callerDepth calleeDepth : Nat}
    {callerMode calleeMode : ActivationMode}
    {targetInitial targetCaller targetEntry targetFinal : TargetState}
    {callerStack : List Word}
    {source : SourceState} {kind : Assembly.HaltKind}
    (hPrefix :
      BoundedEffect config calleeDepth (callerDepth + 1)
        targetInitial targetEntry)
    (hCallerBound :
      activationProtectedBound callerDepth callerMode ≤ callerDepth + 1)
    (hCalleeBound :
      activationProtectedBound calleeDepth calleeMode = callerDepth + 1)
    (hCall :
      CallResultRel contract config calleeDepth calleeMode
        targetCaller targetEntry callerStack (.halted kind source)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)) :
    OutcomeEffect config callerDepth callerMode targetInitial targetFinal
      (.halt kind) := by
  cases hCall with
  | halted _ _ hEffect =>
      obtain ⟨finalDepth, hCalleeEffect⟩ :=
        hEffect.exists_boundedEffect
      rw [hCalleeBound] at hCalleeEffect
      exact OutcomeEffect.halt_of_bounded
        (BoundedEffect.weaken hCallerBound
          (hPrefix.trans hCalleeEffect))

end CallResultRel

namespace CallAttachment

/--
Attach one related completed procedure body through the canonical source and
target call wrappers. Argument realization and caller writeback remain owned
by their adjacent call phases.
-/
theorem of_body
    {program : Functions.Program} {expressions : Expressions.Program}
    {fn : Functions.FunDef} {name : Functions.Name}
    {proc : Expressions.Proc}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth sourceFuel targetFuel : Nat}
    {entryMode : ActivationMode}
    {args callArgs callerStack : List Word}
    {paramStore : Locals.Source.Store}
    {sourceAfterArgs : SourceState} {targetCaller : TargetState}
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hLookup :
      Structured.ProcList.lookup? name expressions.toStructured.procs =
        some proc.toStructured)
    (hRetc : proc.retc = fn.returns.length)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc targetCaller.evm.stack =
        some (callArgs, callerStack))
    (hBody :
      Simulation.Interaction.Rel
        (OpenBodyResultRel contract fn.returns config allocatorDepth
          entryMode
          (AllocationInteractionCall.CalleeEntry.structuredState
            targetCaller callArgs callerStack fn.returns.length))
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore))
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          proc.body
          (AllocationInteractionCall.CalleeEntry.structuredState
            targetCaller callArgs callerStack fn.returns.length))) :
    Simulation.Interaction.Rel
      (OpenCallResultRel contract config allocatorDepth entryMode
        targetCaller
        (AllocationInteractionCall.CalleeEntry.structuredState
          targetCaller callArgs callerStack fn.returns.length)
        callerStack)
      (Functions.InteractionSemantics.FunDef.openRunBody program fn args
        (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Stmt.openRun expressions
        (targetFuel + 1) (.call name) targetCaller) := by
  let sourceEntry :=
    AllocationInteractionCall.CalleeEntry.sourceState
      sourceAfterArgs fn.returns paramStore
  let targetEntry :=
    AllocationInteractionCall.CalleeEntry.structuredState
      targetCaller callArgs callerStack fn.returns.length
  let sourceNext :
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) ->
        Simulation.Interaction EVMException
          Functions.InteractionSemantics.CallResult := fun result =>
    match result.1.mode with
    | .regular | .leave =>
        do
          let values <-
            (Functions.Source.Store.lookupMany fn.returns
                (Functions.InteractionSemantics.stateModel.vars
                  result.1.state)).elim
              (throw EvmYul.EVM.ExecutionException.InvalidInstruction) pure
          pure
            (Functions.Source.Effectful.CallResult.returned
              result.1.state values)
    | .brk | .cont =>
        throw EvmYul.EVM.ExecutionException.InvalidInstruction
    | .halt kind =>
        pure
          (Functions.Source.Effectful.CallResult.halted kind result.1.state)
  let targetNext :
      Expressions.InteractionSemantics.Outcome ->
        Simulation.Interaction EVMException
          Expressions.InteractionSemantics.Outcome := fun outcome =>
    let model := Structured.EffectSemantics.Ordinary.runStateModel
    match outcome.mode with
    | .regular | .leave =>
        match model.popReturn? outcome.state with
        | none => throw EvmYul.EVM.ExecutionException.InvalidInstruction
        | some (frame, returned) =>
            match Structured.StackFrame.attachReturns?
                frame (model.evm outcome.state).stack with
            | none => throw EvmYul.EVM.ExecutionException.InvalidInstruction
            | some stack =>
                let evm := { model.evm outcome.state with stack := stack }
                pure
                  (Structured.EffectSemantics.Outcome.regular
                    (model.withEVM returned evm))
    | .brk | .cont =>
        throw EvmYul.EVM.ExecutionException.InvalidInstruction
    | .halt kind =>
        pure
          (Structured.EffectSemantics.Outcome.halt kind outcome.state)
  have hBodyStructured :
      Simulation.Interaction.Rel
        (OpenBodyResultRel contract fn.returns config allocatorDepth
          entryMode targetEntry)
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
          sourceEntry)
        (Structured.InteractionSemantics.Block.openRun
          expressions.toStructured targetFuel proc.body.toStructured
          targetEntry) := by
    rw [← Expressions.InteractionPreservation.Block.openRun_toStructured]
    simpa [sourceEntry, targetEntry] using hBody
  have hWrapped :=
    Simulation.Interaction.Rel.bind_custom hBodyStructured
      (targetDoneRel :=
        OpenCallResultRel contract config allocatorDepth entryMode
          targetCaller targetEntry callerStack)
      (leftNext := sourceNext)
      (rightNext := targetNext)
      (fun sourceDone targetDone hDone => by
        cases hDone with
        | error hError =>
            exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error hError)
        | ok hResult =>
            cases hResult with
            | @regular source sourceCtx target hLeave hReturns hEffect =>
                simp [Functions.Source.Effectful.Outcome.regular,
                  Locals.Source.Effectful.Outcome.regular,
                  Structured.OutcomeT.regular, sourceNext, targetNext,
                  Functions.InteractionSemantics.stateModel,
                  Locals.InteractionSemantics.stateModel,
                  Locals.Source.Effectful.Ordinary.stateModel,
                  Locals.Source.Effectful.StateModel.vars]
                obtain ⟨values, hValues, hStack⟩ := hLeave.values
                have hPop :
                    target.popReturn? =
                      some
                        ({ callerStack := callerStack,
                           retc := fn.returns.length },
                         { target with returns := targetCaller.returns }) := by
                  unfold Structured.RunState.popReturn?
                  simp only [targetEntry,
                    AllocationInteractionCall.CalleeEntry.structuredState,
                    Structured.RunState.pushReturn_returns] at hReturns
                  rw [hReturns]
                  rfl
                have hLength : values.reverse.length = fn.returns.length := by
                  simpa using Functions.Source.Store.lookupMany_length hValues
                have hAttach :
                    Structured.StackFrame.attachReturns?
                        { callerStack := callerStack,
                          retc := fn.returns.length }
                        target.evm.stack =
                      some (values.reverse ++ callerStack) := by
                  rw [hStack]
                  exact Structured.StackFrame.attachReturns?_eq_some hLength
                let attached : TargetState :=
                  ({ target with returns := targetCaller.returns }).withEVM
                    { target.evm with stack := values.reverse ++ callerStack }
                have hStructural :
                    ActivationEffect config allocatorDepth entryMode
                      target attached := by
                  apply ActivationEffect.of_boundedEffect
                  apply BoundedEffect.of_machine_eq hEffect.ready
                  rfl
                simp only [hValues, Option.elim_some,
                  Simulation.Interaction.monad_pure_bind]
                rw [hPop]
                simp only [Structured.OutcomeT.state]
                rw [hAttach]
                exact Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.ok
                    (CallResultRel.returned
                      (by simpa [attached] using hLeave.shared)
                      (by simp [attached])
                      (by simp [attached])
                      (hEffect.trans hStructural)))
            | @leave source sourceCtx target hLeave hReturns hEffect =>
                simp [Functions.Source.Effectful.Outcome.leave,
                  Locals.Source.Effectful.Outcome.leave,
                  Structured.OutcomeT.leave, sourceNext, targetNext,
                  Functions.InteractionSemantics.stateModel,
                  Locals.InteractionSemantics.stateModel,
                  Locals.Source.Effectful.Ordinary.stateModel,
                  Locals.Source.Effectful.StateModel.vars]
                obtain ⟨values, hValues, hStack⟩ := hLeave.values
                have hPop :
                    target.popReturn? =
                      some
                        ({ callerStack := callerStack,
                           retc := fn.returns.length },
                         { target with returns := targetCaller.returns }) := by
                  unfold Structured.RunState.popReturn?
                  simp only [targetEntry,
                    AllocationInteractionCall.CalleeEntry.structuredState,
                    Structured.RunState.pushReturn_returns] at hReturns
                  rw [hReturns]
                  rfl
                have hLength : values.reverse.length = fn.returns.length := by
                  simpa using Functions.Source.Store.lookupMany_length hValues
                have hAttach :
                    Structured.StackFrame.attachReturns?
                        { callerStack := callerStack,
                          retc := fn.returns.length }
                        target.evm.stack =
                      some (values.reverse ++ callerStack) := by
                  rw [hStack]
                  exact Structured.StackFrame.attachReturns?_eq_some hLength
                let attached : TargetState :=
                  ({ target with returns := targetCaller.returns }).withEVM
                    { target.evm with stack := values.reverse ++ callerStack }
                have hStructural :
                    ActivationEffect config allocatorDepth entryMode
                      target attached := by
                  apply ActivationEffect.of_boundedEffect
                  apply BoundedEffect.of_machine_eq hEffect.ready
                  rfl
                simp only [hValues, Option.elim_some,
                  Simulation.Interaction.monad_pure_bind]
                rw [hPop]
                simp only [Structured.OutcomeT.state]
                rw [hAttach]
                exact Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.ok
                    (CallResultRel.returned
                      (by simpa [attached] using hLeave.shared)
                      (by simp [attached])
                      (by simp [attached])
                      (hEffect.trans hStructural)))
            | brk hReturns hEffect =>
                simp [Functions.Source.Effectful.Outcome.brk,
                  Locals.Source.Effectful.Outcome.brk,
                  Structured.OutcomeT.brk, sourceNext, targetNext]
                exact Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.error rfl)
            | cont hReturns hEffect =>
                simp [Functions.Source.Effectful.Outcome.cont,
                  Locals.Source.Effectful.Outcome.cont,
                  Structured.OutcomeT.cont, sourceNext, targetNext]
                exact Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.error rfl)
            | halt kind hShared hEffect =>
                simp [Functions.Source.Effectful.Outcome.halt,
                  Locals.Source.Effectful.Outcome.halt,
                  Structured.OutcomeT.halt, sourceNext, targetNext]
                exact Simulation.Interaction.Rel.done
                  (Simulation.Interaction.ExceptRel.ok
                    (CallResultRel.halted kind hShared hEffect)))
  have hSourceEq :
      Functions.InteractionSemantics.FunDef.openRunBody program fn args
          (sourceFuel + 1) sourceAfterArgs =
        Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRun program
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            sourceEntry)
          sourceNext := by
    unfold Functions.InteractionSemantics.FunDef.openRunBody
      Functions.Source.Canonical.FunDef.runBody
      Functions.Source.Effectful.Control.FunDef.runBody
    rw [hInsert]
    simp only [Option.elim_some]
    change
      Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRun program
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            sourceEntry)
          _ =
        Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRun program
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            sourceEntry)
          sourceNext
    congr 1
  have hTargetEq :
      Expressions.InteractionSemantics.Stmt.openRun expressions
          (targetFuel + 1) (.call name) targetCaller =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Block.openRun
            expressions.toStructured targetFuel proc.body.toStructured
            targetEntry)
          targetNext := by
    rw [Expressions.InteractionPreservation.Stmt.openRun_toStructured]
    change
      Structured.EffectSemantics.Control.Stmt.run
          Structured.EffectSemantics.Ordinary.runStateModel
          Structured.InteractionSemantics.handler expressions.toStructured
          (targetFuel + 1) (.call name) targetCaller = _
    rw [show targetFuel + 1 = Nat.succ targetFuel by omega]
    simp only [Structured.EffectSemantics.Control.Stmt.run, hLookup,
      Expressions.Proc.toStructured,
      Structured.EffectSemantics.Ordinary.runStateModel_evm,
      Structured.EffectSemantics.Ordinary.runStateModel_withEVM,
      Structured.EffectSemantics.Ordinary.runStateModel_pushReturn,
      Structured.EffectSemantics.Ordinary.runStateModel_popReturn?]
    rw [hSplit, hRetc]
    dsimp [targetEntry, targetNext,
      AllocationInteractionCall.CalleeEntry.structuredState]
    congr 1
    funext outcome
    rcases outcome with ⟨state, mode⟩
    cases mode with
    | regular | leave =>
        cases hPop : state.popReturn? with
        | none => rfl
        | some popped =>
            rcases popped with ⟨frame, returned⟩
            cases hAttach : Structured.StackFrame.attachReturns?
                frame state.evm.stack <;> rfl
    | brk | cont | halt => rfl
  rw [hSourceEq, hTargetEq]
  exact hWrapped

end CallAttachment

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
                    have hActivation :=
                      hEffect.activation_of_not_halt (by
                        intro kind hEq
                        cases hEq)
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
                        hActivation.ready
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
                      hActivation.trans
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
                              using hTargetReturns)
                              (hEffect.activation_of_not_halt (by
                                intro kind hEq
                                cases hEq))))
                    | cont _ _ _ _ =>
                        exact Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok
                            (BodyResultRel.cont (by
                            simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                              using hTargetReturns)
                              (hEffect.activation_of_not_halt (by
                                intro kind hEq
                                cases hEq))))
                    | leave hLeave =>
                        exact Simulation.Interaction.Rel.done
                          (Simulation.Interaction.ExceptRel.ok
                            (BodyResultRel.leave (by simpa [
                              AllocationInteractionStatement.outcomeLive]
                            using hLeave) (by
                              simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                                using hTargetReturns)
                              (hEffect.activation_of_not_halt (by
                                intro kind hEq
                                cases hEq))))
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
    {globalFrameWords allocatorDepth frameBase sourceFuel fuelBound
      targetExtra : Nat}
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
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hTargetExtra : 3 ≤ targetExtra)
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
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              AllocationInteractionRecursive.callStride expressions *
                (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (OpenBodyResultRel contract fn.returns config allocatorDepth
          artifact.mode target)
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          artifact.lowerProc.body target) := by
  obtain ⟨targetFuel, hTargetFuel, hEpilogueFuel, hTargetFuelEq, hBody⟩ :=
    AllocationInteractionRecursiveResource.SelectedCallee.body_of_function_context
      (targetExtra := targetExtra) prepared hProgramScoped hEntry hZero hStackLength
      hReservation hConfig hReady hOwned hBudget hFuelBudget hSourceFuel hSuccess
      hRecursive
  have hReturnsLive :
      forall localName,
        localName ∈ fn.returns ->
          localName ∈
            Functions.Scope.Block.outEnv
              (fn.returns ++ fn.params) fn.body := by
    intro localName hName
    exact Functions.Scope.Block.mem_outEnv (by simp [hName])
  refine ⟨targetFuel, hTargetFuel, hTargetFuelEq, ?_⟩
  exact complete_body_of_rel prepared hConfig hReturnsLive
    (by omega) hBody

/--
Run a compiler-selected callee through the canonical internal-call wrappers.
The caller-side argument phase supplies the exact split and initialized entry;
this theorem owns only callee execution and return attachment.
-/
theorem complete_call
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
    {globalFrameWords allocatorDepth frameBase sourceFuel fuelBound
      targetExtra : Nat}
    {config : Config}
    {args callArgs callerStack : List Word}
    {paramStore : Locals.Source.Store}
    {sourceAfterArgs : SourceState} {targetCaller : TargetState}
    {reservation : MemoryContract.ScratchReservation}
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore)
    (hSplit :
      Structured.StackFrame.splitArgs? artifact.lowerProc.argc
          targetCaller.evm.stack =
        some (callArgs, callerStack))
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase artifact.mode
        (AllocationInteractionCall.CalleeEntry.sourceState
          sourceAfterArgs fn.returns paramStore)
        (AllocationInteractionCall.CalleeEntry.structuredState
          targetCaller callArgs callerStack fn.returns.length))
    (hZero :
      forall localName,
        localName ∈ artifact.slots.returns.map Prod.fst ->
        (AllocationInteractionCall.CalleeEntry.sourceState
          sourceAfterArgs fn.returns paramStore).vars localName =
            some AllocationSupport.zeroWord)
    (hStackLength :
      (AllocationInteractionCall.CalleeEntry.structuredState
        targetCaller callArgs callerStack fn.returns.length).evm.stack.length =
        artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady :
      AllocatorReady config allocatorDepth
        (AllocationInteractionCall.CalleeEntry.structuredState
          targetCaller callArgs callerStack fn.returns.length))
    (hOwned :
      ActivationOwned config allocatorDepth frameBase artifact.mode)
    (hBudget : AllocationInteractionFrame.Budget config allocatorDepth)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hTargetExtra : 3 ≤ targetExtra)
    (hSourceFuel : sourceFuel < fuelBound)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (root := prepared.rootArtifact hProgramScoped)
        contract globalFrameWords fuelBound) :
    exists targetFuel,
      0 < targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              AllocationInteractionRecursive.callStride expressions *
                (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (OpenCallResultRel contract config allocatorDepth artifact.mode
          targetCaller
          (AllocationInteractionCall.CalleeEntry.structuredState
            targetCaller callArgs callerStack fn.returns.length)
          callerStack)
        (Functions.InteractionSemantics.FunDef.openRunBody
          program fn args (sourceFuel + 1) sourceAfterArgs)
        (Expressions.InteractionSemantics.Stmt.openRun
          expressions (targetFuel + 1) (.call name) targetCaller) := by
  obtain ⟨targetFuel, hTargetFuel, hTargetFuelEq, hBody⟩ :=
    complete_body prepared hProgramScoped hEntry hZero hStackLength
      hReservation hConfig hReady hOwned hBudget hFuelBudget hTargetExtra
      hSourceFuel hSuccess
      hRecursive
  refine ⟨targetFuel, hTargetFuel, hTargetFuelEq, ?_⟩
  exact CallAttachment.of_body hInsert artifact.targetLookup
    prepared.procRetc hSplit hBody

end SelectedCallee

end AllocationInteractionCallResultResource
end Functions
end EvmCompiler
