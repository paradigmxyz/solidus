import EvmCompiler.Functions.AllocationObserverCleanup
import EvmCompiler.Functions.AllocationObserverExpression
import EvmCompiler.Functions.AllocationObserverPrimitive

namespace EvmCompiler
namespace Functions
namespace AllocationObserverCall

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

namespace CalleeEntry

/--
The exact target state constructed by Structured call semantics after argument
splitting and before procedure-body execution.
-/
def structuredState {transcript : Trace}
    (target : Structured.ObserverSemantics.State transcript)
    (args callerStack : EvmYul.Stack Word) (retc : Nat) :
    Structured.ObserverSemantics.State transcript :=
  (Structured.ObserverSemantics.stateModel transcript).pushReturn
    ((Structured.ObserverSemantics.stateModel transcript).withEVM target
      { target.source.evm with stack := args })
    callerStack retc

/--
Argument evaluation followed by the actual Structured call-frame construction
establishes the transient entry relation for an all-stack callee.
-/
theorem stack_of_arguments
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {callerPlan calleePlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase calleeFrameBase : Nat}
    {callerMode : AllocationObserverRelation.ActivationMode}
    {pending : List (Locals.Name × Nat)}
    {sourceAfterArgs : Functions.ObserverSemantics.State transcript}
    {targetInitial targetAfterArgs :
      Structured.ObserverSemantics.State transcript}
    {args : List Word}
    {initialStore : Locals.Source.Store}
    {callerStack : EvmYul.Stack Word}
    {retc : Nat}
    (hArgs :
      AllocationObserverRelation.ActivationExprResultRel
        contract callerPlan callerLive 0 callerFrameBase args.length
        callerMode sourceAfterArgs targetInitial targetAfterArgs args)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) initialStore =
        some args) :
    AllocationObserverRelation.ActivationCalleeEntryRel
      contract calleePlan [] pending calleeFrameBase .stack
      ((Functions.ObserverSemantics.stateModel transcript).withSource
        sourceAfterArgs
        { shared := sourceAfterArgs.source.shared
          vars := initialStore })
      (structuredState targetAfterArgs args.reverse callerStack retc) := by
  have hBase := hArgs.state.base
  apply AllocationObserverRelation.ActivationCalleeEntryRel.stack_empty
      (values := args) (suffix := [])
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.pushReturn] using hBase.cursor
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Simulation.ResourceReplay.State.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hBase.core.machine
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Simulation.ResourceReplay.State.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hBase.core.world
  · simpa [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hArgs.state.activeNoWrap
  · simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource] using hLookup
  · simp [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.withEVM, Structured.RunState.pushReturn]

/--
Argument evaluation after the real scratch-frame acquire sequence establishes
the transient entry relation for a frame-backed callee.

The shared target-growth relation transports the acquire-time frame bounds
through arbitrary checked argument expressions.
-/
theorem scratch_of_arguments
    {contract : MemoryContract.Contract}
    {globalFrameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {transcript : Trace}
    {callerPlan calleePlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : AllocationObserverRelation.ActivationMode}
    {pending : List (Locals.Name × Nat)}
    {sourceAfterArgs : Functions.ObserverSemantics.State transcript}
    {targetAfterAcquire targetAfterArgs :
      Structured.ObserverSemantics.State transcript}
    {args : List Word}
    {initialStore : Locals.Source.Store}
    {callerStack : EvmYul.Stack Word}
    {retc : Nat}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hArgs :
      AllocationObserverRelation.ActivationExprResultRel
        contract callerPlan callerLive 1 callerFrameBase args.length
        callerMode sourceAfterArgs targetAfterAcquire targetAfterArgs args)
    (hAcquireStack :
      targetAfterAcquire.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          callerStack)
    (hFrameActive :
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetAfterAcquire.source.evm.activeWords.toNat *
          MemoryContract.wordBytes)
    (hFrameAllocated :
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetAfterAcquire.source.evm.toMachineState.memory.size)
    (hGrowth :
      AllocationObserverRelation.Frame.TargetGrowth
        targetAfterAcquire targetAfterArgs)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) initialStore =
        some args) :
    AllocationObserverRelation.ActivationCalleeEntryRel
      contract calleePlan [] pending
      (AllocationObserverRelation.Frame.baseAt config depth)
      (.scratch 0 config.frameWords)
      ((Functions.ObserverSemantics.stateModel transcript).withSource
        sourceAfterArgs
        { shared := sourceAfterArgs.source.shared
          vars := initialStore })
      (structuredState targetAfterArgs
        (args.reverse ++
          [EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth)])
        callerStack retc) := by
  have hArgsLength : args.length = pending.length := by
    simpa using Functions.Source.Store.lookupMany_length hLookup
  have hFinalActive :
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetAfterArgs.source.evm.activeWords.toNat *
          MemoryContract.wordBytes :=
    hFrameActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hGrowth.active)
  have hFinalAllocated :
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetAfterArgs.source.evm.toMachineState.memory.size :=
    hFrameAllocated.trans hGrowth.memory
  have hFrameNoWrap :=
    AllocationObserverRelation.Frame.noWrap_of_budget_of_scratchFrameConfig?
      hConfig hBudget
  have hFrameHost :=
    AllocationObserverRelation.Frame.hostAddressable_of_budget_of_scratchFrameConfig?
      hConfig hBudget
  obtain ⟨reservation, hReservation, hReserved⟩ :=
    AllocationObserverRelation.Frame.reserved_of_budget_of_scratchFrameConfig?
      hConfig hBudget
  have hBase := hArgs.state.base
  apply
    AllocationObserverRelation.ActivationCalleeEntryRel.scratch_empty
      (values := args)
      (suffix :=
        [EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config depth)])
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.pushReturn] using hBase.cursor
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Simulation.ResourceReplay.State.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hBase.core.machine
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Simulation.ResourceReplay.State.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hBase.core.world
  · rw [← hArgsLength]
    simp [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn]
  · exact hFinalActive
  · exact hFinalAllocated
  · exact hFrameNoWrap
  · exact hFrameHost
  · simpa [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hArgs.state.activeNoWrap
  · exact ⟨reservation, hReservation, hReserved⟩
  · simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource] using hLookup
  · simp [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.withEVM, Structured.RunState.pushReturn]

end CalleeEntry

namespace StructuredCall

inductive ReturnMode where
  | regular
  | leave

def ReturnMode.outcome {transcript : Trace}
    (mode : ReturnMode)
    (state : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Outcome
      (transcript := transcript) :=
  match mode with
  | .regular => Structured.EffectSemantics.Outcome.regular state
  | .leave => Structured.EffectSemantics.Outcome.leave state

/--
A regular procedure-body evaluation determines the real Structured return-frame
pop and return-vector attachment without an externally supplied frame witness.
-/
theorem regular
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {fuel : Nat}
    {name : Structured.Name}
    {proc : Structured.Proc}
    {target bodyFinal :
      Structured.ObserverSemantics.State transcript}
    {args callerStack returnedValues : EvmYul.Stack Word}
    (hLookup :
      Structured.ProcList.lookup? name targetProgram.procs = some proc)
    (hTargetStack :
      target.source.evm.stack = args ++ callerStack)
    (hArgsLength : args.length = proc.argc)
    (hBody :
      Structured.ObserverSemantics.Block.Eval targetProgram fuel proc.body
        (CalleeEntry.structuredState target args callerStack proc.retc)
        (Structured.EffectSemantics.Outcome.regular bodyFinal))
    (hReturnedStack :
      bodyFinal.source.evm.stack = returnedValues)
    (hReturnedLength : returnedValues.length = proc.retc) :
    ∃ returned final,
      (Structured.ObserverSemantics.stateModel transcript).popReturn?
          bodyFinal =
        some
          ({ callerStack := callerStack, retc := proc.retc }, returned) ∧
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (fuel + 1) (.call name) target
        (Structured.EffectSemantics.Outcome.regular final) ∧
      final.cursor = bodyFinal.cursor ∧
      final.source.evm.stack = returnedValues ++ callerStack ∧
      final.source.evm.toMachineState =
        bodyFinal.source.evm.toMachineState ∧
      final.source.evm.toSharedState.toState =
        bodyFinal.source.evm.toSharedState.toState ∧
      final.source.returns = target.source.returns := by
  obtain ⟨returned, hPop, hCursor, hEVM, hReturns⟩ :=
    Structured.ObserverSemantics.CallStack.popReturn_of_nonhalting_eval
      hBody (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
  have hSplit :
      Structured.StackFrame.splitArgs? proc.argc target.source.evm.stack =
        some (args, callerStack) := by
    rw [hTargetStack]
    simpa [hArgsLength] using
      Structured.StackFrame.splitArgs?_append args callerStack
  have hAttach :
      Structured.StackFrame.attachReturns?
          { callerStack := callerStack, retc := proc.retc }
          bodyFinal.source.evm.stack =
        some (returnedValues ++ callerStack) := by
    rw [hReturnedStack]
    exact
      Structured.StackFrame.attachReturns?_eq_some hReturnedLength
  let final :=
    (Structured.ObserverSemantics.stateModel transcript).withEVM returned
      { bodyFinal.source.evm with
        stack := returnedValues ++ callerStack }
  have hEval :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (fuel + 1) (.call name) target
        (Structured.EffectSemantics.Outcome.regular final) := by
    exact
      Structured.EffectSemantics.Stmt.Eval.call_regular
        hLookup hSplit hBody hPop hAttach
  refine ⟨returned, final, hPop, hEval, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, Structured.ObserverSemantics.stateModel, hCursor]
  · simp [final, Structured.ObserverSemantics.stateModel]
  · simp [final, Structured.ObserverSemantics.stateModel, hEVM]
  · simp [final, Structured.ObserverSemantics.stateModel, hEVM]
  · simp [final, Structured.ObserverSemantics.stateModel, hReturns]

/--
A procedure body that exits with `leave` uses the Structured call-leave rule
but still returns regularly to its caller after popping and attaching the
return vector.
-/
theorem leave
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {fuel : Nat}
    {name : Structured.Name}
    {proc : Structured.Proc}
    {target bodyFinal :
      Structured.ObserverSemantics.State transcript}
    {args callerStack returnedValues : EvmYul.Stack Word}
    (hLookup :
      Structured.ProcList.lookup? name targetProgram.procs = some proc)
    (hTargetStack :
      target.source.evm.stack = args ++ callerStack)
    (hArgsLength : args.length = proc.argc)
    (hBody :
      Structured.ObserverSemantics.Block.Eval targetProgram fuel proc.body
        (CalleeEntry.structuredState target args callerStack proc.retc)
        (Structured.EffectSemantics.Outcome.leave bodyFinal))
    (hReturnedStack :
      bodyFinal.source.evm.stack = returnedValues)
    (hReturnedLength : returnedValues.length = proc.retc) :
    ∃ returned final,
      (Structured.ObserverSemantics.stateModel transcript).popReturn?
          bodyFinal =
        some
          ({ callerStack := callerStack, retc := proc.retc }, returned) ∧
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (fuel + 1) (.call name) target
        (Structured.EffectSemantics.Outcome.regular final) ∧
      final.cursor = bodyFinal.cursor ∧
      final.source.evm.stack = returnedValues ++ callerStack ∧
      final.source.evm.toMachineState =
        bodyFinal.source.evm.toMachineState ∧
      final.source.evm.toSharedState.toState =
        bodyFinal.source.evm.toSharedState.toState ∧
      final.source.returns = target.source.returns := by
  obtain ⟨returned, hPop, hCursor, hEVM, hReturns⟩ :=
    Structured.ObserverSemantics.CallStack.popReturn_of_nonhalting_eval
      hBody (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
  have hSplit :
      Structured.StackFrame.splitArgs? proc.argc target.source.evm.stack =
        some (args, callerStack) := by
    rw [hTargetStack]
    simpa [hArgsLength] using
      Structured.StackFrame.splitArgs?_append args callerStack
  have hAttach :
      Structured.StackFrame.attachReturns?
          { callerStack := callerStack, retc := proc.retc }
          bodyFinal.source.evm.stack =
        some (returnedValues ++ callerStack) := by
    rw [hReturnedStack]
    exact
      Structured.StackFrame.attachReturns?_eq_some hReturnedLength
  let final :=
    (Structured.ObserverSemantics.stateModel transcript).withEVM returned
      { bodyFinal.source.evm with
        stack := returnedValues ++ callerStack }
  have hEval :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (fuel + 1) (.call name) target
        (Structured.EffectSemantics.Outcome.regular final) := by
    exact
      Structured.EffectSemantics.Stmt.Eval.call_leave
        hLookup hSplit hBody hPop hAttach
  refine ⟨returned, final, hPop, hEval, ?_, ?_, ?_, ?_, ?_⟩
  · simp [final, Structured.ObserverSemantics.stateModel, hCursor]
  · simp [final, Structured.ObserverSemantics.stateModel]
  · simp [final, Structured.ObserverSemantics.stateModel, hEVM]
  · simp [final, Structured.ObserverSemantics.stateModel, hEVM]
  · simp [final, Structured.ObserverSemantics.stateModel, hReturns]

/--
A terminal procedure body propagates directly through the Structured call.
The caller return frame and generated writeback path are unreachable.
-/
theorem halt
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {fuel : Nat}
    {name : Structured.Name}
    {proc : Structured.Proc}
    {target bodyFinal :
      Structured.ObserverSemantics.State transcript}
    {args callerStack : EvmYul.Stack Word}
    {kind : Assembly.HaltKind}
    (hLookup :
      Structured.ProcList.lookup? name targetProgram.procs = some proc)
    (hTargetStack :
      target.source.evm.stack = args ++ callerStack)
    (hArgsLength : args.length = proc.argc)
    (hBody :
      Structured.ObserverSemantics.Block.Eval targetProgram fuel proc.body
        (CalleeEntry.structuredState target args callerStack proc.retc)
        (Structured.EffectSemantics.Outcome.halt kind bodyFinal)) :
    Structured.ObserverSemantics.Stmt.Eval
      targetProgram (fuel + 1) (.call name) target
      (Structured.EffectSemantics.Outcome.halt kind bodyFinal) := by
  have hSplit :
      Structured.StackFrame.splitArgs? proc.argc target.source.evm.stack =
        some (args, callerStack) := by
    rw [hTargetStack]
    simpa [hArgsLength] using
      Structured.StackFrame.splitArgs?_append args callerStack
  exact
    Structured.EffectSemantics.Stmt.Eval.call_halt
      hLookup hSplit hBody

end StructuredCall

namespace CallCompiler

/--
Successful lowering and Locals compilation of a Functions call expose the
actual adjacent target phases: argument code, the Structured call, returned
value stores, and the optional scratch-frame release.

The theorem retains only equations produced by the existing compilers; it does
not accept generated target code as an independent premise.
-/
theorem components
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.call targets functionName args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ fn loweredArgs callArgs stores release argsCode releaseCode,
      AllocationSupport.lookupFun? functionName lowerCtx.functions =
          some fn ∧
        args.length = fn.params.length ∧
        targets.length = fn.returns.length ∧
        targets.Nodup ∧
        AllocationLowering.lowerExprList lowerCtx lowerState args =
          some loweredArgs ∧
        (if functionName ∈ lowerCtx.frameFunctions then do
            let frameConfig ← lowerCtx.frameConfig?
            some (AllocationLowering.frameExpr frameConfig :: loweredArgs)
          else
            some loweredArgs) =
          some callArgs ∧
        AllocationLowering.lowerCallTargetsCode?
            lowerCtx lowerState targets.reverse targets.length =
          some stores ∧
        (if functionName ∈ lowerCtx.frameFunctions then do
            let frameConfig ← lowerCtx.frameConfig?
            some
              [ .expr
                  (Locals.Expr.code (results := 0)
                    (AllocationSupport.scratchFrameReleaseCode frameConfig)) ]
          else
            some []) =
          some release ∧
        Locals.ExprSeq.compileCode localsCtx 0
            (AllocationLowering.exprSeqOfList callArgs) =
          some argsCode ∧
        Locals.Block.compileOpen localsCtx { stmts := release } =
          some (releaseCode, localsCtx) ∧
        compiledStmts =
          Locals.codeStmt argsCode ++
            [Expressions.Stmt.call functionName] ++
            Locals.codeStmt stores ++ releaseCode ∧
        lowerFinal = lowerState ∧
        localsFinal = localsCtx := by
  obtain
      ⟨fn, loweredArgs, callArgs, stores, release,
        hLookup, hArgsLength, hTargetsLength, hTargets,
        hLowerArgs, hCallArgs, hStores, hRelease,
        rfl, rfl⟩ :=
    AllocationLowering.lowerStmt_call_components hLower
  cases hArgsCode :
      Locals.ExprSeq.compileCode localsCtx 0
        (AllocationLowering.exprSeqOfList callArgs) with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.Expr.compileCode, hArgsCode]
        at hCompile
  | some argsCode =>
      obtain ⟨releaseCode, hReleaseCode⟩ :
          ∃ releaseCode,
            Locals.Block.compileOpen localsCtx { stmts := release } =
              some (releaseCode, localsCtx) := by
        by_cases hFrame :
            functionName ∈ lowerCtx.frameFunctions
        · cases hConfig : lowerCtx.frameConfig? with
          | none =>
              simp [hFrame, hConfig] at hRelease
          | some frameConfig =>
              have hReleaseEq :
                  release =
                    [ .expr
                        (Locals.Expr.code (results := 0)
                          (AllocationSupport.scratchFrameReleaseCode
                            frameConfig)) ] := by
                simpa [hFrame, hConfig] using hRelease.symm
              subst release
              exact
                ⟨Locals.codeStmt
                    (AllocationSupport.scratchFrameReleaseCode frameConfig),
                  by
                    simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                      Locals.Expr.compileCode]⟩
        · have hReleaseEq : release = [] := by
            simpa [hFrame] using hRelease.symm
          subst release
          exact ⟨[], by simp [Locals.Block.compileOpen]⟩
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.Expr.compileCode, Locals.codeStmt,
        hArgsCode, hReleaseCode] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact
        ⟨fn, loweredArgs, callArgs, stores, release,
          argsCode, releaseCode, hLookup, hArgsLength,
          hTargetsLength, hTargets, hLowerArgs, hCallArgs,
          hStores, hRelease, hArgsCode, hReleaseCode, rfl, rfl, rfl⟩

end CallCompiler

namespace SelectedCallee

/--
Compiler-owned artifact for the source function selected by one call.

Every field is reconstructed from the whole-program allocation lowerer; callers
do not provide generated procedures, layouts, or prelude contexts.
-/
structure Artifact
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program)
    (expressions : Expressions.Program)
    (name : Functions.Name)
    (fn : Functions.FunDef) where
  recipe : AllocationSupport.AllocationRecipe
  stackSlots : MixedAllocation.SlotSet
  frameName : Locals.Name
  startState : AllocationSupport.CompileState
  finalState : AllocationSupport.CompileState
  proc : Locals.Proc
  lowerProc : Expressions.Proc
  slots : AllocationSupport.FunSlots
  planEntry : AllocationSupport.ScopedAllocation
  validate :
    AllocationLowering.validatePlan? allocation program =
      some (recipe, stackSlots)
  fresh :
    AllocationLowering.freshFrameName program = some frameName
  wholeLower :
    AllocationLowering.lowerExpressionsFromAllocation?
        allocation program =
      some expressions
  lower :
    AllocationLowering.lowerFunction? recipe stackSlots frameName
        (AllocationSupport.scratchFrameConfig?
          program.memoryContract recipe.frameWords)
        startState fn =
      some (proc, finalState)
  compile : proc.toExpressions? = some lowerProc
  targetLookup :
    Structured.ProcList.lookup? name
        expressions.toStructured.procs =
      some lowerProc.toStructured
  slotsLookup :
    AllocationSupport.lookupFun? fn.name recipe.functionSlots =
      some slots
  slotsMatch : slots.Matches fn
  planEntryMem : planEntry ∈ recipe.functions
  planEntryScope : planEntry.scope = .function fn.name
  planEntryState :
    planEntry.state =
      (AllocationSupport.planBlockOpen (.function fn.name)
        { allocation :=
            { env := AllocationSupport.functionEnv slots
              nextSlot := startState.nextSlot }
          nextScope := 0
          scopes := [] }
        fn.body).allocation
  bodyScopesMem :
    ∀ entry,
      entry ∈
          (AllocationSupport.planBlockOpen (.function fn.name)
            { allocation :=
                { env := AllocationSupport.functionEnv slots
                  nextSlot := startState.nextSlot }
              nextScope := 0
              scopes := [] }
            fn.body).scopes →
        entry ∈ recipe.lexicalScopes
  sourceName : fn.name = name
  sourceMem : fn ∈ program.functions

/--
Construct the selected-callee artifact from the real whole-program lowering and
the canonical source function lookup.
-/
theorem of_lowering
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (hLower :
      AllocationLowering.lowerExpressionsFromAllocation?
          allocation program =
        some expressions)
    (hFind :
      Functions.Source.FunList.find? name program.functions = some fn) :
    Nonempty (Artifact allocation program expressions name fn) := by
  obtain
      ⟨recipe, stackSlots, frameName, before, after, proc, lowerProc,
        selectedSlots, planEntry, hValidate, hFresh, hSelected, hCompile,
        hLookup, hSelectedSlots, hPlanEntryMem, hPlanEntryScope,
        hPlanEntryState, hBodyScopesMem⟩ :=
    AllocationLowering.lowerExpressionsFromAllocation?_find_compiled_function
      hLower hFind
  have hMem :
      fn ∈ program.functions :=
    Functions.Source.FunList.mem_of_find?_eq_some hFind
  obtain
      ⟨slots, _entry, _added, hSlotsLookup, hSlotsMatch,
        _hEntry, _hScope, _hEnv, _hPlan⟩ :=
    AllocationLowering.validatePlan?_function_components
      hValidate hMem
  have hSlotsEq : slots = selectedSlots := by
    rw [hSelectedSlots] at hSlotsLookup
    exact (Option.some.inj hSlotsLookup).symm
  subst slots
  exact
    ⟨{ recipe := recipe
       stackSlots := stackSlots
       frameName := frameName
       startState := before
       finalState := after
       proc := proc
       lowerProc := lowerProc
       slots := selectedSlots
       planEntry := planEntry
       validate := hValidate
       fresh := hFresh
       wholeLower := hLower
       lower := hSelected
       compile := hCompile
       targetLookup := hLookup
       slotsLookup := hSelectedSlots
       slotsMatch := hSlotsMatch
       planEntryMem := hPlanEntryMem
       planEntryScope := hPlanEntryScope
       planEntryState := hPlanEntryState
       bodyScopesMem := hBodyScopesMem
       sourceName :=
         Functions.Source.FunList.name_eq_of_find?_eq_some hFind
       sourceMem := hMem }⟩

def Artifact.root
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (_artifact : Artifact allocation program expressions name fn) :
    Locals.Allocation.ScopeId :=
  .function fn.name

def Artifact.scratchBindings
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    List (Locals.Name × Nat) :=
  AllocationLowering.scratchBindingsForRoot
    artifact.recipe artifact.stackSlots artifact.root

def Artifact.needsFrame
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) : Bool :=
  !artifact.scratchBindings.isEmpty

theorem Artifact.mem_frameFunctions_iff
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    name ∈
        AllocationLowering.frameFunctions
          artifact.recipe artifact.stackSlots ↔
      artifact.needsFrame = true := by
  have hName : fn.name = name := artifact.sourceName
  simpa [Artifact.needsFrame, Artifact.scratchBindings, Artifact.root,
    AllocationLowering.functionNeedsFrame,
    AllocationLowering.rootNeedsFrame, hName] using
    (AllocationLowering.mem_frameFunctions_iff_of_lookup
      artifact.slotsLookup)

theorem Artifact.planEntry_env_extension
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    ∃ added,
      artifact.planEntry.state.env =
        added ++ AllocationSupport.functionEnv artifact.slots := by
  obtain ⟨added, hEnv⟩ :=
    AllocationSupport.planBlockOpen_env_extension
      (.function fn.name)
      { allocation :=
          { env := AllocationSupport.functionEnv artifact.slots
            nextSlot := artifact.startState.nextSlot }
        nextScope := 0
        scopes := [] }
      fn.body
  refine ⟨added, ?_⟩
  rw [artifact.planEntryState]
  simpa using hEnv

theorem Artifact.frameName_not_mem_planEntry_env
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    artifact.frameName ∉ artifact.planEntry.state.env.map Prod.fst := by
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      artifact.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some artifact.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      artifact.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨artifact.recipe,
      by simp [hRecipe],
      artifact.planEntry, ?_, hFrame⟩
  simp only [AllocationLowering.scopedStates, List.mem_cons,
    List.mem_append]
  exact Or.inl (Or.inr artifact.planEntryMem)

theorem Artifact.frameName_not_mem_lexical_entry_env
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn)
    {entry : AllocationSupport.ScopedAllocation}
    (hEntry : entry ∈ artifact.recipe.lexicalScopes) :
    artifact.frameName ∉ entry.state.env.map Prod.fst := by
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      artifact.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some artifact.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      artifact.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨artifact.recipe,
      by simp [hRecipe],
      entry, ?_, hFrame⟩
  simp only [AllocationLowering.scopedStates, List.mem_cons,
    List.mem_append]
  exact Or.inr hEntry

def Artifact.entryLayout
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    Locals.Layout :=
  fn.params.reverse ++
    if artifact.needsFrame then [artifact.frameName] else []

def Artifact.lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    AllocationLowering.Ctx :=
  { functions := artifact.recipe.functionSlots
    frameConfig? :=
      AllocationSupport.scratchFrameConfig?
        program.memoryContract artifact.recipe.frameWords
    frameName := artifact.frameName
    stackSlots := artifact.stackSlots
    root := artifact.root
    scratchBindings := artifact.scratchBindings
    frameFunctions :=
      AllocationLowering.frameFunctions
        artifact.recipe artifact.stackSlots }

def Artifact.entryCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    Locals.Ctx :=
  Locals.Ctx.procEntryWithLayoutAndRetc
    artifact.entryLayout fn.returns.length

def Artifact.bodyStart
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    AllocationLowering.State :=
  let paramResult :=
    AllocationLowering.lowerParams artifact.lowerCtx
      artifact.slots.params artifact.entryLayout
  let returnResult :=
    AllocationLowering.lowerReturns artifact.lowerCtx
      artifact.slots.returns paramResult.2
  { allocation :=
      { env := AllocationSupport.functionEnv artifact.slots
        nextSlot := artifact.startState.nextSlot }
    layout := returnResult.2 }

def Artifact.markers
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    List Locals.Stmt :=
  [AllocationLowering.bindEntryLayout artifact.entryLayout] ++
    if artifact.needsFrame then
      [AllocationLowering.bindScratchBindings
        fn.params.length artifact.scratchBindings]
    else
      []

/--
Complete compiler-owned view of one selected function. The recursive observer
proof consumes this package instead of reopening allocation lowering and Locals
procedure compilation.
-/
structure Prepared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) where
  plan : Locals.Allocation.Plan
  paramCtx : Locals.Ctx
  returnCtx : Locals.Ctx
  mode : AllocationObserverRelation.ActivationMode
  body : Locals.Block
  bodyFinal : AllocationLowering.State
  returnValues : Locals.ExprSeq fn.returns.length
  markerCode : List Expressions.Stmt
  paramCode : List Expressions.Stmt
  returnCode : List Expressions.Stmt
  bodyCode : List Expressions.Stmt
  bodyCtx : Locals.Ctx
  returnValueCode : Structured.Code
  cleanup : Structured.Code
  planLookup :
    allocation.find? (.function fn.name) = some plan
  planEq :
    plan =
      MixedAllocation.allocationOfState
        program.memoryContract artifact.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          artifact.recipe artifact.stackSlots artifact.planEntry.scope
          artifact.planEntry.state)
        artifact.planEntry.state
  planWF : plan.WellFormed
  bodyPlan :
    artifact.planEntry.state = bodyFinal.allocation
  prelude :
    AllocationObserverContext.FunctionPreludeContext
      artifact.lowerCtx plan artifact.recipe.frameWords artifact.slots
      artifact.entryCtx paramCtx returnCtx mode
  mode_eq :
    mode =
      if artifact.needsFrame then
        .scratch 0 artifact.recipe.frameWords
      else
        .stack
  lowerBody :
    AllocationLowering.lowerBlockOpen artifact.lowerCtx fn.returns
        artifact.bodyStart fn.body =
      some (body, bodyFinal)
  lowerReturnValues :
    AllocationLowering.lowerReturnExprs artifact.lowerCtx bodyFinal
        fn.returns =
      some returnValues
  compileMarkers :
    Locals.Block.compileOpen artifact.entryCtx
        { stmts := artifact.markers } =
      some (markerCode, artifact.entryCtx)
  compileParams :
    Locals.Block.compileOpen artifact.entryCtx
        { stmts :=
            (AllocationLowering.lowerParams artifact.lowerCtx
              artifact.slots.params artifact.entryCtx.layout).1 } =
      some (paramCode, paramCtx)
  compileReturns :
    Locals.Block.compileOpen paramCtx
        { stmts :=
            (AllocationLowering.lowerReturns artifact.lowerCtx
              artifact.slots.returns paramCtx.layout).1 } =
      some (returnCode, returnCtx)
  compileBody :
    Locals.Block.compileOpen returnCtx body =
      some (bodyCode, bodyCtx)
  compileReturnValues :
    Locals.ExprSeq.compileCode bodyCtx 0 returnValues =
      some returnValueCode
  compileCleanup :
    bodyCtx.cleanupToPreserving? fn.returns.length 0 =
      some cleanup
  procName : artifact.lowerProc.name = fn.name
  procArgc :
    artifact.lowerProc.argc =
      fn.params.length + (if artifact.needsFrame then 1 else 0)
  procRetc : artifact.lowerProc.retc = fn.returns.length
  procBody :
    artifact.lowerProc.body.stmts =
      markerCode ++ paramCode ++ returnCode ++ bodyCode ++
        Locals.codeStmt returnValueCode ++ Locals.codeStmt cleanup

theorem Artifact.prepare
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn) :
    Nonempty (Prepared artifact) := by
  obtain
      ⟨slots, body, bodyFinal, returnValues,
        markerCode, paramCode, paramCtx, returnCode, returnCtx,
        bodyCode, bodyCtx, returnValueCode, cleanup,
        hSlots, hComponents⟩ :=
    AllocationLowering.lowerFunction?_toExpressions?_body_components
      artifact.lower artifact.compile
  have hSlotsEq : slots = artifact.slots := by
    rw [artifact.slotsLookup] at hSlots
    exact (Option.some.inj hSlots).symm
  subst slots
  dsimp only at hComponents
  rcases hComponents with
    ⟨hLowerBody, hLowerReturnValues, hCompileMarkers,
      hCompileParams, hCompileReturns, hCompileBody,
      hCompileReturnValues, hCompileCleanup, hProcName,
      hProcArgc, hProcRetc, hProcBody⟩
  obtain
      ⟨contextSlots, plan, contextParamCode, contextParamCtx,
        contextReturnCode, contextReturnCtx, mode, hContext⟩ :=
    AllocationObserverContext.FunctionPreludeContext.of_validated_function
      artifact.validate artifact.sourceMem artifact.fresh
      artifact.lower artifact.compile
  dsimp only at hContext
  rcases hContext with
    ⟨hPlanLookup, hPlanWF, hContextSlots, _hContextMatch,
      hContextParams, hContextReturns, hPrelude, hMode⟩
  have hContextSlotsEq : contextSlots = artifact.slots := by
    rw [artifact.slotsLookup] at hContextSlots
    exact (Option.some.inj hContextSlots).symm
  subst contextSlots
  have hContextParams' :
      Locals.Block.compileOpen artifact.entryCtx
          { stmts :=
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).1 } =
        some (contextParamCode, contextParamCtx) := by
    simpa [Artifact.lowerCtx, Artifact.entryCtx, Artifact.entryLayout,
      Artifact.root, Artifact.scratchBindings,
      Artifact.needsFrame] using hContextParams
  have hCompileParams' :
      Locals.Block.compileOpen artifact.entryCtx
          { stmts :=
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).1 } =
        some (paramCode, paramCtx) := by
    simpa [Artifact.lowerCtx, Artifact.entryCtx, Artifact.entryLayout,
      Artifact.root, Artifact.scratchBindings,
      Artifact.needsFrame] using hCompileParams
  have hParamEq :
      (contextParamCode, contextParamCtx) = (paramCode, paramCtx) := by
    exact Option.some.inj (hContextParams'.symm.trans hCompileParams')
  cases hParamEq
  have hContextReturns' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              (AllocationLowering.lowerReturns artifact.lowerCtx
                artifact.slots.returns paramCtx.layout).1 } =
        some (contextReturnCode, contextReturnCtx) := by
    simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using hContextReturns
  have hCompileReturns' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              (AllocationLowering.lowerReturns artifact.lowerCtx
                artifact.slots.returns paramCtx.layout).1 } =
        some (returnCode, returnCtx) := by
    simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using hCompileReturns
  have hReturnEq :
      (contextReturnCode, contextReturnCtx) =
        (returnCode, returnCtx) := by
    exact Option.some.inj (hContextReturns'.symm.trans hCompileReturns')
  cases hReturnEq
  have hEntryPlan :=
    AllocationLowering.validatePlan?_function_entry_plan
      artifact.validate artifact.planEntryMem
  have hEntryPlan' :
      allocation.find? (.function fn.name) =
        some
          (MixedAllocation.allocationOfState
            program.memoryContract artifact.recipe.frameWords
            (MixedAllocation.AllocationRecipe.stackEntriesForScope
              artifact.recipe artifact.stackSlots artifact.planEntry.scope
              artifact.planEntry.state)
            artifact.planEntry.state) := by
    simpa [artifact.planEntryScope] using hEntryPlan
  have hPlanEq :
      plan =
        MixedAllocation.allocationOfState
          program.memoryContract artifact.recipe.frameWords
          (MixedAllocation.AllocationRecipe.stackEntriesForScope
            artifact.recipe artifact.stackSlots artifact.planEntry.scope
            artifact.planEntry.state)
          artifact.planEntry.state := by
    rw [hPlanLookup] at hEntryPlan'
    exact Option.some.inj hEntryPlan'
  let planning : AllocationSupport.PlanningState :=
    { allocation := artifact.bodyStart.allocation
      nextScope := 0
      scopes := [] }
  have hBodyAgreement :=
    AllocationLowering.lowerBlockOpen_allocation_eq_planBlockOpen
      fn.body (.function fn.name) planning artifact.lowerCtx fn.returns
      artifact.bodyStart bodyFinal body rfl hLowerBody
  have hBodyPlan :
      artifact.planEntry.state = bodyFinal.allocation := by
    rw [artifact.planEntryState]
    simpa [planning, Artifact.bodyStart] using hBodyAgreement
  refine
    ⟨{ plan := plan
       paramCtx := paramCtx
       returnCtx := returnCtx
       mode := mode
       body := body
       bodyFinal := bodyFinal
       returnValues := returnValues
       markerCode := markerCode
       paramCode := paramCode
       returnCode := returnCode
       bodyCode := bodyCode
       bodyCtx := bodyCtx
       returnValueCode := returnValueCode
       cleanup := cleanup
       planLookup := ?_
       planEq := hPlanEq
       planWF := hPlanWF
       bodyPlan := hBodyPlan
       prelude := ?_
       mode_eq := ?_
       lowerBody := ?_
       lowerReturnValues := ?_
       compileMarkers := ?_
       compileParams := hCompileParams'
       compileReturns := hCompileReturns'
       compileBody := hCompileBody
       compileReturnValues := hCompileReturnValues
       compileCleanup := hCompileCleanup
       procName := hProcName
       procArgc := ?_
       procRetc := hProcRetc
       procBody := hProcBody }⟩
  · simpa using hPlanLookup
  · simpa [Artifact.lowerCtx, Artifact.entryCtx,
      Artifact.entryLayout, Artifact.root, Artifact.scratchBindings,
      Artifact.needsFrame] using hPrelude
  · simpa [Artifact.needsFrame, Artifact.scratchBindings,
      Artifact.root] using hMode
  · simpa [Artifact.lowerCtx, Artifact.bodyStart,
      Artifact.entryLayout, Artifact.root, Artifact.scratchBindings,
      Artifact.needsFrame] using hLowerBody
  · simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using
      hLowerReturnValues
  · simpa [Artifact.markers, Artifact.entryCtx,
      Artifact.entryLayout, Artifact.needsFrame,
      Artifact.scratchBindings] using hCompileMarkers
  · simpa [Artifact.needsFrame, Artifact.scratchBindings,
      Artifact.root] using hProcArgc

theorem Prepared.signatureNodup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact : Artifact allocation program expressions name fn}
    (prepared : Prepared artifact) :
    (fn.returns ++ fn.params).Nodup := by
  have hSlots :
      ((artifact.slots.returns ++ artifact.slots.params).map Prod.fst).Nodup := by
    exact
      AllocationObserverContext.FunctionPreludeContext.signatureNodup
        prepared.prelude
  simpa [List.map_append, artifact.slotsMatch.2.1,
    artifact.slotsMatch.2.2] using hSlots

theorem Artifact.bodyScoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact : Artifact allocation program expressions name fn)
    (hProgramScoped : program.Scoped) :
    Functions.Scope.Block.Scoped
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      fn.body := by
  have hFnScoped : fn.Scoped :=
    Functions.FunList.scoped_of_mem
      hProgramScoped.1 artifact.sourceMem
  exact
    Functions.Scope.Block.Scoped.of_env_equiv
      (before := fn.returns ++ fn.params)
      (after :=
        (artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
      (by
        intro localName
        simp [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2])
      (Functions.FunDef.bodyScoped hFnScoped)

theorem Prepared.location_stack_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact : Artifact allocation program expressions calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          name prepared.bodyFinal.allocation.env =
        some slot)
    (hStack :
      AllocationLowering.isStackSlot artifact.lowerCtx slot = true) :
    ∃ depth,
      prepared.plan.location? name = some (.stack depth) := by
  have hMemBody :
      (name, slot) ∈ prepared.bodyFinal.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  have hMemEntry :
      (name, slot) ∈ artifact.planEntry.state.env := by
    rw [prepared.bodyPlan]
    exact hMemBody
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hSlot : slot ∈ artifact.stackSlots := by
    exact
      (AllocationLowering.isStackSlot_eq_true_iff
        artifact.lowerCtx slot).mp
        (by simpa [Artifact.lowerCtx] using hStack)
  have hEntry :
      (name, slot) ∈
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          artifact.recipe artifact.stackSlots artifact.planEntry.scope
          artifact.planEntry.state := by
    rw [artifact.planEntryScope]
    exact
      MixedAllocation.AllocationRecipe.mem_stackEntriesForScope_function_of_mem_of_slot_mem
        artifact.slotsLookup hEnv hMemEntry hSlot
  have hNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    have hScopeNodup := prepared.planWF.2.1
    simpa [prepared.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  rw [prepared.planEq]
  exact
    MixedAllocation.allocationOfState_location_stack_of_entry
      hNodup hMemEntry hEntry

theorem Prepared.location_scratch_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact : Artifact allocation program expressions calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          name prepared.bodyFinal.allocation.env =
        some slot)
    (hScratch :
      AllocationLowering.isStackSlot artifact.lowerCtx slot = false) :
    prepared.plan.location? name = some (.scratch slot) := by
  have hMemBody :
      (name, slot) ∈ prepared.bodyFinal.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  have hMemEntry :
      (name, slot) ∈ artifact.planEntry.state.env := by
    rw [prepared.bodyPlan]
    exact hMemBody
  have hSlot : slot ∉ artifact.stackSlots := by
    exact
      (AllocationLowering.isStackSlot_eq_false_iff
        artifact.lowerCtx slot).mp
        (by simpa [Artifact.lowerCtx] using hScratch)
  have hNotEntry :
      (name, slot) ∉
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          artifact.recipe artifact.stackSlots artifact.planEntry.scope
          artifact.planEntry.state :=
    MixedAllocation.AllocationRecipe.not_mem_stackEntriesForScope_of_slot_not_mem
      hSlot
  have hNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    have hScopeNodup := prepared.planWF.2.1
    simpa [prepared.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  rw [prepared.planEq]
  exact
    MixedAllocation.allocationOfState_location_scratch_of_not_entry
      hNodup hMemEntry hNotEntry

theorem Prepared.scratch_bound_of_location
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact : Artifact allocation program expressions calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLocation :
      prepared.plan.location? name = some (.scratch slot)) :
    slot < artifact.recipe.frameWords := by
  rw [prepared.planEq] at hLocation
  have hWF :
      (MixedAllocation.allocationOfState
        program.memoryContract artifact.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          artifact.recipe artifact.stackSlots artifact.planEntry.scope
          artifact.planEntry.state)
        artifact.planEntry.state).WellFormed := by
    rw [← prepared.planEq]
    exact prepared.planWF
  exact
    MixedAllocation.allocationOfState_scratch_bound_of_wellFormed
      hWF hLocation

theorem Prepared.mode_eq_scratch_of_needsFrame
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact : Artifact allocation program expressions name fn}
    (prepared : Prepared artifact)
    (hNeedsFrame : artifact.needsFrame = true) :
    prepared.mode =
      .scratch 0 artifact.recipe.frameWords := by
  simpa [hNeedsFrame] using prepared.mode_eq

theorem Prepared.mode_eq_stack_of_noFrame
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact : Artifact allocation program expressions name fn}
    (prepared : Prepared artifact)
    (hNoFrame : artifact.needsFrame = false) :
    prepared.mode = .stack := by
  simpa [hNoFrame] using prepared.mode_eq

end SelectedCallee

namespace EntryMarkers

theorem compileOpen
    {localsCtx : Locals.Ctx}
    {entryLayout : Locals.Layout}
    {baseDepth : Nat}
    {scratchBindings : List (Locals.Name × Nat)}
    {needsFrame : Bool} :
    Locals.Block.compileOpen localsCtx
        { stmts :=
            [AllocationLowering.bindEntryLayout entryLayout] ++
              if needsFrame then
                [AllocationLowering.bindScratchBindings
                  baseDepth scratchBindings]
              else
                [] } =
      some
        ([Expressions.Stmt.code
            [Structured.BasicInstr.bindLocals 0 entryLayout]] ++
          if needsFrame then
            [Expressions.Stmt.code
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)]
          else
            [],
         localsCtx) := by
  exact AllocationLowering.entryMarkers_compileOpen

theorem run_bindScratchBindingsCode
    {transcript : Trace}
    (baseDepth : Nat)
    (bindings : List (Locals.Name × Nat))
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Code.run
        (AllocationSupport.bindScratchBindingsCode baseDepth bindings)
        target =
      .ok target := by
  induction bindings with
  | nil =>
      rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      simp only [AllocationSupport.bindScratchBindingsCode, List.map_cons]
      rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
      change
        (Except.ok target).bind
          (Structured.ObserverSemantics.Code.run
            (AllocationSupport.bindScratchBindingsCode baseDepth rest)) =
          .ok target
      simpa only [Except.bind] using ih

theorem run
    {transcript : Trace}
    (entryLayout : Locals.Layout)
    (baseDepth : Nat)
    (scratchBindings : List (Locals.Name × Nat))
    (needsFrame : Bool)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Code.run
        ([Structured.BasicInstr.bindLocals 0 entryLayout] ++
          if needsFrame then
            AllocationSupport.bindScratchBindingsCode
              baseDepth scratchBindings
          else
            [])
        target =
      .ok target := by
  cases needsFrame with
  | false =>
      rfl
  | true =>
      rw [AllocationObserverPreservation.ObserverCode.run_append]
      change
        (Except.ok target).bind
            (Structured.ObserverSemantics.Code.run
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)) =
          .ok target
      simpa only [Except.bind] using
        run_bindScratchBindingsCode baseDepth scratchBindings target

theorem eval
    {transcript : Trace}
    (program : Structured.Program)
    (entryLayout : Locals.Layout)
    (baseDepth : Nat)
    (scratchBindings : List (Locals.Name × Nat))
    (needsFrame : Bool)
    (target : Structured.ObserverSemantics.State transcript) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval program fuel
        { stmts :=
            [Structured.Stmt.code
              [Structured.BasicInstr.bindLocals 0 entryLayout]] ++
              if needsFrame then
                [Structured.Stmt.code
                  (AllocationSupport.bindScratchBindingsCode
                    baseDepth scratchBindings)]
              else
                [] }
        target
        (Structured.EffectSemantics.Outcome.regular target) := by
  cases needsFrame with
  | false =>
      exact
        ⟨2,
          Structured.EffectSemantics.Block.Eval.cons_regular
            (Structured.EffectSemantics.Stmt.Eval.code (by rfl))
            Structured.EffectSemantics.Block.Eval.nil⟩
  | true =>
      refine
        ⟨3,
          Structured.EffectSemantics.Block.Eval.cons_regular
            (Structured.EffectSemantics.Stmt.Eval.code (by rfl))
            ?_⟩
      exact
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code
            (run_bindScratchBindingsCode
              baseDepth scratchBindings target))
          Structured.EffectSemantics.Block.Eval.nil

end EntryMarkers

namespace ParameterPrelude

/--
Execute the concrete scratch-parameter sequence while converting one raw entry
argument into an ordinary live spilled local.

The code is exactly the value `DUP`, frame-address/store tail, compiler
promotion swaps, and final `POP` emitted by `lowerScratchParam`.
-/
theorem scratch_step_code
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name}
    {nameOp frameOp : Structured.BasicOp}
    {promoteCode : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target)
    (hWF : plan.WellFormed)
    (hFresh : name ∉ realized)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan (name :: realized) =
        AllocationObserverRelation.currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hNameOp :
      Locals.StackOp.dup? (pending.length + 1) = some nameOp)
    (hFrameOp :
      Locals.StackOp.dup?
          ((pending.length + 1) + frameDepth + 2) =
        some frameOp)
    (hPromote :
      Locals.Ctx.swapRestoreUpTo? pending.length = some promoteCode) :
    ∃ written promoted final,
      Structured.ObserverSemantics.Code.run
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ])
          target =
        .ok written ∧
      Structured.ObserverSemantics.Code.run promoteCode written =
        .ok promoted ∧
      Structured.ObserverSemantics.Code.run
          [Structured.BasicInstr.op .pop] promoted =
        .ok final ∧
      Structured.ObserverSemantics.Code.run
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ] ++
            promoteCode ++
            [Structured.BasicInstr.op .pop])
          target =
        .ok final ∧
      AllocationObserverRelation.CalleeEntryRel contract plan
        (name :: realized) pending frameBase frameDepth frameWords
        source final ∧
      final.source.evm.stack.length + 1 =
        target.source.evm.stack.length ∧
      final.source.evm.toMachineState =
        target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          ((source.source.vars name).getD AllocationSupport.zeroWord) := by
  obtain ⟨value, values, suffix, hValue, hLookup, hTargetStack⟩ :=
    hRel.cons_parts
  have hValuesLength :
      values.length = pending.length := by
    simpa using Functions.Source.Store.lookupMany_length hLookup
  have hValueAt :
      target.source.evm.stack[pending.length]? = some value := by
    rw [hTargetStack]
    simp [hValuesLength]
  let afterValue :=
    AllocationObserverRelation.StateRel.pushTarget value target
  have hValueRun :
      Structured.ObserverSemantics.Code.run
          [Structured.BasicInstr.op nameOp] target =
        .ok afterValue := by
    exact
      AllocationObserverPreservation.ObserverCode.run_dup
        hNameOp hValueAt
  have hAfterValueRel :
      AllocationObserverRelation.ScratchStateRel contract plan realized
        ((pending.length + 1) + 1) frameBase frameDepth frameWords
        source afterValue := by
    simpa using hRel.state.push_target value
  have hAfterValueStack :
      afterValue.source.evm.stack =
        value :: target.source.evm.stack := by
    rfl
  have hRegion :
      reservation.containsRegion
        (AllocationObserverRelation.scratchAddress frameBase slot) 1 :=
    hRel.state.scratchAddress_reserved_of_bound hSlot hReservation
  obtain
      ⟨written, hStoreRun, hWrittenRel, hWrittenStack,
        hWrittenMachine⟩ :=
    AllocationObserverPreservation.Expr.scratchAssignTop_forward_live
      (stackOffset := pending.length + 1)
      hAfterValueRel hAfterValueStack hWF
      (fun other hOther => by
        simp at hOther
        exact hOther)
      hStackOrder (by simp) hLocation hSlot hReservation hRegion hFrameOp
  have hWrittenRel' :
      AllocationObserverRelation.ScratchStateRel contract plan
        (name :: realized) (pending.length + 1) frameBase
        frameDepth frameWords source written := by
    have hInsert :
        source.source.insert name value = source.source :=
      Locals.Source.State.insert_eq_of_apply_eq hValue
    simpa [hInsert] using hWrittenRel
  have hWrittenStack' :
      written.source.evm.stack =
        values.reverse ++ value :: suffix := by
    rw [hWrittenStack, hTargetStack]
  obtain
      ⟨promoted, hPromoteRun, hPromoteCursor,
        hPromoteStack, hPromoteShared, _hPromoteReturns⟩ :=
    AllocationObserverPreservation.ObserverCode.run_swapRestoreUpTo?
      hPromote (by simp [hValuesLength]) hWrittenStack'
  let final :=
    AllocationObserverRelation.StateRel.replaceStackBy
      1 (values.reverse ++ suffix) promoted
  have hPopRun :
      Structured.ObserverSemantics.Code.run
          [Structured.BasicInstr.op .pop] promoted =
        .ok final := by
    simpa [final] using
      AllocationObserverPreservation.ObserverCode.run_pop hPromoteStack
  have hFinalCursor : final.cursor = written.cursor := by
    rw [show final.cursor = promoted.cursor by
      simp [final, AllocationObserverRelation.StateRel.replaceStackBy,
        Simulation.ResourceReplay.State.withSource]]
    exact hPromoteCursor
  have hFinalShared :
      final.source.evm.toSharedState =
        written.source.evm.toSharedState := by
    rw [show
        final.source.evm.toSharedState =
          promoted.source.evm.toSharedState by
      simp [final, AllocationObserverRelation.StateRel.replaceStackBy,
        Simulation.ResourceReplay.State.withSource,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]]
    exact hPromoteShared
  have hFinalStack :
      final.source.evm.stack = values.reverse ++ suffix := by
    rfl
  have hFinalMachine :
      final.source.evm.toMachineState =
        target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          value := by
    calc
      final.source.evm.toMachineState =
          promoted.source.evm.toMachineState := by
            simp [final, AllocationObserverRelation.StateRel.replaceStackBy,
              Simulation.ResourceReplay.State.withSource,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
      _ = written.source.evm.toMachineState := by
        exact congrArg (fun state => state.toMachineState) hPromoteShared
      _ = target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          value := hWrittenMachine
  have hFinalRel :
      AllocationObserverRelation.CalleeEntryRel contract plan
        (name :: realized) pending frameBase frameDepth frameWords
        source final := by
    apply hRel.activate_scratch_after hLookup hTargetStack hWrittenRel'
    · exact hWrittenStack
    · exact hFinalCursor
    · exact hFinalShared
    · exact hFinalStack
  have hWholeStoreRun :
      Structured.ObserverSemantics.Code.run
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ])
          target =
        .ok written := by
    rw [AllocationObserverPreservation.ObserverCode.run_append, hValueRun]
    exact hStoreRun
  refine
    ⟨written, promoted, final, hWholeStoreRun, hPromoteRun,
      hPopRun, ?_, hFinalRel, ?_, ?_⟩
  let storeCode : Structured.Code :=
    [ Structured.BasicInstr.op frameOp,
      Structured.BasicInstr.push (AllocationSupport.slotOffset slot),
      Structured.BasicInstr.op .add,
      Structured.BasicInstr.op .mstore ]
  change
    Structured.ObserverSemantics.Code.run
        ((([Structured.BasicInstr.op nameOp] ++ storeCode) ++
            promoteCode) ++
          [Structured.BasicInstr.op .pop])
        target =
      .ok final
  rw [AllocationObserverPreservation.ObserverCode.run_append]
  change
    (Structured.ObserverSemantics.Code.run
        (([Structured.BasicInstr.op nameOp] ++ storeCode) ++ promoteCode)
        target).bind
      (Structured.ObserverSemantics.Code.run
        [Structured.BasicInstr.op .pop]) =
      .ok final
  rw [AllocationObserverPreservation.ObserverCode.run_append]
  change
    ((Structured.ObserverSemantics.Code.run
        ([Structured.BasicInstr.op nameOp] ++ storeCode) target).bind
      (Structured.ObserverSemantics.Code.run promoteCode)).bind
      (Structured.ObserverSemantics.Code.run
        [Structured.BasicInstr.op .pop]) =
      .ok final
  rw [AllocationObserverPreservation.ObserverCode.run_append, hValueRun]
  simp only [Except.bind]
  change
    ((Structured.ObserverSemantics.Code.run storeCode afterValue).bind
        (Structured.ObserverSemantics.Code.run promoteCode)).bind
      (Structured.ObserverSemantics.Code.run
        [Structured.BasicInstr.op .pop]) =
      .ok final
  rw [show
      Structured.ObserverSemantics.Code.run storeCode afterValue =
        .ok written by simpa [storeCode] using hStoreRun]
  simp only [Except.bind]
  rw [hPromoteRun]
  · exact hPopRun
  · rw [hFinalStack, hTargetStack]
    simp only [List.length_append, List.length_reverse,
      List.length_cons, hValuesLength]
    omega
  · simpa [hValue] using hFinalMachine

/--
Compile and evaluate one real scratch-parameter prelude step.

The opcode witnesses are constructed from source-facing stack-depth bounds,
and the resulting Structured block is the actual output of
`lowerScratchParam` followed by `Locals.Block.compileOpen`.
-/
theorem scratch_step_of_lowerScratchParam
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name}
    {ctx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {above suffix : Locals.Layout}
    {targetProgram : Structured.Program}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target)
    (hWF : plan.WellFormed)
    (hFresh : name ∉ realized)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan (name :: realized) =
        AllocationObserverRelation.currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hLayout :
      localsCtx.layout = above ++ name :: suffix)
    (hAboveLength : above.length = pending.length)
    (hAboveFresh : name ∉ above)
    (hSuffixFresh : name ∉ suffix)
    (hNameDepthBound : above.length + 1 ≤ 16)
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName
          (above ++ name :: suffix) =
        some ((pending.length + 1) + frameDepth + 1))
    (hFrameDepthBound :
      1 + ((pending.length + 1) + frameDepth + 1) ≤ 16) :
    ∃ compiled final,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerScratchParam ctx name slot
                (above ++ name :: suffix)).1 } =
        some
          (compiled, localsCtx.withLayout (above ++ suffix)) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram 4
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular final) ∧
      AllocationObserverRelation.CalleeEntryRel contract plan
        (name :: realized) pending frameBase frameDepth frameWords
        source final ∧
      final.source.evm.stack.length + 1 =
        target.source.evm.stack.length ∧
      final.source.evm.toMachineState =
        target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          ((source.source.vars name).getD AllocationSupport.zeroWord) := by
  obtain ⟨nameOp, hNameOp⟩ :=
    Locals.StackOp.exists_dup?_of_pos_of_le
      (depth := above.length + 1) (by omega) hNameDepthBound
  obtain ⟨frameOp, hFrameOp⟩ :=
    Locals.StackOp.exists_dup?_of_pos_of_le
      (depth := 1 + ((pending.length + 1) + frameDepth + 1))
      (by omega) hFrameDepthBound
  obtain ⟨promoteCode, hPromote⟩ :=
    Locals.Ctx.exists_swapRestoreUpTo?_of_le
      (depth := above.length) (by omega)
  have hCompile :=
    AllocationLowering.lowerScratchParam_compileOpen
      (ctx := ctx) (name := name) (slot := slot)
      (frameDepth := (pending.length + 1) + frameDepth + 1)
      (above := above) (suffix := suffix) (localsCtx := localsCtx)
      (nameOp := nameOp) (frameOp := frameOp)
      (promoteCode := promoteCode)
      hLayout hAboveFresh hSuffixFresh (by omega) hFrameDepth
      hNameOp hFrameOp hPromote
  have hNameOp' :
      Locals.StackOp.dup? (pending.length + 1) = some nameOp := by
    simpa [hAboveLength] using hNameOp
  have hFrameOp' :
      Locals.StackOp.dup?
          ((pending.length + 1) + frameDepth + 2) =
        some frameOp := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFrameOp
  have hPromote' :
      Locals.Ctx.swapRestoreUpTo? pending.length =
        some promoteCode := by
    simpa [hAboveLength] using hPromote
  obtain
      ⟨written, promoted, final, hStoreRun, hPromoteRun,
        hPopRun, _hWholeRun, hFinalRel, hStackLength, hFinalMachine⟩ :=
    scratch_step_code hRel hWF hFresh hLocation hStackOrder hSlot
      hReservation hNameOp' hFrameOp' hPromote'
  let compiled : Expressions.Block :=
    { stmts :=
        [ Expressions.Stmt.code
            ([Structured.BasicInstr.op nameOp] ++
              [ Structured.BasicInstr.op frameOp,
                Structured.BasicInstr.push
                  (AllocationSupport.slotOffset slot),
                Structured.BasicInstr.op .add,
                Structured.BasicInstr.op .mstore ]),
          Expressions.Stmt.code promoteCode,
          Expressions.Stmt.code [Structured.BasicInstr.op .pop] ] }
  refine
    ⟨compiled.stmts, final, by simpa [compiled] using hCompile, ?_,
      hFinalRel, hStackLength, ?_⟩
  change
    Structured.ObserverSemantics.Block.Eval targetProgram 4
      { stmts :=
          [ Structured.Stmt.code
              ([Structured.BasicInstr.op nameOp] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ]),
            Structured.Stmt.code promoteCode,
            Structured.Stmt.code [Structured.BasicInstr.op .pop] ] }
      target
      (Structured.EffectSemantics.Outcome.regular final)
  exact
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hStoreRun)
      (Structured.EffectSemantics.Block.Eval.cons_regular
        (Structured.EffectSemantics.Stmt.Eval.code hPromoteRun)
        (Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hPopRun)
          Structured.EffectSemantics.Block.Eval.nil))
  exact hFinalMachine

/--
Execute and compile the complete real parameter prelude described by the
allocation-owned entry context.

This theorem is recursive over `lowerParams` itself. Its context remains an
internal compiler invariant; the whole-function boundary must construct that
context from the mixed-allocation plan and successful lowering.
-/
theorem forward_of_context
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {globalFrameWords allocatorDepth frameBase frameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Structured.Program}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hContext :
      AllocationObserverContext.ParameterPreludeContext
        lowerCtx plan frameWords realized pending frameDepth localsCtx)
    (hRel :
      AllocationObserverRelation.CalleeEntryRel contract plan realized
        pending frameBase frameDepth frameWords source target)
    (hFrameDepth :
      frameDepth =
        (AllocationObserverRelation.currentStackOrder plan realized).length)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase
          (.scratch frameDepth frameWords)) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerParams lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (AllocationObserverRelation.currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ realized)).length ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length ∧
      AllocationObserverRelation.Frame.SuspendedEffect
        config allocatorDepth target finalTarget := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, frameDepth, 1,
          ?_, ?_, ?_, ?_, ?_, ?_,
          AllocationObserverRelation.Frame.SuspendedEffect.refl hReady⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel.finish
      · simpa using hFrameDepth
      · exact hStackLength
  | @stack _ _ _ _ name slot planDepth classification fresh location
      stackOrder tail =>
      have hNextRel :=
        hRel.activate_stack fresh location stackOrder
      have hNextOwned :
          AllocationObserverRelation.Frame.ActivationOwned
            config allocatorDepth frameBase
              (.scratch (frameDepth + 1) frameWords) := by
        cases hOwned with
        | scratch hDepth hWords =>
            exact .scratch hDepth hWords
      obtain
          ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
            hCompile, hFinalLayout, hEval, hFinalRel, hFinalDepth,
            hFinalStackLength, hFinalEffect⟩ :=
        forward_of_context tail hNextRel
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hStackLength hWF hReservation hConfig hReady hNextOwned
      refine
        ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, hEval, ?_, ?_, ?_, hFinalEffect⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
  | @scratch _ pending _ localsCtx name slot classification fresh location
      stackOrder slotBound layout aboveFresh suffixFresh nameDepthBound
      frameDepthLookup frameDepthBound tail =>
      let above : Locals.Layout :=
        (pending.map Prod.fst).reverse
      let suffix : Locals.Layout :=
        AllocationObserverRelation.currentStackOrder plan
            (name :: realized) ++
          [lowerCtx.frameName]
      have hLayout :
          localsCtx.layout = above ++ name :: suffix := by
        simpa [above, suffix, stackOrder] using layout
      have hSuffixFresh : name ∉ suffix := by
        simpa [suffix, stackOrder] using suffixFresh
      have hFrameDepthLookup :
          Locals.Layout.lookupDepth? lowerCtx.frameName
              (above ++ name :: suffix) =
            some ((pending.length + 1) + frameDepth + 1) := by
        simpa [above, suffix, stackOrder] using frameDepthLookup
      obtain
          ⟨headCompiled, midTarget, hHeadCompile, hHeadEval, hNextRel,
            hStepLength, hStepMachine⟩ :=
        scratch_step_of_lowerScratchParam
          (contract := contract) (transcript := transcript)
          (plan := plan) (realized := realized) (pending := pending)
          (frameBase := frameBase) (frameDepth := frameDepth)
          (frameWords := frameWords) (slot := slot)
          (source := source) (target := target)
          (name := name) (ctx := lowerCtx) (localsCtx := localsCtx)
          (above := above) (suffix := suffix)
          (targetProgram := targetProgram) (reservation := reservation)
          hRel hWF fresh location stackOrder slotBound hReservation
          hLayout (by simp [above]) (by simpa [above] using aboveFresh)
          hSuffixFresh (by simpa [above] using nameDepthBound)
          hFrameDepthLookup frameDepthBound
      have hAddressLt :
          AllocationObserverRelation.scratchAddress frameBase slot <
            EvmYul.UInt256.size := by
        have hEnd :
            AllocationObserverRelation.scratchAddress frameBase slot +
                MemoryContract.wordBytes ≤
              frameBase + MemoryContract.wordBytes * frameWords := by
          have hSucc : slot + 1 ≤ frameWords :=
            Nat.succ_le_iff.mpr slotBound
          calc
            AllocationObserverRelation.scratchAddress frameBase slot +
                MemoryContract.wordBytes =
              frameBase + MemoryContract.wordBytes * (slot + 1) := by
                simp [AllocationObserverRelation.scratchAddress,
                  Nat.mul_add, Nat.add_assoc]
            _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
                frameBase
        exact lt_of_lt_of_le
          (Nat.lt_add_of_pos_right
            (by decide : 0 < MemoryContract.wordBytes))
          (Nat.le_of_lt (hEnd.trans_lt hRel.state.frameNoWrap))
      have hAddressHost :
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes <
            USize.size := by
        have hSucc : slot + 1 ≤ frameWords :=
          Nat.succ_le_iff.mpr slotBound
        calc
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes =
            frameBase + MemoryContract.wordBytes * (slot + 1) := by
              simp [AllocationObserverRelation.scratchAddress,
                Nat.mul_add, Nat.add_assoc]
          _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
              frameBase
          _ < USize.size := hRel.state.frameHostAddressable
      have hStepEffect :
          AllocationObserverRelation.Frame.SuspendedEffect
            config allocatorDepth target midTarget :=
        hOwned.suspendedEffect_of_mstore
          hConfig hReady hStepMachine
          (EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt)
          hAddressHost
      have hMidStackLength :
          midTarget.source.evm.stack.length =
            (localsCtx.withLayout (above ++ suffix)).layout.length := by
        simp only [Locals.Ctx.withLayout]
        have hInitialLength :
            target.source.evm.stack.length =
              (above ++ name :: suffix).length := by
          rw [hStackLength, hLayout]
        simp only [List.length_append, List.length_cons] at hInitialLength
        simp only [List.length_append]
        omega
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalDepth, hFinalStackLength, hTailEffect⟩ :=
        forward_of_context tail hNextRel
          (by simpa [stackOrder] using hFrameDepth)
          (by
            simpa [above, suffix, List.append_assoc] using hMidStackLength)
          hWF hReservation hConfig hStepEffect.ready hOwned
      have hHeadCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (AllocationLowering.lowerScratchParam lowerCtx name slot
                    localsCtx.layout).1 } =
            some
              (headCompiled,
                localsCtx.withLayout (above ++ suffix)) := by
        simpa [hLayout] using hHeadCompile
      have hTailCompile' :
          Locals.Block.compileOpen
              (localsCtx.withLayout (above ++ suffix))
              { stmts :=
                  (AllocationLowering.lowerParams lowerCtx pending
                    (above ++ suffix)).1 } =
            some (tailCompiled, finalCtx) := by
        simpa [above, suffix, List.append_assoc] using hTailCompile
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile' hTailCompile'
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      have hErase :
          AllocationLowering.eraseName name
              (above ++ name :: suffix) =
            above ++ suffix :=
        AllocationLowering.eraseName_append_name aboveFresh hSuffixFresh
      refine
        ⟨headCompiled ++ tailCompiled, finalCtx, finalTarget,
          finalFrameDepth, fuel, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  (headCompiled ++ tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
      · exact hStepEffect.trans hTailEffect
termination_by pending.length

/--
Compile and evaluate the complete parameter prelude for an all-stack
activation.

The compiler emits no executable parameter code in this branch. The proof
still follows the real `lowerParams` recursion and derives each live-local
activation from the raw entry stack.
-/
theorem forward_stack_of_context
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Structured.Program}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    (hContext :
      AllocationObserverContext.ParameterPreludeContext
        lowerCtx plan frameWords realized pending frameDepth localsCtx)
    (hAllStack :
      ∀ binding ∈ pending,
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        realized pending frameBase .stack source target)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length) :
    ∃ compiled finalCtx finalTarget fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerParams lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        .stack source finalTarget ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length ∧
      finalTarget.source.evm.toMachineState =
        target.source.evm.toMachineState := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, 1, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel.finish
      · exact hStackLength
  | @stack _ _ _ _ name slot planDepth classification fresh location
      stackOrder tail =>
      have hNextRel := by
        simpa [AllocationObserverRelation.ActivationMode.afterStackDeclaration]
          using hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, fuel,
            hCompile, hFinalLayout, hEval, hFinalRel,
            hFinalStackLength, hFinalMachine⟩ :=
        forward_stack_of_context tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel hStackLength
      refine
        ⟨compiled, finalCtx, finalTarget, fuel,
          ?_, ?_, hEval, ?_, ?_, hFinalMachine⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · exact hFinalStackLength
  | @scratch _ pending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _layout _aboveFresh _suffixFresh
      _nameDepthBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent :=
        hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

end ParameterPrelude

namespace ReturnPrelude

/--
Compile and execute the complete real return-initialization prelude.

The source function store already contains zero for every named return, so the
compiler-only declarations and frame stores preserve the source state while
establishing the ordinary allocation relation for all returns.
-/
theorem forward_of_context
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {globalFrameWords allocatorDepth frameBase frameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Structured.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hContext :
      AllocationObserverContext.ReturnPreludeContext
        lowerCtx plan frameWords live pending frameDepth localsCtx)
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live 0
        frameBase frameDepth frameWords source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hFrameDepth :
      frameDepth =
        (AllocationObserverRelation.currentStackOrder plan live).length)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase
          (.scratch frameDepth frameWords)) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (AllocationObserverRelation.currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ live)).length ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length ∧
      AllocationObserverRelation.Frame.SuspendedEffect
        config allocatorDepth target finalTarget := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, frameDepth, 1,
          ?_, ?_, ?_, ?_, ?_, ?_,
          AllocationObserverRelation.Frame.SuspendedEffect.refl hReady⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel
      · simpa using hFrameDepth
      · exact hStackLength
  | @stack _ pending _ planDepth _ name slot classification fresh location
      stackOrder tail =>
      let pushed :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.ObserverSemantics.Code.run
              [Structured.BasicInstr.push AllocationSupport.zeroWord]
              target =
            .ok pushed :=
        AllocationObserverPreservation.ObserverCode.run_push
          AllocationSupport.zeroWord target
      have hPushedRel :
          AllocationObserverRelation.ScratchStateRel contract plan live 1
            frameBase frameDepth frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.source.evm.stack =
            AllocationSupport.zeroWord :: target.source.evm.stack := by
        rfl
      have hNameZero :
          source.source.vars name =
            some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          AllocationObserverRelation.ScratchStateRel contract plan
            (name :: live) 0 frameBase (frameDepth + 1) frameWords
            source pushed :=
        hPushedRel.declare_stack_live_existing hPushedStack
          (fun other hOther => by
            simp at hOther
            exact hOther)
            (by simp) location stackOrder hNameZero
      have hNextOwned :
          AllocationObserverRelation.Frame.ActivationOwned
            config allocatorDepth frameBase
              (.scratch (frameDepth + 1) frameWords) := by
        cases hOwned with
        | scratch hDepth hWords =>
            exact .scratch hDepth hWords
      have hNextStackLength :
          pushed.source.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      have hPushedMachine :
          pushed.source.evm.toMachineState =
            target.source.evm.toMachineState := by
        simp [pushed, AllocationObserverRelation.StateRel.pushTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hPushedReady :
          AllocationObserverRelation.Frame.AllocatorReady
            config allocatorDepth pushed :=
        hReady.of_machine_eq hPushedMachine
      have hHeadEffect :
          AllocationObserverRelation.Frame.SuspendedEffect
            config allocatorDepth target pushed :=
        AllocationObserverRelation.Frame.SuspendedEffect.of_allocatorEffect
          (AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
            hReady hPushedMachine)
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalDepth, hFinalStackLength, hFinalEffect⟩ :=
        forward_of_context tail hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hNextStackLength hWF hReservation hConfig hPushedReady hNextOwned
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadRun :
          Structured.ObserverSemantics.Code.run
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))
              target =
            .ok pushed := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hPushRun]
        rfl
      have hHeadEval :
          Structured.ObserverSemantics.Block.Eval targetProgram 2
              { stmts :=
                  [Structured.Stmt.code
                    ([Structured.BasicInstr.push
                        AllocationSupport.zeroWord] ++
                      Locals.bindLocals 0
                        (name :: localsCtx.layout))] }
              target
              (Structured.EffectSemantics.Outcome.regular pushed) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hHeadRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      refine
        ⟨[Expressions.Stmt.code
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))] ++
            tailCompiled,
          finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, ?_, ?_, ?_, ?_, hHeadEffect.trans hFinalEffect⟩
      · simpa [AllocationLowering.lowerReturns, classification] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  ([Expressions.Stmt.code
                      ([Structured.BasicInstr.push
                          AllocationSupport.zeroWord] ++
                        Locals.bindLocals 0
                          (name :: localsCtx.layout))] ++
                    tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
  | @scratch _ pending _ _ name slot classification fresh location
      stackOrder slotBound frameDepthLookup frameDepthBound tail =>
      obtain ⟨frameOp, hFrameOp⟩ :=
        Locals.StackOp.exists_dup?_of_pos_of_le
          (depth := 1 + (frameDepth + 1)) (by omega) frameDepthBound
      let pushed :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.ObserverSemantics.Code.run
              [Structured.BasicInstr.push AllocationSupport.zeroWord]
              target =
            .ok pushed :=
        AllocationObserverPreservation.ObserverCode.run_push
          AllocationSupport.zeroWord target
      have hPushedRel :
          AllocationObserverRelation.ScratchStateRel contract plan live 1
            frameBase frameDepth frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.source.evm.stack =
            AllocationSupport.zeroWord :: target.source.evm.stack := by
        rfl
      have hRegion :
          reservation.containsRegion
            (AllocationObserverRelation.scratchAddress frameBase slot) 1 :=
        hRel.scratchAddress_reserved_of_bound slotBound hReservation
      obtain
          ⟨midTarget, hStoreRun, hStoredRel, hStoredStack,
            hStoredMachine⟩ :=
        AllocationObserverPreservation.Expr.scratchAssignTop_forward_live
          (stackOffset := 0) hPushedRel hPushedStack hWF
          (fun other hOther => by
            simp at hOther
            exact hOther)
          stackOrder (by simp) location slotBound hReservation hRegion
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hFrameOp)
      have hAddressLt :
          AllocationObserverRelation.scratchAddress frameBase slot <
            EvmYul.UInt256.size := by
        have hEnd :
            AllocationObserverRelation.scratchAddress frameBase slot +
                MemoryContract.wordBytes ≤
              frameBase + MemoryContract.wordBytes * frameWords := by
          have hSucc : slot + 1 ≤ frameWords :=
            Nat.succ_le_iff.mpr slotBound
          calc
            AllocationObserverRelation.scratchAddress frameBase slot +
                MemoryContract.wordBytes =
              frameBase + MemoryContract.wordBytes * (slot + 1) := by
                simp [AllocationObserverRelation.scratchAddress,
                  Nat.mul_add, Nat.add_assoc]
            _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
                frameBase
        exact lt_of_lt_of_le
          (Nat.lt_add_of_pos_right
            (by decide : 0 < MemoryContract.wordBytes))
          (Nat.le_of_lt (hEnd.trans_lt hRel.frameNoWrap))
      have hAddressHost :
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes <
            USize.size := by
        have hSucc : slot + 1 ≤ frameWords :=
          Nat.succ_le_iff.mpr slotBound
        calc
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes =
            frameBase + MemoryContract.wordBytes * (slot + 1) := by
              simp [AllocationObserverRelation.scratchAddress,
                Nat.mul_add, Nat.add_assoc]
          _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
              frameBase
          _ < USize.size := hRel.frameHostAddressable
      have hStepEffect :
          AllocationObserverRelation.Frame.SuspendedEffect
            config allocatorDepth target midTarget :=
        hOwned.suspendedEffect_of_mstore
          hConfig hReady hStoredMachine
          (EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt)
          hAddressHost
      have hNameZero :
          source.source.vars name =
            some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          AllocationObserverRelation.ScratchStateRel contract plan
            (name :: live) 0 frameBase frameDepth frameWords
            source midTarget := by
        have hInsert :
            source.source.insert name AllocationSupport.zeroWord =
              source.source :=
          Locals.Source.State.insert_eq_of_apply_eq hNameZero
        simpa [hInsert] using hStoredRel
      have hNextStackLength :
          midTarget.source.evm.stack.length = localsCtx.layout.length := by
        rw [hStoredStack]
        exact hStackLength
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalDepth, hFinalStackLength, hTailEffect⟩ :=
        forward_of_context tail hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by simpa [stackOrder] using hFrameDepth)
          hNextStackLength hWF hReservation hConfig hStepEffect.ready hOwned
      have hHeadCompile :=
        AllocationLowering.lowerScratchReturn_compileOpen
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := frameDepth + 1) (localsCtx := localsCtx)
          (frameOp := frameOp) frameDepthLookup hFrameOp
      have hHeadRun :
          Structured.ObserverSemantics.Code.run
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ])
              target =
            .ok midTarget := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hPushRun]
        exact hStoreRun
      have hHeadEval :
          Structured.ObserverSemantics.Block.Eval targetProgram 2
              { stmts :=
                  [Structured.Stmt.code
                    ([Structured.BasicInstr.push
                        AllocationSupport.zeroWord] ++
                      [ Structured.BasicInstr.op frameOp,
                        Structured.BasicInstr.push
                          (AllocationSupport.slotOffset slot),
                        Structured.BasicInstr.op .add,
                        Structured.BasicInstr.op .mstore ])] }
              target
              (Structured.EffectSemantics.Outcome.regular midTarget) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hHeadRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      refine
        ⟨[Expressions.Stmt.code
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ])] ++
            tailCompiled,
          finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerReturns, classification] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  ([Expressions.Stmt.code
                      ([Structured.BasicInstr.push
                          AllocationSupport.zeroWord] ++
                        [ Structured.BasicInstr.op frameOp,
                          Structured.BasicInstr.push
                            (AllocationSupport.slotOffset slot),
                          Structured.BasicInstr.op .add,
                          Structured.BasicInstr.op .mstore ])] ++
                    tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
      · exact hStepEffect.trans hTailEffect
termination_by pending.length

/--
Compile and execute the complete return-initialization prelude for an
all-stack activation.
-/
theorem forward_stack_of_context
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Structured.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    (hContext :
      AllocationObserverContext.ReturnPreludeContext
        lowerCtx plan frameWords live pending frameDepth localsCtx)
    (hAllStack :
      ∀ binding ∈ pending,
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live 0
        frameBase .stack source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length) :
    ∃ compiled finalCtx finalTarget fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase
        .stack source finalTarget ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length ∧
      finalTarget.source.evm.toMachineState =
        target.source.evm.toMachineState := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, 1, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel
      · exact hStackLength
  | @stack _ pending _ planDepth _ name slot classification fresh location
      stackOrder tail =>
      let pushed :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.ObserverSemantics.Code.run
              [Structured.BasicInstr.push AllocationSupport.zeroWord]
              target =
            .ok pushed :=
        AllocationObserverPreservation.ObserverCode.run_push
          AllocationSupport.zeroWord target
      have hPushedRel :
          AllocationObserverRelation.ActivationStateRel contract plan live 1
            frameBase .stack source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.source.evm.stack =
            AllocationSupport.zeroWord :: target.source.evm.stack := by
        rfl
      have hNameZero :
          source.source.vars name =
            some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          AllocationObserverRelation.ActivationStateRel contract plan
            (name :: live) 0 frameBase .stack source pushed := by
        simpa [AllocationObserverRelation.ActivationMode.afterStackDeclaration]
          using hPushedRel.declare_stack_live_existing hPushedStack
            (fun other hOther => by
              simp at hOther
              exact hOther)
            (by simp) location stackOrder hNameZero
      have hNextStackLength :
          pushed.source.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      have hPushedMachine :
          pushed.source.evm.toMachineState =
            target.source.evm.toMachineState := by
        simp [pushed, AllocationObserverRelation.StateRel.pushTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      obtain
          ⟨tailCompiled, finalCtx, finalTarget,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalStackLength, hFinalMachine⟩ :=
        forward_stack_of_context tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          hNextStackLength
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadRun :
          Structured.ObserverSemantics.Code.run
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))
              target =
            .ok pushed := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hPushRun]
        rfl
      have hHeadEval :
          Structured.ObserverSemantics.Block.Eval targetProgram 2
              { stmts :=
                  [Structured.Stmt.code
                    ([Structured.BasicInstr.push
                        AllocationSupport.zeroWord] ++
                      Locals.bindLocals 0
                        (name :: localsCtx.layout))] }
              target
              (Structured.EffectSemantics.Outcome.regular pushed) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hHeadRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      refine
        ⟨[Expressions.Stmt.code
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))] ++
            tailCompiled,
          finalCtx, finalTarget, fuel, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerReturns, classification] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  ([Expressions.Stmt.code
                      ([Structured.BasicInstr.push
                          AllocationSupport.zeroWord] ++
                        Locals.bindLocals 0
                          (name :: localsCtx.layout))] ++
                    tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · exact hFinalStackLength
      · exact hFinalMachine.trans hPushedMachine
  | @scratch _ pending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent :=
        hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

end ReturnPrelude

namespace FunctionPrelude

/--
Scratch authorization is required exactly for frame-backed activations.
-/
def ScratchAuthorized
    (contract : MemoryContract.Contract) :
    AllocationObserverRelation.ActivationMode → Prop
  | .stack => True
  | .scratch _frameDepth _frameWords =>
      ∃ reservation,
        contract.scratch? = some reservation

theorem SelectedCallee.Prepared.scratchAuthorized
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      SelectedCallee.Artifact allocation program expressions name fn}
    (prepared : SelectedCallee.Prepared artifact)
    {config : AllocationObserverRelation.Frame.Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config) :
    ScratchAuthorized program.memoryContract prepared.mode := by
  by_cases hNeedsFrame : artifact.needsFrame = true
  · rw [prepared.mode_eq_scratch_of_needsFrame hNeedsFrame]
    obtain
        ⟨reservation, hReservation, _hAllocator, _hFirst, _hLimit,
          _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
      AllocationSupport.scratchFrameConfig?_sound hConfig
    exact ⟨reservation, hReservation⟩
  · have hNoFrame : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    rw [prepared.mode_eq_stack_of_noFrame hNoFrame]
    trivial

/--
The canonical Functions function-entry store supplies every source-facing
premise required by the allocation prelude: parameters retain the argument
values, returns are initialized to zero, and the complete body scope is
defined.
-/
theorem initialized_source_facts
    {transcript : Trace}
    {params returns : List Functions.Name}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {source : Functions.ObserverSemantics.State transcript}
    (hSignature : (returns ++ params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany params args
          Locals.Source.Store.empty =
        some paramStore)
    (hVars :
      source.source.vars =
        Functions.Source.Store.initReturns returns paramStore) :
    Functions.Source.Store.lookupMany params source.source.vars =
        some args ∧
      (∀ name, name ∈ returns →
        source.source.vars name = some AllocationSupport.zeroWord) ∧
      AllocationObserverRelation.LiveDefined
        (returns.reverse ++ params.reverse) source.source := by
  obtain ⟨hParams, hReturns⟩ :=
    Functions.Source.Store.initializedStore_lookupMany
      hSignature hInsert
  have hReturnNodup := (List.nodup_append.mp hSignature).1
  have hParams' :
      Functions.Source.Store.lookupMany params source.source.vars =
        some args := by
    simpa [hVars] using hParams
  have hReturns' :
      Functions.Source.Store.lookupMany returns source.source.vars =
        some (returns.map fun _name => AllocationSupport.zeroWord) := by
    simpa [hVars] using hReturns
  refine ⟨hParams', ?_, ?_⟩
  · intro name hName
    rw [hVars]
    exact
      Functions.Source.Store.initReturns_apply_of_mem
        hReturnNodup hName
  · exact
      (AllocationObserverRelation.LiveDefined.of_lookupMany
          (Functions.Source.Store.lookupMany_reverse hReturns')).append
        (AllocationObserverRelation.LiveDefined.of_lookupMany
          (Functions.Source.Store.lookupMany_reverse hParams'))

/--
Compile and execute the complete parameter/return prelude selected by a
checked function compiler artifact.

No generated code is accepted from the caller: both compilation phases are
recovered from `FunctionPreludeContext`, which is constructed by the real
validator, Functions lowerer, and Locals compiler.
-/
theorem forward_stack
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan}
    {frameWords frameBase : Nat}
    {slots : AllocationSupport.FunSlots}
    {entryCtx paramCtx returnCtx : Locals.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    (hContext :
      AllocationObserverContext.FunctionPreludeContext
        lowerCtx plan frameWords slots entryCtx paramCtx returnCtx .stack)
    (hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        [] slots.params frameBase .stack source target)
    (hEntryStackLength :
      target.source.evm.stack.length = entryCtx.layout.length)
    (hZero :
      ∀ name, name ∈ slots.returns.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord) :
    ∃ compiled finalTarget fuel,
      Locals.Block.compileOpen entryCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx slots.params
                entryCtx.layout).1 ++
              (AllocationLowering.lowerReturns lowerCtx slots.returns
                paramCtx.layout).1 } =
        some (compiled, returnCtx) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ActivationStateRel contract plan
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        0 frameBase .stack source finalTarget ∧
      finalTarget.source.evm.stack.length = returnCtx.layout.length := by
  cases hContext with
  | stack parameterSlots returnSlots signatureNodup frameFresh
      parameters returns
      parameterCompile returnCompile entryLayout parameterLayout bodyLayout =>
      obtain ⟨paramExpected, hParamExpected⟩ := parameterCompile
      obtain
          ⟨paramCompiled, paramFinalCtx, paramTarget, paramFuel,
            hParamCompile, _hParamLayout, hParamEval, hParamRel,
            hParamStackLength, _hParamMachine⟩ :=
        ParameterPrelude.forward_stack_of_context
          parameters parameterSlots hEntry hEntryStackLength
      rw [hParamExpected] at hParamCompile
      cases hParamCompile
      have hParamRel' :
          AllocationObserverRelation.ActivationStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase .stack
            source paramTarget := by
        simpa using hParamRel
      obtain ⟨returnExpected, hReturnExpected⟩ := returnCompile
      obtain
          ⟨returnCompiled, returnFinalCtx, returnTarget, returnFuel,
            hReturnCompile, _hReturnLayout, hReturnEval, hReturnRel,
            hReturnStackLength, _hReturnMachine⟩ :=
        ReturnPrelude.forward_stack_of_context
          returns returnSlots hParamRel' hZero hParamStackLength
      rw [hReturnExpected] at hReturnCompile
      cases hReturnCompile
      have hCompile :=
        Locals.Block.compileOpen_append hParamExpected hReturnExpected
      obtain ⟨fuel, hEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hParamEval hReturnEval
      refine
        ⟨paramExpected ++ returnExpected, returnTarget, fuel,
          hCompile, ?_, hReturnRel, hReturnStackLength⟩
      change
        Structured.ObserverSemantics.Block.Eval targetProgram fuel
          { stmts :=
              Expressions.StmtList.toStructured
                (paramExpected ++ returnExpected) }
          target
          (Structured.EffectSemantics.Outcome.regular returnTarget)
      rw [Expressions.StmtList.toStructured_append]
      exact hEval

/--
Package the all-stack function prelude as the ordinary activation invariant
consumed by recursive body preservation.
-/
theorem forward_stack_invariant
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan}
    {frameWords frameBase : Nat}
    {slots : AllocationSupport.FunSlots}
    {entryCtx paramCtx returnCtx : Locals.Ctx}
    {bodyState : AllocationLowering.State}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    (hContext :
      AllocationObserverContext.FunctionPreludeContext
        lowerCtx plan frameWords slots entryCtx paramCtx returnCtx .stack)
    (hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        [] slots.params frameBase .stack source target)
    (hEntryStackLength :
      target.source.evm.stack.length = entryCtx.layout.length)
    (hZero :
      ∀ name, name ∈ slots.returns.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hWF : plan.WellFormed)
    (hBodyEnv :
      bodyState.allocation.env =
        AllocationSupport.functionEnv slots)
    (hBodyLayout : bodyState.layout = returnCtx.layout)
    (hDefined :
      AllocationObserverRelation.LiveDefined
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        source.source) :
    ∃ compiled finalTarget fuel,
      Locals.Block.compileOpen entryCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx slots.params
                entryCtx.layout).1 ++
              (AllocationLowering.lowerReturns lowerCtx slots.returns
                paramCtx.layout).1 } =
        some (compiled, returnCtx) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx bodyState returnCtx plan
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        frameBase .stack source finalTarget := by
  obtain
      ⟨compiled, finalTarget, fuel, hCompile, hEval,
        hRel, hStackLength⟩ :=
    forward_stack hContext hEntry hEntryStackLength hZero
  exact
    ⟨compiled, finalTarget, fuel, hCompile, hEval,
      { compiler :=
          AllocationObserverContext.FunctionPreludeContext.bodyCompiler
            hContext hBodyEnv hBodyLayout hWF
        planWF := hWF
        defined := hDefined
        state := hRel
        stackLength := hStackLength }⟩

theorem forward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan}
    {globalFrameWords allocatorDepth frameWords frameBase : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {slots : AllocationSupport.FunSlots}
    {entryCtx paramCtx returnCtx : Locals.Ctx}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    (hContext :
      AllocationObserverContext.FunctionPreludeContext
        lowerCtx plan frameWords slots entryCtx paramCtx returnCtx mode)
    (hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        [] slots.params frameBase mode source target)
    (hEntryStackLength :
      target.source.evm.stack.length = entryCtx.layout.length)
    (hZero :
      ∀ name, name ∈ slots.returns.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hWF : plan.WellFormed)
    (hScratch : ScratchAuthorized contract mode)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase mode) :
    ∃ compiled finalTarget fuel,
      Locals.Block.compileOpen entryCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx slots.params
                entryCtx.layout).1 ++
              (AllocationLowering.lowerReturns lowerCtx slots.returns
                paramCtx.layout).1 } =
        some (compiled, returnCtx) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ActivationStateRel contract plan
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        0 frameBase
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length)
        source finalTarget ∧
      finalTarget.source.evm.stack.length = returnCtx.layout.length ∧
      AllocationObserverRelation.SameFrame mode
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length) ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target finalTarget := by
  cases hContext with
  | stack parameterSlots returnSlots signatureNodup frameFresh
      parameters returns
      parameterCompile returnCompile entryLayout parameterLayout bodyLayout =>
      obtain ⟨paramExpected, hParamExpected⟩ := parameterCompile
      obtain
          ⟨paramCompiled, paramFinalCtx, paramTarget, paramFuel,
            hParamCompile, _hParamLayout, hParamEval, hParamRel,
            hParamStackLength, hParamMachine⟩ :=
        ParameterPrelude.forward_stack_of_context
          parameters parameterSlots hEntry hEntryStackLength
      rw [hParamExpected] at hParamCompile
      cases hParamCompile
      have hParamRel' :
          AllocationObserverRelation.ActivationStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase .stack
            source paramTarget := by
        simpa using hParamRel
      obtain ⟨returnExpected, hReturnExpected⟩ := returnCompile
      obtain
          ⟨returnCompiled, returnFinalCtx, returnTarget, returnFuel,
            hReturnCompile, _hReturnLayout, hReturnEval, hReturnRel,
            hReturnStackLength, hReturnMachine⟩ :=
        ReturnPrelude.forward_stack_of_context
          returns returnSlots hParamRel' hZero hParamStackLength
      rw [hReturnExpected] at hReturnCompile
      cases hReturnCompile
      have hCompile :=
        Locals.Block.compileOpen_append hParamExpected hReturnExpected
      obtain ⟨fuel, hEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hParamEval hReturnEval
      have hMachine :
          returnTarget.source.evm.toMachineState =
            target.source.evm.toMachineState :=
        hReturnMachine.trans hParamMachine
      refine
        ⟨paramExpected ++ returnExpected, returnTarget, fuel,
          hCompile, ?_, ?_, hReturnStackLength,
          AllocationObserverRelation.SameFrame.stack,
          AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
            (AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
              hReady hMachine)⟩
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  (paramExpected ++ returnExpected) }
            target
            (Structured.EffectSemantics.Outcome.regular returnTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hEval
      · exact hReturnRel
  | scratch signatureNodup frameFresh parameters returns
      parameterCompile returnCompile
      entryLayout parameterLayout bodyLayout =>
      obtain ⟨reservation, hReservation⟩ := hScratch
      have hScratchEntry :=
        AllocationObserverRelation.ActivationCalleeEntryRel.to_scratch hEntry
      obtain ⟨paramExpected, hParamExpected⟩ := parameterCompile
      obtain
          ⟨paramCompiled, paramFinalCtx, paramTarget, paramFrameDepth,
            paramFuel, hParamCompile, _hParamLayout, hParamEval,
            hParamRel, hParamDepth, hParamStackLength, hParamEffect⟩ :=
        ParameterPrelude.forward_of_context
          parameters hScratchEntry
            (by
              simp [AllocationObserverRelation.currentStackOrder])
            hEntryStackLength hWF hReservation hConfig hReady hOwned
      rw [hParamExpected] at hParamCompile
      cases hParamCompile
      have hParamDepth' :
          paramFrameDepth =
            (AllocationObserverRelation.currentStackOrder plan
              (slots.params.map Prod.fst).reverse).length := by
        simpa using hParamDepth
      have hParamRel' :
          AllocationObserverRelation.ScratchStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase
            paramFrameDepth frameWords source paramTarget := by
        simpa using hParamRel
      have hParamRelExact :
          AllocationObserverRelation.ScratchStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase
            (AllocationObserverRelation.currentStackOrder plan
              (slots.params.map Prod.fst).reverse).length
            frameWords source paramTarget := by
        simpa [hParamDepth'] using hParamRel'
      have hParamOwned :
          AllocationObserverRelation.Frame.ActivationOwned
            config allocatorDepth frameBase
              (.scratch
                (AllocationObserverRelation.currentStackOrder plan
                  (slots.params.map Prod.fst).reverse).length
                frameWords) := by
        cases hOwned with
        | scratch hDepth hWords =>
            exact .scratch hDepth hWords
      obtain ⟨returnExpected, hReturnExpected⟩ := returnCompile
      obtain
          ⟨returnCompiled, returnFinalCtx, returnTarget, returnFrameDepth,
            returnFuel, hReturnCompile, _hReturnLayout, hReturnEval,
            hReturnRel, hReturnDepth, hReturnStackLength, hReturnEffect⟩ :=
        ReturnPrelude.forward_of_context
          returns hParamRelExact hZero rfl hParamStackLength
          hWF hReservation hConfig hParamEffect.ready hParamOwned
      rw [hReturnExpected] at hReturnCompile
      cases hReturnCompile
      have hCompile :=
        Locals.Block.compileOpen_append hParamExpected hReturnExpected
      obtain ⟨fuel, hEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hParamEval hReturnEval
      refine
        ⟨paramExpected ++ returnExpected, returnTarget, fuel,
          hCompile, ?_, ?_, hReturnStackLength, ?_,
          hParamEffect.trans hReturnEffect⟩
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  (paramExpected ++ returnExpected) }
            target
            (Structured.EffectSemantics.Outcome.regular returnTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hEval
      · exact
          AllocationObserverRelation.ActivationStateRel.scratch
            (by simpa [hReturnDepth] using hReturnRel)
      · exact
          AllocationObserverRelation.SameFrame.scratch
            0
            (AllocationObserverRelation.currentStackOrder plan
              ((slots.returns.map Prod.fst).reverse ++
                (slots.params.map Prod.fst).reverse)).length
            frameWords

/--
Compile and execute the complete function prelude, then package its exact
post-state with the compiler-derived body context as the standard recursive
statement invariant.
-/
theorem forward_invariant
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan}
    {globalFrameWords allocatorDepth frameWords frameBase : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {slots : AllocationSupport.FunSlots}
    {entryCtx paramCtx returnCtx : Locals.Ctx}
    {mode : AllocationObserverRelation.ActivationMode}
    {bodyState : AllocationLowering.State}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    (hContext :
      AllocationObserverContext.FunctionPreludeContext
        lowerCtx plan frameWords slots entryCtx paramCtx returnCtx mode)
    (hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        [] slots.params frameBase mode source target)
    (hEntryStackLength :
      target.source.evm.stack.length = entryCtx.layout.length)
    (hZero :
      ∀ name, name ∈ slots.returns.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hWF : plan.WellFormed)
    (hScratch : ScratchAuthorized contract mode)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase mode)
    (hBodyEnv :
      bodyState.allocation.env =
        AllocationSupport.functionEnv slots)
    (hBodyLayout : bodyState.layout = returnCtx.layout)
    (hDefined :
      AllocationObserverRelation.LiveDefined
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        source.source) :
    ∃ compiled finalTarget fuel,
      Locals.Block.compileOpen entryCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx slots.params
                entryCtx.layout).1 ++
              (AllocationLowering.lowerReturns lowerCtx slots.returns
                paramCtx.layout).1 } =
        some (compiled, returnCtx) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx bodyState returnCtx plan
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        frameBase
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length)
        source finalTarget ∧
      AllocationObserverRelation.SameFrame mode
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length) ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target finalTarget := by
  obtain
      ⟨compiled, finalTarget, fuel, hCompile, hEval, hRel,
        hStackLength, hSameFrame, hEffect⟩ :=
    forward hContext hEntry hEntryStackLength hZero hWF hScratch
      hConfig hReady hOwned
  refine
    ⟨compiled, finalTarget, fuel, hCompile, hEval, ?_, hSameFrame,
      hEffect⟩
  exact
    { activation :=
        { compiler :=
            AllocationObserverContext.FunctionPreludeContext.bodyCompiler
              hContext hBodyEnv hBodyLayout hWF
          planWF := hWF
          defined := hDefined
          state := hRel
          stackLength := hStackLength }
      allocator := hEffect.ready
      frame := hOwned.sameFrame hSameFrame }

end FunctionPrelude

namespace FunctionReturn

/--
Execute the regular-return epilogue for an all-stack function body.

This is the resource-neutral adjacent theorem used when ordinary allocation
selected no scratch frame for the callee.
-/
theorem forward_regular_stack
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live returns : List Locals.Name}
    {frameBase : Nat}
    {lowered : Locals.ExprSeq returns.length}
    {returnCode cleanup : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {values : List Word}
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase .stack
        source target)
    (hReturnsLive :
      ∀ name, name ∈ returns → name ∈ live)
    (hLookup :
      Functions.Source.Store.lookupMany returns source.source.vars =
        some values)
    (hLower :
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0 lowered =
        some returnCode)
    (hCleanup :
      localsCtx.cleanupToPreserving? returns.length 0 =
        some cleanup) :
    ∃ afterValues final,
      Structured.ObserverSemantics.Code.run returnCode target =
          .ok afterValues ∧
      Structured.ObserverSemantics.Code.run cleanup afterValues =
          .ok final ∧
      Structured.ObserverSemantics.Block.Eval targetProgram 3
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt returnCode ++ Locals.codeStmt cleanup) }
          target
          (Structured.EffectSemantics.Outcome.regular final) ∧
      final.source.evm.stack = values.reverse ∧
      source.cursor = final.cursor ∧
      Compiler.MemoryRelation.MachineRel contract
        source.source.shared.toMachineState
        final.source.evm.toMachineState ∧
      source.source.shared.toState =
        final.source.evm.toSharedState.toState ∧
      final.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  have hSafe :=
    AllocationObserverCleanup.ReturnValues.memorySafeEval
      (contract := contract) (transcript := transcript) hLookup
  have hScoped :=
    AllocationObserverCleanup.ReturnValues.returnExprsScoped hReturnsLive
  have hLowerSeq :=
    AllocationObserverCleanup.ReturnValues.lowerExprSeq hLower
  obtain ⟨afterValues, hValuesRun, hValuesRel⟩ :=
    AllocationObserverExpression.forwardExprSeq
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hSafe hInvariant.compiler hScoped hLowerSeq hCompile hInvariant.state
  have hValuesLength : values.length = returns.length :=
    Functions.Source.Store.lookupMany_length hLookup
  obtain
      ⟨final, hCleanupRun, hCleanupCursor, hFinalStack,
        hCleanupShared, _hCleanupReturns⟩ :=
    AllocationObserverCleanup.Preserving.forward_zero
      (values := values.reverse)
      (baseStack := target.source.evm.stack)
      hCleanup (by simpa [hValuesLength])
      hInvariant.stackLength hValuesRel.stack
  have hCleanupMachine :
      final.source.evm.toMachineState =
        afterValues.source.evm.toMachineState :=
    congrArg (fun state => state.toMachineState) hCleanupShared
  have hCleanupWorld :
      final.source.evm.toSharedState.toState =
        afterValues.source.evm.toSharedState.toState :=
    congrArg EvmYul.SharedState.toState hCleanupShared
  have hEval :
      Structured.ObserverSemantics.Block.Eval targetProgram 3
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt returnCode ++ Locals.codeStmt cleanup) }
          target
          (Structured.EffectSemantics.Outcome.regular final) := by
    change
      Structured.ObserverSemantics.Block.Eval targetProgram 3
        { stmts :=
            [Structured.Stmt.code returnCode,
              Structured.Stmt.code cleanup] }
        target
        (Structured.EffectSemantics.Outcome.regular final)
    exact
      Structured.EffectSemantics.Block.Eval.cons_regular
        (Structured.EffectSemantics.Stmt.Eval.code hValuesRun)
        (Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hCleanupRun)
          Structured.EffectSemantics.Block.Eval.nil)
  exact
    ⟨afterValues, final, hValuesRun, hCleanupRun, hEval, hFinalStack,
      hValuesRel.state.base.cursor.trans hCleanupCursor.symm,
      by simpa [hCleanupMachine] using hValuesRel.state.base.core.machine,
      hValuesRel.state.base.core.world.trans hCleanupWorld.symm,
      by simpa [hCleanupShared] using hValuesRel.state.activeNoWrap⟩

/--
Execute the compiler-owned regular-return epilogue from a completed function
body: evaluate the named return values and discard the complete callee layout
beneath them.
-/
theorem forward_regular
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live returns : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {lowered : Locals.ExprSeq returns.length}
    {returnCode cleanup : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target)
    (hReturnsLive :
      ∀ name, name ∈ returns → name ∈ live)
    (hLookup :
      Functions.Source.Store.lookupMany returns source.source.vars =
        some values)
    (hLower :
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0 lowered =
        some returnCode)
    (hCleanup :
      localsCtx.cleanupToPreserving? returns.length 0 =
        some cleanup) :
    ∃ afterValues final,
      Structured.ObserverSemantics.Code.run returnCode target =
          .ok afterValues ∧
      Structured.ObserverSemantics.Code.run cleanup afterValues =
          .ok final ∧
      Structured.ObserverSemantics.Block.Eval targetProgram 3
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt returnCode ++ Locals.codeStmt cleanup) }
          target
          (Structured.EffectSemantics.Outcome.regular final) ∧
      final.source.evm.stack = values.reverse ∧
      source.cursor = final.cursor ∧
      Compiler.MemoryRelation.MachineRel contract
        source.source.shared.toMachineState
        final.source.evm.toMachineState ∧
      source.source.shared.toState =
        final.source.evm.toSharedState.toState ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target final := by
  have hSafe :=
    AllocationObserverCleanup.ReturnValues.memorySafeEval
      (contract := contract) (transcript := transcript) hLookup
  have hScoped :=
    AllocationObserverCleanup.ReturnValues.returnExprsScoped hReturnsLive
  have hLowerSeq :=
    AllocationObserverCleanup.ReturnValues.lowerExprSeq hLower
  obtain ⟨afterValues, hValuesRun, hValuesRel, hValuesEffect⟩ :=
    AllocationObserverExpression.forwardExprSeqRuntime_with_effect
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hSafe hInvariant.activation.compiler hScoped hLowerSeq
      hCompile hInvariant.activation.state hInvariant.allocator
  have hValuesLength : values.length = returns.length :=
    Functions.Source.Store.lookupMany_length hLookup
  obtain
      ⟨final, hCleanupRun, hCleanupCursor, hFinalStack,
        hCleanupShared, _hCleanupReturns⟩ :=
    AllocationObserverCleanup.Preserving.forward_zero
      (values := values.reverse)
      (baseStack := target.source.evm.stack)
      hCleanup (by simpa [hValuesLength])
      hInvariant.activation.stackLength
      hValuesRel.stack
  have hCleanupMachine :
      final.source.evm.toMachineState =
        afterValues.source.evm.toMachineState :=
    congrArg (fun state => state.toMachineState) hCleanupShared
  have hCleanupWorld :
      final.source.evm.toSharedState.toState =
        afterValues.source.evm.toSharedState.toState :=
    congrArg EvmYul.SharedState.toState hCleanupShared
  have hCleanupEffect :
      AllocationObserverRelation.Frame.AllocatorEffect
        config allocatorDepth afterValues final :=
    AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
      hValuesEffect.ready hCleanupMachine
  have hEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode target final :=
    AllocationObserverRelation.Frame.ActivationEffect.of_allocatorEffect
      (hValuesEffect.trans hCleanupEffect)
  have hEval :
      Structured.ObserverSemantics.Block.Eval targetProgram 3
          { stmts :=
              Expressions.StmtList.toStructured
                (Locals.codeStmt returnCode ++ Locals.codeStmt cleanup) }
          target
          (Structured.EffectSemantics.Outcome.regular final) := by
    change
      Structured.ObserverSemantics.Block.Eval targetProgram 3
        { stmts :=
            [Structured.Stmt.code returnCode,
              Structured.Stmt.code cleanup] }
        target
        (Structured.EffectSemantics.Outcome.regular final)
    exact
      Structured.EffectSemantics.Block.Eval.cons_regular
        (Structured.EffectSemantics.Stmt.Eval.code hValuesRun)
        (Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hCleanupRun)
          Structured.EffectSemantics.Block.Eval.nil)
  exact
    ⟨afterValues, final, hValuesRun, hCleanupRun, hEval, hFinalStack,
      hValuesRel.state.base.cursor.trans hCleanupCursor.symm,
      by simpa [hCleanupMachine] using hValuesRel.state.base.core.machine,
      hValuesRel.state.base.core.world.trans hCleanupWorld.symm,
      hEffect⟩

end FunctionReturn

namespace RegularCallee

def protectedBound
    (calleeDepth : Nat)
    (entryMode : AllocationObserverRelation.ActivationMode) : Nat :=
  match entryMode with
  | .stack => calleeDepth + 1
  | .scratch _ _ => calleeDepth

theorem depth_le_protectedBound
    (calleeDepth : Nat)
    (entryMode : AllocationObserverRelation.ActivationMode) :
    calleeDepth ≤ protectedBound calleeDepth entryMode := by
  cases entryMode <;> simp [protectedBound]

/--
Compose the four compiler-owned phases of a regularly returning callee without
adding allocator bookkeeping.
-/
theorem compose_eval
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {proc : Structured.Proc}
    {markerBlock preludeBlock bodyBlock returnBlock : Structured.Block}
    {targetEntry targetBodyStart targetBodyFinal targetFinal :
      Structured.ObserverSemantics.State transcript}
    {markerFuel preludeFuel bodyFuel returnFuel : Nat}
    (hBodyShape :
      proc.body.stmts =
        markerBlock.stmts ++ preludeBlock.stmts ++
          bodyBlock.stmts ++ returnBlock.stmts)
    (hMarkers :
      Structured.ObserverSemantics.Block.Eval
        targetProgram markerFuel markerBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry))
    (hPrelude :
      Structured.ObserverSemantics.Block.Eval
        targetProgram preludeFuel preludeBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetBodyStart))
    (hBody :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyFuel bodyBlock targetBodyStart
        (Structured.EffectSemantics.Outcome.regular targetBodyFinal))
    (hReturn :
      Structured.ObserverSemantics.Block.Eval
        targetProgram returnFuel returnBlock targetBodyFinal
        (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval
        targetProgram fuel proc.body targetEntry
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  rcases markerBlock with ⟨markerStmts⟩
  rcases preludeBlock with ⟨preludeStmts⟩
  rcases bodyBlock with ⟨bodyStmts⟩
  rcases returnBlock with ⟨returnStmts⟩
  obtain ⟨markerPreludeFuel, hMarkerPrelude⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts) (right := preludeStmts)
      hMarkers hPrelude
  obtain ⟨throughBodyFuel, hThroughBody⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts ++ preludeStmts)
      (right := bodyStmts)
      hMarkerPrelude hBody
  obtain ⟨fuel, hEval⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := (markerStmts ++ preludeStmts) ++ bodyStmts)
      (right := returnStmts)
      hThroughBody hReturn
  refine ⟨fuel, ?_⟩
  cases hProcBody : proc.body with
  | mk procStmts =>
      have hProcStmts :
          procStmts =
            markerStmts ++ preludeStmts ++ bodyStmts ++ returnStmts := by
        simpa [hProcBody] using hBodyShape
      subst procStmts
      simpa [List.append_assoc] using hEval

/--
Compose a nonregular callee body with its compiler-owned entry phases; the
regular return epilogue is unreachable.
-/
theorem compose_nonregular_eval
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {proc : Structured.Proc}
    {markerBlock preludeBlock bodyBlock returnBlock : Structured.Block}
    {targetEntry targetBodyStart : Structured.ObserverSemantics.State transcript}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome (transcript := transcript)}
    {markerFuel preludeFuel bodyFuel : Nat}
    (hBodyShape :
      proc.body.stmts =
        markerBlock.stmts ++ preludeBlock.stmts ++
          bodyBlock.stmts ++ returnBlock.stmts)
    (hMarkers :
      Structured.ObserverSemantics.Block.Eval
        targetProgram markerFuel markerBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry))
    (hPrelude :
      Structured.ObserverSemantics.Block.Eval
        targetProgram preludeFuel preludeBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetBodyStart))
    (hBody :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyFuel bodyBlock targetBodyStart targetOutcome)
    (hNonregular : targetOutcome.mode ≠ .regular) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval
        targetProgram fuel proc.body targetEntry targetOutcome := by
  rcases markerBlock with ⟨markerStmts⟩
  rcases preludeBlock with ⟨preludeStmts⟩
  rcases bodyBlock with ⟨bodyStmts⟩
  rcases returnBlock with ⟨returnStmts⟩
  obtain ⟨markerPreludeFuel, hMarkerPrelude⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts) (right := preludeStmts)
      hMarkers hPrelude
  obtain ⟨throughBodyFuel, hThroughBody⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts ++ preludeStmts)
      (right := bodyStmts)
      hMarkerPrelude hBody
  have hEval :=
    Structured.EffectSemantics.Block.Eval.append_nonregular
      (right := returnStmts) hThroughBody hNonregular
  refine ⟨throughBodyFuel, ?_⟩
  cases hProcBody : proc.body with
  | mk procStmts =>
      have hProcStmts :
          procStmts =
            markerStmts ++ preludeStmts ++ bodyStmts ++ returnStmts := by
        simpa [hProcBody] using hBodyShape
      subst procStmts
      simpa [List.append_assoc] using hEval

/--
Compose the pass-owned phases of one regular callee body: metadata-only entry
markers, parameter/return prelude, recursively preserved source body, and the
regular-return epilogue.
-/
theorem compose
    {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {callerDepth calleeDepth : Nat}
    {entryMode bodyMode : AllocationObserverRelation.ActivationMode}
    {targetProgram : Structured.Program}
    {proc : Structured.Proc}
    {markerBlock preludeBlock bodyBlock returnBlock : Structured.Block}
    {targetEntry targetBodyStart targetBodyFinal targetFinal :
      Structured.ObserverSemantics.State transcript}
    {markerFuel preludeFuel bodyFuel returnFuel : Nat}
    (hBodyShape :
      proc.body.stmts =
        markerBlock.stmts ++ preludeBlock.stmts ++
          bodyBlock.stmts ++ returnBlock.stmts)
    (hMarkers :
      Structured.ObserverSemantics.Block.Eval
        targetProgram markerFuel markerBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry))
    (hPrelude :
      Structured.ObserverSemantics.Block.Eval
        targetProgram preludeFuel preludeBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetBodyStart))
    (hBody :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyFuel bodyBlock targetBodyStart
        (Structured.EffectSemantics.Outcome.regular targetBodyFinal))
    (hReturn :
      Structured.ObserverSemantics.Block.Eval
        targetProgram returnFuel returnBlock targetBodyFinal
        (Structured.EffectSemantics.Outcome.regular targetFinal))
    (hSame :
      AllocationObserverRelation.SameFrame entryMode bodyMode)
    (hPreludeEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config calleeDepth entryMode targetEntry targetBodyStart)
    (hBodyEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config calleeDepth bodyMode targetBodyStart targetBodyFinal)
    (hReturnEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config calleeDepth bodyMode targetBodyFinal targetFinal)
    (hProtectedBound :
      protectedBound calleeDepth entryMode =
        callerDepth + 1) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval
        targetProgram fuel proc.body targetEntry
        (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config calleeDepth (callerDepth + 1)
        targetEntry targetFinal := by
  rcases markerBlock with ⟨markerStmts⟩
  rcases preludeBlock with ⟨preludeStmts⟩
  rcases bodyBlock with ⟨bodyStmts⟩
  rcases returnBlock with ⟨returnStmts⟩
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram markerFuel { stmts := markerStmts } targetEntry
      (Structured.EffectSemantics.Outcome.regular targetEntry)
    at hMarkers
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram preludeFuel { stmts := preludeStmts } targetEntry
      (Structured.EffectSemantics.Outcome.regular targetBodyStart)
    at hPrelude
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram bodyFuel { stmts := bodyStmts } targetBodyStart
      (Structured.EffectSemantics.Outcome.regular targetBodyFinal)
    at hBody
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram returnFuel { stmts := returnStmts } targetBodyFinal
      (Structured.EffectSemantics.Outcome.regular targetFinal)
    at hReturn
  obtain ⟨markerPreludeFuel, hMarkerPrelude⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts) (right := preludeStmts)
      hMarkers hPrelude
  obtain ⟨throughBodyFuel, hThroughBody⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts ++ preludeStmts)
      (right := bodyStmts)
      hMarkerPrelude hBody
  obtain ⟨fuel, hEval⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left :=
        (markerStmts ++ preludeStmts) ++ bodyStmts)
      (right := returnStmts)
      hThroughBody hReturn
  refine ⟨fuel, ?_, ?_⟩
  · cases hProcBody : proc.body with
    | mk procStmts =>
        have hProcStmts :
            procStmts =
              markerStmts ++ preludeStmts ++ bodyStmts ++ returnStmts := by
          simpa [hProcBody] using hBodyShape
        subst procStmts
        simpa [List.append_assoc] using hEval
  · cases hSame with
    | stack =>
        change calleeDepth + 1 = callerDepth + 1 at hProtectedBound
        have hEffect :=
          AllocationObserverRelation.Frame.AllocatorEffect.trans
            (AllocationObserverRelation.Frame.AllocatorEffect.trans
              hPreludeEffect hBodyEffect)
            hReturnEffect
        exact hProtectedBound ▸
          AllocationObserverRelation.Frame.BoundedEffect.of_allocatorEffect
            hEffect
    | scratch =>
        change calleeDepth = callerDepth + 1 at hProtectedBound
        have hEffect :=
          AllocationObserverRelation.Frame.SuspendedEffect.trans
            (AllocationObserverRelation.Frame.SuspendedEffect.trans
              hPreludeEffect hBodyEffect)
            hReturnEffect
        exact hProtectedBound ▸
          AllocationObserverRelation.Frame.BoundedEffect.of_suspendedEffect
            hEffect

/--
Compose a callee whose source body reaches `leave`. The generated regular
return epilogue is unreachable, so the complete procedure body is obtained by
appending it after the checked nonregular body evaluation.
-/
theorem compose_leave
    {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {callerDepth calleeDepth : Nat}
    {entryMode bodyMode : AllocationObserverRelation.ActivationMode}
    {targetProgram : Structured.Program}
    {proc : Structured.Proc}
    {markerBlock preludeBlock bodyBlock returnBlock : Structured.Block}
    {targetEntry targetBodyStart targetBodyFinal :
      Structured.ObserverSemantics.State transcript}
    {markerFuel preludeFuel bodyFuel : Nat}
    (hBodyShape :
      proc.body.stmts =
        markerBlock.stmts ++ preludeBlock.stmts ++
          bodyBlock.stmts ++ returnBlock.stmts)
    (hMarkers :
      Structured.ObserverSemantics.Block.Eval
        targetProgram markerFuel markerBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry))
    (hPrelude :
      Structured.ObserverSemantics.Block.Eval
        targetProgram preludeFuel preludeBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetBodyStart))
    (hBody :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyFuel bodyBlock targetBodyStart
        (Structured.EffectSemantics.Outcome.leave targetBodyFinal))
    (hSame :
      AllocationObserverRelation.SameFrame entryMode bodyMode)
    (hPreludeEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config calleeDepth entryMode targetEntry targetBodyStart)
    (hBodyEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config calleeDepth bodyMode targetBodyStart targetBodyFinal)
    (hProtectedBound :
      protectedBound calleeDepth entryMode =
        callerDepth + 1) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval
        targetProgram fuel proc.body targetEntry
        (Structured.EffectSemantics.Outcome.leave targetBodyFinal) ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config calleeDepth (callerDepth + 1)
        targetEntry targetBodyFinal := by
  rcases markerBlock with ⟨markerStmts⟩
  rcases preludeBlock with ⟨preludeStmts⟩
  rcases bodyBlock with ⟨bodyStmts⟩
  rcases returnBlock with ⟨returnStmts⟩
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram markerFuel { stmts := markerStmts } targetEntry
      (Structured.EffectSemantics.Outcome.regular targetEntry)
    at hMarkers
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram preludeFuel { stmts := preludeStmts } targetEntry
      (Structured.EffectSemantics.Outcome.regular targetBodyStart)
    at hPrelude
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram bodyFuel { stmts := bodyStmts } targetBodyStart
      (Structured.EffectSemantics.Outcome.leave targetBodyFinal)
    at hBody
  obtain ⟨markerPreludeFuel, hMarkerPrelude⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts) (right := preludeStmts)
      hMarkers hPrelude
  obtain ⟨throughBodyFuel, hThroughBody⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts ++ preludeStmts)
      (right := bodyStmts)
      hMarkerPrelude hBody
  have hEval :=
    Structured.EffectSemantics.Block.Eval.append_nonregular
      (right := returnStmts) hThroughBody
      (by
        intro hMode
        cases hMode)
  refine ⟨throughBodyFuel, ?_, ?_⟩
  · cases hProcBody : proc.body with
    | mk procStmts =>
        have hProcStmts :
            procStmts =
              markerStmts ++ preludeStmts ++ bodyStmts ++ returnStmts := by
          simpa [hProcBody] using hBodyShape
        subst procStmts
        simpa [List.append_assoc] using hEval
  · cases hSame with
    | stack =>
        change calleeDepth + 1 = callerDepth + 1 at hProtectedBound
        have hEffect :=
          AllocationObserverRelation.Frame.AllocatorEffect.trans
            hPreludeEffect hBodyEffect
        exact hProtectedBound ▸
          AllocationObserverRelation.Frame.BoundedEffect.of_allocatorEffect
            hEffect
    | scratch =>
        change calleeDepth = callerDepth + 1 at hProtectedBound
        have hEffect :=
          AllocationObserverRelation.Frame.SuspendedEffect.trans
            hPreludeEffect hBodyEffect
        exact hProtectedBound ▸
          AllocationObserverRelation.Frame.BoundedEffect.of_suspendedEffect
            hEffect

/--
Compose a callee whose recursively preserved body has any nonregular outcome.
The generated regular-return epilogue is unreachable. This is the common
callee assembly theorem used by source `leave` and terminal halt paths.
-/
theorem compose_nonregular
    {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {callerDepth calleeDepth : Nat}
    {entryMode bodyMode : AllocationObserverRelation.ActivationMode}
    {targetProgram : Structured.Program}
    {proc : Structured.Proc}
    {markerBlock preludeBlock bodyBlock returnBlock : Structured.Block}
    {targetEntry targetBodyStart : Structured.ObserverSemantics.State transcript}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome (transcript := transcript)}
    {outcomeMode : Locals.Source.Mode}
    {markerFuel preludeFuel bodyFuel : Nat}
    (hBodyShape :
      proc.body.stmts =
        markerBlock.stmts ++ preludeBlock.stmts ++
          bodyBlock.stmts ++ returnBlock.stmts)
    (hMarkers :
      Structured.ObserverSemantics.Block.Eval
        targetProgram markerFuel markerBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry))
    (hPrelude :
      Structured.ObserverSemantics.Block.Eval
        targetProgram preludeFuel preludeBlock targetEntry
        (Structured.EffectSemantics.Outcome.regular targetBodyStart))
    (hBody :
      Structured.ObserverSemantics.Block.Eval
        targetProgram bodyFuel bodyBlock targetBodyStart targetOutcome)
    (hNonregular : targetOutcome.mode ≠ .regular)
    (hSame :
      AllocationObserverRelation.SameFrame entryMode bodyMode)
    (hPreludeEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config calleeDepth entryMode targetEntry targetBodyStart)
    (hBodyEffect :
      AllocationObserverRelation.Frame.OutcomeEffect
        config calleeDepth bodyMode targetBodyStart targetOutcome.state
        outcomeMode)
    (hProtectedBound :
      protectedBound calleeDepth entryMode =
        callerDepth + 1) :
    ∃ finalDepth fuel,
      Structured.ObserverSemantics.Block.Eval
        targetProgram fuel proc.body targetEntry targetOutcome ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config finalDepth (callerDepth + 1)
        targetEntry targetOutcome.state := by
  rcases markerBlock with ⟨markerStmts⟩
  rcases preludeBlock with ⟨preludeStmts⟩
  rcases bodyBlock with ⟨bodyStmts⟩
  rcases returnBlock with ⟨returnStmts⟩
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram markerFuel { stmts := markerStmts } targetEntry
      (Structured.EffectSemantics.Outcome.regular targetEntry)
    at hMarkers
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram preludeFuel { stmts := preludeStmts } targetEntry
      (Structured.EffectSemantics.Outcome.regular targetBodyStart)
    at hPrelude
  change
    Structured.ObserverSemantics.Block.Eval
      targetProgram bodyFuel { stmts := bodyStmts } targetBodyStart
      targetOutcome
    at hBody
  obtain ⟨markerPreludeFuel, hMarkerPrelude⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts) (right := preludeStmts)
      hMarkers hPrelude
  obtain ⟨throughBodyFuel, hThroughBody⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      (left := markerStmts ++ preludeStmts)
      (right := bodyStmts)
      hMarkerPrelude hBody
  have hEval :=
    Structured.EffectSemantics.Block.Eval.append_nonregular
      (right := returnStmts) hThroughBody hNonregular
  have hWholeEffect :
      AllocationObserverRelation.Frame.OutcomeEffect
        config calleeDepth entryMode targetEntry targetOutcome.state
        outcomeMode :=
    AllocationObserverRelation.Frame.OutcomeEffect.prepend_activation
      hPreludeEffect hSame hBodyEffect
  obtain ⟨finalDepth, hBoundedEffect⟩ :=
    hWholeEffect.exists_boundedEffect
  have hProtectedBound' :
      AllocationObserverRelation.Frame.activationProtectedBound
          calleeDepth entryMode =
        callerDepth + 1 := by
    simpa [protectedBound,
      AllocationObserverRelation.Frame.activationProtectedBound] using
      hProtectedBound
  refine ⟨finalDepth, throughBodyFuel, ?_, ?_⟩
  · cases hProcBody : proc.body with
    | mk procStmts =>
        have hProcStmts :
            procStmts =
              markerStmts ++ preludeStmts ++ bodyStmts ++ returnStmts := by
          simpa [hProcBody] using hBodyShape
        subst procStmts
        simpa [List.append_assoc] using hEval
  · exact hProtectedBound' ▸ hBoundedEffect

end RegularCallee

namespace ArgList

/--
Forward preservation for the actual list representation used by Functions
calls. Each source argument is lowered by `lowerExprList`, compiled as the
corresponding `exprSeqOfList`, and discharged by the shared expression theorem.
-/
theorem forward
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationExprResultRel
          contract plan live stackOffset frameBase args.length mode
          sourceFinal target targetFinal values := by
  induction hSafe generalizing lowered code stackOffset target with
  | nil =>
      have hLowered : lowered = [] := by
        simpa [AllocationLowering.lowerExprList] using hLower.symm
      subst lowered
      have hCode : code = [] := by
        simpa [AllocationLowering.exprSeqOfList,
          Locals.ExprSeq.compileCode] using hCompile.symm
      subst code
      exact
        ⟨target, rfl,
          AllocationObserverRelation.ActivationExprResultRel.nil hRel⟩
  | @cons arg rest source afterArg final value values hArg hRest ih =>
      cases hLowerArg :
          AllocationLowering.lowerExpr lowerCtx lowerState arg with
      | none =>
          simp [AllocationLowering.lowerExprList, hLowerArg] at hLower
      | some loweredArg =>
          cases hLowerRest :
              AllocationLowering.lowerExprList lowerCtx lowerState rest with
          | none =>
              simp [AllocationLowering.lowerExprList, hLowerArg,
                hLowerRest] at hLower
          | some loweredRest =>
              have hLowered :
                  lowered = loweredArg :: loweredRest := by
                simpa [AllocationLowering.lowerExprList, hLowerArg,
                  hLowerRest] using hLower.symm
              subst lowered
              rw [AllocationLowering.exprSeqOfList_compileCode_cons] at hCompile
              cases hArgCode :
                  Locals.Expr.compileCode localsCtx stackOffset loweredArg with
              | none =>
                  simp [hArgCode] at hCompile
              | some argCode =>
                  cases hRestCode :
                      Locals.ExprSeq.compileCode localsCtx (stackOffset + 1)
                        (AllocationLowering.exprSeqOfList loweredRest) with
                  | none =>
                      simp [hArgCode, hRestCode] at hCompile
                  | some restCode =>
                      have hCode : code = argCode ++ restCode := by
                        simpa [hArgCode, hRestCode] using hCompile.symm
                      subst code
                      have hArgScoped :
                          Functions.Scope.ExprScoped live arg :=
                        hScoped arg (by simp)
                      have hRestScoped :
                          ∀ candidate, candidate ∈ rest →
                            Functions.Scope.ExprScoped live candidate := by
                        intro candidate hMember
                        exact hScoped candidate (by simp [hMember])
                      obtain ⟨targetAfterArg, hArgRun, hArgRel⟩ :=
                        AllocationObserverExpression.forwardExpr hPrimitive
                          hArg hCtx hArgScoped hLowerArg hArgCode hRel
                      obtain ⟨targetFinal, hRestRun, hRestRel⟩ :=
                        ih hRestScoped hLowerRest hRestCode hArgRel.state
                      refine ⟨targetFinal, ?_, ?_⟩
                      · rw [
                          AllocationObserverPreservation.ObserverCode.run_append,
                          hArgRun]
                        exact hRestRun
                      · simpa [Nat.add_comm] using
                          AllocationObserverRelation.ActivationExprResultRel.append
                            hArgRel hRestRel

/--
Allocator-aware preservation for the actual Functions call-argument list.

This is the call-owner composition of the shared runtime expression theorem;
it retains the ordinary adjacent result relation and composes the complete
allocator effect, including suspended-caller prefix preservation.
-/
theorem forward_runtime
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationExprResultRel
          contract plan live stackOffset frameBase args.length mode
          sourceFinal target targetFinal values ∧
        AllocationObserverRelation.Frame.AllocatorEffect
          config allocatorDepth target targetFinal := by
  induction hSafe generalizing lowered code stackOffset target with
  | nil =>
      have hLowered : lowered = [] := by
        simpa [AllocationLowering.lowerExprList] using hLower.symm
      subst lowered
      have hCode : code = [] := by
        simpa [AllocationLowering.exprSeqOfList,
          Locals.ExprSeq.compileCode] using hCompile.symm
      subst code
      exact
        ⟨target, rfl,
          AllocationObserverRelation.ActivationExprResultRel.nil hRel,
          AllocationObserverRelation.Frame.AllocatorEffect.refl hReady⟩
  | @cons arg rest source afterArg final value values hArg hRest ih =>
      cases hLowerArg :
          AllocationLowering.lowerExpr lowerCtx lowerState arg with
      | none =>
          simp [AllocationLowering.lowerExprList, hLowerArg] at hLower
      | some loweredArg =>
          cases hLowerRest :
              AllocationLowering.lowerExprList lowerCtx lowerState rest with
          | none =>
              simp [AllocationLowering.lowerExprList, hLowerArg,
                hLowerRest] at hLower
          | some loweredRest =>
              have hLowered :
                  lowered = loweredArg :: loweredRest := by
                simpa [AllocationLowering.lowerExprList, hLowerArg,
                  hLowerRest] using hLower.symm
              subst lowered
              rw [AllocationLowering.exprSeqOfList_compileCode_cons] at hCompile
              cases hArgCode :
                  Locals.Expr.compileCode localsCtx stackOffset loweredArg with
              | none =>
                  simp [hArgCode] at hCompile
              | some argCode =>
                  cases hRestCode :
                      Locals.ExprSeq.compileCode localsCtx (stackOffset + 1)
                        (AllocationLowering.exprSeqOfList loweredRest) with
                  | none =>
                      simp [hArgCode, hRestCode] at hCompile
                  | some restCode =>
                      have hCode : code = argCode ++ restCode := by
                        simpa [hArgCode, hRestCode] using hCompile.symm
                      subst code
                      have hArgScoped :
                          Functions.Scope.ExprScoped live arg :=
                        hScoped arg (by simp)
                      have hRestScoped :
                          ∀ candidate, candidate ∈ rest →
                            Functions.Scope.ExprScoped live candidate := by
                        intro candidate hMember
                        exact hScoped candidate (by simp [hMember])
                      obtain
                          ⟨targetAfterArg, hArgRun, hArgRel, hArgEffect⟩ :=
                        AllocationObserverExpression.forwardExprRuntime_with_effect
                          hPrimitive hConfig hArg hCtx hArgScoped hLowerArg
                          hArgCode hRel hReady
                      obtain
                          ⟨targetFinal, hRestRun, hRestRel, hRestEffect⟩ :=
                        ih hRestScoped hLowerRest hRestCode hArgRel.state
                          hArgEffect.ready
                      refine
                        ⟨targetFinal, ?_, ?_,
                          hArgEffect.trans hRestEffect⟩
                      · rw [
                          AllocationObserverPreservation.ObserverCode.run_append,
                          hArgRun]
                        exact hRestRun
                      · simpa [Nat.add_comm] using
                          AllocationObserverRelation.ActivationExprResultRel.append
                            hArgRel hRestRel

/--
Deterministic target execution reflects the same canonical safe source
argument evaluation and result relation computed by `forward`.
-/
theorem backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Functions.Source.Effectful.ArgList.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        args source =
      .ok (sourceFinal, values) ∧
    AllocationObserverRelation.ActivationExprResultRel
      contract plan live stackOffset frameBase args.length mode
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forward hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

end ArgList

namespace PreparedArguments

/--
Prepare an all-stack callee call without introducing allocator bookkeeping.
-/
theorem stack_neutral
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceAfterArgs :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceAfterArgs values)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase .stack
        source target) :
    ∃ targetAfterArgs callerBase,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetAfterArgs ∧
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live 0 frameBase args.length .stack
        sourceAfterArgs target targetAfterArgs values ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan live 0 frameBase .stack sourceAfterArgs callerBase ∧
      targetAfterArgs.source.evm.stack =
        values.reverse ++ target.source.evm.stack ∧
      callerBase.source.evm.stack = target.source.evm.stack := by
  obtain ⟨targetAfterArgs, hRun, hResult⟩ :=
    ArgList.forward
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hSafe hInvariant.compiler hScoped hLower hCompile hInvariant.state
  let callerBase :=
    AllocationObserverRelation.StateRel.popTarget
      target.source.evm.stack targetAfterArgs
  exact
    ⟨targetAfterArgs, callerBase, hRun, hResult, hResult.restore_base,
      hResult.stack, rfl⟩

/--
Prepare an all-stack callee call from the real source argument evaluation and
compiled argument code.
-/
theorem stack
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceAfterArgs :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceAfterArgs values)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target) :
    ∃ targetAfterArgs callerBase,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetAfterArgs ∧
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live 0 frameBase args.length mode
        sourceAfterArgs target targetAfterArgs values ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan live 0 frameBase mode sourceAfterArgs callerBase ∧
      targetAfterArgs.source.evm.stack =
        values.reverse ++ target.source.evm.stack ∧
      callerBase.source.evm.stack = target.source.evm.stack ∧
      callerBase.source.evm.toMachineState =
        targetAfterArgs.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config allocatorDepth (allocatorDepth + 1)
        target targetAfterArgs := by
  obtain ⟨targetAfterArgs, hRun, hResult, hEffect⟩ :=
    ArgList.forward_runtime
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hSafe hInvariant.activation.compiler hScoped hLower hCompile
      hInvariant.activation.state hInvariant.allocator
  let callerBase :=
    AllocationObserverRelation.StateRel.popTarget
      target.source.evm.stack targetAfterArgs
  refine
    ⟨targetAfterArgs, callerBase, hRun, hResult, hResult.restore_base,
      hResult.stack, ?_, ?_,
      AllocationObserverRelation.Frame.BoundedEffect.of_allocatorEffect
        hEffect⟩
  · rfl
  · rfl

/--
Prepare a scratch callee call by executing the real frame-acquire sequence
before the ordinary source arguments.
-/
theorem scratch
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {argsCode : Structured.Code}
    {source sourceAfterArgs :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config allocatorDepth)
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceAfterArgs values)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 1
          (AllocationLowering.exprSeqOfList lowered) =
        some argsCode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source target) :
    ∃ targetAfterAcquire targetAfterArgs callerBase,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetAfterAcquire ∧
      Structured.ObserverSemantics.Code.run argsCode targetAfterAcquire =
        .ok targetAfterArgs ∧
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live 1 frameBase args.length mode
        sourceAfterArgs targetAfterAcquire targetAfterArgs values ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan live 0 frameBase mode sourceAfterArgs callerBase ∧
      targetAfterArgs.source.evm.stack =
        values.reverse ++
          EvmYul.UInt256.ofNat
              (AllocationObserverRelation.Frame.baseAt
                config allocatorDepth) ::
            target.source.evm.stack ∧
      callerBase.source.evm.stack = target.source.evm.stack ∧
      callerBase.source.evm.toMachineState =
        targetAfterArgs.source.evm.toMachineState ∧
      targetAfterAcquire.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt
              config allocatorDepth) ::
          target.source.evm.stack ∧
      AllocationObserverRelation.Frame.baseAt config allocatorDepth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetAfterAcquire.source.evm.activeWords.toNat *
          MemoryContract.wordBytes ∧
      AllocationObserverRelation.Frame.baseAt config allocatorDepth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetAfterAcquire.source.evm.toMachineState.memory.size ∧
      AllocationObserverRelation.Frame.TargetGrowth
        targetAfterAcquire targetAfterArgs ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config (allocatorDepth + 1) (allocatorDepth + 1)
        target targetAfterArgs := by
  obtain
      ⟨targetAfterAcquire, hAcquireRun, hAcquireRel, hAcquireReady,
        hAcquireStack, hFrameActive, hFrameAllocated, hAcquireEffect⟩ :=
    (by
      simpa using
        (AllocationObserverPreservation.Frame.scratchFrameAcquire_activation_forward
          (stackOffset := 0)
          hConfig hPositive hBudget hInvariant.allocator hInvariant.frame
          hInvariant.activation.state))
  obtain ⟨targetAfterArgs, hArgsRun, hResult, hArgsEffect⟩ :=
    ArgList.forward_runtime
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hConfig hSafe hInvariant.activation.compiler hScoped hLower hCompile
      hAcquireRel hAcquireReady
  let argsBase :=
    AllocationObserverRelation.StateRel.popTarget
      targetAfterAcquire.source.evm.stack targetAfterArgs
  have hArgsBase :
      AllocationObserverRelation.ActivationStateRel
        contract plan live 1 frameBase mode sourceAfterArgs argsBase :=
    hResult.restore_base
  let callerBase :=
    AllocationObserverRelation.StateRel.popTarget
      target.source.evm.stack targetAfterArgs
  have hCallStack :
      targetAfterArgs.source.evm.stack =
        values.reverse ++
          EvmYul.UInt256.ofNat
              (AllocationObserverRelation.Frame.baseAt
                config allocatorDepth) ::
            target.source.evm.stack := by
    rw [hResult.stack, hAcquireStack]
  have hCallerBase :
      AllocationObserverRelation.ActivationStateRel
        contract plan live 0 frameBase mode sourceAfterArgs callerBase := by
    apply hArgsBase.rebase_prefix_same_source
      (oldPrefix :=
        [EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config allocatorDepth)])
      (newPrefix := [])
      (baseStack := target.source.evm.stack)
      (targetFinal := callerBase)
    · rfl
    · rfl
    · change
        targetAfterAcquire.source.evm.stack =
          [EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt
              config allocatorDepth)] ++ target.source.evm.stack
      simpa using hAcquireStack
    · rfl
  have hArgsBounded :
      AllocationObserverRelation.Frame.BoundedEffect
        config (allocatorDepth + 1) (allocatorDepth + 1)
        targetAfterAcquire targetAfterArgs :=
    AllocationObserverRelation.Frame.BoundedEffect.weaken
      (by omega)
      (AllocationObserverRelation.Frame.BoundedEffect.of_allocatorEffect
        hArgsEffect)
  refine
    ⟨targetAfterAcquire, targetAfterArgs, callerBase,
      hAcquireRun, hArgsRun, hResult, hCallerBase, hCallStack,
      rfl, rfl, hAcquireStack, hFrameActive, hFrameAllocated,
      hArgsEffect.growth,
      hAcquireEffect.trans hArgsBounded⟩

end PreparedArguments

namespace ScratchFrame

/--
Execute the compiler-owned scratch-frame acquire sequence from a complete
caller runtime invariant. The result keeps the caller activation suspended
below the new frame pointer and advances only the shared allocator depth.
-/
theorem acquire_from_runtime
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {globalFrameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config depth lowerCtx lowerState localsCtx plan live
        frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan live 1 frameBase mode source targetFinal ∧
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) targetFinal ∧
      targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.toMachineState.memory.size ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config (depth + 1) (depth + 1) target targetFinal := by
  simpa using
    (AllocationObserverPreservation.Frame.scratchFrameAcquire_activation_forward
      (stackOffset := 0)
      hConfig hPositive hBudget hInvariant.allocator hInvariant.frame
      hInvariant.activation.state)

/--
Execute the compiler-owned scratch-frame release sequence and reconstruct the
complete caller runtime invariant at its previous allocator depth.
-/
theorem release_to_runtime
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {globalFrameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hActivation :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source target)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config depth frameBase mode) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameReleaseCode config) target =
        .ok targetFinal ∧
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config depth lowerCtx lowerState localsCtx plan live
        frameBase mode source targetFinal ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config depth (depth + 1) target targetFinal := by
  obtain
      ⟨targetFinal, hRun, hState, hFinalReady, hFinalOwned, hEffect⟩ :=
    AllocationObserverPreservation.Frame.scratchFrameRelease_activation_forward
      hConfig hBudget hReady hOwned hActivation.state
  have hFinalStack :=
    (AllocationObserverPreservation.Frame.scratchFrameRelease_backward
      hConfig hBudget hReady hActivation.state.base.core.machine hRun).1
  refine
    ⟨targetFinal, hRun,
      { activation :=
          { compiler := hActivation.compiler
            planWF := hActivation.planWF
            defined := hActivation.defined
            state := hState
            stackLength := ?_ }
        allocator := hFinalReady
        frame := hFinalOwned },
      hEffect⟩
  exact (congrArg List.length hFinalStack).trans hActivation.stackLength

end ScratchFrame

namespace CallTargets

def protectedBound
    (callerDepth : Nat)
    (mode : AllocationObserverRelation.ActivationMode) : Nat :=
  match mode with
  | .stack => callerDepth + 1
  | .scratch _ _ => callerDepth

private def PreservesBoundedEffect
    (contract : MemoryContract.Contract)
    (frameBase : Nat)
    (mode : AllocationObserverRelation.ActivationMode)
    {transcript : Trace}
    (before after : Structured.ObserverSemantics.State transcript) : Prop :=
  ∀ {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {callerDepth readyDepth : Nat},
    AllocationSupport.scratchFrameConfig?
        contract globalFrameWords =
      some config →
    AllocationObserverRelation.Frame.ActivationOwned
        config callerDepth frameBase mode →
    callerDepth ≤ readyDepth →
    AllocationObserverRelation.Frame.AllocatorReady
        config readyDepth before →
    AllocationObserverRelation.Frame.BoundedEffect
      config readyDepth (protectedBound callerDepth mode) before after

private theorem PreservesBoundedEffect.refl
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript} :
    PreservesBoundedEffect contract frameBase mode target target := by
  intro _globalFrameWords _config _callerDepth _readyDepth
    _hConfig _hOwned _hDepth hReady
  exact AllocationObserverRelation.Frame.BoundedEffect.refl hReady

private theorem PreservesBoundedEffect.trans
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {transcript : Trace}
    {before middle after :
      Structured.ObserverSemantics.State transcript}
    (hFirst :
      PreservesBoundedEffect contract frameBase mode before middle)
    (hSecond :
      PreservesBoundedEffect contract frameBase mode middle after) :
    PreservesBoundedEffect contract frameBase mode before after := by
  intro globalFrameWords config callerDepth readyDepth
    hConfig hOwned hDepth hReady
  exact
    (hFirst hConfig hOwned hDepth hReady).trans
      (hSecond hConfig hOwned hDepth
        (hFirst hConfig hOwned hDepth hReady).ready)

private theorem PreservesBoundedEffect.of_machine_eq
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {transcript : Trace}
    {before after :
      Structured.ObserverSemantics.State transcript}
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState) :
    PreservesBoundedEffect contract frameBase mode before after := by
  intro _globalFrameWords _config callerDepth readyDepth
    _hConfig _hOwned hDepth hReady
  apply AllocationObserverRelation.Frame.BoundedEffect.weaken
    (largerBound := readyDepth + 1)
  · cases mode <;> simp [protectedBound] <;> omega
  · exact
      AllocationObserverRelation.Frame.BoundedEffect.of_allocatorEffect
        (AllocationObserverRelation.Frame.AllocatorEffect.of_machine_eq
          hReady hMachine)

private theorem PreservesBoundedEffect.of_scratch_store
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {before after :
      Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word}
    (hRel :
      AllocationObserverRelation.ScratchStateRel
        contract plan live stackOffset frameBase frameDepth frameWords
        source before)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          value) :
    PreservesBoundedEffect contract frameBase
      (.scratch frameDepth frameWords) before after := by
  intro globalFrameWords config callerDepth readyDepth
    hConfig hOwned _hDepth hReady
  have hEndLt :=
    hRel.scratchAddress_end_lt_size hLive hLocation
  have hAddressLt :
      AllocationObserverRelation.scratchAddress frameBase slot <
        EvmYul.UInt256.size := by
    exact lt_of_lt_of_le
      (Nat.lt_add_of_pos_right
        (by decide : 0 < MemoryContract.wordBytes))
      (Nat.le_of_lt hEndLt)
  exact
    AllocationObserverRelation.Frame.BoundedEffect.of_mstore_above
      hReady hMachine
      (EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt)
      (hRel.scratchAddress_end_lt_hostSize hLive hLocation)
      (Or.inl (hOwned.allocatorCell_disjoint_scratchAddress hConfig))
      (fun hProtected =>
        hOwned.baseAt_le_scratchAddress_of_lt hProtected)

private theorem set_append_offset
    {α : Type} (above suffix : List α) (depth : Nat) (value : α) :
    (above ++ suffix).set (above.length + depth) value =
      above ++ suffix.set depth value := by
  induction above with
  | nil =>
      simp
  | cons head tail ih =>
      simp [Nat.succ_add, ih]

private theorem lookupDepth?_none_of_not_mem
    {name : Locals.Name} {layout : Locals.Layout}
    (hNotMem : name ∉ layout) :
    Locals.Layout.lookupDepth? name layout = none := by
  cases hLookup : Locals.Layout.lookupDepth? name layout with
  | none =>
      rfl
  | some depth =>
      exact False.elim
        (hNotMem (Locals.Layout.mem_of_lookupDepth?_eq_some hLookup))

private theorem stack_step
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase planDepth depth : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {layout : Locals.Layout}
    {name : Locals.Name} {value old : Word}
    {remaining rest : List Word}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {code : Structured.Code}
    (hCode :
      AllocationLowering.stackAssignTopCode?
          layout remaining.length name =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live (remaining.length + 1) frameBase mode
        source target)
    (hStack :
      target.source.evm.stack = value :: (remaining ++ rest))
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hCompileDepth :
      Locals.Layout.lookupDepth? name layout = some (depth + 1))
    (hDepthValid : mode.StackDepthValid depth)
    (hOld : source.source.vars name = some old) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live remaining.length frameBase mode
          (source.withSource (source.source.insert name value))
          targetFinal ∧
        targetFinal.source.evm.stack =
          remaining ++ rest.set depth value ∧
        targetFinal.source.evm.toMachineState =
          target.source.evm.toMachineState := by
  cases hSwap :
      Locals.StackOp.swap? (remaining.length + (depth + 1)) with
  | none =>
      simp [AllocationLowering.stackAssignTopCode?, hCompileDepth, hSwap]
        at hCode
  | some op =>
      simp [AllocationLowering.stackAssignTopCode?, hCompileDepth, hSwap]
        at hCode
      subst code
      have hOldTarget :=
        hRel.base.core.store.stack_at hLive hLocation hDepth
      rw [hStack, hOld] at hOldTarget
      have hRestGet :
          (remaining ++ rest)[remaining.length + depth]? = some old := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hOldTarget
      let targetFinal :=
        AllocationObserverRelation.StateRel.replaceStackBy 2
          ((remaining ++ rest).set (remaining.length + depth) value)
          target
      have hRun :
          Structured.ObserverSemantics.Code.run
              [.op op, .op .pop] target =
            .ok targetFinal := by
        simpa [targetFinal, Nat.add_assoc] using
          AllocationObserverPreservation.ObserverCode.run_swap_pop
            (by simpa [Nat.add_assoc] using hSwap)
            hRestGet hStack
      have hFinalRel :
          AllocationObserverRelation.ActivationStateRel
            contract plan live remaining.length frameBase mode
            (source.withSource (source.source.insert name value))
            targetFinal := by
        exact
          hRel.assign_stack_live_at hStack hLive hLocation hDepth
            hDepthValid hOld
      refine ⟨targetFinal, hRun, hFinalRel, ?_, ?_⟩
      · simp [targetFinal,
          AllocationObserverRelation.StateRel.replaceStackBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, set_append_offset]
      · simp [targetFinal,
          AllocationObserverRelation.StateRel.replaceStackBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

private theorem scratch_step
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase frameDepth frameWords slot : Nat}
    {name : Locals.Name} {value : Word}
    {remaining rest : List Word}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {code : Structured.Code}
    (hCode :
      AllocationLowering.scratchAssignTopCode?
          lowerCtx lowerState remaining.length slot =
        some code)
    (hRel :
      AllocationObserverRelation.ScratchStateRel
        contract plan live (remaining.length + 1) frameBase
        frameDepth frameWords source target)
    (hStack :
      target.source.evm.stack = value :: (remaining ++ rest))
    (hWF : plan.WellFormed)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hFrameDepth :
      Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
        some (frameDepth + 1)) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live remaining.length frameBase
          (.scratch frameDepth frameWords)
          (source.withSource (source.source.insert name value))
          targetFinal ∧
        targetFinal.source.evm.stack = remaining ++ rest ∧
        targetFinal.source.evm.toMachineState =
          target.source.evm.toMachineState.mstore
            (EvmYul.UInt256.ofNat
              (AllocationObserverRelation.scratchAddress frameBase slot))
            value := by
  have hStoreCode :
      AllocationSupport.storeTopSlotCode?
          (remaining.length + frameDepth + 1) slot =
        some code := by
    simpa [AllocationLowering.scratchAssignTopCode?,
      AllocationLowering.frameDepth?, hFrameDepth, Nat.add_assoc] using hCode
  have hSlotBound :=
    hRel.scratchBound name slot hLive hLocation
  obtain ⟨reservation, hReservation, _hFrameRegion⟩ :=
    hRel.frameReserved
  have hRegion :=
    hRel.scratchAddress_reserved_of_bound hSlotBound hReservation
  obtain
      ⟨targetFinal, hRun, hFinalRel, hFinalStack,
        hFinalMachine⟩ :=
    AllocationObserverPreservation.Expr.scratchAssignTop_forward_of_storeTopSlotCode?_live
        hRel hStack hWF
        (fun other hOther => Or.inr hOther)
        rfl hLive hLocation hSlotBound hReservation hRegion hStoreCode
  exact
    ⟨targetFinal, hRun, .scratch hFinalRel, hFinalStack, hFinalMachine⟩

/--
Execute the actual code emitted for assigning returned call values to source
targets.

The compiler and source semantics both process the already-reversed target and
value lists from left to right. Each step consumes exactly one temporary stack
value, updates either a stack local or its allocated scratch slot, and leaves
the remaining return prefix intact for the recursive step.
-/
private theorem forward_core
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store}
    {code : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hContext :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive :
      ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live values.length frameBase mode source target)
    (hStack :
      target.source.evm.stack = values ++ rest) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live 0 frameBase mode
          (source.withSource (source.source.withVars finalStore))
          targetFinal ∧
        targetFinal.source.evm.stack.length = rest.length ∧
        PreservesBoundedEffect contract frameBase mode target targetFinal := by
  induction names generalizing values code source target rest with
  | nil =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
          subst finalStore
          have hCode' : code = [] := by
            simpa [AllocationLowering.lowerCallTargetsCode?] using hCode.symm
          subst code
          exact
            ⟨target, rfl,
              by
                simpa [Locals.Source.State.withVars] using hRel,
              by simpa using congrArg List.length hStack,
              PreservesBoundedEffect.refl⟩
      | cons value values =>
          simp [Functions.Source.Store.assignMany] at hAssign
  | cons name names ih =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | cons value values =>
          have hNameLive : name ∈ live :=
            hLive name (by simp)
          have hTailLive :
              ∀ other, other ∈ names → other ∈ live := by
            intro other hOther
            exact hLive other (by simp [hOther])
          change
            (if source.source.vars.contains name then
                Functions.Source.Store.assignMany names values
                  (Locals.Source.Store.insert
                    source.source.vars name value)
              else none) =
              some finalStore at hAssign
          by_cases hContains :
              source.source.vars.contains name = true
          · simp [hContains] at hAssign
            cases hOld : source.source.vars name with
            | none =>
                simp [Locals.Source.Store.contains, hOld] at hContains
            | some old =>
                let sourceNext :=
                  source.withSource (source.source.insert name value)
                have hTailAssign :
                    Functions.Source.Store.assignMany names values
                        sourceNext.source.vars =
                      some finalStore := by
                  simpa [sourceNext, Locals.Source.State.insert] using hAssign
                have hHeadStack :
                    target.source.evm.stack =
                      value :: (values ++ rest) := by
                  simpa using hStack
                have hHeadRel :
                    AllocationObserverRelation.ActivationStateRel
                      contract plan live (values.length + 1) frameBase mode
                      source target := by
                  simpa using hRel
                obtain ⟨slot, hSlot⟩ :=
                  match hContext with
                  | .stack ctx => ctx.slot name hNameLive
                  | .scratch ctx => ctx.slot name hNameLive
                by_cases hStackSlot :
                    AllocationLowering.isStackSlot lowerCtx slot = true
                · cases hHeadCode :
                    AllocationLowering.stackAssignTopCode?
                      lowerState.layout values.length name with
                  | none =>
                      simp [AllocationLowering.lowerCallTargetsCode?,
                        hSlot, hStackSlot, hHeadCode] at hCode
                  | some headCode =>
                      cases hTailCode :
                          AllocationLowering.lowerCallTargetsCode?
                            lowerCtx lowerState names values.length with
                      | none =>
                          simp [AllocationLowering.lowerCallTargetsCode?,
                            hSlot, hStackSlot, hHeadCode, hTailCode] at hCode
                      | some tailCode =>
                          have hWholeCode :
                              code = headCode ++ tailCode := by
                            apply Option.some.inj
                            calc
                              some code =
                                  AllocationLowering.lowerCallTargetsCode?
                                    lowerCtx lowerState (name :: names)
                                      (values.length + 1) :=
                                hCode.symm
                              _ = some (headCode ++ tailCode) := by
                                simp [
                                  AllocationLowering.lowerCallTargetsCode?,
                                  hSlot, hStackSlot, hHeadCode, hTailCode]
                          subst code
                          cases hContext with
                          | stack stackContext =>
                              obtain
                                  ⟨planDepth, depth, hLocation, hCurrentDepth,
                                    hLowerDepth⟩ :=
                                stackContext.stack name slot hNameLive
                                  hSlot hStackSlot
                              obtain
                                  ⟨targetHead, hHeadRun, hHeadFinalRel,
                                    hHeadFinalStack, hHeadMachine⟩ :=
                                stack_step hHeadCode hHeadRel hHeadStack
                                  hNameLive hLocation hCurrentDepth hLowerDepth
                                  trivial hOld
                              obtain
                                  ⟨targetFinal, hTailRun, hFinalRel,
                                    hFinalStack, hTailPreserves⟩ :=
                                ih hTailLive hTailAssign hTailCode
                                  hHeadFinalRel hHeadFinalStack
                              refine
                                ⟨targetFinal, ?_, ?_, ?_, ?_⟩
                              · rw [
                                  AllocationObserverPreservation.ObserverCode.run_append,
                                  hHeadRun]
                                exact hTailRun
                              · simpa [sourceNext,
                                  Locals.Source.State.withVars] using hFinalRel
                              · simpa using hFinalStack
                              · exact
                                  PreservesBoundedEffect.trans
                                    (PreservesBoundedEffect.of_machine_eq
                                      hHeadMachine)
                                    hTailPreserves
                          | @scratch frameDepth frameWords scratchContext =>
                              obtain
                                  ⟨planDepth, depth, hLocation, hCurrentDepth,
                                    hLowerDepth⟩ :=
                                scratchContext.stack name slot hNameLive
                                  hSlot hStackSlot
                              have hDepthValid :
                                  AllocationObserverRelation.ActivationMode.StackDepthValid
                                    (.scratch frameDepth frameWords) depth :=
                                scratchContext.stack_depth_lt_frame
                                  hCurrentDepth
                              obtain
                                  ⟨targetHead, hHeadRun, hHeadFinalRel,
                                    hHeadFinalStack, hHeadMachine⟩ :=
                                stack_step hHeadCode hHeadRel hHeadStack
                                  hNameLive hLocation hCurrentDepth hLowerDepth
                                  hDepthValid hOld
                              obtain
                                  ⟨targetFinal, hTailRun, hFinalRel,
                                    hFinalStack, hTailPreserves⟩ :=
                                ih hTailLive hTailAssign hTailCode
                                  hHeadFinalRel hHeadFinalStack
                              refine
                                ⟨targetFinal, ?_, ?_, ?_, ?_⟩
                              · rw [
                                  AllocationObserverPreservation.ObserverCode.run_append,
                                  hHeadRun]
                                exact hTailRun
                              · simpa [sourceNext,
                                  Locals.Source.State.withVars] using hFinalRel
                              · simpa using hFinalStack
                              · exact
                                  PreservesBoundedEffect.trans
                                    (PreservesBoundedEffect.of_machine_eq
                                      hHeadMachine)
                                    hTailPreserves
                · have hScratchSlot :
                    AllocationLowering.isStackSlot lowerCtx slot = false :=
                    Bool.eq_false_of_not_eq_true hStackSlot
                  cases hContext with
                  | stack stackContext =>
                      have hFrameNone :
                          Locals.Layout.lookupDepth?
                              lowerCtx.frameName lowerState.layout =
                            none :=
                        lookupDepth?_none_of_not_mem
                          stackContext.frameAbsent
                      simp [AllocationLowering.lowerCallTargetsCode?,
                        hSlot, hScratchSlot,
                        AllocationLowering.scratchAssignTopCode?,
                        AllocationLowering.frameDepth?, hFrameNone] at hCode
                  | @scratch frameDepth frameWords scratchContext =>
                      cases hRel with
                      | scratch scratchRel =>
                          obtain ⟨hLocation, hFrameDepth⟩ :=
                            scratchContext.scratch name slot hNameLive
                              hSlot hScratchSlot
                          cases hHeadCode :
                              AllocationLowering.scratchAssignTopCode?
                                lowerCtx lowerState values.length slot with
                          | none =>
                              simp [AllocationLowering.lowerCallTargetsCode?,
                                hSlot, hScratchSlot, hHeadCode] at hCode
                          | some headCode =>
                              cases hTailCode :
                                  AllocationLowering.lowerCallTargetsCode?
                                    lowerCtx lowerState names values.length with
                              | none =>
                                  simp [
                                    AllocationLowering.lowerCallTargetsCode?,
                                    hSlot, hScratchSlot, hHeadCode, hTailCode]
                                    at hCode
                              | some tailCode =>
                                  have hWholeCode :
                                      code = headCode ++ tailCode := by
                                    apply Option.some.inj
                                    calc
                                      some code =
                                          AllocationLowering.lowerCallTargetsCode?
                                              lowerCtx lowerState
                                                (name :: names)
                                                (values.length + 1) :=
                                        hCode.symm
                                      _ = some (headCode ++ tailCode) := by
                                        simp [
                                          AllocationLowering.lowerCallTargetsCode?,
                                          hSlot, hScratchSlot, hHeadCode,
                                          hTailCode]
                                  subst code
                                  obtain
                                      ⟨targetHead, hHeadRun, hHeadFinalRel,
                                        hHeadFinalStack, hHeadMachine⟩ :=
                                    scratch_step hHeadCode scratchRel hHeadStack
                                      hWF hNameLive hLocation hFrameDepth
                                  obtain
                                      ⟨targetFinal, hTailRun, hFinalRel,
                                        hFinalStack, hTailPreserves⟩ :=
                                    ih hTailLive hTailAssign hTailCode
                                      hHeadFinalRel hHeadFinalStack
                                  refine
                                    ⟨targetFinal, ?_, ?_, hFinalStack, ?_⟩
                                  · rw [
                                      AllocationObserverPreservation.ObserverCode.run_append,
                                      hHeadRun]
                                    exact hTailRun
                                  · simpa [sourceNext,
                                      Locals.Source.State.withVars] using
                                      hFinalRel
                                  · exact
                                      PreservesBoundedEffect.trans
                                        (PreservesBoundedEffect.of_scratch_store
                                          scratchRel hNameLive hLocation
                                          hHeadMachine)
                                        hTailPreserves
          · simp [hContains] at hAssign

/--
Execute the actual code emitted for assigning returned call values to source
targets.
-/
theorem forward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store}
    {code : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hContext :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive :
      ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live values.length frameBase mode source target)
    (hStack :
      target.source.evm.stack = values ++ rest) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live 0 frameBase mode
          (source.withSource (source.source.withVars finalStore))
          targetFinal ∧
        targetFinal.source.evm.stack.length = rest.length := by
  obtain
      ⟨targetFinal, hRun, hFinalRel, hFinalStack, _hAllocator⟩ :=
    forward_core hContext hWF hLive hAssign hCode hRel hStack
  exact ⟨targetFinal, hRun, hFinalRel, hFinalStack⟩

/--
Allocator-aware returned-value assignment through the real call-target code.
-/
theorem forward_runtime
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store}
    {code : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hContext :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive :
      ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live values.length frameBase mode source target)
    (hStack :
      target.source.evm.stack = values ++ rest)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase mode)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live 0 frameBase mode
          (source.withSource (source.source.withVars finalStore))
          targetFinal ∧
        targetFinal.source.evm.stack.length = rest.length ∧
        AllocationObserverRelation.Frame.ActivationEffect
          config allocatorDepth mode target targetFinal := by
  obtain
      ⟨targetFinal, hRun, hFinalRel, hFinalStack, hAllocator⟩ :=
    forward_core hContext hWF hLive hAssign hCode hRel hStack
  have hBounded :=
    hAllocator hConfig hOwned (Nat.le_refl allocatorDepth) hReady
  exact
    ⟨targetFinal, hRun, hFinalRel, hFinalStack,
      AllocationObserverRelation.Frame.ActivationEffect.of_boundedEffect
        hBounded⟩

/--
Allocator-aware returned-value assignment while a deeper callee frame may
still be allocated. The result protects exactly the caller prefix permitted by
its activation mode and leaves allocator readiness at `readyDepth`.
-/
theorem forward_runtime_bounded
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {callerDepth readyDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store}
    {code : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hContext :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive :
      ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live values.length frameBase mode source target)
    (hStack :
      target.source.evm.stack = values ++ rest)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config callerDepth frameBase mode)
    (hDepth : callerDepth ≤ readyDepth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config readyDepth target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live 0 frameBase mode
          (source.withSource (source.source.withVars finalStore))
          targetFinal ∧
        targetFinal.source.evm.stack.length = rest.length ∧
        AllocationObserverRelation.Frame.BoundedEffect
          config readyDepth (protectedBound callerDepth mode)
          target targetFinal := by
  obtain
      ⟨targetFinal, hRun, hFinalRel, hFinalStack, hAllocator⟩ :=
    forward_core hContext hWF hLive hAssign hCode hRel hStack
  exact
    ⟨targetFinal, hRun, hFinalRel, hFinalStack,
      hAllocator hConfig hOwned hDepth hReady⟩

end CallTargets

namespace RegularCall

/--
Resume an all-stack caller after a regularly returning selected call and run
the real caller writeback code.
-/
theorem resume_and_writeback_stack
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {sourceAfterArgs sourceReturned :
      Functions.ObserverSemantics.State transcript}
    {callerTargetBase targetCallInput calleeFinal :
      Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {name : Structured.Name}
    {proc : Structured.Proc}
    {bodyFuel : Nat}
    {bodyMode : StructuredCall.ReturnMode}
    {callArgs callerStack returnValues : List Word}
    {targets : List Locals.Name}
    {returnStore : Locals.Source.Store}
    {stores : Structured.Code}
    (hCallerRel :
      AllocationObserverRelation.ActivationStateRel
        contract callerPlan callerLive 0 callerFrameBase .stack
        sourceAfterArgs callerTargetBase)
    (hCallerStack :
      callerTargetBase.source.evm.stack = callerStack)
    (hLookup :
      Structured.ProcList.lookup? name targetProgram.procs = some proc)
    (hCallStack :
      targetCallInput.source.evm.stack = callArgs ++ callerStack)
    (hCallArgsLength : callArgs.length = proc.argc)
    (hBody :
      Structured.ObserverSemantics.Block.Eval targetProgram bodyFuel proc.body
        (CalleeEntry.structuredState
          targetCallInput callArgs callerStack proc.retc)
        (bodyMode.outcome calleeFinal))
    (hReturnedStack :
      calleeFinal.source.evm.stack = returnValues.reverse)
    (hReturnedLength : returnValues.length = proc.retc)
    (hSourceCursor : sourceReturned.cursor = calleeFinal.cursor)
    (hSourceMachine :
      Compiler.MemoryRelation.MachineRel contract
        sourceReturned.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState)
    (hSourceWorld :
      sourceReturned.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState)
    (hCalleeActiveNoWrap :
      calleeFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hCallerContext :
      AllocationObserverContext.ActivationExprContext
        callerLowerCtx callerLowerState callerLocalsCtx
        callerPlan callerLive .stack)
    (hCallerWF : callerPlan.WellFormed)
    (hTargetsLive :
      ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.source.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState
          targets.reverse targets.length =
        some stores) :
    ∃ callFinal targetFinal,
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (bodyFuel + 1) (.call name) targetCallInput
        (Structured.EffectSemantics.Outcome.regular callFinal) ∧
      Structured.ObserverSemantics.Code.run stores callFinal =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationStateRel
        contract callerPlan callerLive 0 callerFrameBase .stack
        ((Functions.ObserverSemantics.stateModel transcript).withSource
          sourceReturned
          { shared := sourceReturned.source.shared
            vars := returnStore })
        targetFinal ∧
      targetFinal.source.evm.stack.length = callerStack.length := by
  obtain
      ⟨returned, callFinal, _hPop, hCallEval, hCallCursor,
        hCallFinalStack, hCallMachine, hCallWorld, _hCallReturns⟩ :=
    (by
      cases bodyMode with
      | regular =>
        exact
          StructuredCall.regular hLookup hCallStack hCallArgsLength hBody
            hReturnedStack (by simpa using hReturnedLength)
      | leave =>
        exact
          StructuredCall.leave hLookup hCallStack hCallArgsLength hBody
            hReturnedStack (by simpa using hReturnedLength))
  let callerReturned :=
    (Functions.ObserverSemantics.stateModel transcript).withSource
      sourceReturned
      { shared := sourceReturned.source.shared
        vars := sourceAfterArgs.source.vars }
  have hResumed :
      AllocationObserverRelation.ActivationStateRel
        contract callerPlan callerLive returnValues.reverse.length
        callerFrameBase .stack callerReturned callFinal := by
    apply AllocationObserverRelation.Frame.resume_after_call_stack hCallerRel
    · rfl
    · change sourceReturned.cursor = callFinal.cursor
      exact hSourceCursor.trans hCallCursor.symm
    · change
        Compiler.MemoryRelation.MachineRel contract
          sourceReturned.source.shared.toMachineState
          callFinal.source.evm.toMachineState
      simpa [hCallMachine] using hSourceMachine
    · change
        sourceReturned.source.shared.toState =
          callFinal.source.evm.toSharedState.toState
      simpa [hCallWorld] using hSourceWorld
    · simpa [hCallerStack] using hCallFinalStack
    · simpa [hCallMachine] using hCalleeActiveNoWrap
  have hAssignReverse :
      Functions.Source.Store.assignMany targets.reverse
          returnValues.reverse callerReturned.source.vars =
        some returnStore := by
    change
      Functions.Source.Store.assignMany targets.reverse
          returnValues.reverse sourceAfterArgs.source.vars =
        some returnStore
    exact
      Functions.Source.Store.assignMany_reverse_of_run
        hAssign hTargetsNodup
  have hStores' :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse
            returnValues.reverse.length =
        some stores := by
    simpa [Functions.Source.Store.assignMany_length hAssign] using hStores
  obtain ⟨targetFinal, hStoresRun, hFinalRel, hFinalStack⟩ :=
    CallTargets.forward hCallerContext hCallerWF
      (fun target hTarget =>
        hTargetsLive target (by simpa using hTarget))
      hAssignReverse hStores' hResumed hCallFinalStack
  refine
    ⟨callFinal, targetFinal, hCallEval, hStoresRun, ?_, hFinalStack⟩
  simpa [callerReturned, Locals.Source.State.withVars] using hFinalRel

/--
Complete a regular Structured call after the callee body has produced its
return vector, then assign those values through the real caller writeback code.

The caller relation is resumed from the callee's protected-prefix effect. The
result remains allocator-ready at `readyDepth`, allowing a scratch callee frame
to be released by the following compiler phase.
-/
theorem resume_and_writeback
    {contract : MemoryContract.Contract}
    {globalFrameWords callerDepth readyDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {transcript : Trace}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : AllocationObserverRelation.ActivationMode}
    {sourceAfterArgs sourceReturned :
      Functions.ObserverSemantics.State transcript}
    {callerTargetBase targetCallInput calleeFinal :
      Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {name : Structured.Name}
    {proc : Structured.Proc}
    {bodyFuel : Nat}
    {bodyMode : StructuredCall.ReturnMode}
    {callArgs callerStack returnValues : List Word}
    {targets : List Locals.Name}
    {returnStore : Locals.Source.Store}
    {stores : Structured.Code}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hCallerRel :
      AllocationObserverRelation.ActivationStateRel
        contract callerPlan callerLive 0 callerFrameBase callerMode
        sourceAfterArgs callerTargetBase)
    (hCallerOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config callerDepth callerFrameBase callerMode)
    (hCallerDepth : callerDepth ≤ readyDepth)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config callerDepth)
    (hCallerStack :
      callerTargetBase.source.evm.stack = callerStack)
    (hLookup :
      Structured.ProcList.lookup? name targetProgram.procs = some proc)
    (hCallStack :
      targetCallInput.source.evm.stack = callArgs ++ callerStack)
    (hCallArgsLength : callArgs.length = proc.argc)
    (hBody :
      Structured.ObserverSemantics.Block.Eval targetProgram bodyFuel proc.body
        (CalleeEntry.structuredState
          targetCallInput callArgs callerStack proc.retc)
        (bodyMode.outcome calleeFinal))
    (hReturnedStack :
      calleeFinal.source.evm.stack = returnValues.reverse)
    (hReturnedLength : returnValues.length = proc.retc)
    (hSourceCursor : sourceReturned.cursor = calleeFinal.cursor)
    (hSourceMachine :
      Compiler.MemoryRelation.MachineRel contract
        sourceReturned.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState)
    (hSourceWorld :
      sourceReturned.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState)
    (hCallEffect :
      AllocationObserverRelation.Frame.BoundedEffect
        config readyDepth (callerDepth + 1)
        callerTargetBase calleeFinal)
    (hCallerContext :
      AllocationObserverContext.ActivationExprContext
        callerLowerCtx callerLowerState callerLocalsCtx
        callerPlan callerLive callerMode)
    (hCallerWF : callerPlan.WellFormed)
    (hTargetsLive :
      ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.source.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState
          targets.reverse targets.length =
        some stores) :
    ∃ callFinal targetFinal,
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram (bodyFuel + 1) (.call name) targetCallInput
        (Structured.EffectSemantics.Outcome.regular callFinal) ∧
      Structured.ObserverSemantics.Code.run stores callFinal =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationStateRel
        contract callerPlan callerLive 0 callerFrameBase callerMode
        ((Functions.ObserverSemantics.stateModel transcript).withSource
          sourceReturned
          { shared := sourceReturned.source.shared
            vars := returnStore })
        targetFinal ∧
      targetFinal.source.evm.stack.length = callerStack.length ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config readyDepth
          (CallTargets.protectedBound callerDepth callerMode)
        callerTargetBase targetFinal := by
  obtain
      ⟨returned, callFinal, _hPop, hCallEval, hCallCursor,
        hCallFinalStack, hCallMachine, hCallWorld, _hCallReturns⟩ :=
    (by
      cases bodyMode with
      | regular =>
        exact
          StructuredCall.regular hLookup hCallStack hCallArgsLength hBody
            hReturnedStack (by simpa using hReturnedLength)
      | leave =>
        exact
          StructuredCall.leave hLookup hCallStack hCallArgsLength hBody
            hReturnedStack (by simpa using hReturnedLength))
  have hAttachEffect :
      AllocationObserverRelation.Frame.BoundedEffect
        config readyDepth (callerDepth + 1)
        calleeFinal callFinal :=
    AllocationObserverRelation.Frame.BoundedEffect.of_machine_eq
      hCallEffect.ready hCallMachine
  have hThroughCall :
      AllocationObserverRelation.Frame.BoundedEffect
        config readyDepth (callerDepth + 1)
        callerTargetBase callFinal :=
    hCallEffect.trans hAttachEffect
  have hProtected :
      AllocationObserverRelation.Frame.ProtectedPrefix
        config callerDepth callerTargetBase callFinal :=
    hThroughCall.prefixStable (by omega) hBudget
  let callerReturned :=
    (Functions.ObserverSemantics.stateModel transcript).withSource
      sourceReturned
      { shared := sourceReturned.source.shared
        vars := sourceAfterArgs.source.vars }
  have hResumed :
      AllocationObserverRelation.ActivationStateRel
        contract callerPlan callerLive returnValues.reverse.length
        callerFrameBase
        callerMode callerReturned callFinal := by
    apply AllocationObserverRelation.Frame.resume_after_call
      (returned := returnValues.reverse)
      hCallerRel hCallerOwned
    · rfl
    · change sourceReturned.cursor = callFinal.cursor
      exact hSourceCursor.trans hCallCursor.symm
    · change
        Compiler.MemoryRelation.MachineRel contract
          sourceReturned.source.shared.toMachineState
          callFinal.source.evm.toMachineState
      simpa [hCallMachine] using hSourceMachine
    · change
        sourceReturned.source.shared.toState =
          callFinal.source.evm.toSharedState.toState
      simpa [hCallWorld] using hSourceWorld
    · simpa [hCallerStack] using hCallFinalStack
    · exact hThroughCall.ready.activeNoWrap
    · exact hProtected
  have hAssignReverse :
      Functions.Source.Store.assignMany targets.reverse
          returnValues.reverse callerReturned.source.vars =
        some returnStore := by
    change
      Functions.Source.Store.assignMany targets.reverse
          returnValues.reverse sourceAfterArgs.source.vars =
        some returnStore
    exact
      Functions.Source.Store.assignMany_reverse_of_run
        hAssign hTargetsNodup
  have hStores' :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse
            returnValues.reverse.length =
        some stores := by
    simpa [Functions.Source.Store.assignMany_length hAssign] using hStores
  obtain
      ⟨targetFinal, hStoresRun, hFinalRel, hFinalStack,
        hWriteEffect⟩ :=
    CallTargets.forward_runtime_bounded
      hConfig hCallerContext hCallerWF
      (fun target hTarget =>
        hTargetsLive target (by simpa using hTarget))
      hAssignReverse hStores' hResumed hCallFinalStack
      hCallerOwned hCallerDepth hThroughCall.ready
  have hBound :
      CallTargets.protectedBound callerDepth callerMode ≤
        callerDepth + 1 := by
    cases callerMode <;> simp [CallTargets.protectedBound]
  have hBeforeWrite :=
    AllocationObserverRelation.Frame.BoundedEffect.weaken
      hBound hThroughCall
  have hEffect :=
    hBeforeWrite.trans hWriteEffect
  refine
    ⟨callFinal, targetFinal, hCallEval, hStoresRun, ?_, hFinalStack,
      hEffect⟩
  simpa [callerReturned, Locals.Source.State.withVars] using hFinalRel

/--
Package a completed call with no callee scratch frame as the caller's ordinary
runtime invariant and activation effect.
-/
theorem complete_without_release
    {contract : MemoryContract.Contract}
    {config : AllocationObserverRelation.Frame.Config}
    {allocatorDepth : Nat}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {targetInitial targetFinal :
      Structured.ObserverSemantics.State transcript}
    (hActivation :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source targetFinal)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase mode)
    (hEffect :
      AllocationObserverRelation.Frame.BoundedEffect
        config allocatorDepth
          (CallTargets.protectedBound allocatorDepth mode)
        targetInitial targetFinal) :
    AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source targetFinal ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode targetInitial targetFinal := by
  have hActivationEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode targetInitial targetFinal := by
    apply
      AllocationObserverRelation.Frame.ActivationEffect.of_boundedEffect
    simpa [CallTargets.protectedBound] using hEffect
  exact
    ⟨{ activation := hActivation
       allocator := hActivationEffect.ready
       frame := hOwned },
      hActivationEffect⟩

/--
Execute the real scratch-frame release after caller writeback and compose the
whole call back to the caller's allocator depth.
-/
theorem complete_with_release
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {targetInitial targetAssigned :
      Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config allocatorDepth)
    (hActivation :
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx lowerState localsCtx plan live frameBase mode
        source targetAssigned)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config allocatorDepth frameBase mode)
    (hEffect :
      AllocationObserverRelation.Frame.BoundedEffect
        config (allocatorDepth + 1)
          (CallTargets.protectedBound allocatorDepth mode)
        targetInitial targetAssigned) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameReleaseCode config)
          targetAssigned =
        .ok targetFinal ∧
      AllocationObserverContext.ActivationRuntimeInvariant
        contract config allocatorDepth lowerCtx lowerState localsCtx
        plan live frameBase mode source targetFinal ∧
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode targetInitial targetFinal := by
  obtain ⟨targetFinal, hRun, hFinalInvariant, hReleaseEffect⟩ :=
    ScratchFrame.release_to_runtime
      hConfig hBudget hActivation hEffect.ready hOwned
  have hBound :
      CallTargets.protectedBound allocatorDepth mode ≤
        allocatorDepth + 1 := by
    cases mode <;> simp [CallTargets.protectedBound]
  have hReleaseEffect' :=
    AllocationObserverRelation.Frame.BoundedEffect.weaken
      hBound hReleaseEffect
  have hWholeEffect :
      AllocationObserverRelation.Frame.BoundedEffect
        config allocatorDepth
          (CallTargets.protectedBound allocatorDepth mode)
        targetInitial targetFinal :=
    hEffect.trans hReleaseEffect'
  have hActivationEffect :
      AllocationObserverRelation.Frame.ActivationEffect
        config allocatorDepth mode targetInitial targetFinal := by
    apply
      AllocationObserverRelation.Frame.ActivationEffect.of_boundedEffect
    simpa [CallTargets.protectedBound] using hWholeEffect
  exact ⟨targetFinal, hRun, hFinalInvariant, hActivationEffect⟩

end RegularCall

end AllocationObserverCall
end Functions
end EvmCompiler
