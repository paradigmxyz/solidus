import EvmCompiler.Functions.AllocationInteractionCallArguments
import EvmCompiler.Functions.AllocationInteractionCursor
import EvmCompiler.Functions.AllocationInteractionScratchStore
import EvmCompiler.Locals.InteractionCleanupPreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionCursor
open AllocationInteractionRelation

namespace CallCompiler

/-- Decompose the existing call compiler into its adjacent runtime phases. -/
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
      AllocationSupport.lookupFun? functionName lowerCtx.functions = some fn ∧
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
              [.expr
                (Locals.Expr.code (results := 0)
                  (AllocationSupport.scratchFrameReleaseCode frameConfig))]
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
            [.call functionName] ++
            Locals.codeStmt stores ++ releaseCode ∧
        lowerFinal = lowerState ∧
        localsFinal = localsCtx := by
  obtain
      ⟨fn, loweredArgs, callArgs, stores, release,
        hLookup, hArgsLength, hTargetsLength, hTargets,
        hLowerArgs, hCallArgs, hStores, hRelease, rfl, rfl⟩ :=
    AllocationLowering.lowerStmt_call_components hLower
  cases hArgsCode :
      Locals.ExprSeq.compileCode localsCtx 0
        (AllocationLowering.exprSeqOfList callArgs) with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.Expr.compileCode, hArgsCode] at hCompile
  | some argsCode =>
      obtain ⟨releaseCode, hReleaseCode⟩ :
          ∃ releaseCode,
            Locals.Block.compileOpen localsCtx { stmts := release } =
              some (releaseCode, localsCtx) := by
        by_cases hFrame : functionName ∈ lowerCtx.frameFunctions
        · cases hConfig : lowerCtx.frameConfig? with
          | none =>
              simp [hFrame, hConfig] at hRelease
          | some frameConfig =>
              have hReleaseEq :
                  release =
                    [.expr
                      (Locals.Expr.code (results := 0)
                        (AllocationSupport.scratchFrameReleaseCode
                          frameConfig))] := by
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

namespace CalleeEntry

/-- Exact target state after argument splitting and return-frame creation. -/
def structuredState (target : Structured.RunState)
    (args callerStack : EvmYul.Stack Word) (retc : Nat) :
    Structured.RunState :=
  (target.withEVM { target.evm with stack := args }).pushReturn
    callerStack retc

/-- Exact source state installed by canonical function-body entry. -/
def sourceState (sourceAfterArgs : SourceState)
    (returns : List Functions.Name) (paramStore : Locals.Source.Store) :
    SourceState :=
  Functions.InteractionSemantics.stateModel.withSource sourceAfterArgs
    { shared := sourceAfterArgs.shared
      vars := Functions.Source.Store.initReturns returns paramStore }

/-- Canonical function-entry stores retain params and zero-initialize returns. -/
theorem initialized_source_facts
    {params returns : List Functions.Name}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {source : SourceState}
    (hSignature : (returns ++ params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany params args
          Locals.Source.Store.empty =
        some paramStore)
    (hVars :
      source.vars = Functions.Source.Store.initReturns returns paramStore) :
    Functions.Source.Store.lookupMany params source.vars = some args ∧
      (∀ name, name ∈ returns →
        source.vars name = some AllocationSupport.zeroWord) ∧
      LiveDefined (returns.reverse ++ params.reverse) source := by
  obtain ⟨hParams, hReturns⟩ :=
    Functions.Source.Store.initializedStore_lookupMany
      hSignature hInsert
  have hReturnNodup := (List.nodup_append.mp hSignature).1
  have hParams' :
      Functions.Source.Store.lookupMany params source.vars = some args := by
    simpa [hVars] using hParams
  have hReturns' :
      Functions.Source.Store.lookupMany returns source.vars =
        some (returns.map fun _name => AllocationSupport.zeroWord) := by
    simpa [hVars] using hReturns
  refine ⟨hParams', ?_, ?_⟩
  · intro name hName
    rw [hVars]
    exact Functions.Source.Store.initReturns_apply_of_mem
      hReturnNodup hName
  · exact
      (LiveDefined.of_lookupMany
        (Functions.Source.Store.lookupMany_reverse hReturns')).append
      (LiveDefined.of_lookupMany
        (Functions.Source.Store.lookupMany_reverse hParams'))

/-- Argument realization establishes an all-stack callee entry relation. -/
theorem stack_of_arguments
    {contract : MemoryContract.Contract}
    {callerPlan calleePlan : Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase calleeFrameBase : Nat}
    {callerMode : ActivationMode}
    {pending : List (Locals.Name × Nat)}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterArgs : TargetState}
    {args : List Word}
    {initialStore : Locals.Source.Store}
    {callerStack : EvmYul.Stack Word}
    {retc : Nat}
    (hArgs :
      ActivationExprResultRel contract callerPlan callerLive 0
        callerFrameBase args.length callerMode sourceAfterArgs targetInitial
        targetAfterArgs args)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) initialStore =
        some args) :
    ActivationCalleeEntryRel contract calleePlan [] pending calleeFrameBase
      .stack
      (Functions.InteractionSemantics.stateModel.withSource sourceAfterArgs
        { shared := sourceAfterArgs.shared, vars := initialStore })
      (structuredState targetAfterArgs args.reverse callerStack retc) := by
  have hBase := hArgs.state.state
  apply ActivationCalleeEntryRel.stack_empty (values := args) (suffix := [])
  · simpa [structuredState, Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Structured.RunState.withEVM, Structured.RunState.pushReturn] using
        hBase.machine
  · simpa [structuredState, Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Structured.RunState.withEVM, Structured.RunState.pushReturn] using
        hBase.world
  · simpa [structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hArgs.state.activeNoWrap
  · simpa [Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using hLookup
  · simp [structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn]

/-- The real target call splitter recovers exactly the compiled arguments. -/
theorem splitArgs_of_arguments
    {contract : MemoryContract.Contract}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerFrameBase argc : Nat} {callerMode : ActivationMode}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterArgs : TargetState}
    {args : List Word}
    (hArgs :
      ActivationExprResultRel contract callerPlan callerLive 0
        callerFrameBase args.length callerMode sourceAfterArgs targetInitial
        targetAfterArgs args)
    (hLength : args.length = argc) :
    Structured.StackFrame.splitArgs? argc targetAfterArgs.evm.stack =
      some (args.reverse, targetInitial.evm.stack) := by
  rw [hArgs.stack, ← hLength]
  simpa using
    Structured.StackFrame.splitArgs?_append args.reverse
      targetInitial.evm.stack

end CalleeEntry

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
        ([.code [.bindLocals 0 entryLayout]] ++
          if needsFrame then
            [.code
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)]
          else
            [],
         localsCtx) := by
  exact AllocationLowering.entryMarkers_compileOpen

theorem openRun_bindScratchBindingsCode
    (baseDepth : Nat)
    (bindings : List (Locals.Name × Nat))
    (target : Structured.RunState) :
    Structured.InteractionSemantics.Code.openRun
        (AllocationSupport.bindScratchBindingsCode baseDepth bindings)
        target =
      .done (.ok target) := by
  induction bindings with
  | nil =>
      rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      rw [show
        AllocationSupport.bindScratchBindingsCode baseDepth
            ((name, slot) :: rest) =
          [.bindScratch baseDepth name slot] ++
            AllocationSupport.bindScratchBindingsCode baseDepth rest by
        rfl]
      rw [Structured.InteractionSemantics.Code.openRun_append]
      change
        Simulation.Interaction.bind (.done (.ok target))
            (Structured.InteractionSemantics.Code.openRun
              (AllocationSupport.bindScratchBindingsCode baseDepth rest)) =
          .done (.ok target)
      exact ih

theorem openRun
    (entryLayout : Locals.Layout)
    (baseDepth : Nat)
    (scratchBindings : List (Locals.Name × Nat))
    (needsFrame : Bool)
    (target : Structured.RunState) :
    Structured.InteractionSemantics.Code.openRun
        ([.bindLocals 0 entryLayout] ++
          if needsFrame then
            AllocationSupport.bindScratchBindingsCode
              baseDepth scratchBindings
          else
            [])
        target =
      .done (.ok target) := by
  cases needsFrame with
  | false =>
      simpa using
        Locals.InteractionPreservation.Code.openRun_bindLocals
          0 entryLayout target
  | true =>
      rw [Structured.InteractionSemantics.Code.openRun_append]
      change
        Simulation.Interaction.bind (.done (.ok target))
            (Structured.InteractionSemantics.Code.openRun
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)) =
          .done (.ok target)
      exact
        openRun_bindScratchBindingsCode baseDepth scratchBindings target

end EntryMarkers

namespace ParameterPrelude

/-- Mixed-allocation placement shared by parameter-prelude construction. -/
inductive Placement
    (lowerCtx : AllocationLowering.Ctx)
    (plan : Locals.Allocation.Plan) (frameWords : Nat) :
    List Locals.Name → List (Locals.Name × Nat) → Prop where
  | nil {live : List Locals.Name} :
      Placement lowerCtx plan frameWords live []
  | stack
      {live : List Locals.Name}
      {pending : List (Locals.Name × Nat)}
      {name : Locals.Name} {slot planDepth : Nat}
      (classification :
        AllocationLowering.isStackSlot lowerCtx slot = true)
      (fresh : name ∉ live)
      (location : plan.location? name = some (.stack planDepth))
      (stackOrder :
        currentStackOrder plan (name :: live) =
          name :: currentStackOrder plan live)
      (tail : Placement lowerCtx plan frameWords (name :: live) pending) :
      Placement lowerCtx plan frameWords live ((name, slot) :: pending)
  | scratch
      {live : List Locals.Name}
      {pending : List (Locals.Name × Nat)}
      {name : Locals.Name} {slot : Nat}
      (classification :
        AllocationLowering.isStackSlot lowerCtx slot = false)
      (fresh : name ∉ live)
      (location : plan.location? name = some (.scratch slot))
      (stackOrder :
        currentStackOrder plan (name :: live) =
          currentStackOrder plan live)
      (slotBound : slot < frameWords)
      (tail : Placement lowerCtx plan frameWords (name :: live) pending) :
      Placement lowerCtx plan frameWords live ((name, slot) :: pending)

namespace Placement

theorem parameters_of_generated
    {lowerCtx : AllocationLowering.Ctx}
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : MixedAllocation.SlotSet}
    {state : AllocationSupport.CompileState}
    {added returns allParams processed pending : AllocationSupport.SlotEnv}
    (hCtxSlots : lowerCtx.stackSlots = stackSlots)
    (hEnv : state.env = added ++ returns ++ allParams)
    (hStateNodup : (state.env.map Prod.fst).Nodup)
    (hParamsNodup : (allParams.map Prod.fst).Nodup)
    (hSplit : allParams = processed ++ pending)
    (hWF :
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots returns.reverse ++
          MixedAllocation.stackEntries stackSlots allParams.reverse)
        state).WellFormed) :
    Placement lowerCtx
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots returns.reverse ++
          MixedAllocation.stackEntries stackSlots allParams.reverse)
        state)
      frameWords (processed.map Prod.fst).reverse pending := by
  induction pending generalizing processed with
  | nil =>
      exact .nil
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      have hCurrentMem : (name, slot) ∈ allParams := by
        rw [hSplit]
        simp
      have hStateMem : (name, slot) ∈ state.env := by
        rw [hEnv]
        simp [hCurrentMem]
      have hNamesNodup :
          (processed.map Prod.fst ++ name :: rest.map Prod.fst).Nodup := by
        simpa [hSplit, List.map_append] using hParamsNodup
      have hNameFresh : name ∉ (processed.map Prod.fst).reverse := by
        have hParts := List.nodup_append.mp hNamesNodup
        intro hName
        exact
          hParts.2.2 name (by simpa using hName) name (by simp) rfl
      have hTailSplit :
          allParams = (processed ++ [(name, slot)]) ++ rest := by
        rw [hSplit]
        simp [List.append_assoc]
      have hBefore :=
        MixedAllocation.allocationOfState_parameter_stack_filter
          (contract := contract) (frameWords := frameWords)
          (stackSlots := stackSlots) (state := state)
          (added := added) (returns := returns)
          (params := allParams) (processed := processed)
          (pending := (name, slot) :: rest)
          hEnv hStateNodup hSplit
      have hAfter :=
        MixedAllocation.allocationOfState_parameter_stack_filter
          (contract := contract) (frameWords := frameWords)
          (stackSlots := stackSlots) (state := state)
          (added := added) (returns := returns)
          (params := allParams)
          (processed := processed ++ [(name, slot)])
          (pending := rest)
          hEnv hStateNodup hTailSplit
      have hNextLive :
          ((processed ++ [(name, slot)]).map Prod.fst).reverse =
            name :: (processed.map Prod.fst).reverse := by
        simp [List.map_append]
      have hBeforeOrder :
          currentStackOrder
              (MixedAllocation.allocationOfState contract frameWords
                (MixedAllocation.stackEntries stackSlots added ++
                  MixedAllocation.stackEntries stackSlots returns.reverse ++
                  MixedAllocation.stackEntries stackSlots allParams.reverse)
                state)
              (processed.map Prod.fst).reverse =
            MixedAllocation.stackOrder stackSlots processed.reverse := by
        simpa [currentStackOrder] using hBefore
      have hAfterOrder :
          currentStackOrder
              (MixedAllocation.allocationOfState contract frameWords
                (MixedAllocation.stackEntries stackSlots added ++
                  MixedAllocation.stackEntries stackSlots returns.reverse ++
                  MixedAllocation.stackEntries stackSlots allParams.reverse)
                state)
              (name :: (processed.map Prod.fst).reverse) =
            MixedAllocation.stackOrder stackSlots
              (processed ++ [(name, slot)]).reverse := by
        rw [← hNextLive]
        simpa [currentStackOrder] using hAfter
      by_cases hStack : slot ∈ stackSlots
      · have hClassification :
            AllocationLowering.isStackSlot lowerCtx slot = true := by
          rw [AllocationLowering.isStackSlot_eq_true_iff, hCtxSlots]
          exact hStack
        have hEntry :
            (name, slot) ∈
              MixedAllocation.stackEntries stackSlots added ++
                MixedAllocation.stackEntries stackSlots returns.reverse ++
                MixedAllocation.stackEntries stackSlots allParams.reverse := by
          simp only [List.mem_append]
          exact
            Or.inr
              (MixedAllocation.mem_stackEntries_iff.mpr
                ⟨by simpa using hCurrentMem, hStack⟩)
        obtain ⟨planDepth, hLocation⟩ :=
          MixedAllocation.allocationOfState_location_stack_of_entry
            hStateNodup hStateMem hEntry
        have hStackOrder :
            currentStackOrder
                (MixedAllocation.allocationOfState contract frameWords
                  (MixedAllocation.stackEntries stackSlots added ++
                    MixedAllocation.stackEntries stackSlots returns.reverse ++
                    MixedAllocation.stackEntries stackSlots allParams.reverse)
                  state)
                (name :: (processed.map Prod.fst).reverse) =
              name ::
                currentStackOrder
                  (MixedAllocation.allocationOfState contract frameWords
                    (MixedAllocation.stackEntries stackSlots added ++
                      MixedAllocation.stackEntries stackSlots returns.reverse ++
                      MixedAllocation.stackEntries stackSlots allParams.reverse)
                    state)
                  (processed.map Prod.fst).reverse := by
          rw [hAfterOrder, hBeforeOrder, List.reverse_append,
            MixedAllocation.stackOrder_append]
          simp [MixedAllocation.stackOrder,
            MixedAllocation.stackEntries, hStack]
        exact
          .stack hClassification hNameFresh hLocation hStackOrder
            (by simpa [List.map_append] using ih hTailSplit)
      · have hClassification :
            AllocationLowering.isStackSlot lowerCtx slot = false := by
          rw [AllocationLowering.isStackSlot_eq_false_iff, hCtxSlots]
          exact hStack
        have hNotEntry :
            (name, slot) ∉
              MixedAllocation.stackEntries stackSlots added ++
                MixedAllocation.stackEntries stackSlots returns.reverse ++
                MixedAllocation.stackEntries stackSlots allParams.reverse := by
          simp only [List.mem_append, not_or]
          exact
            ⟨⟨MixedAllocation.not_mem_stackEntries_of_slot_not_mem hStack,
                MixedAllocation.not_mem_stackEntries_of_slot_not_mem hStack⟩,
              MixedAllocation.not_mem_stackEntries_of_slot_not_mem hStack⟩
        have hLocation :=
          MixedAllocation.allocationOfState_location_scratch_of_not_entry
            (contract := contract) (frameWords := frameWords)
            hStateNodup hStateMem hNotEntry
        have hSlotBound :=
          MixedAllocation.allocationOfState_scratch_bound_of_wellFormed
            hWF hLocation
        have hStackOrder :
            currentStackOrder
                (MixedAllocation.allocationOfState contract frameWords
                  (MixedAllocation.stackEntries stackSlots added ++
                    MixedAllocation.stackEntries stackSlots returns.reverse ++
                    MixedAllocation.stackEntries stackSlots allParams.reverse)
                  state)
                (name :: (processed.map Prod.fst).reverse) =
              currentStackOrder
                (MixedAllocation.allocationOfState contract frameWords
                  (MixedAllocation.stackEntries stackSlots added ++
                    MixedAllocation.stackEntries stackSlots returns.reverse ++
                    MixedAllocation.stackEntries stackSlots allParams.reverse)
                  state)
                (processed.map Prod.fst).reverse := by
          rw [hAfterOrder, hBeforeOrder, List.reverse_append,
            MixedAllocation.stackOrder_append]
          simp [MixedAllocation.stackOrder,
            MixedAllocation.stackEntries, hStack]
        exact
          .scratch hClassification hNameFresh hLocation hStackOrder
            hSlotBound
            (by simpa [List.map_append] using ih hTailSplit)

theorem parameters
    {lowerCtx : AllocationLowering.Ctx}
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : MixedAllocation.SlotSet}
    {state : AllocationSupport.CompileState}
    {added returns params : AllocationSupport.SlotEnv}
    (hCtxSlots : lowerCtx.stackSlots = stackSlots)
    (hEnv : state.env = added ++ returns ++ params)
    (hStateNodup : (state.env.map Prod.fst).Nodup)
    (hParamsNodup : (params.map Prod.fst).Nodup)
    (hWF :
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots returns.reverse ++
          MixedAllocation.stackEntries stackSlots params.reverse)
        state).WellFormed) :
    Placement lowerCtx
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots returns.reverse ++
          MixedAllocation.stackEntries stackSlots params.reverse)
        state)
      frameWords [] params := by
  simpa using
    parameters_of_generated hCtxSlots hEnv hStateNodup hParamsNodup
      (processed := []) (pending := params) rfl hWF

theorem returns_of_generated
    {lowerCtx : AllocationLowering.Ctx}
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : MixedAllocation.SlotSet}
    {state : AllocationSupport.CompileState}
    {added allReturns params processed pending : AllocationSupport.SlotEnv}
    (hCtxSlots : lowerCtx.stackSlots = stackSlots)
    (hEnv : state.env = added ++ allReturns ++ params)
    (hStateNodup : (state.env.map Prod.fst).Nodup)
    (hSignatureNodup : ((allReturns ++ params).map Prod.fst).Nodup)
    (hSplit : allReturns = processed ++ pending)
    (hWF :
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots allReturns.reverse ++
          MixedAllocation.stackEntries stackSlots params.reverse)
        state).WellFormed) :
    Placement lowerCtx
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots allReturns.reverse ++
          MixedAllocation.stackEntries stackSlots params.reverse)
        state)
      frameWords
      ((processed.map Prod.fst).reverse ++ (params.map Prod.fst).reverse)
      pending := by
  induction pending generalizing processed with
  | nil =>
      exact .nil
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      have hCurrentMem : (name, slot) ∈ allReturns := by
        rw [hSplit]
        simp
      have hStateMem : (name, slot) ∈ state.env := by
        rw [hEnv]
        simp [hCurrentMem]
      have hNamesNodup :
          (processed.map Prod.fst ++
            name :: rest.map Prod.fst ++ params.map Prod.fst).Nodup := by
        simpa [hSplit, List.map_append, List.append_assoc] using
          hSignatureNodup
      have hNameFresh :
          name ∉
            (processed.map Prod.fst).reverse ++
              (params.map Prod.fst).reverse := by
        have hParts :=
          List.nodup_append.mp
            (show
              (processed.map Prod.fst ++
                (name :: rest.map Prod.fst ++ params.map Prod.fst)).Nodup
              by simpa [List.append_assoc] using hNamesNodup)
        intro hName
        rcases List.mem_append.mp hName with hProcessed | hParam
        · exact
            hParts.2.2 name (by simpa using hProcessed)
              name (by simp) rfl
        · have hNameTail :
              name ∈ name :: rest.map Prod.fst ++ params.map Prod.fst := by
            simp
          have hProcessedTail :=
            List.nodup_append.mp
              (show
                (name :: rest.map Prod.fst ++ params.map Prod.fst).Nodup
                from hParts.2.1)
          exact
            hProcessedTail.2.2 name (by simp)
              name (by simpa using hParam) rfl
      have hTailSplit :
          allReturns = (processed ++ [(name, slot)]) ++ rest := by
        rw [hSplit]
        simp [List.append_assoc]
      have hBefore :=
        MixedAllocation.allocationOfState_return_stack_filter
          (contract := contract) (frameWords := frameWords)
          (stackSlots := stackSlots) (state := state)
          (added := added) (returns := allReturns) (params := params)
          (processed := processed) (pending := (name, slot) :: rest)
          hEnv hStateNodup hSplit
      have hAfter :=
        MixedAllocation.allocationOfState_return_stack_filter
          (contract := contract) (frameWords := frameWords)
          (stackSlots := stackSlots) (state := state)
          (added := added) (returns := allReturns) (params := params)
          (processed := processed ++ [(name, slot)]) (pending := rest)
          hEnv hStateNodup hTailSplit
      have hNextLive :
          ((processed ++ [(name, slot)]).map Prod.fst).reverse ++
              (params.map Prod.fst).reverse =
            name ::
              ((processed.map Prod.fst).reverse ++
                (params.map Prod.fst).reverse) := by
        simp [List.map_append]
      have hBeforeOrder :
          currentStackOrder
              (MixedAllocation.allocationOfState contract frameWords
                (MixedAllocation.stackEntries stackSlots added ++
                  MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                  MixedAllocation.stackEntries stackSlots params.reverse)
                state)
              ((processed.map Prod.fst).reverse ++
                (params.map Prod.fst).reverse) =
            MixedAllocation.stackOrder stackSlots processed.reverse ++
              MixedAllocation.stackOrder stackSlots params.reverse := by
        simpa [currentStackOrder] using hBefore
      have hAfterOrder :
          currentStackOrder
              (MixedAllocation.allocationOfState contract frameWords
                (MixedAllocation.stackEntries stackSlots added ++
                  MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                  MixedAllocation.stackEntries stackSlots params.reverse)
                state)
              (name ::
                ((processed.map Prod.fst).reverse ++
                  (params.map Prod.fst).reverse)) =
            MixedAllocation.stackOrder stackSlots
                (processed ++ [(name, slot)]).reverse ++
              MixedAllocation.stackOrder stackSlots params.reverse := by
        rw [← hNextLive]
        simpa [currentStackOrder] using hAfter
      by_cases hStack : slot ∈ stackSlots
      · have hClassification :
            AllocationLowering.isStackSlot lowerCtx slot = true := by
          rw [AllocationLowering.isStackSlot_eq_true_iff, hCtxSlots]
          exact hStack
        have hEntry :
            (name, slot) ∈
              MixedAllocation.stackEntries stackSlots added ++
                MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                MixedAllocation.stackEntries stackSlots params.reverse := by
          simp only [List.mem_append]
          exact
            Or.inl
              (Or.inr
                (MixedAllocation.mem_stackEntries_iff.mpr
                  ⟨by simpa using hCurrentMem, hStack⟩))
        obtain ⟨planDepth, hLocation⟩ :=
          MixedAllocation.allocationOfState_location_stack_of_entry
            hStateNodup hStateMem hEntry
        have hStackOrder :
            currentStackOrder
                (MixedAllocation.allocationOfState contract frameWords
                  (MixedAllocation.stackEntries stackSlots added ++
                    MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                    MixedAllocation.stackEntries stackSlots params.reverse)
                  state)
                (name ::
                  ((processed.map Prod.fst).reverse ++
                    (params.map Prod.fst).reverse)) =
              name ::
                currentStackOrder
                  (MixedAllocation.allocationOfState contract frameWords
                    (MixedAllocation.stackEntries stackSlots added ++
                      MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                      MixedAllocation.stackEntries stackSlots params.reverse)
                    state)
                  ((processed.map Prod.fst).reverse ++
                    (params.map Prod.fst).reverse) := by
          rw [hAfterOrder, hBeforeOrder, List.reverse_append,
            MixedAllocation.stackOrder_append]
          simp [MixedAllocation.stackOrder,
            MixedAllocation.stackEntries, hStack]
        exact
          .stack hClassification hNameFresh hLocation hStackOrder
            (by simpa [List.map_append] using ih hTailSplit)
      · have hClassification :
            AllocationLowering.isStackSlot lowerCtx slot = false := by
          rw [AllocationLowering.isStackSlot_eq_false_iff, hCtxSlots]
          exact hStack
        have hNotEntry :
            (name, slot) ∉
              MixedAllocation.stackEntries stackSlots added ++
                MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                MixedAllocation.stackEntries stackSlots params.reverse := by
          simp only [List.mem_append, not_or]
          exact
            ⟨⟨MixedAllocation.not_mem_stackEntries_of_slot_not_mem hStack,
                MixedAllocation.not_mem_stackEntries_of_slot_not_mem hStack⟩,
              MixedAllocation.not_mem_stackEntries_of_slot_not_mem hStack⟩
        have hLocation :=
          MixedAllocation.allocationOfState_location_scratch_of_not_entry
            (contract := contract) (frameWords := frameWords)
            hStateNodup hStateMem hNotEntry
        have hSlotBound :=
          MixedAllocation.allocationOfState_scratch_bound_of_wellFormed
            hWF hLocation
        have hStackOrder :
            currentStackOrder
                (MixedAllocation.allocationOfState contract frameWords
                  (MixedAllocation.stackEntries stackSlots added ++
                    MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                    MixedAllocation.stackEntries stackSlots params.reverse)
                  state)
                (name ::
                  ((processed.map Prod.fst).reverse ++
                    (params.map Prod.fst).reverse)) =
              currentStackOrder
                (MixedAllocation.allocationOfState contract frameWords
                  (MixedAllocation.stackEntries stackSlots added ++
                    MixedAllocation.stackEntries stackSlots allReturns.reverse ++
                    MixedAllocation.stackEntries stackSlots params.reverse)
                  state)
                ((processed.map Prod.fst).reverse ++
                  (params.map Prod.fst).reverse) := by
          rw [hAfterOrder, hBeforeOrder, List.reverse_append,
            MixedAllocation.stackOrder_append]
          simp [MixedAllocation.stackOrder,
            MixedAllocation.stackEntries, hStack]
        exact
          .scratch hClassification hNameFresh hLocation hStackOrder
            hSlotBound
            (by simpa [List.map_append] using ih hTailSplit)

theorem returns
    {lowerCtx : AllocationLowering.Ctx}
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : MixedAllocation.SlotSet}
    {state : AllocationSupport.CompileState}
    {added returns params : AllocationSupport.SlotEnv}
    (hCtxSlots : lowerCtx.stackSlots = stackSlots)
    (hEnv : state.env = added ++ returns ++ params)
    (hStateNodup : (state.env.map Prod.fst).Nodup)
    (hSignatureNodup : ((returns ++ params).map Prod.fst).Nodup)
    (hWF :
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots returns.reverse ++
          MixedAllocation.stackEntries stackSlots params.reverse)
        state).WellFormed) :
    Placement lowerCtx
      (MixedAllocation.allocationOfState contract frameWords
        (MixedAllocation.stackEntries stackSlots added ++
          MixedAllocation.stackEntries stackSlots returns.reverse ++
          MixedAllocation.stackEntries stackSlots params.reverse)
        state)
      frameWords (params.map Prod.fst).reverse returns := by
  simpa using
    returns_of_generated hCtxSlots hEnv hStateNodup hSignatureNodup
      (processed := []) (pending := returns) rfl hWF

end Placement

/-- Compiler-owned invariant following the real `lowerParams` recursion. -/
inductive Context
    (lowerCtx : AllocationLowering.Ctx)
    (plan : Locals.Allocation.Plan) (frameWords : Nat) :
    List Locals.Name → List (Locals.Name × Nat) → Nat →
      Locals.Ctx → Prop where
  | nil
      {realized : List Locals.Name}
      {frameDepth : Nat} {localsCtx : Locals.Ctx} :
      Context lowerCtx plan frameWords realized [] frameDepth localsCtx
  | stack
      {realized : List Locals.Name}
      {pending : List (Locals.Name × Nat)}
      {frameDepth planDepth : Nat}
      {localsCtx : Locals.Ctx}
      {name : Locals.Name} {slot : Nat}
      (classification :
        AllocationLowering.isStackSlot lowerCtx slot = true)
      (fresh : name ∉ realized)
      (location : plan.location? name = some (.stack planDepth))
      (stackOrder :
        currentStackOrder plan (name :: realized) =
          name :: currentStackOrder plan realized)
      (tail :
        Context lowerCtx plan frameWords (name :: realized) pending
          (frameDepth + 1) localsCtx) :
      Context lowerCtx plan frameWords realized ((name, slot) :: pending)
        frameDepth localsCtx
  | scratch
      {realized : List Locals.Name}
      {pending : List (Locals.Name × Nat)}
      {frameDepth : Nat} {localsCtx : Locals.Ctx}
      {name : Locals.Name} {slot : Nat}
      (classification :
        AllocationLowering.isStackSlot lowerCtx slot = false)
      (fresh : name ∉ realized)
      (location : plan.location? name = some (.scratch slot))
      (stackOrder :
        currentStackOrder plan (name :: realized) =
          currentStackOrder plan realized)
      (slotBound : slot < frameWords)
      (layout :
        localsCtx.layout =
          (pending.map Prod.fst).reverse ++
            name :: (currentStackOrder plan realized ++ [lowerCtx.frameName]))
      (aboveFresh : name ∉ (pending.map Prod.fst).reverse)
      (suffixFresh :
        name ∉ currentStackOrder plan realized ++ [lowerCtx.frameName])
      (nameDepthBound : pending.length + 1 ≤ 16)
      (frameDepthLookup :
        Locals.Layout.lookupDepth? lowerCtx.frameName
            ((pending.map Prod.fst).reverse ++
              name ::
                (currentStackOrder plan realized ++ [lowerCtx.frameName])) =
          some ((pending.length + 1) + frameDepth + 1))
      (frameDepthBound :
        1 + ((pending.length + 1) + frameDepth + 1) ≤ 16)
      (tail :
        Context lowerCtx plan frameWords (name :: realized) pending
          frameDepth
          (localsCtx.withLayout
            ((pending.map Prod.fst).reverse ++
              currentStackOrder plan (name :: realized) ++
              [lowerCtx.frameName]))) :
      Context lowerCtx plan frameWords realized ((name, slot) :: pending)
        frameDepth localsCtx

namespace Context

theorem of_stack_placement
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan} {frameWords frameDepth : Nat}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {localsCtx : Locals.Ctx}
    (hPlacement : Placement lowerCtx plan frameWords live pending)
    (hStack :
      ∀ binding, binding ∈ pending →
        AllocationLowering.isStackSlot lowerCtx binding.2 = true) :
    Context lowerCtx plan frameWords live pending frameDepth localsCtx := by
  cases hPlacement with
  | nil =>
      exact .nil
  | @stack _ tailPending name slot planDepth classification fresh
      location stackOrder tail =>
      exact
        .stack classification fresh location stackOrder
          (of_stack_placement tail
            (fun binding hBinding =>
              hStack binding (by simp [hBinding])))
  | @scratch _ tailPending name slot classification fresh location
      stackOrder slotBound tail =>
      have hCurrent := hStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

theorem of_placement
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan} {frameWords frameDepth : Nat}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hPlacement : Placement lowerCtx plan frameWords live pending)
    (hLayout :
      localsCtx.layout =
        (pending.map Prod.fst).reverse ++
          currentStackOrder plan live ++ [lowerCtx.frameName])
    (hNodup : localsCtx.layout.Nodup)
    (hFrameDepth :
      frameDepth = (currentStackOrder plan live).length)
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx)) :
    Context lowerCtx plan frameWords live pending frameDepth localsCtx := by
  cases hPlacement with
  | nil =>
      exact .nil
  | @stack _ tailPending name slot planDepth classification fresh
      location stackOrder tail =>
      have hTailLayout :
          localsCtx.layout =
            (tailPending.map Prod.fst).reverse ++
              currentStackOrder plan (name :: live) ++
              [lowerCtx.frameName] := by
        rw [stackOrder]
        simpa [List.reverse_cons, List.append_assoc] using hLayout
      have hTailDepth :
          frameDepth + 1 =
            (currentStackOrder plan (name :: live)).length := by
        rw [stackOrder, hFrameDepth]
        simp
      have hTailCompile :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (AllocationLowering.lowerParams lowerCtx tailPending
                    localsCtx.layout).1 } =
            some (compiled, finalCtx) := by
        simpa [AllocationLowering.lowerParams, classification] using hCompile
      exact
        .stack classification fresh location stackOrder
          (of_placement tail hTailLayout hNodup hTailDepth hTailCompile)
  | @scratch _ tailPending name slot classification fresh location
      stackOrder slotBound tail =>
      let above : Locals.Layout := (tailPending.map Prod.fst).reverse
      let suffix : Locals.Layout :=
        currentStackOrder plan live ++ [lowerCtx.frameName]
      have hCanonicalLayout :
          localsCtx.layout = above ++ name :: suffix := by
        simpa [above, suffix, List.reverse_cons, List.append_assoc] using
          hLayout
      have hCanonicalNodup : (above ++ name :: suffix).Nodup := by
        simpa [hCanonicalLayout] using hNodup
      have hParts := List.nodup_append.mp hCanonicalNodup
      have hAboveFresh : name ∉ above := by
        intro hName
        exact hParts.2.2 name hName name (by simp) rfl
      have hSuffixFresh : name ∉ suffix :=
        (List.nodup_cons.mp hParts.2.1).1
      have hErase :
          AllocationLowering.eraseName name (above ++ name :: suffix) =
            above ++ suffix :=
        AllocationLowering.eraseName_append_name
          hAboveFresh hSuffixFresh
      have hCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (AllocationLowering.lowerScratchParam lowerCtx name slot
                      (above ++ name :: suffix)).1 ++
                    (AllocationLowering.lowerParams lowerCtx tailPending
                      (above ++ suffix)).1 } =
            some (compiled, finalCtx) := by
        simpa [AllocationLowering.lowerParams, classification,
          hCanonicalLayout, AllocationLowering.lowerScratchParam,
          hErase] using hCompile
      obtain
          ⟨headCompiled, middleCtx, tailCompiled,
            hHeadCompile, hTailCompile, _hCompiled⟩ :=
        Locals.Block.compileOpen_append_components hCompile'
      have hFrameLookup :
          Locals.Layout.lookupDepth? lowerCtx.frameName
              (above ++ name :: suffix) =
            some ((tailPending.length + 1) + frameDepth + 1) := by
        have hLast :=
          Locals.Layout.lookupDepth?_getLast_of_nodup
            hCanonicalNodup (by simp [above, suffix])
        simpa [above, suffix, hFrameDepth, List.length_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLast
      obtain ⟨hNameDepthBound, hFrameDepthBound⟩ :=
        AllocationLowering.lowerScratchParam_compileOpen_depth_bounds
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := (tailPending.length + 1) + frameDepth + 1)
          (above := above) (suffix := suffix) (localsCtx := localsCtx)
          hCanonicalLayout hAboveFresh hSuffixFresh hFrameLookup
          hHeadCompile
      have hTailNodup : (above ++ suffix).Nodup := by
        apply List.nodup_append.mpr
        exact
          ⟨hParts.1, (List.nodup_cons.mp hParts.2.1).2,
            by
              intro left hLeft right hRight hEq
              subst right
              exact
                hParts.2.2 left hLeft left (by simp [hRight]) rfl⟩
      have hTailLayout :
          (localsCtx.withLayout (above ++ suffix)).layout =
            (tailPending.map Prod.fst).reverse ++
              currentStackOrder plan (name :: live) ++
              [lowerCtx.frameName] := by
        simp [Locals.Ctx.withLayout, above, suffix, stackOrder,
          List.append_assoc]
      have hTailCompile' :
          Locals.Block.compileOpen
              (localsCtx.withLayout (above ++ suffix))
              { stmts :=
                  (AllocationLowering.lowerParams lowerCtx tailPending
                    (localsCtx.withLayout (above ++ suffix)).layout).1 } =
            some (tailCompiled, finalCtx) := by
        have hMiddle :
            middleCtx = localsCtx.withLayout (above ++ suffix) := by
          obtain ⟨nameOp, hNameOp⟩ :=
            Locals.StackOp.exists_dup?_of_pos_of_le
              (depth := above.length + 1) (by simp) hNameDepthBound
          obtain ⟨frameOp, hFrameOp⟩ :=
            Locals.StackOp.exists_dup?_of_pos_of_le
              (depth :=
                1 + ((tailPending.length + 1) + frameDepth + 1))
              (by omega) hFrameDepthBound
          obtain ⟨promoteCode, hPromoteCode⟩ :=
            Locals.Ctx.exists_swapRestoreUpTo?_of_le
              (depth := above.length) (by omega)
          have hHeadShape :=
            AllocationLowering.lowerScratchParam_compileOpen
              (ctx := lowerCtx) (name := name) (slot := slot)
              (frameDepth :=
                (tailPending.length + 1) + frameDepth + 1)
              (above := above) (suffix := suffix) (localsCtx := localsCtx)
              hCanonicalLayout hAboveFresh hSuffixFresh (by omega)
              hFrameLookup hNameOp hFrameOp hPromoteCode
          rw [hHeadShape] at hHeadCompile
          exact
            (congrArg Prod.snd (Option.some.inj hHeadCompile)).symm
        subst middleCtx
        simpa [Locals.Ctx.withLayout] using hTailCompile
      have hTailDepth :
          frameDepth =
            (currentStackOrder plan (name :: live)).length := by
        rw [stackOrder, hFrameDepth]
      have hTailContext :=
        of_placement tail hTailLayout hTailNodup hTailDepth hTailCompile'
      exact
        .scratch classification fresh location stackOrder slotBound
          hCanonicalLayout hAboveFresh hSuffixFresh
          (by simpa [above] using hNameDepthBound)
          hFrameLookup hFrameDepthBound
          (by
            simpa [above, suffix, stackOrder, List.append_assoc] using
              hTailContext)
termination_by pending.length

end Context

/-- Execute one compiler-emitted scratch-parameter realization step. -/
theorem scratch_step_code
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {name : Locals.Name}
    {nameOp frameOp : Structured.BasicOp}
    {promoteCode : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ActivationCalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase
        (.scratch frameDepth frameWords) source target)
    (hWF : plan.WellFormed)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      currentStackOrder plan (name :: realized) =
        currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hNameOp :
      Locals.StackOp.dup? (pending.length + 1) = some nameOp)
    (hFrameOp :
      Locals.StackOp.dup? ((pending.length + 1) + frameDepth + 2) =
        some frameOp)
    (hPromote :
      Locals.Ctx.swapRestoreUpTo? pending.length = some promoteCode) :
    ∃ written promoted final,
      Structured.InteractionSemantics.Code.openRun
          ([.op nameOp] ++
            [.op frameOp,
             .push (AllocationSupport.slotOffset slot),
             .op .add,
             .op .mstore])
          target =
        .done (.ok written) ∧
      Structured.InteractionSemantics.Code.openRun promoteCode written =
        .done (.ok promoted) ∧
      Structured.InteractionSemantics.Code.openRun [.op .pop] promoted =
        .done (.ok final) ∧
      Structured.InteractionSemantics.Code.openRun
          ([.op nameOp] ++
            [.op frameOp,
             .push (AllocationSupport.slotOffset slot),
             .op .add,
             .op .mstore] ++
            promoteCode ++ [.op .pop])
          target =
        .done (.ok final) ∧
      ActivationCalleeEntryRel contract plan (name :: realized) pending
        frameBase (.scratch frameDepth frameWords) source final ∧
      final.evm.stack.length + 1 = target.evm.stack.length ∧
      final.evm.toMachineState =
        target.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
          ((source.vars name).getD AllocationSupport.zeroWord) := by
  obtain ⟨value, values, suffix, hValue, hLookup, hTargetStack⟩ :=
    hRel.cons_parts
  have hValuesLength : values.length = pending.length := by
    simpa using Functions.Source.Store.lookupMany_length hLookup
  have hValueAt : target.evm.stack[pending.length]? = some value := by
    rw [hTargetStack]
    simp [hValuesLength]
  let afterValue := StateRel.pushTarget value target
  have hValueRun :
      Structured.InteractionSemantics.Code.openRun [.op nameOp] target =
        .done (.ok afterValue) := by
    simpa [afterValue, StateRel.pushTarget] using
      Locals.InteractionPreservation.Code.openRun_dup hNameOp hValueAt
  have hScratch :
      ScratchStateRel contract plan realized (pending.length + 1) frameBase
        frameDepth frameWords source target := by
    cases hRel.state with
    | scratch state => simpa using state
  have hAfterValueRel :
      ScratchStateRel contract plan realized
        ((pending.length + 1) + 1) frameBase frameDepth frameWords
        source afterValue := by
    simpa [afterValue, StateRel.pushTarget] using
      hScratch.push_target_by 1 value
  have hAfterValueStack :
      afterValue.evm.stack = value :: target.evm.stack := by
    rfl
  have hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1 :=
    hScratch.scratchAddress_reserved_of_bound hSlot hReservation
  obtain
      ⟨written, hStoreRun, hWrittenRel, hWrittenStack,
        hWrittenMachine⟩ :=
    AllocationInteractionScratchStore.assignTop
      (stackOffset := pending.length + 1)
      hAfterValueRel hAfterValueStack hWF
      (fun other hOther => by
        simp at hOther
        exact hOther)
      hStackOrder hLocation hSlot hReservation hRegion hFrameOp
  have hWrittenRel' :
      ScratchStateRel contract plan (name :: realized)
        (pending.length + 1) frameBase frameDepth frameWords
        source written := by
    have hInsert : source.insert name value = source :=
      Locals.Source.State.insert_eq_of_apply_eq hValue
    simpa [hInsert] using hWrittenRel
  have hWrittenStack' :
      written.evm.stack = values.reverse ++ value :: suffix := by
    rw [hWrittenStack, hTargetStack]
  obtain
      ⟨promoted, hPromoteRun, hPromoteStack, hPromoteShared,
        _hPromoteReturns⟩ :=
    Locals.InteractionCleanupPreservation.openRun_swapRestoreUpTo?
      hPromote (by simpa using hValuesLength) hWrittenStack'
  let final :=
    promoted.withEVM
      (promoted.evm.replaceStackAndIncrPC (values.reverse ++ suffix))
  have hPopRun :
      Structured.InteractionSemantics.Code.openRun [.op .pop] promoted =
        .done (.ok final) := by
    simpa [final] using
      Locals.InteractionPreservation.Code.openRun_pop hPromoteStack
  have hFinalShared :
      final.evm.toSharedState = written.evm.toSharedState := by
    rw [show final.evm.toSharedState = promoted.evm.toSharedState by
      simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]]
    exact hPromoteShared
  have hFinalStack : final.evm.stack = values.reverse ++ suffix := by
    rfl
  have hFinalRel :
      ActivationCalleeEntryRel contract plan (name :: realized) pending
        frameBase (.scratch frameDepth frameWords) source final :=
    hRel.activate_scratch_after hLookup hTargetStack hWrittenRel'
      hWrittenStack hFinalShared hFinalStack
  have hWholeStoreRun :
      Structured.InteractionSemantics.Code.openRun
          ([.op nameOp] ++
            [.op frameOp,
             .push (AllocationSupport.slotOffset slot),
             .op .add,
             .op .mstore])
          target =
        .done (.ok written) := by
    rw [Structured.InteractionSemantics.Code.openRun_append, hValueRun]
    exact hStoreRun
  have hWholeRun :
      Structured.InteractionSemantics.Code.openRun
          ([.op nameOp] ++
            [.op frameOp,
             .push (AllocationSupport.slotOffset slot),
             .op .add,
             .op .mstore] ++
            promoteCode ++ [.op .pop])
          target =
        .done (.ok final) := by
    rw [Structured.InteractionSemantics.Code.openRun_append,
      Structured.InteractionSemantics.Code.openRun_append,
      hWholeStoreRun]
    change
      Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun promoteCode written)
          (Structured.InteractionSemantics.Code.openRun [.op .pop]) =
        .done (.ok final)
    rw [hPromoteRun]
    exact hPopRun
  refine
    ⟨written, promoted, final, hWholeStoreRun, hPromoteRun, hPopRun,
      hWholeRun, hFinalRel, ?_, ?_⟩
  · rw [hFinalStack, hTargetStack]
    simp only [List.length_append, List.length_reverse,
      List.length_cons, hValuesLength]
    omega
  · have hFinalMachine :
        final.evm.toMachineState = written.evm.toMachineState := by
      calc
        final.evm.toMachineState = promoted.evm.toMachineState := by
          simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        _ = written.evm.toMachineState :=
          congrArg EvmYul.SharedState.toMachineState hPromoteShared
    rw [hFinalMachine, hWrittenMachine]
    simpa [hValue, afterValue, StateRel.pushTarget, StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

/-- Compile and execute the real lowering of one scratch parameter. -/
theorem scratch_step_of_lowerScratchParam
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {name : Locals.Name}
    {ctx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {above suffix : Locals.Layout}
    {targetProgram : Expressions.Program}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ActivationCalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase
        (.scratch frameDepth frameWords) source target)
    (hWF : plan.WellFormed)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      currentStackOrder plan (name :: realized) =
        currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hLayout : localsCtx.layout = above ++ name :: suffix)
    (hAboveLength : above.length = pending.length)
    (hAboveFresh : name ∉ above)
    (hSuffixFresh : name ∉ suffix)
    (hNameDepthBound : above.length + 1 ≤ 16)
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName (above ++ name :: suffix) =
        some ((pending.length + 1) + frameDepth + 1))
    (hFrameDepthBound :
      1 + ((pending.length + 1) + frameDepth + 1) ≤ 16) :
    ∃ compiled final,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerScratchParam ctx name slot
                (above ++ name :: suffix)).1 } =
        some (compiled, localsCtx.withLayout (above ++ suffix)) ∧
      compiled.length = 3 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + 4)
            { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular final))) ∧
      ActivationCalleeEntryRel contract plan (name :: realized) pending
        frameBase (.scratch frameDepth frameWords) source final ∧
      final.evm.stack.length + 1 = target.evm.stack.length ∧
      final.evm.toMachineState =
        target.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
          ((source.vars name).getD AllocationSupport.zeroWord) := by
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
      Locals.StackOp.dup? ((pending.length + 1) + frameDepth + 2) =
        some frameOp := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFrameOp
  have hPromote' :
      Locals.Ctx.swapRestoreUpTo? pending.length = some promoteCode := by
    simpa [hAboveLength] using hPromote
  obtain
      ⟨written, promoted, final, hStoreRun, hPromoteRun, hPopRun,
        _hWholeRun, hFinalRel, hStackLength, hFinalMachine⟩ :=
    scratch_step_code hRel hWF hLocation hStackOrder hSlot
      hReservation hNameOp' hFrameOp' hPromote'
  let compiled : List Expressions.Stmt :=
    [.code
      ([.op nameOp] ++
        [.op frameOp,
         .push (AllocationSupport.slotOffset slot),
         .op .add,
         .op .mstore]),
     .code promoteCode,
     .code [.op .pop]]
  refine
    ⟨compiled, final, by simpa [compiled] using hCompile, by simp [compiled],
      ?_, hFinalRel, hStackLength, hFinalMachine⟩
  intro targetExtra
  let storeCode : Structured.Code :=
    [.op nameOp] ++
      [.op frameOp,
       .push (AllocationSupport.slotOffset slot),
       .op .add,
       .op .mstore]
  have hStoreStmt :
      Expressions.InteractionSemantics.Stmt.openRun targetProgram
          (targetExtra + 3)
          (.code storeCode) target =
        .done (.ok (Structured.Outcome.regular written)) := by
    unfold Expressions.InteractionSemantics.Stmt.openRun
    simp only [Expressions.EffectSemantics.Control.Stmt.run]
    change
      Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun storeCode target)
          _ =
        .done (.ok (Structured.Outcome.regular written))
    rw [show
      Structured.InteractionSemantics.Code.openRun storeCode target =
        .done (.ok written) by simpa [storeCode] using hStoreRun]
    rfl
  have hPromoteStmt :
      Expressions.InteractionSemantics.Stmt.openRun targetProgram
          (targetExtra + 2)
          (.code promoteCode) written =
        .done (.ok (Structured.Outcome.regular promoted)) := by
    unfold Expressions.InteractionSemantics.Stmt.openRun
    simp only [Expressions.EffectSemantics.Control.Stmt.run]
    change
      Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun promoteCode written)
          _ =
        .done (.ok (Structured.Outcome.regular promoted))
    rw [hPromoteRun]
    rfl
  have hPopStmt :
      Expressions.InteractionSemantics.Stmt.openRun targetProgram
          (targetExtra + 1)
          (.code [.op .pop]) promoted =
        .done (.ok (Structured.Outcome.regular final)) := by
    unfold Expressions.InteractionSemantics.Stmt.openRun
    simp only [Expressions.EffectSemantics.Control.Stmt.run]
    change
      Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun [.op .pop] promoted)
          _ =
        .done (.ok (Structured.Outcome.regular final))
    rw [hPopRun]
    rfl
  unfold Expressions.InteractionSemantics.Stmt.openRun at hStoreStmt
  unfold Expressions.InteractionSemantics.Stmt.openRun at hPromoteStmt
  unfold Expressions.InteractionSemantics.Stmt.openRun at hPopStmt
  dsimp only [compiled]
  change
    Expressions.InteractionSemantics.Block.openRun targetProgram
        ((targetExtra + 3) + 1)
        { stmts :=
            [.code storeCode, .code promoteCode, .code [.op .pop]] }
        target =
      .done (.ok (Structured.Outcome.regular final))
  rw [Expressions.InteractionSemantics.Block.openRun_cons, hStoreStmt]
  change
    Expressions.InteractionSemantics.Block.openRun targetProgram
        ((targetExtra + 2) + 1)
        { stmts := [.code promoteCode, .code [.op .pop]] } written =
      .done (.ok (Structured.Outcome.regular final))
  rw [Expressions.InteractionSemantics.Block.openRun_cons, hPromoteStmt]
  change
    Expressions.InteractionSemantics.Block.openRun targetProgram
        ((targetExtra + 1) + 1)
        { stmts := [.code [.op .pop]] } promoted =
      .done (.ok (Structured.Outcome.regular final))
  rw [Expressions.InteractionSemantics.Block.openRun_cons, hPopStmt]
  exact
    Expressions.InteractionSemantics.Block.openRun_nil
      targetProgram targetExtra final

/-- Execute and compile the complete scratch-backed parameter prelude. -/
theorem forward_scratch
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hContext :
      Context lowerCtx plan frameWords realized pending frameDepth localsCtx)
    (hRel :
      ActivationCalleeEntryRel contract plan realized pending frameBase
        (.scratch frameDepth frameWords) source target)
    (hFrameDepth :
      frameDepth = (currentStackOrder plan realized).length)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = compiled.length + 1 ∧
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerParams lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ realized)).length ∧
      finalTarget.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, frameDepth, 1, by omega, rfl,
        ?_, ?_, ?_, ?_, ?_, hStackLength⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · cases hRel.finish with
        | scratch state => simpa using state
      · simpa using hFrameDepth
  | @stack _ tailPending _ planDepth _ name slot classification fresh
      location stackOrder tail =>
      have hNextRel :
          ActivationCalleeEntryRel contract plan (name :: realized)
            tailPending frameBase
            (.scratch (frameDepth + 1) frameWords) source target := by
        simpa [ActivationMode.afterStackDeclaration] using
          hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
            hFuel, hFuelLength, hCompile, hFinalLayout, hEvalAt, hFinalRel,
            hFinalDepth, hFinalStackLength⟩ :=
        forward_scratch (targetProgram := targetProgram) tail hNextRel
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hStackLength hWF hReservation
      refine
        ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel, hFuel,
          hFuelLength, ?_, ?_, hEvalAt, ?_, ?_, hFinalStackLength⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
  | @scratch _ tailPending _ _ name slot classification fresh location
      stackOrder slotBound layout aboveFresh suffixFresh nameDepthBound
      frameDepthLookup frameDepthBound tail =>
      let above : Locals.Layout := (tailPending.map Prod.fst).reverse
      let suffix : Locals.Layout :=
        currentStackOrder plan (name :: realized) ++ [lowerCtx.frameName]
      have hLayout : localsCtx.layout = above ++ name :: suffix := by
        simpa [above, suffix, stackOrder] using layout
      have hSuffixFresh : name ∉ suffix := by
        simpa [suffix, stackOrder] using suffixFresh
      have hFrameDepthLookup :
          Locals.Layout.lookupDepth? lowerCtx.frameName
              (above ++ name :: suffix) =
            some ((tailPending.length + 1) + frameDepth + 1) := by
        simpa [above, suffix, stackOrder] using frameDepthLookup
      obtain
          ⟨headCompiled, midTarget, hHeadCompile, hHeadLength,
            hHeadEval, hNextRel, hStepLength, _hStepMachine⟩ :=
        scratch_step_of_lowerScratchParam
          (contract := contract) (plan := plan) (realized := realized)
          (pending := tailPending) (frameBase := frameBase)
          (frameDepth := frameDepth) (frameWords := frameWords)
          (slot := slot) (source := source) (target := target)
          (name := name) (ctx := lowerCtx) (localsCtx := localsCtx)
          (above := above) (suffix := suffix)
          (targetProgram := targetProgram) (reservation := reservation)
          hRel hWF location stackOrder slotBound hReservation hLayout
          (by simp [above]) (by simpa [above] using aboveFresh)
          hSuffixFresh (by simpa [above] using nameDepthBound)
          hFrameDepthLookup frameDepthBound
      have hMidStackLength :
          midTarget.evm.stack.length =
            (localsCtx.withLayout (above ++ suffix)).layout.length := by
        simp only [Locals.Ctx.withLayout]
        have hInitialLength :
            target.evm.stack.length = (above ++ name :: suffix).length := by
          rw [hStackLength, hLayout]
        simp only [List.length_append, List.length_cons] at hInitialLength
        simp only [List.length_append]
        omega
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth, tailFuel,
            hTailFuel, hTailFuelLength, hTailCompile, hFinalLayout,
            hTailEvalAt, hFinalRel,
            hFinalDepth, hFinalStackLength⟩ :=
        forward_scratch (targetProgram := targetProgram) tail hNextRel
          (by simpa [stackOrder] using hFrameDepth)
          (by
            simpa [above, suffix, List.append_assoc] using hMidStackLength)
          hWF hReservation
      have hHeadCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (AllocationLowering.lowerScratchParam lowerCtx name slot
                    localsCtx.layout).1 } =
            some
              (headCompiled, localsCtx.withLayout (above ++ suffix)) := by
        simpa [hLayout] using hHeadCompile
      have hTailCompile' :
          Locals.Block.compileOpen
              (localsCtx.withLayout (above ++ suffix))
              { stmts :=
                  (AllocationLowering.lowerParams lowerCtx tailPending
                    (above ++ suffix)).1 } =
            some (tailCompiled, finalCtx) := by
        simpa [Locals.Ctx.withLayout, above, suffix,
          List.append_assoc] using hTailCompile
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile' hTailCompile'
      have hErase :
          AllocationLowering.eraseName name (above ++ name :: suffix) =
            above ++ suffix :=
        AllocationLowering.eraseName_append_name aboveFresh hSuffixFresh
      let fuel := headCompiled.length + tailFuel
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + fuel)
                { stmts := headCompiled ++ tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hHeadAtFuel :
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + fuel) { stmts := headCompiled } target =
              .done (.ok (Structured.Outcome.regular midTarget)) := by
          have hRun := hHeadEval (targetExtra + tailFuel - 1)
          have hFuelEq :
              targetExtra + tailFuel - 1 + 4 = targetExtra + fuel := by
            simp [fuel, hHeadLength]
            omega
          simpa [hFuelEq] using hRun
        rw [Expressions.InteractionSemantics.Block.openRun_append,
          hHeadAtFuel]
        have hRemaining :
            targetExtra + fuel - headCompiled.length =
              targetExtra + tailFuel := by
          simp only [fuel]
          omega
        simpa [hRemaining] using hTailEvalAt targetExtra
      refine
        ⟨headCompiled ++ tailCompiled, finalCtx, finalTarget,
          finalFrameDepth, fuel, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hFinalStackLength⟩
      · simp [fuel]
        omega
      · simp only [fuel, List.length_append, hHeadLength, hTailFuelLength]
        omega
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using hFinalLayout
      · exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
termination_by pending.length

/-- Execute and compile the complete all-stack parameter prelude. -/
theorem forward_stack
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    (hContext :
      Context lowerCtx plan frameWords realized pending frameDepth localsCtx)
    (hAllStack :
      ∀ binding, binding ∈ pending →
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      ActivationCalleeEntryRel contract plan realized pending frameBase
        .stack source target)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length) :
    ∃ compiled finalCtx finalTarget fuel,
      0 < fuel ∧
      fuel = compiled.length + 1 ∧
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerParams lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        .stack source finalTarget ∧
      finalTarget.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, 1, by omega, rfl, ?_, ?_, ?_, ?_,
        hStackLength⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · simpa using hRel.finish
  | @stack _ tailPending _ _ _ name slot classification fresh location
      stackOrder tail =>
      have hNextRel :
          ActivationCalleeEntryRel contract plan (name :: realized)
            tailPending frameBase .stack source target := by
        simpa [ActivationMode.afterStackDeclaration] using
          hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength, hCompile,
            hFinalLayout, hEvalAt, hFinalRel, hFinalStackLength⟩ :=
        forward_stack (targetProgram := targetProgram) tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel hStackLength
      refine
        ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength,
          ?_, ?_, hEvalAt,
          ?_, hFinalStackLength⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
  | @scratch _ tailPending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _layout _aboveFresh _suffixFresh
      _nameDepthBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent := hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

end ParameterPrelude

namespace ReturnPrelude

/-- Compiler-owned invariant following the real `lowerReturns` recursion. -/
inductive Context
    (lowerCtx : AllocationLowering.Ctx)
    (plan : Locals.Allocation.Plan) (frameWords : Nat) :
    List Locals.Name → List (Locals.Name × Nat) → Nat →
      Locals.Ctx → Prop where
  | nil
      {live : List Locals.Name}
      {frameDepth : Nat} {localsCtx : Locals.Ctx} :
      Context lowerCtx plan frameWords live [] frameDepth localsCtx
  | stack
      {live : List Locals.Name}
      {pending : List (Locals.Name × Nat)}
      {frameDepth planDepth : Nat}
      {localsCtx : Locals.Ctx}
      {name : Locals.Name} {slot : Nat}
      (classification :
        AllocationLowering.isStackSlot lowerCtx slot = true)
      (fresh : name ∉ live)
      (location : plan.location? name = some (.stack planDepth))
      (stackOrder :
        currentStackOrder plan (name :: live) =
          name :: currentStackOrder plan live)
      (tail :
        Context lowerCtx plan frameWords (name :: live) pending
          (frameDepth + 1)
          (localsCtx.withLayout (name :: localsCtx.layout))) :
      Context lowerCtx plan frameWords live ((name, slot) :: pending)
        frameDepth localsCtx
  | scratch
      {live : List Locals.Name}
      {pending : List (Locals.Name × Nat)}
      {frameDepth : Nat} {localsCtx : Locals.Ctx}
      {name : Locals.Name} {slot : Nat}
      (classification :
        AllocationLowering.isStackSlot lowerCtx slot = false)
      (fresh : name ∉ live)
      (location : plan.location? name = some (.scratch slot))
      (stackOrder :
        currentStackOrder plan (name :: live) =
          currentStackOrder plan live)
      (slotBound : slot < frameWords)
      (frameDepthLookup :
        Locals.Layout.lookupDepth? lowerCtx.frameName localsCtx.layout =
          some (frameDepth + 1))
      (frameDepthBound : 1 + (frameDepth + 1) ≤ 16)
      (tail :
        Context lowerCtx plan frameWords (name :: live) pending
          frameDepth localsCtx) :
      Context lowerCtx plan frameWords live ((name, slot) :: pending)
        frameDepth localsCtx

namespace Context

theorem of_stack_placement
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan} {frameWords frameDepth : Nat}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {localsCtx : Locals.Ctx}
    (hPlacement :
      ParameterPrelude.Placement lowerCtx plan frameWords live pending)
    (hStack :
      ∀ binding, binding ∈ pending →
        AllocationLowering.isStackSlot lowerCtx binding.2 = true) :
    Context lowerCtx plan frameWords live pending frameDepth localsCtx := by
  cases hPlacement with
  | nil =>
      exact .nil
  | @stack _ tailPending name slot planDepth classification fresh
      location stackOrder tail =>
      exact
        .stack classification fresh location stackOrder
          (of_stack_placement tail
            (fun binding hBinding =>
              hStack binding (by simp [hBinding])))
  | @scratch _ tailPending name slot classification fresh location
      stackOrder slotBound tail =>
      have hCurrent := hStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

theorem of_placement
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan} {frameWords frameDepth : Nat}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hPlacement :
      ParameterPrelude.Placement lowerCtx plan frameWords live pending)
    (hLayout :
      localsCtx.layout =
        currentStackOrder plan live ++ [lowerCtx.frameName])
    (hNodup : localsCtx.layout.Nodup)
    (hFrameDepth :
      frameDepth = (currentStackOrder plan live).length)
    (hFrameFresh : lowerCtx.frameName ∉ pending.map Prod.fst)
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx)) :
    Context lowerCtx plan frameWords live pending frameDepth localsCtx := by
  cases hPlacement with
  | nil =>
      exact .nil
  | @stack _ tailPending name slot planDepth classification fresh
      location stackOrder tail =>
      have hCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  [.let_ name (.lit AllocationSupport.zeroWord)] ++
                    (AllocationLowering.lowerReturns lowerCtx tailPending
                      (name :: localsCtx.layout)).1 } =
            some (compiled, finalCtx) := by
        simpa [AllocationLowering.lowerReturns, classification] using hCompile
      obtain
          ⟨headCompiled, middleCtx, tailCompiled,
            hHeadCompile, hTailCompile, _hCompiled⟩ :=
        Locals.Block.compileOpen_append_components hCompile'
      have hHeadShape :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      rw [hHeadShape] at hHeadCompile
      have hMiddle :
          middleCtx = localsCtx.withLayout (name :: localsCtx.layout) :=
        (congrArg Prod.snd (Option.some.inj hHeadCompile)).symm
      subst middleCtx
      have hTailLayout :
          (localsCtx.withLayout (name :: localsCtx.layout)).layout =
            currentStackOrder plan (name :: live) ++
              [lowerCtx.frameName] := by
        simp [Locals.Ctx.withLayout, stackOrder, hLayout,
          List.append_assoc]
      have hTailNodup :
          (localsCtx.withLayout (name :: localsCtx.layout)).layout.Nodup := by
        have hNameNotLayout : name ∉ localsCtx.layout := by
          rw [hLayout]
          simp only [List.mem_append, List.mem_singleton, not_or]
          constructor
          · intro hCurrent
            exact fresh (mem_live_of_mem_currentStackOrder hCurrent)
          · intro hFrame
            have hNameFrame : lowerCtx.frameName = name := hFrame.symm
            exact hFrameFresh (by simp [hNameFrame])
        simp [Locals.Ctx.withLayout, hNameNotLayout, hNodup]
      have hTailDepth :
          frameDepth + 1 =
            (currentStackOrder plan (name :: live)).length := by
        rw [stackOrder, hFrameDepth]
        simp
      have hTailCompile' :
          Locals.Block.compileOpen
              (localsCtx.withLayout (name :: localsCtx.layout))
              { stmts :=
                  (AllocationLowering.lowerReturns lowerCtx tailPending
                    (localsCtx.withLayout
                      (name :: localsCtx.layout)).layout).1 } =
            some (tailCompiled, finalCtx) := by
        simpa [Locals.Ctx.withLayout] using hTailCompile
      exact
        .stack classification fresh location stackOrder
          (of_placement tail hTailLayout hTailNodup hTailDepth
            (fun hFrame => hFrameFresh (by simp [hFrame]))
            hTailCompile')
  | @scratch _ tailPending name slot classification fresh location
      stackOrder slotBound tail =>
      have hFrameLookup :
          Locals.Layout.lookupDepth? lowerCtx.frameName localsCtx.layout =
            some (frameDepth + 1) := by
        have hLast :=
          Locals.Layout.lookupDepth?_getLast_of_nodup hNodup
            (by simpa [hLayout])
        simpa [hLayout, hFrameDepth, List.length_append,
          Nat.add_assoc] using hLast
      have hCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  [.expr
                    (AllocationLowering.scratchStoreExpr
                      lowerCtx.frameName slot
                      (.lit AllocationSupport.zeroWord))] ++
                    (AllocationLowering.lowerReturns lowerCtx tailPending
                      localsCtx.layout).1 } =
            some (compiled, finalCtx) := by
        simpa [AllocationLowering.lowerReturns, classification] using hCompile
      obtain
          ⟨headCompiled, middleCtx, tailCompiled,
            hHeadCompile, hTailCompile, _hCompiled⟩ :=
        Locals.Block.compileOpen_append_components hCompile'
      have hFrameDepthBound :=
        AllocationLowering.lowerScratchReturn_compileOpen_depth_bound
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := frameDepth + 1) (localsCtx := localsCtx)
          hFrameLookup hHeadCompile
      obtain ⟨frameOp, hFrameOp⟩ :=
        Locals.StackOp.exists_dup?_of_pos_of_le
          (depth := 1 + (frameDepth + 1))
          (by omega) hFrameDepthBound
      have hHeadShape :=
        AllocationLowering.lowerScratchReturn_compileOpen
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := frameDepth + 1) (localsCtx := localsCtx)
          hFrameLookup hFrameOp
      rw [hHeadShape] at hHeadCompile
      have hMiddle : middleCtx = localsCtx :=
        (congrArg Prod.snd (Option.some.inj hHeadCompile)).symm
      subst middleCtx
      have hTailLayout :
          localsCtx.layout =
            currentStackOrder plan (name :: live) ++
              [lowerCtx.frameName] := by
        rw [stackOrder]
        exact hLayout
      have hTailDepth :
          frameDepth =
            (currentStackOrder plan (name :: live)).length := by
        rw [stackOrder, hFrameDepth]
      exact
        .scratch classification fresh location stackOrder slotBound
          hFrameLookup hFrameDepthBound
          (of_placement tail hTailLayout hNodup hTailDepth
            (fun hFrame => hFrameFresh (by simp [hFrame]))
            (by simpa using hTailCompile))
termination_by pending.length

end Context

/-- Execute and compile the complete scratch-capable return prelude. -/
theorem forward_scratch
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hContext :
      Context lowerCtx plan frameWords live pending frameDepth localsCtx)
    (hRel :
      ScratchStateRel contract plan live 0 frameBase frameDepth frameWords
        source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.vars name = some AllocationSupport.zeroWord)
    (hFrameDepth :
      frameDepth = (currentStackOrder plan live).length)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = compiled.length + 1 ∧
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ live)).length ∧
      finalTarget.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, frameDepth, 1, by omega, rfl,
        ?_, ?_, ?_, ?_, ?_, hStackLength⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · simpa using hRel
      · simpa using hFrameDepth
  | @stack _ tailPending _ planDepth _ name slot classification fresh
      location stackOrder tail =>
      let pushed := StateRel.pushTargetBy 33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.InteractionSemantics.Code.openRun
              [.push AllocationSupport.zeroWord] target =
            .done (.ok pushed) := by
        simpa [pushed, StateRel.pushTargetBy] using
          Locals.InteractionPreservation.Code.openRun_push
            AllocationSupport.zeroWord target
      have hPushedRel :
          ScratchStateRel contract plan live 1 frameBase frameDepth
            frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.evm.stack = AllocationSupport.zeroWord :: target.evm.stack :=
        rfl
      have hNameZero :
          source.vars name = some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          ScratchStateRel contract plan (name :: live) 0 frameBase
            (frameDepth + 1) frameWords source pushed := by
        have hDeclared :=
          hPushedRel.declare_stack_live hPushedStack
            (fun other hOther => by
              simp at hOther
              exact hOther)
            location stackOrder
        rw [Locals.Source.State.insert_eq_of_apply_eq hNameZero] at hDeclared
        simpa using hDeclared
      have hNextStackLength :
          pushed.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailFuel, hTailFuelLength, hTailCompile, hFinalLayout,
            hTailEvalAt,
            hFinalRel, hFinalDepth, hFinalStackLength⟩ :=
        forward_scratch (targetProgram := targetProgram) tail hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hNextStackLength hWF hReservation
      let headCode : Structured.Code :=
        [.push AllocationSupport.zeroWord] ++
          Locals.bindLocals 0 (name :: localsCtx.layout)
      let headStmt : Expressions.Stmt := .code headCode
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadCodeRun :
          Structured.InteractionSemantics.Code.openRun headCode target =
            .done (.ok pushed) := by
        rw [show headCode =
            [.push AllocationSupport.zeroWord] ++
              Locals.bindLocals 0 (name :: localsCtx.layout) by rfl,
          Structured.InteractionSemantics.Code.openRun_append, hPushRun]
        rfl
      have hHeadStmtRun (targetExtra : Nat) :
          Expressions.EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Ordinary.runStateModel
              Structured.InteractionSemantics.handler targetProgram
              (targetExtra + tailFuel) headStmt target =
            .done (.ok (Structured.Outcome.regular pushed)) := by
        simp only [headStmt, Expressions.EffectSemantics.Control.Stmt.run]
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              _ =
            .done (.ok (Structured.Outcome.regular pushed))
        rw [hHeadCodeRun]
        rfl
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + (tailFuel + 1))
                { stmts := headStmt :: tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hFuel :
            targetExtra + (tailFuel + 1) =
              (targetExtra + tailFuel) + 1 := by omega
        rw [hFuel, Expressions.InteractionSemantics.Block.openRun_cons,
          hHeadStmtRun targetExtra]
        exact hTailEvalAt targetExtra
      refine
        ⟨headStmt :: tailCompiled, finalCtx, finalTarget, finalFrameDepth,
          tailFuel + 1, by omega, ?_, ?_, ?_, hCombinedEval, ?_, ?_,
          hFinalStackLength⟩
      · simp [hTailFuelLength]
      · simpa [headStmt, headCode, AllocationLowering.lowerReturns,
          classification] using hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
  | @scratch _ tailPending _ _ name slot classification fresh location
      stackOrder slotBound frameDepthLookup frameDepthBound tail =>
      obtain ⟨frameOp, hFrameOp⟩ :=
        Locals.StackOp.exists_dup?_of_pos_of_le
          (depth := 1 + (frameDepth + 1)) (by omega) frameDepthBound
      let pushed := StateRel.pushTargetBy 33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.InteractionSemantics.Code.openRun
              [.push AllocationSupport.zeroWord] target =
            .done (.ok pushed) := by
        simpa [pushed, StateRel.pushTargetBy] using
          Locals.InteractionPreservation.Code.openRun_push
            AllocationSupport.zeroWord target
      have hPushedRel :
          ScratchStateRel contract plan live 1 frameBase frameDepth
            frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.evm.stack = AllocationSupport.zeroWord :: target.evm.stack :=
        rfl
      have hRegion :
          reservation.containsRegion (scratchAddress frameBase slot) 1 :=
        hRel.scratchAddress_reserved_of_bound slotBound hReservation
      obtain
          ⟨midTarget, hStoreRun, hStoredRel, hStoredStack,
            _hStoredMachine⟩ :=
        AllocationInteractionScratchStore.assignTop
          (stackOffset := 0) hPushedRel hPushedStack hWF
          (fun other hOther => by
            simp at hOther
            exact hOther)
          stackOrder location slotBound hReservation hRegion
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hFrameOp)
      have hNameZero :
          source.vars name = some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          ScratchStateRel contract plan (name :: live) 0 frameBase
            frameDepth frameWords source midTarget := by
        have hInsert :
            source.insert name AllocationSupport.zeroWord = source :=
          Locals.Source.State.insert_eq_of_apply_eq hNameZero
        simpa [hInsert] using hStoredRel
      have hNextStackLength :
          midTarget.evm.stack.length = localsCtx.layout.length := by
        rw [hStoredStack]
        exact hStackLength
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailFuel, hTailFuelLength, hTailCompile, hFinalLayout,
            hTailEvalAt,
            hFinalRel, hFinalDepth, hFinalStackLength⟩ :=
        forward_scratch (targetProgram := targetProgram) tail hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by simpa [stackOrder] using hFrameDepth)
          hNextStackLength hWF hReservation
      let headCode : Structured.Code :=
        [.push AllocationSupport.zeroWord] ++
          [.op frameOp,
           .push (AllocationSupport.slotOffset slot),
           .op .add,
           .op .mstore]
      let headStmt : Expressions.Stmt := .code headCode
      have hHeadCompile :=
        AllocationLowering.lowerScratchReturn_compileOpen
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := frameDepth + 1) (localsCtx := localsCtx)
          (frameOp := frameOp) frameDepthLookup hFrameOp
      have hHeadCodeRun :
          Structured.InteractionSemantics.Code.openRun headCode target =
            .done (.ok midTarget) := by
        rw [show headCode =
            [.push AllocationSupport.zeroWord] ++
              [.op frameOp,
               .push (AllocationSupport.slotOffset slot),
               .op .add,
               .op .mstore] by rfl,
          Structured.InteractionSemantics.Code.openRun_append, hPushRun]
        exact hStoreRun
      have hHeadStmtRun (targetExtra : Nat) :
          Expressions.EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Ordinary.runStateModel
              Structured.InteractionSemantics.handler targetProgram
              (targetExtra + tailFuel) headStmt target =
            .done (.ok (Structured.Outcome.regular midTarget)) := by
        simp only [headStmt, Expressions.EffectSemantics.Control.Stmt.run]
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              _ =
            .done (.ok (Structured.Outcome.regular midTarget))
        rw [hHeadCodeRun]
        rfl
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + (tailFuel + 1))
                { stmts := headStmt :: tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hFuel :
            targetExtra + (tailFuel + 1) =
              (targetExtra + tailFuel) + 1 := by omega
        rw [hFuel, Expressions.InteractionSemantics.Block.openRun_cons,
          hHeadStmtRun targetExtra]
        exact hTailEvalAt targetExtra
      refine
        ⟨headStmt :: tailCompiled, finalCtx, finalTarget, finalFrameDepth,
          tailFuel + 1, by omega, ?_, ?_, ?_, hCombinedEval, ?_, ?_,
          hFinalStackLength⟩
      · simp [hTailFuelLength]
      · simpa [headStmt, headCode, AllocationLowering.lowerReturns,
          classification] using hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
termination_by pending.length

/-- Execute and compile the complete all-stack return prelude. -/
theorem forward_stack
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    (hContext :
      Context lowerCtx plan frameWords live pending frameDepth localsCtx)
    (hAllStack :
      ∀ binding, binding ∈ pending →
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      ActivationStateRel contract plan live 0 frameBase .stack source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.vars name = some AllocationSupport.zeroWord)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length) :
    ∃ compiled finalCtx finalTarget fuel,
      0 < fuel ∧
      fuel = compiled.length + 1 ∧
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase .stack
        source finalTarget ∧
      finalTarget.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, 1, by omega, rfl, ?_, ?_, ?_, ?_,
        hStackLength⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · simpa using hRel
  | @stack _ tailPending _ _ _ name slot classification fresh location
      stackOrder tail =>
      let pushed := StateRel.pushTargetBy 33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.InteractionSemantics.Code.openRun
              [.push AllocationSupport.zeroWord] target =
            .done (.ok pushed) := by
        simpa [pushed, StateRel.pushTargetBy] using
          Locals.InteractionPreservation.Code.openRun_push
            AllocationSupport.zeroWord target
      have hPushedRel :
          ActivationStateRel contract plan live 1 frameBase .stack
            source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.evm.stack = AllocationSupport.zeroWord :: target.evm.stack :=
        rfl
      have hNameZero :
          source.vars name = some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          ActivationStateRel contract plan (name :: live) 0 frameBase .stack
            source pushed := by
        have hDeclared :=
          hPushedRel.declare_stack_live hPushedStack
            (fun other hOther => by
              simp at hOther
              exact hOther)
            location stackOrder
        rw [Locals.Source.State.insert_eq_of_apply_eq hNameZero] at hDeclared
        simpa [ActivationMode.afterStackDeclaration] using hDeclared
      have hNextStackLength :
          pushed.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, tailFuel, hTailFuel,
            hTailFuelLength, hTailCompile, hFinalLayout, hTailEvalAt, hFinalRel,
            hFinalStackLength⟩ :=
        forward_stack (targetProgram := targetProgram) tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          hNextStackLength
      let headCode : Structured.Code :=
        [.push AllocationSupport.zeroWord] ++
          Locals.bindLocals 0 (name :: localsCtx.layout)
      let headStmt : Expressions.Stmt := .code headCode
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadCodeRun :
          Structured.InteractionSemantics.Code.openRun headCode target =
            .done (.ok pushed) := by
        rw [show headCode =
            [.push AllocationSupport.zeroWord] ++
              Locals.bindLocals 0 (name :: localsCtx.layout) by rfl,
          Structured.InteractionSemantics.Code.openRun_append, hPushRun]
        rfl
      have hHeadStmtRun (targetExtra : Nat) :
          Expressions.EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Ordinary.runStateModel
              Structured.InteractionSemantics.handler targetProgram
              (targetExtra + tailFuel) headStmt target =
            .done (.ok (Structured.Outcome.regular pushed)) := by
        simp only [headStmt, Expressions.EffectSemantics.Control.Stmt.run]
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              _ =
            .done (.ok (Structured.Outcome.regular pushed))
        rw [hHeadCodeRun]
        rfl
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + (tailFuel + 1))
                { stmts := headStmt :: tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hFuel :
            targetExtra + (tailFuel + 1) =
              (targetExtra + tailFuel) + 1 := by omega
        rw [hFuel, Expressions.InteractionSemantics.Block.openRun_cons,
          hHeadStmtRun targetExtra]
        exact hTailEvalAt targetExtra
      refine
        ⟨headStmt :: tailCompiled, finalCtx, finalTarget, tailFuel + 1,
          by omega, ?_, ?_, ?_, hCombinedEval, ?_, hFinalStackLength⟩
      · simp [hTailFuelLength]
      · simpa [headStmt, headCode, AllocationLowering.lowerReturns,
          classification] using hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
  | @scratch _ tailPending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent := hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

end ReturnPrelude

/-- Stable caller-side decomposition of one ordinary compiled function call. -/
structure CallComponents
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
    (cursor :
      CoreCursor root scope live
        { stmts := .call targets functionName args :: rest }
        lowerState localsCtx) where
  headLower : List Locals.Stmt
  headCode : List Expressions.Stmt
  tail :
    CoreCursor root scope live { stmts := rest } lowerState localsCtx
  fn : AllocationSupport.FunSlots
  loweredArgs : List (Locals.Expr 1)
  callArgs : List (Locals.Expr 1)
  stores : Structured.Code
  release : List Locals.Stmt
  argsCode : Structured.Code
  releaseCode : List Expressions.Stmt
  lookup :
    AllocationSupport.lookupFun? functionName root.lowerCtx.functions = some fn
  argsLength : args.length = fn.params.length
  targetsLength : targets.length = fn.returns.length
  targetsNodup : targets.Nodup
  lowerArgs :
    AllocationLowering.lowerExprList root.lowerCtx lowerState args =
      some loweredArgs
  callArgs_eq :
    (if functionName ∈ root.lowerCtx.frameFunctions then do
        let frameConfig ← root.lowerCtx.frameConfig?
        some (AllocationLowering.frameExpr frameConfig :: loweredArgs)
      else
        some loweredArgs) =
      some callArgs
  stores_eq :
    AllocationLowering.lowerCallTargetsCode?
        root.lowerCtx lowerState targets.reverse targets.length =
      some stores
  release_eq :
    (if functionName ∈ root.lowerCtx.frameFunctions then do
        let frameConfig ← root.lowerCtx.frameConfig?
        some
          [.expr
            (Locals.Expr.code (results := 0)
              (AllocationSupport.scratchFrameReleaseCode frameConfig))]
      else
        some []) =
      some release
  compileArgs :
    Locals.ExprSeq.compileCode localsCtx 0
        (AllocationLowering.exprSeqOfList callArgs) =
      some argsCode
  compileRelease :
    Locals.Block.compileOpen localsCtx { stmts := release } =
      some (releaseCode, localsCtx)
  headCode_eq :
    headCode =
      Locals.codeStmt argsCode ++ [.call functionName] ++
        Locals.codeStmt stores ++ releaseCode
  compiled : cursor.compiled = headCode ++ tail.compiled
  lower :
    AllocationLowering.lowerStmt root.lowerCtx root.returns lowerState
        (.call targets functionName args) =
      some (headLower, lowerState)
  compile :
    Locals.Block.compileOpen localsCtx { stmts := headLower } =
      some (headCode, localsCtx)
  step :
    StepTransport lowerState lowerState localsCtx localsCtx live
      (.call targets functionName args)
  exactTail : ExactTail cursor tail

/-- Construct the caller-side artifact solely from the ordinary compiler. -/
theorem CoreCursor.callComponents
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
    (cursor :
      CoreCursor root scope live
        { stmts := .call targets functionName args :: rest }
        lowerState localsCtx) :
    Nonempty (CallComponents cursor) := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals,
        hLower, hCompile, _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain
      ⟨fn, loweredArgs, callArgs, stores, release, argsCode, releaseCode,
        hLookup, hArgsLength, hTargetsLength, hTargetsNodup,
        hLowerArgs, hCallArgs, hStores, hRelease,
        hCompileArgs, hCompileRelease, hHeadCode,
        hAfterState, hAfterLocals⟩ :=
    CallCompiler.components hLower hCompile
  subst afterState
  subst afterLocals
  exact ⟨{
    headLower := headLower
    headCode := headCode
    tail := tail
    fn := fn
    loweredArgs := loweredArgs
    callArgs := callArgs
    stores := stores
    release := release
    argsCode := argsCode
    releaseCode := releaseCode
    lookup := hLookup
    argsLength := hArgsLength
    targetsLength := hTargetsLength
    targetsNodup := hTargetsNodup
    lowerArgs := hLowerArgs
    callArgs_eq := hCallArgs
    stores_eq := hStores
    release_eq := hRelease
    compileArgs := hCompileArgs
    compileRelease := hCompileRelease
    headCode_eq := hHeadCode
    compiled := hCompiled
    lower := hLower
    compile := hCompile
    step := StepTransport.of_compilers hScoped hLower hCompile
    exactTail :=
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩ }⟩

namespace SelectedCallee

/-- Compiler-owned artifact for the source function selected by one call. -/
structure Artifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (name : Functions.Name) (fn : Functions.FunDef) where
  startState : AllocationSupport.CompileState
  finalState : AllocationSupport.CompileState
  proc : Locals.Proc
  lowerProc : Expressions.Proc
  slots : AllocationSupport.FunSlots
  planEntry : AllocationSupport.ScopedAllocation
  lower :
    AllocationLowering.lowerFunction? compilation.recipe
        compilation.stackSlots compilation.frameName
        (AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords)
        startState fn =
      some (proc, finalState)
  compile : proc.toExpressions? = some lowerProc
  targetLookup :
    Structured.ProcList.lookup? name expressions.toStructured.procs =
      some lowerProc.toStructured
  slotsLookup :
    AllocationSupport.lookupFun? fn.name
        compilation.recipe.functionSlots =
      some slots
  slotsMatch : slots.Matches fn
  planEntryMem : planEntry ∈ compilation.recipe.functions
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
        entry ∈ compilation.recipe.lexicalScopes
  sourceName : fn.name = name
  sourceMem : fn ∈ program.functions

/-- Construct a selected callee solely from source lookup and real lowering. -/
theorem Artifact.of_find
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (hFind :
      Functions.Source.FunList.find? name program.functions = some fn) :
    Nonempty (Artifact compilation name fn) := by
  obtain
      ⟨recipe, stackSlots, frameName, before, after, proc, lowerProc,
        selectedSlots, planEntry, hValidate, hFresh, hSelected, hCompile,
        hLookup, hSelectedSlots, hPlanEntryMem, hPlanEntryScope,
        hPlanEntryState, hBodyScopesMem⟩ :=
    AllocationLowering.lowerExpressionsFromAllocation?_find_compiled_function
      compilation.lower hFind
  have hValidated :
      (recipe, stackSlots) =
        (compilation.recipe, compilation.stackSlots) := by
    exact Option.some.inj (hValidate.symm.trans compilation.validate)
  cases hValidated
  have hFrame : frameName = compilation.frameName := by
    exact Option.some.inj (hFresh.symm.trans compilation.fresh)
  subst frameName
  have hMem : fn ∈ program.functions :=
    Functions.Source.FunList.mem_of_find?_eq_some hFind
  obtain
      ⟨slots, _entry, _added, hSlotsLookup, hSlotsMatch,
        _hEntry, _hScope, _hEnv, _hPlan⟩ :=
    AllocationLowering.validatePlan?_function_components
      compilation.validate hMem
  have hSlotsEq : slots = selectedSlots := by
    rw [hSelectedSlots] at hSlotsLookup
    exact (Option.some.inj hSlotsLookup).symm
  subst slots
  exact
    ⟨{ startState := before
       finalState := after
       proc := proc
       lowerProc := lowerProc
       slots := selectedSlots
       planEntry := planEntry
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
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (_artifact : Artifact compilation name fn) :
    Locals.Allocation.ScopeId :=
  .function fn.name

def Artifact.scratchBindings
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    List (Locals.Name × Nat) :=
  AllocationLowering.scratchBindingsForRoot
    compilation.recipe compilation.stackSlots artifact.root

def Artifact.needsFrame
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : Bool :=
  !artifact.scratchBindings.isEmpty

def Artifact.lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    AllocationLowering.Ctx :=
  compilation.lowerCtx artifact.root artifact.scratchBindings

theorem Artifact.lowerCtxShared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    compilation.CtxShared artifact.lowerCtx :=
  compilation.lowerCtx_shared artifact.root artifact.scratchBindings

/-- A caller lookup through any context owned by the same compilation selects
the exact slots carried by the compiler-selected callee artifact. -/
theorem Artifact.slots_eq_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    {callerCtx : AllocationLowering.Ctx}
    (hCaller : compilation.CtxShared callerCtx)
    {slots : AllocationSupport.FunSlots}
    (hLookup :
      AllocationSupport.lookupFun? name callerCtx.functions = some slots) :
    slots = artifact.slots := by
  have hArtifactLookup :
      AllocationSupport.lookupFun? name callerCtx.functions =
        some artifact.slots := by
    rw [hCaller.functions]
    simpa [artifact.sourceName] using artifact.slotsLookup
  rw [hArtifactLookup] at hLookup
  exact (Option.some.inj hLookup).symm

/-- The ordinary caller frame classification agrees with the selected callee's
compiler-owned scratch bindings. -/
theorem Artifact.mem_frameFunctions_iff
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    {callerCtx : AllocationLowering.Ctx}
    (hCaller : compilation.CtxShared callerCtx) :
    name ∈ callerCtx.frameFunctions ↔ artifact.needsFrame = true := by
  rw [hCaller.frameFunctions]
  have hLookup :
      AllocationSupport.lookupFun? name compilation.recipe.functionSlots =
        some artifact.slots := by
    simpa [artifact.sourceName] using artifact.slotsLookup
  simpa [Artifact.needsFrame, Artifact.scratchBindings, Artifact.root,
    AllocationLowering.functionNeedsFrame,
    AllocationLowering.rootNeedsFrame, artifact.sourceName] using
    (AllocationLowering.mem_frameFunctions_iff_of_lookup hLookup)

/-- A selected scratch-backed callee has a positive checked frame size. -/
theorem Artifact.config_frameWords_pos
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    {config : AllocationSupport.ScratchFrameConfig}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hNeedsFrame : artifact.needsFrame = true) :
    0 < config.frameWords := by
  have hRootNeeds :
      AllocationLowering.rootNeedsFrame compilation.recipe
          compilation.stackSlots artifact.root = true := by
    unfold AllocationLowering.rootNeedsFrame
    simpa only [Artifact.needsFrame, Artifact.scratchBindings] using hNeedsFrame
  have hPositive : 0 < compilation.recipe.frameWords :=
    AllocationLowering.frameWords_pos_of_validate_of_rootNeedsFrame
      compilation.validate hRootNeeds
  obtain
      ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
        hWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  rw [hWords]
  exact hPositive

theorem Artifact.planEntry_env_extension
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
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
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    compilation.frameName ∉ artifact.planEntry.state.env.map Prod.fst := by
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      compilation.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨compilation.recipe, by simp [hRecipe], artifact.planEntry, ?_, hFrame⟩
  simp only [AllocationLowering.scopedStates, List.mem_cons,
    List.mem_append]
  exact Or.inl (Or.inr artifact.planEntryMem)

theorem Artifact.frameName_not_mem_lexical_entry_env
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    {entry : AllocationSupport.ScopedAllocation}
    (hEntry : entry ∈ compilation.recipe.lexicalScopes) :
    compilation.frameName ∉ entry.state.env.map Prod.fst := by
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      compilation.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨compilation.recipe, by simp [hRecipe], entry, ?_, hFrame⟩
  simp only [AllocationLowering.scopedStates, List.mem_cons,
    List.mem_append]
  exact Or.inr hEntry

def Artifact.entryLayout
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : Locals.Layout :=
  fn.params.reverse ++
    if artifact.needsFrame then [compilation.frameName] else []

def Artifact.entryCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : Locals.Ctx :=
  Locals.Ctx.procEntryWithLayoutAndRetc
    artifact.entryLayout fn.returns.length

def Artifact.bodyStart
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
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
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : List Locals.Stmt :=
  [AllocationLowering.bindEntryLayout artifact.entryLayout] ++
    if artifact.needsFrame then
      [AllocationLowering.bindScratchBindings
        fn.params.length artifact.scratchBindings]
    else
      []

def Artifact.mode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : ActivationMode :=
  if artifact.needsFrame then
    .scratch 0 compilation.recipe.frameWords
  else
    .stack

/-- Minimal compiler-prepared view needed by call and body preservation. -/
structure Prepared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) where
  plan : Locals.Allocation.Plan
  paramCtx : Locals.Ctx
  returnCtx : Locals.Ctx
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
  planLookup : allocation.find? (.function fn.name) = some plan
  planEq :
    plan =
      MixedAllocation.allocationOfState
        program.memoryContract compilation.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots artifact.planEntry.scope
          artifact.planEntry.state)
        artifact.planEntry.state
  planWF : plan.WellFormed
  bodyPlan : artifact.planEntry.state = bodyFinal.allocation
  signatureNodup :
    ((artifact.slots.returns ++ artifact.slots.params).map Prod.fst).Nodup
  frameFresh :
    compilation.frameName ∉
      (artifact.slots.returns ++ artifact.slots.params).map Prod.fst
  paramLayout :
    paramCtx.layout =
      AllocationInteractionRelation.currentStackOrder plan
          (artifact.slots.params.map Prod.fst).reverse ++
        if artifact.needsFrame then [compilation.frameName] else []
  bodyLayout :
    returnCtx.layout =
      AllocationInteractionRelation.currentStackOrder plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse) ++
        if artifact.needsFrame then [compilation.frameName] else []
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
    Locals.Block.compileOpen returnCtx body = some (bodyCode, bodyCtx)
  compileReturnValues :
    Locals.ExprSeq.compileCode bodyCtx 0 returnValues =
      some returnValueCode
  compileCleanup :
    bodyCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup
  procName : artifact.lowerProc.name = fn.name
  procArgc :
    artifact.lowerProc.argc =
      fn.params.length + (if artifact.needsFrame then 1 else 0)
  procRetc : artifact.lowerProc.retc = fn.returns.length
  procBody :
    artifact.lowerProc.body.stmts =
      markerCode ++ paramCode ++ returnCode ++ bodyCode ++
        Locals.codeStmt returnValueCode ++ Locals.codeStmt cleanup

def Prepared.bodyMode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) : ActivationMode :=
  artifact.mode.atStackDepth
    (currentStackOrder prepared.plan
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)).length

theorem Artifact.prepare
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
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
  let plan :=
    MixedAllocation.allocationOfState
      program.memoryContract compilation.recipe.frameWords
      (MixedAllocation.AllocationRecipe.stackEntriesForScope
        compilation.recipe compilation.stackSlots artifact.planEntry.scope
        artifact.planEntry.state)
      artifact.planEntry.state
  have hEntryPlan :=
    AllocationLowering.validatePlan?_function_entry_plan
      compilation.validate artifact.planEntryMem
  have hPlanLookup :
      allocation.find? (.function fn.name) = some plan := by
    simpa [plan, artifact.planEntryScope] using hEntryPlan
  have hPlanWF : plan.WellFormed :=
    Locals.Allocation.ProgramPlan.wellFormed_of_find?_eq_some
      (AllocationLowering.validatePlan?_sound compilation.validate).1
      hPlanLookup
  have hCompileParams' :
      Locals.Block.compileOpen artifact.entryCtx
          { stmts :=
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).1 } =
        some (paramCode, paramCtx) := by
    simpa [Artifact.lowerCtx, Artifact.entryCtx, Artifact.entryLayout,
      Artifact.root, Artifact.scratchBindings, Artifact.needsFrame] using
      hCompileParams
  have hCompileReturns' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              (AllocationLowering.lowerReturns artifact.lowerCtx
                artifact.slots.returns paramCtx.layout).1 } =
        some (returnCode, returnCtx) := by
    simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using hCompileReturns
  have hParamActualLayout :
      paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryCtx.layout).2 :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      hCompileParams'
  have hReturnActualLayout :
      returnCtx.layout =
        (AllocationLowering.lowerReturns artifact.lowerCtx
          artifact.slots.returns paramCtx.layout).2 :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      hCompileReturns'
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  have hSourceSignature :=
    AllocationSupport.planRecipeCore?_function_signature_valid
      hRecipe artifact.sourceMem
  have hSignatureNodup :
      ((artifact.slots.returns ++ artifact.slots.params).map Prod.fst).Nodup := by
    simpa [List.map_append, artifact.slotsMatch.2.1,
      artifact.slotsMatch.2.2] using hSourceSignature.1
  have hSignatureParts :=
    List.nodup_append.mp (by
      simpa [List.map_append] using hSignatureNodup)
  have hParamsNodup :
      (artifact.slots.params.map Prod.fst).Nodup := hSignatureParts.2.1
  have hFrameFreshParams :
      compilation.frameName ∉ artifact.slots.params.map Prod.fst := by
    intro hFrame
    apply AllocationLowering.freshFrameName_not_mem_params
      compilation.fresh artifact.sourceMem
    rw [← artifact.slotsMatch.2.1]
    exact hFrame
  have hFrameFreshReturns :
      compilation.frameName ∉ artifact.slots.returns.map Prod.fst := by
    intro hFrame
    apply AllocationLowering.freshFrameName_not_mem_returns
      compilation.fresh artifact.sourceMem
    rw [← artifact.slotsMatch.2.2]
    exact hFrame
  have hFrameFresh :
      compilation.frameName ∉
        (artifact.slots.returns ++ artifact.slots.params).map Prod.fst := by
    simpa [List.map_append, hFrameFreshReturns, hFrameFreshParams]
  obtain ⟨added, hEntryEnv⟩ := artifact.planEntry_env_extension
  have hEntryEnv' :
      artifact.planEntry.state.env =
        added ++ artifact.slots.returns ++ artifact.slots.params := by
    simpa [AllocationSupport.functionEnv, List.append_assoc] using hEntryEnv
  have hStateNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    simpa [plan, MixedAllocation.allocationOfState] using hPlanWF.2.1
  have hEntries :
      MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots artifact.planEntry.scope
          artifact.planEntry.state =
        MixedAllocation.stackEntries compilation.stackSlots added ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.params.reverse := by
    rw [artifact.planEntryScope]
    exact
      MixedAllocation.AllocationRecipe.stackEntriesForScope_function_of_env_extension
        artifact.slotsLookup hEntryEnv
  have hParameterOrder :
      currentStackOrder plan
          (artifact.slots.params.map Prod.fst).reverse =
        MixedAllocation.stackOrder compilation.stackSlots
          artifact.slots.params.reverse := by
    have hOrder :=
      MixedAllocation.allocationOfState_parameter_stack_filter
        (contract := program.memoryContract)
        (frameWords := compilation.recipe.frameWords)
        (stackSlots := compilation.stackSlots)
        (state := artifact.planEntry.state)
        (added := added) (returns := artifact.slots.returns)
        (params := artifact.slots.params)
        (processed := artifact.slots.params) (pending := [])
        hEntryEnv' hStateNodup (by simp)
    simpa [plan, currentStackOrder, hEntries] using hOrder
  have hBodyOrder :
      currentStackOrder plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse) =
        MixedAllocation.stackOrder compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackOrder compilation.stackSlots
            artifact.slots.params.reverse := by
    have hOrder :=
      MixedAllocation.allocationOfState_return_stack_filter
        (contract := program.memoryContract)
        (frameWords := compilation.recipe.frameWords)
        (stackSlots := compilation.stackSlots)
        (state := artifact.planEntry.state)
        (added := added) (returns := artifact.slots.returns)
        (params := artifact.slots.params)
        (processed := artifact.slots.returns) (pending := [])
        hEntryEnv' hStateNodup (by simp)
    simpa [plan, currentStackOrder, hEntries] using hOrder
  have hParamLayout :
      paramCtx.layout =
        currentStackOrder plan
            (artifact.slots.params.map Prod.fst).reverse ++
          if artifact.needsFrame then [compilation.frameName] else [] := by
    by_cases hNeedsFrame : artifact.needsFrame = true
    · have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse ++
              [compilation.frameName] := by
        change artifact.entryLayout = _
        rw [show artifact.entryLayout =
            fn.params.reverse ++ [compilation.frameName] by
          simp [Artifact.entryLayout, hNeedsFrame]]
        rw [artifact.slotsMatch.2.1]
      have hParamPure :=
        AllocationLowering.lowerParams_layout_eq_stackOrder
          (ctx := artifact.lowerCtx) (params := artifact.slots.params)
          (suffix := [compilation.frameName]) hParamsNodup
          (by
            intro localName hParam hFrame
            simp only [List.mem_singleton] at hFrame
            subst localName
            exact hFrameFreshParams hParam)
      rw [if_pos hNeedsFrame]
      calc
        paramCtx.layout =
            (AllocationLowering.lowerParams artifact.lowerCtx
              artifact.slots.params artifact.entryCtx.layout).2 :=
          hParamActualLayout
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse ++
              [compilation.frameName] := by
          simpa [hEntryLayout, Artifact.lowerCtx] using hParamPure
        _ =
            currentStackOrder plan
                (artifact.slots.params.map Prod.fst).reverse ++
              [compilation.frameName] := by rw [hParameterOrder]
    · have hNeedsFrameFalse : artifact.needsFrame = false :=
        Bool.eq_false_of_not_eq_true hNeedsFrame
      have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse := by
        change artifact.entryLayout = _
        rw [show artifact.entryLayout = fn.params.reverse by
          simp [Artifact.entryLayout, hNeedsFrameFalse]]
        rw [artifact.slotsMatch.2.1]
      have hParamPure :=
        AllocationLowering.lowerParams_layout_eq_stackOrder
          (ctx := artifact.lowerCtx) (params := artifact.slots.params)
          (suffix := []) hParamsNodup (by simp)
      rw [if_neg hNeedsFrame]
      calc
        paramCtx.layout =
            (AllocationLowering.lowerParams artifact.lowerCtx
              artifact.slots.params artifact.entryCtx.layout).2 :=
          hParamActualLayout
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
              artifact.slots.params.reverse := by
          simpa [hEntryLayout, Artifact.lowerCtx] using hParamPure
        _ =
            currentStackOrder plan
              (artifact.slots.params.map Prod.fst).reverse :=
          hParameterOrder.symm
        _ = _ ++ [] := by simp
  have hBodyLayout :
      returnCtx.layout =
        currentStackOrder plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse) ++
          if artifact.needsFrame then [compilation.frameName] else [] := by
    by_cases hNeedsFrame : artifact.needsFrame = true
    · have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse ++
              [compilation.frameName] := by
        change artifact.entryLayout = _
        rw [show artifact.entryLayout =
            fn.params.reverse ++ [compilation.frameName] by
          simp [Artifact.entryLayout, hNeedsFrame]]
        rw [artifact.slotsMatch.2.1]
      have hParamPure :=
        AllocationLowering.lowerParams_layout_eq_stackOrder
          (ctx := artifact.lowerCtx) (params := artifact.slots.params)
          (suffix := [compilation.frameName]) hParamsNodup
          (by
            intro localName hParam hFrame
            simp only [List.mem_singleton] at hFrame
            subst localName
            exact hFrameFreshParams hParam)
      have hParamLayout :
          paramCtx.layout =
            currentStackOrder plan
                (artifact.slots.params.map Prod.fst).reverse ++
              [compilation.frameName] := by
        calc
          paramCtx.layout =
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).2 :=
            hParamActualLayout
          _ =
              MixedAllocation.stackOrder compilation.stackSlots
                  artifact.slots.params.reverse ++
                [compilation.frameName] := by
            simpa [hEntryLayout, Artifact.lowerCtx] using hParamPure
          _ =
              currentStackOrder plan
                  (artifact.slots.params.map Prod.fst).reverse ++
                [compilation.frameName] := by rw [hParameterOrder]
      have hReturnPure :=
        AllocationLowering.lowerReturns_layout_eq_stackOrder
          artifact.lowerCtx artifact.slots.returns paramCtx.layout
      rw [if_pos hNeedsFrame]
      calc
        returnCtx.layout =
            (AllocationLowering.lowerReturns artifact.lowerCtx
              artifact.slots.returns paramCtx.layout).2 :=
          hReturnActualLayout
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              paramCtx.layout := by
          simpa [Artifact.lowerCtx] using hReturnPure
        _ =
            (MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse) ++
              [compilation.frameName] := by
          rw [hParamLayout, hParameterOrder, List.append_assoc]
        _ =
            currentStackOrder plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse) ++
              [compilation.frameName] := by rw [hBodyOrder]
    · have hNeedsFrameFalse : artifact.needsFrame = false :=
        Bool.eq_false_of_not_eq_true hNeedsFrame
      have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse := by
        change artifact.entryLayout = _
        rw [show artifact.entryLayout = fn.params.reverse by
          simp [Artifact.entryLayout, hNeedsFrameFalse]]
        rw [artifact.slotsMatch.2.1]
      have hParamPure :=
        AllocationLowering.lowerParams_layout_eq_stackOrder
          (ctx := artifact.lowerCtx) (params := artifact.slots.params)
          (suffix := []) hParamsNodup (by simp)
      have hParamLayout :
          paramCtx.layout =
            currentStackOrder plan
              (artifact.slots.params.map Prod.fst).reverse := by
        calc
          paramCtx.layout =
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).2 :=
            hParamActualLayout
          _ =
              MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse := by
            simpa [hEntryLayout, Artifact.lowerCtx] using hParamPure
          _ =
              currentStackOrder plan
                (artifact.slots.params.map Prod.fst).reverse :=
            hParameterOrder.symm
      have hReturnPure :=
        AllocationLowering.lowerReturns_layout_eq_stackOrder
          artifact.lowerCtx artifact.slots.returns paramCtx.layout
      rw [if_neg hNeedsFrame]
      calc
        returnCtx.layout =
            (AllocationLowering.lowerReturns artifact.lowerCtx
              artifact.slots.returns paramCtx.layout).2 :=
          hReturnActualLayout
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              paramCtx.layout := by
          simpa [Artifact.lowerCtx] using hReturnPure
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse := by
          rw [hParamLayout, hParameterOrder]
        _ =
            currentStackOrder plan
              ((artifact.slots.returns.map Prod.fst).reverse ++
                (artifact.slots.params.map Prod.fst).reverse) :=
          hBodyOrder.symm
        _ = _ ++ [] := by simp
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
       planLookup := hPlanLookup
       planEq := rfl
       planWF := hPlanWF
       bodyPlan := hBodyPlan
       signatureNodup := hSignatureNodup
       frameFresh := hFrameFresh
       paramLayout := hParamLayout
       bodyLayout := hBodyLayout
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
  · simpa [Artifact.lowerCtx, Artifact.bodyStart, Artifact.entryLayout,
      Artifact.root, Artifact.scratchBindings, Artifact.needsFrame] using
      hLowerBody
  · simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using
      hLowerReturnValues
  · simpa [Artifact.markers, Artifact.entryCtx, Artifact.entryLayout,
      Artifact.needsFrame, Artifact.scratchBindings] using hCompileMarkers
  · simpa [Artifact.needsFrame, Artifact.scratchBindings,
      Artifact.root] using hProcArgc

theorem Prepared.bodyStartLayout
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    artifact.bodyStart.layout = prepared.returnCtx.layout := by
  have hParam :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturn :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  change
    (AllocationLowering.lowerReturns artifact.lowerCtx
      artifact.slots.returns
      (AllocationLowering.lowerParams artifact.lowerCtx
        artifact.slots.params artifact.entryLayout).2).2 =
      prepared.returnCtx.layout
  have hEntryLayout : artifact.entryCtx.layout = artifact.entryLayout := rfl
  rw [← hEntryLayout, ← hParam]
  exact hReturn.symm

theorem Prepared.location_stack_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {calleeName : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          name artifact.bodyStart.allocation.env =
        some slot)
    (hStack :
      AllocationLowering.isStackSlot artifact.lowerCtx slot = true) :
    ∃ depth,
      prepared.plan.location? name = some (.stack depth) := by
  have hMemBody :
      (name, slot) ∈ artifact.bodyStart.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hMemEntry : (name, slot) ∈ artifact.planEntry.state.env := by
    rw [hEnv]
    exact List.mem_append_right added hMemBody
  have hSlot : slot ∈ compilation.stackSlots := by
    have hSlotCtx :=
      (AllocationLowering.isStackSlot_eq_true_iff
        artifact.lowerCtx slot).mp hStack
    rwa [artifact.lowerCtxShared.stackSlots] at hSlotCtx
  have hEntry :
      (name, slot) ∈
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots
          artifact.planEntry.scope artifact.planEntry.state := by
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
    {compilation : Compilation allocation program expressions}
    {calleeName : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          name artifact.bodyStart.allocation.env =
        some slot)
    (hScratch :
      AllocationLowering.isStackSlot artifact.lowerCtx slot = false) :
    prepared.plan.location? name = some (.scratch slot) := by
  have hMemBody :
      (name, slot) ∈ artifact.bodyStart.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hMemEntry : (name, slot) ∈ artifact.planEntry.state.env := by
    rw [hEnv]
    exact List.mem_append_right added hMemBody
  have hSlot : slot ∉ compilation.stackSlots := by
    have hSlotCtx :=
      (AllocationLowering.isStackSlot_eq_false_iff
        artifact.lowerCtx slot).mp hScratch
    rwa [artifact.lowerCtxShared.stackSlots] at hSlotCtx
  have hNotEntry :
      (name, slot) ∉
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots
          artifact.planEntry.scope artifact.planEntry.state :=
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

theorem Prepared.bodyCompiler
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {calleeName : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation calleeName fn}
    (prepared : Prepared artifact) :
    AllocationContext.ActivationExprContext artifact.lowerCtx
      artifact.bodyStart prepared.returnCtx prepared.plan
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      prepared.bodyMode := by
  let live :=
    (artifact.slots.returns.map Prod.fst).reverse ++
      (artifact.slots.params.map Prod.fst).reverse
  have hLayout :
      prepared.returnCtx.layout = artifact.bodyStart.layout :=
    prepared.bodyStartLayout.symm
  have bindingOfLive :
      ∀ localName, localName ∈ live →
        ∃ slot,
          (localName, slot) ∈
            artifact.slots.returns ++ artifact.slots.params := by
    intro localName hLive
    have hName :
        localName ∈
          (artifact.slots.returns ++ artifact.slots.params).map Prod.fst := by
      simpa [live, List.map_append] using hLive
    rcases List.mem_map.mp hName with ⟨binding, hBinding, hEq⟩
    rcases binding with ⟨candidate, slot⟩
    simp only at hEq
    subst candidate
    exact ⟨slot, hBinding⟩
  have slotLookup :
      ∀ localName, localName ∈ live →
        ∃ slot,
          AllocationSupport.lookupSlot?
              localName artifact.bodyStart.allocation.env =
            some slot := by
    intro localName hLive
    obtain ⟨slot, hBinding⟩ := bindingOfLive localName hLive
    refine ⟨slot, ?_⟩
    exact
      AllocationSupport.lookupSlot?_eq_some_of_mem
        prepared.signatureNodup hBinding
  have hFrameFresh :
      compilation.frameName ∉ currentStackOrder prepared.plan live := by
    intro hFrame
    have hFrameLive := mem_live_of_mem_currentStackOrder hFrame
    apply prepared.frameFresh
    simpa [live, List.map_append] using hFrameLive
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hBodyLayout :
        artifact.bodyStart.layout =
          currentStackOrder prepared.plan live ++
            [compilation.frameName] := by
      rw [prepared.bodyStartLayout, prepared.bodyLayout,
        if_pos hNeedsFrame]
    have hBodyMode :
        prepared.bodyMode =
          .scratch (currentStackOrder prepared.plan live).length
            compilation.recipe.frameWords := by
      simp [Prepared.bodyMode, Artifact.mode, hNeedsFrame,
        ActivationMode.atStackDepth, live]
    rw [hBodyMode]
    apply AllocationContext.ActivationExprContext.scratch_of_layout
      prepared.planWF hLayout hBodyLayout
      (by simpa only [live]) hFrameFresh
    · exact slotLookup
    · intro localName slot hLive hLookup hStack
      exact prepared.location_stack_of_lookup hLookup hStack
    · intro localName slot hLive hLookup hScratch
      exact prepared.location_scratch_of_lookup hLookup hScratch
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hBodyLayout :
        artifact.bodyStart.layout =
          currentStackOrder prepared.plan live := by
      rw [prepared.bodyStartLayout, prepared.bodyLayout,
        if_neg hNeedsFrame]
      simpa only [live, List.append_nil]
    have hRootNoFrame :
        AllocationLowering.rootNeedsFrame compilation.recipe
            compilation.stackSlots (.function fn.name) = false := by
      simpa [Artifact.needsFrame, Artifact.scratchBindings, Artifact.root,
        AllocationLowering.rootNeedsFrame] using hNeedsFrameFalse
    have allStack :
        ∀ localName slot,
          localName ∈ live →
          AllocationSupport.lookupSlot?
              localName artifact.bodyStart.allocation.env =
            some slot →
          AllocationLowering.isStackSlot artifact.lowerCtx slot = true := by
      intro localName slot hLive hLookup
      have hMemBody :=
        AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
      obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
      have hMemEntry :
          (localName, slot) ∈ artifact.planEntry.state.env := by
        rw [hEnv]
        exact List.mem_append_right added hMemBody
      have hSlot :=
        AllocationLowering.slot_mem_of_function_rootNeedsFrame_eq_false
          artifact.planEntryMem artifact.planEntryScope hMemEntry hRootNoFrame
      simpa [AllocationLowering.isStackSlot, Artifact.lowerCtx,
        Compilation.lowerCtx] using hSlot
    have stackLocation :
        ∀ localName, localName ∈ live →
          ∃ planDepth,
            prepared.plan.location? localName = some (.stack planDepth) := by
      intro localName hLive
      obtain ⟨slot, hLookup⟩ := slotLookup localName hLive
      exact prepared.location_stack_of_lookup hLookup
        (allStack localName slot hLive hLookup)
    have stackOnly : LiveStackOnly prepared.plan live := by
      intro localName slot hLive hScratchLocation
      obtain ⟨planDepth, hStackLocation⟩ :=
        stackLocation localName hLive
      rw [hStackLocation] at hScratchLocation
      simp at hScratchLocation
    have hFrameAbsent :
        artifact.lowerCtx.frameName ∉ artifact.bodyStart.layout := by
      rw [hBodyLayout]
      simpa [Artifact.lowerCtx, Compilation.lowerCtx] using hFrameFresh
    have hBodyMode : prepared.bodyMode = .stack := by
      simp [Prepared.bodyMode, Artifact.mode, hNeedsFrameFalse,
        ActivationMode.atStackDepth]
    rw [hBodyMode]
    apply AllocationContext.ActivationExprContext.stack_of_layout
      prepared.planWF hLayout hBodyLayout.symm hFrameAbsent stackOnly
      stackLocation slotLookup

theorem Artifact.bodyScoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    (hProgramScoped : program.Scoped) :
    Functions.Scope.Block.Scoped
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      fn.body := by
  have hFnScoped : fn.Scoped :=
    Functions.FunList.scoped_of_mem hProgramScoped.1 artifact.sourceMem
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

theorem Prepared.parameterPlacement
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    ParameterPrelude.Placement artifact.lowerCtx prepared.plan
      compilation.recipe.frameWords [] artifact.slots.params := by
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hEnv' :
      artifact.planEntry.state.env =
        added ++ artifact.slots.returns ++ artifact.slots.params := by
    simpa [AllocationSupport.functionEnv, List.append_assoc] using hEnv
  have hStateNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    simpa [prepared.planEq, MixedAllocation.allocationOfState] using
      prepared.planWF.2.1
  have hParamsNodup : (artifact.slots.params.map Prod.fst).Nodup := by
    exact
      (List.nodup_append.mp (by
        simpa [List.map_append] using prepared.signatureNodup)).2.1
  have hEntries :
      MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots artifact.planEntry.scope
          artifact.planEntry.state =
        MixedAllocation.stackEntries compilation.stackSlots added ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.params.reverse := by
    rw [artifact.planEntryScope]
    exact
      MixedAllocation.AllocationRecipe.stackEntriesForScope_function_of_env_extension
        artifact.slotsLookup hEnv
  have hPlanEq :
      prepared.plan =
        MixedAllocation.allocationOfState program.memoryContract
          compilation.recipe.frameWords
          (MixedAllocation.stackEntries compilation.stackSlots added ++
            MixedAllocation.stackEntries compilation.stackSlots
              artifact.slots.returns.reverse ++
            MixedAllocation.stackEntries compilation.stackSlots
              artifact.slots.params.reverse)
          artifact.planEntry.state := by
    rw [prepared.planEq, hEntries]
  have hExplicitWF :
      (MixedAllocation.allocationOfState program.memoryContract
        compilation.recipe.frameWords
        (MixedAllocation.stackEntries compilation.stackSlots added ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.params.reverse)
        artifact.planEntry.state).WellFormed := by
    rw [← hPlanEq]
    exact prepared.planWF
  have hPlacement :=
    ParameterPrelude.Placement.parameters
      artifact.lowerCtxShared.stackSlots hEnv' hStateNodup hParamsNodup
      hExplicitWF
  rw [← hPlanEq] at hPlacement
  exact hPlacement

theorem Prepared.returnPlacement
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    ParameterPrelude.Placement artifact.lowerCtx prepared.plan
      compilation.recipe.frameWords
      (artifact.slots.params.map Prod.fst).reverse
      artifact.slots.returns := by
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hEnv' :
      artifact.planEntry.state.env =
        added ++ artifact.slots.returns ++ artifact.slots.params := by
    simpa [AllocationSupport.functionEnv, List.append_assoc] using hEnv
  have hStateNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    simpa [prepared.planEq, MixedAllocation.allocationOfState] using
      prepared.planWF.2.1
  have hEntries :
      MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots artifact.planEntry.scope
          artifact.planEntry.state =
        MixedAllocation.stackEntries compilation.stackSlots added ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.params.reverse := by
    rw [artifact.planEntryScope]
    exact
      MixedAllocation.AllocationRecipe.stackEntriesForScope_function_of_env_extension
        artifact.slotsLookup hEnv
  have hPlanEq :
      prepared.plan =
        MixedAllocation.allocationOfState program.memoryContract
          compilation.recipe.frameWords
          (MixedAllocation.stackEntries compilation.stackSlots added ++
            MixedAllocation.stackEntries compilation.stackSlots
              artifact.slots.returns.reverse ++
            MixedAllocation.stackEntries compilation.stackSlots
              artifact.slots.params.reverse)
          artifact.planEntry.state := by
    rw [prepared.planEq, hEntries]
  have hExplicitWF :
      (MixedAllocation.allocationOfState program.memoryContract
        compilation.recipe.frameWords
        (MixedAllocation.stackEntries compilation.stackSlots added ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.params.reverse)
        artifact.planEntry.state).WellFormed := by
    rw [← hPlanEq]
    exact prepared.planWF
  have hPlacement :=
    ParameterPrelude.Placement.returns
      artifact.lowerCtxShared.stackSlots hEnv' hStateNodup
      prepared.signatureNodup hExplicitWF
  rw [← hPlanEq] at hPlacement
  exact hPlacement

theorem Artifact.paramsAllStack_of_needsFrame_false
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    (hNeedsFrame : artifact.needsFrame = false) :
    ∀ binding, binding ∈ artifact.slots.params →
      AllocationLowering.isStackSlot artifact.lowerCtx binding.2 = true := by
  have hRootNoFrame :
      AllocationLowering.rootNeedsFrame compilation.recipe
          compilation.stackSlots (.function fn.name) = false := by
    simpa [Artifact.needsFrame, Artifact.scratchBindings, Artifact.root,
      AllocationLowering.rootNeedsFrame] using hNeedsFrame
  intro binding hBinding
  rcases binding with ⟨localName, slot⟩
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hMemEntry :
      (localName, slot) ∈ artifact.planEntry.state.env := by
    rw [hEnv]
    simp [AllocationSupport.functionEnv, hBinding]
  have hSlot :=
    AllocationLowering.slot_mem_of_function_rootNeedsFrame_eq_false
      artifact.planEntryMem artifact.planEntryScope hMemEntry hRootNoFrame
  simpa [AllocationLowering.isStackSlot, Artifact.lowerCtx,
    Compilation.lowerCtx] using hSlot

theorem Artifact.returnsAllStack_of_needsFrame_false
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    (hNeedsFrame : artifact.needsFrame = false) :
    ∀ binding, binding ∈ artifact.slots.returns →
      AllocationLowering.isStackSlot artifact.lowerCtx binding.2 = true := by
  have hRootNoFrame :
      AllocationLowering.rootNeedsFrame compilation.recipe
          compilation.stackSlots (.function fn.name) = false := by
    simpa [Artifact.needsFrame, Artifact.scratchBindings, Artifact.root,
      AllocationLowering.rootNeedsFrame] using hNeedsFrame
  intro binding hBinding
  rcases binding with ⟨localName, slot⟩
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hMemEntry :
      (localName, slot) ∈ artifact.planEntry.state.env := by
    rw [hEnv]
    simp [AllocationSupport.functionEnv, hBinding]
  have hSlot :=
    AllocationLowering.slot_mem_of_function_rootNeedsFrame_eq_false
      artifact.planEntryMem artifact.planEntryScope hMemEntry hRootNoFrame
  simpa [AllocationLowering.isStackSlot, Artifact.lowerCtx,
    Compilation.lowerCtx] using hSlot

theorem Prepared.parameterContext
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    ParameterPrelude.Context artifact.lowerCtx prepared.plan
      compilation.recipe.frameWords [] artifact.slots.params 0
      artifact.entryCtx := by
  have hPlacement := prepared.parameterPlacement
  have hParamsNodup : (artifact.slots.params.map Prod.fst).Nodup := by
    exact
      (List.nodup_append.mp (by
        simpa [List.map_append] using prepared.signatureNodup)).2.1
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hLayout :
        artifact.entryCtx.layout =
          (artifact.slots.params.map Prod.fst).reverse ++
            currentStackOrder prepared.plan [] ++
            [artifact.lowerCtx.frameName] := by
      simp [Artifact.entryCtx, Artifact.entryLayout, hNeedsFrame,
        artifact.slotsMatch.2.1, Artifact.lowerCtx, Compilation.lowerCtx,
        currentStackOrder, List.append_assoc,
        Locals.Ctx.procEntryWithLayoutAndRetc,
        Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
        Locals.Ctx.initial]
    have hNodup : artifact.entryCtx.layout.Nodup := by
      have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse ++
              [artifact.lowerCtx.frameName] := by
        simp [Artifact.entryCtx, Artifact.entryLayout, hNeedsFrame,
          artifact.slotsMatch.2.1, Artifact.lowerCtx, Compilation.lowerCtx,
          Locals.Ctx.procEntryWithLayoutAndRetc,
          Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
          Locals.Ctx.initial]
      rw [hEntryLayout]
      apply List.nodup_append.mpr
      refine ⟨by simpa using hParamsNodup, by simp, ?_⟩
      intro localName hParam frame hFrame hEq
      simp only [List.mem_singleton] at hFrame
      subst frame
      subst localName
      have hParam' :
          compilation.frameName ∈ artifact.slots.params.map Prod.fst := by
        simpa using hParam
      apply prepared.frameFresh
      simp [List.map_append, hParam']
    exact
      ParameterPrelude.Context.of_placement hPlacement hLayout hNodup
        (by simp [currentStackOrder]) prepared.compileParams
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hAllStack :
        ∀ binding, binding ∈ artifact.slots.params →
          AllocationLowering.isStackSlot artifact.lowerCtx binding.2 = true :=
      artifact.paramsAllStack_of_needsFrame_false hNeedsFrameFalse
    exact
      ParameterPrelude.Context.of_stack_placement hPlacement hAllStack

theorem Prepared.returnContext
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    ReturnPrelude.Context artifact.lowerCtx prepared.plan
      compilation.recipe.frameWords
      (artifact.slots.params.map Prod.fst).reverse
      artifact.slots.returns
      (currentStackOrder prepared.plan
        (artifact.slots.params.map Prod.fst).reverse).length
      prepared.paramCtx := by
  have hPlacement := prepared.returnPlacement
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hLayout :
        prepared.paramCtx.layout =
          currentStackOrder prepared.plan
              (artifact.slots.params.map Prod.fst).reverse ++
            [artifact.lowerCtx.frameName] := by
      simpa [hNeedsFrame, Artifact.lowerCtx, Compilation.lowerCtx] using
        prepared.paramLayout
    have hNodup : prepared.paramCtx.layout.Nodup := by
      rw [hLayout]
      apply List.nodup_append.mpr
      refine
        ⟨currentStackOrder_nodup prepared.planWF, by simp, ?_⟩
      intro localName hCurrent frame hFrame hEq
      simp only [List.mem_singleton] at hFrame
      subst frame
      subst localName
      apply prepared.frameFresh
      have hLive := mem_live_of_mem_currentStackOrder hCurrent
      have hLive' :
          compilation.frameName ∈ artifact.slots.params.map Prod.fst := by
        simpa [Artifact.lowerCtx, Compilation.lowerCtx] using hLive
      simp [List.map_append, hLive']
    have hFrameFresh :
        artifact.lowerCtx.frameName ∉
          artifact.slots.returns.map Prod.fst := by
      intro hFrame
      apply prepared.frameFresh
      have hFrame' :
          compilation.frameName ∈ artifact.slots.returns.map Prod.fst := by
        simpa [Artifact.lowerCtx, Compilation.lowerCtx] using hFrame
      simp [List.map_append, hFrame']
    exact
      ReturnPrelude.Context.of_placement hPlacement hLayout hNodup rfl
        hFrameFresh prepared.compileReturns
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    exact
      ReturnPrelude.Context.of_stack_placement hPlacement
        (artifact.returnsAllStack_of_needsFrame_false hNeedsFrameFalse)

theorem Prepared.parameters_forward_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase
        (.scratch 0 compilation.recipe.frameWords) source target)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation) :
    ∃ finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = prepared.paramCode.length + 1 ∧
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.paramCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase
        finalFrameDepth compilation.recipe.frameWords source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder prepared.plan
          (artifact.slots.params.map Prod.fst).reverse).length ∧
      finalTarget.evm.stack.length = prepared.paramCtx.layout.length := by
  obtain
      ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel, hFuel,
        hFuelLength, hCompile, hFinalLayout, hEvalAt, hFinalRel, hFinalDepth,
        hFinalStackLength⟩ :=
    ParameterPrelude.forward_scratch prepared.parameterContext hRel
      (by simp [currentStackOrder]) hStackLength prepared.planWF hReservation
  have hPair :
      (compiled, finalCtx) = (prepared.paramCode, prepared.paramCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileParams)
  cases hPair
  exact
    ⟨finalTarget, finalFrameDepth, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt,
      by simpa using hFinalRel, by simpa using hFinalDepth,
      hFinalStackLength⟩

theorem Prepared.parameters_forward_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length) :
    ∃ finalTarget fuel,
      0 < fuel ∧
      fuel = prepared.paramCode.length + 1 ∧
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.paramCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase .stack
        source finalTarget ∧
      finalTarget.evm.stack.length = prepared.paramCtx.layout.length := by
  obtain
      ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength, hCompile,
        hFinalLayout, hEvalAt, hFinalRel, hFinalStackLength⟩ :=
    ParameterPrelude.forward_stack prepared.parameterContext
      (artifact.paramsAllStack_of_needsFrame_false hNeedsFrame)
      hRel hStackLength
  have hPair :
      (compiled, finalCtx) = (prepared.paramCode, prepared.paramCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileParams)
  cases hPair
  exact
    ⟨finalTarget, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt,
      by simpa using hFinalRel, hFinalStackLength⟩

theorem Prepared.returns_forward_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase
        (currentStackOrder prepared.plan
          (artifact.slots.params.map Prod.fst).reverse).length
        compilation.recipe.frameWords source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = prepared.paramCtx.layout.length)
    (hReservation : contract.scratch? = some reservation) :
    ∃ finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = prepared.returnCode.length + 1 ∧
      prepared.returnCtx.layout =
        (AllocationLowering.lowerReturns artifact.lowerCtx
          artifact.slots.returns prepared.paramCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.returnCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.returnCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase finalFrameDepth compilation.recipe.frameWords
        source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder prepared.plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse)).length ∧
      finalTarget.evm.stack.length = prepared.returnCtx.layout.length := by
  obtain
      ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel, hFuel,
        hFuelLength, hCompile, hFinalLayout, hEvalAt, hFinalRel, hFinalDepth,
        hFinalStackLength⟩ :=
    ReturnPrelude.forward_scratch (targetProgram := expressions)
      prepared.returnContext hRel hZero rfl
      hStackLength prepared.planWF hReservation
  have hPair :
      (compiled, finalCtx) = (prepared.returnCode, prepared.returnCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileReturns)
  cases hPair
  exact
    ⟨finalTarget, finalFrameDepth, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt,
      hFinalRel, hFinalDepth, hFinalStackLength⟩

theorem Prepared.returns_forward_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hRel :
      ActivationStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase .stack
        source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = prepared.paramCtx.layout.length) :
    ∃ finalTarget fuel,
      0 < fuel ∧
      fuel = prepared.returnCode.length + 1 ∧
      prepared.returnCtx.layout =
        (AllocationLowering.lowerReturns artifact.lowerCtx
          artifact.slots.returns prepared.paramCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.returnCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.returnCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase .stack source finalTarget ∧
      finalTarget.evm.stack.length = prepared.returnCtx.layout.length := by
  obtain
      ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength, hCompile,
        hFinalLayout, hEvalAt, hFinalRel, hFinalStackLength⟩ :=
    ReturnPrelude.forward_stack (targetProgram := expressions)
      prepared.returnContext
      (artifact.returnsAllStack_of_needsFrame_false hNeedsFrame)
      hRel hZero hStackLength
  have hPair :
      (compiled, finalCtx) = (prepared.returnCode, prepared.returnCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileReturns)
  cases hPair
  exact
    ⟨finalTarget, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt,
      hFinalRel, hFinalStackLength⟩

/-- Exact generated shape of the compiler-selected callee-entry markers. -/
theorem Prepared.markerCode_shape
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    prepared.markerCode =
    [.code [.bindLocals 0 artifact.entryLayout]] ++
      if artifact.needsFrame then
        [.code
          (AllocationSupport.bindScratchBindingsCode
            fn.params.length artifact.scratchBindings)]
      else
        [] := by
  let generated : List Expressions.Stmt :=
    [.code [.bindLocals 0 artifact.entryLayout]] ++
      if artifact.needsFrame then
        [.code
          (AllocationSupport.bindScratchBindingsCode
            fn.params.length artifact.scratchBindings)]
      else
        []
  have hGenerated :
      Locals.Block.compileOpen artifact.entryCtx
          { stmts := artifact.markers } =
        some (generated, artifact.entryCtx) := by
    simpa [generated, Artifact.markers] using
      (EntryMarkers.compileOpen
        (localsCtx := artifact.entryCtx)
        (entryLayout := artifact.entryLayout)
        (baseDepth := fn.params.length)
        (scratchBindings := artifact.scratchBindings)
        (needsFrame := artifact.needsFrame))
  have hPair :
      (prepared.markerCode, artifact.entryCtx) =
        (generated, artifact.entryCtx) :=
    Option.some.inj (prepared.compileMarkers.symm.trans hGenerated)
  simpa [generated] using congrArg Prod.fst hPair

/-- Entry markers execute with any positive fuel reserved for their suffix. -/
theorem Prepared.markers_forward_at
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    (target : Structured.RunState)
    (tailFuel : Nat) (hTailFuel : 0 < tailFuel) :
    Expressions.InteractionSemantics.Block.openRun expressions
        (prepared.markerCode.length + tailFuel)
        { stmts := prepared.markerCode } target =
      .done (.ok (Structured.Outcome.regular target)) := by
  rw [prepared.markerCode_shape]
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hBind :
        Structured.InteractionSemantics.Code.openRun
            [.bindLocals 0 artifact.entryLayout] target =
          .done (.ok target) := by
      simpa using
        Locals.InteractionPreservation.Code.openRun_bindLocals
          0 artifact.entryLayout target
    have hScratch :
        Structured.InteractionSemantics.Code.openRun
            (AllocationSupport.bindScratchBindingsCode
              fn.params.length artifact.scratchBindings)
            target =
          .done (.ok target) :=
      EntryMarkers.openRun_bindScratchBindingsCode
        fn.params.length artifact.scratchBindings target
    have hFirst :=
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions (2 + tailFuel) [.bindLocals 0 artifact.entryLayout]
        target target (by omega) hBind
    have hSecond :=
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions (1 + tailFuel)
        (AllocationSupport.bindScratchBindingsCode
          fn.params.length artifact.scratchBindings)
        target target (by omega) hScratch
    simp only [hNeedsFrame, if_true, List.length_append,
      List.length_singleton]
    rw [Expressions.InteractionSemantics.Block.openRun_append expressions
      [Expressions.Stmt.code [.bindLocals 0 artifact.entryLayout]]
      [Expressions.Stmt.code
        (AllocationSupport.bindScratchBindingsCode
          fn.params.length artifact.scratchBindings)]
      (2 + tailFuel) target, hFirst]
    simpa using hSecond
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hBind :
        Structured.InteractionSemantics.Code.openRun
            [.bindLocals 0 artifact.entryLayout] target =
          .done (.ok target) := by
      simpa using
        Locals.InteractionPreservation.Code.openRun_bindLocals
          0 artifact.entryLayout target
    simp only [hNeedsFrameFalse, if_false, List.append_nil,
      List.length_singleton]
    exact
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions (1 + tailFuel) [.bindLocals 0 artifact.entryLayout]
        target target (by omega) hBind

/-- Execute the exact compiler-selected metadata markers at callee entry. -/
theorem Prepared.markers_forward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    (target : Structured.RunState) :
    Expressions.InteractionSemantics.Block.openRun expressions 4
        { stmts := prepared.markerCode } target =
      .done (.ok (Structured.Outcome.regular target)) := by
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hRun := prepared.markers_forward_at target 2 (by omega)
    have hLength : prepared.markerCode.length = 2 := by
      rw [prepared.markerCode_shape]
      simp [hNeedsFrame]
    simpa [hLength] using hRun
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hRun := prepared.markers_forward_at target 3 (by omega)
    have hLength : prepared.markerCode.length = 1 := by
      rw [prepared.markerCode_shape]
      simp [hNeedsFrameFalse]
    simpa [hLength] using hRun

/-- Compose marker, parameter, and return setup with exact suffix fuel. -/
theorem Prepared.prelude_forward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {target afterParams finalTarget : Structured.RunState}
    {paramFuel returnFuel : Nat}
    (hParamFuel : 0 < paramFuel)
    (hReturnFuel : 0 < returnFuel)
    (hParamFuelLength : paramFuel = prepared.paramCode.length + 1)
    (hParamRunAt :
      ∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + paramFuel)
            { stmts := prepared.paramCode } target =
          .done (.ok (Structured.Outcome.regular afterParams)))
    (hReturnRun :
      Expressions.InteractionSemantics.Block.openRun expressions returnFuel
          { stmts := prepared.returnCode } afterParams =
        .done (.ok (Structured.Outcome.regular finalTarget))) :
    ∃ preludeFuel,
      0 < preludeFuel ∧
      preludeFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions preludeFuel
          { stmts :=
              prepared.markerCode ++
                (prepared.paramCode ++ prepared.returnCode) }
          target =
        .done (.ok (Structured.Outcome.regular finalTarget)) := by
  let tailFuel := prepared.paramCode.length + returnFuel
  let preludeFuel := prepared.markerCode.length + tailFuel
  have hTailFuel : 0 < tailFuel := by
    simp [tailFuel]
    omega
  have hMarkerRun :=
    prepared.markers_forward_at target tailFuel hTailFuel
  have hParamRun :
      Expressions.InteractionSemantics.Block.openRun expressions tailFuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular afterParams)) := by
    have hRun := hParamRunAt (returnFuel - 1)
    have hFuelEq : returnFuel - 1 + paramFuel = tailFuel := by
      rw [hParamFuelLength]
      simp only [tailFuel]
      omega
    simpa [hFuelEq] using hRun
  have hParamReturnRun :
      Expressions.InteractionSemantics.Block.openRun expressions tailFuel
          { stmts := prepared.paramCode ++ prepared.returnCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) := by
    rw [Expressions.InteractionSemantics.Block.openRun_append, hParamRun]
    have hRemaining :
        tailFuel - prepared.paramCode.length = returnFuel := by
      simp [tailFuel]
    simpa [hRemaining] using hReturnRun
  refine ⟨preludeFuel, ?_, ?_, ?_⟩
  · simp [preludeFuel, tailFuel]
    omega
  · simp [preludeFuel, tailFuel, Nat.add_assoc]
  · rw [Expressions.InteractionSemantics.Block.openRun_append, hMarkerRun]
    have hRemaining :
        preludeFuel - prepared.markerCode.length = tailFuel := by
      simp [preludeFuel]
    simpa [hRemaining] using hParamReturnRun

/-- Execute setup while reserving an exact positive suffix budget. -/
theorem Prepared.prelude_forward_at
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {target afterParams finalTarget : Structured.RunState}
    {paramFuel returnFuel : Nat}
    (hParamFuelLength : paramFuel = prepared.paramCode.length + 1)
    (hReturnFuelLength : returnFuel = prepared.returnCode.length + 1)
    (hParamRunAt :
      ∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + paramFuel)
            { stmts := prepared.paramCode } target =
          .done (.ok (Structured.Outcome.regular afterParams)))
    (hReturnRunAt :
      ∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + returnFuel)
            { stmts := prepared.returnCode } afterParams =
          .done (.ok (Structured.Outcome.regular finalTarget)))
    (suffixFuel : Nat) (hSuffixFuel : 0 < suffixFuel) :
    Expressions.InteractionSemantics.Block.openRun expressions
        (prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + suffixFuel)
        { stmts :=
            prepared.markerCode ++
              (prepared.paramCode ++ prepared.returnCode) }
        target =
      .done (.ok (Structured.Outcome.regular finalTarget)) := by
  let returnBudget := prepared.returnCode.length + suffixFuel
  let paramBudget := prepared.paramCode.length + returnBudget
  let totalBudget := prepared.markerCode.length + paramBudget
  have hReturnBudget : 0 < returnBudget := by
    simp [returnBudget]
    omega
  have hParamBudget : 0 < paramBudget := by
    simp [paramBudget]
    omega
  have hReturnRun :
      Expressions.InteractionSemantics.Block.openRun expressions returnBudget
          { stmts := prepared.returnCode } afterParams =
        .done (.ok (Structured.Outcome.regular finalTarget)) := by
    have hRun := hReturnRunAt (suffixFuel - 1)
    have hFuelEq : suffixFuel - 1 + returnFuel = returnBudget := by
      rw [hReturnFuelLength]
      simp only [returnBudget]
      omega
    simpa [hFuelEq] using hRun
  have hParamRun :
      Expressions.InteractionSemantics.Block.openRun expressions paramBudget
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular afterParams)) := by
    have hRun := hParamRunAt (returnBudget - 1)
    have hFuelEq : returnBudget - 1 + paramFuel = paramBudget := by
      rw [hParamFuelLength]
      simp only [paramBudget]
      omega
    simpa [hFuelEq] using hRun
  have hParamReturnRun :
      Expressions.InteractionSemantics.Block.openRun expressions paramBudget
          { stmts := prepared.paramCode ++ prepared.returnCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) := by
    rw [Expressions.InteractionSemantics.Block.openRun_append, hParamRun]
    have hRemaining :
        paramBudget - prepared.paramCode.length = returnBudget := by
      simp [paramBudget]
    simpa [hRemaining] using hReturnRun
  have hMarkerRun :=
    prepared.markers_forward_at target paramBudget hParamBudget
  have hTotal :
      prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + suffixFuel = totalBudget := by
    simp [totalBudget, paramBudget, returnBudget, Nat.add_assoc]
  rw [hTotal, Expressions.InteractionSemantics.Block.openRun_append,
    hMarkerRun]
  have hRemaining :
      totalBudget - prepared.markerCode.length = paramBudget := by
    simp [totalBudget]
  simpa [hRemaining] using hParamReturnRun

/-- Prefix any related callee body with the exact compiler-selected setup. -/
theorem Prepared.prelude_then_body
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {sourceRun :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {doneRel :
      Except EVMException
          (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
        Except EVMException Expressions.InteractionSemantics.Outcome → Prop}
    {target finalTarget : Structured.RunState}
    {bodyCode : List Expressions.Stmt} {bodyFuel : Nat}
    (hBodyFuel : 0 < bodyFuel)
    (hPreludeAt :
      ∀ suffixFuel, 0 < suffixFuel →
        Expressions.InteractionSemantics.Block.openRun expressions
            (prepared.markerCode.length + prepared.paramCode.length +
              prepared.returnCode.length + suffixFuel)
            { stmts :=
                prepared.markerCode ++
                  (prepared.paramCode ++ prepared.returnCode) }
            target =
          .done (.ok (Structured.Outcome.regular finalTarget)))
    (hBody :
      Simulation.Interaction.Rel doneRel sourceRun
        (Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
          { stmts := bodyCode } finalTarget)) :
    Simulation.Interaction.Rel doneRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        (prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + bodyFuel)
        { stmts :=
            prepared.markerCode ++ prepared.paramCode ++
              prepared.returnCode ++ bodyCode }
        target) := by
  have hTarget :
      Expressions.InteractionSemantics.Block.openRun expressions
          (prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length + bodyFuel)
          { stmts :=
              prepared.markerCode ++ prepared.paramCode ++
                prepared.returnCode ++ bodyCode }
          target =
        Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
          { stmts := bodyCode } finalTarget := by
    rw [show
      prepared.markerCode ++ prepared.paramCode ++
          prepared.returnCode ++ bodyCode =
        (prepared.markerCode ++
          (prepared.paramCode ++ prepared.returnCode)) ++ bodyCode by
      simp [List.append_assoc],
      Expressions.InteractionSemantics.Block.openRun_append,
      hPreludeAt bodyFuel hBodyFuel]
    have hRemaining :
        prepared.markerCode.length + prepared.paramCode.length +
              prepared.returnCode.length + bodyFuel -
            (prepared.markerCode.length +
              (prepared.paramCode.length + prepared.returnCode.length)) =
          bodyFuel := by
      omega
    simpa [hRemaining]
  rw [hTarget]
  exact hBody

/-- The real argument lookup and return initialization define every body local. -/
theorem Prepared.bodyLiveDefined
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat} {mode : ActivationMode}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase mode source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord) :
    LiveDefined
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      source := by
  obtain ⟨values, suffix, hLookup, hStack⟩ := hRel.realization
  clear suffix hStack
  intro localName hLive
  rcases List.mem_append.mp hLive with hReturn | hParam
  · exact ⟨AllocationSupport.zeroWord, hZero localName (by simpa using hReturn)⟩
  · have hContains : source.vars.contains localName = true :=
      Functions.Source.Store.lookupMany_contains_of_mem hLookup
        (by simpa using hParam)
    cases hValue : source.vars localName with
    | none =>
        simp [Locals.Source.Store.contains, hValue] at hContains
    | some value =>
        exact ⟨value, rfl⟩

/-- Scratch-backed callee setup reaches the ordinary recursive body invariant. -/
theorem Prepared.body_entry_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hNeedsFrame : artifact.needsFrame = true)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase
        (.scratch 0 compilation.recipe.frameWords) source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation) :
    ∃ afterParams finalTarget paramFuel returnFuel preludeFuel,
      0 < paramFuel ∧
      0 < returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions 4
          { stmts := prepared.markerCode } target =
        .done (.ok (Structured.Outcome.regular target)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions paramFuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular afterParams)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions returnFuel
          { stmts := prepared.returnCode } afterParams =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      0 < preludeFuel ∧
      preludeFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions preludeFuel
          { stmts :=
              prepared.markerCode ++
                (prepared.paramCode ++ prepared.returnCode) }
          target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ suffixFuel, 0 < suffixFuel →
        Expressions.InteractionSemantics.Block.openRun expressions
            (prepared.markerCode.length + prepared.paramCode.length +
              prepared.returnCode.length + suffixFuel)
            { stmts :=
                prepared.markerCode ++
                  (prepared.paramCode ++ prepared.returnCode) }
            target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      AllocationContext.ActivationInvariant contract artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase prepared.bodyMode source finalTarget := by
  obtain
        ⟨afterParams, paramFrameDepth, paramFuel, hParamFuel,
        hParamFuelLength,
        _hParamLayout, hParamRun, hParamRunAt, hParamRel, hParamDepth,
        hParamStackLength⟩ :=
    prepared.parameters_forward_scratch hRel hStackLength hReservation
  obtain
        ⟨finalTarget, finalFrameDepth, returnFuel, hReturnFuel,
        hReturnFuelLength,
        _hReturnLayout, hReturnRun, hReturnRunAt, hReturnRel, hReturnDepth,
        hReturnStackLength⟩ :=
    prepared.returns_forward_scratch
      (by simpa [hParamDepth] using hParamRel) hZero
      hParamStackLength hReservation
  obtain ⟨preludeFuel, hPreludeFuel, hPreludeLength, hPreludeRun⟩ :=
    prepared.prelude_forward hParamFuel hReturnFuel hParamFuelLength
      hParamRunAt hReturnRun
  have hState :
      ActivationStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase prepared.bodyMode source finalTarget := by
    have hScratchState :
        ActivationStateRel contract prepared.plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse)
          0 frameBase
          (.scratch finalFrameDepth compilation.recipe.frameWords)
          source finalTarget :=
      .scratch hReturnRel
    simpa [Prepared.bodyMode, Artifact.mode, hNeedsFrame,
      ActivationMode.atStackDepth, hReturnDepth] using hScratchState
  refine
    ⟨afterParams, finalTarget, paramFuel, returnFuel, preludeFuel,
      hParamFuel, hReturnFuel, prepared.markers_forward target,
      hParamRun, hReturnRun, hPreludeFuel, hPreludeLength, hPreludeRun,
      (fun suffixFuel hSuffixFuel =>
        prepared.prelude_forward_at hParamFuelLength hReturnFuelLength
          hParamRunAt hReturnRunAt suffixFuel hSuffixFuel), ?_⟩
  exact
    { compiler := prepared.bodyCompiler
      planWF := prepared.planWF
      defined := prepared.bodyLiveDefined hRel hZero
      state := hState
      stackLength := hReturnStackLength }

/-- Stack-only callee setup reaches the ordinary recursive body invariant. -/
theorem Prepared.body_entry_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length) :
    ∃ afterParams finalTarget paramFuel returnFuel preludeFuel,
      0 < paramFuel ∧
      0 < returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions 4
          { stmts := prepared.markerCode } target =
        .done (.ok (Structured.Outcome.regular target)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions paramFuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular afterParams)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions returnFuel
          { stmts := prepared.returnCode } afterParams =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      0 < preludeFuel ∧
      preludeFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions preludeFuel
          { stmts :=
              prepared.markerCode ++
                (prepared.paramCode ++ prepared.returnCode) }
          target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ suffixFuel, 0 < suffixFuel →
        Expressions.InteractionSemantics.Block.openRun expressions
            (prepared.markerCode.length + prepared.paramCode.length +
              prepared.returnCode.length + suffixFuel)
            { stmts :=
                prepared.markerCode ++
                  (prepared.paramCode ++ prepared.returnCode) }
            target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      AllocationContext.ActivationInvariant contract artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase prepared.bodyMode source finalTarget := by
  obtain
      ⟨afterParams, paramFuel, hParamFuel, hParamFuelLength, _hParamLayout,
        hParamRun, hParamRunAt, hParamRel, hParamStackLength⟩ :=
    prepared.parameters_forward_stack hNeedsFrame hRel hStackLength
  obtain
      ⟨finalTarget, returnFuel, hReturnFuel, hReturnFuelLength,
        _hReturnLayout,
        hReturnRun, hReturnRunAt, hReturnRel, hReturnStackLength⟩ :=
    prepared.returns_forward_stack hNeedsFrame hParamRel hZero
      hParamStackLength
  obtain ⟨preludeFuel, hPreludeFuel, hPreludeLength, hPreludeRun⟩ :=
    prepared.prelude_forward hParamFuel hReturnFuel hParamFuelLength
      hParamRunAt hReturnRun
  have hState :
      ActivationStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase prepared.bodyMode source finalTarget := by
    simpa [Prepared.bodyMode, Artifact.mode, hNeedsFrame,
      ActivationMode.atStackDepth] using hReturnRel
  refine
    ⟨afterParams, finalTarget, paramFuel, returnFuel, preludeFuel,
      hParamFuel, hReturnFuel, prepared.markers_forward target,
      hParamRun, hReturnRun, hPreludeFuel, hPreludeLength, hPreludeRun,
      (fun suffixFuel hSuffixFuel =>
        prepared.prelude_forward_at hParamFuelLength hReturnFuelLength
          hParamRunAt hReturnRunAt suffixFuel hSuffixFuel), ?_⟩
  exact
    { compiler := prepared.bodyCompiler
      planWF := prepared.planWF
      defined := prepared.bodyLiveDefined hRel hZero
      state := hState
      stackLength := hReturnStackLength }

/-- Package a compiler-selected function body as an ordinary recursive root. -/
def Prepared.rootArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    (hProgramScoped : program.Scoped) :
    RootArtifact compilation :=
  { functionRoot? := some fn.name
    rootScope := .function fn.name
    slots := artifact.slots
    returns := fn.returns
    sourceBlock := fn.body
    startState := artifact.bodyStart
    startLocals := prepared.returnCtx
    planning :=
      { allocation := artifact.bodyStart.allocation
        nextScope := 0
        scopes := [] }
    planningAllocation := rfl
    rootScopeOwner := rfl
    plan := prepared.plan
    planWF := prepared.planWF
    finalState := prepared.bodyFinal
    finalLocals := prepared.bodyCtx
    planEq := by
      rw [prepared.planEq, artifact.planEntryScope, prepared.bodyPlan]
    finalFrameFresh := by
      rw [← prepared.bodyPlan]
      exact artifact.frameName_not_mem_planEntry_env
    lexicalFrameFresh := by
      intro entry hEntry
      exact artifact.frameName_not_mem_lexical_entry_env hEntry
    scopeStackEntries := by
      intro scope state added hRoot hEnv
      exact
        MixedAllocation.AllocationRecipe.stackEntriesForScope_of_functionRoot_env_extension
          hRoot artifact.slotsLookup hEnv
    plannedFinal := by
      calc
        (AllocationSupport.planBlockOpen (.function fn.name)
            { allocation := artifact.bodyStart.allocation
              nextScope := 0
              scopes := [] }
            fn.body).allocation =
            artifact.planEntry.state := by
          simpa [Artifact.bodyStart] using artifact.planEntryState.symm
        _ = prepared.bodyFinal.allocation := prepared.bodyPlan
    plannedScopes := by
      simpa [Artifact.bodyStart] using artifact.bodyScopesMem
    lowered := prepared.body
    compiled := prepared.bodyCode
    lowerCtx := artifact.lowerCtx
    lowerCtxShared := artifact.lowerCtxShared
    lower := prepared.lowerBody
    compile := prepared.compileBody
    sourceScoped := artifact.bodyScoped hProgramScoped
    activeEnv := by
      refine ⟨[], ?_, ?_⟩
      · simp [Artifact.bodyStart]
      · simp }

/-- The selected callee body enters the shared recursive cursor interface. -/
def Prepared.rootCursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    (hProgramScoped : program.Scoped) :
    CoreCursor (prepared.rootArtifact hProgramScoped)
      (.function fn.name)
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      fn.body artifact.bodyStart prepared.returnCtx :=
  (prepared.rootArtifact hProgramScoped).cursor

end SelectedCallee

/-- A real caller lookup determines a canonical source function and all of the
compiler-owned callee artifacts needed by the adjacent call proof. -/
theorem CallComponents.selectedCallee
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
    (components : CallComponents cursor) :
    ∃ fn,
      Functions.Source.FunList.find? functionName program.functions =
          some fn ∧
        ∃ artifact : SelectedCallee.Artifact compilation functionName fn,
          Nonempty (SelectedCallee.Prepared artifact) ∧
            components.fn = artifact.slots := by
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  have hRecipeLookup :
      AllocationSupport.lookupFun? functionName
          compilation.recipe.functionSlots =
        some components.fn := by
    simpa [root.lowerCtxShared.functions] using components.lookup
  obtain ⟨fn, hFind, _hSlotsMatch⟩ :=
    AllocationSupport.planRecipeCore?_find?_of_lookupFun?
      hRecipe hRecipeLookup
  obtain ⟨artifact⟩ := SelectedCallee.Artifact.of_find hFind
  have hSlots : components.fn = artifact.slots :=
    artifact.slots_eq_of_lookup root.lowerCtxShared components.lookup
  exact ⟨fn, hFind, artifact, artifact.prepare, hSlots⟩

end AllocationInteractionCall
end Functions
end EvmCompiler
