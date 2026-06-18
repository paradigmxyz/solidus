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
      Expressions.InteractionSemantics.Block.openRun targetProgram 4
          { stmts := compiled } target =
        .done (.ok (Structured.Outcome.regular final)) ∧
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
    ⟨compiled, final, by simpa [compiled] using hCompile, ?_,
      hFinalRel, hStackLength, hFinalMachine⟩
  let storeCode : Structured.Code :=
    [.op nameOp] ++
      [.op frameOp,
       .push (AllocationSupport.slotOffset slot),
       .op .add,
       .op .mstore]
  have hStoreStmt :
      Expressions.InteractionSemantics.Stmt.openRun targetProgram 3
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
      Expressions.InteractionSemantics.Stmt.openRun targetProgram 2
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
      Expressions.InteractionSemantics.Stmt.openRun targetProgram 1
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
    Expressions.InteractionSemantics.Block.openRun targetProgram (3 + 1)
        { stmts :=
            [.code storeCode, .code promoteCode, .code [.op .pop]] }
        target =
      .done (.ok (Structured.Outcome.regular final))
  rw [Expressions.InteractionSemantics.Block.openRun_cons, hStoreStmt]
  change
    Expressions.InteractionSemantics.Block.openRun targetProgram (2 + 1)
        { stmts := [.code promoteCode, .code [.op .pop]] } written =
      .done (.ok (Structured.Outcome.regular final))
  rw [Expressions.InteractionSemantics.Block.openRun_cons, hPromoteStmt]
  change
    Expressions.InteractionSemantics.Block.openRun targetProgram (1 + 1)
        { stmts := [.code [.op .pop]] } promoted =
      .done (.ok (Structured.Outcome.regular final))
  rw [Expressions.InteractionSemantics.Block.openRun_cons, hPopStmt]
  exact
    Expressions.InteractionSemantics.Block.openRun_nil
      targetProgram 0 final

end ParameterPrelude

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

end AllocationInteractionCall
end Functions
end EvmCompiler
