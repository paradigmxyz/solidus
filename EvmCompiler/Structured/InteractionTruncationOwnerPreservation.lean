import EvmCompiler.Structured.InteractionBoundedOwnerPreservation
import EvmCompiler.Structured.InteractionFuelSafety
import EvmCompiler.TypedCfg.InteractionFuelSafety

namespace EvmCompiler
namespace Structured
namespace InteractionTruncationOwnerPreservation
namespace OpenOutcome

open InteractionOwnerPreservation.OpenOutcome

abbrev StopPolicy :=
  InteractionControlPreservation.OpenOutcome.StopPolicy

abbrev BoundedTruncationExecPreservesUnder :=
  InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder

abbrev BoundedExecPreservesUnder :=
  InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder

abbrev RecursiveBoundary :=
  InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary

abbrev FragmentContract :=
  InteractionOwnerPreservation.OpenOutcome.FragmentContract

abbrev StmtContract :=
  InteractionOwnerPreservation.OpenOutcome.StmtContract

/-- Source-budgeted structural-truncation capability for one compiled block. -/
def BlockOwnerAt
    (sourceFuel : Nat)
    (program : Structured.Program)
    (entryShapes : TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg) : Prop :=
  forall {blockSourceFuel compilerFuel : Nat} {block : Structured.Block}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result}
      {source : RunState} {tokens : List Word}
      {policy : StopPolicy}
      {canBreak canContinue canLeave : Bool},
    blockSourceFuel <= sourceFuel ->
    TypedCfgCompiler.compileBlockFuel? compilerFuel block ctx
        supply entry input regular = some result ->
    TypedCfgPreservation.BlocksInProgram result cfg ->
    TypedCfgPreservation.CallsInProgram result generated.calls ->
    Structured.Block.WF canBreak canContinue canLeave block ->
    block.FrameSafe ->
    Structured.ProcList.BlockCallsResolved program.procs block ->
    TypedCfgPreservation.OutcomeSimulation.ContextSupports
      ctx canBreak canContinue canLeave ->
    ctx.procs = program.procs ->
    (canLeave = true ->
      exists frame rest, source.returns = frame :: rest) ->
    FragmentContract cfg result ctx supply entry regular input
      source tokens policy ->
    BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        program blockSourceFuel block source)
      (InteractionStaticCost.blockBudget
        program blockSourceFuel block)
      policy

theorem BlockOwnerAt.mono
    {smaller larger : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    (hOwner : BlockOwnerAt larger program entryShapes cfg generated)
    (hLe : smaller <= larger) :
    BlockOwnerAt smaller program entryShapes cfg generated := by
  intro blockSourceFuel compilerFuel block ctx supply entry regular input
    result source tokens policy canBreak canContinue canLeave hBlockLe
  exact hOwner (Nat.le_trans hBlockLe hLe)

namespace BoundedTruncationExecPreservesUnder

/-- A source computation that truncates before exposing an interaction is
matched by the zero-step target runner. -/
theorem immediate
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {targetBudget : Nat} {policy : StopPolicy}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hSource : sourceRun =
      Simulation.Interaction.error (.OutOfFuel : EVMException)) :
    BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget policy := by
  intro target _hStateRel transcript hExec
  rw [hSource] at hExec
  cases hExec
  exact ⟨0, Nat.zero_le _, Simulation.Interaction.Follows.nil _⟩

/-- A source interaction proved incapable of structural exhaustion has no
truncation branch to preserve. -/
theorem vacuous
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {targetBudget : Nat} {policy : StopPolicy}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hSafe : Simulation.Interaction.AllDone
      Assembly.InteractionFuelSafety.NotOutOfFuel sourceRun) :
    BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget policy := by
  intro _target _hStateRel transcript hExec
  have hNot :=
    Simulation.Interaction.AllDone.property_of_executes hSafe hExec
  exact False.elim (hNot rfl)

end BoundedTruncationExecPreservesUnder

namespace Block

theorem zero
    {program : Structured.Program} {block : Structured.Block}
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy} :
    BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun program 0 block source)
      (InteractionStaticCost.blockBudget program 0 block)
      policy := by
  apply BoundedTruncationExecPreservesUnder.immediate
  rfl

end Block

namespace Call

open InteractionCallPreservation.Call

theorem openStep_procEntry_of_adapter
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {proc : Structured.Proc}
    {fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes sourceProgram.procs proc
        context.procBlocks context.procCalls}
    {adapter : TypedCfg.Block}
    (hEntry : fragment.entry = ProcLabel.body proc.name)
    (hAdapterCompile :
      TypedCfgCompiler.mkBlock?
          (ProcLabel.entry proc.name)
          (TypedCfgCompiler.Shape.procEntry proc)
          [.relabel fragment.input] (.jump (ProcLabel.body proc.name)) =
        some adapter)
    (hAdapterMem : adapter ∈ context.procBlocks)
    (state : EVMState) :
    TypedCfg.InteractionSemantics.Program.openStep
        cfg (ProcLabel.entry proc.name) state =
      Simulation.Interaction.pure
        (.jump fragment.entry state) := by
  have hMem : adapter ∈ cfg.blocks := by
    have hBlocksEq :
        cfg.blocks =
          context.main.blocks ++ context.procBlocks ++
            TypedCfgCompiler.dispatchBlocks sourceProgram.procs
              (context.main.calls ++ context.procCalls) ++
            [{ label := ProcLabel.programEnd
               input :=
                 context.main.fallthrough?.getD TypedCfg.Shape.caller
               body := []
               output :=
                 context.main.fallthrough?.getD TypedCfg.Shape.caller
               term := .halt .stop }] :=
      congrArg TypedCfg.Program.blocks context.cfgEq
    rw [hBlocksEq]
    simp [hAdapterMem]
  have hFind :=
    TypedCfg.Program.findBlock?_eq_some_of_mem
      context.wellTyped.1 hMem
  unfold TypedCfgCompiler.mkBlock? at hAdapterCompile
  cases hType :
      TypedCfg.Instr.type? (.relabel fragment.input)
        (TypedCfgCompiler.Shape.procEntry proc) with
  | none =>
      simp [TypedCfg.Block.bodyType?, hType] at hAdapterCompile
  | some output =>
      simp [TypedCfg.Block.bodyType?, hType] at hAdapterCompile
      cases hAdapterCompile
      have hOpenBody :
          TypedCfg.InteractionSemantics.Block.openRunBody
              [.relabel fragment.input]
              (TypedCfgCompiler.Shape.procEntry proc) state =
            Simulation.Interaction.pure (state, output) := by
        rw [
          TypedCfg.InteractionSemantics.Block.openRunBody_eq_done_of_forall_not_prim]
        · simp [
            TypedCfg.Block.runBody, TypedCfg.Instr.runAt,
            hType, TypedCfg.Instr.runState]
          rfl
        · intro instr hMem op hEq
          simp only [List.mem_singleton] at hMem
          exact TypedCfg.Instr.noConfusion (hMem.symm.trans hEq)
      simp only [
        TypedCfg.InteractionSemantics.Program.openStep,
        TypedCfg.Control.Program.step, hFind,
        TypedCfg.Control.Block.run]
      change
        (do
          let result ←
            TypedCfg.InteractionSemantics.Block.openRunBody
              [.relabel fragment.input]
              (TypedCfgCompiler.Shape.procEntry proc) state
          if result.2 = output then
            pure (TypedCfg.Block.runTerm output
              (.jump (ProcLabel.body proc.name)) result.1)
          else
            throw .InvalidInstruction) =
          Simulation.Interaction.pure
            (.jump fragment.entry state)
      rw [hOpenBody]
      simp [hEntry, TypedCfg.Block.runTerm]
      rfl


theorem prepend_call_route_follows
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {proc : Structured.Proc}
    {fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes sourceProgram.procs proc
        context.procBlocks context.procCalls}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    {entry : Assembly.Label} {target targetAtEntry : EVMState}
    {tailFuel : Nat}
    {transcript : Simulation.Interaction.Transcript}
    (hCall :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (.jump (ProcLabel.entry proc.name) targetAtEntry))
    (hProcEntryNoStop :
      policy (ProcLabel.entry proc.name) targetAtEntry = false)
    (hFragmentEntryNoStop :
      policy fragment.entry targetAtEntry = false)
    (hTail :
      Simulation.Interaction.Follows
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg tailFuel fragment.entry targetAtEntry)
        transcript) :
    exists targetFuel,
      targetFuel <= tailFuel + 2 /\
      Simulation.Interaction.Follows
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg targetFuel entry target)
        transcript := by
  have hCallExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        [] (.ok (.jump (ProcLabel.entry proc.name) targetAtEntry)) := by
    rw [hCall]
    exact Simulation.Interaction.Executes.done _
  rcases fragment.route with hDirect | hAdapterRoute
  · rcases hDirect with ⟨hEntry, _hInput⟩
    have hTailAtProc :
        Simulation.Interaction.Follows
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            policy cfg tailFuel (ProcLabel.entry proc.name) targetAtEntry)
          transcript := by
      simpa [hEntry] using hTail
    have hWhole :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump_follows
        hCallExec hProcEntryNoStop hTailAtProc
    exact ⟨tailFuel + 1, by omega, by simpa using hWhole⟩
  · rcases hAdapterRoute with
      ⟨adapter, hEntry, _hInput, _hFrame,
        hAdapterCompile, hAdapterMem⟩
    have hAdapter :=
      openStep_procEntry_of_adapter context hEntry
        hAdapterCompile hAdapterMem targetAtEntry
    have hAdapterExec :
        Simulation.Interaction.Executes
          (TypedCfg.InteractionSemantics.Program.openStep
            cfg (ProcLabel.entry proc.name) targetAtEntry)
          [] (.ok (.jump fragment.entry targetAtEntry)) := by
      rw [hAdapter]
      exact Simulation.Interaction.Executes.done _
    have hRoute :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump_follows
        hAdapterExec hFragmentEntryNoStop hTail
    have hWhole :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump_follows
        hCallExec hProcEntryNoStop hRoute
    exact ⟨(tailFuel + 1) + 1, by omega, by simpa using hWhole⟩

theorem body_leave_elim
    {program : Structured.Program} {proc : Structured.Proc}
    {bodyResult : TypedCfgCompiler.Result}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        bodyResult (procContext program proc)
        (ProcLabel.exit proc.name) returns tokens
        (.leave source) target) :
    ∃ targetState,
      target = .jump (ProcLabel.exit proc.name) targetState ∧
        TypedCfgPreservation.StateRel source tokens targetState ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            (TypedCfgCompiler.Shape.procExit proc)
            source.evm.stack.length ∧
          source.returns = returns := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  obtain ⟨label, targetState, hLabel, rfl, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.leave_elim hOutcome
  have hLabelEq : label = ProcLabel.exit proc.name := by
    simpa [
      procContext,
      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
      using hLabel.symm
  subst label
  refine ⟨targetState, rfl, hStateRel, ?_, ?_⟩
  · simpa [
      InteractionControlPreservation.OpenOutcome.FrameFits,
      procContext] using hFits
  · simpa [
      InteractionControlPreservation.OpenOutcome.ActivationRestored]
      using hRestored

theorem openRun_call_truncation_bounded_under
    {compilerFuel sourceFuel bodyBudget : Nat}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes sourceProgram.procs proc
        generated.procBlocks generated.procCalls)
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hProcs : ctx.procs = sourceProgram.procs)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hInputFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hProcWF : proc.WF)
    (hProcEntryNoStop :
      forall {args callerStack : EvmYul.Stack Word}
          {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) ->
        TypedCfgPreservation.StateRel
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens) targetState ->
          policy (ProcLabel.entry proc.name) targetState = false)
    (hFragmentEntryNoStop :
      forall {args callerStack : EvmYul.Stack Word}
          {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) ->
        TypedCfgPreservation.StateRel
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens) targetState ->
          policy fragment.entry targetState = false)
    (hBodyDone :
      forall {args callerStack : EvmYul.Stack Word},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          fragment.result cfg fragment.entry
          (procContext sourceProgram proc) (ProcLabel.exit proc.name)
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
          (Structured.Stmt.callToken supply :: tokens)
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel proc.body
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc))
          bodyBudget
          (bodyStopPolicy fragment.result sourceProgram proc
            (((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc).returns)
            (Structured.Stmt.callToken supply :: tokens) policy))
    (hBodyTruncated :
      forall {args callerStack : EvmYul.Stack Word},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          fragment.result cfg fragment.entry
          (procContext sourceProgram proc) (ProcLabel.exit proc.name)
          ((source.withEVM { source.evm with stack := args }).pushReturn
            callerStack proc.retc)
          (Structured.Stmt.callToken supply :: tokens)
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel proc.body
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc))
          bodyBudget
          (bodyStopPolicy fragment.result sourceProgram proc
            (((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc).returns)
            (Structured.Stmt.callToken supply :: tokens) policy)) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.call name) source)
      (bodyBudget + 3) policy := by
  have hCompilerLookup :
      Structured.ProcList.lookup? name ctx.procs = some proc := by
    simpa [hProcs] using hLookup
  rcases
      TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
        hCompilerLookup hCompile with
    ⟨returnShape, output, hSource, hAfter, hCallType, hResult⟩
  subst result
  let site : TypedCfgCompiler.DispatchSite :=
    { procName := name
      token := Structured.Stmt.callToken supply
      returnLabel := regular
      caseLabel := .generated supply 10000 }
  have hSiteMem : site ∈ generated.calls := by
    apply hResultCalls site
    simp [site]
  have hName : proc.name = name :=
    Structured.ProcList.name_of_lookup? hLookup
  have hArgBound : proc.argc <= TypedCfgCompiler.Shape.sourceLength input :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
  have hStackBound : proc.argc <= source.evm.stack.length :=
    Nat.le_trans hArgBound hInputFits.1
  let args := source.evm.stack.take proc.argc
  let callerStack := source.evm.stack.drop proc.argc
  have hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack) := by
    simp [Structured.StackFrame.splitArgs?, hStackBound, args, callerStack]
  let callSource : RunState :=
    ((source.withEVM { source.evm with stack := args }).pushReturn
      callerStack proc.retc)
  intro target hStateRel transcript hSourceExec
  have hCallBodyDone := hBodyDone hSplit
  have hCallBodyTruncated := hBodyTruncated hSplit
  rcases
      openStep_entry_of_compileStmtFuel?
        hCompilerLookup hCompile hBlocks hStateRel hSplit hProcWF with
    ⟨targetAtEntry, hCallStep, hCallStateRel⟩
  have hCallStep' :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (.jump (ProcLabel.entry proc.name) targetAtEntry) := by
    simpa [hName] using hCallStep
  have hCallStateRel' :
      TypedCfgPreservation.StateRel callSource
        (Structured.Stmt.callToken supply :: tokens) targetAtEntry := by
    simpa [callSource] using hCallStateRel
  simp only [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    EffectSemantics.Ordinary.runStateModel_evm,
    EffectSemantics.Ordinary.runStateModel_withEVM,
    EffectSemantics.Ordinary.runStateModel_pushReturn,
    EffectSemantics.Ordinary.runStateModel_popReturn?,
    hLookup, hSplit] at hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    ⟨bodyError, hOutcome, hBodySourceError⟩ |
      ⟨bodyOutcome, bodyTranscript, restTranscript,
        hTranscript, hBodyExec, hRestExec⟩
  · cases hOutcome
    obtain ⟨bodyFuel, hBodyFuel, hTargetBodyFollow⟩ :=
      hCallBodyTruncated targetAtEntry hCallStateRel' transcript
        hBodySourceError
    have hTargetBodyOuter :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined_follows
        (outer := policy)
        (inner :=
          bodyStopPolicy fragment.result sourceProgram proc
            callSource.returns
            (Structured.Stmt.callToken supply :: tokens) policy)
        (hRefines := by
          intro label state hStop
          simp [bodyStopPolicy,
            InteractionControlPreservation.OpenOutcome.pushStopJump,
            hStop])
        hTargetBodyFollow
    obtain ⟨targetFuel, hRouteFuel, hTargetFollow⟩ :=
      prepend_call_route_follows (fragment := fragment) generated hCallStep'
        (hProcEntryNoStop hSplit hCallStateRel')
        (hFragmentEntryNoStop hSplit hCallStateRel')
        hTargetBodyOuter
    exact ⟨targetFuel, by omega, hTargetFollow⟩
  · subst transcript
    obtain ⟨bodyFuel, bodyRemaining, targetBodyOutcome, hBodyFuel,
        hTargetBodyExec, hBodyRelRaw⟩ :=
      hCallBodyDone targetAtEntry hCallStateRel'
        bodyTranscript bodyOutcome hBodyExec
    have hBodyRel :
        InteractionControlPreservation.OpenOutcome.Rel
          fragment.result (procContext sourceProgram proc)
          (ProcLabel.exit proc.name) callSource.returns
          (Structured.Stmt.callToken supply :: tokens)
          bodyOutcome targetBodyOutcome := by
      simpa [callSource] using hBodyRelRaw
    rcases bodyOutcome with ⟨bodyState, bodyMode⟩
    cases bodyMode with
    | regular =>
        obtain ⟨targetAtExit, hTargetOutcome, hBodyStateRel,
            hBodyFits, hBodyReturns⟩ :=
          InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
            fragment.fallthrough hBodyRel
        let frame : ReturnDest :=
          { callerStack := callerStack, retc := proc.retc }
        let returned : RunState :=
          { bodyState with returns := source.returns }
        have hPop : bodyState.popReturn? = some (frame, returned) := by
          simp [RunState.popReturn?, hBodyReturns, callSource, frame, returned]
        have hLength : bodyState.evm.stack.length = proc.retc :=
          hBodyFits.2 proc.retc
            (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
        have hAttach :
            Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
              some (bodyState.evm.stack ++ callerStack) := by
          simp [Structured.StackFrame.attachReturns?, frame, hLength]
        simp [hPop, hAttach] at hRestExec
        cases hRestExec
    | leave =>
        obtain ⟨targetAtExit, hTargetOutcome, hBodyStateRel,
            hBodyFits, hBodyReturns⟩ := body_leave_elim hBodyRel
        let frame : ReturnDest :=
          { callerStack := callerStack, retc := proc.retc }
        let returned : RunState :=
          { bodyState with returns := source.returns }
        have hPop : bodyState.popReturn? = some (frame, returned) := by
          simp [RunState.popReturn?, hBodyReturns, callSource, frame, returned]
        have hLength : bodyState.evm.stack.length = proc.retc :=
          hBodyFits.2 proc.retc
            (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
        have hAttach :
            Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
              some (bodyState.evm.stack ++ callerStack) := by
          simp [Structured.StackFrame.attachReturns?, frame, hLength]
        simp [hPop, hAttach] at hRestExec
        cases hRestExec
    | brk =>
        obtain ⟨label, targetState, hLabel, _⟩ :=
          TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim hBodyRel.1
        simp [procContext,
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          at hLabel
    | cont =>
        obtain ⟨label, targetState, hLabel, _⟩ :=
          TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim hBodyRel.1
        simp [procContext,
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          at hLabel
    | halt kind => cases hRestExec

theorem call_succ
    {compilerFuel sourceFuel bodyBudget : Nat}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hProcs : ctx.procs = sourceProgram.procs)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hInputFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hProcWF : proc.WF)
    (hProcEntryNoStop :
      forall {args callerStack : EvmYul.Stack Word}
          {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) ->
        TypedCfgPreservation.StateRel
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens) targetState ->
          policy (ProcLabel.entry proc.name) targetState = false)
    (hFragmentEntryNoStop :
      forall (fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes sourceProgram.procs proc
            generated.procBlocks generated.procCalls),
        forall {args callerStack : EvmYul.Stack Word}
            {targetState : EVMState},
          Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
              some (args, callerStack) ->
          TypedCfgPreservation.StateRel
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc)
              (Structured.Stmt.callToken supply :: tokens) targetState ->
            policy fragment.entry targetState = false)
    (hBodyDone :
      forall (fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes sourceProgram.procs proc
            generated.procBlocks generated.procCalls),
        TypedCfgPreservation.BlocksInProgram fragment.result cfg ->
        TypedCfgPreservation.CallsInProgram fragment.result generated.calls ->
        forall {args callerStack : EvmYul.Stack Word},
          Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
              some (args, callerStack) ->
          InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
            fragment.result cfg fragment.entry
            (procContext sourceProgram proc) (ProcLabel.exit proc.name)
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceFuel proc.body
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc))
            bodyBudget
            (bodyStopPolicy fragment.result sourceProgram proc
              (((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc).returns)
              (Structured.Stmt.callToken supply :: tokens) policy))
    (hBodyTruncated :
      forall (fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes sourceProgram.procs proc
            generated.procBlocks generated.procCalls),
        TypedCfgPreservation.BlocksInProgram fragment.result cfg ->
        TypedCfgPreservation.CallsInProgram fragment.result generated.calls ->
        forall {args callerStack : EvmYul.Stack Word},
          Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
              some (args, callerStack) ->
          InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
            fragment.result cfg fragment.entry
            (procContext sourceProgram proc) (ProcLabel.exit proc.name)
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceFuel proc.body
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc))
            bodyBudget
            (bodyStopPolicy fragment.result sourceProgram proc
              (((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc).returns)
              (Structured.Stmt.callToken supply :: tokens) policy)) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.call name) source)
      (bodyBudget + 3) policy := by
  rcases generated.procFragment_of_lookup? hLookup with
    ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
  exact
    openRun_call_truncation_bounded_under generated fragment hLookup hProcs
      hCompile hBlocks hResultCalls hInputFits hProcWF
      hProcEntryNoStop (hFragmentEntryNoStop fragment)
      (hBodyDone fragment hFragmentBlocks hFragmentCalls)
      (hBodyTruncated fragment hFragmentBlocks hFragmentCalls)


end Call

namespace Loop

open InteractionLoopPreservation.Loop

theorem openRunForLoop_truncation_bounded_under
    {sourceFuel : Nat}
    {sourceProgram : Structured.Program}
    {cond : Structured.Code} {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {loopLabel bodyLabel postLabel regular : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {result bodyResult postResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {returns : List ReturnDest}
    {tokens : List Word}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hConditionMem :
      conditionBlock loopLabel bodyLabel regular
          loopInput condOutput cond ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput = some ())
    (hBodyRequire :
      bodyResult.requireFallthrough?
          { condOutput with slots := condOutput.slots.tail } = some ())
    (hPostRequire : postResult.requireFallthrough? loopInput = some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        loopInput source.evm.stack.length)
    (hSourceReturns : source.returns = returns)
    (hBodyEntryNoStop :
      forall {bodySource : RunState} {targetState : EVMState},
        bodySource.returns = returns ->
        TypedCfgPreservation.StateRel bodySource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
          policy bodyLabel targetState = false)
    (hPostEntryNoStop :
      forall {postSource : RunState} {targetState : EVMState},
        postSource.returns = returns ->
        TypedCfgPreservation.StateRel postSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
          policy postLabel targetState = false)
    (hLoopEntryNoStop :
      forall {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = returns ->
        TypedCfgPreservation.StateRel loopSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length ->
          policy loopLabel targetState = false)
    (hBodyDone :
      forall {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
        bodySource.returns = returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg bodyLabel
          (bodyContext ctx regular postLabel
            { condOutput with slots := condOutput.slots.tail })
          postLabel bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel body)
          (bodyStopPolicy bodyResult postResult ctx regular
            postLabel loopLabel
            { condOutput with slots := condOutput.slots.tail }
            returns tokens policy))
    (hBodyTruncated :
      forall {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
        bodySource.returns = returns ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          bodyResult cfg bodyLabel
          (bodyContext ctx regular postLabel
            { condOutput with slots := condOutput.slots.tail })
          postLabel bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel body)
          (bodyStopPolicy bodyResult postResult ctx regular
            postLabel loopLabel
            { condOutput with slots := condOutput.slots.tail }
            returns tokens policy))
    (hPostDone :
      forall {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
        postSource.returns = returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          postResult cfg postLabel (outerContext ctx)
          loopLabel postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel post)
          (postStopPolicy postResult ctx loopLabel returns tokens policy))
    (hPostTruncated :
      forall {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
        postSource.returns = returns ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          postResult cfg postLabel (outerContext ctx)
          loopLabel postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel post)
          (postStopPolicy postResult ctx loopLabel returns tokens policy)) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg loopLabel ctx regular source tokens
      (InteractionSemantics.Stmt.openRunForLoop
        sourceProgram sourceFuel cond post body source)
      (InteractionStaticCost.loopBudget
        sourceProgram sourceFuel cond post body)
      policy := by
  induction sourceFuel generalizing source with
  | zero =>
      intro target _hStateRel transcript hSourceExec
      change
        Simulation.Interaction.Executes
          (Simulation.Interaction.error
            (Error := EVMException) .OutOfFuel)
          transcript (.error .OutOfFuel) at hSourceExec
      cases hSourceExec
      exact ⟨0, Nat.zero_le _, Simulation.Interaction.Follows.nil _⟩
  | succ fuel ih =>
      intro target hStateRel transcript hSourceExec
      have hSourceExec' :
          Simulation.Interaction.Executes
            (Simulation.Interaction.bind
              (InteractionSemantics.Code.openRunCondition cond source)
              (fun conditionResult =>
                if conditionResult.2 then
                  Simulation.Interaction.bind
                    (InteractionSemantics.Block.openRun
                      sourceProgram fuel body conditionResult.1)
                    (fun bodyOutcome =>
                      match bodyOutcome.mode with
                      | .brk =>
                          Simulation.Interaction.pure
                            (Structured.Outcome.regular bodyOutcome.state)
                      | .regular | .cont =>
                          Simulation.Interaction.bind
                            (InteractionSemantics.Block.openRun
                              sourceProgram fuel post bodyOutcome.state)
                            (fun postOutcome =>
                              match postOutcome.mode with
                              | .regular =>
                                  InteractionSemantics.Stmt.openRunForLoop
                                    sourceProgram fuel cond post body
                                    postOutcome.state
                              | .brk | .cont =>
                                  Simulation.Interaction.error
                                    .InvalidInstruction
                              | .leave | .halt _ =>
                                  Simulation.Interaction.pure postOutcome)
                      | .leave | .halt _ =>
                          Simulation.Interaction.pure bodyOutcome)
                else
                  Simulation.Interaction.pure
                    (Structured.Outcome.regular conditionResult.1)))
            transcript (.error .OutOfFuel) := by
        simpa [
          InteractionSemantics.Stmt.openRunForLoop,
          EffectSemantics.Control.Stmt.runForLoop] using hSourceExec
      rcases Simulation.Interaction.Executes.bind_cases hSourceExec' with
        ⟨conditionError, hOutcome, hConditionError⟩ |
          ⟨conditionResult, conditionTranscript, restTranscript,
            hTranscript, hConditionExec, hRestExec⟩
      · cases hOutcome
        have hHeadRel :=
          openStep_condition hBlocks hConditionMem hType hSource
            hFits hStateRel
        have hHeadWithReturns :=
          Simulation.Interaction.Rel.strengthen_left hHeadRel
            (InteractionSemantics.Code.openRunCondition_returns cond source)
        obtain ⟨targetDone, hTargetConditionExec, hConditionDone⟩ :=
          Simulation.Interaction.Rel.executes hHeadWithReturns hConditionError
        cases targetDone with
        | error targetError =>
            have hTargetExec :
                Simulation.Interaction.Executes
                  (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                    policy cfg 1 loopLabel target)
                  transcript (.error targetError) := by
              rw [
                TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
              exact Simulation.Interaction.Executes.bind_error
                hTargetConditionExec
            exact ⟨1, by
              rw [InteractionStaticCost.loopBudget_succ]
              omega, hTargetExec.follows⟩
        | ok targetOutcome => cases hConditionDone.1
      · subst transcript
        have hHeadRel :=
          openStep_condition hBlocks hConditionMem hType hSource
            hFits hStateRel
        have hHeadWithReturns :=
          Simulation.Interaction.Rel.strengthen_left hHeadRel
            (InteractionSemantics.Code.openRunCondition_returns cond source)
        obtain ⟨targetDone, hTargetConditionExec, hConditionDone⟩ :=
          Simulation.Interaction.Rel.executes hHeadWithReturns hConditionExec
        cases targetDone with
        | error targetError => cases hConditionDone.1
        | ok targetOutcome =>
            rcases conditionResult with ⟨afterCond, condTrue⟩
            rcases hConditionDone with ⟨hConditionRel, hConditionReturns⟩
            cases hConditionRel with
            | ok hConditionRel =>
                rcases hConditionRel with
                  ⟨targetAfterCond, hTargetOutcome,
                    hAfterCondRel, hAfterCondFits⟩
                have hAfterCondReturns : afterCond.returns = returns := by
                  have hEq : afterCond.returns = source.returns := by
                    simpa [InteractionSemantics.Code.ConditionReturnsEq]
                      using hConditionReturns
                  exact hEq.trans hSourceReturns
                cases condTrue with
                | false =>
                    simp only [if_false] at hTargetOutcome hRestExec
                    cases hRestExec
                | true =>
                    simp only [if_true] at hTargetOutcome hRestExec
                    subst targetOutcome
                    rcases Simulation.Interaction.Executes.bind_cases hRestExec with
                      ⟨bodyError, hOutcome, hBodySourceError⟩ |
                        ⟨bodyOutcome, bodyTranscript, afterBodyTranscript,
                          hBodyTranscript, hBodyExec, hAfterBodyExec⟩
                    · cases hOutcome
                      obtain ⟨bodyFuel, hBodyFuel, hTargetBodyFollow⟩ :=
                        hBodyTruncated (blockFuel := fuel)
                          (Nat.lt_succ_self fuel) hAfterCondFits
                          hAfterCondReturns targetAfterCond hAfterCondRel
                          restTranscript hBodySourceError
                      have hTargetBodyOuter :=
                        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined_follows
                          (outer := policy)
                          (inner :=
                            bodyStopPolicy bodyResult postResult ctx regular
                              postLabel loopLabel
                              { condOutput with
                                slots := condOutput.slots.tail }
                              returns tokens policy)
                          (hRefines := by
                            intro label state hStop
                            simp [bodyStopPolicy, postStopPolicy,
                              InteractionControlPreservation.OpenOutcome.pushStopJump,
                              hStop])
                          hTargetBodyFollow
                      have hTargetExec :=
                        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump_follows
                          hTargetConditionExec
                          (hBodyEntryNoStop hAfterCondReturns hAfterCondRel
                            hAfterCondFits)
                          hTargetBodyOuter
                      exact ⟨bodyFuel + 1, by
                        rw [InteractionStaticCost.loopBudget_succ]
                        omega, by simpa using hTargetExec⟩
                    · subst restTranscript
                      obtain ⟨bodyFuel, bodyRemaining, targetBodyOutcome,
                          hBodyFuel, hTargetBodyExec, hBodyRelRaw⟩ :=
                        hBodyDone (blockFuel := fuel)
                          (Nat.lt_succ_self fuel) hAfterCondFits
                          hAfterCondReturns targetAfterCond hAfterCondRel
                          bodyTranscript bodyOutcome hBodyExec
                      have hBodyRel :
                          InteractionControlPreservation.OpenOutcome.Rel
                            bodyResult
                            (bodyContext ctx regular postLabel
                              { condOutput with slots := condOutput.slots.tail })
                            postLabel returns tokens
                            bodyOutcome targetBodyOutcome := by
                        simpa [hAfterCondReturns] using hBodyRelRaw
                      rcases bodyOutcome with ⟨bodyState, bodyMode⟩
                      have continueWithPost
                          (hExit :
                            exists targetPostEntry,
                              targetBodyOutcome = .jump postLabel targetPostEntry /\
                              TypedCfgPreservation.StateRel bodyState tokens
                                targetPostEntry /\
                              TypedCfgCompiler.Shape.SourceFrameFits
                                { condOutput with
                                  slots := condOutput.slots.tail }
                                bodyState.evm.stack.length /\
                              bodyState.returns = returns)
                          (hAfterBodyPostExec :
                            Simulation.Interaction.Executes
                              (Simulation.Interaction.bind
                                (InteractionSemantics.Block.openRun
                                  sourceProgram fuel post bodyState)
                                (fun postOutcome =>
                                  match postOutcome.mode with
                                  | .regular =>
                                      InteractionSemantics.Stmt.openRunForLoop
                                        sourceProgram fuel cond post body
                                        postOutcome.state
                                  | .brk | .cont =>
                                      Simulation.Interaction.error
                                        .InvalidInstruction
                                  | .leave | .halt _ =>
                                      Simulation.Interaction.pure postOutcome))
                              afterBodyTranscript (.error .OutOfFuel)) :
                          exists used,
                            used <= InteractionStaticCost.loopBudget sourceProgram
                              (Nat.succ fuel) cond post body /\
                            Simulation.Interaction.Follows
                              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                                policy cfg used loopLabel target)
                              (conditionTranscript ++
                                (bodyTranscript ++ afterBodyTranscript)) := by
                        obtain ⟨targetPostEntry, rfl, hPostStateRel,
                            hPostFits, hBodyReturns⟩ := hExit
                        rcases Simulation.Interaction.Executes.bind_cases
                            hAfterBodyPostExec with
                          ⟨postError, hOutcome, hPostSourceError⟩ |
                            ⟨postOutcome, postTranscript, afterPostTranscript,
                              hPostTranscript, hPostExec, hAfterPostExec⟩
                        · cases hOutcome
                          obtain ⟨postFuel, hPostFuel, hTargetPostFollow⟩ :=
                            hPostTruncated (blockFuel := fuel)
                              (Nat.lt_succ_self fuel) hPostFits hBodyReturns
                              targetPostEntry hPostStateRel afterBodyTranscript hPostSourceError
                          have hTargetPostOuter :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined_follows
                              (outer := policy)
                              (inner :=
                                postStopPolicy postResult ctx loopLabel
                                  returns tokens policy)
                              (hRefines := by
                                intro label state hStop
                                simp [postStopPolicy,
                                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                                  hStop])
                              hTargetPostFollow
                          have hBodyTail :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump_follows
                              (outer := policy)
                              (inner :=
                                bodyStopPolicy bodyResult postResult ctx
                                  regular postLabel loopLabel
                                  { condOutput with
                                    slots := condOutput.slots.tail }
                                  returns tokens policy)
                              (hRefines := by
                                intro label state hStop
                                simp [bodyStopPolicy, postStopPolicy,
                                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                                  hStop])
                              hTargetBodyExec
                              (hPostEntryNoStop hBodyReturns hPostStateRel hPostFits)
                              hTargetPostOuter
                          have hTargetExec :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump_follows
                              hTargetConditionExec
                              (hBodyEntryNoStop hAfterCondReturns
                                hAfterCondRel hAfterCondFits)
                              hBodyTail
                          exact ⟨bodyFuel + postFuel + 1, by
                            rw [InteractionStaticCost.loopBudget_succ]
                            omega, by
                              simpa [List.append_assoc, Nat.add_assoc]
                                using hTargetExec⟩
                        · subst afterBodyTranscript
                          obtain ⟨postFuel, postRemaining, targetPostOutcome,
                              hPostFuel, hTargetPostExec, hPostRelRaw⟩ :=
                            hPostDone (blockFuel := fuel)
                              (Nat.lt_succ_self fuel) hPostFits hBodyReturns
                              targetPostEntry hPostStateRel postTranscript
                              postOutcome hPostExec
                          have hPostRel :
                              InteractionControlPreservation.OpenOutcome.Rel
                                postResult (outerContext ctx) loopLabel
                                returns tokens postOutcome targetPostOutcome := by
                            simpa [hBodyReturns] using hPostRelRaw
                          rcases postOutcome with ⟨postState, postMode⟩
                          cases postMode with
                          | regular =>
                              obtain ⟨targetLoopEntry, rfl, hLoopStateRel,
                                  hLoopFits, hPostReturns⟩ :=
                                InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                                  hPostRequire hPostRel
                              obtain ⟨loopFuel, hLoopFuel,
                                  hTargetLoopFollow⟩ :=
                                ih hLoopFits hPostReturns
                                  (fun {blockFuel} {bodySource} hFuel =>
                                    hBodyDone (Nat.lt_trans hFuel
                                      (Nat.lt_succ_self fuel)))
                                  (fun {blockFuel} {bodySource} hFuel =>
                                    hBodyTruncated (Nat.lt_trans hFuel
                                      (Nat.lt_succ_self fuel)))
                                  (fun {blockFuel} {postSource} hFuel =>
                                    hPostDone (Nat.lt_trans hFuel
                                      (Nat.lt_succ_self fuel)))
                                  (fun {blockFuel} {postSource} hFuel =>
                                    hPostTruncated (Nat.lt_trans hFuel
                                      (Nat.lt_succ_self fuel)))
                                  targetLoopEntry hLoopStateRel afterPostTranscript hAfterPostExec
                              have hPostAndLoop :=
                                InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump_follows
                                  (outer := policy)
                                  (inner :=
                                    postStopPolicy postResult ctx loopLabel
                                      returns tokens policy)
                                  (hRefines := by
                                    intro label state hStop
                                    simp [postStopPolicy,
                                      InteractionControlPreservation.OpenOutcome.pushStopJump,
                                      hStop])
                                  hTargetPostExec
                                  (hLoopEntryNoStop hPostReturns hLoopStateRel
                                    hLoopFits)
                                  hTargetLoopFollow
                              have hBodyTail :=
                                InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump_follows
                                  (outer := policy)
                                  (inner :=
                                    bodyStopPolicy bodyResult postResult ctx
                                      regular postLabel loopLabel
                                      { condOutput with
                                        slots := condOutput.slots.tail }
                                      returns tokens policy)
                                  (hRefines := by
                                    intro label state hStop
                                    simp [bodyStopPolicy, postStopPolicy,
                                      InteractionControlPreservation.OpenOutcome.pushStopJump,
                                      hStop])
                                  hTargetBodyExec
                                  (hPostEntryNoStop hBodyReturns hPostStateRel
                                    hPostFits)
                                  hPostAndLoop
                              have hTargetExec :=
                                InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump_follows
                                  hTargetConditionExec
                                  (hBodyEntryNoStop hAfterCondReturns
                                    hAfterCondRel hAfterCondFits)
                                  hBodyTail
                              exact
                                ⟨bodyFuel + (postFuel + loopFuel) + 1,
                                  by
                                    rw [InteractionStaticCost.loopBudget_succ]
                                    omega, by
                                      simpa [List.append_assoc, Nat.add_assoc]
                                        using hTargetExec⟩
                          | brk =>
                              obtain ⟨label, targetState, hLabel, _⟩ :=
                                TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim
                                  hPostRel.1
                              simp [outerContext,
                                TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                                at hLabel
                          | cont =>
                              obtain ⟨label, targetState, hLabel, _⟩ :=
                                TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim
                                  hPostRel.1
                              simp [outerContext,
                                TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                                at hLabel
                          | leave => cases hAfterPostExec
                          | halt kind => cases hAfterPostExec
                      cases bodyMode with
                      | brk => cases hAfterBodyExec
                      | regular =>
                          exact continueWithPost
                            (InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                              hBodyRequire hBodyRel)
                            hAfterBodyExec
                      | cont =>
                          exact continueWithPost
                            (body_continue_to_post hBodyRel) hAfterBodyExec
                      | leave => cases hAfterBodyExec
                      | halt kind => cases hAfterBodyExec

theorem composeInitializer_truncation_bounded_under
    {initResult result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry loopLabel regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context} {loopInput : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {initRun : Simulation.Interaction EVMException Structured.Outcome}
    {loopRun : RunState ->
      Simulation.Interaction EVMException Structured.Outcome}
    {initBudget loopBudget : Nat}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hInitRequire : initResult.requireFallthrough? loopInput = some ())
    (hInitDone :
      InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
        initResult cfg entry (outerContext ctx) loopLabel source tokens
        initRun initBudget
        (initStopPolicy initResult ctx loopLabel
          source.returns tokens policy))
    (hInitTruncated :
      InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
        initResult cfg entry (outerContext ctx) loopLabel source tokens
        initRun initBudget
        (initStopPolicy initResult ctx loopLabel
          source.returns tokens policy))
    (hLoopEntryNoStop :
      forall {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = source.returns ->
        TypedCfgPreservation.StateRel loopSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length ->
          policy loopLabel targetState = false)
    (hLoopTruncated :
      forall loopSource,
        loopSource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.FrameFits
            initResult (outerContext ctx)
            (Structured.Outcome.regular loopSource) ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          result cfg loopLabel ctx regular loopSource tokens
          (loopRun loopSource) loopBudget policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (Simulation.Interaction.bind initRun
        (fun initOutcome =>
          match initOutcome.mode with
          | .regular => loopRun initOutcome.state
          | .brk | .cont =>
              Simulation.Interaction.error .InvalidInstruction
          | .leave | .halt _ =>
              Simulation.Interaction.pure initOutcome))
      (initBudget + loopBudget) policy := by
  intro target hStateRel transcript hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    ⟨initError, hOutcome, hInitSourceError⟩ |
      ⟨initOutcome, initTranscript, restTranscript,
        hTranscript, hInitExec, hAfterInitExec⟩
  · cases hOutcome
    obtain ⟨initFuel, hInitFuel, hTargetInitFollow⟩ :=
      hInitTruncated target hStateRel transcript hInitSourceError
    have hTargetOuter :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined_follows
        (outer := policy)
        (inner :=
          initStopPolicy initResult ctx loopLabel
            source.returns tokens policy)
        (hRefines := by
          intro label state hStop
          simp [initStopPolicy,
            InteractionControlPreservation.OpenOutcome.pushStopJump,
            hStop])
        hTargetInitFollow
    exact ⟨initFuel, by omega, hTargetOuter⟩
  · subst transcript
    obtain ⟨initFuel, initRemaining, targetInitOutcome, hInitFuel,
        hTargetInitExec, hInitRel⟩ :=
      hInitDone target hStateRel initTranscript initOutcome hInitExec
    rcases initOutcome with ⟨initState, initMode⟩
    cases initMode with
    | regular =>
        obtain ⟨targetLoopEntry, rfl, hLoopStateRel,
            hLoopFits, hInitReturns⟩ :=
          InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
            hInitRequire hInitRel
        obtain ⟨loopFuel, hLoopFuel, hTargetLoopFollow⟩ :=
          hLoopTruncated initState hInitReturns hInitRel.2.1
            targetLoopEntry hLoopStateRel restTranscript hAfterInitExec
        have hTargetExec :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump_follows
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx loopLabel
                source.returns tokens policy)
            (hRefines := by
              intro label state hStop
              simp [initStopPolicy,
                InteractionControlPreservation.OpenOutcome.pushStopJump,
                hStop])
            hTargetInitExec
            (hLoopEntryNoStop hInitReturns hLoopStateRel hLoopFits)
            hTargetLoopFollow
        exact ⟨initFuel + loopFuel, by omega,
          by simpa using hTargetExec⟩
    | brk =>
        obtain ⟨label, targetState, hLabel, _⟩ :=
          TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim hInitRel.1
        simp [outerContext,
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          at hLabel
    | cont =>
        obtain ⟨label, targetState, hLabel, _⟩ :=
          TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim hInitRel.1
        simp [outerContext,
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          at hLabel
    | leave => cases hAfterInitExec
    | halt kind => cases hAfterInitExec



end Loop

namespace Switch

open InteractionSwitchPreservation.Switch

/-- Prepend the compiler-owned default-arm entry to a truncating selected
body. The route itself exposes no source interaction. -/
theorem default_some
    {compilerFuel sourceFuel bodyBudget : Nat}
    {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hEnclosingFallthrough :
      enclosingResult.fallthrough? = some bodyShape)
    (hBodyEntryNoStop :
      forall targetAfter,
        TypedCfgPreservation.StateRel
            (source.withEVM { source.evm with stack := stack })
            tokens targetAfter ->
          policy (.generated supply 2000) targetAfter = false)
    (hBody :
      forall {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000)
            bodyShape regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        bodyResult.requireFallthrough? bodyShape = some () ->
        enclosingResult.fallthrough? = some bodyShape ->
        BoundedTruncationExecPreservesUnder
          bodyResult cfg (.generated supply 2000) ctx regular
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
            (source.withEVM { source.evm with stack := stack }))
          bodyBudget policy) :
    BoundedTruncationExecPreservesUnder
      enclosingResult cfg entry ctx regular source tokens
      (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
        (source.withEVM { source.evm with stack := stack }))
      (bodyBudget + 1) policy := by
  obtain ⟨bodyResult, hBodyCompile, hRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
      hPopType hCompile
  subst result
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram bodyResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hMem]
  have hBodyPreserves :=
    hBody hBodyCompile hBodyBlocks hBodyCalls
      hRequire hEnclosingFallthrough
  have hBodyLifted :=
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.change_result_of_required_fallthrough
      hRequire hEnclosingFallthrough hBodyPreserves
  apply
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.prepend_closed_jump
  · intro target hStateRel
    exact
      InteractionSwitchPreservation.Switch.openStep_pop_jump
        (entry := entry) (label := .generated supply 2000)
        (input := valueShape) (output := bodyShape)
        hBlocks (by simp) hPopType hStateRel hPop
  · exact hBodyEntryNoStop
  · exact hBodyLifted

theorem cases_some
    {compilerFuel sourceFuel bodyBudget : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular = some result)
    (hSupply : base + 1 <= supply)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = some selected)
    (hEnclosingFallthrough :
      enclosingResult.fallthrough? = some bodyShape)
    (hRegular : TypedCfgCompilerFacts.RegularAtSupply regular base)
    (hBoundary :
      InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
        cfg source.returns tokens policy base regular)
    (hValueActivation :
      TypedCfgPreservation.ActivationInput tokens valueShape)
    (hValueFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        valueShape source.evm.stack.length)
    (hBodyActivation :
      TypedCfgPreservation.ActivationInput tokens bodyShape)
    (hBodyFits :
      TypedCfgCompiler.Shape.SourceFrameFits bodyShape stack.length)
    (hDefaultEntryNoStop :
      forall targetAfter,
        TypedCfgPreservation.StateRel source tokens targetAfter ->
          policy (LabelSupply.label base 1) targetAfter = false)
    (hCase :
      forall {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (TypedCfgCompiler.switchBodyLabel base caseIdx)
            bodyShape regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        base + 1 <= caseSupply ->
        bodyResult.requireFallthrough? bodyShape = some () ->
        enclosingResult.fallthrough? = some bodyShape ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          bodyResult cfg
          (TypedCfgCompiler.switchBodyLabel base caseIdx) ctx regular
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          bodyBudget policy)
    (hDefault :
      defaultBody = some selected ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          enclosingResult cfg (LabelSupply.label base 1) ctx regular
          source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          (bodyBudget + 1) policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      enclosingResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram sourceFuel selected
        (source.withEVM { source.evm with stack := stack }))
      (bodyBudget + cases.length + 1) policy := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefaultSelected : defaultBody = some selected := by
            simpa [Structured.Switch.select] using hSelect
          simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hDefault hDefaultSelected
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          obtain
              ⟨bodyResult, tail, hBodyCompile, hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hBodyCalls :
              TypedCfgPreservation.CallsInProgram
                bodyResult generatedCalls := by
            intro site hMem
            apply hResultCalls site
            simp [hResult, hMem]
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hTailCalls :
              TypedCfgPreservation.CallsInProgram tail generatedCalls := by
            intro site hMem
            apply hResultCalls site
            simp [hResult, hMem]
          by_cases hEq : caseValue = value
          · have hSelected : body = selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            subst selected
            have hBodyPreserves :=
              hCase hBodyCompile hBodyBlocks hBodyCalls
                hSupply hRequire hEnclosingFallthrough
            have hBodyLifted :=
              InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.change_result_of_required_fallthrough
                hRequire hEnclosingFallthrough hBodyPreserves
            have hBodyPadded :=
              InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.mono_budget
                hBodyLifted
                (show bodyBudget <= bodyBudget + rest.length by omega)
            have hFromCase :
                InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchCaseLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyBudget + rest.length) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.prepend_closed_jump
              · intro target hStateRel
                exact
                  openStep_pop_jump
                    (entry := TypedCfgCompiler.switchCaseLabel base idx)
                    (label := TypedCfgCompiler.switchBodyLabel base idx)
                    (input := valueShape) (output := bodyShape)
                    hBlocks (by simp [hResult]) hPopType hStateRel hPop
              · intro targetAfter hAfterRel
                have hBodyShape :
                    TypedCfgPreservation.LabelShape cfg
                      (TypedCfgCompiler.switchBodyLabel base idx)
                      bodyShape :=
                  TypedCfgPreservation.LabelShape.of_compileBlockFuel?
                    hBodyCompile hBodyBlocks
                have hBodyBoundary :
                    InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
                      cfg
                        (source.withEVM
                          { source.evm with stack := stack }).returns
                        tokens policy base regular :=
                  hBoundary.congr_returns rfl
                simpa [TypedCfgCompiler.switchBodyLabel] using
                  hBodyBoundary.eq_false_of_stateRel
                    (scope := base) (tag := 6 * idx + 1005)
                    (Nat.le_refl base)
                    (hRegular.current_generated_ne (by omega))
                    hBodyShape hBodyActivation hAfterRel hBodyFits
              · exact hBodyPadded
            have hFromTest :
                InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  (((bodyBudget + rest.length) + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.prepend_closed_jump
              · intro target hStateRel
                rcases
                    openStep_test
                      (testLabel := TypedCfgCompiler.switchTestLabel base idx)
                      (caseLabel := TypedCfgCompiler.switchCaseLabel base idx)
                      (nextTest :=
                        TypedCfgCompilerFacts.Switch.nextTestLabel
                          base idx rest)
                      (caseValue := caseValue) (value := value)
                      hBlocks (by simp [hResult]) hHead hStateRel hPop with
                  ⟨targetAfter, hTargetRun, hAfterRel⟩
                refine ⟨targetAfter, ?_, hAfterRel⟩
                simpa [hEq] using hTargetRun
              · intro targetAfter hAfterRel
                have hCaseShape :
                    TypedCfgPreservation.LabelShape cfg
                      (TypedCfgCompiler.switchCaseLabel base idx)
                      valueShape :=
                  TypedCfgPreservation.LabelShape.of_hasEntry
                    (TypedCfgCompilerFacts.Switch.cases_cons_case_hasEntry
                      hHead hPopType hCompile) hBlocks
                simpa [TypedCfgCompiler.switchCaseLabel] using
                  hBoundary.eq_false_of_stateRel
                    (scope := base) (tag := 6 * idx + 1003)
                    (Nat.le_refl base)
                    (hRegular.current_generated_ne (by omega))
                    hCaseShape hValueActivation hAfterRel hValueFits
              · exact hFromCase
            simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel] using hFromTest
          · have hTailSelect :
                Structured.Switch.select value rest defaultBody =
                  some selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            have hTailPreserves :=
              ih hTailCompile
                (Nat.le_trans hSupply
                  (TypedCfgCompilerFacts.Supply.block_next_ge hBodyCompile))
                hTailBlocks hTailCalls hTailSelect hCase hDefault
            have hSkipped :
                InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel selected
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyBudget + rest.length + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.prepend_closed_jump
              · intro target hStateRel
                rcases
                    openStep_test
                      (testLabel := TypedCfgCompiler.switchTestLabel base idx)
                      (caseLabel := TypedCfgCompiler.switchCaseLabel base idx)
                      (nextTest :=
                        TypedCfgCompilerFacts.Switch.nextTestLabel
                          base idx rest)
                      (caseValue := caseValue) (value := value)
                      hBlocks (by simp [hResult]) hHead hStateRel hPop with
                  ⟨targetAfter, hTargetRun, hAfterRel⟩
                refine ⟨targetAfter, ?_, hAfterRel⟩
                simpa [hEq] using hTargetRun
              · intro targetAfter hAfterRel
                cases rest with
                | nil =>
                    simpa [
                      TypedCfgCompilerFacts.Switch.nextTestLabel,
                      TypedCfgCompilerFacts.Switch.casesEntryLabel] using
                      hDefaultEntryNoStop targetAfter hAfterRel
                | cons next rest =>
                    have hNextShape :
                        TypedCfgPreservation.LabelShape cfg
                          (TypedCfgCompiler.switchTestLabel base (idx + 1))
                          valueShape :=
                      TypedCfgPreservation.LabelShape.of_hasEntry
                        (TypedCfgCompilerFacts.Switch.cases_cons_test_hasEntry
                          hHead hPopType hTailCompile) hTailBlocks
                    simpa [
                      TypedCfgCompilerFacts.Switch.nextTestLabel,
                      TypedCfgCompilerFacts.Switch.casesEntryLabel] using
                      hBoundary.eq_false_of_stateRel
                        (scope := base)
                        (tag := 6 * (idx + 1) + 1001)
                        (Nat.le_refl base)
                        (hRegular.current_generated_ne (by omega))
                        hNextShape hValueActivation hAfterRel hValueFits
              · simpa [
                  TypedCfgCompilerFacts.Switch.nextTestLabel] using
                  hTailPreserves
            simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel] using hSkipped


end Switch

namespace Block

open InteractionControlPreservation.Block

theorem nil_succ
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          [] ctx supply entry input regular = some result) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1) { stmts := [] } source)
      1 policy := by
  intro target hStateRel transcript hSourceExec
  simp only [
    InteractionSemantics.Block.openRun,
    EffectSemantics.Control.Block.run] at hSourceExec
  cases hSourceExec

theorem cons_succ
    {compilerFuel sourceFuel headBudget tailBudget : Nat}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hMiddleNoStop :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape}
          {middleSource : RunState} {targetMiddle : EVMState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        InteractionControlPreservation.OpenOutcome.Rel headResult ctx
            (TypedCfgCompiler.restLabel supply) source.returns tokens
            (.regular middleSource)
            (.jump (TypedCfgCompiler.restLabel supply) targetMiddle) ->
          policy (TypedCfgCompiler.restLabel supply) targetMiddle = false)
    (hHeadNoTail :
      forall {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        TypedCfgPreservation.BlocksInProgram headResult cfg ->
        TypedCfgPreservation.CallsInProgram headResult generatedCalls ->
        headResult.fallthrough? = none ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget policy /\
          InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget policy)
    (hHeadWithTail :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        TypedCfgPreservation.BlocksInProgram headResult cfg ->
        TypedCfgPreservation.CallsInProgram headResult generatedCalls ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        result = headResult.append tailResult ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget
            (InteractionControlPreservation.OpenOutcome.pushStopJump headResult ctx
              (TypedCfgCompiler.restLabel supply)
              source.returns tokens policy) /\
          InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget
            (InteractionControlPreservation.OpenOutcome.pushStopJump headResult ctx
              (TypedCfgCompiler.restLabel supply)
              source.returns tokens policy))
    (hTailTruncated :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        TypedCfgPreservation.CallsInProgram tailResult generatedCalls ->
        middleSource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.FrameFits headResult ctx
          (Structured.Outcome.regular middleSource) ->
        result = headResult.append tailResult ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder tailResult cfg
          (TypedCfgCompiler.restLabel supply) ctx regular
          middleSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
          tailBudget policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := stmt :: rest } source)
      (headBudget + tailBudget) policy := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    have hHeadPair :=
      hHeadNoTail hHeadCompile hBlocks hResultCalls hFallthrough
    have hIgnored :=
      InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.ignore_tail_of_no_fallthrough
        (resultRegular := regular)
        (tailRun := fun middleSource =>
          InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
        hFallthrough
        hHeadPair.1 hHeadPair.2
    have hPadded :=
      InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.mono_budget hIgnored
        (show headBudget <= headBudget + tailBudget by omega)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hPadded
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHeadCalls :=
      TypedCfgPreservation.CallsInProgram.left_of_append hResultCalls
    have hTailCalls :=
      TypedCfgPreservation.CallsInProgram.right_of_append hResultCalls
    have hHeadPair :=
      hHeadWithTail hHeadCompile hHeadBlocks hHeadCalls hFallthrough
        hTailCompile hTailBlocks rfl
    have hComposed :=
      InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.sequence
        hHeadPair.1 hHeadPair.2
        (fun hRel =>
          hMiddleNoStop hHeadCompile hFallthrough
            hTailCompile hTailBlocks hRel)
        (fun middleSource hReturns hFits =>
          hTailTruncated hHeadCompile hFallthrough hTailCompile
            hTailBlocks hTailCalls hReturns hFits rfl)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hComposed


end Block

namespace Stmt

open InteractionLoopPreservation.Loop
open InteractionLoopPreservation.Loop.Stmt
open InteractionTruncationOwnerPreservation.OpenOutcome.Loop



/-- At zero recursive fuel, recursive statements truncate immediately. The
nonrecursive statement forms are independently proved incapable of structural
fuel exhaustion. -/
theorem zero
    {program : Structured.Program} {stmt : Structured.Stmt}
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy} :
    BoundedTruncationExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Stmt.openRun program 0 stmt source)
      (InteractionStaticCost.stmtBudget program 0 stmt)
      policy := by
  cases stmt with
  | code code =>
      apply BoundedTruncationExecPreservesUnder.vacuous
      unfold InteractionSemantics.Stmt.openRun
      simp only [EffectSemantics.Control.Stmt.run]
      exact Assembly.InteractionFuelSafety.NotOutOfFuel.bind
        (InteractionFuelSafety.Code.openRun code source)
        (fun _ => .done trivial)
  | if_ cond body =>
      apply BoundedTruncationExecPreservesUnder.immediate
      rfl
  | switch scrutinee cases defaultBody =>
      apply BoundedTruncationExecPreservesUnder.immediate
      rfl
  | for_ init cond post body =>
      apply BoundedTruncationExecPreservesUnder.immediate
      rfl
  | brk =>
      apply BoundedTruncationExecPreservesUnder.vacuous
      exact .done trivial
  | cont =>
      apply BoundedTruncationExecPreservesUnder.vacuous
      exact .done trivial
  | leave =>
      apply BoundedTruncationExecPreservesUnder.vacuous
      cases hReturns : source.returns with
      | nil =>
          change Simulation.Interaction.AllDone
            Assembly.InteractionFuelSafety.NotOutOfFuel
            (match source.returns with
            | [] => Simulation.Interaction.error .InvalidInstruction
            | _ :: _ => Simulation.Interaction.pure
                (Structured.Outcome.leave source))
          rw [hReturns]
          exact .done (by
            simp [Assembly.InteractionFuelSafety.NotOutOfFuel])
      | cons frame rest =>
          change Simulation.Interaction.AllDone
            Assembly.InteractionFuelSafety.NotOutOfFuel
            (match source.returns with
            | [] => Simulation.Interaction.error .InvalidInstruction
            | _ :: _ => Simulation.Interaction.pure
                (Structured.Outcome.leave source))
          rw [hReturns]
          exact .done trivial
  | call name =>
      apply BoundedTruncationExecPreservesUnder.immediate
      rfl
  | terminal kind =>
      apply BoundedTruncationExecPreservesUnder.vacuous
      unfold InteractionSemantics.Stmt.openRun
      simp only [EffectSemantics.Control.Stmt.run]
      exact Assembly.InteractionFuelSafety.NotOutOfFuel.bind
        (InteractionFuelSafety.Terminal.openStep kind source)
        (fun _ => .done trivial)

/-- Structural truncation of a compiled `if` can occur only in its selected
body. The condition is primitive code and is independently fuel-safe. -/
theorem if_succ
    {compilerFuel sourceFuel : Nat}
    {sourceProgram : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRegular : TypedCfgCompilerFacts.RegularAtSupply regular supply)
    (hActivation : TypedCfgPreservation.ActivationInput tokens input)
    (hBoundary :
      RecursiveBoundary cfg source.returns tokens policy supply regular)
    (hBody :
      forall {output : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : RunState},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            { output with slots := output.slots.tail } regular =
          some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        afterCond.returns = source.returns ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { output with slots := output.slots.tail }
            afterCond.evm.stack.length ->
        bodyResult.requireFallthrough?
            { output with slots := output.slots.tail } = some () ->
        result.fallthrough? =
          some { output with slots := output.slots.tail } ->
        BoundedTruncationExecPreservesUnder
          bodyResult cfg (LabelSupply.label supply 0) ctx
          regular afterCond tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterCond)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel body)
          policy) :
    BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.if_ cond body) source)
      (InteractionStaticCost.stmtBudget
        sourceProgram (sourceFuel + 1) (.if_ cond body))
      policy := by
  intro target hStateRel transcript hSourceExec
  obtain
      ⟨output, _condition, bodyResult,
        hType, hSource, _hHead, hBodyCompile,
        hBodyRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
  let bodyInput : TypedCfg.Shape :=
    { output with slots := output.slots.tail }
  have hFallthrough : result.fallthrough? = some bodyInput := by
    simp [bodyInput, hResult]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hResult, hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram bodyResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hResult, hMem]
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term := .jumpi (LabelSupply.label supply 0) regular }
  have hFind : cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated, hResult])
  have hHeadRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens bodyInput)
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa [generated, bodyInput] using
      (InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := entry)
        (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular)
        hType hSource hFits hStateRel)
  have hHeadWithReturns :=
    Simulation.Interaction.Rel.strengthen_left hHeadRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  have hSourceExec' :
      Simulation.Interaction.Executes
        (Simulation.Interaction.bind
          (InteractionSemantics.Code.openRunCondition cond source)
          (fun result =>
            if result.2 then
              InteractionSemantics.Block.openRun
                sourceProgram sourceFuel body result.1
            else
              Simulation.Interaction.pure
                (Structured.Outcome.regular result.1)))
        transcript (.error .OutOfFuel) := by
    simpa [
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Stmt.run] using hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec' with
    ⟨conditionError, hOutcome, hConditionError⟩ |
      ⟨conditionResult, headTranscript, restTranscript,
        hTranscript, hConditionExec, hRestExec⟩
  · cases hOutcome
    have hSafe :=
      Simulation.Interaction.AllDone.property_of_executes
        (InteractionFuelSafety.Code.openRunCondition cond source)
        hConditionError
    exact False.elim (hSafe rfl)
  · subst transcript
    obtain ⟨targetDone, hTargetHeadExec, hDone⟩ :=
      Simulation.Interaction.Rel.executes hHeadWithReturns hConditionExec
    cases targetDone with
    | error targetError => cases hDone.1
    | ok targetOutcome =>
        rcases conditionResult with ⟨afterCond, condTrue⟩
        rcases hDone with ⟨hCondition, hReturns⟩
        cases hCondition with
        | ok hCondition =>
            rcases hCondition with
              ⟨targetAfterCond, hTargetOutcome,
                hAfterCondRel, hAfterCondFits⟩
            have hReturnsEq : afterCond.returns = source.returns := by
              simpa [InteractionSemantics.Code.ConditionReturnsEq] using hReturns
            cases condTrue with
            | false =>
                simp only [if_false] at hTargetOutcome hRestExec
                cases hRestExec
            | true =>
                simp only [if_true] at hTargetOutcome hRestExec
                subst targetOutcome
                obtain ⟨bodyFuel, hBodyFuel, hTargetBodyFollow⟩ :=
                  hBody hBodyCompile hBodyBlocks hBodyCalls hReturnsEq
                    hAfterCondFits hBodyRequire hFallthrough
                    targetAfterCond hAfterCondRel restTranscript hRestExec
                have hBodyShape :
                    TypedCfgPreservation.LabelShape
                      cfg (LabelSupply.label supply 0) bodyInput :=
                  TypedCfgPreservation.LabelShape.of_compileBlockFuel?
                    hBodyCompile hBodyBlocks
                have hBodyActivation :
                    TypedCfgPreservation.ActivationInput tokens bodyInput :=
                  (hActivation.code hType).tail
                    (TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                      hSource)
                have hNoStop :
                    policy (LabelSupply.label supply 0) targetAfterCond = false :=
                  (hBoundary.congr_returns hReturnsEq.symm).eq_false_of_stateRel
                    (scope := supply) (tag := 0)
                    (Nat.le_refl supply)
                    (hRegular.current_generated_ne (by omega))
                    hBodyShape hBodyActivation hAfterCondRel hAfterCondFits
                have hContinuationFollow :
                    Simulation.Interaction.Follows
                      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
                        policy cfg bodyFuel
                        (.jump (LabelSupply.label supply 0) targetAfterCond))
                      restTranscript := by
                  simpa [
                    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                    hNoStop] using hTargetBodyFollow
                have hTargetFollow :
                    Simulation.Interaction.Follows
                      (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                        policy cfg (bodyFuel + 1) entry target)
                      (headTranscript ++ restTranscript) := by
                  rw [
                    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                  exact Simulation.Interaction.Follows.bind_ok
                    hTargetHeadExec hContinuationFollow
                exact ⟨bodyFuel + 1, by
                  rw [InteractionStaticCost.stmtBudget_if_succ]
                  omega, hTargetFollow⟩

theorem switch_succ
    {compilerFuel sourceFuel : Nat}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRegular : TypedCfgCompilerFacts.RegularAtSupply regular supply)
    (hActivation : TypedCfgPreservation.ActivationInput tokens input)
    (hBoundary :
      InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
        cfg source.returns tokens policy supply regular)
    (hBody :
      forall {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyInput : TypedCfg.Shape}
        {body : Structured.Block}
        {bodyResult : TypedCfgCompiler.Result}
        {afterPop : RunState} {value : Word},
        Structured.Switch.select value cases defaultBody = some body ->
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
            bodySupply bodyEntry bodyInput regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        supply + 1 <= bodySupply ->
        afterPop.returns = source.returns ->
        TypedCfgCompiler.Shape.SourceFrameFits
          bodyInput afterPop.evm.stack.length ->
        bodyResult.requireFallthrough? bodyInput = some () ->
        result.fallthrough? = some bodyInput ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          bodyResult cfg bodyEntry ctx regular afterPop tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterPop)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel body)
          policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (InteractionStaticCost.stmtBudget sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody))
      policy := by
  intro target hStateRel transcript hSourceExec
  obtain
      ⟨valueShape, valueSlot, caseResult, defaultResult,
        hType, hSource, hValue, hCasesCompileRaw,
        hDefaultCompileRaw, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch hCompile
  let bodyShape : TypedCfg.Shape :=
    { valueShape with slots := valueShape.slots.tail }
  have hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
    cases valueShape with
    | mk slots tail =>
        cases slots with
        | nil => simp at hValue
        | cons slot rest => simp [bodyShape, TypedCfg.Instr.type?]
  have hCasesCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          supply (supply + 1) 0 valueShape bodyShape regular =
        some caseResult := by
    simpa [bodyShape] using hCasesCompileRaw
  have hDefaultCompile :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel defaultBody ctx
          caseResult.next (LabelSupply.label supply 1)
          valueShape bodyShape regular = some defaultResult := by
    simpa [bodyShape] using hDefaultCompileRaw
  cases compilerFuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCasesCompile
  | succ bodyCompilerFuel =>
      have hFallthrough : result.fallthrough? = some bodyShape := by
        simp [bodyShape, hResult]
      have hCaseBlocks :
          TypedCfgPreservation.BlocksInProgram caseResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hResult, hMem]
      have hCaseCalls :
          TypedCfgPreservation.CallsInProgram caseResult generatedCalls := by
        intro site hMem
        apply hResultCalls site
        simp [hResult, hMem]
      have hDefaultBlocks :
          TypedCfgPreservation.BlocksInProgram defaultResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hResult, hMem]
      have hDefaultCalls :
          TypedCfgPreservation.CallsInProgram defaultResult generatedCalls := by
        intro site hMem
        apply hResultCalls site
        simp [hResult, hMem]
      have hCasesNext : supply + 1 <= caseResult.next :=
        TypedCfgCompilerFacts.Supply.cases_next_ge
          hValue hPopType hCasesCompile
      let firstTest :=
        TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg scrutinee
          output := valueShape
          term := .jump firstTest }
      have hFind : cfg.findBlock? entry = some generated := by
        exact hBlocks generated (by simp [generated, firstTest, hResult])
      have hHeadRel :
          Simulation.Interaction.Rel
            (InteractionBranchPreservation.Code.JumpDoneRel
              firstTest tokens valueShape)
            (InteractionSemantics.Code.openRun scrutinee source)
            (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
        simp only [
          TypedCfg.InteractionSemantics.Program.openStep,
          TypedCfg.Control.Program.step, hFind]
        simpa [generated] using
          (InteractionBranchPreservation.Code.openRun_jump_toCfg
            (entry := entry) (label := firstTest)
            hType hFits hStateRel)
      have hHeadWithReturns :=
        Simulation.Interaction.Rel.strengthen_left hHeadRel
          (InteractionSemantics.Code.openRun_returns scrutinee source)
      have hSourceExec' :
          Simulation.Interaction.Executes
            (Simulation.Interaction.bind
              (InteractionSemantics.Code.openRun scrutinee source)
              (fun afterScrutinee =>
                match afterScrutinee.evm.stack.pop with
                | none => Simulation.Interaction.error .StackUnderflow
                | some ⟨stack, value⟩ =>
                    let afterPop :=
                      afterScrutinee.withEVM
                        { afterScrutinee.evm with stack := stack }
                    match Structured.Switch.select value cases defaultBody with
                    | some selected =>
                        InteractionSemantics.Block.openRun
                          sourceProgram sourceFuel selected afterPop
                    | none =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular afterPop)))
            transcript (.error .OutOfFuel) := by
        simpa [
          InteractionSemantics.Stmt.openRun,
          EffectSemantics.Control.Stmt.run,
          EffectSemantics.Ordinary.runStateModel_evm,
          EffectSemantics.Ordinary.runStateModel_withEVM] using hSourceExec
      rcases Simulation.Interaction.Executes.bind_cases hSourceExec' with
        ⟨scrutineeError, hOutcome, hScrutineeError⟩ |
          ⟨afterScrutinee, headTranscript, restTranscript,
            hTranscript, hScrutineeExec, hRestExec⟩
      · cases hOutcome
        obtain ⟨targetDone, hTargetHeadExec, hDone⟩ :=
          Simulation.Interaction.Rel.executes
            hHeadWithReturns hScrutineeError
        cases targetDone with
        | error targetError =>
            have hTargetExec :
                Simulation.Interaction.Executes
                  (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                    policy cfg 1 entry target)
                  transcript (.error targetError) := by
              rw [
                TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
              exact Simulation.Interaction.Executes.bind_error hTargetHeadExec
            exact ⟨1, by
              rw [InteractionStaticCost.stmtBudget_switch_succ]
              omega, hTargetExec.follows⟩
        | ok targetOutcome => cases hDone.1
      · subst transcript
        obtain ⟨targetDone, hTargetHeadExec, hDone⟩ :=
          Simulation.Interaction.Rel.executes hHeadWithReturns hScrutineeExec
        cases targetDone with
        | error targetError => cases hDone.1
        | ok targetOutcome =>
            rcases hDone with ⟨hHead, hReturns⟩
            cases hHead with
            | ok hJump =>
                rcases hJump with
                  ⟨targetAfterScrutinee, hTargetOutcome,
                    hAfterRel, hAfterFits⟩
                subst targetOutcome
                have hReturnsEq :
                    afterScrutinee.returns = source.returns := by
                  simpa using hReturns
                have hSourceOne :
                    1 <= TypedCfgCompiler.Shape.sourceLength valueShape :=
                  TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                    hSource
                have hStackOne :
                    1 <= afterScrutinee.evm.stack.length :=
                  Nat.le_trans hSourceOne hAfterFits.1
                obtain ⟨stack, value, hPop⟩ :=
                  Assembly.PrimStep.Stack.exists_pop_of_one_le hStackOne
                have hPopLength :
                    afterScrutinee.evm.stack.length = stack.length + 1 := by
                  cases hStack : afterScrutinee.evm.stack with
                  | nil => simp [hStack, EvmYul.Stack.pop] at hPop
                  | cons head tail =>
                      simp [hStack, EvmYul.Stack.pop] at hPop
                      rcases hPop with ⟨rfl, rfl⟩
                      simp [hStack]
                have hBodyFits :
                    TypedCfgCompiler.Shape.SourceFrameFits
                      bodyShape stack.length := by
                  have hTailFits :=
                    TypedCfgCompilerFacts.Shape.sourceFrameFits_tail
                      hSourceOne
                      (show
                        TypedCfgCompiler.Shape.SourceFrameFits valueShape
                          (stack.length + 1) by
                        simpa [hPopLength] using hAfterFits)
                  simpa [bodyShape] using hTailFits
                have hValueActivation :
                    TypedCfgPreservation.ActivationInput tokens valueShape :=
                  hActivation.code hType
                have hBodyActivation :
                    TypedCfgPreservation.ActivationInput tokens bodyShape :=
                  hValueActivation.tail hSourceOne
                have hAfterBoundary :
                    InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
                      cfg afterScrutinee.returns tokens policy supply regular :=
                  hBoundary.congr_returns hReturnsEq.symm
                have hNoStop :
                    policy firstTest targetAfterScrutinee = false := by
                  cases hCases : cases with
                  | nil =>
                      have hFirstShape :
                          TypedCfgPreservation.LabelShape cfg
                            (LabelSupply.label supply 1) valueShape :=
                        TypedCfgPreservation.LabelShape.of_hasEntry
                          (TypedCfgCompilerFacts.Switch.default_hasEntry
                            hPopType hDefaultCompile) hDefaultBlocks
                      simpa [
                        firstTest, hCases,
                        TypedCfgCompilerFacts.Switch.casesEntryLabel,
                        LabelSupply.label] using
                        hAfterBoundary.eq_false_of_stateRel
                          (scope := supply) (tag := 1)
                          (Nat.le_refl supply)
                          (hRegular.current_generated_ne (by omega))
                          hFirstShape hValueActivation hAfterRel hAfterFits
                  | cons next rest =>
                      have hFirstShape :
                          TypedCfgPreservation.LabelShape cfg
                            (TypedCfgCompiler.switchTestLabel supply 0)
                            valueShape :=
                        TypedCfgPreservation.LabelShape.of_hasEntry
                          (TypedCfgCompilerFacts.Switch.cases_cons_test_hasEntry
                            hValue hPopType
                            (by simpa [hCases] using hCasesCompile))
                          hCaseBlocks
                      simpa [
                        firstTest, hCases,
                        TypedCfgCompilerFacts.Switch.casesEntryLabel,
                        TypedCfgCompiler.switchTestLabel] using
                        hAfterBoundary.eq_false_of_stateRel
                          (scope := supply) (tag := 1001)
                          (Nat.le_refl supply)
                          (hRegular.current_generated_ne (by omega))
                          hFirstShape hValueActivation hAfterRel hAfterFits
                have hDefaultEntryNoStop :
                    forall targetAfter,
                      TypedCfgPreservation.StateRel
                          afterScrutinee tokens targetAfter ->
                        policy (LabelSupply.label supply 1) targetAfter = false := by
                  intro targetAfter hTargetRel
                  have hDefaultShape :
                      TypedCfgPreservation.LabelShape cfg
                        (LabelSupply.label supply 1) valueShape :=
                    TypedCfgPreservation.LabelShape.of_hasEntry
                      (TypedCfgCompilerFacts.Switch.default_hasEntry
                        hPopType hDefaultCompile) hDefaultBlocks
                  exact hAfterBoundary.eq_false_of_stateRel
                    (scope := supply) (tag := 1)
                    (Nat.le_refl supply)
                    (hRegular.current_generated_ne (by omega))
                    hDefaultShape hValueActivation hTargetRel hAfterFits
                let routeBudget :=
                  InteractionStaticCost.switchBodyBudget
                    sourceProgram sourceFuel cases defaultBody +
                    cases.length + 1
                have finishRoute
                    {routeRun :
                      Simulation.Interaction EVMException Structured.Outcome}
                    (hRoute :
                      InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
                        result cfg firstTest ctx regular afterScrutinee tokens
                        routeRun routeBudget policy)
                    (hRest :
                      Simulation.Interaction.Executes routeRun restTranscript
                        (.error .OutOfFuel)) :
                    exists targetFuel,
                      targetFuel <=
                        InteractionStaticCost.stmtBudget sourceProgram
                          (sourceFuel + 1)
                          (.switch scrutinee cases defaultBody) /\
                      Simulation.Interaction.Follows
                        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                          policy cfg targetFuel entry target)
                        (headTranscript ++ restTranscript) := by
                  obtain ⟨routeFuel, hRouteFuel, hTargetRouteFollow⟩ :=
                    hRoute targetAfterScrutinee hAfterRel
                      restTranscript hRest
                  have hContinuationFollow :
                      Simulation.Interaction.Follows
                        (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
                          policy cfg routeFuel
                          (.jump firstTest targetAfterScrutinee))
                        restTranscript := by
                    simpa [
                      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                      hNoStop] using hTargetRouteFollow
                  have hTargetFollow :
                      Simulation.Interaction.Follows
                        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                          policy cfg (routeFuel + 1) entry target)
                        (headTranscript ++ restTranscript) := by
                    rw [
                      TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                    exact Simulation.Interaction.Follows.bind_ok
                      hTargetHeadExec hContinuationFollow
                  exact ⟨routeFuel + 1, by
                    rw [InteractionStaticCost.stmtBudget_switch_succ]
                    dsimp [routeBudget] at hRouteFuel
                    omega, hTargetFollow⟩
                cases hSelect :
                    Structured.Switch.select value cases defaultBody with
                | none =>
                    simp only [hPop, hSelect] at hRestExec
                    cases hRestExec
                | some selected =>
                    have hSelectedBudget :
                        InteractionStaticCost.blockBudget
                            sourceProgram sourceFuel selected <=
                          InteractionStaticCost.switchBodyBudget
                            sourceProgram sourceFuel cases defaultBody := by
                      apply TypedCfgCompilerFacts.switch_property_of_select
                        (cases := cases) (defaultBody := defaultBody)
                        (property := fun selected =>
                          InteractionStaticCost.blockBudget
                              sourceProgram sourceFuel selected <=
                            InteractionStaticCost.switchBodyBudget
                              sourceProgram sourceFuel cases defaultBody)
                      · intro caseValue caseBody hMem
                        exact
                          InteractionStaticCost.blockBudget_le_switchBodyBudget_of_mem
                            hMem
                      · intro default hDefault
                        simpa [hDefault] using
                          InteractionStaticCost.blockBudget_le_switchBodyBudget_of_default
                            (program := sourceProgram) (fuel := sourceFuel)
                            (cases := cases) (body := default)
                      · exact hSelect
                    have hCaseRoute :
                        forall {caseBodyCompilerFuel caseSupply caseIdx : Nat}
                          {bodyResult : TypedCfgCompiler.Result},
                          TypedCfgCompiler.compileBlockFuel?
                              caseBodyCompilerFuel selected ctx caseSupply
                              (TypedCfgCompiler.switchBodyLabel supply caseIdx)
                              bodyShape regular = some bodyResult ->
                          TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
                          TypedCfgPreservation.CallsInProgram
                            bodyResult generatedCalls ->
                          supply + 1 <= caseSupply ->
                          bodyResult.requireFallthrough? bodyShape = some () ->
                          result.fallthrough? = some bodyShape ->
                          InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
                            bodyResult cfg
                            (TypedCfgCompiler.switchBodyLabel supply caseIdx)
                            ctx regular
                            (afterScrutinee.withEVM
                              { afterScrutinee.evm with stack := stack })
                            tokens
                            (InteractionSemantics.Block.openRun
                              sourceProgram sourceFuel selected
                              (afterScrutinee.withEVM
                                { afterScrutinee.evm with stack := stack }))
                            (InteractionStaticCost.switchBodyBudget
                              sourceProgram sourceFuel cases defaultBody)
                            policy := by
                      intro caseBodyCompilerFuel caseSupply caseIdx bodyResult
                        hBodyCompile hBodyBlocks hBodyCalls hBodySupply
                        hBodyRequire hResultFallthrough
                      apply
                        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.mono_budget
                          (hBody hSelect hBodyCompile hBodyBlocks hBodyCalls
                            hBodySupply (by
                              simpa [RunState.withEVM] using hReturnsEq)
                            hBodyFits hBodyRequire hResultFallthrough)
                      exact hSelectedBudget
                    have hDefaultRoute
                        (hDefaultSelected : defaultBody = some selected) :
                        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
                          result cfg (LabelSupply.label supply 1) ctx regular
                          afterScrutinee tokens
                          (InteractionSemantics.Block.openRun
                            sourceProgram sourceFuel selected
                            (afterScrutinee.withEVM
                              { afterScrutinee.evm with stack := stack }))
                          (InteractionStaticCost.switchBodyBudget
                              sourceProgram sourceFuel cases defaultBody + 1)
                          policy := by
                      have hCompileSome :
                          TypedCfgCompiler.compileDefaultFuel?
                              (bodyCompilerFuel + 1) (some selected) ctx
                              caseResult.next (LabelSupply.label supply 1)
                              valueShape bodyShape regular = some defaultResult := by
                        simpa [hDefaultSelected] using hDefaultCompile
                      apply
                        Switch.default_some
                          (enclosingResult := result)
                          (bodyBudget :=
                            InteractionStaticCost.switchBodyBudget
                              sourceProgram sourceFuel cases defaultBody)
                          hCompileSome hDefaultBlocks hDefaultCalls hPopType hPop
                          hFallthrough
                      · intro targetAfter hTargetRel
                        obtain ⟨bodyResult, hBodyCompile,
                            _hRequire, hDefaultResult⟩ :=
                          TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
                            hPopType hCompileSome
                        have hBodyBlocks :
                            TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
                          intro block hMem
                          apply hDefaultBlocks block
                          simp [hDefaultResult, hMem]
                        have hBodyShape :
                            TypedCfgPreservation.LabelShape cfg
                              (.generated caseResult.next 2000) bodyShape :=
                          TypedCfgPreservation.LabelShape.of_compileBlockFuel?
                            hBodyCompile hBodyBlocks
                        have hDefaultBodyBoundary :
                            InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
                              cfg
                                (afterScrutinee.withEVM
                                  { afterScrutinee.evm with stack := stack }).returns
                                tokens policy supply regular :=
                          hAfterBoundary.congr_returns rfl
                        exact hDefaultBodyBoundary.eq_false_of_stateRel
                          (scope := caseResult.next) (tag := 2000)
                          (Nat.le_trans (Nat.le_succ supply) hCasesNext)
                          ((hRegular.before_succ.mono hCasesNext).generated_ne
                            (Nat.le_refl caseResult.next))
                          hBodyShape hBodyActivation hTargetRel hBodyFits
                      · intro bodyResult hBodyCompile hBodyBlocks hBodyCalls
                          hBodyRequire hResultFallthrough
                        apply
                          InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.mono_budget
                            (hBody hSelect hBodyCompile hBodyBlocks hBodyCalls
                              (Nat.le_trans hCasesNext
                                (Nat.le_succ caseResult.next))
                              (by simpa [RunState.withEVM] using hReturnsEq)
                              hBodyFits hBodyRequire hResultFallthrough)
                        exact hSelectedBudget
                    have hCasesSome :=
                      Switch.cases_some
                        (enclosingResult := result)
                        (bodyBudget :=
                          InteractionStaticCost.switchBodyBudget
                            sourceProgram sourceFuel cases defaultBody)
                        hCasesCompile (Nat.le_refl (supply + 1))
                        hCaseBlocks hCaseCalls hValue hPopType hPop
                        hSelect hFallthrough hRegular hAfterBoundary
                        hValueActivation hAfterFits hBodyActivation hBodyFits
                        hDefaultEntryNoStop hCaseRoute hDefaultRoute
                    exact finishRoute hCasesSome
                      (by simpa [hPop, hSelect] using hRestExec)


theorem for_succ
    {compilerFuel sourceFuel : Nat}
    {sourceProgram : Structured.Program}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRegular : TypedCfgCompilerFacts.RegularAtSupply regular supply)
    (hActivation :
      TypedCfgPreservation.ActivationInput tokens input)
    (hBoundary :
      InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
        cfg source.returns tokens policy supply regular)
    (hInitDone :
      forall {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            (outerContext ctx) (supply + 1) entry input
            (LabelSupply.label supply 0) = some initResult ->
        TypedCfgPreservation.BlocksInProgram initResult cfg ->
        TypedCfgPreservation.CallsInProgram initResult generatedCalls ->
        TypedCfgPreservation.LabelShape cfg
          (LabelSupply.label supply 0) loopInput ->
        initResult.fallthrough? = some loopInput ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          initResult cfg entry (outerContext ctx)
          (LabelSupply.label supply 0) source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel init source)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel init)
          (initStopPolicy initResult ctx
            (LabelSupply.label supply 0)
            source.returns tokens policy))
    (hInitTruncated :
      forall {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            (outerContext ctx) (supply + 1) entry input
            (LabelSupply.label supply 0) = some initResult ->
        TypedCfgPreservation.BlocksInProgram initResult cfg ->
        TypedCfgPreservation.CallsInProgram initResult generatedCalls ->
        TypedCfgPreservation.LabelShape cfg
          (LabelSupply.label supply 0) loopInput ->
        initResult.fallthrough? = some loopInput ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          initResult cfg entry (outerContext ctx)
          (LabelSupply.label supply 0) source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel init source)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel init)
          (initStopPolicy initResult ctx
            (LabelSupply.label supply 0)
            source.returns tokens policy))
    (hBodyDone :
      forall {initResult bodyResult postResult : TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            (bodyContext ctx regular (LabelSupply.label supply 2)
              { condOutput with slots := condOutput.slots.tail })
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) = some bodyResult ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) = some postResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
        bodySource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg (LabelSupply.label supply 1)
          (bodyContext ctx regular (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail })
          (LabelSupply.label supply 2) bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel body)
          (bodyStopPolicy bodyResult postResult ctx regular
            (LabelSupply.label supply 2) (LabelSupply.label supply 0)
            { condOutput with slots := condOutput.slots.tail }
            source.returns tokens policy))
    (hBodyTruncated :
      forall {initResult bodyResult postResult : TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            (bodyContext ctx regular (LabelSupply.label supply 2)
              { condOutput with slots := condOutput.slots.tail })
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) = some bodyResult ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) = some postResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
        bodySource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          bodyResult cfg (LabelSupply.label supply 1)
          (bodyContext ctx regular (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail })
          (LabelSupply.label supply 2) bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel body)
          (bodyStopPolicy bodyResult postResult ctx regular
            (LabelSupply.label supply 2) (LabelSupply.label supply 0)
            { condOutput with slots := condOutput.slots.tail }
            source.returns tokens policy))
    (hPostDone :
      forall {initResult bodyResult postResult : TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) = some postResult ->
        TypedCfgPreservation.BlocksInProgram postResult cfg ->
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
        postSource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          postResult cfg (LabelSupply.label supply 2)
          (outerContext ctx) (LabelSupply.label supply 0)
          postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel post)
          (postStopPolicy postResult ctx (LabelSupply.label supply 0)
            source.returns tokens policy))
    (hPostTruncated :
      forall {initResult bodyResult postResult : TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) = some postResult ->
        TypedCfgPreservation.BlocksInProgram postResult cfg ->
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
        postSource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
          postResult cfg (LabelSupply.label supply 2)
          (outerContext ctx) (LabelSupply.label supply 0)
          postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel post)
          (postStopPolicy postResult ctx (LabelSupply.label supply 0)
            source.returns tokens policy)) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun sourceProgram (sourceFuel + 1)
        (.for_ init cond post body) source)
      (InteractionStaticCost.stmtBudget sourceProgram (sourceFuel + 1)
        (.for_ init cond post body)) policy := by
  rcases TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for hCompile with
    ⟨initResult, loopInput, condOutput, _condition,
      bodyResult, postResult, hInitCompileRaw, hInitFallthrough,
      hType, hSource, _hHead, hBodyCompileRaw, hBodyRequire,
      hPostCompileRaw, hPostRequire, hResult⟩
  have hInitCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
          (outerContext ctx) (supply + 1) entry input
          (LabelSupply.label supply 0) = some initResult := by
    simpa [outerContext] using hInitCompileRaw
  have hBodyCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body
          (bodyContext ctx regular (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail })
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) = some bodyResult := by
    simpa [bodyContext] using hBodyCompileRaw
  have hPostCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel post
          (outerContext ctx) bodyResult.next (LabelSupply.label supply 2)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 0) = some postResult := by
    simpa [outerContext] using hPostCompileRaw
  subst result
  have hInitBlocks : TypedCfgPreservation.BlocksInProgram initResult cfg := by
    intro block hMem; apply hBlocks block; simp [hMem]
  have hBodyBlocks : TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem; apply hBlocks block; simp [hMem]
  have hPostBlocks : TypedCfgPreservation.BlocksInProgram postResult cfg := by
    intro block hMem; apply hBlocks block; simp [hMem]
  have hInitCalls :
      TypedCfgPreservation.CallsInProgram initResult generatedCalls := by
    intro site hMem; apply hResultCalls site; simp [hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram bodyResult generatedCalls := by
    intro site hMem; apply hResultCalls site; simp [hMem]
  have hPostCalls :
      TypedCfgPreservation.CallsInProgram postResult generatedCalls := by
    intro site hMem; apply hResultCalls site; simp [hMem]
  have hConditionMem :
      conditionBlock (LabelSupply.label supply 0)
          (LabelSupply.label supply 1) regular loopInput condOutput cond ∈
        ({ blocks := initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term := .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
           next := postResult.next
           calls := initResult.calls ++ bodyResult.calls ++ postResult.calls
           fallthrough? := some { condOutput with
             slots := condOutput.slots.tail } } :
          TypedCfgCompiler.Result).blocks := by
    simp [conditionBlock]
  have hLoopShape :
      TypedCfgPreservation.LabelShape cfg
        (LabelSupply.label supply 0) loopInput := by
    refine ⟨conditionBlock (LabelSupply.label supply 0)
      (LabelSupply.label supply 1) regular loopInput condOutput cond,
      hBlocks _ hConditionMem, rfl⟩
  have hBodyShape :
      TypedCfgPreservation.LabelShape cfg (LabelSupply.label supply 1)
        { condOutput with slots := condOutput.slots.tail } :=
    TypedCfgPreservation.LabelShape.of_compileBlockFuel?
      hBodyCompile hBodyBlocks
  have hPostShape :
      TypedCfgPreservation.LabelShape cfg (LabelSupply.label supply 2)
        { condOutput with slots := condOutput.slots.tail } :=
    TypedCfgPreservation.LabelShape.of_compileBlockFuel?
      hPostCompile hPostBlocks
  have hLoopActivation :
      TypedCfgPreservation.ActivationInput tokens loopInput :=
    hActivation.blockFallthrough hInitCompile hInitFallthrough
  have hBodyActivation :
      TypedCfgPreservation.ActivationInput tokens
        { condOutput with slots := condOutput.slots.tail } :=
    (hLoopActivation.code hType).tail
      (TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource)
  have hInitSupply : supply + 1 <= initResult.next :=
    TypedCfgCompilerFacts.Supply.block_next_ge hInitCompile
  have hBodySupply : supply + 1 <= bodyResult.next :=
    Nat.le_trans hInitSupply
      (TypedCfgCompilerFacts.Supply.block_next_ge hBodyCompile)
  have hOwnerFacts :
      OwnerFacts cfg generatedCalls tokens supply
        { blocks := initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term := .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
          next := postResult.next
          calls := initResult.calls ++ bodyResult.calls ++ postResult.calls
          fallthrough? := some { condOutput with
            slots := condOutput.slots.tail } }
        initResult bodyResult postResult loopInput condOutput :=
    { bodyCalls := hBodyCalls
      postCalls := hPostCalls
      loopShape := hLoopShape
      bodyShape := hBodyShape
      postShape := hPostShape
      bodyActivation := hBodyActivation
      initSupply := hInitSupply
      bodySupply := hBodySupply
      bodyRequire := hBodyRequire
      postRequire := hPostRequire
      enclosingFallthrough := rfl }
  have hLoopEntryNoStop :
      forall {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = source.returns ->
        TypedCfgPreservation.StateRel loopSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits loopInput
            loopSource.evm.stack.length ->
          policy (LabelSupply.label supply 0) targetState = false := by
    intro loopSource targetState hReturns hRel hLoopFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 0) (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hLoopShape hLoopActivation hRel hLoopFits
  have hBodyEntryNoStop :
      forall {bodySource : RunState} {targetState : EVMState},
        bodySource.returns = source.returns ->
        TypedCfgPreservation.StateRel bodySource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
          policy (LabelSupply.label supply 1) targetState = false := by
    intro bodySource targetState hReturns hRel hBodyFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 1) (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hBodyShape hBodyActivation hRel hBodyFits
  have hPostEntryNoStop :
      forall {postSource : RunState} {targetState : EVMState},
        postSource.returns = source.returns ->
        TypedCfgPreservation.StateRel postSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
          policy (LabelSupply.label supply 2) targetState = false := by
    intro postSource targetState hReturns hRel hPostFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 2) (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hPostShape hBodyActivation hRel hPostFits
  have hInitRequire : initResult.requireFallthrough? loopInput = some () :=
    TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
      (Or.inr hInitFallthrough)
  have hInitDonePreserves :=
    hInitDone hInitCompile hInitBlocks hInitCalls hLoopShape hInitFallthrough
  have hInitTruncatedPreserves :=
    hInitTruncated hInitCompile hInitBlocks hInitCalls hLoopShape hInitFallthrough
  have hComposed :=
    composeInitializer_truncation_bounded_under
      (result :=
        { blocks := initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term := .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
          next := postResult.next
          calls := initResult.calls ++ bodyResult.calls ++ postResult.calls
          fallthrough? := some { condOutput with
            slots := condOutput.slots.tail } })
      (loopInput := loopInput)
      (loopRun := fun loopSource =>
        InteractionSemantics.Stmt.openRunForLoop
          sourceProgram sourceFuel cond post body loopSource)
      hInitRequire hInitDonePreserves hInitTruncatedPreserves hLoopEntryNoStop
      (fun loopSource hReturns hFrame => by
        rcases hFrame with ⟨shape, hShape, hLoopFits⟩
        rw [hInitFallthrough] at hShape
        cases hShape
        exact
          openRunForLoop_truncation_bounded_under
            hBlocks hConditionMem hType hSource hBodyRequire hPostRequire
            hLoopFits hReturns hBodyEntryNoStop hPostEntryNoStop
            hLoopEntryNoStop
            (fun {blockFuel} {bodySource} hFuel hBodyFits hBodyReturns =>
              hBodyDone hFuel hBodyCompile hPostCompile hBodyBlocks
                hOwnerFacts hBodyFits hBodyReturns)
            (fun {blockFuel} {bodySource} hFuel hBodyFits hBodyReturns =>
              hBodyTruncated hFuel hBodyCompile hPostCompile hBodyBlocks
                hOwnerFacts hBodyFits hBodyReturns)
            (fun {blockFuel} {postSource} hFuel hPostFits hPostReturns =>
              hPostDone hFuel hPostCompile hPostBlocks
                hOwnerFacts hPostFits hPostReturns)
            (fun {blockFuel} {postSource} hFuel hPostFits hPostReturns =>
              hPostTruncated hFuel hPostCompile hPostBlocks
                hOwnerFacts hPostFits hPostReturns))
  simpa [
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Stmt.run,
      InteractionStaticCost.stmtBudget_for_succ] using hComposed



theorem if_truncation_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave (.if_ cond body))
    (hFrameSafe : Structured.Stmt.FrameSafe (.if_ cond body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs (.if_ cond body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.if_ cond body) source)
      (InteractionStaticCost.stmtBudget
        program (sourceFuel + 1) (.if_ cond body))
      policy := by
  cases hWF with
  | if_ hBodyWF =>
      cases hFrameSafe with
      | if_ _hCondSafe hBodySafe =>
          cases hCalls with
          | if_ hBodyCallsResolved =>
              apply
                if_succ
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation contract.boundary
              intro output bodyResult afterCond
                hBodyCompile hBodyBlocks hBodyCalls hReturns
                hBodyFits hRequire hFallthrough
              apply
                hBlockOwner (Nat.le_refl sourceFuel)
                  hBodyCompile hBodyBlocks hBodyCalls
                  hBodyWF hBodySafe hBodyCallsResolved hSupports hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt := Or.inl contract.before_succ.regular
                    before := contract.before_succ
                    activation :=
                      contract.activation.stmtFallthrough
                        hCompile hFallthrough
                    boundary :=
                      (contract.boundary.mono
                        (Nat.le_succ supply)).congr_returns hReturns.symm
                    shapes :=
                      contract.shapes.of_required_fallthrough
                        hRequire hFallthrough
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      apply contract.stops
                      have hWhole :=
                        InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hRequire hFallthrough hRel
                      simpa [hReturns] using hWhole
                    nonregular := by
                      intro childResult childRegular sourceOutcome
                        targetOutcome hMode hRel
                      apply contract.nonregular hMode
                      simpa [hReturns] using hRel }

theorem switch_truncation_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave
        (.switch scrutinee cases defaultBody))
    (hFrameSafe :
      Structured.Stmt.FrameSafe (.switch scrutinee cases defaultBody))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs
        (.switch scrutinee cases defaultBody))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (InteractionStaticCost.stmtBudget program (sourceFuel + 1)
        (.switch scrutinee cases defaultBody))
      policy := by
  cases hWF with
  | switch hCasesWF hDefaultWF =>
      cases hFrameSafe with
      | switch _hScrutineeSafe hCasesSafe hDefaultSafe =>
          cases hCalls with
          | switch hCasesCalls hDefaultCalls =>
              apply
                switch_succ
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation contract.boundary
              intro bodyCompilerFuel bodySupply bodyEntry bodyInput
                body bodyResult afterPop value hSelect hBodyCompile
                hBodyBlocks hBodyResultCalls hBodySupply hReturns
                hBodyFits hRequire hFallthrough
              have hSelectedWF :=
                Structured.Switch.wf_of_select
                  hCasesWF hDefaultWF hSelect
              have hSelectedFrameSafe :=
                TypedCfgCompilerFacts.switch_property_of_select
                  hCasesSafe hDefaultSafe hSelect
              have hSelectedCalls :=
                TypedCfgCompilerFacts.switch_property_of_select
                  hCasesCalls hDefaultCalls hSelect
              have hSupply : supply <= bodySupply :=
                Nat.le_trans (Nat.le_succ supply) hBodySupply
              have hBefore := contract.before_succ.mono hBodySupply
              apply
                hBlockOwner (Nat.le_refl sourceFuel)
                  hBodyCompile hBodyBlocks hBodyResultCalls
                  hSelectedWF hSelectedFrameSafe hSelectedCalls
                  hSupports hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt := Or.inl hBefore.regular
                    before := hBefore
                    activation :=
                      contract.activation.stmtFallthrough
                        hCompile hFallthrough
                    boundary :=
                      (contract.boundary.mono hSupply).congr_returns
                        hReturns.symm
                    shapes :=
                      contract.shapes.of_required_fallthrough
                        hRequire hFallthrough
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      apply contract.stops
                      have hWhole :=
                        InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hRequire hFallthrough hRel
                      simpa [hReturns] using hWhole
                    nonregular := by
                      intro childResult childRegular sourceOutcome
                        targetOutcome hMode hRel
                      apply contract.nonregular hMode
                      simpa [hReturns] using hRel }

theorem for_truncation_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave
        (.for_ init cond post body))
    (hFrameSafe :
      Structured.Stmt.FrameSafe (.for_ init cond post body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs
        (.for_ init cond post body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (hTruncationBlockOwner :
      InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program (sourceFuel + 1)
        (.for_ init cond post body) source)
      (InteractionStaticCost.stmtBudget program (sourceFuel + 1)
        (.for_ init cond post body))
      policy := by
  cases hWF with
  | for_ hInitWF hPostWF hBodyWF =>
      cases hFrameSafe with
      | for_ hInitSafe _hCondSafe hPostSafe hBodySafe =>
          cases hCalls with
          | for_ hInitCalls hPostCalls hBodyCalls =>
              apply
                for_succ
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation contract.boundary
              · intro initResult loopInput hInitCompile hInitBlocks
                  hInitResultCalls hLoopShape hInitFallthrough
                have hInitRequire :
                    initResult.requireFallthrough? loopInput = some () :=
                  TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
                    (Or.inr hInitFallthrough)
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hInitRequire hLoopShape
                apply
                  hBlockOwner (Nat.le_refl sourceFuel)
                    hInitCompile hInitBlocks hInitResultCalls
                    hInitWF hInitSafe hInitCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · exact hSourceReturns
                · simpa [InteractionLoopPreservation.Loop.initStopPolicy] using
                    (show
                      FragmentContract cfg initResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        (supply + 1) entry (LabelSupply.label supply 0)
                        input source tokens
                        (InteractionLoopPreservation.Loop.initStopPolicy
                          initResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := contract.fits
                        regularAt := Or.inl hInitBefore.regular
                        before := hInitBefore
                        activation := contract.activation
                        boundary :=
                          (contract.boundary.mono
                            (Nat.le_succ supply)).push
                              hInitShapes hOuterBefore
                        shapes := hInitShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel
                        nonregular :=
                          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                            policy })
              · intro initResult loopInput hInitCompile hInitBlocks
                  hInitResultCalls hLoopShape hInitFallthrough
                have hInitRequire :
                    initResult.requireFallthrough? loopInput = some () :=
                  TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
                    (Or.inr hInitFallthrough)
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hInitRequire hLoopShape
                apply
                  hTruncationBlockOwner (Nat.le_refl sourceFuel)
                    hInitCompile hInitBlocks hInitResultCalls
                    hInitWF hInitSafe hInitCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · exact hSourceReturns
                · simpa [InteractionLoopPreservation.Loop.initStopPolicy] using
                    (show
                      FragmentContract cfg initResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        (supply + 1) entry (LabelSupply.label supply 0)
                        input source tokens
                        (InteractionLoopPreservation.Loop.initStopPolicy
                          initResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := contract.fits
                        regularAt := Or.inl hInitBefore.regular
                        before := hInitBefore
                        activation := contract.activation
                        boundary :=
                          (contract.boundary.mono
                            (Nat.le_succ supply)).push
                              hInitShapes hOuterBefore
                        shapes := hInitShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel
                        nonregular :=
                          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                            policy })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel bodySource hFuel hBodyCompile hPostCompile
                  hBodyBlocks hFacts hBodyFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply <= initResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.initSupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ hFacts.initSupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                have hBodyBoundaryBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 0)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyShapes :
                    BoundaryShapes cfg bodyResult
                      (InteractionLoopPreservation.Loop.bodyContext
                        ctx regular (LabelSupply.label supply 2) branchInput)
                      (LabelSupply.label supply 2) := by
                  simpa [branchInput] using
                    (LoopContract.body_shapes contract.shapes
                      hFacts.enclosingFallthrough hFacts.bodyRequire
                      hFacts.postShape)
                have hBodyBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 2)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyBoundary :=
                  hPostBoundary.push hBodyShapes hBodyBoundaryBefore
                apply
                  hBlockOwner (Nat.le_of_lt hFuel)
                    hBodyCompile hBodyBlocks hFacts.bodyCalls
                    hBodyWF hBodySafe hBodyCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                      hSupports regular (LabelSupply.label supply 2) branchInput)
                    (by
                      simpa [InteractionLoopPreservation.Loop.bodyContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ := hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [branchInput,
                    InteractionLoopPreservation.Loop.bodyStopPolicy,
                    InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg bodyResult
                        (InteractionLoopPreservation.Loop.bodyContext ctx regular
                          (LabelSupply.label supply 2) branchInput)
                        initResult.next (LabelSupply.label supply 1)
                        (LabelSupply.label supply 2) branchInput
                        bodySource tokens
                        (InteractionLoopPreservation.Loop.bodyStopPolicy
                          bodyResult postResult ctx regular
                          (LabelSupply.label supply 2)
                          (LabelSupply.label supply 0) branchInput
                          source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hBodyFits
                        regularAt := Or.inl hBodyBefore.regular
                        before := hBodyBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hBodyBoundary.congr_returns hReturns.symm
                        shapes := hBodyShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel bodyResult
                                (InteractionLoopPreservation.Loop.bodyContext
                                  ctx regular (LabelSupply.label supply 2)
                                  branchInput)
                                (LabelSupply.label supply 2)
                                source.returns tokens sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx (LabelSupply.label supply 0)
                                source.returns tokens policy) hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx (LabelSupply.label supply 0)
                                source.returns tokens policy) hMode
                          simpa [hReturns] using hRel })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel bodySource hFuel hBodyCompile hPostCompile
                  hBodyBlocks hFacts hBodyFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply <= initResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.initSupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ hFacts.initSupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                have hBodyBoundaryBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 0)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyShapes :
                    BoundaryShapes cfg bodyResult
                      (InteractionLoopPreservation.Loop.bodyContext
                        ctx regular (LabelSupply.label supply 2) branchInput)
                      (LabelSupply.label supply 2) := by
                  simpa [branchInput] using
                    (LoopContract.body_shapes contract.shapes
                      hFacts.enclosingFallthrough hFacts.bodyRequire
                      hFacts.postShape)
                have hBodyBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 2)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyBoundary :=
                  hPostBoundary.push hBodyShapes hBodyBoundaryBefore
                apply
                  hTruncationBlockOwner (Nat.le_of_lt hFuel)
                    hBodyCompile hBodyBlocks hFacts.bodyCalls
                    hBodyWF hBodySafe hBodyCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                      hSupports regular (LabelSupply.label supply 2) branchInput)
                    (by
                      simpa [InteractionLoopPreservation.Loop.bodyContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ := hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [branchInput,
                    InteractionLoopPreservation.Loop.bodyStopPolicy,
                    InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg bodyResult
                        (InteractionLoopPreservation.Loop.bodyContext ctx regular
                          (LabelSupply.label supply 2) branchInput)
                        initResult.next (LabelSupply.label supply 1)
                        (LabelSupply.label supply 2) branchInput
                        bodySource tokens
                        (InteractionLoopPreservation.Loop.bodyStopPolicy
                          bodyResult postResult ctx regular
                          (LabelSupply.label supply 2)
                          (LabelSupply.label supply 0) branchInput
                          source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hBodyFits
                        regularAt := Or.inl hBodyBefore.regular
                        before := hBodyBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hBodyBoundary.congr_returns hReturns.symm
                        shapes := hBodyShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel bodyResult
                                (InteractionLoopPreservation.Loop.bodyContext
                                  ctx regular (LabelSupply.label supply 2)
                                  branchInput)
                                (LabelSupply.label supply 2)
                                source.returns tokens sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx (LabelSupply.label supply 0)
                                source.returns tokens policy) hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx (LabelSupply.label supply 0)
                                source.returns tokens policy) hMode
                          simpa [hReturns] using hRel })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel postSource hFuel hPostCompile hPostBlocks
                  hFacts hPostFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply <= bodyResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.bodySupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ hFacts.bodySupply
                have hPostBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ hFacts.bodySupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                apply
                  hBlockOwner (Nat.le_of_lt hFuel)
                    hPostCompile hPostBlocks hFacts.postCalls
                    hPostWF hPostSafe hPostCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ := hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [branchInput,
                    InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg postResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        bodyResult.next (LabelSupply.label supply 2)
                        (LabelSupply.label supply 0) branchInput postSource tokens
                        (InteractionLoopPreservation.Loop.postStopPolicy
                          postResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hPostFits
                        regularAt := Or.inl hPostBefore.regular
                        before := hPostBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hPostBoundary.congr_returns hReturns.symm
                        shapes := hPostShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel postResult
                                (InteractionLoopPreservation.Loop.outerContext ctx)
                                (LabelSupply.label supply 0)
                                source.returns tokens sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              policy hMode
                          simpa [hReturns] using hRel })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel postSource hFuel hPostCompile hPostBlocks
                  hFacts hPostFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply <= bodyResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.bodySupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ hFacts.bodySupply
                have hPostBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ hFacts.bodySupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                apply
                  hTruncationBlockOwner (Nat.le_of_lt hFuel)
                    hPostCompile hPostBlocks hFacts.postCalls
                    hPostWF hPostSafe hPostCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ := hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [branchInput,
                    InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg postResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        bodyResult.next (LabelSupply.label supply 2)
                        (LabelSupply.label supply 0) branchInput postSource tokens
                        (InteractionLoopPreservation.Loop.postStopPolicy
                          postResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hPostFits
                        regularAt := Or.inl hPostBefore.regular
                        before := hPostBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hPostBoundary.congr_returns hReturns.symm
                        shapes := hPostShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel postResult
                                (InteractionLoopPreservation.Loop.outerContext ctx)
                                (LabelSupply.label supply 0)
                                source.returns tokens sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              policy hMode
                          simpa [hReturns] using hRel })

theorem call_truncation_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {name : Structured.Name}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.call name) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs (.call name))
    (hProcs : ctx.procs = program.procs)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (hBlockOwner :
      InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (hTruncationBlockOwner :
      InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.call name) source)
      (InteractionStaticCost.stmtBudget
        program (sourceFuel + 1) (.call name))
      policy := by
  cases hCalls with
  | call hContains =>
      obtain ⟨proc, hLookup⟩ :=
        Structured.ProcList.exists_lookup?_of_contains hContains
      have hProcWF :=
        Structured.Program.procWF_of_lookup? hProgramWF hLookup
      have hProcFrameSafe :=
        Structured.Program.procFrameSafe_of_lookup?
          hProgramFrameSafe hLookup
      have hProcCalls :=
        Structured.Program.procCallsResolved_of_lookup?
          hProgramWF hLookup
      have hBodyBudget :=
        InteractionStaticCost.blockBudget_le_procBodyBudget_of_lookup
          (program := program) (fuel := sourceFuel) hLookup
      have hBounded :=
        Call.call_succ
          (bodyBudget :=
            InteractionStaticCost.procBodyBudget program sourceFuel)
          generated hLookup hProcs hCompile hBlocks hResultCalls
          contract.fits hProcWF
          (by
            intro args callerStack targetState hSplit hStateRel
            have hExtension :=
              CallContract.extension
                (source := source) (tokens := tokens)
                (args := args) (callerStack := callerStack)
                (retc := proc.retc) (supply := supply)
            exact
              contract.boundary.ownership.eq_false_of_stateRel_extension
                (TypedCfgPreservation.LabelShape.procEntry generated hLookup)
                (TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc)
                hExtension hStateRel
                (TypedCfgPreservation.SourceFrameFits.procEntry_of_splitArgs
                  hSplit))
          (by
            intro fragment args callerStack targetState hSplit hStateRel
            have hExtension :=
              CallContract.extension
                (source := source) (tokens := tokens)
                (args := args) (callerStack := callerStack)
                (retc := proc.retc) (supply := supply)
            have hFragmentShape :
                TypedCfgPreservation.LabelShape
                  cfg fragment.entry fragment.input :=
              TypedCfgPreservation.LabelShape.of_compileBlock?
                fragment.compile
                (by
                  apply
                    TypedCfgPreservation.BlocksInProgram.of_subset_of_wellTyped
                      generated.wellTyped
                  intro block hMem
                  rw [generated.cfgEq]
                  have hProcMem := fragment.blocks block hMem
                  simp [hProcMem, List.append_assoc])
            exact
              contract.boundary.ownership.eq_false_of_stateRel_extension
                hFragmentShape fragment.input_returnTokenDepth
                hExtension hStateRel
                (fragment.input_sourceFrameFits_of_splitArgs hSplit))
          (by
            intro fragment hFragmentBlocks hFragmentCalls
              args callerStack hSplit
            let callSource : RunState :=
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc)
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body
                    (InteractionCallPreservation.Call.procContext program proc)
                    fragment.supply fragment.entry fragment.input
                    (ProcLabel.exit proc.name) = some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?,
                InteractionCallPreservation.Call.procContext] using
                fragment.compile
            have hExtension :
                TypedCfgPreservation.ActivationExtension
                  source.returns tokens callSource.returns
                  (Structured.Stmt.callToken supply :: tokens) := by
              simpa [callSource] using
                (CallContract.extension
                  (source := source) (tokens := tokens)
                  (args := args) (callerStack := callerStack)
                  (retc := proc.retc) (supply := supply))
            have hShapes := CallContract.shapes generated hLookup fragment
            have hOwned :=
              hBlockOwner (Nat.le_refl sourceFuel)
                hFragmentCompile hFragmentBlocks hFragmentCalls
                hProcWF.2.2 hProcFrameSafe hProcCalls
                (CallContract.supports program proc) rfl
                (by
                  intro _hCanLeave
                  exact
                    ⟨{ callerStack := callerStack, retc := proc.retc },
                      source.returns, by simp [callSource]⟩)
                (show
                  FragmentContract cfg fragment.result
                    (InteractionCallPreservation.Call.procContext program proc)
                    fragment.supply fragment.entry (ProcLabel.exit proc.name)
                    fragment.input callSource
                    (Structured.Stmt.callToken supply :: tokens)
                    (InteractionCallPreservation.Call.bodyStopPolicy
                      fragment.result program proc callSource.returns
                      (Structured.Stmt.callToken supply :: tokens) policy) from
                  { fits := fragment.input_sourceFrameFits_of_splitArgs hSplit
                    regularAt := Or.inl (by trivial)
                    before := CallContract.before
                    activation :=
                      TypedCfgPreservation.ActivationInput.active
                        ⟨proc.argc, fragment.input_returnTokenDepth⟩
                    boundary :=
                      contract.boundary.push_child hExtension hShapes
                        CallContract.before
                    shapes := hShapes
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      exact
                        InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                          policy hRel
                    nonregular :=
                      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                        policy })
            exact
              InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.mono_budget
                hOwned hBodyBudget)
          (by
            intro fragment hFragmentBlocks hFragmentCalls
              args callerStack hSplit
            let callSource : RunState :=
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc)
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body
                    (InteractionCallPreservation.Call.procContext program proc)
                    fragment.supply fragment.entry fragment.input
                    (ProcLabel.exit proc.name) = some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?,
                InteractionCallPreservation.Call.procContext] using
                fragment.compile
            have hExtension :
                TypedCfgPreservation.ActivationExtension
                  source.returns tokens callSource.returns
                  (Structured.Stmt.callToken supply :: tokens) := by
              simpa [callSource] using
                (CallContract.extension
                  (source := source) (tokens := tokens)
                  (args := args) (callerStack := callerStack)
                  (retc := proc.retc) (supply := supply))
            have hShapes := CallContract.shapes generated hLookup fragment
            have hOwned :=
              hTruncationBlockOwner (Nat.le_refl sourceFuel)
                hFragmentCompile hFragmentBlocks hFragmentCalls
                hProcWF.2.2 hProcFrameSafe hProcCalls
                (CallContract.supports program proc) rfl
                (by
                  intro _hCanLeave
                  exact
                    ⟨{ callerStack := callerStack, retc := proc.retc },
                      source.returns, by simp [callSource]⟩)
                (show
                  FragmentContract cfg fragment.result
                    (InteractionCallPreservation.Call.procContext program proc)
                    fragment.supply fragment.entry (ProcLabel.exit proc.name)
                    fragment.input callSource
                    (Structured.Stmt.callToken supply :: tokens)
                    (InteractionCallPreservation.Call.bodyStopPolicy
                      fragment.result program proc callSource.returns
                      (Structured.Stmt.callToken supply :: tokens) policy) from
                  { fits := fragment.input_sourceFrameFits_of_splitArgs hSplit
                    regularAt := Or.inl (by trivial)
                    before := CallContract.before
                    activation :=
                      TypedCfgPreservation.ActivationInput.active
                        ⟨proc.argc, fragment.input_returnTokenDepth⟩
                    boundary :=
                      contract.boundary.push_child hExtension hShapes
                        CallContract.before
                    shapes := hShapes
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      exact
                        InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                          policy hRel
                    nonregular :=
                      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                        policy })
            exact
              InteractionControlPreservation.OpenOutcome.BoundedTruncationExecPreservesUnder.mono_budget
                hOwned hBodyBudget)
      simpa [InteractionStaticCost.stmtBudget_call_succ,
        Nat.add_comm] using hBounded

theorem bounded_succ
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          stmt ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave stmt)
    (hFrameSafe : stmt.FrameSafe)
    (hCalls : Structured.ProcList.StmtCallsResolved program.procs stmt)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true -> exists frame rest, source.returns = frame :: rest)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (hBlockOwner :
      InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt
        sourceFuel program entryShapes cfg generated)
    (hTruncationBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedTruncationExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) stmt source)
      (InteractionStaticCost.stmtBudget program (sourceFuel + 1) stmt)
      policy := by
  cases stmt with
  | code code =>
      simpa [InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] using
        (zero (program := program) (stmt := .code code)
          (result := result) (cfg := cfg) (entry := entry)
          (regular := regular) (ctx := ctx) (source := source)
          (tokens := tokens) (policy := policy))
  | if_ cond body =>
      exact
        if_truncation_bounded hCompile hBlocks hResultCalls hWF hFrameSafe
          hCalls hSupports hProcs hSourceReturns hTruncationBlockOwner contract
  | switch scrutinee cases defaultBody =>
      exact
        switch_truncation_bounded hCompile hBlocks hResultCalls hWF
          hFrameSafe hCalls hSupports hProcs hSourceReturns
          hTruncationBlockOwner contract
  | for_ init cond post body =>
      exact
        for_truncation_bounded hCompile hBlocks hResultCalls hWF hFrameSafe
          hCalls hSupports hProcs hSourceReturns hBlockOwner
          hTruncationBlockOwner contract
  | brk =>
      simpa [InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] using
        (zero (program := program) (stmt := .brk)
          (result := result) (cfg := cfg) (entry := entry)
          (regular := regular) (ctx := ctx) (source := source)
          (tokens := tokens) (policy := policy))
  | cont =>
      simpa [InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] using
        (zero (program := program) (stmt := .cont)
          (result := result) (cfg := cfg) (entry := entry)
          (regular := regular) (ctx := ctx) (source := source)
          (tokens := tokens) (policy := policy))
  | leave =>
      simpa [InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] using
        (zero (program := program) (stmt := .leave)
          (result := result) (cfg := cfg) (entry := entry)
          (regular := regular) (ctx := ctx) (source := source)
          (tokens := tokens) (policy := policy))
  | call name =>
      exact
        call_truncation_bounded hCompile hBlocks hResultCalls hCalls hProcs
          hProgramWF hProgramFrameSafe hBlockOwner hTruncationBlockOwner
          contract
  | terminal kind =>
      simpa [InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] using
        (zero (program := program) (stmt := .terminal kind)
          (result := result) (cfg := cfg) (entry := entry)
          (regular := regular) (ctx := ctx) (source := source)
          (tokens := tokens) (policy := policy))

end Stmt

theorem block_owner
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) :
    InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt sourceFuel program entryShapes cfg generated := by
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      unfold InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt
      intro blockSourceFuel compilerFuel block ctx supply entry regular input
        result source tokens policy canBreak canContinue canLeave
        hSourceFuel hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
        hSupports hProcs hSourceReturns contract
      cases blockSourceFuel with
      | zero =>
          exact Block.zero
      | succ innerFuel =>
          have hInnerLt : innerFuel < sourceFuel := by omega
          have hInnerOwner :
              InteractionTruncationOwnerPreservation.OpenOutcome.BlockOwnerAt innerFuel program entryShapes cfg generated :=
            ih innerFuel hInnerLt
          have hInnerDoneOwner :
              InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt
                innerFuel program entryShapes cfg generated :=
            InteractionBoundedOwnerPreservation.OpenOutcome.block_owner
              generated hProgramWF hProgramFrameSafe innerFuel
          cases compilerFuel with
          | zero =>
              simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
          | succ listFuel =>
              unfold TypedCfgCompiler.compileBlockFuel? at hCompile
              cases listFuel with
              | zero =>
                  simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
              | succ compilerFuel =>
                  cases block with
                  | mk stmts =>
                      cases stmts with
                      | nil =>
                          simpa only [
                            InteractionStaticCost.blockBudget_nil_succ] using
                            Block.nil_succ
                              (sourceProgram := program)
                              (sourceFuel := innerFuel) hCompile
                      | cons stmt rest =>
                          cases compilerFuel with
                          | zero =>
                              simp [
                                TypedCfgCompiler.compileStmtListFuel?,
                                TypedCfgCompiler.compileStmtFuel?] at hCompile
                          | succ stmtCompilerFuel =>
                              cases hWF with
                              | cons hStmtWF hRestWF =>
                                  cases hFrameSafe with
                                  | cons hStmtSafe hRestSafe =>
                                      cases hCalls with
                                      | mk hStmtListCalls =>
                                          cases hStmtListCalls with
                                          | cons hStmtCalls hRestCalls =>
                                              rw [
                                                InteractionStaticCost.blockBudget_cons_succ]
                                              apply
                                                Block.cons_succ
                                                  hCompile hBlocks hResultCalls
                                              · intro headResult tailResult
                                                  tailInput middleSource
                                                  targetMiddle hHeadCompile
                                                  hFallthrough hTailCompile
                                                  hTailBlocks hRel
                                                have hTailShape :
                                                    TypedCfgPreservation.LabelShape
                                                      cfg
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      tailInput :=
                                                  TypedCfgPreservation.LabelShape.of_compileStmtListFuel?
                                                    hTailCompile hTailBlocks
                                                obtain ⟨targetState, hTarget,
                                                    hStateRel⟩ :=
                                                  TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                                                    hRel.1
                                                have hTargetEq :
                                                    targetState = targetMiddle := by
                                                  cases hTarget
                                                  rfl
                                                subst targetState
                                                rcases hRel.2.1 with
                                                  ⟨shape, hShape, hFits⟩
                                                have hReturns :
                                                    middleSource.returns =
                                                      source.returns := by
                                                  simpa [
                                                    InteractionControlPreservation.OpenOutcome.ActivationRestored]
                                                    using hRel.2.2
                                                have hShapeEq : shape = tailInput :=
                                                  Option.some.inj
                                                    (hShape.symm.trans hFallthrough)
                                                subst shape
                                                exact
                                                  (contract.boundary.congr_returns
                                                    hReturns.symm).eq_false_of_stateRel
                                                    (source := middleSource)
                                                    (scope := supply) (tag := 100)
                                                    (Nat.le_refl supply)
                                                    (contract.before.regular.generated_ne
                                                      (Nat.le_refl supply))
                                                    hTailShape
                                                    (contract.activation.stmtFallthrough
                                                      hHeadCompile hFallthrough)
                                                    hStateRel hFits
                                              · intro headResult hHeadCompile
                                                  hHeadBlocks hHeadCalls hFallthrough
                                                have hHeadContract :
                                                    StmtContract cfg headResult
                                                      ctx supply entry
                                                      (TypedCfgCompiler.restLabel supply)
                                                      input source tokens policy :=
                                                  { fits := contract.fits
                                                    regularAt := Or.inr rfl
                                                    before := contract.before.nonregular
                                                    activation := contract.activation
                                                    boundary :=
                                                      contract.boundary.rebase_regular
                                                        contract.before.regular
                                                    shapes :=
                                                      contract.shapes.of_fallthrough_none
                                                        hFallthrough
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      exact contract.nonregular
                                                        (hRel.mode_ne_regular_of_fallthrough_none
                                                          hFallthrough) hRel
                                                    nonregular := contract.nonregular }
                                                cases innerFuel with
                                                | zero =>
                                                    exact
                                                      ⟨InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.bounded_zero
                                                          hHeadCompile hHeadBlocks
                                                          hStmtWF hSupports
                                                          hSourceReturns hHeadContract,
                                                        Stmt.zero⟩
                                                | succ recursiveFuel =>
                                                    exact
                                                      ⟨InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.bounded_succ
                                                          hHeadCompile hHeadBlocks
                                                          hHeadCalls hStmtWF hStmtSafe
                                                          hStmtCalls hSupports hProcs
                                                          hSourceReturns hProgramWF
                                                          hProgramFrameSafe
                                                          (InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt.mono
                                                            hInnerDoneOwner
                                                            (Nat.le_succ recursiveFuel))
                                                          hHeadContract,
                                                        Stmt.bounded_succ
                                                          hHeadCompile hHeadBlocks
                                                          hHeadCalls hStmtWF hStmtSafe
                                                          hStmtCalls hSupports hProcs
                                                          hSourceReturns hProgramWF
                                                          hProgramFrameSafe
                                                          (InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt.mono
                                                            hInnerDoneOwner
                                                            (Nat.le_succ recursiveFuel))
                                                          (hInnerOwner.mono
                                                            (Nat.le_succ recursiveFuel))
                                                          hHeadContract⟩
                                              · intro headResult tailResult
                                                  tailInput hHeadCompile hHeadBlocks
                                                  hHeadCalls hFallthrough
                                                  hTailCompile hTailBlocks hWhole
                                                have wholeContract :
                                                    FragmentContract cfg
                                                      (headResult.append tailResult)
                                                      ctx supply entry regular input
                                                      source tokens policy := by
                                                  simpa [hWhole] using contract
                                                have hTailShape :
                                                    TypedCfgPreservation.LabelShape cfg
                                                      (TypedCfgCompiler.restLabel supply)
                                                      tailInput :=
                                                  TypedCfgPreservation.LabelShape.of_compileStmtListFuel?
                                                    hTailCompile hTailBlocks
                                                have hHeadShapes :
                                                    BoundaryShapes cfg headResult ctx
                                                      (TypedCfgCompiler.restLabel supply) :=
                                                  wholeContract.shapes.with_regular
                                                    (by
                                                      intro shape hShape
                                                      have hShapeEq : shape = tailInput :=
                                                        Option.some.inj
                                                          (hShape.symm.trans hFallthrough)
                                                      subst shape
                                                      exact hTailShape)
                                                have hHeadContract :
                                                    StmtContract cfg headResult ctx
                                                      supply entry
                                                      (TypedCfgCompiler.restLabel supply)
                                                      input source tokens
                                                      (InteractionControlPreservation.OpenOutcome.pushStopJump
                                                        headResult ctx
                                                        (TypedCfgCompiler.restLabel supply)
                                                        source.returns tokens policy) :=
                                                  { fits := contract.fits
                                                    regularAt := Or.inr rfl
                                                    before := contract.before.nonregular
                                                    activation := wholeContract.activation
                                                    boundary :=
                                                      wholeContract.boundary.push_current
                                                        wholeContract.regularAt
                                                        wholeContract.before.nonregular
                                                        rfl hHeadShapes
                                                    shapes := hHeadShapes
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      exact
                                                        InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                                                          policy hRel
                                                    nonregular :=
                                                      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                                                        policy }
                                                cases innerFuel with
                                                | zero =>
                                                    exact
                                                      ⟨InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.bounded_zero
                                                          hHeadCompile hHeadBlocks
                                                          hStmtWF hSupports
                                                          hSourceReturns hHeadContract,
                                                        Stmt.zero⟩
                                                | succ recursiveFuel =>
                                                    exact
                                                      ⟨InteractionBoundedOwnerPreservation.OpenOutcome.Stmt.bounded_succ
                                                          hHeadCompile hHeadBlocks
                                                          hHeadCalls hStmtWF hStmtSafe
                                                          hStmtCalls hSupports hProcs
                                                          hSourceReturns hProgramWF
                                                          hProgramFrameSafe
                                                          (InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt.mono
                                                            hInnerDoneOwner
                                                            (Nat.le_succ recursiveFuel))
                                                          hHeadContract,
                                                        Stmt.bounded_succ
                                                          hHeadCompile hHeadBlocks
                                                          hHeadCalls hStmtWF hStmtSafe
                                                          hStmtCalls hSupports hProcs
                                                          hSourceReturns hProgramWF
                                                          hProgramFrameSafe
                                                          (InteractionBoundedOwnerPreservation.OpenOutcome.BlockOwnerAt.mono
                                                            hInnerDoneOwner
                                                            (Nat.le_succ recursiveFuel))
                                                          (hInnerOwner.mono
                                                            (Nat.le_succ recursiveFuel))
                                                          hHeadContract⟩
                                              · intro headResult tailResult
                                                  tailInput middleSource
                                                  hHeadCompile hFallthrough
                                                  hTailCompile hTailBlocks
                                                  hTailCalls hReturns hFrameFits hWhole
                                                have wholeContract :
                                                    FragmentContract cfg
                                                      (headResult.append tailResult)
                                                      ctx supply entry regular input
                                                      source tokens policy := by
                                                  simpa [hWhole] using contract
                                                have hHeadNext :
                                                    supply + 1 <= headResult.next :=
                                                  TypedCfgCompilerFacts.Supply.stmt_next_ge_succ
                                                    hHeadCompile
                                                have hTailFits :
                                                    TypedCfgCompiler.Shape.SourceFrameFits
                                                      tailInput
                                                      middleSource.evm.stack.length := by
                                                  rcases hFrameFits with
                                                    ⟨shape, hShape, hFits⟩
                                                  have hShapeEq : shape = tailInput :=
                                                    Option.some.inj
                                                      (hShape.symm.trans hFallthrough)
                                                  subst shape
                                                  exact hFits
                                                have hTailShapes :
                                                    BoundaryShapes cfg tailResult
                                                      ctx regular :=
                                                  wholeContract.shapes.with_regular
                                                    (by
                                                      intro shape hShape
                                                      apply wholeContract.shapes.regular
                                                      simp [
                                                        TypedCfgCompiler.Result.append,
                                                        hShape])
                                                have hTailContract :
                                                    FragmentContract cfg tailResult
                                                      ctx headResult.next
                                                      (TypedCfgCompiler.restLabel supply)
                                                      regular tailInput middleSource
                                                      tokens policy :=
                                                  { fits := hTailFits
                                                    regularAt :=
                                                      Or.inl
                                                        (contract.before.regular.mono
                                                          (Nat.le_trans
                                                            (Nat.le_succ supply)
                                                            hHeadNext))
                                                    before :=
                                                      contract.before.mono
                                                        (Nat.le_trans
                                                          (Nat.le_succ supply)
                                                          hHeadNext)
                                                    activation :=
                                                      contract.activation.stmtFallthrough
                                                        hHeadCompile hFallthrough
                                                    boundary :=
                                                      (contract.boundary.mono
                                                        (Nat.le_trans
                                                          (Nat.le_succ supply)
                                                          hHeadNext)).congr_returns
                                                        hReturns.symm
                                                    shapes := hTailShapes
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      apply wholeContract.stops
                                                      have hRel' :
                                                          Rel tailResult ctx regular
                                                            source.returns tokens
                                                            sourceOutcome targetOutcome := by
                                                        simpa [hReturns] using hRel
                                                      exact
                                                        InteractionControlPreservation.OpenOutcome.Rel.append_right
                                                          hRel'
                                                    nonregular := by
                                                      intro childResult childRegular
                                                        sourceOutcome targetOutcome
                                                        hMode hRel
                                                      apply contract.nonregular hMode
                                                      simpa [hReturns] using hRel }
                                                have hTailBlockCompile :
                                                    TypedCfgCompiler.compileBlockFuel?
                                                        (Nat.succ
                                                          (stmtCompilerFuel + 1))
                                                        { stmts := rest } ctx
                                                        headResult.next
                                                        (TypedCfgCompiler.restLabel supply)
                                                        tailInput regular =
                                                      some tailResult := by
                                                  unfold
                                                    TypedCfgCompiler.compileBlockFuel?
                                                  exact hTailCompile
                                                apply
                                                  hInnerOwner
                                                    (blockSourceFuel := innerFuel)
                                                    (compilerFuel :=
                                                      Nat.succ
                                                        (stmtCompilerFuel + 1))
                                                    (block := { stmts := rest })
                                                    (ctx := ctx)
                                                    (supply := headResult.next)
                                                    (entry :=
                                                      TypedCfgCompiler.restLabel supply)
                                                    (regular := regular)
                                                    (input := tailInput)
                                                    (result := tailResult)
                                                    (source := middleSource)
                                                    (tokens := tokens)
                                                    (policy := policy)
                                                    (canBreak := canBreak)
                                                    (canContinue := canContinue)
                                                    (canLeave := canLeave)
                                                    (Nat.le_refl innerFuel)
                                                    hTailBlockCompile hTailBlocks
                                                    hTailCalls hRestWF hRestSafe
                                                    (.mk hRestCalls)
                                                    hSupports hProcs
                                                · intro hCanLeave
                                                  obtain ⟨frame, remaining,
                                                      hSourceEq⟩ :=
                                                    hSourceReturns hCanLeave
                                                  exact
                                                    ⟨frame, remaining,
                                                      hReturns.trans hSourceEq⟩
                                                · exact hTailContract

namespace GeneratedProgram

def topPolicy
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (source : RunState) : StopPolicy :=
  InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.topPolicy
    generated source

/-- Structural exhaustion of the generated main block preserves the exact
ordered interaction prefix at the compiler-owned target budget. -/
theorem main_truncation_bounded
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    BoundedTruncationExecPreservesUnder generated.main cfg
      TypedCfgCompiler.entryLabel { procs := program.procs }
      ProcLabel.programEnd source []
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)
      (InteractionStaticCost.blockBudget
        program sourceFuel program.body)
      (topPolicy generated source) := by
  have hMainCompile :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel program.body + 1)
          program.body { procs := program.procs }
          0 TypedCfgCompiler.entryLabel TypedCfg.Shape.caller
          ProcLabel.programEnd = some generated.main := by
    simpa [TypedCfgCompiler.compileBlock?] using generated.mainCompile
  have hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        { procs := program.procs } false false false :=
    { breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by simp }
  have hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        { procs := program.procs } ProcLabel.programEnd 0 :=
    { regular := by trivial
      breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by simp }
  have hShapes :=
    InteractionOwnerPreservation.OpenOutcome.GeneratedProgram.main_shapes
      generated
  have hBaseBoundary :
      RecursiveBoundary cfg source.returns []
        (fun _ _ => false) 0 ProcLabel.programEnd :=
    { ownership :=
        InteractionBoundaryPreservation.OpenOutcome.StopPolicy.ActivationProtected.empty
          cfg source.returns []
      fresh :=
        InteractionBoundaryPreservation.OpenOutcome.StopPolicy.ActivationFreshExcept.of_static
          (by
            intro scope tag target hScope hNe
            rfl) }
  have hBoundary :
      RecursiveBoundary cfg source.returns []
        (topPolicy generated source) 0 ProcLabel.programEnd := by
    simpa [topPolicy,
      InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.topPolicy,
      InteractionOwnerPreservation.OpenOutcome.GeneratedProgram.topPolicy] using
      hBaseBoundary.push hShapes hBefore
  have hOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated :=
    block_owner generated hProgramWF hProgramFrameSafe sourceFuel
  apply
    hOwner
      (blockSourceFuel := sourceFuel)
      (compilerFuel := TypedCfgCompiler.blockFuel program.body + 1)
      (block := program.body)
      (ctx := { procs := program.procs })
      (supply := 0)
      (entry := TypedCfgCompiler.entryLabel)
      (regular := ProcLabel.programEnd)
      (input := TypedCfg.Shape.caller)
      (result := generated.main)
      (source := source)
      (tokens := [])
      (policy := topPolicy generated source)
      (canBreak := false)
      (canContinue := false)
      (canLeave := false)
      (Nat.le_refl sourceFuel)
      hMainCompile generated.mainBlocks generated.mainCalls
      hProgramWF.2.2.2.2 hProgramFrameSafe.2 hProgramWF.2.2.2.1
      hSupports rfl
  · intro hFalse
    cases hFalse
  · exact
      { fits := by
          simp [
            TypedCfgCompiler.Shape.SourceFrameFits,
            TypedCfgCompiler.Shape.sourceLength,
            TypedCfgCompiler.Shape.sourceView,
            TypedCfg.Shape.caller,
            TypedCfg.Shape.length,
            TypedCfg.Shape.returnTokenDepth?,
            TypedCfg.Shape.returnTokenDepthList?]
        regularAt := Or.inl (by trivial)
        before := hBefore
        activation := TypedCfgPreservation.ActivationInput.top _
        boundary := hBoundary
        shapes := hShapes
        stops := by
          intro sourceOutcome targetOutcome hRel
          exact
            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
              (fun _ _ => false) hRel
        nonregular :=
          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
            (fun _ _ => false) }

/-- The complete unconditional Structured-to-TypedCfg theorem. Successful
leaves and runtime errors are related exactly; source structural exhaustion
releases only the target suffix after the same ordered interaction prefix. -/
theorem main_forward
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    InteractionControlPreservation.OpenOutcome.ForwardPreservesUnder
      generated.main cfg TypedCfgCompiler.entryLabel
      { procs := program.procs } ProcLabel.programEnd .stop source []
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)
      (InteractionStaticCost.blockBudget
        program sourceFuel program.body)
      (topPolicy generated source) := by
  have hSuccess :=
    InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.main_uniform
      generated hProgramWF hProgramFrameSafe sourceFuel source
  have hRuntime :=
    InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.main_runtime_error_uniform
      generated hProgramWF hProgramFrameSafe sourceFuel source
  have hTruncation :=
    main_truncation_bounded generated hProgramWF hProgramFrameSafe
      sourceFuel source
  exact
    InteractionControlPreservation.OpenOutcome.UniformExecPreservesUnder.with_runtime_errors_and_truncation
      (regularExit := .stop) hSuccess hRuntime hTruncation

/-- Whole-program relation after discharging the generated regular continuation
through its concrete `STOP` block. -/
def PrefixOutcomeRel
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg) :
    Structured.Outcome → TypedCfg.Outcome → Prop
  | ⟨source, .regular⟩, .halt .stop target =>
      TypedCfgPreservation.StateRel source [] target ∧
        InteractionControlPreservation.OpenOutcome.FrameFits
          generated.main { procs := program.procs } ⟨source, .regular⟩ ∧
        InteractionControlPreservation.OpenOutcome.ActivationRestored
          [] ⟨source, .regular⟩
  | source@⟨_, .halt _⟩, target@(.halt _ _) =>
      InteractionControlPreservation.OpenOutcome.Rel
        generated.main { procs := program.procs } ProcLabel.programEnd
        [] [] source target
  | _, _ => False

abbrev PrefixDoneRel
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg) :=
  Simulation.Interaction.ExceptRel
    Assembly.InteractionFuelSafety.StructuralErrorRel
    (PrefixOutcomeRel generated)

/-- Every completed generated whole-program prefix carries exactly the terminal
safety needed by the adjacent Assembly lowering. -/
theorem PrefixDoneRel.targetSafe
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg}
    {sourceDone : Except EVMException Structured.Outcome}
    {targetDone : Except EVMException TypedCfg.Outcome}
    (hRel : PrefixDoneRel generated sourceDone targetDone) :
    TypedCfg.InteractionSemantics.Program.PrefixAssemblySafe targetDone := by
  cases hRel with
  | error hError => trivial
  | @ok sourceOutcome targetOutcome hOutcome =>
      rcases sourceOutcome with ⟨source, mode⟩
      cases mode with
      | regular =>
          cases targetOutcome with
          | halt kind target =>
              cases kind with
              | stop =>
                  change Assembly.InteractionSemantics.Terminal.SafeAt
                    .stop target
                  unfold Assembly.InteractionSemantics.Terminal.SafeAt
                  change ∃ final, Assembly.PrimOp.stop.step target = .ok final
                  refine ⟨
                    { target with
                      toMachineState :=
                        (target.toMachineState.setReturnData ByteArray.empty).setHReturn
                          ByteArray.empty }, ?_⟩
                  rfl
              | «return» | revert | selfdestruct => cases hOutcome
          | jump label target
          | fallthrough target
          | returnDispatch target
          | invalid target => cases hOutcome
      | halt kind =>
          cases targetOutcome with
          | halt targetKind target =>
              obtain ⟨hTerminal, _hFits, _hRestored⟩ := hOutcome
              obtain ⟨targetState, targetFinal, hTarget, hStep, _hState⟩ :=
                TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim hTerminal
              cases hTarget
              exact ⟨targetFinal, hStep⟩
          | jump label target
          | fallthrough target
          | returnDispatch target
          | invalid target => cases hOutcome
      | brk | cont | leave => cases hOutcome

private theorem programEnd_prefix
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg)
    (remaining : Nat) (state : EVMState) :
    Simulation.Interaction.bind
        (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
          (fun _ _ => false) cfg 1
          (.stopped remaining (.jump ProcLabel.programEnd state)))
        TypedCfg.InteractionSemantics.Program.finishRunResultPrefix =
      Simulation.Interaction.pure (.halt .stop state) := by
  have hStep :
      TypedCfg.InteractionSemantics.Program.openStep
          cfg ProcLabel.programEnd state =
        Simulation.Interaction.pure (.halt .stop state) := by
    unfold TypedCfg.InteractionSemantics.Program.openStep
      TypedCfg.Control.Program.step
    rw [generated.programEndBlock]
    change
      Simulation.Interaction.bind
          (.done (.ok
            (state, generated.main.fallthrough?.getD TypedCfg.Shape.caller)))
          (fun result =>
            if result.2 =
                generated.main.fallthrough?.getD TypedCfg.Shape.caller then
              .done (.ok
                (TypedCfg.Outcome.halt Assembly.HaltKind.stop result.1))
            else Simulation.Interaction.error
              (Error := EVMException)
              EvmYul.EVM.ExecutionException.InvalidInstruction) =
        .done (.ok
          (TypedCfg.Outcome.halt Assembly.HaltKind.stop state))
    rw [Simulation.Interaction.bind_done_ok]
    rw [if_pos rfl]
  unfold
    TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind,
    hStep]
  rfl

private def completePrefixRun (cfg : TypedCfg.Program)
    (result : TypedCfg.Control.Program.RunResult) :
    TypedCfg.InteractionSemantics.OpenOutcome :=
  Simulation.Interaction.bind
    (TypedCfg.InteractionSemantics.Program.continueOpenRunNResultWithRefinedStop
      (fun _ _ => false) cfg 1 result)
    TypedCfg.InteractionSemantics.Program.finishRunResultPrefix

private def completePrefixDone (cfg : TypedCfg.Program) :
    Except EVMException TypedCfg.Control.Program.RunResult →
      TypedCfg.InteractionSemantics.OpenOutcome
  | .error error => .done (.error error)
  | .ok result => completePrefixRun cfg result

/-- A related generated boundary result is completed to the canonical TypedCfg
whole-program prefix outcome without exposing a generated certificate. -/
private theorem complete_prefix
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg)
    {sourceDone : Except EVMException Structured.Outcome}
    {targetDone : Except EVMException TypedCfg.Control.Program.RunResult}
    (hDone :
      InteractionControlPreservation.OpenOutcome.SegmentDoneRel
        generated.main { procs := program.procs }
        ProcLabel.programEnd [] [] .stop sourceDone targetDone)
    (hTargetSafe : Assembly.InteractionFuelSafety.NotOutOfFuel targetDone) :
    Simulation.Interaction.ForwardRel
      InteractionControlPreservation.OpenOutcome.Truncated
      (PrefixDoneRel generated)
      (.done sourceDone)
      (completePrefixDone cfg targetDone) := by
  cases hDone with
  | error hError =>
      exact .done (Simulation.Interaction.ExceptRel.error
        (Assembly.InteractionFuelSafety.StructuralErrorRel.of_target_not
          hTargetSafe))
  | @ok sourceOutcome targetResult hSegment =>
      cases targetResult with
      | exhausted label state =>
          exact False.elim hSegment
      | stopped remaining targetOutcome =>
          change
            InteractionControlPreservation.OpenOutcome.Rel
              generated.main { procs := program.procs }
              ProcLabel.programEnd [] [] sourceOutcome targetOutcome
            at hSegment
          obtain ⟨hOutcome, hFits, hRestored⟩ := hSegment
          rcases sourceOutcome with ⟨source, mode⟩
          cases mode with
          | regular =>
              obtain ⟨target, rfl, hState⟩ :=
                TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                  hOutcome
              have hComplete := programEnd_prefix generated remaining target
              change
                Simulation.Interaction.ForwardRel
                  InteractionControlPreservation.OpenOutcome.Truncated
                  (PrefixDoneRel generated)
                  (.done (.ok ⟨source, .regular⟩))
                  (completePrefixRun cfg
                    (.stopped remaining
                      (.jump
                        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                          { procs := program.procs } ProcLabel.programEnd).regular
                        target)))
              rw [show completePrefixRun cfg
                    (.stopped remaining
                      (.jump
                        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                          { procs := program.procs } ProcLabel.programEnd).regular
                        target)) =
                    Simulation.Interaction.pure (.halt .stop target) by
                  simpa [completePrefixRun,
                    TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                    using hComplete]
              exact .done
                (Simulation.Interaction.ExceptRel.ok
                  ⟨hState, hFits, hRestored⟩)
          | brk =>
              obtain ⟨label, target, hLabel, _hTarget, _hState⟩ :=
                TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim hOutcome
              simp [TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                at hLabel
          | cont =>
              obtain ⟨label, target, hLabel, _hTarget, _hState⟩ :=
                TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim hOutcome
              simp [TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                at hLabel
          | leave =>
              obtain ⟨label, target, hLabel, _hTarget, _hState⟩ :=
                TypedCfgPreservation.OutcomeSimulation.Rel.leave_elim hOutcome
              simp [TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
                at hLabel
          | halt kind =>
              obtain ⟨target, targetFinal, rfl, hStep, hState⟩ :=
                TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim hOutcome
              change
                Simulation.Interaction.ForwardRel
                  InteractionControlPreservation.OpenOutcome.Truncated
                  (PrefixDoneRel generated)
                  (.done (.ok ⟨source, .halt kind⟩))
                  (completePrefixRun cfg
                    (.stopped remaining (.halt kind target)))
              rw [show completePrefixRun cfg
                    (.stopped remaining (.halt kind target)) =
                    Simulation.Interaction.pure (.halt kind target) by rfl]
              exact .done
                (Simulation.Interaction.ExceptRel.ok
                  ⟨hOutcome, hFits, hRestored⟩)

/-- Complete unconditional Structured-to-TypedCfg preservation in the canonical
whole-program prefix semantics. -/
theorem main_prefix_forward
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) (target : EVMState)
    (hStateRel : TypedCfgPreservation.StateRel source [] target) :
    Simulation.Interaction.ForwardRel
      InteractionControlPreservation.OpenOutcome.Truncated
      (PrefixDoneRel generated)
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix cfg
        (InteractionStaticCost.blockBudget
          program sourceFuel program.body + 1)
        TypedCfgCompiler.entryLabel target) := by
  have hReturns : source.returns = [] := by
    rcases hStateRel with ⟨realized, hRealize, _hRuntime⟩
    cases hSourceReturns : source.returns with
    | nil => rfl
    | cons frame returns =>
        simp [hSourceReturns, TypedCfgPreservation.realizeStack] at hRealize
  have hBase :=
    main_forward generated hProgramWF hProgramFrameSafe sourceFuel source
      target hStateRel
  rw [hReturns] at hBase
  have hBaseSafe := Simulation.Interaction.ForwardRel.strengthen_right hBase
    (TypedCfg.InteractionFuelSafety.Program.openRunNResultWithStop
      (topPolicy generated source) cfg
      (InteractionStaticCost.blockBudget program sourceFuel program.body)
      TypedCfgCompiler.entryLabel target)
  have hBound := Simulation.Interaction.ForwardRel.bind_right
    (targetDoneRel := PrefixDoneRel generated)
    (rightNext := completePrefixRun cfg) hBaseSafe
    (fun _leftDone _rightDone hDone => by
      rcases hDone with ⟨hRelated, hSafe⟩
      cases _rightDone with
      | error error =>
          exact complete_prefix (cfg := cfg) generated hRelated hSafe
      | ok result =>
          exact complete_prefix (cfg := cfg) generated hRelated hSafe)
  rw [TypedCfg.InteractionSemantics.Program.openRunNPrefix_eq_refinedStop_add]
  exact hBound

/-- Compiler-facing adjacent theorem. The generated context and all recursive
ownership evidence are computed and discharged inside the pass. -/
theorem generateWithProcEntryShapes?_main_forward
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? program entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    exists generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg,
      InteractionControlPreservation.OpenOutcome.ForwardPreservesUnder
        generated.main cfg TypedCfgCompiler.entryLabel
        { procs := program.procs } ProcLabel.programEnd .stop source []
        (InteractionSemantics.Block.openRun
          program sourceFuel program.body source)
        (InteractionStaticCost.blockBudget
          program sourceFuel program.body)
        (topPolicy generated source) := by
  let generated :=
    TypedCfgPreservation.Program.GeneratedContext.of_generate
      hGenerate hWellTyped
  exact
    ⟨generated,
      main_forward generated hProgramWF hProgramFrameSafe sourceFuel source⟩

end GeneratedProgram


end OpenOutcome
end InteractionTruncationOwnerPreservation
end Structured
end EvmCompiler
