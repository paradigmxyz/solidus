import EvmCompiler.Structured.ObserverLoopAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Call

abbrev Trace := Assembly.ResourceTrace

theorem popReturn_of_stateRel
    {transcript : Trace}
    {bodyState : ObserverSemantics.State transcript}
    {token : Word} {tokens : List Word}
    {target : EVMState} {trace : Trace}
    (hRel :
      ObserverPreservation.StateRel
        bodyState (token :: tokens) target trace) :
    ∃ frame returned,
      (ObserverSemantics.stateModel transcript).popReturn? bodyState =
        some (frame, returned) ∧
      bodyState.source.popReturn? =
        some (frame, returned.source) ∧
      returned.cursor = bodyState.cursor := by
  obtain ⟨frame, returns, hReturns⟩ :=
    TypedCfgPreservation.StateRel.returns_cons_of_tokens_cons hRel.1
  let returnedSource : RunState :=
    { bodyState.source with returns := returns }
  let returned : ObserverSemantics.State transcript :=
    bodyState.withSource returnedSource
  have hPop :
      (ObserverSemantics.stateModel transcript).popReturn? bodyState =
        some (frame, returned) := by
    simp [ObserverSemantics.stateModel, RunState.popReturn?,
      hReturns, returned, returnedSource]
  obtain ⟨hSourcePop, hCursor⟩ :=
    ObserverSemantics.stateModel_popReturn?_eq_some hPop
  exact ⟨frame, returned, hPop, hSourcePop, hCursor⟩

theorem splitArgs?_of_compileStmtFuel?_call
    {transcript : Trace} {compilerFuel : Nat}
    {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace) :
    ∃ args callerStack,
      Structured.StackFrame.splitArgs? proc.argc
          source.source.evm.stack =
        some (args, callerStack) := by
  obtain
      ⟨returnShape, output, hSource, hReturnShape, hType, hResult⟩ :=
    TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
      hLookup hCompile
  have hArgBound :
      proc.argc ≤ TypedCfgCompiler.Shape.sourceLength input :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
      hSource
  have hStackBound :
      proc.argc ≤ source.source.evm.stack.length :=
    Nat.le_trans hArgBound hRel.sourceStack
  exact
    ⟨source.source.evm.stack.take proc.argc,
      source.source.evm.stack.drop proc.argc,
      by
        simp [Structured.StackFrame.splitArgs?, hStackBound]⟩

private theorem sinkTopUnder_observer_none
    (depth : Nat) :
    ∀ instr,
      instr ∈ TypedCfgCompiler.sinkTopUnder depth →
        TypedCfg.ObserverSemantics.Instr.observer? instr = none := by
  induction depth with
  | zero =>
      intro instr hMem
      simp [TypedCfgCompiler.sinkTopUnder] at hMem
  | succ depth ih =>
      intro instr hMem
      simp [TypedCfgCompiler.sinkTopUnder] at hMem
      rcases hMem with rfl | hMem
      · rfl
      · exact ih instr hMem

/--
The generated call-entry block takes one deterministic target step.

The source-visible argument check supplies a real source split, while the
shared call-entry realization theorem constructs the callee state and exact
procedure-entry frame relation.
-/
theorem entry_step_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace : Trace}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hProcWF : proc.WF)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace) :
    ∃ args callerStack targetFinal,
      Structured.StackFrame.splitArgs? proc.argc
          source.source.evm.stack =
        some (args, callerStack) ∧
      TypedCfg.ObserverSemantics.Program.step cfg entry target trace =
        .ok (.jump (ProcLabel.entry name) targetFinal, trace) ∧
      ObserverPreservation.StateRel.At
        (TypedCfgCompiler.Shape.procEntry proc)
        (source.withSource
          ((source.source.withEVM
            { source.source.evm with stack := args }).pushReturn
              callerStack proc.retc))
        (Structured.Stmt.callToken supply :: tokens)
        targetFinal trace := by
  obtain
      ⟨returnShape, output, hSource, hReturnShape, hType, hResult⟩ :=
    TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
      hLookup hCompile
  obtain ⟨args, callerStack, hSplit⟩ :=
    splitArgs?_of_compileStmtFuel?_call
      hLookup hCompile hRel
  have hResultEq := hResult
  subst result
  rcases
      TypedCfgPreservation.CallStack.runBody_callEntry_preserves
        (retc := proc.retc)
        (token := Structured.Stmt.callToken supply)
        hRel.rel.1 hSplit hType hProcWF.1 with
    ⟨expected, hPlainBody, hExpectedRel⟩
  have hSilent :
      ∀ instr,
        instr ∈
            (.returnToken (Structured.Stmt.callToken supply) ::
              TypedCfgCompiler.sinkTopUnder proc.argc) →
          TypedCfg.ObserverSemantics.Instr.observer? instr = none := by
    intro instr hMem
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hMem
    · rfl
    · exact sinkTopUnder_observer_none proc.argc instr hMem
  have hObserverBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (.returnToken (Structured.Stmt.callToken supply) ::
            TypedCfgCompiler.sinkTopUnder proc.argc)
          input target trace =
        .ok ((expected, output), trace) := by
    rw [TypedCfg.ObserverSemantics.Block.runBody_of_forall_observer?_eq_none
      hSilent, hPlainBody]
    rfl
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body :=
        .returnToken (Structured.Stmt.callToken supply) ::
          TypedCfgCompiler.sinkTopUnder proc.argc
      output := output
      term := .jump (ProcLabel.entry name) }
  have hFind : cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hExpectedStep :
      TypedCfg.ObserverSemantics.Program.step cfg entry target trace =
        .ok (.jump (ProcLabel.entry name) expected, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    change
      TypedCfg.ObserverSemantics.Block.run generated target trace =
        .ok (.jump (ProcLabel.entry name) expected, trace)
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [show
      TypedCfg.ObserverSemantics.Block.runBody
          generated.body generated.input target trace =
        .ok ((expected, generated.output), trace) by
      simpa [generated] using hObserverBody]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hArgsLength :
      args.length = proc.argc :=
    (TypedCfgPreservation.CallStack.splitArgs?_eq_some hSplit).1
  let callState : ObserverSemantics.State transcript :=
    source.withSource
      ((source.source.withEVM
        { source.source.evm with stack := args }).pushReturn
          callerStack proc.retc)
  have hCallRel :
      ObserverPreservation.StateRel
        callState (Structured.Stmt.callToken supply :: tokens)
        expected trace :=
    ⟨by simpa [callState] using hExpectedRel, hRel.rel.2⟩
  have hCallFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procEntry proc)
        callState.source.evm.stack.length := by
    rw [TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
        (TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc)]
    simpa [callState] using hArgsLength
  exact
    ⟨args, callerStack, expected, hSplit, hExpectedStep,
      ObserverPreservation.StateRel.At.ofFits hCallRel hCallFits⟩

/--
The canonical procedure entry reaches the compiler-selected body entry in at
most one target step, preserving both runtime state and the exact source frame.
-/
theorem procEntry_runN
    {transcript : Trace}
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
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel :
      ObserverPreservation.StateRel.At
        (TypedCfgCompiler.Shape.procEntry proc)
        source tokens target trace) :
    ∃ routeFuel,
      routeFuel ≤ 1 ∧
        TypedCfg.ObserverSemantics.Program.runN cfg routeFuel
            (ProcLabel.entry proc.name) target trace =
          .ok (.jump fragment.entry target, trace) ∧
        ObserverPreservation.StateRel.At
          fragment.input source tokens target trace := by
  rcases fragment.route with hDirect | hAdapterRoute
  · rcases hDirect with ⟨hEntry, hInput⟩
    refine ⟨0, by omega, ?_, ?_⟩
    · simp [hEntry]
    · simpa [hInput] using hRel
  · rcases hAdapterRoute with
      ⟨adapter, hEntry, hInput, hFrame,
        hAdapterCompile, hAdapterMem⟩
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
                 term := .invalid }] :=
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
        have hPlainRunAt :
            TypedCfg.Instr.runAt (.relabel fragment.input)
                (TypedCfgCompiler.Shape.procEntry proc) target =
              .ok (target, output) := by
          unfold TypedCfg.Instr.runAt
          rw [hType]
          simp [TypedCfg.Instr.runState, Bind.bind, Except.bind]
        have hObserverRunAt :
            TypedCfg.ObserverSemantics.Instr.runAt
                (.relabel fragment.input)
                (TypedCfgCompiler.Shape.procEntry proc)
                target trace =
              .ok ((target, output), trace) := by
          rw [TypedCfg.ObserverSemantics.Instr.runAt_of_observer?_eq_none
            (by rfl), hPlainRunAt]
          rfl
        let generated : TypedCfg.Block :=
          { label := ProcLabel.entry proc.name
            input := TypedCfgCompiler.Shape.procEntry proc
            body := [.relabel fragment.input]
            output := output
            term := .jump (ProcLabel.body proc.name) }
        have hRun :
            TypedCfg.ObserverSemantics.Block.run generated target trace =
              .ok (.jump (ProcLabel.body proc.name) target, trace) := by
          unfold TypedCfg.ObserverSemantics.Block.run
          rw [TypedCfg.ObserverSemantics.Block.runBody_cons,
            hObserverRunAt]
          simp [TypedCfg.ObserverSemantics.Block.runBody_nil,
            generated, TypedCfg.Block.runTerm,
            Bind.bind, Except.bind]
        have hStep :
            TypedCfg.ObserverSemantics.Program.step cfg
                (ProcLabel.entry proc.name) target trace =
              .ok (.jump fragment.entry target, trace) := by
          unfold TypedCfg.ObserverSemantics.Program.step
          rw [show
            cfg.findBlock? (ProcLabel.entry proc.name) =
                some generated by
              simpa [generated] using hFind]
          simpa [hEntry, generated] using hRun
        have hInputDepth :
            fragment.input.returnTokenDepth? = some proc.argc :=
          TypedCfgCompilerFacts.Shape.requireReturnTokenDepth?_eq_some_iff.mp
            hFrame
        have hSourceLength :
            source.source.evm.stack.length = proc.argc := by
          have hProcFits := hRel.sourceFrameFits
          rw [TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
              (TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc)]
            at hProcFits
          exact hProcFits
        have hInputFits :
            TypedCfgCompiler.Shape.SourceFrameFits fragment.input
              source.source.evm.stack.length := by
          rw [TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
              hInputDepth]
          exact hSourceLength
        refine ⟨1, by omega, ?_, ?_⟩
        · simpa [hEntry] using
            TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep
        · exact
            ObserverPreservation.StateRel.At.ofFits hRel.rel hInputFits

/--
Return dispatch is one deterministic target step from the generated procedure
exit block to the call site's regular continuation.
-/
theorem dispatch_step
    {transcript : Trace}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {site : TypedCfgCompiler.DispatchSite}
    {bodyState returned : ObserverSemantics.State transcript}
    {frame : ReturnDest} {stack : EvmYul.Stack Word}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs =
        some proc)
    (hSiteProc : site.procName = proc.name)
    (hSiteMem : site ∈ context.calls)
    (hRel :
      ObserverPreservation.StateRel
        bodyState (site.token :: tokens) target trace)
    (hPop :
      bodyState.source.popReturn? =
        some (frame, returned.source))
    (hCursor : returned.cursor = bodyState.cursor)
    (hAttach :
      Structured.StackFrame.attachReturns? frame
          bodyState.source.evm.stack =
        some stack)
    (hRetc : frame.retc = proc.retc) :
    ∃ targetFinal,
      TypedCfg.ObserverSemantics.Program.step cfg
          (ProcLabel.exit proc.name) target trace =
        .ok (.jump site.returnLabel targetFinal, trace) ∧
      ObserverPreservation.StateRel
        (returned.withSource
          (returned.source.withEVM
            { bodyState.source.evm with stack := stack }))
        tokens targetFinal trace := by
  rcases
      TypedCfgPreservation.CallStack.eraseReturnToken_preserves
        hRel.1 hPop hAttach with
    ⟨hToken, hFinalRel⟩
  have hFindTarget :
      TypedCfg.Block.ReturnSite.findTarget? site.token
          (TypedCfgCompiler.returnSitesFor proc.name context.calls) =
        some site.returnLabel := by
    simpa [hSiteProc] using
      TypedCfgCompilerFacts.Call.findTarget?_returnSitesFor_of_mem
        context.tokensUnique hSiteMem
  have hSitesNonempty :
      (TypedCfgCompiler.returnSitesFor
        proc.name context.calls).isEmpty = false := by
    cases hSites :
        TypedCfgCompiler.returnSitesFor proc.name context.calls with
    | nil =>
        simp [hSites, TypedCfg.Block.ReturnSite.findTarget?] at hFindTarget
    | cons head rest =>
        rfl
  have hFindBlock := context.dispatchBlock hLookup
  let targetFinal : EVMState :=
    { target with stack := target.stack.eraseIdx proc.retc }
  let generated := TypedCfgCompiler.dispatchBlock proc context.calls
  have hRun :
      TypedCfg.ObserverSemantics.Block.run generated target trace =
        .ok (.jump site.returnLabel targetFinal, trace) := by
    rw [hRetc] at hToken hFinalRel
    simp [generated, TypedCfg.ObserverSemantics.Block.run,
      TypedCfg.ObserverSemantics.Block.runBody_nil,
      TypedCfgCompiler.dispatchBlock, hSitesNonempty,
      TypedCfg.Block.runTerm,
      TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit,
      hToken, hFindTarget, targetFinal, Bind.bind, Except.bind]
  have hStep :
      TypedCfg.ObserverSemantics.Program.step cfg
          (ProcLabel.exit proc.name) target trace =
        .ok (.jump site.returnLabel targetFinal, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFindBlock]
    exact hRun
  refine ⟨targetFinal, hStep, ?_⟩
  rw [hRetc] at hFinalRel
  refine ⟨?_, ?_⟩
  · simpa using hFinalRel
  · simpa [Simulation.ResourceReplay.State.remaining, hCursor] using hRel.2

/--
Fixed-fuel backward adequacy for a checked internal call. The callee callback
is required only at strictly smaller target fuel, which is the well-founded
interface used by generated-context recursive composition.
-/
theorem adequateWithinFuel_call_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    {name : Structured.Name}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {targetFuel : Nat}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hProcs : ctx.procs = program.procs)
    (hProgramWF : program.WF)
    (hRegular : continuations.regular = regular)
    (hProcEntryNotAccepted :
      ∀ {proc : Structured.Proc},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ target,
            ¬ accept (.jump (ProcLabel.entry proc.name) target))
    (hProcExitNotAccepted :
      ∀ {proc : Structured.Proc}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ target,
            OutcomeSimulation.FrameMatches callSource
              (Structured.Stmt.callToken supply :: tokens)
              (TypedCfgCompiler.Shape.procExit proc) target →
            (∃ hidden : EvmYul.Stack Word,
              TypedCfgPreservation.realizeStack
                  [] source.source.returns tokens = some hidden) →
            (∃ frame : Structured.ReturnDest,
              callSource.source.returns =
                frame :: source.source.returns) →
            ¬ accept (.jump (ProcLabel.exit proc.name) target))
    (hBodyEntryNotAccepted :
      ∀ {proc : Structured.Proc}
        {fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes program.procs proc
            generated.procBlocks generated.procCalls}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ target,
            ¬ OutcomeSimulation.JumpAt callSource
              (Structured.Stmt.callToken supply :: tokens)
              (ProcLabel.exit proc.name)
              (TypedCfgCompiler.Shape.procExit proc) accept
              (.jump fragment.entry target))
    (hBodyAdequate :
      ∀ {proc : Structured.Proc}
        {fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes program.procs proc
            generated.procBlocks generated.procCalls}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ {bodyTargetFuel : Nat},
          bodyTargetFuel < targetFuel →
          OutcomeSimulation.AdequateWithinFuel
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel proc.body callSource sourceOutcome)
            fragment.result
            { procs := program.procs
              leaveLabel? := some (ProcLabel.exit proc.name)
              leaveShape? :=
                some (TypedCfgCompiler.Shape.procExit proc) }
            cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name)
                leaveShape? :=
                  some (TypedCfgCompiler.Shape.procExit proc) }
              (ProcLabel.exit proc.name))
            (OutcomeSimulation.JumpAt callSource
              (Structured.Stmt.callToken supply :: tokens)
              (ProcLabel.exit proc.name)
              (TypedCfgCompiler.Shape.procExit proc) accept)
            fragment.entry fragment.input callSource
            (Structured.Stmt.callToken supply :: tokens)
            bodyTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.call name) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens
      targetFuel := by
  intro hAccept target trace traceFinal
    targetOutcome hRel hReach
  obtain ⟨proc, hLookupCtx⟩ :=
    TypedCfgCompilerFacts.Call.exists_lookup_of_compileStmtFuel?_call
      hCompile
  have hLookup :
      Structured.ProcList.lookup? name program.procs = some proc := by
    simpa [hProcs] using hLookupCtx
  have hProcWF :=
    Structured.Program.procWF_of_lookup? hProgramWF hLookup
  have hName :=
    Structured.ProcList.name_of_lookup? hLookup
  obtain
      ⟨returnShape, output, hSource, hReturnShape, hType, hResult⟩ :=
    TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
      hLookupCtx hCompile
  subst result
  let site : TypedCfgCompiler.DispatchSite :=
    { procName := name
      token := Structured.Stmt.callToken supply
      returnLabel := regular
      caseLabel := .generated supply 10000 }
  have hSiteMem : site ∈ generated.calls := by
    apply hCalls site
    simp [site]
  obtain ⟨fragment, hFragmentBlocks, hFragmentCalls⟩ :=
    generated.procFragment_of_lookup? hLookup
  obtain
      ⟨args, callerStack, targetAtEntry,
        hSplit, hEntryStep, hEntryRel⟩ :=
    entry_step_of_compileStmtFuel?
      hLookupCtx hCompile hBlocks hProcWF hRel
  have hAfterEntry :=
    OutcomeSimulation.FirstReaches.tail_of_step_jump
      hReach hEntryStep
  have hAfterEntryPositive : 0 < targetFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hAfterEntry (by
        simpa [hName] using
          hProcEntryNotAccepted hLookup targetAtEntry)
  cases targetFuel with
  | zero =>
      omega
  | succ targetFuel =>
      obtain ⟨routeFuel, hRouteOne, hRouteRun, hFragmentRel⟩ :=
        procEntry_runN generated (fragment := fragment) hEntryRel
      obtain
          ⟨routePrefixFuel, routePrefixOutcome, routePrefixTrace,
            hRoutePrefixLe, hRoutePrefix⟩ :=
        OutcomeSimulation.FirstReaches.exists_of_run
          hRouteRun (show
            (fun outcome =>
              outcome =
                TypedCfg.Outcome.jump fragment.entry targetAtEntry)
              (TypedCfg.Outcome.jump fragment.entry targetAtEntry) from rfl)
      have hRouteOutcome :
          routePrefixOutcome =
            TypedCfg.Outcome.jump fragment.entry targetAtEntry :=
        hRoutePrefix.boundary.symm
      subst routePrefixOutcome
      have hRouteTrace : routePrefixTrace = trace := by
        cases routePrefixFuel with
        | zero =>
            have hRun := hRoutePrefix.run
            simp only
              [TypedCfg.ObserverSemantics.Program.runN_zero] at hRun
            exact (Prod.mk.inj (Except.ok.inj hRun)).2.symm
        | succ routePrefixFuel =>
            have hPrefixZero : routePrefixFuel = 0 := by
              omega
            subst routePrefixFuel
            have hRouteFuel : routeFuel = 1 := by
              omega
            subst routeFuel
            have hEq :
                (.ok
                    (TypedCfg.Outcome.jump
                      fragment.entry targetAtEntry,
                      routePrefixTrace) :
                  Except TypedCfg.EVMException
                    (TypedCfg.Outcome × Trace)) =
                  .ok
                    (TypedCfg.Outcome.jump
                      fragment.entry targetAtEntry, trace) :=
              hRoutePrefix.run.symm.trans hRouteRun
            exact (Prod.mk.inj (Except.ok.inj hEq)).2
      subst routePrefixTrace
      have hRouteLe : routePrefixFuel ≤ targetFuel + 1 := by
        omega
      have hAfterEntryProc :
          OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
            (ProcLabel.entry proc.name) targetAtEntry trace
            targetOutcome traceFinal := by
        simpa [hName] using hAfterEntry
      have hAfterRoute :=
        OutcomeSimulation.FirstReaches.tail_of_prefix_jump
          hAfterEntryProc hRoutePrefix hRouteLe
      let callSource : ObserverSemantics.State transcript :=
        source.withSource
          ((source.source.withEVM
            { source.source.evm with stack := args }).pushReturn
              callerStack proc.retc)
      have hBodyFinalAccepted :
          OutcomeSimulation.JumpAt callSource
            (Structured.Stmt.callToken supply :: tokens)
            (ProcLabel.exit proc.name)
            (TypedCfgCompiler.Shape.procExit proc)
            accept targetOutcome :=
        OutcomeSimulation.JumpAt.of_accept hAfterRoute.boundary
      obtain
          ⟨bodyPrefixFuel, bodyTargetOutcome, bodyTrace,
            hBodyPrefixLe, hBodyReach⟩ :=
        OutcomeSimulation.FirstReaches.exists_of_run
          hAfterRoute.run hBodyFinalAccepted
      have hBodyPositive : 0 < bodyPrefixFuel :=
        OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
          hBodyReach
          (hBodyEntryNotAccepted hLookup targetAtEntry)
      cases bodyPrefixFuel with
      | zero =>
          omega
      | succ bodyTargetFuel =>
          obtain
              ⟨bodySourceFuel, bodyOutcome,
                hBodyEval, hBodyRel, hBodyArtifact⟩ :=
            hBodyAdequate (fragment := fragment)
              (callSource := callSource) hLookup
              (bodyTargetFuel := bodyTargetFuel) (by omega)
              (fun bodyFuel bodyOutcome targetOutcome bodyTrace
                  hBodyEval hBodyRel _hBodyArtifact => by
                have hExitJoin :
                    OutcomeSimulation.JoinArtifact
                      { procs := program.procs
                        leaveLabel? := some (ProcLabel.exit proc.name)
                        leaveShape? :=
                          some (TypedCfgCompiler.Shape.procExit proc) }
                      (TypedCfgCompiler.Shape.procExit proc)
                      bodyOutcome :=
                  OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
                    fragment.fallthrough _hBodyArtifact
                rcases bodyOutcome with ⟨bodyState, bodyMode⟩
                cases bodyMode with
                | regular =>
                    obtain ⟨targetState, hTargetOutcome, hStateRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                        hBodyRel
                    subst targetOutcome
                    exact
                      OutcomeSimulation.JumpAt.of_rel
                        (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
                          hBodyEval
                          (by simp [ObserverSemantics.Outcome.Nonhalting]))
                        hStateRel hExitJoin
                | brk =>
                    obtain ⟨label, targetState, hLabel,
                      hTargetOutcome, _hStateRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.brk_elim
                        hBodyRel
                    change (none : Option Assembly.Label) = some label at hLabel
                    cases hLabel
                | cont =>
                    obtain ⟨label, targetState, hLabel,
                      hTargetOutcome, _hStateRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.cont_elim
                        hBodyRel
                    change (none : Option Assembly.Label) = some label at hLabel
                    cases hLabel
                | leave =>
                    obtain ⟨label, targetState, hLabel,
                      hTargetOutcome, _hStateRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.leave_elim
                        hBodyRel
                    have hLabelEq : label = ProcLabel.exit proc.name := by
                      simpa using (Option.some.inj hLabel).symm
                    subst label
                    subst targetOutcome
                    have hExitFits :
                        TypedCfgCompiler.Shape.SourceFrameFits
                          (TypedCfgCompiler.Shape.procExit proc)
                          bodyState.source.evm.stack.length := by
                      simpa [OutcomeSimulation.JoinArtifact] using hExitJoin
                    exact
                      OutcomeSimulation.JumpAt.of_rel
                        (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
                          hBodyEval
                          (by simp [ObserverSemantics.Outcome.Nonhalting]))
                        _hStateRel hExitFits
                | halt kind =>
                    obtain
                        ⟨targetBefore, targetAfter, hTargetOutcome,
                          hTargetStep, hHaltRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.halt_elim
                        hBodyRel
                    subst targetOutcome
                    have hOuterRel :
                        ObserverPreservation.OutcomeSimulation.Rel
                          continuations tokens
                          (Structured.OutcomeT.halt kind bodyState)
                          (.halt kind targetBefore) bodyTrace :=
                      ObserverPreservation.OutcomeSimulation.Rel.halt_iff.mpr
                        ⟨rfl, targetAfter, hTargetStep, hHaltRel⟩
                    apply OutcomeSimulation.JumpAt.of_accept
                    exact
                      hAccept (bodyFuel + 1)
                        (Structured.OutcomeT.halt kind bodyState)
                        (.halt kind targetBefore) bodyTrace
                        (Structured.EffectSemantics.Stmt.Eval.call_halt
                          hLookup hSplit hBodyEval)
                        hOuterRel (by trivial))
              (by simpa [callSource] using hFragmentRel)
              hBodyReach
          rcases bodyOutcome with ⟨bodyState, bodyMode⟩
          cases bodyMode with
          | halt kind =>
              obtain
                  ⟨targetBefore, targetAfter, hBodyTarget,
                    hTargetStep, hHaltRel⟩ :=
                ObserverPreservation.OutcomeSimulation.Rel.halt_elim
                  hBodyRel
              subst bodyTargetOutcome
              have hOuterRel :
                  ObserverPreservation.OutcomeSimulation.Rel
                    continuations tokens
                    (Structured.OutcomeT.halt kind bodyState)
                    (.halt kind targetBefore) bodyTrace :=
                ObserverPreservation.OutcomeSimulation.Rel.halt_iff.mpr
                  ⟨rfl, targetAfter, hTargetStep, hHaltRel⟩
              obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                  hAfterRoute hBodyReach hBodyPrefixLe
                  (hAccept (bodySourceFuel + 1)
                    (Structured.OutcomeT.halt kind bodyState)
                    (.halt kind targetBefore) bodyTrace
                    (Structured.EffectSemantics.Stmt.Eval.call_halt
                      hLookup hSplit hBodyEval)
                    hOuterRel (by trivial))
              subst targetOutcome
              subst traceFinal
              exact
                ⟨bodySourceFuel + 1,
                  Structured.OutcomeT.halt kind bodyState,
                  Structured.EffectSemantics.Stmt.Eval.call_halt
                    hLookup hSplit hBodyEval,
                  hOuterRel, by trivial⟩
          | brk =>
              change
                ∃ output,
                  (none : Option TypedCfg.Shape) = some output ∧
                    TypedCfgCompiler.Shape.SourceFrameFits output
                      bodyState.source.evm.stack.length
                at hBodyArtifact
              obtain ⟨output, hNone, _hFits⟩ := hBodyArtifact
              cases hNone
          | cont =>
              change
                ∃ output,
                  (none : Option TypedCfg.Shape) = some output ∧
                    TypedCfgCompiler.Shape.SourceFrameFits output
                      bodyState.source.evm.stack.length
                at hBodyArtifact
              obtain ⟨output, hNone, _hFits⟩ := hBodyArtifact
              cases hNone
          | regular =>
              obtain ⟨targetAtExit, hBodyTarget, hBodyStateRel⟩ :=
                ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                  hBodyRel
              subst bodyTargetOutcome
              have hExitFits :
                  TypedCfgCompiler.Shape.SourceFrameFits
                    (TypedCfgCompiler.Shape.procExit proc)
                    bodyState.source.evm.stack.length := by
                exact
                  OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
                    fragment.fallthrough hBodyArtifact
              obtain
                  ⟨frame, returned, hPop, hSourcePop, hCursor⟩ :=
                popReturn_of_stateRel hBodyStateRel
              have hFrameEq :=
                ObserverSemantics.CallStack.poppedFrame_eq_of_regular_eval
                  hBodyEval hPop
              have hBodyLength :
                  bodyState.source.evm.stack.length = proc.retc := by
                rw [TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
                    (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)]
                  at hExitFits
                exact hExitFits
              let stack :=
                bodyState.source.evm.stack ++ callerStack
              have hAttach :
                  Structured.StackFrame.attachReturns? frame
                      bodyState.source.evm.stack =
                    some stack := by
                simp [Structured.StackFrame.attachReturns?,
                  hFrameEq, hBodyLength, stack]
              have hSiteProc : site.procName = proc.name := by
                simp [site,
                  Structured.ProcList.name_of_lookup? hLookup]
              obtain ⟨targetFinal, hDispatchStep, hFinalRel⟩ :=
                dispatch_step generated hLookup hSiteProc hSiteMem
                  hBodyStateRel hSourcePop hCursor hAttach
                  (by simpa [hFrameEq])
              have hAfterBody :=
                OutcomeSimulation.FirstReaches.tail_of_prefix_jump
                  hAfterRoute hBodyReach hBodyPrefixLe
              have hAfterBodyPositive :
                  0 < targetFuel + 1 - routePrefixFuel -
                      (bodyTargetFuel + 1) :=
                OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                  hAfterBody
                  (hProcExitNotAccepted
                    (callSource := callSource) hLookup targetAtExit
                    (OutcomeSimulation.FrameMatches.of_rel
                      (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
                        hBodyEval
                        (by simp [ObserverSemantics.Outcome.Nonhalting]))
                      hBodyStateRel hExitFits)
                    (by
                      obtain ⟨hidden, hHidden, _hStack⟩ :=
                        ObserverPreservation.StateRel.targetStack_decompose
                          hRel
                      exact ⟨hidden, hHidden⟩)
                    (by
                      refine
                        ⟨{ callerStack := callerStack, retc := proc.retc },
                          ?_⟩
                      simp [callSource, RunState.pushReturn,
                        RunState.withEVM]))
              cases hResidual :
                  targetFuel + 1 - routePrefixFuel -
                    (bodyTargetFuel + 1) with
              | zero =>
                  omega
              | succ dispatchFuel =>
                  let finalSource : ObserverSemantics.State transcript :=
                    returned.withSource
                      (returned.source.withEVM
                        { bodyState.source.evm with stack := stack })
                  have hArgsLength :=
                    (TypedCfgPreservation.CallStack.splitArgs?_eq_some
                      hSplit).1
                  have hSourceStack :=
                    (TypedCfgPreservation.CallStack.splitArgs?_eq_some
                      hSplit).2
                  have hFinalFits :
                      TypedCfgCompiler.Shape.SourceFrameFits returnShape
                        finalSource.source.evm.stack.length := by
                    have hAfterFits :=
                      TypedCfgCompilerFacts.Shape.sourceFrameFits_afterCall
                        hSource hReturnShape hRel.sourceFrameFits
                    have hLength :
                        finalSource.source.evm.stack.length =
                          source.source.evm.stack.length -
                            proc.argc + proc.retc := by
                      simp [finalSource, stack, hSourceStack,
                        hArgsLength, hBodyLength, Nat.add_comm]
                    simpa [hLength] using hAfterFits
                  have hCallEval :
                      ObserverSemantics.Stmt.Eval program
                        (bodySourceFuel + 1) (.call name) source
                        (Structured.OutcomeT.regular finalSource) := by
                    simpa [callSource, finalSource] using
                      Structured.EffectSemantics.Stmt.Eval.call_regular
                        (model := ObserverSemantics.stateModel transcript)
                        (handler := ObserverSemantics.handler transcript)
                        (program := program)
                        hLookup hSplit hBodyEval hPop hAttach
                  have hCallRel :
                      ObserverPreservation.OutcomeSimulation.Rel
                        continuations tokens
                        (Structured.OutcomeT.regular finalSource)
                        (.jump regular targetFinal) bodyTrace :=
                    ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                      ⟨by simpa [site] using hRegular.symm,
                        by simpa [finalSource] using hFinalRel⟩
                  have hDispatchAccepted :
                      accept (.jump regular targetFinal) := by
                    exact
                      hAccept (bodySourceFuel + 1)
                        (Structured.OutcomeT.regular finalSource)
                        (.jump regular targetFinal) bodyTrace
                        hCallEval hCallRel
                        ⟨returnShape, rfl, hFinalFits⟩
                  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
                    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
                      (by simpa [hResidual] using hAfterBody)
                      hDispatchStep hDispatchAccepted
                  subst targetOutcome
                  subst traceFinal
                  exact
                    ⟨bodySourceFuel + 1,
                      Structured.OutcomeT.regular finalSource,
                      hCallEval, hCallRel,
                      ⟨returnShape, rfl, hFinalFits⟩⟩
          | leave =>
              obtain
                  ⟨leaveLabel, targetAtExit, hLeaveLabel,
                    hBodyTarget, hBodyStateRel⟩ :=
                ObserverPreservation.OutcomeSimulation.Rel.leave_elim
                  hBodyRel
              have hExitLabel : leaveLabel = ProcLabel.exit proc.name := by
                simpa using (Option.some.inj hLeaveLabel).symm
              subst leaveLabel
              subst bodyTargetOutcome
              have hExitFits :
                  TypedCfgCompiler.Shape.SourceFrameFits
                    (TypedCfgCompiler.Shape.procExit proc)
                    bodyState.source.evm.stack.length := by
                change
                  ∃ output,
                    some (TypedCfgCompiler.Shape.procExit proc) =
                        some output ∧
                      TypedCfgCompiler.Shape.SourceFrameFits output
                        bodyState.source.evm.stack.length
                  at hBodyArtifact
                obtain ⟨output, hOutput, hFits⟩ := hBodyArtifact
                have hOutputEq :
                    output = TypedCfgCompiler.Shape.procExit proc :=
                  Option.some.inj hOutput.symm
                simpa [hOutputEq] using hFits
              obtain
                  ⟨frame, returned, hPop, hSourcePop, hCursor⟩ :=
                popReturn_of_stateRel hBodyStateRel
              have hFrameEq :=
                ObserverSemantics.CallStack.poppedFrame_eq_of_leave_eval
                  hBodyEval hPop
              have hBodyLength :
                  bodyState.source.evm.stack.length = proc.retc := by
                rw [TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
                    (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)]
                  at hExitFits
                exact hExitFits
              let stack :=
                bodyState.source.evm.stack ++ callerStack
              have hAttach :
                  Structured.StackFrame.attachReturns? frame
                      bodyState.source.evm.stack =
                    some stack := by
                simp [Structured.StackFrame.attachReturns?,
                  hFrameEq, hBodyLength, stack]
              have hSiteProc : site.procName = proc.name := by
                simp [site,
                  Structured.ProcList.name_of_lookup? hLookup]
              obtain ⟨targetFinal, hDispatchStep, hFinalRel⟩ :=
                dispatch_step generated hLookup hSiteProc hSiteMem
                  hBodyStateRel hSourcePop hCursor hAttach
                  (by simpa [hFrameEq])
              have hAfterBody :=
                OutcomeSimulation.FirstReaches.tail_of_prefix_jump
                  hAfterRoute hBodyReach hBodyPrefixLe
              have hAfterBodyPositive :
                  0 < targetFuel + 1 - routePrefixFuel -
                      (bodyTargetFuel + 1) :=
                OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                  hAfterBody
                  (hProcExitNotAccepted
                    (callSource := callSource) hLookup targetAtExit
                    (OutcomeSimulation.FrameMatches.of_rel
                      (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
                        hBodyEval
                        (by simp [ObserverSemantics.Outcome.Nonhalting]))
                      hBodyStateRel hExitFits)
                    (by
                      obtain ⟨hidden, hHidden, _hStack⟩ :=
                        ObserverPreservation.StateRel.targetStack_decompose
                          hRel
                      exact ⟨hidden, hHidden⟩)
                    (by
                      refine
                        ⟨{ callerStack := callerStack, retc := proc.retc },
                          ?_⟩
                      simp [callSource, RunState.pushReturn,
                        RunState.withEVM]))
              cases hResidual :
                  targetFuel + 1 - routePrefixFuel -
                    (bodyTargetFuel + 1) with
              | zero =>
                  omega
              | succ dispatchFuel =>
                  let finalSource : ObserverSemantics.State transcript :=
                    returned.withSource
                      (returned.source.withEVM
                        { bodyState.source.evm with stack := stack })
                  have hArgsLength :=
                    (TypedCfgPreservation.CallStack.splitArgs?_eq_some
                      hSplit).1
                  have hSourceStack :=
                    (TypedCfgPreservation.CallStack.splitArgs?_eq_some
                      hSplit).2
                  have hFinalFits :
                      TypedCfgCompiler.Shape.SourceFrameFits returnShape
                        finalSource.source.evm.stack.length := by
                    have hAfterFits :=
                      TypedCfgCompilerFacts.Shape.sourceFrameFits_afterCall
                        hSource hReturnShape hRel.sourceFrameFits
                    have hLength :
                        finalSource.source.evm.stack.length =
                          source.source.evm.stack.length -
                            proc.argc + proc.retc := by
                      simp [finalSource, stack, hSourceStack,
                        hArgsLength, hBodyLength, Nat.add_comm]
                    simpa [hLength] using hAfterFits
                  have hCallEval :
                      ObserverSemantics.Stmt.Eval program
                        (bodySourceFuel + 1) (.call name) source
                        (Structured.OutcomeT.regular finalSource) := by
                    simpa [callSource, finalSource] using
                      Structured.EffectSemantics.Stmt.Eval.call_leave
                        (model := ObserverSemantics.stateModel transcript)
                        (handler := ObserverSemantics.handler transcript)
                        (program := program)
                        hLookup hSplit hBodyEval hPop hAttach
                  have hCallRel :
                      ObserverPreservation.OutcomeSimulation.Rel
                        continuations tokens
                        (Structured.OutcomeT.regular finalSource)
                        (.jump regular targetFinal) bodyTrace :=
                    ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                      ⟨by simpa [site] using hRegular.symm,
                        by simpa [finalSource] using hFinalRel⟩
                  have hDispatchAccepted :
                      accept (.jump regular targetFinal) := by
                    exact
                      hAccept (bodySourceFuel + 1)
                        (Structured.OutcomeT.regular finalSource)
                        (.jump regular targetFinal) bodyTrace
                        hCallEval hCallRel
                        ⟨returnShape, rfl, hFinalFits⟩
                  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
                    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
                      (by simpa [hResidual] using hAfterBody)
                      hDispatchStep hDispatchAccepted
                  subst targetOutcome
                  subst traceFinal
                  exact
                    ⟨bodySourceFuel + 1,
                      Structured.OutcomeT.regular finalSource,
                      hCallEval, hCallRel,
                      ⟨returnShape, rfl, hFinalFits⟩⟩

/--
Unbounded adjacent-pass call interface. Generated-context recursion should use
the fixed-fuel theorem above; callers that already own full callee adequacy can
use this wrapper.
-/
theorem adequateWithin_call_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    {name : Structured.Name}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hProcs : ctx.procs = program.procs)
    (hProgramWF : program.WF)
    (hRegular : continuations.regular = regular)
    (hProcEntryNotAccepted :
      ∀ {proc : Structured.Proc},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ target,
            ¬ accept (.jump (ProcLabel.entry proc.name) target))
    (hProcExitNotAccepted :
      ∀ {proc : Structured.Proc}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ target,
            OutcomeSimulation.FrameMatches callSource
              (Structured.Stmt.callToken supply :: tokens)
              (TypedCfgCompiler.Shape.procExit proc) target →
            (∃ hidden : EvmYul.Stack Word,
              TypedCfgPreservation.realizeStack
                  [] source.source.returns tokens = some hidden) →
            (∃ frame : Structured.ReturnDest,
              callSource.source.returns =
                frame :: source.source.returns) →
            ¬ accept (.jump (ProcLabel.exit proc.name) target))
    (hBodyEntryNotAccepted :
      ∀ {proc : Structured.Proc}
        {fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes program.procs proc
            generated.procBlocks generated.procCalls}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
          ∀ target,
            ¬ OutcomeSimulation.JumpAt callSource
              (Structured.Stmt.callToken supply :: tokens)
              (ProcLabel.exit proc.name)
              (TypedCfgCompiler.Shape.procExit proc) accept
              (.jump fragment.entry target))
    (hBodyAdequate :
      ∀ {proc : Structured.Proc}
        {fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes program.procs proc
            generated.procBlocks generated.procCalls}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
          OutcomeSimulation.AdequateWithin
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel proc.body callSource sourceOutcome)
            fragment.result
            { procs := program.procs
              leaveLabel? := some (ProcLabel.exit proc.name)
              leaveShape? :=
                some (TypedCfgCompiler.Shape.procExit proc) }
            cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name)
                leaveShape? :=
                  some (TypedCfgCompiler.Shape.procExit proc) }
              (ProcLabel.exit proc.name))
            (OutcomeSimulation.JumpAt callSource
              (Structured.Stmt.callToken supply :: tokens)
              (ProcLabel.exit proc.name)
              (TypedCfgCompiler.Shape.procExit proc) accept)
            fragment.entry fragment.input callSource
            (Structured.Stmt.callToken supply :: tokens)) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.call name) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  exact
    adequateWithinFuel_call_of_compileStmtFuel?
      generated hCompile hBlocks hCalls hProcs hProgramWF hRegular
      hProcEntryNotAccepted hProcExitNotAccepted hBodyEntryNotAccepted
      (fun {proc} {fragment} {callSource} hLookup
          {bodyTargetFuel} _hSmaller =>
        OutcomeSimulation.AdequateWithin.fuel
          (hBodyAdequate (fragment := fragment)
            (callSource := callSource) hLookup)
          bodyTargetFuel)
      hAccept hRel hReach

end Call
end ObserverAdequacy
end Structured
end EvmCompiler
