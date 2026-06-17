import EvmCompiler.Structured.InteractionLoopPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionCallPreservation

namespace Call

def procContext (program : Structured.Program)
    (proc : Structured.Proc) : TypedCfgCompiler.Context :=
  { procs := program.procs
    leaveLabel? := some (ProcLabel.exit proc.name)
    leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }

def bodyStopPolicy
    (bodyResult : TypedCfgCompiler.Result)
    (program : Structured.Program) (proc : Structured.Proc)
    (returns : List ReturnDest) (tokens : List Word)
    (policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy) :
    InteractionControlPreservation.OpenOutcome.StopPolicy :=
  InteractionControlPreservation.OpenOutcome.pushStopJump
    bodyResult (procContext program proc) (ProcLabel.exit proc.name)
    returns tokens policy

private theorem popReturn_eq_of_returns_eq
    {source bodyState returned : RunState}
    {callerStack : EvmYul.Stack Word} {retc : Nat}
    {frame : ReturnDest}
    (hReturns :
      bodyState.returns =
        ((source.pushReturn callerStack retc).returns))
    (hPop : bodyState.popReturn? = some (frame, returned)) :
    frame = { callerStack := callerStack, retc := retc } ∧
      returned.returns = source.returns := by
  simp only [RunState.pushReturn_returns] at hReturns
  unfold RunState.popReturn? at hPop
  rw [hReturns] at hPop
  simp at hPop
  refine ⟨hPop.1.symm, ?_⟩
  rw [← hPop.2]

private theorem finalFrameFits
    {input returnShape : TypedCfg.Shape}
    {source bodyState : RunState}
    {proc : Structured.Proc}
    {args callerStack stack : EvmYul.Stack Word}
    {frame : ReturnDest}
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? proc.argc input =
        some ())
    (hAfter :
      TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc =
        some returnShape)
    (hInputFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hBodyFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procExit proc)
        bodyState.evm.stack.length)
    (hFrame :
      frame = { callerStack := callerStack, retc := proc.retc })
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack) :
    TypedCfgCompiler.Shape.SourceFrameFits returnShape stack.length := by
  have hBodyLength :
      bodyState.evm.stack.length = proc.retc := by
    exact
      hBodyFits.2 proc.retc
        (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
  have hArgsLength :=
    (TypedCfgPreservation.CallStack.splitArgs?_eq_some hSplit).1
  have hSourceStack :=
    (TypedCfgPreservation.CallStack.splitArgs?_eq_some hSplit).2
  have hStack :
      stack = bodyState.evm.stack ++ callerStack := by
    subst frame
    unfold Structured.StackFrame.attachReturns? at hAttach
    simp [hBodyLength] at hAttach
    exact hAttach.symm
  have hAfterFits :=
    TypedCfgCompilerFacts.Shape.sourceFrameFits_afterCall
      hSource hAfter hInputFits
  have hLength :
      stack.length =
        source.evm.stack.length - proc.argc + proc.retc := by
    rw [hStack, hSourceStack]
    simp [hArgsLength, hBodyLength]
    omega
  simpa [hLength] using hAfterFits

private theorem executes_call_cases
    {program : Structured.Program} {fuel : Nat}
    {name : Structured.Name} {proc : Structured.Proc}
    {source : RunState}
    {args callerStack : EvmYul.Stack Word}
    {transcript : Simulation.Interaction.Transcript}
    {sourceOutcome : Structured.Outcome}
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Stmt.openRun
          program (fuel + 1) (.call name) source)
        transcript (.ok sourceOutcome)) :
    (∃ bodyState frame returned stack,
        Simulation.Interaction.Executes
          (InteractionSemantics.Block.openRun program fuel proc.body
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc))
          transcript (.ok (.regular bodyState)) ∧
        bodyState.popReturn? = some (frame, returned) ∧
        Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
          some stack ∧
        sourceOutcome =
          .regular
            (returned.withEVM { bodyState.evm with stack := stack })) ∨
      (∃ bodyState frame returned stack,
        Simulation.Interaction.Executes
          (InteractionSemantics.Block.openRun program fuel proc.body
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc))
          transcript (.ok (.leave bodyState)) ∧
        bodyState.popReturn? = some (frame, returned) ∧
        Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
          some stack ∧
        sourceOutcome =
          .regular
            (returned.withEVM { bodyState.evm with stack := stack })) ∨
      ∃ bodyState kind,
        Simulation.Interaction.Executes
          (InteractionSemantics.Block.openRun program fuel proc.body
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc))
          transcript (.ok (.halt kind bodyState)) ∧
        sourceOutcome = .halt kind bodyState := by
  simp only [
    InteractionSemantics.Stmt.openRun,
    EffectSemantics.Control.Stmt.run,
    EffectSemantics.Ordinary.runStateModel_evm,
    EffectSemantics.Ordinary.runStateModel_withEVM,
    EffectSemantics.Ordinary.runStateModel_pushReturn,
    EffectSemantics.Ordinary.runStateModel_popReturn?,
    hLookup, hSplit] at hExec
  rcases
      Simulation.Interaction.Executes.bind_cases hExec with
    hError |
      ⟨bodyOutcome, bodyTranscript, restTranscript,
        hTranscript, hBodyExec, hRestExec⟩
  · rcases hError with ⟨err, hOutcome, _hBodyError⟩
    cases hOutcome
  · rcases bodyOutcome with ⟨bodyState, bodyMode⟩
    cases bodyMode with
    | regular =>
        cases hPop : bodyState.popReturn? with
        | none =>
            simp [hPop] at hRestExec
            cases hRestExec
        | some pair =>
            rcases pair with ⟨frame, returned⟩
            cases hAttach :
                Structured.StackFrame.attachReturns?
                  frame bodyState.evm.stack with
            | none =>
                simp [hPop, hAttach] at hRestExec
                cases hRestExec
            | some stack =>
                simp [
                  hPop, hAttach,
                  Simulation.Interaction.instMonad] at hRestExec
                cases hRestExec
                simp at hTranscript
                subst transcript
                exact
                  .inl
                    ⟨bodyState, frame, returned, stack,
                      hBodyExec, hPop, hAttach, rfl⟩
    | leave =>
        cases hPop : bodyState.popReturn? with
        | none =>
            simp [hPop] at hRestExec
            cases hRestExec
        | some pair =>
            rcases pair with ⟨frame, returned⟩
            cases hAttach :
                Structured.StackFrame.attachReturns?
                  frame bodyState.evm.stack with
            | none =>
                simp [hPop, hAttach] at hRestExec
                cases hRestExec
            | some stack =>
                simp [
                  hPop, hAttach,
                  Simulation.Interaction.instMonad] at hRestExec
                cases hRestExec
                simp at hTranscript
                subst transcript
                exact
                  .inr
                    (.inl
                      ⟨bodyState, frame, returned, stack,
                        hBodyExec, hPop, hAttach, rfl⟩)
    | brk =>
        cases hRestExec
    | cont =>
        cases hRestExec
    | halt kind =>
        cases hRestExec
        simp at hTranscript
        subst transcript
        exact
          .inr (.inr ⟨bodyState, kind, hBodyExec, rfl⟩)

private theorem sinkTopUnder_not_prim
    (depth : Nat) {instr : TypedCfg.Instr}
    (hMem : instr ∈ TypedCfgCompiler.sinkTopUnder depth)
    (op : Assembly.PrimOp) :
    instr ≠ .prim op := by
  induction depth with
  | zero =>
      simp [TypedCfgCompiler.sinkTopUnder] at hMem
  | succ depth ih =>
      simp only [TypedCfgCompiler.sinkTopUnder, List.mem_cons] at hMem
      rcases hMem with rfl | hRest
      · intro hEq
        cases hEq
      · exact ih hRest

private theorem openRunBody_callEntry_eq_pure
    {argc : Nat} {input output : TypedCfg.Shape}
    {token : Word} {target final : EVMState}
    (hRun :
      TypedCfg.Block.runBody
          (.returnToken token :: TypedCfgCompiler.sinkTopUnder argc)
          input target =
        .ok (final, output)) :
    TypedCfg.InteractionSemantics.Block.openRunBody
        (.returnToken token :: TypedCfgCompiler.sinkTopUnder argc)
        input target =
      Simulation.Interaction.pure (final, output) := by
  rw [
    TypedCfg.InteractionSemantics.Block.openRunBody_eq_done_of_forall_not_prim]
  · rw [hRun]
    rfl
  · intro instr hMem op hEq
    simp only [List.mem_cons] at hMem
    rcases hMem with hHead | hTail
    · exact TypedCfg.Instr.noConfusion (hHead.symm.trans hEq)
    · exact (sinkTopUnder_not_prim argc hTail op) hEq

/--
The compiler-generated call-site block is silent in the shared interaction
semantics and reaches the canonical procedure entry with the source call frame
realized by the generated return token.
-/
theorem openStep_entry_of_compileStmtFuel?
    {compilerFuel : Nat} {name : Structured.Name}
    {proc : Structured.Proc} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {source : RunState}
    {tokens : List Word} {target : EVMState}
    {args callerStack : EvmYul.Stack Word}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hProcWF : proc.WF) :
    ∃ targetFinal,
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (.jump (ProcLabel.entry name) targetFinal) ∧
      TypedCfgPreservation.StateRel
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Structured.Stmt.callToken supply :: tokens) targetFinal := by
  rcases
      TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
        hLookup hCompile with
    ⟨returnShape, output, hSource, hReturnShape, hType, rfl⟩
  rcases
      TypedCfgPreservation.CallStack.runBody_callEntry_preserves
        hRel hSplit hType hProcWF.1 with
    ⟨targetFinal, hRunBody, hFinalRel⟩
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body :=
        .returnToken (Structured.Stmt.callToken supply) ::
          TypedCfgCompiler.sinkTopUnder proc.argc
      output := output
      term := .jump (ProcLabel.entry name) }
  have hFind : cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  have hOpenBody :
      TypedCfg.InteractionSemantics.Block.openRunBody generated.body
          input target =
        Simulation.Interaction.pure (targetFinal, output) := by
    apply openRunBody_callEntry_eq_pure
    simpa [generated] using hRunBody
  refine ⟨targetFinal, ?_, hFinalRel⟩
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind,
    TypedCfg.Control.Block.run]
  change
    (do
      let result ←
        TypedCfg.InteractionSemantics.Block.openRunBody
          generated.body generated.input target
      if result.2 = generated.output then
        pure (TypedCfg.Block.runTerm
          generated.output generated.term result.1)
      else
        throw .InvalidInstruction) =
      Simulation.Interaction.pure
        (.jump (ProcLabel.entry name) targetFinal)
  rw [hOpenBody]
  simp [generated, TypedCfg.Block.runTerm]
  rfl

private theorem openStep_procEntry_of_adapter
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

private theorem prepend_call_route
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
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    {entry : Assembly.Label} {target targetAtEntry : EVMState}
    {tailFuel tailRemaining : Nat}
    {targetOutcome : TypedCfg.Outcome}
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
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg tailFuel fragment.entry targetAtEntry)
        transcript
        (.ok (.stopped tailRemaining targetOutcome))) :
    ∃ targetFuel,
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
          policy cfg targetFuel entry target)
        transcript
        (.ok (.stopped tailRemaining targetOutcome)) := by
  have hCallExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        []
        (.ok (.jump (ProcLabel.entry proc.name) targetAtEntry)) := by
    rw [hCall]
    exact
      Simulation.Interaction.Executes.done
        (.ok
          (TypedCfg.Outcome.jump
            (ProcLabel.entry proc.name) targetAtEntry))
  rcases fragment.route with hDirect | hAdapterRoute
  · rcases hDirect with ⟨hEntry, _hInput⟩
    have hTailAtProc :
        Simulation.Interaction.Executes
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            policy cfg tailFuel (ProcLabel.entry proc.name) targetAtEntry)
          transcript
          (.ok (.stopped tailRemaining targetOutcome)) := by
      simpa [hEntry] using hTail
    have hWhole :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
        hCallExec hProcEntryNoStop hTailAtProc
    exact ⟨tailFuel + 1, by simpa using hWhole⟩
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
          []
          (.ok (.jump fragment.entry targetAtEntry)) := by
      rw [hAdapter]
      exact
        Simulation.Interaction.Executes.done
          (.ok
            (TypedCfg.Outcome.jump fragment.entry targetAtEntry))
    have hRoute :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
        hAdapterExec hFragmentEntryNoStop hTail
    have hWhole :=
      InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
        hCallExec hProcEntryNoStop hRoute
    exact ⟨(tailFuel + 1) + 1, by simpa using hWhole⟩

private theorem body_leave_elim
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

private theorem body_halt_to_call
    {program : Structured.Program} {proc : Structured.Proc}
    {bodyResult result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label}
    {bodyReturns returns : List ReturnDest}
    {bodyTokens tokens : List Word}
    {source : RunState} {kind : Assembly.HaltKind}
    {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        bodyResult (procContext program proc)
        (ProcLabel.exit proc.name) bodyReturns bodyTokens
        (.halt kind source) target) :
    InteractionControlPreservation.OpenOutcome.Rel
      result ctx regular returns tokens
      (.halt kind source) target := by
  rcases hRel with ⟨hOutcome, _hFits, _hRestored⟩
  obtain ⟨targetState, targetFinal, rfl, hStep, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim hOutcome
  refine ⟨?_, trivial, trivial⟩
  exact
    TypedCfgPreservation.OutcomeSimulation.Rel.halt_iff.mpr
      ⟨rfl, targetFinal, hStep, hStateRel⟩

/--
The canonical generated procedure-entry adapter is also silent in the shared
interaction semantics. Direct entries take zero target steps; relabel adapters
take exactly one.
-/
theorem openRunNResult_procEntry
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
    (state : EVMState) :
    ∃ fuel,
      TypedCfg.InteractionSemantics.Program.openRunN
          cfg fuel (ProcLabel.entry proc.name) state =
        Simulation.Interaction.pure
          (.jump fragment.entry state) := by
  rcases fragment.route with hDirect | hAdapterRoute
  · rcases hDirect with ⟨hEntry, _hInput⟩
    refine ⟨0, ?_⟩
    rw [hEntry]
    rfl
  · rcases hAdapterRoute with
      ⟨adapter, hEntry, _hInput, _hFrame,
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
        refine ⟨1, ?_⟩
        rw [TypedCfg.InteractionSemantics.Program.openRunN_one]
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

/--
The generated procedure-exit block is silent in the shared interaction
semantics. It selects the registered call site, removes the compiler return
token, and restores the source caller state.
-/
theorem openStep_dispatch
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {site : TypedCfgCompiler.DispatchSite}
    {bodyState returned : RunState} {frame : ReturnDest}
    {stack : EvmYul.Stack Word} {tokens : List Word}
    {target : EVMState}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hSiteProc : site.procName = proc.name)
    (hSiteMem : site ∈ context.calls)
    (hRel :
      TypedCfgPreservation.StateRel
        bodyState (site.token :: tokens) target)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hRetc : frame.retc = proc.retc) :
    ∃ targetFinal,
      TypedCfg.InteractionSemantics.Program.openStep
          cfg (ProcLabel.exit proc.name) target =
        Simulation.Interaction.pure
          (.jump site.returnLabel targetFinal) ∧
      TypedCfgPreservation.StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        tokens targetFinal := by
  rcases
      TypedCfgPreservation.CallStack.eraseReturnToken_preserves
        hRel hPop hAttach with
    ⟨hToken, hFinalRel⟩
  have hFind :
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
        simp [hSites, TypedCfg.Block.ReturnSite.findTarget?] at hFind
    | cons head rest =>
        rfl
  have hBlock := context.dispatchBlock hLookup
  let targetFinal : EVMState :=
    { target with stack := target.stack.eraseIdx proc.retc }
  have hTarget :
      TypedCfg.InteractionSemantics.Program.openStep
          cfg (ProcLabel.exit proc.name) target =
        Simulation.Interaction.pure
          (.jump site.returnLabel targetFinal) := by
    rw [hRetc] at hToken hFinalRel
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hBlock,
      TypedCfg.Control.Block.run]
    change
      (do
        let result ←
          TypedCfg.InteractionSemantics.Block.openRunBody
            [] (TypedCfgCompiler.Shape.procExit proc) target
        if result.2 = TypedCfgCompiler.Shape.procExit proc then
          pure
            (TypedCfg.Block.runTerm
              (TypedCfgCompiler.Shape.procExit proc)
              (if
                (TypedCfgCompiler.returnSitesFor
                    proc.name context.calls).isEmpty
               then .invalid
               else
                 .returnDispatch proc.retc
                   (TypedCfgCompiler.returnSitesFor
                     proc.name context.calls))
              result.1)
        else
          throw .InvalidInstruction) =
        Simulation.Interaction.pure
          (.jump site.returnLabel targetFinal)
    simp [
      TypedCfg.InteractionSemantics.Block.openRunBody,
      TypedCfg.Control.Block.runBody, hSitesNonempty,
      TypedCfg.Block.runTerm,
      TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit,
      hToken, hFind, targetFinal,
      Simulation.Interaction.instMonad,
      Simulation.Interaction.bind,
      Simulation.Interaction.pure]
  refine ⟨targetFinal, hTarget, ?_⟩
  rw [hRetc] at hFinalRel
  exact hFinalRel

/--
Execution-indexed preservation for one compiled internal procedure call.

The recursive procedure body is supplied by the adjacent block owner. This
theorem owns only call-site routing, the optional entry adapter, generated
return dispatch, and conversion of regular/leave body outcomes into the
caller's regular continuation.
-/
theorem openRun_call_exec_under
    {compilerFuel sourceFuel : Nat}
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
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hProcs : ctx.procs = sourceProgram.procs)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hInputFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hProcWF : proc.WF)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hProcEntryNoStop :
      ∀ {args callerStack : EvmYul.Stack Word}
          {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) →
          TypedCfgPreservation.StateRel
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens) targetState →
          policy (ProcLabel.entry proc.name) targetState = false)
    (hFragmentEntryNoStop :
      ∀ {args callerStack : EvmYul.Stack Word}
          {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) →
          TypedCfgPreservation.StateRel
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens) targetState →
          policy fragment.entry targetState = false)
    (hProcExitNoStop :
      ∀ {args callerStack : EvmYul.Stack Word}
          {bodyState : RunState} {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) →
          TypedCfgPreservation.StateRel bodyState
            (Structured.Stmt.callToken supply :: tokens) targetState →
          TypedCfgCompiler.Shape.SourceFrameFits
            (TypedCfgCompiler.Shape.procExit proc)
            bodyState.evm.stack.length →
          bodyState.returns =
            (((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc).returns) →
          policy (ProcLabel.exit proc.name) targetState = false)
    (hBody :
      ∀ {args callerStack : EvmYul.Stack Word},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) →
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
            fragment.result cfg fragment.entry
            (procContext sourceProgram proc)
            (ProcLabel.exit proc.name)
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceFuel proc.body
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc))
            (bodyStopPolicy fragment.result sourceProgram proc
              (((source.withEVM
                  { source.evm with stack := args }).pushReturn
                    callerStack proc.retc).returns)
              (Structured.Stmt.callToken supply :: tokens) policy)) :
    InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.call name) source)
      policy := by
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
  have hName :
      proc.name = name :=
    Structured.ProcList.name_of_lookup? hLookup
  intro target hStateRel transcript sourceOutcome hSourceExec
  cases hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack with
  | none =>
      simp only [
        InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run,
        EffectSemantics.Ordinary.runStateModel_evm,
        hLookup, hSplit] at hSourceExec
      cases hSourceExec
  | some split =>
      rcases split with ⟨args, callerStack⟩
      let callSource : RunState :=
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack proc.retc)
      have hCallBody :=
        hBody (args := args) (callerStack := callerStack) hSplit
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
            (Structured.Stmt.callToken supply :: tokens)
            targetAtEntry := by
        simpa [callSource] using hCallStateRel
      rcases
          executes_call_cases hLookup hSplit hSourceExec with
        hRegular | hLeaveOrHalt
      · rcases hRegular with
          ⟨bodyState, frame, returned, stack,
            hBodyExec, hPop, hAttach, hSourceOutcome⟩
        subst sourceOutcome
        obtain
            ⟨bodyFuel, bodyRemaining, targetBodyOutcome,
              hTargetBodyExec, hBodyRelRaw⟩ :=
          hCallBody targetAtEntry hCallStateRel'
            transcript (.regular bodyState) hBodyExec
        have hBodyRel :
            InteractionControlPreservation.OpenOutcome.Rel
              fragment.result (procContext sourceProgram proc)
              (ProcLabel.exit proc.name) callSource.returns
              (Structured.Stmt.callToken supply :: tokens)
              (.regular bodyState) targetBodyOutcome := by
          simpa [callSource] using hBodyRelRaw
        obtain
            ⟨targetAtExit, rfl, hBodyStateRel,
              hBodyFits, hBodyReturns⟩ :=
          InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
            fragment.fallthrough hBodyRel
        obtain ⟨hFrameEq, hReturnedReturns⟩ :=
          popReturn_eq_of_returns_eq
            (source := source.withEVM
              { source.evm with stack := args })
            (by simpa [callSource] using hBodyReturns) hPop
        have hFinalFits :
            TypedCfgCompiler.Shape.SourceFrameFits
              returnShape stack.length :=
          finalFrameFits hSource hAfter hInputFits hSplit hBodyFits
            hFrameEq hAttach
        have hSiteProc : site.procName = proc.name := by
          simp [site, hName]
        have hRetc : frame.retc = proc.retc := by
          simp [hFrameEq]
        rcases
            openStep_dispatch generated hLookup hSiteProc hSiteMem
              hBodyStateRel hPop hAttach hRetc with
          ⟨targetFinal, hDispatch, hFinalStateRel⟩
        have hWholeRel :
            InteractionControlPreservation.OpenOutcome.Rel
              { blocks :=
                  [{ label := entry
                     input := input
                     body :=
                       .returnToken (Structured.Stmt.callToken supply) ::
                         TypedCfgCompiler.sinkTopUnder proc.argc
                     output := output
                     term := .jump (ProcLabel.entry name) }]
                next := supply + 1
                calls := [site]
                fallthrough? := some returnShape }
              ctx regular source.returns tokens
              (.regular
                (returned.withEVM
                  { bodyState.evm with stack := stack }))
              (.jump regular targetFinal) := by
          refine ⟨?_, ?_, ?_⟩
          · exact
              TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                ⟨rfl, hFinalStateRel⟩
          · exact ⟨returnShape, rfl, hFinalFits⟩
          · simpa [
              InteractionControlPreservation.OpenOutcome.ActivationRestored]
              using hReturnedReturns
        have hFinalStop := hStops hWholeRel
        have hDispatchExec :
            Simulation.Interaction.Executes
              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                policy cfg 1 (ProcLabel.exit proc.name) targetAtExit)
              []
              (.ok (.stopped 0 (.jump regular targetFinal))) := by
          change policy regular targetFinal = true at hFinalStop
          rw [
            TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind,
            hDispatch]
          simpa [
            site,
            Simulation.Interaction.instMonad,
            Simulation.Interaction.bind,
            Simulation.Interaction.pure,
            TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
            hFinalStop] using
            (Simulation.Interaction.Executes.done
              (.ok
                (TypedCfg.Control.Program.RunResult.stopped 0
                  (TypedCfg.Outcome.jump regular targetFinal))))
        have hBodyAndDispatch :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
            (outer := policy)
            (inner :=
              bodyStopPolicy fragment.result sourceProgram proc
                callSource.returns
                (Structured.Stmt.callToken supply :: tokens) policy)
            (hRefines := by
              intro label state hStop
              simp [
                bodyStopPolicy,
                InteractionControlPreservation.OpenOutcome.pushStopJump,
                hStop])
            hTargetBodyExec
            (hProcExitNoStop hSplit hBodyStateRel hBodyFits
              (by simpa [callSource] using hBodyReturns))
            hDispatchExec
        obtain ⟨targetFuel, hTargetExec⟩ :=
          prepend_call_route (fragment := fragment) generated hCallStep'
            (hProcEntryNoStop hSplit hCallStateRel')
            (hFragmentEntryNoStop hSplit hCallStateRel')
            hBodyAndDispatch
        exact
          ⟨targetFuel, bodyRemaining, .jump regular targetFinal,
            by simpa using hTargetExec, hWholeRel⟩
      · rcases hLeaveOrHalt with hLeave | hHalt
        · rcases hLeave with
            ⟨bodyState, frame, returned, stack,
              hBodyExec, hPop, hAttach, hSourceOutcome⟩
          subst sourceOutcome
          obtain
              ⟨bodyFuel, bodyRemaining, targetBodyOutcome,
                hTargetBodyExec, hBodyRelRaw⟩ :=
            hCallBody targetAtEntry hCallStateRel'
              transcript (.leave bodyState) hBodyExec
          have hBodyRel :
              InteractionControlPreservation.OpenOutcome.Rel
                fragment.result (procContext sourceProgram proc)
                (ProcLabel.exit proc.name) callSource.returns
                (Structured.Stmt.callToken supply :: tokens)
                (.leave bodyState) targetBodyOutcome := by
            simpa [callSource] using hBodyRelRaw
          obtain
              ⟨targetAtExit, rfl, hBodyStateRel,
                hBodyFits, hBodyReturns⟩ :=
            body_leave_elim hBodyRel
          obtain ⟨hFrameEq, hReturnedReturns⟩ :=
            popReturn_eq_of_returns_eq
              (source := source.withEVM
                { source.evm with stack := args })
              (by simpa [callSource] using hBodyReturns) hPop
          have hFinalFits :
              TypedCfgCompiler.Shape.SourceFrameFits
                returnShape stack.length :=
            finalFrameFits hSource hAfter hInputFits hSplit hBodyFits
              hFrameEq hAttach
          have hSiteProc : site.procName = proc.name := by
            simp [site, hName]
          have hRetc : frame.retc = proc.retc := by
            simp [hFrameEq]
          rcases
              openStep_dispatch generated hLookup hSiteProc hSiteMem
                hBodyStateRel hPop hAttach hRetc with
            ⟨targetFinal, hDispatch, hFinalStateRel⟩
          have hWholeRel :
              InteractionControlPreservation.OpenOutcome.Rel
                { blocks :=
                    [{ label := entry
                       input := input
                       body :=
                         .returnToken (Structured.Stmt.callToken supply) ::
                           TypedCfgCompiler.sinkTopUnder proc.argc
                       output := output
                       term := .jump (ProcLabel.entry name) }]
                  next := supply + 1
                  calls := [site]
                  fallthrough? := some returnShape }
                ctx regular source.returns tokens
                (.regular
                  (returned.withEVM
                    { bodyState.evm with stack := stack }))
                (.jump regular targetFinal) := by
            refine ⟨?_, ?_, ?_⟩
            · exact
                TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                  ⟨rfl, hFinalStateRel⟩
            · exact ⟨returnShape, rfl, hFinalFits⟩
            · simpa [
                InteractionControlPreservation.OpenOutcome.ActivationRestored]
                using hReturnedReturns
          have hFinalStop := hStops hWholeRel
          have hDispatchExec :
              Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                  policy cfg 1 (ProcLabel.exit proc.name) targetAtExit)
                []
                (.ok (.stopped 0 (.jump regular targetFinal))) := by
            change policy regular targetFinal = true at hFinalStop
            rw [
              TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind,
              hDispatch]
            simpa [
              site,
              Simulation.Interaction.instMonad,
              Simulation.Interaction.bind,
              Simulation.Interaction.pure,
              TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
              hFinalStop] using
              (Simulation.Interaction.Executes.done
                (.ok
                  (TypedCfg.Control.Program.RunResult.stopped 0
                    (TypedCfg.Outcome.jump regular targetFinal))))
          have hBodyAndDispatch :=
            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
              (outer := policy)
              (inner :=
                bodyStopPolicy fragment.result sourceProgram proc
                  callSource.returns
                  (Structured.Stmt.callToken supply :: tokens) policy)
              (hRefines := by
                intro label state hStop
                simp [
                  bodyStopPolicy,
                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                  hStop])
              hTargetBodyExec
              (hProcExitNoStop hSplit hBodyStateRel hBodyFits
                (by simpa [callSource] using hBodyReturns))
              hDispatchExec
          obtain ⟨targetFuel, hTargetExec⟩ :=
            prepend_call_route (fragment := fragment) generated hCallStep'
              (hProcEntryNoStop hSplit hCallStateRel')
              (hFragmentEntryNoStop hSplit hCallStateRel')
              hBodyAndDispatch
          exact
            ⟨targetFuel, bodyRemaining, .jump regular targetFinal,
              by simpa using hTargetExec, hWholeRel⟩
        · rcases hHalt with
            ⟨bodyState, kind, hBodyExec, hSourceOutcome⟩
          subst sourceOutcome
          obtain
              ⟨bodyFuel, bodyRemaining, targetBodyOutcome,
                hTargetBodyExec, hBodyRelRaw⟩ :=
            hCallBody targetAtEntry hCallStateRel'
              transcript (.halt kind bodyState) hBodyExec
          have hBodyRel :
              InteractionControlPreservation.OpenOutcome.Rel
                fragment.result (procContext sourceProgram proc)
                (ProcLabel.exit proc.name) callSource.returns
                (Structured.Stmt.callToken supply :: tokens)
                (.halt kind bodyState) targetBodyOutcome := by
            simpa [callSource] using hBodyRelRaw
          have hWholeRel :
              InteractionControlPreservation.OpenOutcome.Rel
                { blocks :=
                    [{ label := entry
                       input := input
                       body :=
                         .returnToken (Structured.Stmt.callToken supply) ::
                           TypedCfgCompiler.sinkTopUnder proc.argc
                       output := output
                       term := .jump (ProcLabel.entry name) }]
                  next := supply + 1
                  calls := [site]
                  fallthrough? := some returnShape }
                ctx regular source.returns tokens
                (.halt kind bodyState) targetBodyOutcome :=
            body_halt_to_call hBodyRel
          have hTargetBodyOuter :=
            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
              (outer := policy)
              (inner :=
                bodyStopPolicy fragment.result sourceProgram proc
                  callSource.returns
                  (Structured.Stmt.callToken supply :: tokens) policy)
              (hRefines := by
                intro label state hStop
                simp [
                  bodyStopPolicy,
                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                  hStop])
              hTargetBodyExec (hStops hWholeRel)
          obtain ⟨targetFuel, hTargetExec⟩ :=
            prepend_call_route (fragment := fragment) generated hCallStep'
              (hProcEntryNoStop hSplit hCallStateRel')
              (hFragmentEntryNoStop hSplit hCallStateRel')
              hTargetBodyOuter
          exact
            ⟨targetFuel, bodyRemaining, targetBodyOutcome,
              hTargetExec, hWholeRel⟩

/--
Compiler-facing internal-call preservation.

The generated whole-program context selects the callee fragment and exposes
only its adjacent block/call ownership facts to the recursive block owner.
-/
theorem openRun_call_exec_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply}
    {entry regular : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hProcs : ctx.procs = sourceProgram.procs)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hInputFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hProcWF : proc.WF)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hProcEntryNoStop :
      ∀ {args callerStack : EvmYul.Stack Word}
          {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) →
          TypedCfgPreservation.StateRel
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens) targetState →
          policy (ProcLabel.entry proc.name) targetState = false)
    (hProcExitNoStop :
      ∀ {args callerStack : EvmYul.Stack Word}
          {bodyState : RunState} {targetState : EVMState},
        Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
            some (args, callerStack) →
          TypedCfgPreservation.StateRel bodyState
            (Structured.Stmt.callToken supply :: tokens) targetState →
          TypedCfgCompiler.Shape.SourceFrameFits
            (TypedCfgCompiler.Shape.procExit proc)
            bodyState.evm.stack.length →
          bodyState.returns =
            (((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc).returns) →
          policy (ProcLabel.exit proc.name) targetState = false)
    (hFragmentEntryNoStop :
      ∀ (fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes sourceProgram.procs proc
            generated.procBlocks generated.procCalls),
        ∀ {args callerStack : EvmYul.Stack Word}
            {targetState : EVMState},
          Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
              some (args, callerStack) →
            TypedCfgPreservation.StateRel
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc)
              (Structured.Stmt.callToken supply :: tokens) targetState →
            policy fragment.entry targetState = false)
    (hBody :
      ∀ (fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes sourceProgram.procs proc
            generated.procBlocks generated.procCalls),
        TypedCfgPreservation.BlocksInProgram fragment.result cfg →
        TypedCfgPreservation.CallsInProgram
            fragment.result generated.calls →
        ∀ {args callerStack : EvmYul.Stack Word},
          Structured.StackFrame.splitArgs?
              proc.argc source.evm.stack =
            some (args, callerStack) →
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
            fragment.result cfg fragment.entry
            (procContext sourceProgram proc)
            (ProcLabel.exit proc.name)
            ((source.withEVM { source.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Structured.Stmt.callToken supply :: tokens)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceFuel proc.body
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc))
            (bodyStopPolicy fragment.result sourceProgram proc
              (((source.withEVM
                  { source.evm with stack := args }).pushReturn
                    callerStack proc.retc).returns)
              (Structured.Stmt.callToken supply :: tokens) policy)) :
    InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.call name) source)
      policy := by
  rcases generated.procFragment_of_lookup? hLookup with
    ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
  exact
    openRun_call_exec_under generated fragment hLookup hProcs
      hCompile hBlocks hResultCalls hInputFits hProcWF hStops
      hProcEntryNoStop (hFragmentEntryNoStop fragment) hProcExitNoStop
      (hBody fragment hFragmentBlocks hFragmentCalls)

end Call

end InteractionCallPreservation
end Structured
end EvmCompiler
