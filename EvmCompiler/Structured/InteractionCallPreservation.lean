import EvmCompiler.Structured.InteractionLoopPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionCallPreservation

namespace Call

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

end Call

end InteractionCallPreservation
end Structured
end EvmCompiler
