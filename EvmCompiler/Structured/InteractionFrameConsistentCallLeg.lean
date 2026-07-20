import EvmCompiler.Structured.InteractionFrameConsistentDispatchLeg

/-!
# Strengthened (`realizedWitnessFC`) `hInv` leg — the callHead (push) arm (session 46)

Session 46 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-45 frontier item 1).

The `callHead` disjunct is the only leg that PUSHES a ghost return frame: the compiled call-site
block jumps to the callee entry after recording a return frame `{ callerStack := caller stack,
retc := callee.retc }` under the fresh return token `callToken supply`.  The strengthened
successor therefore needs its child `FrameConsistent` to carry ONE MORE head — the pushed
frame's `FrameHeadConsistent` — atop the (transported) entry tail.

This module banks `realizedWitnessFC_of_callHead_dispatch`, which ESTABLISHES the pushed frame's
head consistency from:

* the call's own registered dispatch site `S = { procName := name, token := callToken supply,
  returnLabel := regular, … }` (`components_of_compileStmtFuel?_call`), in `context.calls` via
  `hResultCalls`;
* token uniqueness (`context.tokensUnique` + `List.inj_on_of_nodup_map`) to pin ANY site sharing
  the fresh token to `S` — so the frame's `retc = proc.retc` and its return continuation is
  `regular`;
* the caller-continuation shape `LabelShape cfg regular returnShape` (`hReg`, the same enriched
  regular field `codeHead`/`ifHead` carry) and the restored-frame fit
  (`sourceFrameFits_afterCall`).

Then `FrameConsistent.cons` prepends it to the entry tail and the bare call machinery lands the
strengthened callee-entry witness.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**`callHead` disjunct strengthened `hInv` leg.**  Establishes the pushed return frame's
`FrameHeadConsistent` (via the call's own site + token uniqueness + the caller-continuation
`hReg`) and prepends it to the transported entry tail (`FrameConsistent.cons`), then lands the
strengthened callee-entry witness through the bare call machinery. -/
theorem realizedWitnessFC_of_callHead_dispatch
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext sourceProgram entryShapes cfg)
    {compilerFuel : Nat} {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular next : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hProcs : ctx.procs = sourceProgram.procs)
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls : TypedCfgPreservation.CallsInProgram result context.calls)
    (hEntryShape :
      TypedCfgPreservation.LabelShape cfg (ProcLabel.entry name)
        (TypedCfgCompiler.Shape.procEntry proc))
    (hProcWF : proc.WF)
    (hReg :
      ∀ out, result.fallthrough? = some out →
        TypedCfgPreservation.LabelShape cfg regular out)
    (hReal : realizedWitnessFC sourceProgram cfg context.calls entry target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg context.calls next state' := by
  obtain ⟨returnShape, output, hSource, hReturnShape, hType, hResultEq⟩ :=
    TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call hLookup hCompile
  have hFall : result.fallthrough? = some returnShape := by rw [hResultEq]
  -- The call block, found in the cfg; unify with the entry witness block.
  have hCallMem :
      ({ label := entry
         input := input
         body :=
           .returnToken (Structured.Stmt.callToken supply) ::
             TypedCfgCompiler.sinkTopUnder proc.argc
         output := output
         term := .jump (ProcLabel.entry name) } : TypedCfg.Block) ∈ result.blocks := by
    rw [hResultEq]; simp
  have hFindCall :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body :=
              .returnToken (Structured.Stmt.callToken supply) ::
                TypedCfgCompiler.sinkTopUnder proc.argc
            output := output
            term := .jump (ProcLabel.entry name) } :=
    hBlocks _ hCallMem
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits0, hFC⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := input
          body :=
            .returnToken (Structured.Stmt.callToken supply) ::
              TypedCfgCompiler.sinkTopUnder proc.argc
          output := output
          term := .jump (ProcLabel.entry name) } :=
    Option.some.inj (hFindReal.symm.trans hFindCall)
  subst hBlockEq
  have hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length := hFits0
  -- Argument split.
  have hArgBound : proc.argc ≤ TypedCfgCompiler.Shape.sourceLength input :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
  have hStackBound : proc.argc ≤ source.evm.stack.length :=
    Nat.le_trans hArgBound hFits.1
  have hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (source.evm.stack.take proc.argc, source.evm.stack.drop proc.argc) := by
    simp [Structured.StackFrame.splitArgs?, hStackBound]
  have hStk :
      ((source.withEVM
            { source.evm with stack := source.evm.stack.take proc.argc }).pushReturn
          (source.evm.stack.drop proc.argc) proc.retc).evm.stack =
        source.evm.stack.take proc.argc := by
    simp [RunState.pushReturn, RunState.withEVM]
  have hFitsChild :
      TypedCfgCompiler.Shape.SourceFrameFits
        (TypedCfgCompiler.Shape.procEntry proc)
        ((source.withEVM
            { source.evm with stack := source.evm.stack.take proc.argc }).pushReturn
          (source.evm.stack.drop proc.argc) proc.retc).evm.stack.length := by
    rw [hStk]
    exact TypedCfgPreservation.SourceFrameFits.procEntry_of_splitArgs hSplit
  -- The call's own registered dispatch site.
  set S : TypedCfgCompiler.DispatchSite :=
    { procName := name
      token := Structured.Stmt.callToken supply
      returnLabel := regular
      caseLabel := .generated supply 10000 } with hSdef
  have hSMem : S ∈ context.calls := by
    apply hResultCalls
    rw [hResultEq]; simp [hSdef]
  -- Establish the pushed frame's head consistency.
  have hPushHead :
      FrameHeadConsistent sourceProgram cfg context.calls
        { callerStack := source.evm.stack.drop proc.argc, retc := proc.retc }
        (Structured.Stmt.callToken supply) := by
    intro site' proc' hSite'Mem hTok' hLookup'
    have hSiteEq : S = site' :=
      List.inj_on_of_nodup_map context.tokensUnique hSMem hSite'Mem
        (by rw [hSdef]; exact hTok'.symm)
    have hProc' : proc' = proc := by
      have : Structured.ProcList.lookup? name sourceProgram.procs = some proc := by
        rw [← hProcs]; exact hLookup
      have hSite'Name : site'.procName = name := by rw [← hSiteEq, hSdef]
      rw [hSite'Name, this] at hLookup'
      exact (Option.some.inj hLookup').symm
    refine ⟨by rw [hProc'], returnShape, ?_, ?_⟩
    · have hSite'Ret : site'.returnLabel = regular := by rw [← hSiteEq, hSdef]
      rw [hSite'Ret]
      exact hReg returnShape hFall
    · -- restored caller frame fits `returnShape` at `retc + callerStack.length`
      have hFit :=
        TypedCfgCompilerFacts.Shape.sourceFrameFits_afterCall
          hSource hReturnShape hFits
      simp only [List.length_drop]
      rw [Nat.add_comm proc.retc (source.evm.stack.length - proc.argc)]
      exact hFit
  -- Land the child witness through the bare call machinery, threading the strengthened FC.
  obtain ⟨targetFinal, hStep, hChildRel⟩ :=
    InteractionCallPreservation.Call.openStep_entry_of_compileStmtFuel?
      hLookup hCompile hBlocks hStateRel hSplit hProcWF
  refine realizedWitnessFC_of_pure_jump hStep hChildRel hExec hEntryShape hFitsChild ?_
  -- child `FrameConsistent`: pushed head prepended to the transported entry tail
  show
    FrameConsistent sourceProgram cfg context.calls
      ((source.withEVM
          { source.evm with stack := source.evm.stack.take proc.argc }).pushReturn
        (source.evm.stack.drop proc.argc) proc.retc).returns
      (Structured.Stmt.callToken supply :: tokens)
  have hReturnsEq :
      ((source.withEVM
            { source.evm with stack := source.evm.stack.take proc.argc }).pushReturn
          (source.evm.stack.drop proc.argc) proc.retc).returns =
        { callerStack := source.evm.stack.drop proc.argc, retc := proc.retc } ::
          source.returns := by
    simp [RunState.pushReturn, RunState.withEVM]
  rw [hReturnsEq]
  exact FrameConsistent.cons hPushHead hFC

end InteractionFrameConsistent
end Structured
end EvmCompiler
