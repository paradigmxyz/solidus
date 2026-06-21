import EvmCompiler.Functions.AllocationLayoutLowering
import EvmCompiler.Functions.StackLowering
import EvmCompiler.Locals.Compiler

/-!
Adjacent executable bridge from stack-scheduled Functions lowering to the
ordinary Locals compiler.  Semantic preservation remains owned by the
Functions-to-Locals proof boundary; this module contains no observer semantics
and does not bypass the existing Locals compiler.
-/

namespace EvmCompiler
namespace Functions
namespace StackLoweringCompilation

open AllocationLiveness

structure BlockArtifact
    (sourceCtx : StackLowering.Ctx) (demand : Demand)
    (pinned : LiveSet) (initial : Locals.Ctx) (source : Block) where
  facts : AllocationLivenessFacts.Region
  schedule : StackSchedule.Region
  locals : Locals.Block
  code : List Expressions.Stmt
  finalCtx : Locals.Ctx
  factsEq :
    AllocationLivenessFacts.annotateBlock? demand source = some facts
  scheduleEq :
    StackSchedule.scheduleBlock? pinned initial.layout source facts =
      some schedule
  lowerEq :
    StackLowering.lowerScheduledBlock? sourceCtx source schedule =
      some locals
  compileEq :
    Locals.Block.compileOpen initial locals = some (code, finalCtx)
  finalLayout : finalCtx.layout = schedule.finalLayout

def compileBlock?
    (sourceCtx : StackLowering.Ctx) (demand : Demand)
    (pinned : LiveSet) (initial : Locals.Ctx) (source : Block) :
    Option (BlockArtifact sourceCtx demand pinned initial source) :=
  match hFacts : AllocationLivenessFacts.annotateBlock? demand source with
  | none => none
  | some facts =>
      match hSchedule :
          StackSchedule.scheduleBlock? pinned initial.layout source facts with
      | none => none
      | some schedule =>
          match hLower :
              StackLowering.lowerScheduledBlock? sourceCtx source schedule with
          | none => none
          | some locals =>
              match hCompile : Locals.Block.compileOpen initial locals with
              | none => none
              | some (code, finalCtx) =>
                  if hFinal : finalCtx.layout = schedule.finalLayout then
                    some
                      { facts
                        schedule
                        locals
                        code
                        finalCtx
                        factsEq := hFacts
                        scheduleEq := hSchedule
                        lowerEq := hLower
                        compileEq := hCompile
                        finalLayout := hFinal }
                  else
                    none

theorem compileBlock?_sound
    {sourceCtx : StackLowering.Ctx} {demand : Demand}
    {pinned : LiveSet} {initial : Locals.Ctx} {source : Block}
    {artifact : BlockArtifact sourceCtx demand pinned initial source}
    (hCompile :
      compileBlock? sourceCtx demand pinned initial source = some artifact) :
    Locals.Block.compileOpen initial artifact.locals =
        some (artifact.code, artifact.finalCtx) ∧
      artifact.finalCtx.layout = artifact.schedule.finalLayout := by
  exact ⟨artifact.compileEq, artifact.finalLayout⟩

/-- The ordinary Locals compiler realizes the return-initialization prelude's
canonical layout without changing any enclosing control destination. -/
theorem initReturns_compileOpen_final
    {names : List Name} {ctx final : Locals.Ctx}
    {code : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen ctx { stmts := Lower.initReturns names } =
        some (code, final)) :
    final = ctx.withLayout (names.reverse ++ ctx.layout) := by
  induction names generalizing ctx code final with
  | nil =>
      simp [Lower.initReturns, Locals.Block.compileOpen] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      cases ctx
      rfl
  | cons name rest ih =>
      obtain ⟨headCode, middle, tailCode, hHead, hTail, _hCode⟩ :=
        Locals.Block.compileOpen_cons_components hCompile
      cases hValue : Locals.Expr.compileCode ctx 0 (.lit Lower.zero) with
      | none =>
          simp [Locals.Stmt.compile, hValue] at hHead
      | some valueCode =>
          simp [Locals.Stmt.compile, hValue] at hHead
          rcases hHead with ⟨rfl, rfl⟩
          have hFinal := ih hTail
          simpa [Locals.Ctx.withLayout, List.reverse_cons,
            List.append_assoc] using hFinal

/-- Successful stack lowering and ordinary Locals procedure compilation expose
the exact adjacent phases consumed by function-call preservation. No generated
code or layout is accepted as a theorem premise. -/
def returnCodeStmts : Option Structured.Code → List Expressions.Stmt
  | none => []
  | some code => [.code code]

theorem lowerFunction?_toExpressions?_components
    {functions : List FunDef} {fn : FunDef} {proc : Locals.Proc}
    {lowerProc : Expressions.Proc}
    (hLower : StackLowering.lowerFunction? functions fn = some proc)
    (hCompile : proc.toExpressions? = some lowerProc) :
    ∃ facts schedule localsBody,
    ∃ targetBody : Expressions.Block,
    ∃ finalCtx returnPreludeCode,
    ∃ returnCode? : Option Structured.Code,
    ∃ cleanup,
      AllocationLivenessFacts.annotateBlock?
          (StackLowering.functionDemand fn) fn.body = some facts ∧
      StackSchedule.scheduleBlock? ∅
          (StackLowering.functionBodyLayout fn) fn.body facts =
        some schedule ∧
      StackLowering.lowerScheduledBlock?
          { functions, returns := fn.returns } fn.body schedule =
        some localsBody ∧
      StackAccess.ExprSeq.check? schedule.finalLayout 0
          (StackLowering.returnWords fn.returns) = some () ∧
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length) ∧
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            (StackLowering.functionBodyLayout fn) fn.returns.length)
          localsBody = some (targetBody.stmts, finalCtx) ∧
      (match returnCode? with
        | none => fn.returns = []
        | some returnCode =>
            Locals.ExprSeq.compileCode finalCtx 0
                (StackLowering.returnWords fn.returns) = some returnCode) ∧
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup ∧
      lowerProc =
        { name := fn.name
          argc := fn.params.length
          retc := fn.returns.length
          body :=
            { stmts :=
                [.code [.bindLocals 0 fn.params.reverse]] ++
                  (returnPreludeCode ++
                    (targetBody.stmts ++
                      (returnCodeStmts returnCode? ++ [.code cleanup]))) } } := by
  obtain ⟨facts, schedule, localsBody, hFacts, hSchedule, hBody,
      hAccess, hProc⟩ :=
    StackLowering.lowerFunction?_components hLower
  obtain ⟨compiledBody, hPreserving, hLowerProc⟩ :=
    Locals.Proc.toExpressions?_components hCompile
  obtain ⟨fullCode, procFinalCtx, hOpen, hFinish⟩ :=
    Locals.Block.compileToPreserving_components hPreserving
  have hOpen' :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts :=
              [Lower.bindEntryLayout fn.params.reverse] ++
                (Lower.initReturns fn.returns ++
                  (localsBody.stmts ++
                    StackLowering.pushWordReturns fn.returns)) } =
        some (fullCode, procFinalCtx) := by
    rw [hProc] at hOpen
    simpa [List.append_assoc] using hOpen
  have hFinish' :
      Locals.finishToPreserving procFinalCtx fn.returns.length 0 fullCode =
        some compiledBody := by
    rw [hProc] at hFinish
    simpa using hFinish
  have hLowerProc' :
      lowerProc =
        { name := fn.name
          argc := fn.params.length
          retc := fn.returns.length
          body := compiledBody } := by
    rw [hProc] at hLowerProc
    simpa using hLowerProc
  obtain ⟨markerCode, afterMarker, restCode, hMarker, hRest, hFullCode⟩ :=
    Locals.Block.compileOpen_append_components hOpen'
  have hMarkerExpected :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := [Lower.bindEntryLayout fn.params.reverse] } =
        some
          ([.code [.bindLocals 0 fn.params.reverse]],
            Locals.Ctx.procEntryWithLayoutAndRetc
              fn.params.reverse fn.returns.length) := by
    simp [Lower.bindEntryLayout, Locals.Block.compileOpen,
      Locals.Stmt.compile, Locals.Expr.compileCode, Locals.codeStmt]
  have hMarkerPair := Option.some.inj (hMarkerExpected.symm.trans hMarker)
  have hMarkerCode :
      markerCode = [.code [.bindLocals 0 fn.params.reverse]] :=
    (congrArg Prod.fst hMarkerPair).symm
  have hAfterMarker :
      afterMarker =
        Locals.Ctx.procEntryWithLayoutAndRetc
          fn.params.reverse fn.returns.length :=
    (congrArg Prod.snd hMarkerPair).symm
  subst markerCode
  subst afterMarker
  obtain ⟨returnPreludeCode, afterPrelude, afterPreludeCode,
      hPrelude, hAfterPrelude, hRestCode⟩ :=
    Locals.Block.compileOpen_append_components hRest
  have hAfterPreludeEq :
      afterPrelude =
        Locals.Ctx.procEntryWithLayoutAndRetc
          (StackLowering.functionBodyLayout fn) fn.returns.length := by
    have hFinal := initReturns_compileOpen_final hPrelude
    simpa [StackLowering.functionBodyLayout,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.withLayout,
      List.append_assoc] using hFinal
  subst afterPrelude
  obtain ⟨bodyCode, bodyFinalCtx, returnStmtCode,
      hBodyCompile, hReturnCompile, hAfterPreludeCode⟩ :=
    Locals.Block.compileOpen_append_components hAfterPrelude
  cases hReturns : fn.returns with
  | nil =>
      have hAccess' := hAccess
      rw [hReturns] at hAccess'
      simp only [hReturns] at *
      have hReturnCompile' := hReturnCompile
      simp [StackLowering.pushWordReturns, Locals.Block.compileOpen]
          at hReturnCompile'
      rcases hReturnCompile' with ⟨rfl, rfl⟩
      obtain ⟨cleanup, hCleanup, hCompiledBody⟩ :=
        Locals.finishToPreserving_components hFinish'
      let targetBody : Expressions.Block := { stmts := bodyCode }
      refine ⟨facts, schedule, localsBody, targetBody, bodyFinalCtx,
        returnPreludeCode, none, cleanup, hFacts, hSchedule, hBody,
        hAccess', hPrelude, ?_, (by trivial), hCleanup, ?_⟩
      · cases localsBody
        exact hBodyCompile
      · rw [hLowerProc', hCompiledBody, hFullCode, hRestCode,
          hAfterPreludeCode]
        simp [targetBody, returnCodeStmts, Locals.codeStmt,
          List.append_assoc]
  | cons returnName rest =>
      have hAccess' := hAccess
      rw [hReturns] at hAccess'
      simp only [hReturns] at *
      have hReturnCompile' := hReturnCompile
      have hReturnSingle :=
        Locals.Block.compileOpen_single_components
          (by simpa [StackLowering.pushWordReturns] using hReturnCompile')
      cases hReturnCode :
          Locals.ExprSeq.compileCode bodyFinalCtx 0
            (StackLowering.returnWords (returnName :: rest)) with
      | none =>
          simp [Locals.Stmt.compile, hReturnCode] at hReturnSingle
      | some returnCode =>
          simp [Locals.Stmt.compile, hReturnCode] at hReturnSingle
          rcases hReturnSingle with ⟨rfl, rfl⟩
          obtain ⟨cleanup, hCleanup, hCompiledBody⟩ :=
            Locals.finishToPreserving_components hFinish'
          let targetBody : Expressions.Block := { stmts := bodyCode }
          refine ⟨facts, schedule, localsBody, targetBody, bodyFinalCtx,
            returnPreludeCode, some returnCode, cleanup, hFacts, hSchedule,
            hBody, hAccess', hPrelude, ?_, hReturnCode, hCleanup, ?_⟩
          · cases localsBody
            exact hBodyCompile
          · rw [hLowerProc', hCompiledBody, hFullCode, hRestCode,
              hAfterPreludeCode]
            simp [targetBody, returnCodeStmts, Locals.codeStmt,
              List.append_assoc]

namespace Examples

def deadProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ← StackLowering.lowerProgram? StackLowering.Examples.deadProgram
  Locals.Program.compile? lower

theorem deadProgram_compiles : deadProgramCompiles?.isSome = true := by
  native_decide

def dormantCallProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ←
    StackLowering.lowerProgram?
      StackLowering.Examples.dormantCallProgram
  Locals.Program.compile? lower

theorem dormantCallProgram_compiles :
    dormantCallProgramCompiles?.isSome = true := by
  native_decide

def controlProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ←
    StackLowering.lowerProgram? StackLowering.Examples.controlProgram
  Locals.Program.compile? lower

theorem controlProgram_compiles :
    controlProgramCompiles?.isSome = true := by
  native_decide

def controlMainBlockArtifact? :=
  compileBlock?
    { functions := [], returns := [] }
    { normal := ∅ } ∅ Locals.Ctx.initial
    StackLowering.Examples.controlProgram.body

theorem controlMainBlock_layout_checked :
    controlMainBlockArtifact?.isSome = true := by
  native_decide

end Examples

end StackLoweringCompilation
end Functions
end EvmCompiler
