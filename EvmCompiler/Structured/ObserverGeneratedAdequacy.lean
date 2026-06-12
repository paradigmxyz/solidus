import EvmCompiler.Structured.ObserverCallAdequacy
import EvmCompiler.Structured.ObserverSequenceAdequacy
import EvmCompiler.Structured.ObserverSwitchAdequacy
import EvmCompiler.Structured.ObserverTerminalAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy

/-!
Generated-context backward adequacy for the Structured-to-TypedCfg pass.

This module owns the mutual statement/block theorem. The sibling modules own
the individual compiler forms; this module supplies only the recursive source
context and activation-aware boundary composition shared across those forms.
-/

/--
Source-facing context needed by recursive backward adequacy.

Control permissions are related to the existing compiler context, procedure
lookup uses the original source program, and `leave` is enabled only when the
current activation carries a concrete return token.
-/
structure SourceContext
    (program : Structured.Program)
    (ctx : TypedCfgCompiler.Context)
    (tokens : List Word)
    (canBreak canContinue canLeave : Bool) : Prop where
  supports :
    TypedCfgPreservation.OutcomeSimulation.ContextSupports
      ctx canBreak canContinue canLeave
  procs : ctx.procs = program.procs
  leaveTokens : canLeave = true → tokens ≠ []

namespace SourceContext

theorem withoutLoop
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave) :
    SourceContext program
      { ctx with
        breakLabel? := none
        breakShape? := none
        continueLabel? := none
        continueShape? := none }
      tokens false false canLeave :=
  { supports := hContext.supports.withoutLoop
    procs := hContext.procs
    leaveTokens := hContext.leaveTokens }

theorem loopBody
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (breakLabel continueLabel : Assembly.Label)
    (shape : TypedCfg.Shape) :
    SourceContext program
      { ctx with
        breakLabel? := some breakLabel
        breakShape? := some shape
        continueLabel? := some continueLabel
        continueShape? := some shape }
      tokens true true canLeave :=
  { supports :=
      hContext.supports.loopBody
        breakLabel continueLabel shape
    procs := hContext.procs
    leaveTokens := hContext.leaveTokens }

theorem procedure
    (program : Structured.Program) (proc : Structured.Proc)
    (token : Word) (tokens : List Word) :
    SourceContext program
      { procs := program.procs
        leaveLabel? := some (ProcLabel.exit proc.name)
        leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
      (token :: tokens) false false true :=
  { supports :=
      { breakLabel := by simp
        continueLabel := by simp
        leaveLabel := by
          intro _hEnabled
          exact ⟨ProcLabel.exit proc.name, rfl⟩ }
    procs := rfl
    leaveTokens := by simp }

end SourceContext

namespace OutcomeSimulation.RecursiveBoundary

/--
Move an enclosing recursive boundary to a later compiler supply after source
execution that preserves the current return stack.
-/
theorem sameActivation
    {transcript : Trace} {cfg : TypedCfg.Program}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply next : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg left tokens accept supply regular)
    (hReturns : left.source.returns = right.source.returns)
    (hSupply : supply ≤ next) :
    OutcomeSimulation.RecursiveBoundary
      cfg right tokens accept next regular :=
  (hBoundary.congr_returns hReturns).mono hSupply

/--
Install the exact statement-list tail continuation in the same activation.
-/
theorem statementTail
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape}
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hRegular :
      OutcomeSimulation.RegularAtSupply regular supply)
    (hShape :
      OutcomeSimulation.LabelShape cfg
        (TypedCfgCompiler.restLabel supply) shape) :
    OutcomeSimulation.RecursiveBoundary cfg source tokens
      (OutcomeSimulation.JumpAt source tokens
        (TypedCfgCompiler.restLabel supply) shape accept)
      supply (TypedCfgCompiler.restLabel supply) :=
  hBoundary.jumpAt_rest hRegular hShape

/--
Install a procedure-exit continuation in a strictly deeper activation.
-/
theorem procedureBody
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source child : ObserverSemantics.State transcript}
    {tokens childTokens : List Word}
    {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular next : Assembly.Label}
    {shape : TypedCfg.Shape}
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hExtension :
      OutcomeSimulation.ActivationExtension
        source.source.returns tokens
        child.source.returns childTokens)
    (hShape : OutcomeSimulation.LabelShape cfg next shape)
    (childSupply : LabelSupply) :
    OutcomeSimulation.RecursiveBoundary cfg child childTokens
      (OutcomeSimulation.JumpAt child childTokens next shape accept)
      childSupply next :=
  hBoundary.pushJumpAt hExtension hShape childSupply

end OutcomeSimulation.RecursiveBoundary

namespace Generated

theorem adequateWithinFuel_code
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel :=
  (Stmt.adequateWithin_code_of_compileStmtFuel?
    hCompile hBlocks rfl).fuel targetFuel

theorem adequateWithinFuel_brk
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hAllowed : canBreak = true)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel .brk source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  obtain ⟨label, hLabel⟩ :=
    hContext.supports.breakLabel hAllowed
  exact
    (Stmt.adequateWithin_brk_of_compileStmtFuel?
      hLabel hCompile hBlocks).fuel targetFuel

theorem adequateWithinFuel_cont
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hAllowed : canContinue = true)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel .cont source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  obtain ⟨label, hLabel⟩ :=
    hContext.supports.continueLabel hAllowed
  exact
    (Stmt.adequateWithin_cont_of_compileStmtFuel?
      hLabel hCompile hBlocks).fuel targetFuel

theorem adequateWithinFuel_leave
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hAllowed : canLeave = true)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel .leave source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  obtain ⟨label, hLabel⟩ :=
    hContext.supports.leaveLabel hAllowed
  exact
    (Stmt.adequateWithin_leave_of_compileStmtFuel?_tokens
      hLabel (hContext.leaveTokens hAllowed)
      hCompile hBlocks).fuel targetFuel

theorem adequateWithinFuel_terminal
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hWellTyped : cfg.WellTyped) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.terminal kind) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel :=
  (Stmt.adequateWithin_terminal_of_compileStmtFuel?
    hCompile hBlocks hWellTyped).fuel targetFuel

end Generated

end ObserverAdequacy
end Structured
end EvmCompiler
