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

/--
Entry classification used by generated-context adequacy.

The top activation has no realized return tokens. Every procedure activation
instead carries a compiler-owned return token in its TypedCfg input shape.
-/
def ActivationInput
    (tokens : List Word) (input : TypedCfg.Shape) : Prop :=
  tokens = [] ∨ TypedCfgCompilerFacts.ReturnTokenActive input

namespace ActivationInput

theorem top (input : TypedCfg.Shape) :
    ActivationInput [] input :=
  Or.inl rfl

theorem active
    {tokens : List Word} {input : TypedCfg.Shape}
    (hActive : TypedCfgCompilerFacts.ReturnTokenActive input) :
    ActivationInput tokens input :=
  Or.inr hActive

theorem code
    {tokens : List Word} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    (hActivation : ActivationInput tokens input)
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    ActivationInput tokens output := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact Or.inr (hActive.code hType)

theorem tail
    {tokens : List Word} {shape : TypedCfg.Shape}
    (hActivation : ActivationInput tokens shape)
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape) :
    ActivationInput tokens
      { shape with slots := shape.slots.tail } := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact Or.inr (hActive.tail hSource)

theorem stmtFallthrough
    {tokens : List Word} {fuel : Nat}
    {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input output : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActivation : ActivationInput tokens input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result)
    (hFallthrough : result.fallthrough? = some output) :
    ActivationInput tokens output := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact
      Or.inr
        ((TypedCfgCompilerFacts.activeResult_of_compileStmtFuel?
          hActive hCompile).fallthrough output hFallthrough)

end ActivationInput

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
View the same enclosing acceptance boundary under the generated statement-list
rest label. When the outer regular label predates the supply, every generated
label is distinct from it; when it is already the rest label, the freshness
contract is unchanged.
-/
theorem restRegular
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hRegular :
      OutcomeSimulation.RegularAtSupply regular supply) :
    OutcomeSimulation.RecursiveBoundary cfg source tokens accept
      supply (TypedCfgCompiler.restLabel supply) := by
  refine ⟨hBoundary.ownership, ?_⟩
  intro scope tag target hScope hNe hAccepted
  apply hBoundary.fresh scope tag target hScope
  · rcases hRegular with hBefore | rfl
    · exact hBefore.generated_ne hScope
    · exact hNe
  · exact hAccepted

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

/--
Reject a newly generated current-activation entry uniformly at top level and
inside procedures.

At top level a strict activation extension into an empty token stack is
impossible. Inside a procedure, the active return-token shape separates the
current frame from every accepted ancestor frame.
-/
theorem rejectGenerated
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hActivation : ActivationInput tokens shape)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hAccepted : accept (.jump (.generated scope tag) target))
    (hShape :
      OutcomeSimulation.LabelShape cfg
        (.generated scope tag) shape)
    (hCurrent :
      OutcomeSimulation.FrameMatches source tokens shape target) :
    False := by
  rcases hActivation with hTop | hActive
  · rcases
        hBoundary.fresh scope tag target hScope hNe hAccepted with
      ⟨_owner, ownerTokens, _block, _hFind, _hFrame, hExtension⟩
    exact hExtension.childTokens_ne_nil hTop
  · rcases hActive with ⟨depth, hDepth⟩
    exact
      hBoundary.reject hScope hNe hAccepted hShape hDepth hCurrent

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

theorem adequateWithinFuel_if
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hActivation : ActivationInput tokens input)
    (hRegular :
      OutcomeSimulation.RegularAtSupply regular supply)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        afterCond.source.returns = source.source.returns →
        ActivationInput tokens bodyInput →
        OutcomeSimulation.RecursiveBoundary
          cfg afterCond tokens accept (supply + 1) regular →
        ∀ bodyTargetFuel, bodyTargetFuel < targetFuel →
          OutcomeSimulation.AdequateWithinFuel
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel body afterCond sourceOutcome)
            bodyResult ctx cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular)
            accept (LabelSupply.label supply 0)
            bodyInput afterCond tokens bodyTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  obtain
      ⟨output, _condition, knownBodyResult,
        hType, hSource, _hHead, hKnownBodyCompile,
        _hRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if
      hCompile
  subst result
  have hOutputActivation := hActivation.code hType
  have hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength output :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
      hSource
  have hBodyActivation := hOutputActivation.tail hSourceOne
  have hKnownBodyBlocks :
      TypedCfgPreservation.BlocksInProgram knownBodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hKnownBodyShape :
      OutcomeSimulation.LabelShape cfg
        (LabelSupply.label supply 0)
        { output with slots := output.slots.tail } :=
    OutcomeSimulation.LabelShape.of_compileBlockFuel?
      hKnownBodyCompile hKnownBodyBlocks
  apply
    Stmt.adequateWithinFuel_if_of_compileStmtFuel?
      targetFuel hCompile hBlocks rfl
  · intro current bodyInput target hReturns hShape hFrame hAccepted
    have hInputEq :
        bodyInput = { output with slots := output.slots.tail } :=
      OutcomeSimulation.LabelShape.eq hShape hKnownBodyShape
    subst bodyInput
    exact
      (hBoundary.congr_returns hReturns.symm).rejectGenerated
        hBodyActivation (Nat.le_refl supply)
        (by
          simpa [LabelSupply.label] using
            hRegular.current_generated_ne (by omega : 0 ≠ 100))
        hAccepted hShape hFrame
  · intro bodyInput bodyResult afterCond
      hBodyCompile hBodyBlocks hReturns bodyTargetFuel hFuel
    have hBodyShape :
        OutcomeSimulation.LabelShape cfg
          (LabelSupply.label supply 0) bodyInput :=
      OutcomeSimulation.LabelShape.of_compileBlockFuel?
        hBodyCompile hBodyBlocks
    have hInputEq :
        bodyInput = { output with slots := output.slots.tail } :=
      OutcomeSimulation.LabelShape.eq hBodyShape hKnownBodyShape
    subst bodyInput
    exact
      hBodyAdequate hBodyCompile hBodyBlocks hReturns
        hBodyActivation
        (hBoundary.sameActivation hReturns.symm (Nat.le_succ supply))
        bodyTargetFuel hFuel

end Generated

end ObserverAdequacy
end Structured
end EvmCompiler
