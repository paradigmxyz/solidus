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
    (hActivation : OutcomeSimulation.ActivationInput tokens shape)
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
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
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
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram bodyResult globalCalls →
        afterCond.source.returns = source.source.returns →
        OutcomeSimulation.ActivationInput tokens bodyInput →
        OutcomeSimulation.RecursiveBoundary
          cfg afterCond tokens accept (supply + 1) regular →
        OutcomeSimulation.EntryRejected cfg afterCond tokens accept
          (LabelSupply.label supply 0) bodyInput →
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
  have hKnownBodyCalls :
      TypedCfgPreservation.CallsInProgram knownBodyResult globalCalls := by
    intro site hMem
    apply hCalls site
    simpa using hMem
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
    have hResultEq : bodyResult = knownBodyResult :=
      Option.some.inj (hBodyCompile.symm.trans hKnownBodyCompile)
    subst bodyResult
    exact
      hBodyAdequate hBodyCompile hBodyBlocks hKnownBodyCalls hReturns
        hBodyActivation
        (hBoundary.sameActivation hReturns.symm (Nat.le_succ supply))
        (by
          intro target hShape hFrame hAccepted
          exact
            (hBoundary.congr_returns hReturns.symm).rejectGenerated
              hBodyActivation (Nat.le_refl supply)
              (by
                simpa [LabelSupply.label] using
                  hRegular.current_generated_ne (by omega : 0 ≠ 100))
              hAccepted hShape hFrame)
        bodyTargetFuel hFuel

theorem adequateWithinFuel_switch
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {canBreak canContinue canLeave : Bool}
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hRegular :
      OutcomeSimulation.RegularAtSupply regular supply)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hCasesWF :
      ∀ caseValue body, (caseValue, body) ∈ cases →
        Structured.Block.WF
          canBreak canContinue canLeave body)
    (hDefaultWF :
      ∀ body, defaultBody = some body →
        Structured.Block.WF
          canBreak canContinue canLeave body)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hBodyAdequate :
      ∀ {selected : Structured.Block}
        {afterScrutinee : ObserverSemantics.State transcript}
        {stack : EvmYul.Stack Word} {value : Word}
        {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram bodyResult globalCalls →
        Structured.Block.WF
          canBreak canContinue canLeave selected →
        OutcomeSimulation.LabelBeforeSupply bodyEntry bodySupply →
        OutcomeSimulation.EntryRejected cfg
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens accept bodyEntry bodyShape →
        (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack })).source.returns =
          source.source.returns →
        OutcomeSimulation.ActivationInput tokens bodyShape →
        supply + 1 ≤ bodySupply →
        OutcomeSimulation.RegularAtSupply regular bodySupply →
        OutcomeSimulation.RecursiveBoundary
          cfg
            (afterScrutinee.withSource
              (afterScrutinee.source.withEVM
                { afterScrutinee.source.evm with stack := stack }))
            tokens accept bodySupply regular →
        ∀ bodyTargetFuel, bodyTargetFuel < targetFuel →
          OutcomeSimulation.AdequateWithinFuel
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval program sourceFuel selected
                (afterScrutinee.withSource
                  (afterScrutinee.source.withEVM
                    { afterScrutinee.source.evm with stack := stack }))
                sourceOutcome)
            bodyResult ctx cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular)
            accept bodyEntry bodyShape
            (afterScrutinee.withSource
              (afterScrutinee.source.withEVM
                { afterScrutinee.source.evm with stack := stack }))
            tokens bodyTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.switch scrutinee cases defaultBody) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  apply
    Switch.adequateWithinFuel_switch_of_compileStmtFuel?
      targetFuel hActivation hCompile hBlocks hCalls rfl
  · intro caseIdx remaining current shape
      hReturns hCurrentActivation target hShape hFrame hAccepted
    cases remaining with
    | nil =>
        exact
          (hBoundary.congr_returns hReturns.symm).rejectGenerated
            (scope := supply) (tag := 1)
            hCurrentActivation (Nat.le_refl supply)
            (by
              simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel,
                LabelSupply.label] using
                hRegular.current_generated_ne (by omega : 1 ≠ 100))
            (by
              simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel,
                LabelSupply.label] using hAccepted)
            (by
              simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel,
                LabelSupply.label] using hShape)
            hFrame
    | cons head rest =>
        exact
          (hBoundary.congr_returns hReturns.symm).rejectGenerated
            (scope := supply) (tag := 6 * caseIdx + 1001)
            hCurrentActivation (Nat.le_refl supply)
            (by
              simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel,
                TypedCfgCompiler.switchTestLabel] using
                hRegular.current_generated_ne
                  (by omega : 6 * caseIdx + 1001 ≠ 100))
            (by
              simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel,
                TypedCfgCompiler.switchTestLabel] using hAccepted)
            (by
              simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel,
                TypedCfgCompiler.switchTestLabel] using hShape)
            hFrame
  · intro caseIdx current shape
      hReturns hCurrentActivation target hShape hFrame hAccepted
    exact
      (hBoundary.congr_returns hReturns.symm).rejectGenerated
        (scope := supply) (tag := 6 * caseIdx + 1003)
        hCurrentActivation (Nat.le_refl supply)
        (by
          simpa [TypedCfgCompiler.switchCaseLabel] using
            hRegular.current_generated_ne
              (by omega : 6 * caseIdx + 1003 ≠ 100))
        (by simpa [TypedCfgCompiler.switchCaseLabel] using hAccepted)
        (by simpa [TypedCfgCompiler.switchCaseLabel] using hShape)
        hFrame
  · intro caseIdx current shape
      hReturns hCurrentActivation target hShape hFrame hAccepted
    exact
      (hBoundary.congr_returns hReturns.symm).rejectGenerated
        (scope := supply) (tag := 6 * caseIdx + 1005)
        hCurrentActivation (Nat.le_refl supply)
        (by
          simpa [TypedCfgCompiler.switchBodyLabel] using
            hRegular.current_generated_ne
              (by omega : 6 * caseIdx + 1005 ≠ 100))
        (by simpa [TypedCfgCompiler.switchBodyLabel] using hAccepted)
        (by simpa [TypedCfgCompiler.switchBodyLabel] using hShape)
        hFrame
  · intro generatedSupply hSupply current shape
      hReturns hCurrentActivation target hShape hFrame hAccepted
    apply
      (hBoundary.congr_returns hReturns.symm).rejectGenerated
        (scope := generatedSupply) (tag := 2000)
        hCurrentActivation hSupply ?_ hAccepted hShape hFrame
    rcases hRegular with hBefore | rfl
    · exact hBefore.generated_ne hSupply
    · simp [TypedCfgCompiler.restLabel]
  · intro selected afterScrutinee stack value
      bodyCompilerFuel bodySupply bodyEntry bodyShape bodyResult
      bodyTargetFuel _hScrutinee _hPop _hSelect
      hReturns hBodyActivation hBodySupply _hFuel
      hBodyCompile hBodyBlocks hBodyCalls hBodyEntryBefore hBodyEntryRejected
    exact
      hBodyAdequate (value := value)
        hBodyCompile hBodyBlocks hBodyCalls
        (Structured.Switch.wf_of_select hCasesWF hDefaultWF _hSelect)
        hBodyEntryBefore
        hBodyEntryRejected hReturns hBodyActivation hBodySupply
        (hRegular.advance hBodySupply)
        (hBoundary.sameActivation hReturns.symm
          (Nat.le_trans (Nat.le_succ supply) hBodySupply))
        bodyTargetFuel _hFuel

theorem adequateWithinFuel_for
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {init : Structured.Block} {cond : Structured.Code}
    {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hInitWF :
      Structured.Block.WF false false canLeave init)
    (hPostWF :
      Structured.Block.WF false false canLeave post)
    (hBodyWF :
      Structured.Block.WF true true canLeave body)
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hEntryBefore :
      OutcomeSimulation.LabelBeforeSupply entry supply)
    (hRegular :
      OutcomeSimulation.RegularAtSupply regular supply)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hEntryRejected :
      OutcomeSimulation.EntryRejected
        cfg source tokens accept entry input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hBlockAdequate :
      ∀ {block : Structured.Block}
        {blockCtx : TypedCfgCompiler.Context}
        {blockSupply : LabelSupply}
        {blockEntry blockRegular : Assembly.Label}
        {blockInput : TypedCfg.Shape}
        {blockResult : TypedCfgCompiler.Result}
        {blockSource : ObserverSemantics.State transcript}
        {blockAccept : TypedCfg.Outcome → Prop}
        {blockCanBreak blockCanContinue blockCanLeave : Bool},
        SourceContext program blockCtx tokens
            blockCanBreak blockCanContinue blockCanLeave →
        Structured.Block.WF
          blockCanBreak blockCanContinue blockCanLeave block →
        OutcomeSimulation.ActivationInput tokens blockInput →
        OutcomeSimulation.LabelBeforeSupply blockEntry blockSupply →
        OutcomeSimulation.LabelBeforeSupply blockRegular blockSupply →
        OutcomeSimulation.RecursiveBoundary
          cfg blockSource tokens blockAccept blockSupply blockRegular →
        OutcomeSimulation.EntryRejected cfg blockSource tokens blockAccept
          blockEntry blockInput →
        TypedCfgCompiler.compileBlockFuel? compilerFuel block blockCtx
            blockSupply blockEntry blockInput blockRegular =
          some blockResult →
        TypedCfgPreservation.BlocksInProgram blockResult cfg →
        TypedCfgPreservation.CallsInProgram blockResult globalCalls →
        ∀ blockTargetFuel, blockTargetFuel ≤ targetFuel →
          OutcomeSimulation.AdequateWithinFuel
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel block blockSource sourceOutcome)
            blockResult blockCtx cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              blockCtx blockRegular)
            blockAccept blockEntry blockInput blockSource tokens
            blockTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.for_ init cond post body) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  have hEntryShape :
      OutcomeSimulation.LabelShape cfg entry input :=
    OutcomeSimulation.LabelShape.of_compileStmtFuel?
      hCompile hBlocks
  apply
    Loop.adequateWithinFuel_for_of_compileStmtFuel?
      targetFuel hActivation hCompile hBlocks hCalls
  · intro loopShape target hFrame
    simp only [OutcomeSimulation.JumpAt]
    intro hAccepted
    rcases hAccepted with hCurrent | hOuter
    · exact
        (hEntryBefore.generated_ne (Nat.le_refl supply))
          hCurrent.1.symm
    · exact hEntryRejected target hEntryShape hFrame hOuter
  · intro generatedOffset hOffset current shape
      hReturns hCurrentActivation target hShape hFrame hAccepted
    exact
      (hBoundary.congr_returns hReturns.symm).rejectGenerated
        (scope := supply) (tag := generatedOffset)
        hCurrentActivation (Nat.le_refl supply)
        (by
          simpa [LabelSupply.label] using
            hRegular.current_generated_ne (by omega))
        (by simpa [LabelSupply.label] using hAccepted)
        (by simpa [LabelSupply.label] using hShape)
        hFrame
  · intro initResult loopInput hInitCompile
      hInitFallthrough hInitBlocks hInitCalls hLoopActivation hLoopShape
      initTargetFuel hFuel initSource hReturns hInitEntryRejected
    simpa [Loop.postContinuations,
      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext] using
      (hBlockAdequate hContext.withoutLoop hInitWF hActivation
        (hEntryBefore.mono (Nat.le_succ supply))
        (by
          simp [OutcomeSimulation.LabelBeforeSupply,
            LabelSupply.label])
        ((hBoundary.congr_returns hReturns.symm).jumpAt_current
          hRegular hLoopShape)
        hInitEntryRejected
        hInitCompile hInitBlocks hInitCalls
        initTargetFuel hFuel)
  · intro initResult bodyResult condOutput
      hBodyCompile hBodyBlocks hBodyCalls hBodyActivation hPostShape hInitNext
      bodySource hReturns hBodyEntryRejected bodyTargetFuel hFuel
    have hBodySupplyBefore :
        OutcomeSimulation.LabelBeforeSupply
          (LabelSupply.label supply 1) initResult.next := by
      simpa [OutcomeSimulation.LabelBeforeSupply,
        LabelSupply.label] using
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self supply) hInitNext)
    have hPostBefore :
        OutcomeSimulation.LabelBeforeSupply
          (LabelSupply.label supply 2) initResult.next := by
      simpa [OutcomeSimulation.LabelBeforeSupply,
        LabelSupply.label] using
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self supply) hInitNext)
    exact
      hBlockAdequate
        (hContext.loopBody regular
          (LabelSupply.label supply 2)
          { condOutput with slots := condOutput.slots.tail })
        hBodyWF hBodyActivation hBodySupplyBefore hPostBefore
        ((hBoundary.sameActivation hReturns.symm
            (Nat.le_trans (Nat.le_succ supply) hInitNext)).jumpAt_before
          (hRegular.before_succ.mono hInitNext)
          hPostBefore hPostShape)
        hBodyEntryRejected
        hBodyCompile hBodyBlocks hBodyCalls
        bodyTargetFuel (Nat.le_of_lt hFuel)
  · intro bodyResult postResult condOutput loopInput
      hPostCompile hPostBlocks hPostCalls hBodyActivation hLoopActivation
      hLoopShape hBodySupply
      postSource hReturns hPostEntryRejected postTargetFuel hFuel
    have hPostSupplyBefore :
        OutcomeSimulation.LabelBeforeSupply
          (LabelSupply.label supply 2) bodyResult.next := by
      simpa [OutcomeSimulation.LabelBeforeSupply,
        LabelSupply.label] using
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self supply) hBodySupply)
    have hLoopBefore :
        OutcomeSimulation.LabelBeforeSupply
          (LabelSupply.label supply 0) bodyResult.next := by
      simpa [OutcomeSimulation.LabelBeforeSupply,
        LabelSupply.label] using
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self supply) hBodySupply)
    exact
      hBlockAdequate hContext.withoutLoop hPostWF hBodyActivation
        hPostSupplyBefore hLoopBefore
        ((hBoundary.sameActivation hReturns.symm
            (Nat.le_trans (Nat.le_succ supply) hBodySupply)).jumpAt_before
          (hRegular.before_succ.mono
            hBodySupply)
          hLoopBefore hLoopShape)
        hPostEntryRejected
        hPostCompile hPostBlocks hPostCalls
        postTargetFuel (Nat.le_of_lt hFuel)

theorem adequateWithinFuel_call
    {transcript : Trace} {compilerFuel targetFuel : Nat}
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
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hProgramWF : program.WF)
    (hBodyAdequate :
      ∀ {proc : Structured.Proc}
        {fragment :
          TypedCfgPreservation.Program.ProcFragment
            entryShapes program.procs proc
            generated.procBlocks generated.procCalls}
        {callSource : ObserverSemantics.State transcript},
        Structured.ProcList.lookup? name program.procs = some proc →
        TypedCfgPreservation.BlocksInProgram fragment.result cfg →
        TypedCfgPreservation.CallsInProgram
          fragment.result generated.calls →
        SourceContext program
          { procs := program.procs
            leaveLabel? := some (ProcLabel.exit proc.name)
            leaveShape? :=
              some (TypedCfgCompiler.Shape.procExit proc) }
          (Structured.Stmt.callToken supply :: tokens)
          false false true →
        OutcomeSimulation.ActivationInput
          (Structured.Stmt.callToken supply :: tokens) fragment.input →
        OutcomeSimulation.LabelBeforeSupply
          fragment.entry fragment.supply →
        OutcomeSimulation.LabelBeforeSupply
          (ProcLabel.exit proc.name) fragment.supply →
        OutcomeSimulation.RecursiveBoundary cfg callSource
          (Structured.Stmt.callToken supply :: tokens)
          (OutcomeSimulation.JumpAt callSource
            (Structured.Stmt.callToken supply :: tokens)
            (ProcLabel.exit proc.name)
            (TypedCfgCompiler.Shape.procExit proc) accept)
          fragment.supply (ProcLabel.exit proc.name) →
        OutcomeSimulation.EntryRejected cfg callSource
          (Structured.Stmt.callToken supply :: tokens)
          (OutcomeSimulation.JumpAt callSource
            (Structured.Stmt.callToken supply :: tokens)
            (ProcLabel.exit proc.name)
            (TypedCfgCompiler.Shape.procExit proc) accept)
          fragment.entry fragment.input →
        ∀ bodyTargetFuel, bodyTargetFuel < targetFuel →
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
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  apply
    Call.adequateWithinFuel_call_of_compileStmtFuel?_protected
      generated hCompile hBlocks hCalls hContext.procs hProgramWF rfl
      hBoundary.ownership
  intro proc fragment callSource hLookup hFragmentBlocks hFragmentCalls
    hExtension bodyTargetFuel hFuel
  have hInputActivation :
      OutcomeSimulation.ActivationInput
        (Structured.Stmt.callToken supply :: tokens) fragment.input :=
    OutcomeSimulation.ActivationInput.active
      ⟨proc.argc,
        TypedCfgCompilerFacts.ActiveResult.procFragment_input fragment⟩
  have hEntryBefore :
      OutcomeSimulation.LabelBeforeSupply
        fragment.entry fragment.supply := by
    rcases fragment.route with hDirect | hAdapter
    · rw [hDirect.1]
      trivial
    · rcases hAdapter with
        ⟨_adapter, hEntry, _hInput, _hFrame, _hCompile, _hMem⟩
      rw [hEntry]
      trivial
  have hRegularBefore :
      OutcomeSimulation.LabelBeforeSupply
        (ProcLabel.exit proc.name) fragment.supply :=
    by trivial
  have hExitShape :
      OutcomeSimulation.LabelShape cfg
        (ProcLabel.exit proc.name)
        (TypedCfgCompiler.Shape.procExit proc) :=
    OutcomeSimulation.LabelShape.procExit generated hLookup
  exact
    hBodyAdequate hLookup hFragmentBlocks hFragmentCalls
      (SourceContext.procedure program proc
        (Structured.Stmt.callToken supply) tokens)
      hInputActivation hEntryBefore hRegularBefore
      (hBoundary.procedureBody hExtension hExitShape fragment.supply)
      (by
        intro target hShape hFrame hAccepted
        rcases hAccepted with hCurrent | hOuter
        · exact
            (OutcomeSimulation.ProcFragment.entry_ne_exit fragment)
              hCurrent.1
        · exact
            hBoundary.ownership.reject_extension hOuter hShape
              (TypedCfgCompilerFacts.ActiveResult.procFragment_input fragment)
              hExtension hFrame)
      bodyTargetFuel hFuel

theorem adequateWithinFuel_cons
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hRegularBefore :
      OutcomeSimulation.LabelBeforeSupply regular supply)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hEntryNotAccepted :
      ∀ joinShape targetState,
        OutcomeSimulation.LabelShape cfg entry input →
          OutcomeSimulation.FrameMatches source tokens input targetState →
          ¬ OutcomeSimulation.JumpAt source tokens
              (TypedCfgCompiler.restLabel supply) joinShape accept
              (.jump entry targetState))
    (hHeadAdequate :
      ∀ {headResult : TypedCfgCompiler.Result}
        {headAccept : TypedCfg.Outcome → Prop},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        TypedCfgPreservation.CallsInProgram headResult globalCalls →
        OutcomeSimulation.RecursiveBoundary cfg source tokens headAccept
          supply (TypedCfgCompiler.restLabel supply) →
        OutcomeSimulation.EntryRejected cfg source tokens headAccept
          entry input →
        ∀ headTargetFuel, headTargetFuel ≤ targetFuel →
          OutcomeSimulation.AdequateWithinFuel
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Stmt.Eval
                program sourceFuel stmt source sourceOutcome)
            headResult ctx cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx (TypedCfgCompiler.restLabel supply))
            headAccept entry input source tokens headTargetFuel)
    (hTailAdequate :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape}
        {tailSource : ObserverSemantics.State transcript},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        TypedCfgPreservation.CallsInProgram tailResult globalCalls →
        tailSource.source.returns = source.source.returns →
        OutcomeSimulation.ActivationInput tokens tailInput →
        OutcomeSimulation.RegularAtSupply regular headResult.next →
        OutcomeSimulation.RecursiveBoundary cfg tailSource tokens accept
          headResult.next regular →
        OutcomeSimulation.EntryRejected cfg tailSource tokens accept
          (TypedCfgCompiler.restLabel supply) tailInput →
        ∀ tailTargetFuel, tailTargetFuel ≤ targetFuel →
          OutcomeSimulation.AdequateWithinFuel
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel { stmts := rest }
                tailSource sourceOutcome)
            tailResult ctx cfg
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular)
            accept (TypedCfgCompiler.restLabel supply)
            tailInput tailSource tokens tailTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := stmt :: rest }
          source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  apply
    Block.adequateWithinFuel_cons_of_compileStmtListFuel?
      targetFuel hCompile hBlocks hCalls hEntryNotAccepted
  · intro headResult joinShape hHeadCompile hFallthrough
      hShape tailSource targetState hReturns hFrame hAccepted
    exact
      (hBoundary.congr_returns hReturns.symm).rejectGenerated
        (hActivation.stmtFallthrough hHeadCompile hFallthrough)
        (Nat.le_refl supply)
        (by
          simpa [TypedCfgCompiler.restLabel] using
            hRegularBefore.generated_ne (Nat.le_refl supply))
        hAccepted hShape hFrame
  · intro headResult hHeadCompile hHeadBlocks hHeadCalls _hFallthrough
      headTargetFuel hFuel
    exact
      hHeadAdequate hHeadCompile hHeadBlocks hHeadCalls
        (hBoundary.restRegular (Or.inl hRegularBefore))
        (by
          intro target hShape hFrame hAccepted
          exact
            hEntryNotAccepted input target hShape hFrame (Or.inr hAccepted))
        headTargetFuel hFuel
  · intro headResult joinShape hHeadCompile hHeadBlocks hHeadCalls
      _hFallthrough hShape headTargetFuel hFuel
    exact
      hHeadAdequate hHeadCompile hHeadBlocks hHeadCalls
        (hBoundary.statementTail (Or.inl hRegularBefore) hShape)
        (by
          intro target hEntryShape hFrame hAccepted
          exact
            hEntryNotAccepted joinShape target hEntryShape hFrame hAccepted)
        headTargetFuel hFuel
  · intro headResult tailResult tailInput tailSource
      hHeadCompile hFallthrough hTailCompile hTailBlocks hTailCalls hReturns
      tailTargetFuel hFuel
    have hNext :
        supply ≤ headResult.next :=
      TypedCfgCompilerFacts.Supply.stmt_next_ge hHeadCompile
    exact
      hTailAdequate hHeadCompile hFallthrough hTailCompile hTailBlocks
        hTailCalls
        hReturns
        (hActivation.stmtFallthrough hHeadCompile hFallthrough)
        (Or.inl (hRegularBefore.mono hNext))
        (hBoundary.sameActivation hReturns.symm hNext)
        (by
          intro target hShape hFrame hAccepted
          exact
            (hBoundary.congr_returns hReturns.symm).rejectGenerated
              (hActivation.stmtFallthrough hHeadCompile hFallthrough)
              (Nat.le_refl supply)
              (by
                simpa [TypedCfgCompiler.restLabel] using
                  hRegularBefore.generated_ne (Nat.le_refl supply))
              hAccepted hShape hFrame)
        tailTargetFuel hFuel

mutual

/--
Generated-context backward adequacy for every well-formed Structured block.

The recursion is horizontal and pass-owned: syntax children decrease compiler
fuel, while procedure bodies decrease target execution fuel.
-/
theorem adequateWithinFuel_block
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hProgramWF : program.WF)
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hWF :
      Structured.Block.WF
        canBreak canContinue canLeave block)
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hEntryBefore :
      OutcomeSimulation.LabelBeforeSupply entry supply)
    (hRegularBefore :
      OutcomeSimulation.LabelBeforeSupply regular supply)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hEntryRejected :
      OutcomeSimulation.EntryRejected
        cfg source tokens accept entry input)
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel block ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel block source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  cases compilerFuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ blockFuel =>
      rcases block with ⟨stmts⟩
      cases stmts with
      | nil =>
          cases blockFuel with
          | zero =>
              simp [TypedCfgCompiler.compileBlockFuel?,
                TypedCfgCompiler.compileStmtListFuel?] at hCompile
          | succ listFuel =>
              exact
                (Block.adequateWithin_nil_of_compileBlockFuel?
                  hCompile hBlocks rfl).fuel targetFuel
      | cons stmt rest =>
          cases hWF with
          | cons hStmtWF hRestWF =>
              cases blockFuel with
              | zero =>
                  simp [TypedCfgCompiler.compileBlockFuel?,
                    TypedCfgCompiler.compileStmtListFuel?] at hCompile
              | succ listFuel =>
                  have hListCompile :
                      TypedCfgCompiler.compileStmtListFuel? (listFuel + 1)
                          (stmt :: rest) ctx supply entry input regular =
                        some result := by
                    simpa [TypedCfgCompiler.compileBlockFuel?] using hCompile
                  apply
                    adequateWithinFuel_cons
                      hActivation hRegularBefore hBoundary
                      hListCompile hBlocks hCalls
                  · intro joinShape target hShape hFrame hAccepted
                    rcases hAccepted with hCurrent | hOuter
                    · exact
                        (hEntryBefore.generated_ne (Nat.le_refl supply))
                          hCurrent.1.symm
                    · exact hEntryRejected target hShape hFrame hOuter
                  · intro headResult headAccept hHeadCompile hHeadBlocks
                      hHeadCalls hHeadBoundary hHeadEntryRejected
                      headTargetFuel hHeadFuel
                    by_cases hStrict : headTargetFuel < targetFuel
                    · exact
                        adequateWithinFuel_stmt generated hProgramWF
                          hContext hStmtWF hActivation hEntryBefore
                          (Or.inr rfl) hHeadBoundary hHeadEntryRejected
                          hHeadCompile hHeadBlocks hHeadCalls
                          (targetFuel := headTargetFuel)
                    · have hEq : headTargetFuel = targetFuel := by
                        omega
                      subst headTargetFuel
                      exact
                        adequateWithinFuel_stmt generated hProgramWF
                          hContext hStmtWF hActivation hEntryBefore
                          (Or.inr rfl) hHeadBoundary hHeadEntryRejected
                          hHeadCompile hHeadBlocks hHeadCalls
                          (targetFuel := targetFuel)
                  · intro headResult tailResult tailInput tailSource
                      hHeadCompile hFallthrough hTailCompile hTailBlocks
                      hTailCalls hReturns hTailActivation _hTailRegular
                      hTailBoundary hTailEntryRejected
                      tailTargetFuel hTailFuel
                    have hTailBlockCompile :
                        TypedCfgCompiler.compileBlockFuel? (listFuel + 1)
                            { stmts := rest } ctx headResult.next
                            (TypedCfgCompiler.restLabel supply)
                            tailInput regular =
                          some tailResult := by
                      simpa [TypedCfgCompiler.compileBlockFuel?] using
                        hTailCompile
                    have hTailEntryBefore :
                        OutcomeSimulation.LabelBeforeSupply
                          (TypedCfgCompiler.restLabel supply)
                          headResult.next := by
                      simpa [OutcomeSimulation.LabelBeforeSupply,
                        TypedCfgCompiler.restLabel] using
                        TypedCfgCompilerFacts.Supply.stmt_next_ge_succ
                          hHeadCompile
                    have hTailRegularBefore :
                        OutcomeSimulation.LabelBeforeSupply
                          regular headResult.next :=
                      hRegularBefore.mono
                        (TypedCfgCompilerFacts.Supply.stmt_next_ge
                          hHeadCompile)
                    by_cases hStrict : tailTargetFuel < targetFuel
                    · exact
                        adequateWithinFuel_block generated hProgramWF
                          hContext hRestWF hTailActivation
                          hTailEntryBefore hTailRegularBefore
                          hTailBoundary hTailEntryRejected
                          hTailBlockCompile hTailBlocks hTailCalls
                          (targetFuel := tailTargetFuel)
                    · have hEq : tailTargetFuel = targetFuel := by
                        omega
                      subst tailTargetFuel
                      exact
                        adequateWithinFuel_block generated hProgramWF
                          hContext hRestWF hTailActivation
                          hTailEntryBefore hTailRegularBefore
                          hTailBoundary hTailEntryRejected
                          hTailBlockCompile hTailBlocks hTailCalls
                          (targetFuel := targetFuel)
  termination_by (targetFuel, compilerFuel, 1)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | apply Prod.Lex.right
        apply Prod.Lex.left
        omega

/--
Generated-context backward adequacy for every well-formed Structured statement.
-/
theorem adequateWithinFuel_stmt
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {canBreak canContinue canLeave : Bool}
    (hProgramWF : program.WF)
    (hContext :
      SourceContext program ctx tokens
        canBreak canContinue canLeave)
    (hWF :
      Structured.Stmt.WF
        canBreak canContinue canLeave stmt)
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hEntryBefore :
      OutcomeSimulation.LabelBeforeSupply entry supply)
    (hRegular :
      OutcomeSimulation.RegularAtSupply regular supply)
    (hBoundary :
      OutcomeSimulation.RecursiveBoundary
        cfg source tokens accept supply regular)
    (hEntryRejected :
      OutcomeSimulation.EntryRejected
        cfg source tokens accept entry input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel stmt source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens targetFuel := by
  cases compilerFuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases hWF with
      | code =>
          exact adequateWithinFuel_code hCompile hBlocks
      | if_ hBodyWF =>
          apply
            adequateWithinFuel_if hActivation hRegular hBoundary
              hCompile hBlocks hCalls
          intro bodyInput bodyResult afterCond hBodyCompile
            hBodyBlocks hBodyCalls hReturns hBodyActivation
            hBodyBoundary hBodyEntryRejected bodyTargetFuel hBodyFuel
          exact
            adequateWithinFuel_block generated hProgramWF
              hContext hBodyWF hBodyActivation
              (by
                simp [OutcomeSimulation.LabelBeforeSupply,
                  LabelSupply.label])
              hRegular.before_succ hBodyBoundary hBodyEntryRejected
              hBodyCompile hBodyBlocks hBodyCalls
              (targetFuel := bodyTargetFuel)
      | switch hCasesWF hDefaultWF =>
          cases compilerFuel with
          | zero =>
              obtain
                  ⟨_valueShape, _valueSlot, _caseResult, _defaultResult,
                    _hType, _hSource, _hHead, hCasesCompile,
                    _hDefaultCompile, _hResult⟩ :=
                TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
                  hCompile
              simp [TypedCfgCompiler.compileCasesFuel?] at hCasesCompile
          | succ switchFuel =>
              apply
                adequateWithinFuel_switch
                  hActivation hRegular hBoundary hCasesWF hDefaultWF
                  hCompile hBlocks hCalls
              intro selected afterScrutinee stack value
                bodyCompilerFuel bodySupply bodyEntry bodyShape bodyResult
                hBodyCompile hBodyBlocks hBodyCalls hSelectedWF hBodyEntryBefore
                hBodyEntryRejected hReturns hBodyActivation hBodySupply
                _hBodyRegular hBodyBoundary bodyTargetFuel hBodyFuel
              exact
                adequateWithinFuel_block generated hProgramWF
                  hContext hSelectedWF hBodyActivation
                  hBodyEntryBefore
                  (hRegular.before_succ.mono hBodySupply)
                  hBodyBoundary hBodyEntryRejected
                  hBodyCompile hBodyBlocks hBodyCalls
                  (targetFuel := bodyTargetFuel)
      | for_ hInitWF hPostWF hBodyWF =>
          apply
            adequateWithinFuel_for
              hContext hInitWF hPostWF hBodyWF
              hActivation hEntryBefore hRegular hBoundary
              hEntryRejected hCompile hBlocks hCalls
          intro block blockCtx blockSupply blockEntry blockRegular
            blockInput blockResult blockSource blockAccept
            blockCanBreak blockCanContinue blockCanLeave
            hBlockContext hBlockWF hBlockActivation
            hBlockEntryBefore hBlockRegularBefore hBlockBoundary
            hBlockEntryRejected hBlockCompile hBlockBlocks hBlockCalls
            blockTargetFuel hBlockFuel
          by_cases hStrict : blockTargetFuel < targetFuel
          · exact
              adequateWithinFuel_block generated hProgramWF
                hBlockContext hBlockWF hBlockActivation
                hBlockEntryBefore hBlockRegularBefore
                hBlockBoundary hBlockEntryRejected
                hBlockCompile hBlockBlocks hBlockCalls
                (targetFuel := blockTargetFuel)
          · have hEq : blockTargetFuel = targetFuel := by
              omega
            subst blockTargetFuel
            exact
              adequateWithinFuel_block generated hProgramWF
                hBlockContext hBlockWF hBlockActivation
                hBlockEntryBefore hBlockRegularBefore
                hBlockBoundary hBlockEntryRejected
                hBlockCompile hBlockBlocks hBlockCalls
                (targetFuel := targetFuel)
      | brk hAllowed =>
          exact
            adequateWithinFuel_brk hContext hAllowed hCompile hBlocks
      | cont hAllowed =>
          exact
            adequateWithinFuel_cont hContext hAllowed hCompile hBlocks
      | leave hAllowed =>
          exact
            adequateWithinFuel_leave hContext hAllowed hCompile hBlocks
      | call =>
          apply
            adequateWithinFuel_call generated hContext hBoundary
              hCompile hBlocks hCalls hProgramWF
          intro proc fragment callSource hLookup hFragmentBlocks
            hFragmentCalls hProcContext hProcActivation
            hProcEntryBefore hProcRegularBefore hProcBoundary
            hProcEntryRejected bodyTargetFuel hBodyFuel
          have hFragmentCompile :
              TypedCfgCompiler.compileBlockFuel?
                  (TypedCfgCompiler.blockFuel proc.body + 1)
                  proc.body
                  { procs := program.procs
                    leaveLabel? := some (ProcLabel.exit proc.name)
                    leaveShape? :=
                      some (TypedCfgCompiler.Shape.procExit proc) }
                  fragment.supply fragment.entry fragment.input
                  (ProcLabel.exit proc.name) =
                some fragment.result := by
            simpa [TypedCfgCompiler.compileBlock?] using fragment.compile
          exact
            adequateWithinFuel_block generated hProgramWF
              hProcContext
              (Structured.Program.procWF_of_lookup?
                hProgramWF hLookup).2.2
              hProcActivation hProcEntryBefore hProcRegularBefore
              hProcBoundary hProcEntryRejected
              hFragmentCompile hFragmentBlocks hFragmentCalls
              (targetFuel := bodyTargetFuel)
      | terminal =>
          exact
            adequateWithinFuel_terminal
              hCompile hBlocks generated.wellTyped
  termination_by (targetFuel, compilerFuel, 0)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | apply Prod.Lex.right
        apply Prod.Lex.left
        omega

end

end Generated

end ObserverAdequacy
end Structured
end EvmCompiler
