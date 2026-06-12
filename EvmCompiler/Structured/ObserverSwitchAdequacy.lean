import EvmCompiler.Structured.ObserverAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Switch

/--
Fixed-target-fuel interface for checked switches.
-/
theorem adequateWithinFuel_switch_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (targetFuel : Nat)
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hRegular : continuations.regular = regular)
    (hDispatchEntryNotAccepted :
      ∀ caseIdx remaining,
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (TypedCfgCompilerFacts.Switch.casesEntryLabel
            supply caseIdx remaining))
    (hCaseEntryNotAccepted :
      ∀ caseIdx,
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (TypedCfgCompiler.switchCaseLabel supply caseIdx))
    (hCaseBodyEntryNotAccepted :
      ∀ caseIdx,
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (TypedCfgCompiler.switchBodyLabel supply caseIdx))
    (hDefaultBodyEntryNotAccepted :
      ∀ generatedSupply,
        supply ≤ generatedSupply →
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (.generated generatedSupply 2000))
    (hBodyAdequate :
      ∀ {selected : Structured.Block}
        {afterScrutinee : ObserverSemantics.State transcript}
        {stack : EvmYul.Stack Word} {value : Word}
        {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        bodyTargetFuel,
        ObserverSemantics.Code.run scrutinee source =
          .ok afterScrutinee →
        afterScrutinee.source.evm.stack.pop = some (stack, value) →
        Structured.Switch.select value cases defaultBody =
          some selected →
        (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack })).source.returns =
          source.source.returns →
        OutcomeSimulation.ActivationInput tokens bodyShape →
        supply + 1 ≤ bodySupply →
        bodyTargetFuel < targetFuel →
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram bodyResult globalCalls →
        OutcomeSimulation.LabelBeforeSupply bodyEntry bodySupply →
        OutcomeSimulation.EntryRejected cfg
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens accept bodyEntry bodyShape →
        OutcomeSimulation.AdequateWithinFuel
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel selected
              (afterScrutinee.withSource
                (afterScrutinee.source.withEVM
                  { afterScrutinee.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept bodyEntry bodyShape
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens bodyTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.switch scrutinee cases defaultBody) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens
      targetFuel := by
  intro hAccept target trace traceFinal
    targetOutcome hRel hReach
  exact
    outcome_switch_of_compileStmtFuel?_and_firstReaches
      hActivation hCompile hBlocks hCalls hRegular hAccept
      hDispatchEntryNotAccepted hCaseEntryNotAccepted
      hCaseBodyEntryNotAccepted hDefaultBodyEntryNotAccepted
      hRel hReach hBodyAdequate

/--
Unbounded switch adequacy recovered from the fixed-fuel rule.
-/
theorem adequateWithin_switch_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hActivation : OutcomeSimulation.ActivationInput tokens input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hCalls :
      TypedCfgPreservation.CallsInProgram result globalCalls)
    (hRegular : continuations.regular = regular)
    (hDispatchEntryNotAccepted :
      ∀ caseIdx remaining,
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (TypedCfgCompilerFacts.Switch.casesEntryLabel
            supply caseIdx remaining))
    (hCaseEntryNotAccepted :
      ∀ caseIdx,
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (TypedCfgCompiler.switchCaseLabel supply caseIdx))
    (hCaseBodyEntryNotAccepted :
      ∀ caseIdx,
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (TypedCfgCompiler.switchBodyLabel supply caseIdx))
    (hDefaultBodyEntryNotAccepted :
      ∀ generatedSupply,
        supply ≤ generatedSupply →
        OutcomeSimulation.SameActivationEntryRejected cfg source tokens accept
          (.generated generatedSupply 2000))
    (hBodyAdequate :
      ∀ {selected : Structured.Block}
        {afterScrutinee : ObserverSemantics.State transcript}
        {stack : EvmYul.Stack Word} {value : Word}
        {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        ObserverSemantics.Code.run scrutinee source =
          .ok afterScrutinee →
        afterScrutinee.source.evm.stack.pop = some (stack, value) →
        Structured.Switch.select value cases defaultBody =
          some selected →
        (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack })).source.returns =
          source.source.returns →
        OutcomeSimulation.ActivationInput tokens bodyShape →
        supply + 1 ≤ bodySupply →
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        TypedCfgPreservation.CallsInProgram bodyResult globalCalls →
        OutcomeSimulation.LabelBeforeSupply bodyEntry bodySupply →
        OutcomeSimulation.EntryRejected cfg
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens accept bodyEntry bodyShape →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel selected
              (afterScrutinee.withSource
                (afterScrutinee.source.withEVM
                  { afterScrutinee.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept bodyEntry bodyShape
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.switch scrutinee cases defaultBody) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  exact
    adequateWithinFuel_switch_of_compileStmtFuel?
      targetFuel hActivation hCompile hBlocks hCalls hRegular
      hDispatchEntryNotAccepted hCaseEntryNotAccepted
      hCaseBodyEntryNotAccepted hDefaultBodyEntryNotAccepted
      (fun bodyTargetFuel hScrutinee hPop hSelect hReturns
          hBodyActivation hBodySupply _hFuel
          hBodyCompile hBodyBlocks hBodyCalls hEntryBefore hEntryRejected =>
        (hBodyAdequate hScrutinee hPop hSelect hReturns
          hBodyActivation hBodySupply
          hBodyCompile hBodyBlocks hBodyCalls hEntryBefore
          hEntryRejected).fuel
          bodyTargetFuel)
      hAccept hRel hReach

end Switch
end ObserverAdequacy
end Structured
end EvmCompiler
