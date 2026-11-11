import EvmCompiler.Structured.InteractionSwitchPreservation
import EvmCompiler.Structured.InteractionStaticCost

namespace EvmCompiler
namespace Structured
namespace InteractionSwitchPreservation
namespace Switch

/--
Source-budgeted routing through a present default arm.

`callBase` is the dense call-token counter the enclosing switch reached before
the default arm (`ctx.callBase + caseResult.calls.length`). It is a compiler
spectator: it selects which fragment was compiled, never what the fragment
means, so every semantic position below stays at `ctx`.
-/
theorem openRun_default_some_bounded_under_of_compileDefaultFuel?
    {compilerFuel sourceFuel bodyBudget : Nat}
    {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {callBase : Nat}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) { ctx with callBase := callBase } supply entry
          valueShape bodyShape regular =
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
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            { ctx with callBase := callBase }
            (supply + 1) (.generated supply 2000)
            bodyShape regular =
          some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        bodyResult.requireFallthrough? bodyShape = some () ->
        enclosingResult.fallthrough? = some bodyShape ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg (.generated supply 2000) ctx regular
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
            (source.withEVM { source.evm with stack := stack }))
          bodyBudget policy) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
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
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.change_result_of_required_fallthrough
      hRequire hEnclosingFallthrough hBodyPreserves
  apply
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.prepend_closed_jump
  · intro target hStateRel
    exact
      openStep_pop_jump
        (entry := entry) (label := .generated supply 2000)
        (input := valueShape) (output := bodyShape)
        hBlocks (by simp) hPopType hStateRel hPop
  · rfl
  · exact hBodyEntryNoStop
  · exact hBodyLifted

theorem openRun_default_some_runtime_error_bounded_under_of_compileDefaultFuel?
    {compilerFuel sourceFuel bodyBudget : Nat}
    {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {callBase : Nat}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) { ctx with callBase := callBase } supply entry
          valueShape bodyShape regular =
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
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            { ctx with callBase := callBase }
            (supply + 1) (.generated supply 2000)
            bodyShape regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        bodyResult.requireFallthrough? bodyShape = some () ->
        enclosingResult.fallthrough? = some bodyShape ->
        InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
          bodyResult cfg (.generated supply 2000) ctx regular
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun sourceProgram sourceFuel body
            (source.withEVM { source.evm with stack := stack }))
          bodyBudget policy) :
    InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
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
    InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.change_result_of_required_fallthrough
      hRequire hEnclosingFallthrough hBodyPreserves
  apply
    InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.prepend_closed_jump
  · intro target hStateRel
    exact
      openStep_pop_jump
        (entry := entry) (label := .generated supply 2000)
        (input := valueShape) (output := bodyShape)
        hBlocks (by simp) hPopType hStateRel hPop
  · exact hBodyEntryNoStop
  · exact hBodyLifted

/--
Source-budgeted selected-case routing under activation-aware recursive label
ownership. Only the selected block contributes open effects.
-/
theorem openRun_cases_some_bounded_under_of_compileCasesFuel?
    {compilerFuel sourceFuel bodyBudget : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {callBase : Nat}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases
          { ctx with callBase := callBase }
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
      forall {bodyCompilerFuel caseSupply caseIdx caseCallBase : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected
            { ctx with callBase := caseCallBase }
            caseSupply (TypedCfgCompiler.switchBodyLabel base caseIdx)
            bodyShape regular =
          some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        base + 1 <= caseSupply ->
        bodyResult.requireFallthrough? bodyShape = some () ->
        enclosingResult.fallthrough? = some bodyShape ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg
          (TypedCfgCompiler.switchBodyLabel base caseIdx) ctx regular
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          bodyBudget policy)
    (hDefault :
      defaultBody = some selected ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          enclosingResult cfg (LabelSupply.label base 1) ctx regular
          source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          (bodyBudget + 1) policy) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      enclosingResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram sourceFuel selected
        (source.withEVM { source.evm with stack := stack }))
      (bodyBudget + cases.length + 1) policy := by
  induction cases generalizing
      compilerFuel callBase supply idx result selected with
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
              InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.change_result_of_required_fallthrough
                hRequire hEnclosingFallthrough hBodyPreserves
            have hBodyPadded :=
              InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.mono_budget
                hBodyLifted
                (show bodyBudget <= bodyBudget + rest.length by omega)
            have hFromCase :
                InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchCaseLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyBudget + rest.length) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.prepend_closed_jump
              · intro target hStateRel
                exact
                  openStep_pop_jump
                    (entry := TypedCfgCompiler.switchCaseLabel base idx)
                    (label := TypedCfgCompiler.switchBodyLabel base idx)
                    (input := valueShape) (output := bodyShape)
                    hBlocks (by simp [hResult]) hPopType hStateRel hPop
              · rfl
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
                InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  (((bodyBudget + rest.length) + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.prepend_closed_jump
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
              · rfl
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
            have hTailCompileBase :
                TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest
                    { ctx with
                      callBase := callBase + bodyResult.calls.length }
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular =
                  some tail := by
              simpa [TypedCfgCompiler.Context.advance] using hTailCompile
            have hTailPreserves :=
              ih hTailCompileBase
                (Nat.le_trans hSupply
                  (TypedCfgCompilerFacts.Supply.block_next_ge hBodyCompile))
                hTailBlocks hTailCalls hTailSelect hCase hDefault
            have hSkipped :
                InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel selected
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyBudget + rest.length + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.prepend_closed_jump
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
              · rfl
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

theorem openRun_cases_some_runtime_error_bounded_under_of_compileCasesFuel?
    {compilerFuel sourceFuel bodyBudget : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {callBase : Nat}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases
          { ctx with callBase := callBase }
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
      forall {bodyCompilerFuel caseSupply caseIdx caseCallBase : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected
            { ctx with callBase := caseCallBase }
            caseSupply (TypedCfgCompiler.switchBodyLabel base caseIdx)
            bodyShape regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        base + 1 <= caseSupply ->
        bodyResult.requireFallthrough? bodyShape = some () ->
        enclosingResult.fallthrough? = some bodyShape ->
        InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
          bodyResult cfg
          (TypedCfgCompiler.switchBodyLabel base caseIdx) ctx regular
          (source.withEVM { source.evm with stack := stack }) tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          bodyBudget policy)
    (hDefault :
      defaultBody = some selected ->
        InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
          enclosingResult cfg (LabelSupply.label base 1) ctx regular
          source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel selected
            (source.withEVM { source.evm with stack := stack }))
          (bodyBudget + 1) policy) :
    InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
      enclosingResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram sourceFuel selected
        (source.withEVM { source.evm with stack := stack }))
      (bodyBudget + cases.length + 1) policy := by
  induction cases generalizing
      compilerFuel callBase supply idx result selected with
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
              InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.change_result_of_required_fallthrough
                hRequire hEnclosingFallthrough hBodyPreserves
            have hBodyPadded :=
              InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.mono_budget
                hBodyLifted
                (show bodyBudget <= bodyBudget + rest.length by omega)
            have hFromCase :
                InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchCaseLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyBudget + rest.length) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.prepend_closed_jump
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
                InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel body
                    (source.withEVM { source.evm with stack := stack }))
                  (((bodyBudget + rest.length) + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.prepend_closed_jump
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
            have hTailCompileBase :
                TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest
                    { ctx with
                      callBase := callBase + bodyResult.calls.length }
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular =
                  some tail := by
              simpa [TypedCfgCompiler.Context.advance] using hTailCompile
            have hTailPreserves :=
              ih hTailCompileBase
                (Nat.le_trans hSupply
                  (TypedCfgCompilerFacts.Supply.block_next_ge hBodyCompile))
                hTailBlocks hTailCalls hTailSelect hCase hDefault
            have hSkipped :
                InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
                  enclosingResult cfg
                  (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                  source tokens
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceFuel selected
                    (source.withEVM { source.evm with stack := stack }))
                  ((bodyBudget + rest.length + 1) + 1) policy := by
              apply
                InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.prepend_closed_jump
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

/-- Activation-aware source-budgeted routing when no switch body is selected. -/
theorem openRun_cases_none_bounded_under_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {callBase : Nat}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result enclosingResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases
          { ctx with callBase := callBase }
          base supply idx valueShape bodyShape regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Structured.Switch.select value cases defaultBody = none)
    (hRegular : TypedCfgCompilerFacts.RegularAtSupply regular base)
    (hBoundary :
      InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
        cfg source.returns tokens policy base regular)
    (hValueActivation :
      TypedCfgPreservation.ActivationInput tokens valueShape)
    (hValueFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        valueShape source.evm.stack.length)
    (hDefaultEntryNoStop :
      forall targetAfter,
        TypedCfgPreservation.StateRel source tokens targetAfter ->
          policy (LabelSupply.label base 1) targetAfter = false)
    (hDefault :
      defaultBody = none ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          enclosingResult cfg (LabelSupply.label base 1) ctx regular
          source tokens
          (Simulation.Interaction.pure
            (Structured.Outcome.regular
              (source.withEVM { source.evm with stack := stack })))
          1 policy) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      enclosingResult cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases) ctx
      regular source tokens
      (Simulation.Interaction.pure
        (Structured.Outcome.regular
          (source.withEVM { source.evm with stack := stack })))
      (cases.length + 1) policy := by
  induction cases generalizing compilerFuel callBase supply idx result with
  | nil =>
      cases compilerFuel with
      | zero => simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefaultNone : defaultBody = none := by
            simpa [Structured.Switch.select] using hSelect
          simpa [TypedCfgCompilerFacts.Switch.casesEntryLabel] using
            hDefault hDefaultNone
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero => simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          obtain
              ⟨bodyResult, tail, _hBodyCompile, _hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hResult, hMem]
          have hNe : caseValue ≠ value := by
            intro hEq
            simp [Structured.Switch.select, hEq] at hSelect
          have hTailSelect :
              Structured.Switch.select value rest defaultBody = none := by
            simpa [Structured.Switch.select, hNe] using hSelect
          have hTailCompileBase :
              TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest
                  { ctx with
                    callBase := callBase + bodyResult.calls.length }
                  base bodyResult.next (idx + 1) valueShape bodyShape
                  regular =
                some tail := by
            simpa [TypedCfgCompiler.Context.advance] using hTailCompile
          have hTailPreserves :=
            ih hTailCompileBase hTailBlocks hTailSelect
          have hSkipped :
              InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
                enclosingResult cfg
                (TypedCfgCompiler.switchTestLabel base idx) ctx regular
                source tokens
                (Simulation.Interaction.pure
                  (Structured.Outcome.regular
                    (source.withEVM { source.evm with stack := stack })))
                ((rest.length + 1) + 1) policy := by
            apply
              InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.prepend_closed_jump
            · intro target hStateRel
              rcases
                  openStep_test
                    (testLabel :=
                      TypedCfgCompiler.switchTestLabel base idx)
                    (caseLabel :=
                      TypedCfgCompiler.switchCaseLabel base idx)
                    (nextTest :=
                      TypedCfgCompilerFacts.Switch.nextTestLabel
                        base idx rest)
                    (caseValue := caseValue) (value := value)
                    hBlocks (by simp [hResult]) hHead hStateRel hPop with
                ⟨targetAfter, hTargetRun, hAfterRel⟩
              refine ⟨targetAfter, ?_, hAfterRel⟩
              simpa [hNe] using hTargetRun
            · rfl
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

namespace Stmt

/-- Source-budgeted successful-execution preservation for a compiled switch. -/
theorem openRun_switch_bounded_under_of_compileStmtFuel?
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
    (hStops :
      forall {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome ->
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hBody :
      forall {bodyCompilerFuel bodySupply bodyCallBase : Nat}
        {bodyEntry : Assembly.Label} {bodyInput : TypedCfg.Shape}
        {body : Structured.Block}
        {bodyResult : TypedCfgCompiler.Result}
        {afterPop : RunState} {value : Word},
        Structured.Switch.select value cases defaultBody = some body ->
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body
            { ctx with callBase := bodyCallBase }
            bodySupply bodyEntry bodyInput regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        supply + 1 <= bodySupply ->
        afterPop.returns = source.returns ->
        TypedCfgCompiler.Shape.SourceFrameFits
          bodyInput afterPop.evm.stack.length ->
        bodyResult.requireFallthrough? bodyInput = some () ->
        result.fallthrough? = some bodyInput ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg bodyEntry ctx regular afterPop tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterPop)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel body)
          policy) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (InteractionStaticCost.stmtBudget sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody))
      policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨valueShape, valueSlot, caseResult, defaultResult,
        hType, hSource, hValue, hCasesCompileRaw,
        hDefaultCompileRaw, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
      hCompile
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
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases
          { ctx with callBase := ctx.callBase }
          supply (supply + 1) 0 valueShape bodyShape regular =
        some caseResult := by
    simpa [bodyShape] using hCasesCompileRaw
  have hDefaultCompile :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel defaultBody
          { ctx with
            callBase := ctx.callBase + caseResult.calls.length }
          caseResult.next (LabelSupply.label supply 1)
          valueShape bodyShape regular = some defaultResult := by
    simpa [bodyShape, TypedCfgCompiler.Context.advance] using
      hDefaultCompileRaw
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
      have hDefaultFallthrough :
          defaultResult.fallthrough? = some bodyShape :=
        TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
          hPopType hDefaultCompile
      have hDefaultRequire :
          defaultResult.requireFallthrough? bodyShape = some () :=
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
          (Or.inr hDefaultFallthrough)
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
            (TypedCfg.InteractionSemantics.Program.openStep
              cfg entry target) := by
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
            transcript (.ok sourceOutcome) := by
        simpa [
          InteractionSemantics.Stmt.openRun,
          EffectSemantics.Control.Stmt.run,
          EffectSemantics.Ordinary.runStateModel_evm,
          EffectSemantics.Ordinary.runStateModel_withEVM] using hSourceExec
      rcases Simulation.Interaction.Executes.bind_cases hSourceExec' with
        hSourceError |
          ⟨afterScrutinee, headTranscript, restTranscript,
            hTranscript, hScrutineeExec, hRestExec⟩
      · rcases hSourceError with
          ⟨err, hOutcome, _hScrutineeError⟩
        cases hOutcome
      · subst transcript
        obtain ⟨targetDone, hTargetHeadExec, hDone⟩ :=
          Simulation.Interaction.Rel.executes
            hHeadWithReturns hScrutineeExec
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
                        policy (LabelSupply.label supply 1)
                          targetAfter = false := by
                  intro targetAfter hTargetRel
                  have hDefaultShape :
                      TypedCfgPreservation.LabelShape cfg
                        (LabelSupply.label supply 1) valueShape :=
                    TypedCfgPreservation.LabelShape.of_hasEntry
                      (TypedCfgCompilerFacts.Switch.default_hasEntry
                        hPopType hDefaultCompile) hDefaultBlocks
                  exact
                    hAfterBoundary.eq_false_of_stateRel
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
                      InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
                        result cfg firstTest ctx regular afterScrutinee tokens
                        routeRun routeBudget policy)
                    (hRest :
                      Simulation.Interaction.Executes routeRun restTranscript
                        (.ok sourceOutcome)) :
                    exists targetFuel remaining targetFinal,
                      targetFuel <=
                        InteractionStaticCost.stmtBudget sourceProgram
                          (sourceFuel + 1)
                          (.switch scrutinee cases defaultBody) /\
                      Simulation.Interaction.Executes
                        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                          policy cfg targetFuel entry target)
                        (headTranscript ++ restTranscript)
                        (.ok (.stopped remaining targetFinal)) /\
                      InteractionControlPreservation.OpenOutcome.Rel
                        result ctx regular source.returns tokens
                        sourceOutcome targetFinal := by
                  obtain
                      ⟨routeFuel, remaining, targetFinal, hRouteFuel,
                        hTargetRouteExec, hRouteRel⟩ :=
                    hRoute targetAfterScrutinee hAfterRel
                      restTranscript sourceOutcome hRest
                  have hContinuationExec :
                      Simulation.Interaction.Executes
                        (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
                          policy cfg routeFuel
                          (.jump firstTest targetAfterScrutinee))
                        restTranscript (.ok (.stopped remaining targetFinal)) := by
                    simpa [
                      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                      hNoStop] using hTargetRouteExec
                  have hCombined :=
                    Simulation.Interaction.Executes.bind_ok
                      hTargetHeadExec hContinuationExec
                  have hTargetExec :
                      Simulation.Interaction.Executes
                        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                          policy cfg (routeFuel + 1) entry target)
                        (headTranscript ++ restTranscript)
                        (.ok (.stopped remaining targetFinal)) := by
                    rw [
                      TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                    exact hCombined
                  exact
                    ⟨routeFuel + 1, remaining, targetFinal,
                      by
                        rw [InteractionStaticCost.stmtBudget_switch_succ]
                        dsimp [routeBudget] at hRouteFuel
                        omega,
                      hTargetExec,
                      by simpa [hReturnsEq] using hRouteRel⟩
                cases hSelect :
                    Structured.Switch.select value cases defaultBody with
                | none =>
                    have hDefaultRoute
                        (hDefaultNone : defaultBody = none) :
                        InteractionControlPreservation.OpenOutcome.PreservesUnder
                          result cfg (LabelSupply.label supply 1) ctx
                          regular .stop afterScrutinee tokens
                          (Simulation.Interaction.pure
                            (Structured.Outcome.regular
                              (afterScrutinee.withEVM
                                { afterScrutinee.evm with stack := stack })))
                          1 policy := by
                      have hCompileNone :
                          TypedCfgCompiler.compileDefaultFuel?
                              (bodyCompilerFuel + 1) none
                              { ctx with
                                callBase :=
                                  ctx.callBase + caseResult.calls.length }
                              caseResult.next (LabelSupply.label supply 1)
                              valueShape bodyShape regular =
                            some defaultResult := by
                        simpa [hDefaultNone] using hDefaultCompile
                      have hBase :=
                        Switch.openRun_default_none_under_of_compileDefaultFuel?
                          (result := defaultResult) (regularExit := .stop)
                          (source := afterScrutinee) (tokens := tokens)
                          (policy := policy) hCompileNone hDefaultBlocks
                          hPopType hPop hBodyFits
                          (fun {sourceOutcome} {targetOutcome} hRel => by
                            have hWholeRel :=
                              InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                                hDefaultRequire hFallthrough hRel
                            exact hStops (by
                              simpa [hReturnsEq] using hWholeRel))
                      exact
                        InteractionControlPreservation.OpenOutcome.PreservesUnder.change_result_of_required_fallthrough
                          hDefaultRequire hFallthrough hBase
                    have hDefaultBounded
                        (hDefaultNone : defaultBody = none) :=
                      InteractionControlPreservation.OpenOutcome.PreservesUnder.boundedExec
                        (hDefaultRoute hDefaultNone)
                    have hCasesNone :=
                      Switch.openRun_cases_none_bounded_under_of_compileCasesFuel?
                        (enclosingResult := result)
                        hCasesCompile hCaseBlocks hValue hPopType hPop
                        hSelect hRegular hAfterBoundary hValueActivation
                        hAfterFits hDefaultEntryNoStop
                        (fun hDefaultNone => hDefaultBounded hDefaultNone)
                    have hCasesPadded :=
                      InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.mono_budget
                        hCasesNone
                        (show cases.length + 1 <= routeBudget by
                          dsimp [routeBudget]
                          omega)
                    exact
                      finishRoute hCasesPadded
                        (by simpa [hPop, hSelect] using hRestExec)
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
                        forall {caseBodyCompilerFuel caseSupply caseIdx
                            caseCallBase : Nat}
                          {bodyResult : TypedCfgCompiler.Result},
                          TypedCfgCompiler.compileBlockFuel?
                              caseBodyCompilerFuel selected
                              { ctx with callBase := caseCallBase } caseSupply
                              (TypedCfgCompiler.switchBodyLabel supply caseIdx)
                              bodyShape regular = some bodyResult ->
                          TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
                          TypedCfgPreservation.CallsInProgram
                            bodyResult generatedCalls ->
                          supply + 1 <= caseSupply ->
                          bodyResult.requireFallthrough? bodyShape = some () ->
                          result.fallthrough? = some bodyShape ->
                          InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
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
                      intro caseBodyCompilerFuel caseSupply caseIdx
                        caseCallBase bodyResult
                        hBodyCompile hBodyBlocks hBodyCalls hBodySupply
                        hBodyRequire hResultFallthrough
                      apply
                        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.mono_budget
                          (hBody hSelect hBodyCompile hBodyBlocks hBodyCalls
                            hBodySupply (by
                              simpa [RunState.withEVM] using hReturnsEq)
                            hBodyFits hBodyRequire hResultFallthrough)
                      exact hSelectedBudget
                    have hDefaultRoute
                        (hDefaultSelected : defaultBody = some selected) :
                        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
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
                              (bodyCompilerFuel + 1) (some selected)
                              { ctx with
                                callBase :=
                                  ctx.callBase + caseResult.calls.length }
                              caseResult.next (LabelSupply.label supply 1)
                              valueShape bodyShape regular =
                            some defaultResult := by
                        simpa [hDefaultSelected] using hDefaultCompile
                      apply
                        Switch.openRun_default_some_bounded_under_of_compileDefaultFuel?
                          (enclosingResult := result)
                          (bodyBudget :=
                            InteractionStaticCost.switchBodyBudget
                              sourceProgram sourceFuel cases defaultBody)
                          hCompileSome hDefaultBlocks hDefaultCalls hPopType hPop
                          hFallthrough
                      · intro targetAfter hTargetRel
                        obtain
                            ⟨bodyResult, hBodyCompile,
                              _hRequire, hDefaultResult⟩ :=
                          TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
                            hPopType hCompileSome
                        have hBodyBlocks :
                            TypedCfgPreservation.BlocksInProgram
                              bodyResult cfg := by
                          intro block hMem
                          apply hDefaultBlocks block
                          simp [hDefaultResult, hMem]
                        have hBodyShape :
                            TypedCfgPreservation.LabelShape cfg
                              (.generated caseResult.next 2000)
                              bodyShape :=
                          TypedCfgPreservation.LabelShape.of_compileBlockFuel?
                            hBodyCompile hBodyBlocks
                        have hDefaultBodyBoundary :
                            InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
                              cfg
                                (afterScrutinee.withEVM
                                  { afterScrutinee.evm with stack := stack }).returns
                                tokens policy supply regular :=
                          hAfterBoundary.congr_returns rfl
                        exact
                          hDefaultBodyBoundary.eq_false_of_stateRel
                            (scope := caseResult.next) (tag := 2000)
                            (Nat.le_trans (Nat.le_succ supply) hCasesNext)
                            ((hRegular.before_succ.mono hCasesNext).generated_ne
                              (Nat.le_refl caseResult.next))
                            hBodyShape hBodyActivation hTargetRel hBodyFits
                      · intro bodyResult hBodyCompile hBodyBlocks hBodyCalls
                          hBodyRequire hResultFallthrough
                        apply
                          InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.mono_budget
                            (hBody hSelect hBodyCompile hBodyBlocks hBodyCalls
                              (Nat.le_trans hCasesNext
                                (Nat.le_succ caseResult.next))
                              (by simpa [RunState.withEVM] using hReturnsEq)
                              hBodyFits hBodyRequire hResultFallthrough)
                        exact hSelectedBudget
                    have hCasesSome :=
                      Switch.openRun_cases_some_bounded_under_of_compileCasesFuel?
                        (enclosingResult := result)
                        (bodyBudget :=
                          InteractionStaticCost.switchBodyBudget
                            sourceProgram sourceFuel cases defaultBody)
                        hCasesCompile (Nat.le_refl (supply + 1))
                        hCaseBlocks hCaseCalls hValue hPopType hPop
                        hSelect hFallthrough hRegular hAfterBoundary
                        hValueActivation hAfterFits hBodyActivation hBodyFits
                        hDefaultEntryNoStop hCaseRoute hDefaultRoute
                    exact
                      finishRoute hCasesSome
                        (by simpa [hPop, hSelect] using hRestExec)

theorem openRun_switch_runtime_error_bounded_under_of_compileStmtFuel?
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
      forall {bodyCompilerFuel bodySupply bodyCallBase : Nat}
        {bodyEntry : Assembly.Label} {bodyInput : TypedCfg.Shape}
        {body : Structured.Block}
        {bodyResult : TypedCfgCompiler.Result}
        {afterPop : RunState} {value : Word},
        Structured.Switch.select value cases defaultBody = some body ->
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body
            { ctx with callBase := bodyCallBase }
            bodySupply bodyEntry bodyInput regular = some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        supply + 1 <= bodySupply ->
        afterPop.returns = source.returns ->
        TypedCfgCompiler.Shape.SourceFrameFits
          bodyInput afterPop.evm.stack.length ->
        bodyResult.requireFallthrough? bodyInput = some () ->
        result.fallthrough? = some bodyInput ->
        InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
          bodyResult cfg bodyEntry ctx regular afterPop tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterPop)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel body)
          policy) :
    InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (InteractionStaticCost.stmtBudget sourceProgram (sourceFuel + 1)
        (.switch scrutinee cases defaultBody))
      policy := by
  intro target hStateRel transcript sourceError hRuntime hSourceExec
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
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases
          { ctx with callBase := ctx.callBase }
          supply (supply + 1) 0 valueShape bodyShape regular =
        some caseResult := by
    simpa [bodyShape] using hCasesCompileRaw
  have hDefaultCompile :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel defaultBody
          { ctx with
            callBase := ctx.callBase + caseResult.calls.length }
          caseResult.next (LabelSupply.label supply 1)
          valueShape bodyShape regular = some defaultResult := by
    simpa [bodyShape, TypedCfgCompiler.Context.advance] using
      hDefaultCompileRaw
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
            transcript (.error sourceError) := by
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
            exact ⟨1, targetError, by
              rw [InteractionStaticCost.stmtBudget_switch_succ]
              omega, hTargetExec⟩
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
                      InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
                        result cfg firstTest ctx regular afterScrutinee tokens
                        routeRun routeBudget policy)
                    (hRest :
                      Simulation.Interaction.Executes routeRun restTranscript
                        (.error sourceError)) :
                    exists targetFuel targetError,
                      targetFuel <=
                        InteractionStaticCost.stmtBudget sourceProgram
                          (sourceFuel + 1)
                          (.switch scrutinee cases defaultBody) /\
                      Simulation.Interaction.Executes
                        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                          policy cfg targetFuel entry target)
                        (headTranscript ++ restTranscript)
                        (.error targetError) := by
                  obtain ⟨routeFuel, targetError, hRouteFuel,
                      hTargetRouteExec⟩ :=
                    hRoute targetAfterScrutinee hAfterRel
                      restTranscript sourceError hRuntime hRest
                  have hContinuationExec :
                      Simulation.Interaction.Executes
                        (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
                          policy cfg routeFuel
                          (.jump firstTest targetAfterScrutinee))
                        restTranscript (.error targetError) := by
                    simpa [
                      TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                      hNoStop] using hTargetRouteExec
                  have hTargetExec :
                      Simulation.Interaction.Executes
                        (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                          policy cfg (routeFuel + 1) entry target)
                        (headTranscript ++ restTranscript)
                        (.error targetError) := by
                    rw [
                      TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                    exact Simulation.Interaction.Executes.bind_ok
                      hTargetHeadExec hContinuationExec
                  exact ⟨routeFuel + 1, targetError, by
                    rw [InteractionStaticCost.stmtBudget_switch_succ]
                    dsimp [routeBudget] at hRouteFuel
                    omega, hTargetExec⟩
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
                        forall {caseBodyCompilerFuel caseSupply caseIdx
                            caseCallBase : Nat}
                          {bodyResult : TypedCfgCompiler.Result},
                          TypedCfgCompiler.compileBlockFuel?
                              caseBodyCompilerFuel selected
                              { ctx with callBase := caseCallBase } caseSupply
                              (TypedCfgCompiler.switchBodyLabel supply caseIdx)
                              bodyShape regular = some bodyResult ->
                          TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
                          TypedCfgPreservation.CallsInProgram
                            bodyResult generatedCalls ->
                          supply + 1 <= caseSupply ->
                          bodyResult.requireFallthrough? bodyShape = some () ->
                          result.fallthrough? = some bodyShape ->
                          InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
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
                      intro caseBodyCompilerFuel caseSupply caseIdx
                        caseCallBase bodyResult
                        hBodyCompile hBodyBlocks hBodyCalls hBodySupply
                        hBodyRequire hResultFallthrough
                      apply
                        InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.mono_budget
                          (hBody hSelect hBodyCompile hBodyBlocks hBodyCalls
                            hBodySupply (by
                              simpa [RunState.withEVM] using hReturnsEq)
                            hBodyFits hBodyRequire hResultFallthrough)
                      exact hSelectedBudget
                    have hDefaultRoute
                        (hDefaultSelected : defaultBody = some selected) :
                        InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder
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
                              (bodyCompilerFuel + 1) (some selected)
                              { ctx with callBase :=
                                  ctx.callBase + caseResult.calls.length }
                              caseResult.next (LabelSupply.label supply 1)
                              valueShape bodyShape regular = some defaultResult := by
                        simpa [hDefaultSelected] using hDefaultCompile
                      apply
                        Switch.openRun_default_some_runtime_error_bounded_under_of_compileDefaultFuel?
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
                          InteractionControlPreservation.OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.mono_budget
                            (hBody hSelect hBodyCompile hBodyBlocks hBodyCalls
                              (Nat.le_trans hCasesNext
                                (Nat.le_succ caseResult.next))
                              (by simpa [RunState.withEVM] using hReturnsEq)
                              hBodyFits hBodyRequire hResultFallthrough)
                        exact hSelectedBudget
                    have hCasesSome :=
                      Switch.openRun_cases_some_runtime_error_bounded_under_of_compileCasesFuel?
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

end Stmt
end InteractionSwitchPreservation
end Structured
end EvmCompiler
