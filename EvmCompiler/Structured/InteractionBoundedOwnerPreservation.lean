import EvmCompiler.Structured.InteractionOwnerPreservation
import EvmCompiler.Structured.InteractionBoundedBlockPreservation
import EvmCompiler.Structured.InteractionBoundedBranchPreservation
import EvmCompiler.Structured.InteractionBoundedSwitchPreservation
import EvmCompiler.Structured.InteractionBoundedLoopPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionBoundedOwnerPreservation
namespace OpenOutcome

open InteractionOwnerPreservation.OpenOutcome

abbrev StopPolicy :=
  InteractionControlPreservation.OpenOutcome.StopPolicy

abbrev Rel :=
  InteractionControlPreservation.OpenOutcome.Rel

abbrev BoundedExecPreservesUnder :=
  InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder

abbrev BoundaryShapes :=
  InteractionBoundaryPreservation.OpenOutcome.BoundaryShapes

abbrev RecursiveBoundary :=
  InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary

abbrev FragmentContract :=
  InteractionOwnerPreservation.OpenOutcome.FragmentContract

abbrev StmtContract :=
  InteractionOwnerPreservation.OpenOutcome.StmtContract

/-- Source-budgeted recursive block capability at one smaller fuel ceiling. -/
def BlockOwnerAt
    (sourceFuel : Nat)
    (program : Structured.Program)
    (entryShapes : TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg) : Prop :=
  forall {blockSourceFuel compilerFuel : Nat} {block : Structured.Block}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result}
      {source : RunState} {tokens : List Word}
      {policy : StopPolicy}
      {canBreak canContinue canLeave : Bool},
    blockSourceFuel <= sourceFuel ->
    TypedCfgCompiler.compileBlockFuel? compilerFuel block ctx
        supply entry input regular = some result ->
    TypedCfgPreservation.BlocksInProgram result cfg ->
    TypedCfgPreservation.CallsInProgram result generated.calls ->
    Structured.Block.WF canBreak canContinue canLeave block ->
    block.FrameSafe ->
    Structured.ProcList.BlockCallsResolved program.procs block ->
    TypedCfgPreservation.OutcomeSimulation.ContextSupports
      ctx canBreak canContinue canLeave ->
    ctx.procs = program.procs ->
    (canLeave = true ->
      exists frame rest, source.returns = frame :: rest) ->
    FragmentContract cfg result ctx supply entry regular input
      source tokens policy ->
    BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        program blockSourceFuel block source)
      (InteractionStaticCost.blockBudget
        program blockSourceFuel block)
      policy

theorem BlockOwnerAt.mono
    {smaller larger : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    (hOwner : BlockOwnerAt larger program entryShapes cfg generated)
    (hLe : smaller <= larger) :
    BlockOwnerAt smaller program entryShapes cfg generated := by
  intro blockSourceFuel compilerFuel block ctx supply entry regular input
    result source tokens policy canBreak canContinue canLeave hBlockLe
  exact hOwner (Nat.le_trans hBlockLe hLe)

namespace Stmt

theorem code_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.code code) source)
      (InteractionStaticCost.stmtBudget program sourceFuel (.code code))
      policy := by
  simpa only [InteractionStaticCost.stmtBudget_code] using
    InteractionControlPreservation.OpenOutcome.PreservesUnder.boundedExec
      (InteractionControlPreservation.Stmt.openRun_code_under_of_compileStmtFuel?
        (sourceProgram := program) (sourceFuel := sourceFuel)
        (regularExit := .stop)
        hCompile hBlocks contract.fits contract.stops)

theorem if_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave (.if_ cond body))
    (hFrameSafe : Structured.Stmt.FrameSafe (.if_ cond body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs (.if_ cond body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.if_ cond body) source)
      (InteractionStaticCost.stmtBudget
        program (sourceFuel + 1) (.if_ cond body))
      policy := by
  cases hWF with
  | if_ hBodyWF =>
      cases hFrameSafe with
      | if_ _hCondSafe hBodySafe =>
          cases hCalls with
          | if_ hBodyCallsResolved =>
              apply
                InteractionBranchPreservation.Stmt.openRun_if_bounded_under_of_compileStmtFuel?
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation
                  contract.boundary contract.stops
              intro output bodyResult afterCond
                hBodyCompile hBodyBlocks hBodyCalls hReturns
                hBodyFits hRequire hFallthrough
              apply
                hBlockOwner (Nat.le_refl sourceFuel)
                  hBodyCompile hBodyBlocks hBodyCalls
                  hBodyWF hBodySafe hBodyCallsResolved hSupports hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt := Or.inl contract.before_succ.regular
                    before := contract.before_succ
                    activation :=
                      contract.activation.stmtFallthrough
                        hCompile hFallthrough
                    boundary :=
                      (contract.boundary.mono
                        (Nat.le_succ supply)).congr_returns hReturns.symm
                    shapes :=
                      contract.shapes.of_required_fallthrough
                        hRequire hFallthrough
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      apply contract.stops
                      have hWhole :=
                        InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hRequire hFallthrough hRel
                      simpa [hReturns] using hWhole
                    nonregular := by
                      intro childResult childRegular sourceOutcome
                        targetOutcome hMode hRel
                      apply contract.nonregular hMode
                      simpa [hReturns] using hRel }

theorem switch_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave
        (.switch scrutinee cases defaultBody))
    (hFrameSafe :
      Structured.Stmt.FrameSafe (.switch scrutinee cases defaultBody))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs
        (.switch scrutinee cases defaultBody))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program (sourceFuel + 1)
        (.switch scrutinee cases defaultBody) source)
      (InteractionStaticCost.stmtBudget program (sourceFuel + 1)
        (.switch scrutinee cases defaultBody))
      policy := by
  cases hWF with
  | switch hCasesWF hDefaultWF =>
      cases hFrameSafe with
      | switch _hScrutineeSafe hCasesSafe hDefaultSafe =>
          cases hCalls with
          | switch hCasesCalls hDefaultCalls =>
              apply
                InteractionSwitchPreservation.Stmt.openRun_switch_bounded_under_of_compileStmtFuel?
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation
                  contract.boundary contract.stops
              intro bodyCompilerFuel bodySupply bodyEntry bodyInput
                body bodyResult afterPop value hSelect hBodyCompile
                hBodyBlocks hBodyResultCalls hBodySupply hReturns
                hBodyFits hRequire hFallthrough
              have hSelectedWF :=
                Structured.Switch.wf_of_select
                  hCasesWF hDefaultWF hSelect
              have hSelectedFrameSafe :=
                TypedCfgCompilerFacts.switch_property_of_select
                  hCasesSafe hDefaultSafe hSelect
              have hSelectedCalls :=
                TypedCfgCompilerFacts.switch_property_of_select
                  hCasesCalls hDefaultCalls hSelect
              have hSupply : supply <= bodySupply :=
                Nat.le_trans (Nat.le_succ supply) hBodySupply
              have hBefore := contract.before_succ.mono hBodySupply
              apply
                hBlockOwner (Nat.le_refl sourceFuel)
                  hBodyCompile hBodyBlocks hBodyResultCalls
                  hSelectedWF hSelectedFrameSafe hSelectedCalls
                  hSupports hProcs
              · intro hCanLeave
                obtain ⟨frame, rest, hSourceEq⟩ :=
                  hSourceReturns hCanLeave
                exact ⟨frame, rest, hReturns.trans hSourceEq⟩
              · exact
                  { fits := hBodyFits
                    regularAt := Or.inl hBefore.regular
                    before := hBefore
                    activation :=
                      contract.activation.stmtFallthrough
                        hCompile hFallthrough
                    boundary :=
                      (contract.boundary.mono hSupply).congr_returns
                        hReturns.symm
                    shapes :=
                      contract.shapes.of_required_fallthrough
                        hRequire hFallthrough
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      apply contract.stops
                      have hWhole :=
                        InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hRequire hFallthrough hRel
                      simpa [hReturns] using hWhole
                    nonregular := by
                      intro childResult childRegular sourceOutcome
                        targetOutcome hMode hRel
                      apply contract.nonregular hMode
                      simpa [hReturns] using hRel }

theorem for_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF :
      Structured.Stmt.WF canBreak canContinue canLeave
        (.for_ init cond post body))
    (hFrameSafe :
      Structured.Stmt.FrameSafe (.for_ init cond post body))
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs
        (.for_ init cond post body))
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program (sourceFuel + 1)
        (.for_ init cond post body) source)
      (InteractionStaticCost.stmtBudget program (sourceFuel + 1)
        (.for_ init cond post body))
      policy := by
  cases hWF with
  | for_ hInitWF hPostWF hBodyWF =>
      cases hFrameSafe with
      | for_ hInitSafe _hCondSafe hPostSafe hBodySafe =>
          cases hCalls with
          | for_ hInitCalls hPostCalls hBodyCalls =>
              apply
                InteractionLoopPreservation.Loop.Stmt.openRun_for_bounded_under_of_compileStmtFuel?
                  hCompile hBlocks hResultCalls contract.fits
                  contract.regularAt contract.activation
                  contract.boundary contract.stops
              · intro initResult loopInput hInitCompile hInitBlocks
                  hInitResultCalls hLoopShape hInitFallthrough
                have hInitRequire :
                    initResult.requireFallthrough? loopInput = some () :=
                  TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
                    (Or.inr hInitFallthrough)
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ
                    (Nat.le_refl (supply + 1))
                have hInitShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hInitRequire hLoopShape
                apply
                  hBlockOwner (Nat.le_refl sourceFuel)
                    hInitCompile hInitBlocks hInitResultCalls
                    hInitWF hInitSafe hInitCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · exact hSourceReturns
                · simpa [
                    InteractionLoopPreservation.Loop.initStopPolicy] using
                    (show
                      FragmentContract cfg initResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        (supply + 1) entry
                        (LabelSupply.label supply 0) input source tokens
                        (InteractionLoopPreservation.Loop.initStopPolicy
                          initResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := contract.fits
                        regularAt := Or.inl hInitBefore.regular
                        before := hInitBefore
                        activation := contract.activation
                        boundary :=
                          (contract.boundary.mono
                            (Nat.le_succ supply)).push
                              hInitShapes hOuterBefore
                        shapes := hInitShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel
                        nonregular :=
                          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                            policy })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel bodySource hFuel hBodyCompile hPostCompile
                  hBodyBlocks hFacts hBodyFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply <= initResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.initSupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    hFacts.initSupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                have hBodyBoundaryBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 0)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyShapes :
                    BoundaryShapes cfg bodyResult
                      (InteractionLoopPreservation.Loop.bodyContext
                        ctx regular (LabelSupply.label supply 2)
                        branchInput)
                      (LabelSupply.label supply 2) := by
                  simpa [branchInput] using
                    (LoopContract.body_shapes contract.shapes
                      hFacts.enclosingFallthrough hFacts.bodyRequire
                      hFacts.postShape)
                have hBodyBefore :=
                  LoopContract.body_before
                    (childRegular := LabelSupply.label supply 2)
                    (postTag := 2) (branchInput := branchInput)
                    contract.before_succ hFacts.initSupply
                    (LoopContract.generated_before hFacts.initSupply)
                have hBodyBoundary :=
                  hPostBoundary.push hBodyShapes hBodyBoundaryBefore
                apply
                  hBlockOwner (Nat.le_of_lt hFuel)
                    hBodyCompile hBodyBlocks hFacts.bodyCalls
                    hBodyWF hBodySafe hBodyCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.loopBody
                      hSupports regular (LabelSupply.label supply 2)
                      branchInput)
                    (by
                      simpa [InteractionLoopPreservation.Loop.bodyContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ :=
                    hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [
                    branchInput,
                    InteractionLoopPreservation.Loop.bodyStopPolicy,
                    InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg bodyResult
                        (InteractionLoopPreservation.Loop.bodyContext
                          ctx regular (LabelSupply.label supply 2)
                          branchInput)
                        initResult.next (LabelSupply.label supply 1)
                        (LabelSupply.label supply 2)
                        branchInput bodySource tokens
                        (InteractionLoopPreservation.Loop.bodyStopPolicy
                          bodyResult postResult ctx regular
                          (LabelSupply.label supply 2)
                          (LabelSupply.label supply 0)
                          branchInput source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hBodyFits
                        regularAt := Or.inl hBodyBefore.regular
                        before := hBodyBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hBodyBoundary.congr_returns hReturns.symm
                        shapes := hBodyShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel bodyResult
                                (InteractionLoopPreservation.Loop.bodyContext
                                  ctx regular (LabelSupply.label supply 2)
                                  branchInput)
                                (LabelSupply.label supply 2)
                                source.returns tokens
                                sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx
                                (LabelSupply.label supply 0)
                                source.returns tokens policy)
                              hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              (InteractionLoopPreservation.Loop.postStopPolicy
                                postResult ctx
                                (LabelSupply.label supply 0)
                                source.returns tokens policy)
                              hMode
                          simpa [hReturns] using hRel })
              · intro initResult bodyResult postResult loopInput condOutput
                  blockFuel postSource hFuel hPostCompile hPostBlocks
                  hFacts hPostFits hReturns
                let branchInput : TypedCfg.Shape :=
                  { condOutput with slots := condOutput.slots.tail }
                have hParentSupply : supply <= bodyResult.next :=
                  Nat.le_trans (Nat.le_succ supply) hFacts.bodySupply
                have hOuterBefore :=
                  LoopContract.outer_before contract.before_succ
                    hFacts.bodySupply
                have hPostBefore :=
                  LoopContract.outer_generated_before
                    (tag := 0) contract.before_succ hFacts.bodySupply
                have hPostShapes :=
                  LoopContract.outer_shapes contract.shapes
                    hFacts.postRequire hFacts.loopShape
                have hPostBoundary :=
                  (contract.boundary.mono hParentSupply).push
                    hPostShapes hOuterBefore
                apply
                  hBlockOwner (Nat.le_of_lt hFuel)
                    hPostCompile hPostBlocks hFacts.postCalls
                    hPostWF hPostSafe hPostCalls
                    (TypedCfgPreservation.OutcomeSimulation.ContextSupports.withoutLoop
                      hSupports)
                    (by
                      simpa [InteractionLoopPreservation.Loop.outerContext]
                        using hProcs)
                · intro hCanLeave
                  obtain ⟨frame, rest, hSourceEq⟩ :=
                    hSourceReturns hCanLeave
                  exact ⟨frame, rest, hReturns.trans hSourceEq⟩
                · simpa [
                    branchInput,
                    InteractionLoopPreservation.Loop.postStopPolicy] using
                    (show
                      FragmentContract cfg postResult
                        (InteractionLoopPreservation.Loop.outerContext ctx)
                        bodyResult.next (LabelSupply.label supply 2)
                        (LabelSupply.label supply 0)
                        branchInput postSource tokens
                        (InteractionLoopPreservation.Loop.postStopPolicy
                          postResult ctx (LabelSupply.label supply 0)
                          source.returns tokens policy) from
                      { fits := by simpa [branchInput] using hPostFits
                        regularAt := Or.inl hPostBefore.regular
                        before := hPostBefore
                        activation := by
                          simpa [branchInput] using hFacts.bodyActivation
                        boundary := hPostBoundary.congr_returns hReturns.symm
                        shapes := hPostShapes
                        stops := by
                          intro sourceOutcome targetOutcome hRel
                          have hRel' :
                              Rel postResult
                                (InteractionLoopPreservation.Loop.outerContext ctx)
                                (LabelSupply.label supply 0)
                                source.returns tokens
                                sourceOutcome targetOutcome := by
                            simpa [hReturns] using hRel
                          exact
                            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                              policy hRel'
                        nonregular := by
                          intro childResult childRegular sourceOutcome
                            targetOutcome hMode hRel
                          apply
                            InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                              policy hMode
                          simpa [hReturns] using hRel })

theorem call_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {name : Structured.Name}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.call name) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs (.call name))
    (hProcs : ctx.procs = program.procs)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) (.call name) source)
      (InteractionStaticCost.stmtBudget
        program (sourceFuel + 1) (.call name))
      policy := by
  cases hCalls with
  | call hContains =>
      obtain ⟨proc, hLookup⟩ :=
        Structured.ProcList.exists_lookup?_of_contains hContains
      have hProcWF :=
        Structured.Program.procWF_of_lookup? hProgramWF hLookup
      have hProcFrameSafe :=
        Structured.Program.procFrameSafe_of_lookup?
          hProgramFrameSafe hLookup
      have hProcCalls :=
        Structured.Program.procCallsResolved_of_lookup?
          hProgramWF hLookup
      have hBodyBudget :=
        InteractionStaticCost.blockBudget_le_procBodyBudget_of_lookup
          (program := program) (fuel := sourceFuel) hLookup
      have hBounded :=
        InteractionCallPreservation.Call.openRun_call_bounded_under_of_compileStmtFuel?
          (bodyBudget :=
            InteractionStaticCost.procBodyBudget program sourceFuel)
          generated hLookup hProcs hCompile hBlocks hResultCalls
          contract.fits hProcWF contract.stops
          (by
            intro args callerStack targetState hSplit hStateRel
            have hExtension :=
              CallContract.extension
                (source := source) (tokens := tokens)
                (args := args) (callerStack := callerStack)
                (retc := proc.retc) (supply := supply)
            exact
              contract.boundary.ownership.eq_false_of_stateRel_extension
                (TypedCfgPreservation.LabelShape.procEntry generated hLookup)
                (TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc)
                hExtension hStateRel
                (TypedCfgPreservation.SourceFrameFits.procEntry_of_splitArgs
                  hSplit))
          (by
            intro args callerStack bodyState targetState
              hSplit hStateRel hFits hReturns
            have hExtension :
                TypedCfgPreservation.ActivationExtension
                  source.returns tokens bodyState.returns
                  (Structured.Stmt.callToken supply :: tokens) := by
              rw [hReturns]
              exact
                CallContract.extension
                  (source := source) (tokens := tokens)
                  (args := args) (callerStack := callerStack)
                  (retc := proc.retc) (supply := supply)
            exact
              contract.boundary.ownership.eq_false_of_stateRel_extension
                (TypedCfgPreservation.LabelShape.procExit generated hLookup)
                (TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit proc)
                hExtension hStateRel hFits)
          (by
            intro fragment args callerStack targetState hSplit hStateRel
            have hExtension :=
              CallContract.extension
                (source := source) (tokens := tokens)
                (args := args) (callerStack := callerStack)
                (retc := proc.retc) (supply := supply)
            have hFragmentShape :
                TypedCfgPreservation.LabelShape
                  cfg fragment.entry fragment.input :=
              TypedCfgPreservation.LabelShape.of_compileBlock?
                fragment.compile
                (by
                  apply
                    TypedCfgPreservation.BlocksInProgram.of_subset_of_wellTyped
                      generated.wellTyped
                  intro block hMem
                  rw [generated.cfgEq]
                  have hProcMem := fragment.blocks block hMem
                  simp [hProcMem, List.append_assoc])
            exact
              contract.boundary.ownership.eq_false_of_stateRel_extension
                hFragmentShape fragment.input_returnTokenDepth
                hExtension hStateRel
                (fragment.input_sourceFrameFits_of_splitArgs hSplit))
          (by
            intro fragment hFragmentBlocks hFragmentCalls
              args callerStack hSplit
            let callSource : RunState :=
              ((source.withEVM { source.evm with stack := args }).pushReturn
                callerStack proc.retc)
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body
                    (InteractionCallPreservation.Call.procContext program proc)
                    fragment.supply fragment.entry fragment.input
                    (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [
                TypedCfgCompiler.compileBlock?,
                InteractionCallPreservation.Call.procContext] using
                fragment.compile
            have hExtension :
                TypedCfgPreservation.ActivationExtension
                  source.returns tokens callSource.returns
                  (Structured.Stmt.callToken supply :: tokens) := by
              simpa [callSource] using
                (CallContract.extension
                  (source := source) (tokens := tokens)
                  (args := args) (callerStack := callerStack)
                  (retc := proc.retc) (supply := supply))
            have hShapes :=
              CallContract.shapes generated hLookup fragment
            have hOwned :=
              hBlockOwner (Nat.le_refl sourceFuel)
                hFragmentCompile hFragmentBlocks hFragmentCalls
                hProcWF.2.2 hProcFrameSafe hProcCalls
                (CallContract.supports program proc) rfl
                (by
                  intro _hCanLeave
                  exact
                    ⟨{ callerStack := callerStack, retc := proc.retc },
                      source.returns, by simp [callSource]⟩)
                (show
                  FragmentContract cfg fragment.result
                    (InteractionCallPreservation.Call.procContext program proc)
                    fragment.supply fragment.entry (ProcLabel.exit proc.name)
                    fragment.input callSource
                    (Structured.Stmt.callToken supply :: tokens)
                    (InteractionCallPreservation.Call.bodyStopPolicy
                      fragment.result program proc callSource.returns
                      (Structured.Stmt.callToken supply :: tokens) policy) from
                  { fits := fragment.input_sourceFrameFits_of_splitArgs hSplit
                    regularAt := Or.inl (by trivial)
                    before := CallContract.before
                    activation :=
                      TypedCfgPreservation.ActivationInput.active
                        ⟨proc.argc, fragment.input_returnTokenDepth⟩
                    boundary :=
                      contract.boundary.push_child hExtension hShapes
                        CallContract.before
                    shapes := hShapes
                    stops := by
                      intro sourceOutcome targetOutcome hRel
                      exact
                        InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                          policy hRel
                    nonregular :=
                      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                        policy })
            exact
              InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.mono_budget
                hOwned hBodyBudget)
      simpa [InteractionStaticCost.stmtBudget_call_succ,
        Nat.add_comm] using hBounded

theorem brk_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .brk)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .brk source)
      (InteractionStaticCost.stmtBudget program sourceFuel .brk)
      policy := by
  cases hWF with
  | brk hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.breakLabel hAllowed
      simpa only [InteractionStaticCost.stmtBudget_brk] using
        InteractionControlPreservation.OpenOutcome.PreservesUnder.boundedExec
          (InteractionLeafPreservation.Stmt.openRun_brk_under_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            (regularExit := .stop)
            hExit hCompile hBlocks contract.fits contract.nonregular)

theorem cont_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .cont)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .cont source)
      (InteractionStaticCost.stmtBudget program sourceFuel .cont)
      policy := by
  cases hWF with
  | cont hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.continueLabel hAllowed
      simpa only [InteractionStaticCost.stmtBudget_cont] using
        InteractionControlPreservation.OpenOutcome.PreservesUnder.boundedExec
          (InteractionLeafPreservation.Stmt.openRun_cont_under_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            (regularExit := .stop)
            hExit hCompile hBlocks contract.fits contract.nonregular)

theorem leave_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave .leave)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program sourceFuel .leave source)
      (InteractionStaticCost.stmtBudget program sourceFuel .leave)
      policy := by
  cases hWF with
  | leave hAllowed =>
      obtain ⟨exitLabel, hExit⟩ := hSupports.leaveLabel hAllowed
      obtain ⟨frame, rest, hReturns⟩ := hSourceReturns hAllowed
      simpa only [InteractionStaticCost.stmtBudget_leave] using
        InteractionControlPreservation.OpenOutcome.PreservesUnder.boundedExec
          (InteractionLeafPreservation.Stmt.openRun_leave_under_of_compileStmtFuel?
            (sourceProgram := program) (sourceFuel := sourceFuel)
            (regularExit := .stop)
            hExit hReturns hCompile hBlocks contract.fits
            contract.nonregular)

theorem terminal_bounded
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program sourceFuel (.terminal kind) source)
      (InteractionStaticCost.stmtBudget
        program sourceFuel (.terminal kind))
      policy := by
  simpa only [InteractionStaticCost.stmtBudget_terminal] using
    InteractionControlPreservation.OpenOutcome.PreservesUnder.boundedExec
      (InteractionLeafPreservation.Stmt.openRun_terminal_under_of_compileStmtFuel?
        (sourceProgram := program) (sourceFuel := sourceFuel)
        (regularExit := .stop)
        hCompile hBlocks contract.fits contract.nonregular)

theorem bounded_succ
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program} {stmt : Structured.Stmt}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          stmt ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generated.calls)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave stmt)
    (hFrameSafe : Structured.Stmt.FrameSafe stmt)
    (hCalls :
      Structured.ProcList.StmtCallsResolved program.procs stmt)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hProcs : ctx.procs = program.procs)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (hBlockOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        program (sourceFuel + 1) stmt source)
      (InteractionStaticCost.stmtBudget
        program (sourceFuel + 1) stmt)
      policy := by
  cases stmt with
  | code code =>
      exact code_bounded hCompile hBlocks contract
  | if_ cond body =>
      exact
        if_bounded hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
          hSupports hProcs hSourceReturns hBlockOwner contract
  | switch scrutinee cases defaultBody =>
      exact
        switch_bounded hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
          hSupports hProcs hSourceReturns hBlockOwner contract
  | for_ init cond post body =>
      exact
        for_bounded hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
          hSupports hProcs hSourceReturns hBlockOwner contract
  | brk =>
      exact brk_bounded hCompile hBlocks hWF hSupports contract
  | cont =>
      exact cont_bounded hCompile hBlocks hWF hSupports contract
  | leave =>
      exact
        leave_bounded hCompile hBlocks hWF hSupports hSourceReturns contract
  | call name =>
      exact
        call_bounded hCompile hBlocks hResultCalls hCalls hProcs
          hProgramWF hProgramFrameSafe hBlockOwner contract
  | terminal kind =>
      exact terminal_bounded hCompile hBlocks contract

theorem bounded_zero
    {compilerFuel : Nat}
    {program : Structured.Program} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {policy : StopPolicy}
    {canBreak canContinue canLeave : Bool}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          stmt ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hWF : Structured.Stmt.WF canBreak canContinue canLeave stmt)
    (hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        ctx canBreak canContinue canLeave)
    (hSourceReturns :
      canLeave = true ->
        exists frame rest, source.returns = frame :: rest)
    (contract :
      StmtContract cfg result ctx supply entry regular input
        source tokens policy) :
    BoundedExecPreservesUnder result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun program 0 stmt source)
      (InteractionStaticCost.stmtBudget program 0 stmt)
      policy := by
  cases stmt with
  | code code => exact code_bounded hCompile hBlocks contract
  | if_ cond body
  | switch cond body defaultBody
  | for_ body cond defaultBody body_1
  | call cond =>
      intro target hStateRel transcript sourceOutcome hExec
      simp only [
        InteractionSemantics.Stmt.openRun,
        EffectSemantics.Control.Stmt.run] at hExec
      cases hExec
  | brk => exact brk_bounded hCompile hBlocks hWF hSupports contract
  | cont => exact cont_bounded hCompile hBlocks hWF hSupports contract
  | leave =>
      exact
        leave_bounded hCompile hBlocks hWF hSupports hSourceReturns contract
  | terminal kind => exact terminal_bounded hCompile hBlocks contract

end Stmt

/-- Fuel-founded source-budgeted owner for every compiled Structured block. -/
theorem block_owner
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) :
    BlockOwnerAt sourceFuel program entryShapes cfg generated := by
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      unfold BlockOwnerAt
      intro blockSourceFuel compilerFuel block ctx supply entry regular input
        result source tokens policy canBreak canContinue canLeave
        hSourceFuel hCompile hBlocks hResultCalls hWF hFrameSafe hCalls
        hSupports hProcs hSourceReturns contract
      cases blockSourceFuel with
      | zero =>
          intro target hStateRel transcript sourceOutcome hExec
          simp only [
            InteractionSemantics.Block.openRun,
            EffectSemantics.Control.Block.run] at hExec
          cases hExec
      | succ innerFuel =>
          have hInnerLt : innerFuel < sourceFuel := by omega
          have hInnerOwner :
              BlockOwnerAt innerFuel program entryShapes cfg generated :=
            ih innerFuel hInnerLt
          cases compilerFuel with
          | zero =>
              simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
          | succ listFuel =>
              unfold TypedCfgCompiler.compileBlockFuel? at hCompile
              cases listFuel with
              | zero =>
                  simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
              | succ compilerFuel =>
                  cases block with
                  | mk stmts =>
                      cases stmts with
                      | nil =>
                          simpa only [
                            InteractionStaticCost.blockBudget_nil_succ] using
                            InteractionControlPreservation.Block.openRun_nil_bounded_under_of_compileStmtListFuel?
                              (sourceProgram := program)
                              (sourceFuel := innerFuel)
                              hCompile hBlocks contract.fits contract.stops
                      | cons stmt rest =>
                          cases compilerFuel with
                          | zero =>
                              simp [
                                TypedCfgCompiler.compileStmtListFuel?,
                                TypedCfgCompiler.compileStmtFuel?] at hCompile
                          | succ stmtCompilerFuel =>
                              cases hWF with
                              | cons hStmtWF hRestWF =>
                                  cases hFrameSafe with
                                  | cons hStmtSafe hRestSafe =>
                                      cases hCalls with
                                      | mk hStmtListCalls =>
                                          cases hStmtListCalls with
                                          | cons hStmtCalls hRestCalls =>
                                              rw [
                                                InteractionStaticCost.blockBudget_cons_succ]
                                              apply
                                                InteractionControlPreservation.Block.openRun_cons_bounded_under_of_compileStmtListFuel?
                                                  hCompile hBlocks hResultCalls
                                              · intro headResult tailResult
                                                  tailInput middleSource
                                                  targetMiddle hHeadCompile
                                                  hFallthrough hTailCompile
                                                  hTailBlocks hRel
                                                have hTailShape :
                                                    TypedCfgPreservation.LabelShape
                                                      cfg
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      tailInput :=
                                                  TypedCfgPreservation.LabelShape.of_compileStmtListFuel?
                                                    hTailCompile hTailBlocks
                                                obtain
                                                    ⟨targetState, hTarget,
                                                      hStateRel⟩ :=
                                                  TypedCfgPreservation.OutcomeSimulation.Rel.regular_elim
                                                    hRel.1
                                                have hTargetEq :
                                                    targetState = targetMiddle := by
                                                  cases hTarget
                                                  rfl
                                                subst targetState
                                                rcases hRel.2.1 with
                                                  ⟨shape, hShape, hFits⟩
                                                have hReturns :
                                                    middleSource.returns =
                                                      source.returns := by
                                                  simpa [
                                                    InteractionControlPreservation.OpenOutcome.ActivationRestored]
                                                    using hRel.2.2
                                                have hShapeEq : shape = tailInput :=
                                                  Option.some.inj
                                                    (hShape.symm.trans hFallthrough)
                                                subst shape
                                                exact
                                                  (contract.boundary.congr_returns
                                                    hReturns.symm).eq_false_of_stateRel
                                                    (source := middleSource)
                                                    (scope := supply) (tag := 100)
                                                    (Nat.le_refl supply)
                                                    (contract.before.regular.generated_ne
                                                      (Nat.le_refl supply))
                                                    hTailShape
                                                    (contract.activation.stmtFallthrough
                                                      hHeadCompile hFallthrough)
                                                    hStateRel hFits
                                              · exact contract.nonregular
                                              · intro headResult hHeadCompile
                                                  hHeadBlocks hHeadCalls hFallthrough
                                                have hHeadContract :
                                                    StmtContract cfg headResult
                                                      ctx supply entry
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      input source tokens policy :=
                                                  { fits := contract.fits
                                                    regularAt := Or.inr rfl
                                                    before :=
                                                      contract.before.nonregular
                                                    activation := contract.activation
                                                    boundary :=
                                                      contract.boundary.rebase_regular
                                                        contract.before.regular
                                                    shapes :=
                                                      contract.shapes.of_fallthrough_none
                                                        hFallthrough
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      exact
                                                        contract.nonregular
                                                          (hRel.mode_ne_regular_of_fallthrough_none
                                                            hFallthrough)
                                                          hRel
                                                    nonregular := contract.nonregular }
                                                cases innerFuel with
                                                | zero =>
                                                    exact
                                                      Stmt.bounded_zero
                                                        hHeadCompile hHeadBlocks
                                                        hStmtWF hSupports
                                                        hSourceReturns hHeadContract
                                                | succ recursiveFuel =>
                                                    exact
                                                      Stmt.bounded_succ
                                                        hHeadCompile hHeadBlocks
                                                        hHeadCalls hStmtWF hStmtSafe
                                                        hStmtCalls hSupports hProcs
                                                        hSourceReturns hProgramWF
                                                        hProgramFrameSafe
                                                        (hInnerOwner.mono
                                                          (Nat.le_succ recursiveFuel))
                                                        hHeadContract
                                              · intro headResult tailResult
                                                  tailInput hHeadCompile hHeadBlocks
                                                  hHeadCalls hFallthrough
                                                  hTailCompile hTailBlocks hWhole
                                                have wholeContract :
                                                    FragmentContract cfg
                                                      (headResult.append tailResult)
                                                      ctx supply entry regular input
                                                      source tokens policy := by
                                                  simpa [hWhole] using contract
                                                have hTailShape :
                                                    TypedCfgPreservation.LabelShape
                                                      cfg
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      tailInput :=
                                                  TypedCfgPreservation.LabelShape.of_compileStmtListFuel?
                                                    hTailCompile hTailBlocks
                                                have hHeadShapes :
                                                    BoundaryShapes cfg headResult ctx
                                                      (TypedCfgCompiler.restLabel
                                                        supply) :=
                                                  wholeContract.shapes.with_regular
                                                    (by
                                                      intro shape hShape
                                                      have hShapeEq :
                                                          shape = tailInput :=
                                                        Option.some.inj
                                                          (hShape.symm.trans
                                                            hFallthrough)
                                                      subst shape
                                                      exact hTailShape)
                                                have hHeadContract :
                                                    StmtContract cfg headResult ctx
                                                      supply entry
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      input source tokens
                                                      (InteractionControlPreservation.OpenOutcome.pushStopJump
                                                        headResult ctx
                                                        (TypedCfgCompiler.restLabel
                                                          supply)
                                                        source.returns tokens
                                                        policy) :=
                                                  { fits := contract.fits
                                                    regularAt := Or.inr rfl
                                                    before :=
                                                      contract.before.nonregular
                                                    activation :=
                                                      wholeContract.activation
                                                    boundary :=
                                                      wholeContract.boundary.push_current
                                                        wholeContract.regularAt
                                                        wholeContract.before.nonregular
                                                        rfl hHeadShapes
                                                    shapes := hHeadShapes
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      exact
                                                        InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
                                                          policy hRel
                                                    nonregular :=
                                                      InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
                                                        policy }
                                                cases innerFuel with
                                                | zero =>
                                                    exact
                                                      Stmt.bounded_zero
                                                        hHeadCompile hHeadBlocks
                                                        hStmtWF hSupports
                                                        hSourceReturns hHeadContract
                                                | succ recursiveFuel =>
                                                    exact
                                                      Stmt.bounded_succ
                                                        hHeadCompile hHeadBlocks
                                                        hHeadCalls hStmtWF hStmtSafe
                                                        hStmtCalls hSupports hProcs
                                                        hSourceReturns hProgramWF
                                                        hProgramFrameSafe
                                                        (hInnerOwner.mono
                                                          (Nat.le_succ recursiveFuel))
                                                        hHeadContract
                                              · intro headResult tailResult
                                                  tailInput middleSource
                                                  hHeadCompile hFallthrough
                                                  hTailCompile hTailBlocks
                                                  hTailCalls hReturns hFrameFits
                                                  hWhole
                                                have wholeContract :
                                                    FragmentContract cfg
                                                      (headResult.append tailResult)
                                                      ctx supply entry regular input
                                                      source tokens policy := by
                                                  simpa [hWhole] using contract
                                                have hHeadNext :
                                                    supply + 1 <= headResult.next :=
                                                  TypedCfgCompilerFacts.Supply.stmt_next_ge_succ
                                                    hHeadCompile
                                                have hTailFits :
                                                    TypedCfgCompiler.Shape.SourceFrameFits
                                                      tailInput
                                                      middleSource.evm.stack.length := by
                                                  rcases hFrameFits with
                                                    ⟨shape, hShape, hFits⟩
                                                  have hShapeEq : shape = tailInput :=
                                                    Option.some.inj
                                                      (hShape.symm.trans hFallthrough)
                                                  subst shape
                                                  exact hFits
                                                have hTailShapes :
                                                    BoundaryShapes cfg tailResult
                                                      ctx regular :=
                                                  wholeContract.shapes.with_regular
                                                    (by
                                                      intro shape hShape
                                                      apply
                                                        wholeContract.shapes.regular
                                                      simp [
                                                        TypedCfgCompiler.Result.append,
                                                        hShape])
                                                have hTailContract :
                                                    FragmentContract cfg tailResult
                                                      ctx headResult.next
                                                      (TypedCfgCompiler.restLabel
                                                        supply)
                                                      regular tailInput middleSource
                                                      tokens policy :=
                                                  { fits := hTailFits
                                                    regularAt :=
                                                      Or.inl
                                                        (contract.before.regular.mono
                                                          (Nat.le_trans
                                                            (Nat.le_succ supply)
                                                            hHeadNext))
                                                    before :=
                                                      contract.before.mono
                                                        (Nat.le_trans
                                                          (Nat.le_succ supply)
                                                          hHeadNext)
                                                    activation :=
                                                      contract.activation.stmtFallthrough
                                                        hHeadCompile hFallthrough
                                                    boundary :=
                                                      (contract.boundary.mono
                                                        (Nat.le_trans
                                                          (Nat.le_succ supply)
                                                          hHeadNext)).congr_returns
                                                        hReturns.symm
                                                    shapes := hTailShapes
                                                    stops := by
                                                      intro sourceOutcome
                                                        targetOutcome hRel
                                                      apply wholeContract.stops
                                                      have hRel' :
                                                          Rel tailResult ctx regular
                                                            source.returns tokens
                                                            sourceOutcome
                                                            targetOutcome := by
                                                        simpa [hReturns] using hRel
                                                      exact
                                                        InteractionControlPreservation.OpenOutcome.Rel.append_right
                                                          hRel'
                                                    nonregular := by
                                                      intro childResult childRegular
                                                        sourceOutcome targetOutcome
                                                        hMode hRel
                                                      apply contract.nonregular hMode
                                                      simpa [hReturns] using hRel }
                                                have hTailBlockCompile :
                                                    TypedCfgCompiler.compileBlockFuel?
                                                        (Nat.succ
                                                          (stmtCompilerFuel + 1))
                                                        { stmts := rest } ctx
                                                        headResult.next
                                                        (TypedCfgCompiler.restLabel
                                                          supply)
                                                        tailInput regular =
                                                      some tailResult := by
                                                  unfold
                                                    TypedCfgCompiler.compileBlockFuel?
                                                  exact hTailCompile
                                                apply
                                                  hInnerOwner
                                                    (blockSourceFuel := innerFuel)
                                                    (compilerFuel :=
                                                      Nat.succ
                                                        (stmtCompilerFuel + 1))
                                                    (block := { stmts := rest })
                                                    (ctx := ctx)
                                                    (supply := headResult.next)
                                                    (entry :=
                                                      TypedCfgCompiler.restLabel
                                                        supply)
                                                    (regular := regular)
                                                    (input := tailInput)
                                                    (result := tailResult)
                                                    (source := middleSource)
                                                    (tokens := tokens)
                                                    (policy := policy)
                                                    (canBreak := canBreak)
                                                    (canContinue := canContinue)
                                                    (canLeave := canLeave)
                                                    (Nat.le_refl innerFuel)
                                                    hTailBlockCompile hTailBlocks
                                                    hTailCalls hRestWF hRestSafe
                                                    (.mk hRestCalls)
                                                    hSupports hProcs
                                                · intro hCanLeave
                                                  obtain
                                                      ⟨frame, remaining,
                                                        hSourceEq⟩ :=
                                                    hSourceReturns hCanLeave
                                                  exact
                                                    ⟨frame, remaining,
                                                      hReturns.trans hSourceEq⟩
                                                · exact hTailContract

namespace GeneratedProgram

def topPolicy
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (source : RunState) : StopPolicy :=
  InteractionOwnerPreservation.OpenOutcome.GeneratedProgram.topPolicy
    generated source

theorem main_bounded
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    BoundedExecPreservesUnder generated.main cfg
      TypedCfgCompiler.entryLabel { procs := program.procs }
      ProcLabel.programEnd source []
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)
      (InteractionStaticCost.blockBudget
        program sourceFuel program.body)
      (topPolicy generated source) := by
  have hMainCompile :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel program.body + 1)
          program.body { procs := program.procs }
          0 TypedCfgCompiler.entryLabel TypedCfg.Shape.caller
          ProcLabel.programEnd = some generated.main := by
    simpa [TypedCfgCompiler.compileBlock?] using generated.mainCompile
  have hSupports :
      TypedCfgPreservation.OutcomeSimulation.ContextSupports
        { procs := program.procs } false false false :=
    { breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by simp }
  have hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        { procs := program.procs } ProcLabel.programEnd 0 :=
    { regular := by trivial
      breakLabel := by simp
      continueLabel := by simp
      leaveLabel := by simp }
  have hShapes :=
    InteractionOwnerPreservation.OpenOutcome.GeneratedProgram.main_shapes
      generated
  have hBaseBoundary :
      RecursiveBoundary cfg source.returns []
        (fun _ _ => false) 0 ProcLabel.programEnd :=
    { ownership :=
        InteractionBoundaryPreservation.OpenOutcome.StopPolicy.ActivationProtected.empty
          cfg source.returns []
      fresh :=
        InteractionBoundaryPreservation.OpenOutcome.StopPolicy.ActivationFreshExcept.of_static
          (by
            intro scope tag target hScope hNe
            rfl) }
  have hBoundary :
      RecursiveBoundary cfg source.returns []
        (topPolicy generated source) 0 ProcLabel.programEnd := by
    simpa [topPolicy,
      InteractionOwnerPreservation.OpenOutcome.GeneratedProgram.topPolicy] using
      hBaseBoundary.push hShapes hBefore
  have hOwner :
      BlockOwnerAt sourceFuel program entryShapes cfg generated :=
    block_owner generated hProgramWF hProgramFrameSafe sourceFuel
  apply
    hOwner
      (blockSourceFuel := sourceFuel)
      (compilerFuel := TypedCfgCompiler.blockFuel program.body + 1)
      (block := program.body)
      (ctx := { procs := program.procs })
      (supply := 0)
      (entry := TypedCfgCompiler.entryLabel)
      (regular := ProcLabel.programEnd)
      (input := TypedCfg.Shape.caller)
      (result := generated.main)
      (source := source)
      (tokens := [])
      (policy := topPolicy generated source)
      (canBreak := false)
      (canContinue := false)
      (canLeave := false)
      (Nat.le_refl sourceFuel)
      hMainCompile generated.mainBlocks generated.mainCalls
      hProgramWF.2.2.2.2 hProgramFrameSafe.2 hProgramWF.2.2.2.1
      hSupports rfl
  · intro hFalse
    cases hFalse
  · exact
      { fits := by
          simp [
            TypedCfgCompiler.Shape.SourceFrameFits,
            TypedCfgCompiler.Shape.sourceLength,
            TypedCfgCompiler.Shape.sourceView,
            TypedCfg.Shape.caller,
            TypedCfg.Shape.length,
            TypedCfg.Shape.returnTokenDepth?,
            TypedCfg.Shape.returnTokenDepthList?]
        regularAt := Or.inl (by trivial)
        before := hBefore
        activation := TypedCfgPreservation.ActivationInput.top _
        boundary := hBoundary
        shapes := hShapes
        stops := by
          intro sourceOutcome targetOutcome hRel
          exact
            InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
              (fun _ _ => false) hRel
        nonregular :=
          InteractionControlPreservation.OpenOutcome.StopPolicy.StopsNonregular.push
            (fun _ _ => false) }

theorem main_uniform
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    InteractionControlPreservation.OpenOutcome.UniformExecPreservesUnder
      generated.main cfg TypedCfgCompiler.entryLabel
      { procs := program.procs } ProcLabel.programEnd source []
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)
      (InteractionStaticCost.blockBudget
        program sourceFuel program.body)
      (topPolicy generated source) := by
  apply
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder.uniform
      (main_bounded generated hProgramWF hProgramFrameSafe sourceFuel source)
  intro sourceOutcome targetOutcome hRel
  exact
    InteractionControlPreservation.OpenOutcome.targetStoppedBy_pushStopJump_of_rel
      (fun _ _ => false) hRel

theorem generateWithProcEntryShapes?_main_uniform
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? program entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState) :
    exists generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg,
      InteractionControlPreservation.OpenOutcome.UniformExecPreservesUnder
        generated.main cfg TypedCfgCompiler.entryLabel
        { procs := program.procs } ProcLabel.programEnd source []
        (InteractionSemantics.Block.openRun
          program sourceFuel program.body source)
        (InteractionStaticCost.blockBudget
          program sourceFuel program.body)
        (topPolicy generated source) := by
  let generated :=
    TypedCfgPreservation.Program.GeneratedContext.of_generate
      hGenerate hWellTyped
  exact
    ⟨generated,
      main_uniform generated hProgramWF hProgramFrameSafe
        sourceFuel source⟩

/--
Adjacent same-observation theorem for checked Structured generation. The
compiler-owned generated context is constructed internally and returned only as
the witness selecting the pass result relation.
-/
theorem generateWithProcEntryShapes?_main_preserves
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? program entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hProgramWF : program.WF)
    (hProgramFrameSafe : program.FrameSafe)
    (sourceFuel : Nat) (source : RunState)
    (hSuccessful : Simulation.Interaction.Successful
      (InteractionSemantics.Block.openRun
        program sourceFuel program.body source)) :
    exists generated :
        TypedCfgPreservation.Program.GeneratedContext
          program entryShapes cfg,
      InteractionControlPreservation.OpenOutcome.PreservesUnder
        generated.main cfg TypedCfgCompiler.entryLabel
        { procs := program.procs } ProcLabel.programEnd .stop source []
        (InteractionSemantics.Block.openRun
          program sourceFuel program.body source)
        (InteractionStaticCost.blockBudget
          program sourceFuel program.body)
        (topPolicy generated source) := by
  obtain ⟨generated, hUniform⟩ :=
    generateWithProcEntryShapes?_main_uniform
      hGenerate hWellTyped hProgramWF hProgramFrameSafe sourceFuel source
  exact
    ⟨generated,
      InteractionControlPreservation.OpenOutcome.UniformExecPreservesUnder.preserves
        hUniform hSuccessful⟩

end GeneratedProgram

end OpenOutcome
end InteractionBoundedOwnerPreservation
end Structured
end EvmCompiler
