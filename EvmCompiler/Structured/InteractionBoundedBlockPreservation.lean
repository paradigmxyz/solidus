import EvmCompiler.Structured.InteractionControlPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionControlPreservation
namespace Block

theorem openRun_nil_bounded_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          [] ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hStops :
      forall {sourceOutcome targetOutcome},
        OpenOutcome.Rel result ctx regular source.returns tokens
            sourceOutcome targetOutcome ->
          OpenOutcome.TargetStoppedBy policy targetOutcome) :
    OpenOutcome.BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1) { stmts := [] } source)
      1 policy :=
  OpenOutcome.PreservesUnder.boundedExec
    (openRun_nil_under_of_compileStmtListFuel?
      (regularExit := .stop) hCompile hBlocks hFits hStops)

theorem openRun_cons_bounded_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel headBudget tailBudget : Nat}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hMiddleNoStop :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape}
          {middleSource : RunState} {targetMiddle : EVMState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest
            (ctx.advance headResult) headResult.next
            (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        OpenOutcome.Rel headResult ctx
            (TypedCfgCompiler.restLabel supply) source.returns tokens
            (.regular middleSource)
            (.jump (TypedCfgCompiler.restLabel supply) targetMiddle) ->
          policy (TypedCfgCompiler.restLabel supply) targetMiddle = false)
    (hNonregularStops :
      OpenOutcome.StopPolicy.StopsNonregular
        policy ctx source.returns tokens)
    (hHeadNoTail :
      forall {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult ->
        TypedCfgPreservation.BlocksInProgram headResult cfg ->
        TypedCfgPreservation.CallsInProgram headResult generatedCalls ->
        headResult.fallthrough? = none ->
        OpenOutcome.BoundedExecPreservesUnder headResult cfg entry ctx
          (TypedCfgCompiler.restLabel supply) source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          headBudget policy)
    (hHeadWithTail :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult ->
        TypedCfgPreservation.BlocksInProgram headResult cfg ->
        TypedCfgPreservation.CallsInProgram headResult generatedCalls ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest
            (ctx.advance headResult) headResult.next
            (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        result = headResult.append tailResult ->
        OpenOutcome.BoundedExecPreservesUnder headResult cfg entry ctx
          (TypedCfgCompiler.restLabel supply) source tokens
          (InteractionSemantics.Stmt.openRun
            sourceProgram sourceFuel stmt source)
          headBudget
          (OpenOutcome.pushStopJump headResult ctx
            (TypedCfgCompiler.restLabel supply)
            source.returns tokens policy))
    (hTail :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest
            (ctx.advance headResult) headResult.next
            (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        TypedCfgPreservation.CallsInProgram tailResult generatedCalls ->
        middleSource.returns = source.returns ->
        OpenOutcome.FrameFits headResult ctx
          (Structured.Outcome.regular middleSource) ->
        result = headResult.append tailResult ->
        OpenOutcome.BoundedExecPreservesUnder tailResult cfg
          (TypedCfgCompiler.restLabel supply) ctx regular
          middleSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
          tailBudget policy) :
    OpenOutcome.BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := stmt :: rest } source)
      (headBudget + tailBudget) policy := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    have hHead :=
      hHeadNoTail hHeadCompile hBlocks hResultCalls hFallthrough
    have hIgnored :=
      OpenOutcome.BoundedExecPreservesUnder.ignore_tail_of_no_fallthrough
        (resultRegular := regular)
        (tailRun := fun middleSource =>
          InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
        hFallthrough hHead
    have hPadded :=
      OpenOutcome.BoundedExecPreservesUnder.mono_budget hIgnored
        (show headBudget <= headBudget + tailBudget by omega)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hPadded
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHeadCalls :=
      TypedCfgPreservation.CallsInProgram.left_of_append hResultCalls
    have hTailCalls :=
      TypedCfgPreservation.CallsInProgram.right_of_append hResultCalls
    have hHead :=
      hHeadWithTail hHeadCompile hHeadBlocks hHeadCalls hFallthrough
        hTailCompile hTailBlocks rfl
    have hComposed :=
      OpenOutcome.BoundedExecPreservesUnder.sequence hHead
        (fun hRel =>
          hMiddleNoStop hHeadCompile hFallthrough
            hTailCompile hTailBlocks hRel)
        (fun hMode hRel => hNonregularStops hMode hRel)
        (fun middleSource hReturns hFits =>
          hTail hHeadCompile hFallthrough hTailCompile
            hTailBlocks hTailCalls hReturns hFits rfl)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hComposed

theorem openRun_nil_runtime_error_bounded_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          [] ctx supply entry input regular = some result) :
    OpenOutcome.BoundedRuntimeErrorExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1) { stmts := [] } source)
      1 policy := by
  intro target hStateRel transcript sourceError hRuntime hSourceExec
  simp only [
    InteractionSemantics.Block.openRun,
    EffectSemantics.Control.Block.run] at hSourceExec
  cases hSourceExec

theorem openRun_cons_runtime_error_bounded_under_of_compileStmtListFuel?
    {compilerFuel sourceFuel headBudget tailBudget : Nat}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy : OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hMiddleNoStop :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape}
          {middleSource : RunState} {targetMiddle : EVMState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest
            (ctx.advance headResult) headResult.next
            (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        OpenOutcome.Rel headResult ctx
            (TypedCfgCompiler.restLabel supply) source.returns tokens
            (.regular middleSource)
            (.jump (TypedCfgCompiler.restLabel supply) targetMiddle) ->
          policy (TypedCfgCompiler.restLabel supply) targetMiddle = false)
    (hHeadNoTail :
      forall {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        TypedCfgPreservation.BlocksInProgram headResult cfg ->
        TypedCfgPreservation.CallsInProgram headResult generatedCalls ->
        headResult.fallthrough? = none ->
        OpenOutcome.BoundedExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget policy /\
          OpenOutcome.BoundedRuntimeErrorExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget policy)
    (hHeadWithTail :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        TypedCfgPreservation.BlocksInProgram headResult cfg ->
        TypedCfgPreservation.CallsInProgram headResult generatedCalls ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest
            (ctx.advance headResult) headResult.next
            (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        result = headResult.append tailResult ->
        OpenOutcome.BoundedExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget
            (OpenOutcome.pushStopJump headResult ctx
              (TypedCfgCompiler.restLabel supply)
              source.returns tokens policy) /\
          OpenOutcome.BoundedRuntimeErrorExecPreservesUnder headResult cfg entry ctx
            (TypedCfgCompiler.restLabel supply) source tokens
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceFuel stmt source)
            headBudget
            (OpenOutcome.pushStopJump headResult ctx
              (TypedCfgCompiler.restLabel supply)
              source.returns tokens policy))
    (hTailError :
      forall {headResult tailResult : TypedCfgCompiler.Result}
          {tailInput : TypedCfg.Shape} {middleSource : RunState},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) = some headResult ->
        headResult.fallthrough? = some tailInput ->
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest
            (ctx.advance headResult) headResult.next
            (TypedCfgCompiler.restLabel supply)
            tailInput regular = some tailResult ->
        TypedCfgPreservation.BlocksInProgram tailResult cfg ->
        TypedCfgPreservation.CallsInProgram tailResult generatedCalls ->
        middleSource.returns = source.returns ->
        OpenOutcome.FrameFits headResult ctx
          (Structured.Outcome.regular middleSource) ->
        result = headResult.append tailResult ->
        OpenOutcome.BoundedRuntimeErrorExecPreservesUnder tailResult cfg
          (TypedCfgCompiler.restLabel supply) ctx regular
          middleSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
          tailBudget policy) :
    OpenOutcome.BoundedRuntimeErrorExecPreservesUnder result cfg entry ctx regular
      source tokens
      (InteractionSemantics.Block.openRun
        sourceProgram (sourceFuel + 1)
        { stmts := stmt :: rest } source)
      (headBudget + tailBudget) policy := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    have hHeadPair :=
      hHeadNoTail hHeadCompile hBlocks hResultCalls hFallthrough
    have hIgnored :=
      OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.ignore_tail_of_no_fallthrough
        (resultRegular := regular)
        (tailRun := fun middleSource =>
          InteractionSemantics.Block.openRun
            sourceProgram sourceFuel { stmts := rest } middleSource)
        hFallthrough
        hHeadPair.1 hHeadPair.2
    have hPadded :=
      OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.mono_budget hIgnored
        (show headBudget <= headBudget + tailBudget by omega)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hPadded
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    have hHeadCalls :=
      TypedCfgPreservation.CallsInProgram.left_of_append hResultCalls
    have hTailCalls :=
      TypedCfgPreservation.CallsInProgram.right_of_append hResultCalls
    have hHeadPair :=
      hHeadWithTail hHeadCompile hHeadBlocks hHeadCalls hFallthrough
        hTailCompile hTailBlocks rfl
    have hComposed :=
      OpenOutcome.BoundedRuntimeErrorExecPreservesUnder.sequence
        hHeadPair.1 hHeadPair.2
        (fun hRel =>
          hMiddleNoStop hHeadCompile hFallthrough
            hTailCompile hTailBlocks hRel)
        (fun middleSource hReturns hFits =>
          hTailError hHeadCompile hFallthrough hTailCompile
            hTailBlocks hTailCalls hReturns hFits rfl)
    simpa [
      InteractionSemantics.Block.openRun,
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Block.run] using hComposed

end Block
end InteractionControlPreservation
end Structured
end EvmCompiler
