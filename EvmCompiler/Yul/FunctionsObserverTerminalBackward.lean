import EvmCompiler.Functions.EffectSemanticsInversion
import EvmCompiler.Yul.FunctionsObserverExpressionBackward
import EvmCompiler.Yul.FunctionsObserverTerminal

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminalBackward

/-!
Terminal backward adequacy owned by the adjacent Yul-to-Functions pass.

This module reconstructs source terminal failures from concrete executions of
the ordinary Functions output. It reuses the canonical expression lowering,
effect semantics, and terminal relation; it does not define a second compiler
or control interpreter.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

structure AlignedPrimitiveExpressionBackward
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (prim : EvmYul.Operation .Yul)
    (args : List AstExpr)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (kind : Assembly.HaltKind)
    (targetFinal : Functions.ObserverSemantics.State transcript) where
  sourceFuel : Nat
  failure :
    Yul.Source.Effectful.Failure
      (ObserverSemantics.SourceReplay.State transcript)
  sourceRun :
    Yul.Source.Effectful.exec
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        sourceFuel (.ExprStmtCall (.Call (.inl prim) args))
        codeOverride source =
      .error failure
  observable :
    Yul.Source.Effectful.Exception.Observable failure.exception
  relation :
    FunctionsObserverOutcome.TerminalFailureRel codeRel failure
      (Functions.Source.Effectful.Outcome.halt kind targetFinal)

/--
Reconstruct a terminal Yul primitive expression after its generated argument
prelude has completed regularly.

The concrete `terminalArgs` execution determines the actual target arguments.
The compiler-owned stable-argument theorem identifies those arguments with the
source replay reconstructed by expression backward adequacy.
-/
theorem primitiveExpressionAfterArgsBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq kind.argCount}
    {targetFuel terminalFuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetAfterPre targetFinal :
      Functions.ObserverSemantics.State transcript}
    {ctx ctxAfterPre terminalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hTerminal : Prim.terminal? prim = some kind)
    (hLowering :
      EvmCompiler.Yul.Expr.List.UncheckedBoundLowering
        before args preArgs lowerArgs after)
    (hSeq :
      EvmCompiler.Yul.Expr.List.toStackSeq?
          lowerArgs kind.argCount =
        some seq)
    (hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr = true)
    (hExpr :
      FunctionsObserverExpressionBackward.RecursiveAlignedValueBackwardBelow
        profile sourceContract contract transcript codeRel program
        codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hPreRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := preArgs } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfterPre,
            ctxAfterPre))
    (hTerminalRun :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctxAfterPre terminalFuel
          (.terminalArgs kind seq) targetAfterPre =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind targetFinal,
            terminalCtx)) :
    Nonempty
      (AlignedPrimitiveExpressionBackward contract codeRel codeOverride
        prim args source kind targetFinal) := by
  obtain ⟨argsBackward⟩ :=
    FunctionsObserverExpressionBackward.boundArgsBackwardBelow
      profile sourceContract contract transcript codeRel program
      codeOverride bound hTargetFuel hLowering hEligible hExpr
      hRel hDomain hScope hPreRun
  let argsExact := argsBackward.result
  obtain
      ⟨targetAfterArgs, targetValues, terminalFinal,
        hTargetArgs, hTargetTerminal, hOutcome, _hTerminalCtx⟩ :=
    Functions.Source.Effectful.Stmt.run_terminalArgs_ok_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTerminalRun
  have hSeq' :
      EvmCompiler.Yul.Expr.List.toSeq?
          lowerArgs.reverse kind.argCount =
        some seq := by
    simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
  have hTargetArgList :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs.reverse targetAfterPre =
        .ok (targetAfterArgs, targetValues) :=
    FunctionsObserverExpression.argListEval_of_toSeq
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (fun hEval =>
        Functions.ObserverSafety.SafeSemantics.eval_outputs_length hEval)
      hSeq' hTargetArgs
  have hExtends :
      StateRelation.Vars.TargetExtends
          argsExact.prepared.prepared.prepared.finalTarget.source.vars
          targetAfterPre.source.vars := by
    rw [argsExact.finalTarget_eq]
    exact StateRelation.Vars.TargetExtends.refl _
  have hStable :=
    argsExact.prepared.prepared.stackStable targetAfterPre hExtends
  rw [hStable] at hTargetArgList
  have hArgsPair := Except.ok.inj hTargetArgList
  injection hArgsPair with hTargetState hTargetValues
  subst targetAfterArgs
  subst targetValues
  injection hOutcome with hTargetFinal
  subst terminalFinal
  let commonFuel := max argsBackward.sourceFuel 2
  have hArgsFuel : argsBackward.sourceFuel ≤ commonFuel :=
    Nat.le_max_left _ _
  have hTerminalFuel : 2 ≤ commonFuel :=
    Nat.le_max_right _ _
  have hSourceArgs :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          commonFuel args.reverse codeOverride source =
        .ok (argsExact.sourceFinal, argsExact.values.reverse) :=
    Yul.Source.Effectful.evalArgs_mono
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
        contract transcript)
      hArgsFuel argsExact.sourceRun
  have hAfterRel := argsExact.prepared.relation
  rw [argsExact.finalTarget_eq] at hAfterRel
  obtain ⟨failure, hSourceTerminal, hObservable, hFailureRel⟩ :=
    FunctionsObserverTerminal.primitiveBackwardAt
      hTerminalFuel hTerminal hAfterRel hTargetTerminal
  have hSourceTerminal' :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval commonFuel argsExact.sourceFinal prim
          argsExact.values.reverse.reverse =
        .error failure := by
    simpa using hSourceTerminal
  have hSourceRun :=
    Yul.Source.Effectful.exec_expr_primitive_error_of_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hSourceArgs hSourceTerminal'
  exact
    ⟨commonFuel + 1, failure, hSourceRun,
      hObservable, hFailureRel⟩

end FunctionsObserverTerminalBackward
end Yul
end EvmCompiler
