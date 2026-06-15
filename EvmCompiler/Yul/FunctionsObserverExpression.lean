import EvmCompiler.Yul.Compiler
import EvmCompiler.Yul.FunctionsObserverPrimitive

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverExpression

/-!
Expression preservation owned by the adjacent Yul-to-Functions pass.

This module consumes the ordinary Yul expression lowering functions and the
pass-owned primitive dispatcher. It does not define an observer-specific
expression compiler.
-/

abbrev Word := Assembly.Word

theorem exprSeqEval_seqCast
    {σ : Type}
    (model : Functions.Source.Effectful.StateModel σ)
    (prim : Functions.Source.Effectful.PrimitiveSemantics σ)
    {left right : Nat} (h : left = right)
    (exprs : Locals.ExprSeq left) (state : σ) :
    Locals.Source.Effectful.Expr.ExprSeq.eval
        model prim (EvmCompiler.Yul.Expr.seqCast h exprs) state =
      Locals.Source.Effectful.Expr.ExprSeq.eval
        model prim exprs state := by
  cases h
  rfl

theorem argListEval_toSeq
    {σ : Type}
    (model : Functions.Source.Effectful.StateModel σ)
    (prim : Functions.Source.Effectful.PrimitiveSemantics σ) :
    ∀ {exprs : List (Functions.Expr 1)} {results : Nat}
      {seq : Locals.ExprSeq results}
      {source final : σ} {values : List Word},
      EvmCompiler.Yul.Expr.List.toSeq? exprs results = some seq →
      Functions.Source.Effectful.ArgList.eval model prim exprs source =
        .ok (final, values) →
      Locals.Source.Effectful.Expr.ExprSeq.eval
          model prim seq source =
        .ok (final, values)
  | [], results, seq, source, final, values, hSeq, hRun => by
      cases results with
      | zero =>
          simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
          subst seq
          simpa [Functions.Source.Effectful.ArgList.eval,
            Locals.Source.Effectful.Expr.ExprSeq.eval] using hRun
      | succ results =>
          simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
  | head :: rest, results, seq, source, final, values, hSeq, hRun => by
      cases results with
      | zero =>
          simp [EvmCompiler.Yul.Expr.List.toSeq?] at hSeq
      | succ results =>
          cases hTailSeq :
              EvmCompiler.Yul.Expr.List.toSeq? rest results with
          | none =>
              simp [EvmCompiler.Yul.Expr.List.toSeq?, hTailSeq] at hSeq
          | some tailSeq =>
              rw [EvmCompiler.Yul.Expr.List.toSeq?, hTailSeq] at hSeq
              injection hSeq with hSeq
              subst seq
              unfold Functions.Source.Effectful.ArgList.eval at hRun
              cases hHead :
                  Functions.Source.Effectful.Expr.evalOne
                    model prim head source with
              | error err =>
                  simp [hHead] at hRun
              | ok headResult =>
                  rcases headResult with ⟨afterHead, value⟩
                  simp [hHead] at hRun
                  cases hRest :
                      Functions.Source.Effectful.ArgList.eval
                        model prim rest afterHead with
                  | error err =>
                      simp [hRest] at hRun
                  | ok restResult =>
                      rcases restResult with ⟨afterRest, restValues⟩
                      simp [hRest] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      have hHeadEval :
                          Functions.Source.Effectful.Expr.eval
                              model prim head source =
                            .ok (afterHead, [value]) := by
                        unfold Functions.Source.Effectful.Expr.evalOne at hHead
                        unfold Locals.Source.Effectful.Expr.evalOne at hHead
                        cases hEval :
                            Functions.Source.Effectful.Expr.eval
                              model prim head source with
                        | error evalErr =>
                            simp [hEval] at hHead
                        | ok evalResult =>
                            rcases evalResult with ⟨headFinal, headValues⟩
                            cases headValues with
                            | nil =>
                                simp [hEval, Functions.Source.invalid,
                                  Structured.invalid] at hHead
                            | cons first remaining =>
                                cases remaining with
                                | nil =>
                                    simp [hEval] at hHead
                                    rcases hHead with ⟨rfl, rfl⟩
                                    simpa using hEval
                                | cons second tail =>
                                    simp [hEval, Functions.Source.invalid,
                                      Structured.invalid] at hHead
                      have hTailEval :
                          Locals.Source.Effectful.Expr.ExprSeq.eval
                              model prim tailSeq afterHead =
                            .ok (afterRest, restValues) :=
                        argListEval_toSeq model prim hTailSeq hRest
                      rw [exprSeqEval_seqCast]
                      simp [Locals.Source.Effectful.Expr.ExprSeq.eval,
                        hHeadEval, hTailEval]

theorem exprEval_cast
    {σ : Type}
    (model : Functions.Source.Effectful.StateModel σ)
    (prim : Functions.Source.Effectful.PrimitiveSemantics σ)
    {left right : Nat} (h : left = right)
    (expr : Locals.Expr left) (state : σ) :
    Functions.Source.Effectful.Expr.eval
        model prim (EvmCompiler.Yul.Expr.cast h expr) state =
      Functions.Source.Effectful.Expr.eval model prim expr state := by
  cases h
  rfl

structure DirectAt
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : Prop where
  evalValues :
    ∀ {results : Nat} {expr : AstExpr} {lower : Locals.Expr results}
      {source source' : ObserverSemantics.SourceReplay.State transcript}
      {target : Functions.ObserverSemantics.State transcript}
      {values : List Word},
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower →
      StateRelation.Replay.Rel codeRel source target →
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel expr codeOverride source =
        .ok (source', values) →
      ∃ target' : Functions.ObserverSemantics.State transcript,
        Functions.Source.Effectful.Expr.eval
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            lower target =
          .ok (target', values) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        values.length = results
  evalArgs :
    ∀ {args : List AstExpr} {lower : List (Locals.Expr 1)}
      {source source' : ObserverSemantics.SourceReplay.State transcript}
      {target : Functions.ObserverSemantics.State transcript}
      {values : List Word},
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower →
      StateRelation.Replay.Rel codeRel source target →
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel args codeOverride source =
        .ok (source', values) →
      ∃ target' : Functions.ObserverSemantics.State transcript,
        Functions.Source.Effectful.ArgList.eval
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            lower target =
          .ok (target', values) ∧
        StateRelation.Replay.Rel codeRel source' target'

theorem directAt
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) :
    DirectAt contract transcript codeRel codeOverride fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact
            { evalValues := by
                intro results expr lower source source' target values
                  hLower hRel hRun
                simp [Yul.Source.Effectful.evalValues,
                  Yul.Source.Effectful.fail] at hRun
              evalArgs := by
                intro args lower source source' target values
                  hLower hRel hRun
                simp [Yul.Source.Effectful.evalArgs,
                  Yul.Source.Effectful.fail] at hRun }
      | succ previous =>
          have hPrevious :
              DirectAt contract transcript codeRel codeOverride previous :=
            ih previous (Nat.lt_succ_self previous)
          refine
            { evalValues := ?_
              evalArgs := ?_ }
          · intro results expr lower source source' target values
              hLower hRel hRun
            cases expr with
            | Lit value =>
                by_cases hResults : 1 = results
                · cases hResults
                  simp [EvmCompiler.Yul.Expr.toLocals?,
                    EvmCompiler.Yul.Expr.cast] at hLower
                  subst lower
                  simp [Yul.Source.Effectful.evalValues] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  refine ⟨target, ?_, hRel, by simp⟩
                  rfl
                · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower
            | Var name =>
                by_cases hResults : 1 = results
                · cases hResults
                  simp [EvmCompiler.Yul.Expr.toLocals?,
                    EvmCompiler.Yul.Expr.cast] at hLower
                  subst lower
                  rcases hRel.2 with
                    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
                  cases hLookup : sourceVars.lookup name with
                  | none =>
                      simp [Yul.Source.Effectful.evalValues,
                        ObserverSemantics.SourceReplay.stateModel,
                        EvmYul.Yul.State.lookup?, hSource, hLookup,
                        Yul.Source.Effectful.fail] at hRun
                  | some value =>
                      simp [Yul.Source.Effectful.evalValues,
                        ObserverSemantics.SourceReplay.stateModel,
                        EvmYul.Yul.State.lookup?, hSource, hLookup] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      have hTargetLookup :
                          target.source.vars name = some value := by
                        rw [← hVars name]
                        exact hLookup
                      refine ⟨target, ?_, hRel, by simp⟩
                      simp [Functions.Source.Effectful.Expr.eval,
                        Locals.Source.Effectful.Expr.eval,
                        Functions.ObserverSemantics.stateModel,
                        Locals.ObserverSemantics.stateModel,
                        Locals.Source.Effectful.StateModel.vars,
                        identName, hTargetLookup]
                · simp [EvmCompiler.Yul.Expr.toLocals?, hResults] at hLower
            | Call callee args =>
                cases callee with
                | inr functionName =>
                    simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
                | inl prim =>
                    cases hOp : Prim.toBasicOp? prim with
                    | none =>
                        simp [EvmCompiler.Yul.Expr.toLocals?, hOp] at hLower
                    | some op =>
                        cases hArgsLower :
                            EvmCompiler.Yul.Expr.List.toLocals1? args with
                        | none =>
                            simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                              hArgsLower] at hLower
                        | some lowerArgs =>
                            cases hSeq :
                                EvmCompiler.Yul.Expr.List.toStackSeq?
                                  lowerArgs
                                  (Expressions.Structured.BasicOp.inputs op) with
                            | none =>
                                simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                  hArgsLower, hSeq] at hLower
                            | some seq =>
                                by_cases hOutputs :
                                    Expressions.Structured.BasicOp.outputs op =
                                      results
                                · simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq, hOutputs] at hLower
                                  subst lower
                                  simp only [Yul.Source.Effectful.evalValues]
                                    at hRun
                                  cases hArgsRun :
                                      Yul.Source.Effectful.evalArgs
                                        (ObserverSemantics.SourceReplay.stateModel
                                          transcript)
                                        (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                                          contract transcript)
                                        previous args.reverse codeOverride
                                        source with
                                  | error failure =>
                                      simp [hArgsRun] at hRun
                                  | ok argResult =>
                                      rcases argResult with
                                        ⟨sourceAfterArgs, reversedValues⟩
                                      simp [hArgsRun] at hRun
                                      have hLowerReverse :
                                          EvmCompiler.Yul.Expr.List.toLocals1?
                                              args.reverse =
                                            some lowerArgs.reverse :=
                                        EvmCompiler.Yul.Expr.List.toLocals1?_reverse
                                          hArgsLower
                                      obtain
                                          ⟨targetAfterArgs, hTargetArgList,
                                            hArgsRel⟩ :=
                                        hPrevious.evalArgs hLowerReverse
                                          hRel hArgsRun
                                      have hDirectSeq :
                                          EvmCompiler.Yul.Expr.List.toSeq?
                                              lowerArgs.reverse
                                              (Expressions.Structured.BasicOp.inputs
                                                op) =
                                            some seq := by
                                        simpa [EvmCompiler.Yul.Expr.List.toStackSeq?]
                                          using hSeq
                                      have hTargetArgs :
                                          Locals.Source.Effectful.Expr.ExprSeq.eval
                                              (Functions.ObserverSemantics.stateModel
                                                transcript)
                                              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                                contract transcript)
                                              seq target =
                                            .ok
                                              (targetAfterArgs,
                                                reversedValues) :=
                                        argListEval_toSeq
                                          (Functions.ObserverSemantics.stateModel
                                            transcript)
                                          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                            contract transcript)
                                          hDirectSeq hTargetArgList
                                      have hArgLength :
                                          reversedValues.length =
                                            lowerArgs.reverse.length :=
                                        Functions.Source.Effectful.ArgList.eval_length
                                          (Functions.ObserverSemantics.stateModel
                                            transcript)
                                          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                            contract transcript)
                                          hTargetArgList
                                      have hSeqLength :
                                          lowerArgs.reverse.length =
                                            Expressions.Structured.BasicOp.inputs
                                              op :=
                                        EvmCompiler.Yul.Expr.List.toSeq?_length
                                          hDirectSeq
                                      have hArity :
                                          reversedValues.reverse.length =
                                            Expressions.Structured.BasicOp.inputs
                                              op := by
                                        simpa [List.length_reverse,
                                          hArgLength] using hSeqLength
                                      cases previous with
                                      | zero =>
                                          obtain ⟨_hSafe, hPrimCall⟩ :=
                                            EvmCompiler.Yul.ObserverSafety.SafeSemantics.eval_ok_parts
                                              hRun
                                          simp [ObserverSemantics.SourceReplay.primCall,
                                            EvmYul.Yul.primCall,
                                            Yul.Source.Effectful.fail] at hPrimCall
                                      | succ primFuel =>
                                          obtain
                                              ⟨targetFinal, hTargetPrimitive,
                                                hFinalRel⟩ :=
                                            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelected
                                              (Prim.toBasicOp?_some_terminal_none
                                                hOp)
                                              (Prim.toUncheckedBasicOp?_of_toBasicOp?
                                                hOp)
                                              hArity hArgsRel hRun
                                          have hTargetPrimitive' :
                                              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                                  contract transcript).eval
                                                  op targetAfterArgs
                                                  reversedValues =
                                                .ok (targetFinal, values) := by
                                            simpa using hTargetPrimitive
                                          refine
                                            ⟨targetFinal, ?_, hFinalRel, ?_⟩
                                          · rw [exprEval_cast]
                                            simp [Functions.Source.Effectful.Expr.eval,
                                              Locals.Source.Effectful.Expr.eval,
                                              hTargetArgs, hTargetPrimitive']
                                          · have hLength :=
                                              Functions.ObserverSafety.SafeSemantics.eval_outputs_length
                                                hTargetPrimitive'
                                            simpa [hOutputs] using hLength
                                · simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq, hOutputs] at hLower
          · intro args lower source source' target values
              hLower hRel hRun
            cases args with
            | nil =>
                simp [EvmCompiler.Yul.Expr.List.toLocals1?] at hLower
                subst lower
                simp [Yul.Source.Effectful.evalArgs] at hRun
                rcases hRun with ⟨rfl, rfl⟩
                exact ⟨target, rfl, hRel⟩
            | cons head rest =>
                cases hHeadLower :
                    EvmCompiler.Yul.Expr.toLocals? 1 head with
                | none =>
                    simp [EvmCompiler.Yul.Expr.List.toLocals1?,
                      hHeadLower] at hLower
                | some lowerHead =>
                    cases hRestLower :
                        EvmCompiler.Yul.Expr.List.toLocals1? rest with
                    | none =>
                        simp [EvmCompiler.Yul.Expr.List.toLocals1?,
                          hHeadLower, hRestLower] at hLower
                    | some lowerRest =>
                        simp [EvmCompiler.Yul.Expr.List.toLocals1?,
                          hHeadLower, hRestLower] at hLower
                        subst lower
                        simp only [Yul.Source.Effectful.evalArgs] at hRun
                        cases hHeadRun :
                            Yul.Source.Effectful.eval
                              (ObserverSemantics.SourceReplay.stateModel
                                transcript)
                              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                                contract transcript)
                              previous head codeOverride source with
                        | error failure =>
                            simp [hHeadRun, Yul.Source.Effectful.evalTail] at hRun
                        | ok headResult =>
                            rcases headResult with
                              ⟨sourceAfterHead, value⟩
                            simp [hHeadRun] at hRun
                            unfold Yul.Source.Effectful.eval at hHeadRun
                            cases hHeadValues :
                                Yul.Source.Effectful.evalValues
                                  (ObserverSemantics.SourceReplay.stateModel
                                    transcript)
                                  (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                                    contract transcript)
                                  previous head codeOverride source with
                            | error failure =>
                                simp [hHeadValues] at hHeadRun
                            | ok headValuesResult =>
                                rcases headValuesResult with
                                  ⟨sourceAfterValues, headValues⟩
                                simp [hHeadValues] at hHeadRun
                                rcases hHeadRun with ⟨rfl, rfl⟩
                                obtain
                                    ⟨targetAfterHead, hTargetHead,
                                      hHeadRel, hHeadLength⟩ :=
                                  hPrevious.evalValues hHeadLower hRel
                                    hHeadValues
                                have hHeadValues :
                                    headValues = [headValues.head!] := by
                                  cases headValues with
                                  | nil =>
                                      simp at hHeadLength
                                  | cons first tail =>
                                      cases tail with
                                      | nil => rfl
                                      | cons second remaining =>
                                          simp at hHeadLength
                                rw [hHeadValues] at hTargetHead
                                cases previous with
                                | zero =>
                                    simp [Yul.Source.Effectful.evalTail,
                                      Yul.Source.Effectful.fail] at hRun
                                | succ tailFuel =>
                                    cases hRestRun :
                                        Yul.Source.Effectful.evalArgs
                                          (ObserverSemantics.SourceReplay.stateModel
                                            transcript)
                                          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                                            contract transcript)
                                          tailFuel rest codeOverride
                                          sourceAfterValues with
                                    | error failure =>
                                        simp [Yul.Source.Effectful.evalTail,
                                          hRestRun] at hRun
                                    | ok restResult =>
                                        rcases restResult with
                                          ⟨sourceFinal, restValues⟩
                                        simp only [Yul.Source.Effectful.evalTail,
                                          hRestRun] at hRun
                                        injection hRun with hPair
                                        injection hPair with hState hValues
                                        subst source'
                                        subst values
                                        have hTail :
                                            DirectAt contract transcript
                                              codeRel codeOverride tailFuel :=
                                          ih tailFuel (by omega)
                                        obtain
                                            ⟨targetFinal, hTargetRest,
                                              hFinalRel⟩ :=
                                          hTail.evalArgs hRestLower hHeadRel
                                            hRestRun
                                        have hTargetHeadOne :
                                            Functions.Source.Effectful.Expr.evalOne
                                                (Functions.ObserverSemantics.stateModel
                                                  transcript)
                                                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                                  contract transcript)
                                                lowerHead target =
                                              .ok
                                                (targetAfterHead,
                                                  headValues.head!) := by
                                          simp [Functions.Source.Effectful.Expr.evalOne,
                                            Locals.Source.Effectful.Expr.evalOne,
                                            hTargetHead]
                                        refine
                                          ⟨targetFinal, ?_, hFinalRel⟩
                                        simp [Functions.Source.Effectful.ArgList.eval,
                                          hTargetHeadOne,
                                          hTargetRest]

theorem toLocals_forward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel results : Nat}
    {expr : AstExpr} {lower : Locals.Expr results}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hLower :
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel expr codeOverride source =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      values.length = results :=
  (directAt contract transcript codeRel codeOverride fuel).evalValues
    hLower hRel hRun

theorem toLocalsArgs_forward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {args : List AstExpr} {lower : List (Locals.Expr 1)}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hLower :
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel args codeOverride source =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' :=
  (directAt contract transcript codeRel codeOverride fuel).evalArgs
    hLower hRel hRun

end FunctionsObserverExpression
end Yul
end EvmCompiler
