import EvmCompiler.Yul.FunctionsObserverExpression
import EvmCompiler.Yul.SolcValidation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverExpressionBackward

/-!
Backward adequacy for direct Yul expressions.

The fuel bound is source-syntax owned and invariant under argument reversal.
It supplies enough canonical Yul fuel for every recursively reconstructed
argument without exposing a replay witness or compiler-generated certificate.
-/

abbrev Word := Assembly.Word

mutual

  def directFuel : AstExpr → Nat
    | .Lit _value => 1
    | .Var _name => 1
    | .Call _callee args =>
        max (2 * args.length + maxDirectFuel args) 2 + 1

  def maxDirectFuel : List AstExpr → Nat
    | [] => 1
    | expr :: rest => max (directFuel expr) (maxDirectFuel rest)

end

def directArgsFuel (args : List AstExpr) : Nat :=
  2 * args.length + maxDirectFuel args

theorem one_le_directFuel :
    ∀ expr : AstExpr, 1 ≤ directFuel expr
  | .Lit _value => by simp [directFuel]
  | .Var _name => by simp [directFuel]
  | .Call _callee args => by
      simp [directFuel]

theorem one_le_maxDirectFuel :
    ∀ args : List AstExpr, 1 ≤ maxDirectFuel args
  | [] => by simp [maxDirectFuel]
  | expr :: rest => by
      exact
        le_trans (one_le_directFuel expr)
          (Nat.le_max_left _ _)

theorem one_le_directArgsFuel (args : List AstExpr) :
    1 ≤ directArgsFuel args := by
  unfold directArgsFuel
  have hMax := one_le_maxDirectFuel args
  omega

theorem maxDirectFuel_append :
    ∀ left right : List AstExpr,
      maxDirectFuel (left ++ right) =
        max (maxDirectFuel left) (maxDirectFuel right)
  | [], right => by
      simp [maxDirectFuel, one_le_maxDirectFuel right]
  | expr :: rest, right => by
      simp [maxDirectFuel, maxDirectFuel_append rest right,
        Nat.max_assoc]

theorem maxDirectFuel_reverse (args : List AstExpr) :
    maxDirectFuel args.reverse = maxDirectFuel args := by
  induction args with
  | nil =>
      rfl
  | cons expr rest ih =>
      rw [List.reverse_cons, maxDirectFuel_append, ih]
      have hExpr : maxDirectFuel [expr] = directFuel expr := by
        simp [maxDirectFuel, one_le_directFuel expr]
      rw [hExpr]
      simp only [maxDirectFuel]
      exact Nat.max_comm _ _

theorem directArgsFuel_reverse (args : List AstExpr) :
    directArgsFuel args.reverse = directArgsFuel args := by
  simp [directArgsFuel, maxDirectFuel_reverse]

structure DirectBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) : Prop where
  evalValues :
    ∀ {layout : List Name} {results : Nat}
      {expr : AstExpr} {lower : Locals.Expr results}
      {source : ObserverSemantics.SourceReplay.State transcript}
      {target targetFinal : Functions.ObserverSemantics.State transcript}
      {values : List Word},
      directFuel expr ≤ fuel →
      SolcValidation.ExprOk? profile sourceContract layout results expr =
        true →
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (targetFinal, values) →
      ∃ sourceFinal : ObserverSemantics.SourceReplay.State transcript,
        Yul.Source.Effectful.evalValues
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            fuel expr codeOverride source =
          .ok (sourceFinal, values) ∧
        StateRelation.Replay.ScopedExactRel
          codeRel layout sourceFinal targetFinal
  evalArgs :
    ∀ {layout : List Name} {args : List AstExpr}
      {lower : List (Locals.Expr 1)}
      {source : ObserverSemantics.SourceReplay.State transcript}
      {target targetFinal : Functions.ObserverSemantics.State transcript}
      {values : List Word},
      directArgsFuel args ≤ fuel →
      (∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr =
          true) →
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (targetFinal, values) →
      ∃ sourceFinal : ObserverSemantics.SourceReplay.State transcript,
        Yul.Source.Effectful.evalArgs
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            fuel args codeOverride source =
          .ok (sourceFinal, values) ∧
        StateRelation.Replay.ScopedExactRel
          codeRel layout sourceFinal targetFinal

theorem directBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat) :
    DirectBackwardAt profile sourceContract contract transcript
      codeRel codeOverride fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact
            { evalValues := by
                intro layout results expr lower source target targetFinal
                  values hFuel hOk hLower hRel hTarget
                have hOne := one_le_directFuel expr
                omega
              evalArgs := by
                intro layout args lower source target targetFinal values
                  hFuel hOk hLower hRel hTarget
                have hOne := one_le_directArgsFuel args
                omega }
      | succ previous =>
          have hPrevious :
              DirectBackwardAt profile sourceContract contract transcript
                codeRel codeOverride previous :=
            ih previous (Nat.lt_succ_self previous)
          refine
            { evalValues := ?_
              evalArgs := ?_ }
          · intro layout results expr lower source target targetFinal
              values hFuel hOk hLower hRel hTarget
            cases expr with
            | Lit value =>
                simp [SolcValidation.ExprOk?] at hOk
                subst results
                simp [EvmCompiler.Yul.Expr.toLocals?,
                  EvmCompiler.Yul.Expr.cast] at hLower
                subst lower
                obtain ⟨rfl, rfl⟩ :=
                  Functions.Source.Effectful.Expr.eval_lit_ok_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    hTarget
                refine ⟨source, ?_, hRel⟩
                simp [Yul.Source.Effectful.evalValues]
            | Var name =>
                simp [SolcValidation.ExprOk?] at hOk
                rcases hOk with ⟨hResults, hName⟩
                subst results
                simp [EvmCompiler.Yul.Expr.toLocals?,
                  EvmCompiler.Yul.Expr.cast] at hLower
                subst lower
                obtain ⟨value, hTargetLookup, rfl, rfl⟩ :=
                  Functions.Source.Effectful.Expr.eval_var_ok_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    hTarget
                rcases hRel.2 with
                  ⟨sourceShared, sourceVars, hSource, hShared,
                    hScoped, hDomain⟩
                have hSourceLookup :
                    source.source.lookup? name = some value := by
                  rw [hSource]
                  have hValue := hScoped name (by simpa using hName)
                  have hTargetLookup' :
                      targetFinal.source.vars name = some value := by
                    simpa using hTargetLookup
                  rw [hTargetLookup'] at hValue
                  simpa [EvmYul.Yul.State.lookup?] using hValue
                refine
                  ⟨source, ?_,
                    ⟨hRel.1, sourceShared, sourceVars, hSource,
                      hShared, hScoped, hDomain⟩⟩
                simp [Yul.Source.Effectful.evalValues,
                  ObserverSemantics.SourceReplay.stateModel,
                  hSourceLookup]
            | Call callee args =>
                cases callee with
                | inr functionName =>
                    simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
                | inl prim =>
                    have hArgsOk :
                        ∀ expr, expr ∈ args.reverse →
                          SolcValidation.ExprOk? profile sourceContract
                              layout 1 expr =
                            true := by
                      intro candidate hMem
                      exact
                        SolcValidation.exprOk_of_exprsOk_of_mem
                          (SolcValidation.exprsOk_of_exprOk_primitive hOk)
                          (by simpa using hMem)
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
                                  rw [FunctionsObserverExpression.exprEval_cast]
                                    at hTarget
                                  obtain
                                      ⟨targetAfterArgs, reversedValues,
                                        hTargetSeq, hTargetPrimitive⟩ :=
                                    Functions.Source.Effectful.Expr.eval_prim_ok_parts
                                      (Functions.ObserverSemantics.stateModel
                                        transcript)
                                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                        contract transcript)
                                      hTarget
                                  have hDirectSeq :
                                      EvmCompiler.Yul.Expr.List.toSeq?
                                          lowerArgs.reverse
                                          (Expressions.Structured.BasicOp.inputs
                                            op) =
                                        some seq := by
                                    simpa
                                      [EvmCompiler.Yul.Expr.List.toStackSeq?]
                                      using hSeq
                                  have hTargetArgs :
                                      Functions.Source.Effectful.ArgList.eval
                                          (Functions.ObserverSemantics.stateModel
                                            transcript)
                                          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                            contract transcript)
                                          lowerArgs.reverse target =
                                        .ok
                                          (targetAfterArgs,
                                            reversedValues) :=
                                    FunctionsObserverExpression.argListEval_of_toSeq
                                      (Functions.ObserverSemantics.stateModel
                                        transcript)
                                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                        contract transcript)
                                      (Functions.ObserverSafety.SafeSemantics.eval_outputs_length
                                        (contract := contract)
                                        (transcript := transcript))
                                      hDirectSeq hTargetSeq
                                  have hLowerReverse :
                                      EvmCompiler.Yul.Expr.List.toLocals1?
                                          args.reverse =
                                        some lowerArgs.reverse :=
                                    EvmCompiler.Yul.Expr.List.toLocals1?_reverse
                                      hArgsLower
                                  have hArgsFuel :
                                      directArgsFuel args.reverse ≤
                                        previous := by
                                    rw [directArgsFuel_reverse]
                                    unfold directArgsFuel
                                    have hBase :
                                        2 * args.length +
                                            maxDirectFuel args ≤
                                          max
                                            (2 * args.length +
                                              maxDirectFuel args)
                                            2 :=
                                      Nat.le_max_left _ _
                                    simp [directFuel] at hFuel
                                    omega
                                  obtain
                                      ⟨sourceAfterArgs, hSourceArgs,
                                        hArgsRel⟩ :=
                                    hPrevious.evalArgs hArgsFuel hArgsOk
                                      hLowerReverse hRel hTargetArgs
                                  have hArgLength :
                                      reversedValues.length =
                                        lowerArgs.reverse.length :=
                                    Functions.Source.Effectful.ArgList.eval_length
                                      (Functions.ObserverSemantics.stateModel
                                        transcript)
                                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                        contract transcript)
                                      hTargetArgs
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
                                    simpa [List.length_reverse, hArgLength]
                                      using hSeqLength
                                  cases previous with
                                  | zero =>
                                      have hOne :=
                                        one_le_directArgsFuel args.reverse
                                      omega
                                  | succ firstFuel =>
                                      cases firstFuel with
                                      | zero =>
                                          simp [directFuel,
                                            directArgsFuel] at hFuel
                                      | succ primFuel =>
                                          have hTargetPrimitive' :
                                              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                                                  contract transcript).eval
                                                  op targetAfterArgs
                                                  (reversedValues.reverse.reverse) =
                                                .ok (targetFinal, values) := by
                                            simpa using hTargetPrimitive
                                          obtain
                                              ⟨sourceFinal, hSourcePrimitive,
                                                hFinalRel, hStore⟩ :=
                                            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelectedBackwardAt
                                              primFuel
                                              (contract := contract)
                                              (sourceValues :=
                                                reversedValues.reverse)
                                              (Prim.toBasicOp?_some_terminal_none
                                                hOp)
                                              (Prim.toUncheckedBasicOp?_of_toBasicOp?
                                                hOp)
                                              (StateRelation.Replay.rel_of_scopedExact
                                                hArgsRel)
                                              hTargetPrimitive'
                                          refine
                                            ⟨sourceFinal, ?_,
                                              StateRelation.Replay.scopedExact_of_rel_store
                                                hFinalRel ?_⟩
                                          · simp only
                                              [Yul.Source.Effectful.evalValues,
                                                hSourceArgs]
                                            simpa using hSourcePrimitive
                                          · rw [hStore]
                                            exact
                                              StateRelation.Replay.sourceStoreDomain_of_scopedExact
                                                hArgsRel
                                · simp [EvmCompiler.Yul.Expr.toLocals?, hOp,
                                    hArgsLower, hSeq, hOutputs] at hLower
          · intro layout args lower source target targetFinal values
              hFuel hOk hLower hRel hTarget
            cases args with
            | nil =>
                simp [EvmCompiler.Yul.Expr.List.toLocals1?] at hLower
                subst lower
                obtain ⟨rfl, rfl⟩ :=
                  Functions.Source.Effectful.ArgList.eval_nil_ok_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    hTarget
                refine ⟨source, ?_, hRel⟩
                simp [Yul.Source.Effectful.evalArgs]
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
                        obtain
                            ⟨targetAfterHead, value, restValues,
                              hTargetHead, hTargetRest, hValues⟩ :=
                          Functions.Source.Effectful.ArgList.eval_cons_ok_parts
                            (Functions.ObserverSemantics.stateModel transcript)
                            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                              contract transcript)
                            hTarget
                        subst values
                        have hHeadFuel :
                            directFuel head ≤ previous := by
                          unfold directArgsFuel at hFuel
                          simp only [List.length_cons, maxDirectFuel] at hFuel
                          have hMax :
                              directFuel head ≤
                                max (directFuel head)
                                  (maxDirectFuel rest) :=
                            Nat.le_max_left _ _
                          omega
                        obtain
                            ⟨sourceAfterHead, hSourceHead, hHeadRel⟩ :=
                          hPrevious.evalValues hHeadFuel
                            (hOk head (by simp)) hHeadLower hRel hTargetHead
                        cases previous with
                        | zero =>
                            have hOne := one_le_directFuel head
                            omega
                        | succ tailFuel =>
                            have hRestFuel :
                                directArgsFuel rest ≤ tailFuel := by
                              unfold directArgsFuel at hFuel ⊢
                              simp only [List.length_cons,
                                maxDirectFuel] at hFuel
                              have hMax :
                                  maxDirectFuel rest ≤
                                    max (directFuel head)
                                      (maxDirectFuel rest) :=
                                Nat.le_max_right _ _
                              omega
                            have hTail :
                                DirectBackwardAt profile sourceContract
                                  contract transcript codeRel codeOverride
                                  tailFuel :=
                              ih tailFuel (by omega)
                            obtain
                                ⟨sourceFinal, hSourceRest, hFinalRel⟩ :=
                              hTail.evalArgs hRestFuel
                                (fun expr hMem =>
                                  hOk expr (List.mem_cons_of_mem head hMem))
                                hRestLower hHeadRel hTargetRest
                            have hSourceHeadEval :
                                Yul.Source.Effectful.eval
                                    (ObserverSemantics.SourceReplay.stateModel
                                      transcript)
                                    (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                                      contract transcript)
                                    tailFuel.succ head codeOverride source =
                                  .ok (sourceAfterHead, value) := by
                              simp [Yul.Source.Effectful.eval,
                                hSourceHead]
                            refine ⟨sourceFinal, ?_, hFinalRel⟩
                            simp [Yul.Source.Effectful.evalArgs,
                              hSourceHeadEval,
                              Yul.Source.Effectful.evalTail,
                              hSourceRest]

end FunctionsObserverExpressionBackward
end Yul
end EvmCompiler
