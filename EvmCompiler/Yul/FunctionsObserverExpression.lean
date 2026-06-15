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

theorem deferredEval_stable
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {expr : AstExpr} {lower : Locals.Expr 1}
    {fresh fresh' : Fresh.State} {pre : List Functions.Stmt}
    {base candidate : Functions.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? fresh expr =
        some (pre, lower, fresh'))
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower base =
        .ok (base, [value]))
    (hExtends :
      StateRelation.Vars.TargetExtends
        base.source.vars candidate.source.vars) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        lower candidate =
      .ok (candidate, [value]) := by
  cases expr with
  | Lit literal =>
      simp [EvmCompiler.Yul.Expr.lower1Unchecked?,
        EvmCompiler.Yul.Expr.lowerUnchecked?,
        EvmCompiler.Yul.Expr.cast] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      simpa [Functions.Source.Effectful.Expr.eval,
        Locals.Source.Effectful.Expr.eval] using hEval
  | Var name =>
      simp [EvmCompiler.Yul.Expr.lower1Unchecked?,
        EvmCompiler.Yul.Expr.lowerUnchecked?,
        EvmCompiler.Yul.Expr.cast] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      have hLookup :
          base.source.vars (identName name) = some value := by
        cases hBaseLookup :
            base.source.vars (identName name) with
        | none =>
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.vars,
              hBaseLookup, Functions.Source.invalid,
              Structured.invalid] at hEval
        | some actual =>
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.vars,
              hBaseLookup] at hEval
            rcases hEval with ⟨rfl⟩
            rfl
      have hCandidateLookup :
          candidate.source.vars (identName name) = some value :=
        hExtends (identName name) value hLookup
      simp [Functions.Source.Effectful.Expr.eval,
        Locals.Source.Effectful.Expr.eval,
        Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.vars, hCandidateLookup]
  | Call callee args =>
      simp [EvmCompiler.Yul.Expr.deferredBoundArgSafe?] at hSafe

theorem deferredEval_state_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {expr : AstExpr} {lower : Locals.Expr 1}
    {fresh fresh' : Fresh.State} {pre : List Functions.Stmt}
    {source final : Functions.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? fresh expr =
        some (pre, lower, fresh'))
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower source =
        .ok (final, [value])) :
    final = source := by
  cases expr with
  | Lit literal =>
      simp [EvmCompiler.Yul.Expr.lower1Unchecked?,
        EvmCompiler.Yul.Expr.lowerUnchecked?,
        EvmCompiler.Yul.Expr.cast] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      simpa [Functions.Source.Effectful.Expr.eval,
        Locals.Source.Effectful.Expr.eval] using
          (congrArg Prod.fst (Except.ok.inj hEval)).symm
  | Var name =>
      simp [EvmCompiler.Yul.Expr.lower1Unchecked?,
        EvmCompiler.Yul.Expr.lowerUnchecked?,
        EvmCompiler.Yul.Expr.cast] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      cases hLookup : source.source.vars (identName name) with
      | none =>
          simp [Functions.Source.Effectful.Expr.eval,
            Locals.Source.Effectful.Expr.eval,
            Functions.ObserverSemantics.stateModel,
            Locals.ObserverSemantics.stateModel,
            Locals.Source.Effectful.StateModel.vars,
            hLookup, Functions.Source.invalid,
            Structured.invalid] at hEval
      | some actual =>
          simp [Functions.Source.Effectful.Expr.eval,
            Locals.Source.Effectful.Expr.eval,
            Functions.ObserverSemantics.stateModel,
            Locals.ObserverSemantics.stateModel,
            Locals.Source.Effectful.StateModel.vars,
            hLookup] at hEval
          exact hEval.1.symm
  | Call callee args =>
      simp [EvmCompiler.Yul.Expr.deferredBoundArgSafe?] at hSafe

theorem deferredSourceEval_state_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat} {expr : AstExpr}
    {source final : ObserverSemantics.SourceReplay.State transcript}
    {value : Word}
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hEval :
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel expr codeOverride source =
        .ok (final, value)) :
    final = source := by
  cases fuel with
  | zero =>
      simp [Yul.Source.Effectful.eval,
        Yul.Source.Effectful.evalValues,
        Yul.Source.Effectful.fail] at hEval
  | succ previous =>
      cases expr with
      | Lit literal =>
          simp [Yul.Source.Effectful.eval,
            Yul.Source.Effectful.evalValues] at hEval
          exact hEval.1.symm
      | Var name =>
          cases hLookup : source.source.lookup? name with
          | none =>
              simp [Yul.Source.Effectful.eval,
                Yul.Source.Effectful.evalValues,
                ObserverSemantics.SourceReplay.stateModel, hLookup,
                Yul.Source.Effectful.fail] at hEval
          | some actual =>
              simp [Yul.Source.Effectful.eval,
                Yul.Source.Effectful.evalValues,
                ObserverSemantics.SourceReplay.stateModel, hLookup] at hEval
              exact hEval.1.symm
      | Call callee args =>
          simp [EvmCompiler.Yul.Expr.deferredBoundArgSafe?] at hSafe

theorem deferredSourceEvalValues_of_eval
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat} {expr : AstExpr}
    {source final : ObserverSemantics.SourceReplay.State transcript}
    {value : Word}
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hEval :
      Yul.Source.Effectful.eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel expr codeOverride source =
        .ok (final, value)) :
    Yul.Source.Effectful.evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        fuel expr codeOverride source =
      .ok (final, [value]) := by
  cases fuel with
  | zero =>
      simp [Yul.Source.Effectful.eval,
        Yul.Source.Effectful.evalValues,
        Yul.Source.Effectful.fail] at hEval
  | succ previous =>
      cases expr with
      | Lit literal =>
          simp [Yul.Source.Effectful.eval,
            Yul.Source.Effectful.evalValues] at hEval ⊢
          exact hEval
      | Var name =>
          cases hLookup : source.source.lookup? name with
          | none =>
              simp [Yul.Source.Effectful.eval,
                Yul.Source.Effectful.evalValues,
                ObserverSemantics.SourceReplay.stateModel, hLookup,
                Yul.Source.Effectful.fail] at hEval
          | some actual =>
              simp [Yul.Source.Effectful.eval,
                Yul.Source.Effectful.evalValues,
                ObserverSemantics.SourceReplay.stateModel, hLookup]
                at hEval ⊢
              exact hEval
      | Call callee args =>
          simp [EvmCompiler.Yul.Expr.deferredBoundArgSafe?] at hSafe

def StableValue
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (base : Functions.ObserverSemantics.State transcript)
    (lower : Locals.Expr 1) (value : Word) : Prop :=
  ∀ candidate : Functions.ObserverSemantics.State transcript,
    StateRelation.Vars.TargetExtends
        base.source.vars candidate.source.vars →
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower candidate =
        .ok (candidate, [value])

def StableArgs
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (base : Functions.ObserverSemantics.State transcript)
    (lower : List (Locals.Expr 1)) (values : List Word) : Prop :=
  ∀ candidate : Functions.ObserverSemantics.State transcript,
    StateRelation.Vars.TargetExtends
        base.source.vars candidate.source.vars →
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower candidate =
        .ok (candidate, values)

namespace StableValue

theorem deferred
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {expr : AstExpr} {lower : Locals.Expr 1}
    {fresh fresh' : Fresh.State} {pre : List Functions.Stmt}
    {base : Functions.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? fresh expr =
        some (pre, lower, fresh'))
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower base =
        .ok (base, [value])) :
    StableValue contract transcript base lower value := by
  intro candidate hExtends
  exact deferredEval_stable hSafe hLower hEval hExtends

theorem var
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {base : Functions.ObserverSemantics.State transcript}
    {name : Name} {value : Word}
    (hLookup : base.source.vars name = some value) :
    StableValue contract transcript base (.var name) value := by
  intro candidate hExtends
  have hCandidate : candidate.source.vars name = some value :=
    hExtends name value hLookup
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Functions.ObserverSemantics.stateModel,
    Locals.ObserverSemantics.stateModel,
    Locals.Source.Effectful.StateModel.vars, hCandidate]

end StableValue

namespace StableArgs

theorem nil
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    (base : Functions.ObserverSemantics.State transcript) :
    StableArgs contract transcript base [] [] := by
  intro candidate hExtends
  rfl

theorem cons
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {base : Functions.ObserverSemantics.State transcript}
    {head : Locals.Expr 1} {rest : List (Locals.Expr 1)}
    {value : Word} {values : List Word}
    (hHead : StableValue contract transcript base head value)
    (hRest : StableArgs contract transcript base rest values) :
    StableArgs contract transcript base (head :: rest) (value :: values) := by
  intro candidate hExtends
  have hHeadEval := hHead candidate hExtends
  have hHeadOne :
      Functions.Source.Effectful.Expr.evalOne
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          head candidate =
        .ok (candidate, value) := by
    simp [Functions.Source.Effectful.Expr.evalOne,
      Locals.Source.Effectful.Expr.evalOne, hHeadEval]
  have hRestEval := hRest candidate hExtends
  simp [Functions.Source.Effectful.ArgList.eval, hHeadOne, hRestEval]

end StableArgs

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
                        exact hVars name value hLookup
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

theorem toLocals_forward_targetDomain
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel results : Nat}
    {expr : AstExpr} {lower : Locals.Expr results}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word} {used : List Name}
    (hLower :
      EvmCompiler.Yul.Expr.toLocals? results expr = some lower)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin used target.source.vars)
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
      values.length = results ∧
      StateRelation.Vars.TargetDomainWithin used target'.source.vars := by
  obtain ⟨target', hTarget, hFinalRel, hLength⟩ :=
    toLocals_forward hLower hRel hRun
  have hVars :
      target'.source.vars = target.source.vars :=
    Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hTarget
  exact
    ⟨target', hTarget, hFinalRel, hLength,
      hDomain.congr hVars⟩

theorem toLocalsArgs_forward_targetDomain
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {args : List AstExpr} {lower : List (Locals.Expr 1)}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word} {used : List Name}
    (hLower :
      EvmCompiler.Yul.Expr.List.toLocals1? args = some lower)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin used target.source.vars)
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
      StateRelation.Replay.Rel codeRel source' target' ∧
      StateRelation.Vars.TargetDomainWithin used target'.source.vars := by
  obtain ⟨target', hTarget, hFinalRel⟩ :=
    toLocalsArgs_forward hLower hRel hRun
  have hVars :
      target'.source.vars = target.source.vars :=
    Functions.ObserverSafety.SafeSemantics.argList_eval_vars_eq hTarget
  exact
    ⟨target', hTarget, hFinalRel, hDomain.congr hVars⟩

theorem bindGenerated
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx} {stmtFuel : Nat}
    {before after : Fresh.State} {tmp : Name}
    {lower : Locals.Expr 1} {value : Word}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {targetBefore targetAfter :
      Functions.ObserverSemantics.State transcript}
    (hFresh : Fresh.fresh? before = some (tmp, after))
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower targetBefore =
        .ok (targetAfter, [value]))
    (hRel : StateRelation.Replay.Rel codeRel source targetAfter)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used targetAfter.source.vars)
    (hCtx : StateRelation.Vars.NamesWithin before.used ctx.scope) :
    let targetBound :=
      targetAfter.withSource (targetAfter.source.insert tmp value)
    let ctxBound := { ctx with scope := tmp :: ctx.scope }
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx stmtFuel (.let_ tmp lower) targetBefore =
      .ok
        (Functions.Source.Effectful.Outcome.regular targetBound, ctxBound) ∧
    StateRelation.Replay.Rel codeRel source targetBound ∧
    StateRelation.Vars.TargetDomainWithin
      after.used targetBound.source.vars ∧
    StateRelation.Vars.NamesWithin after.used ctxBound.scope := by
  have hEvalOne :
      Functions.Source.Effectful.Expr.evalOne
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower targetBefore =
        .ok (targetAfter, value) := by
    unfold Functions.Source.Effectful.Expr.evalOne
    unfold Locals.Source.Effectful.Expr.evalOne
    change
      Locals.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower targetBefore =
        .ok (targetAfter, [value]) at hEval
    rw [hEval]
    rfl
  obtain ⟨hUsed, hNotMem⟩ := Fresh.fresh?_components hFresh
  have hSourceHidden :
      source.source.lookup? tmp = none :=
    StateRelation.Replay.source_lookup_none_of_targetDomainWithin
      hRel hDomain hNotMem
  have hFinalRel :
      StateRelation.Replay.Rel codeRel source
        (targetAfter.withSource (targetAfter.source.insert tmp value)) :=
    StateRelation.Replay.insert_target_hidden hRel hSourceHidden
  have hFinalDomain :
      StateRelation.Vars.TargetDomainWithin after.used
        (targetAfter.withSource
          (targetAfter.source.insert tmp value)).source.vars := by
    rw [hUsed]
    exact hDomain.insert hNotMem
  dsimp
  refine ⟨?_, hFinalRel, hFinalDomain, ?_⟩
  · unfold Functions.Source.Effectful.Stmt.run
    rw [hEvalOne]
    rfl
  · intro name hMem
    rw [hUsed]
    simp only [List.mem_cons] at hMem ⊢
    rcases hMem with hEq | hActive
    · exact Or.inl hEq
    · exact Or.inr (hCtx name hActive)

structure Prepared
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (fresh : Fresh.State)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  finalTarget : Functions.ObserverSemantics.State transcript
  finalCtx : Functions.Source.Ctx
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular finalTarget, finalCtx)
  rel : StateRelation.Replay.Rel codeRel source finalTarget
  domain :
    StateRelation.Vars.TargetDomainWithin
      fresh.used finalTarget.source.vars
  scope : StateRelation.Vars.NamesWithin fresh.used finalCtx.scope
  varsExtends :
    StateRelation.Vars.TargetExtends
      target.source.vars finalTarget.source.vars

namespace Prepared

def empty
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope) :
    Prepared contract transcript codeRel program []
      fresh source target ctx := by
  exact
    { finalTarget := target
      finalCtx := ctx
      run :=
        ⟨1, by
          simp [Functions.Source.Effectful.Block.runOpen,
            Functions.Source.Effectful.Outcome.regular,
            Locals.Source.Effectful.Outcome.regular]⟩
      rel := hRel
      domain := hDomain
      scope := hScope
      varsExtends := StateRelation.Vars.TargetExtends.refl _ }

def append
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {left right : List Functions.Stmt}
    {middleFresh finalFresh : Fresh.State}
    {middleSource finalSource :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hLeft :
      Prepared contract transcript codeRel program left
        middleFresh middleSource target ctx)
    (hRight :
      Prepared contract transcript codeRel program right
        finalFresh finalSource hLeft.finalTarget hLeft.finalCtx) :
    Prepared contract transcript codeRel program (left ++ right)
      finalFresh finalSource target ctx := by
  exact
    { finalTarget := hRight.finalTarget
      finalCtx := hRight.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program left right ctx hLeft.finalCtx target hLeft.finalTarget
          (Functions.Source.Effectful.Outcome.regular hRight.finalTarget)
          hRight.finalCtx hLeft.run hRight.run
      rel := hRight.rel
      domain := hRight.domain
      scope := hRight.scope
      varsExtends :=
        StateRelation.Vars.TargetExtends.trans
          hLeft.varsExtends hRight.varsExtends }

def generated
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {before after : Fresh.State} {tmp : Name}
    {lower : Locals.Expr 1} {value : Word}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {targetBefore targetAfter :
      Functions.ObserverSemantics.State transcript}
    (hFresh : Fresh.fresh? before = some (tmp, after))
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower targetBefore =
        .ok (targetAfter, [value]))
    (hRel : StateRelation.Replay.Rel codeRel source targetAfter)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used targetAfter.source.vars)
    (hCtx : StateRelation.Vars.NamesWithin before.used ctx.scope) :
    Prepared contract transcript codeRel program
      [.let_ tmp lower] after source targetBefore ctx := by
  have hBound :=
    bindGenerated
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      (ctx := ctx) (stmtFuel := 1)
      hFresh hEval hRel hDomain hCtx
  let targetBound :=
    targetAfter.withSource (targetAfter.source.insert tmp value)
  let ctxBound := { ctx with scope := tmp :: ctx.scope }
  have hEvalVars :
      targetAfter.source.vars = targetBefore.source.vars :=
    Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hEval
  have hTargetHidden : targetAfter.source.vars tmp = none :=
    hDomain.lookup_none (Fresh.not_mem_of_fresh? hFresh)
  have hBeforeEval :
      StateRelation.Vars.TargetExtends
        targetBefore.source.vars targetAfter.source.vars := by
    intro name result hLookup
    rw [hEvalVars]
    exact hLookup
  have hEvalBound :
      StateRelation.Vars.TargetExtends
        targetAfter.source.vars targetBound.source.vars := by
    dsimp [targetBound]
    exact
      StateRelation.Vars.TargetExtends.insert_fresh hTargetHidden
  refine
    { finalTarget := targetBound
      finalCtx := ctxBound
      run := ?_
      rel := hBound.2.1
      domain := hBound.2.2.1
      scope := hBound.2.2.2
      varsExtends :=
        StateRelation.Vars.TargetExtends.trans hBeforeEval hEvalBound }
  have hEmpty :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctxBound 1 { stmts := [] } targetBound =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetBound,
            ctxBound) := by
    simp [Functions.Source.Effectful.Block.runOpen,
      Functions.Source.Effectful.Outcome.regular,
      Locals.Source.Effectful.Outcome.regular]
  exact
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hBound.1 hEmpty

end Prepared

structure PreparedValue
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (fresh : Fresh.State)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (value : Word) where
  preTarget : Functions.ObserverSemantics.State transcript
  evalTarget : Functions.ObserverSemantics.State transcript
  finalCtx : Functions.Source.Ctx
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget, finalCtx)
  eval :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        lower preTarget =
      .ok (evalTarget, [value])
  rel : StateRelation.Replay.Rel codeRel source evalTarget
  domain :
    StateRelation.Vars.TargetDomainWithin
      fresh.used evalTarget.source.vars
  scope : StateRelation.Vars.NamesWithin fresh.used finalCtx.scope
  varsExtends :
    StateRelation.Vars.TargetExtends
      target.source.vars preTarget.source.vars

structure ScopedPreparedValue
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (fresh : Fresh.State)
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (value : Word) where
  prepared :
    PreparedValue contract transcript codeRel program pre lower
      fresh source target ctx value
  relation :
    StateRelation.Replay.ScopedExactRel codeRel layout
      source prepared.evalTarget

def RecursiveScopedValueForward
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (program : Functions.Program)
    (bound : Nat) : Prop :=
  ∀ {exprFuel : Nat} {before after : Fresh.State}
    {layout : List Name}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word},
    exprFuel < bound →
      EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
        some (pre, lower, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          exprFuel expr codeOverride source =
        .ok (source', values) →
      ∃ value,
        values = [value] ∧
          Nonempty
            (ScopedPreparedValue contract transcript codeRel program
              pre lower after layout source' target ctx value)

structure BoundValue
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (before after : Fresh.State)
    (tmp : Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (value : Word) where
  prepared :
    Prepared contract transcript codeRel program
      (pre ++ [.let_ tmp lower]) after source target ctx
  lookup : prepared.finalTarget.source.vars tmp = some value

namespace PreparedValue

noncomputable def direct
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat} {expr : AstExpr} {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {value : Word}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 expr = some lower)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel expr codeOverride source =
        .ok (source', [value])) :
    PreparedValue contract transcript codeRel program [] lower
      fresh source' target ctx value := by
  let hResult :=
    toLocals_forward_targetDomain hLower hRel hDomain hRun
  let target' := Classical.choose hResult
  have hParts := Classical.choose_spec hResult
  exact
    { preTarget := target
      evalTarget := target'
      finalCtx := ctx
      run :=
        ⟨1, by
          simp [Functions.Source.Effectful.Block.runOpen,
            Functions.Source.Effectful.Outcome.regular,
            Locals.Source.Effectful.Outcome.regular]⟩
      eval := hParts.1
      rel := hParts.2.1
      domain := hParts.2.2.2
      scope := hScope
      varsExtends := StateRelation.Vars.TargetExtends.refl _ }

def bind
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {tmp : Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {value : Word}
    (hValue :
      PreparedValue contract transcript codeRel program pre lower
        before source target ctx value)
    (hFresh : Fresh.fresh? before = some (tmp, after)) :
    BoundValue contract transcript codeRel program pre lower before after
      tmp source target ctx value := by
  let generated :=
    Prepared.generated
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      hFresh hValue.eval hValue.rel hValue.domain hValue.scope
  let prepared :
      Prepared contract transcript codeRel program
        (pre ++ [.let_ tmp lower]) after source target ctx :=
    { finalTarget := generated.finalTarget
      finalCtx := generated.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program pre [.let_ tmp lower] ctx hValue.finalCtx target
          hValue.preTarget
          (Functions.Source.Effectful.Outcome.regular generated.finalTarget)
          generated.finalCtx hValue.run generated.run
      rel := generated.rel
      domain := generated.domain
      scope := generated.scope
      varsExtends :=
        StateRelation.Vars.TargetExtends.trans
          hValue.varsExtends generated.varsExtends }
  refine
    { prepared := prepared
      lookup := ?_ }
  dsimp [prepared, generated, Prepared.generated]
  simp [Locals.Source.State.insert, Locals.Source.Store.insert]

end PreparedValue

structure PreparedArgs
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : List (Locals.Expr 1))
    (fresh : Fresh.State)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (values : List Word) where
  prepared :
    Prepared contract transcript codeRel program pre
      fresh source target ctx
  stable :
    StableArgs contract transcript prepared.finalTarget lower values

namespace PreparedArgs

def empty
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope) :
    PreparedArgs contract transcript codeRel program [] []
      fresh source target ctx [] := by
  let prepared :=
    Prepared.empty
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      hRel hDomain hScope
  exact
    { prepared := prepared
      stable := StableArgs.nil prepared.finalTarget }

def direct
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {stateRest stateHead : Fresh.State}
    {expr : AstExpr} {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)} {lowerHead : Locals.Expr 1}
    {sourceRest sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {restValues : List Word} {value : Word}
    (hRest :
      PreparedArgs contract transcript codeRel program preRest lowerRest
        stateRest sourceRest target ctx restValues)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? stateRest expr =
        some (preHead, lowerHead, stateHead))
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerHead hRest.prepared.finalTarget =
        .ok (hRest.prepared.finalTarget, [value]))
    (hRel :
      StateRelation.Replay.Rel codeRel sourceFinal
        hRest.prepared.finalTarget) :
    PreparedArgs contract transcript codeRel program
      (preRest ++ preHead) (lowerHead :: lowerRest)
      stateHead sourceFinal target ctx (value :: restValues) := by
  obtain ⟨rfl, rfl, hDirectLower⟩ :=
    EvmCompiler.Yul.Expr.lower1Unchecked?_deferred_parts hSafe hLower
  let prepared :
      Prepared contract transcript codeRel program preRest
        stateHead sourceFinal target ctx :=
    { finalTarget := hRest.prepared.finalTarget
      finalCtx := hRest.prepared.finalCtx
      run := hRest.prepared.run
      rel := hRel
      domain := hRest.prepared.domain
      scope := hRest.prepared.scope
      varsExtends := hRest.prepared.varsExtends }
  let stableHead :
      StableValue contract transcript prepared.finalTarget lowerHead value :=
    StableValue.deferred hSafe hLower hEval
  let result :
      PreparedArgs contract transcript codeRel program preRest
        (lowerHead :: lowerRest) stateHead sourceFinal target ctx
        (value :: restValues) :=
    { prepared := prepared
      stable := StableArgs.cons stableHead hRest.stable }
  simpa using result

def bound
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {stateRest stateHead stateFresh : Fresh.State}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)} {lowerHead : Locals.Expr 1}
    {tmp : Name}
    {sourceRest sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {restValues : List Word} {value : Word}
    (hRest :
      PreparedArgs contract transcript codeRel program preRest lowerRest
        stateRest sourceRest target ctx restValues)
    (hValue :
      PreparedValue contract transcript codeRel program preHead lowerHead
        stateHead sourceFinal hRest.prepared.finalTarget
        hRest.prepared.finalCtx value)
    (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh)) :
    PreparedArgs contract transcript codeRel program
      (preRest ++ preHead ++ [.let_ tmp lowerHead])
      (.var tmp :: lowerRest) stateFresh sourceFinal target ctx
      (value :: restValues) := by
  let boundValue := hValue.bind hFresh
  let prepared :=
    Prepared.append hRest.prepared boundValue.prepared
  have hHeadLookup :
      prepared.finalTarget.source.vars tmp = some value := by
    exact boundValue.lookup
  have hHeadStable :
      StableValue contract transcript prepared.finalTarget (.var tmp) value :=
    StableValue.var hHeadLookup
  have hRestStable :
      StableArgs contract transcript prepared.finalTarget lowerRest
        restValues := by
    intro candidate hCandidate
    apply hRest.stable candidate
    exact
      StateRelation.Vars.TargetExtends.trans
        boundValue.prepared.varsExtends hCandidate
  let result :
      PreparedArgs contract transcript codeRel program
        (preRest ++ (preHead ++ [.let_ tmp lowerHead]))
        (.var tmp :: lowerRest) stateFresh sourceFinal target ctx
        (value :: restValues) :=
    { prepared := prepared
      stable := StableArgs.cons hHeadStable hRestStable }
  simpa [List.append_assoc] using result

theorem ofUncheckedLowering
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {initial final : Fresh.State}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {reversedValues : List Word}
    (hLowering :
      EvmCompiler.Yul.Expr.List.UncheckedBoundLowering
        initial args pre lowerArgs final)
    (hExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          StateRelation.Replay.Rel codeRel exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              before.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin before.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (PreparedValue contract transcript codeRel program exprPre lower
              after exprSource' exprTarget exprCtx value))
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel args.reverse codeOverride source =
        .ok (source', reversedValues)) :
    Nonempty
      (PreparedArgs contract transcript codeRel program pre lowerArgs
        final source' target ctx reversedValues.reverse) := by
  induction hLowering generalizing fuel source source' target ctx reversedValues with
  | nil =>
      cases fuel with
      | zero =>
          simp [Yul.Source.Effectful.evalArgs,
            Yul.Source.Effectful.fail] at hRun
      | succ previous =>
          simp [Yul.Source.Effectful.evalArgs] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact ⟨PreparedArgs.empty hRel hDomain hScope⟩
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      rw [List.reverse_cons] at hRun
      obtain
          ⟨middle, restReversed, headValues, headFuel,
            hFuel, hRestRun, hHeadRun, hValues⟩ :=
        Yul.Source.Effectful.evalArgs_append_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨exprFuel, value, hExprFuel, hHeadEval, hHeadValues⟩ :=
        Yul.Source.Effectful.evalArgs_singleton_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hHeadRun
      obtain ⟨restPrepared⟩ :=
        ih hExpr hRel hDomain hScope hRestRun
      have hSourceEq : source' = middle :=
        deferredSourceEval_state_eq hDirect.1 hHeadEval
      subst source'
      have hHeadEvalValues :=
        deferredSourceEvalValues_of_eval hDirect.1 hHeadEval
      obtain ⟨_hPre, _hState, hDirectLower⟩ :=
        EvmCompiler.Yul.Expr.lower1Unchecked?_deferred_parts
          hDirect.1 hHead
      obtain
          ⟨targetAfter, hTargetEval, hFinalRel, _hLength, _hFinalDomain⟩ :=
        toLocals_forward_targetDomain hDirectLower
          restPrepared.prepared.rel restPrepared.prepared.domain
          hHeadEvalValues
      have hTargetEq :
          targetAfter = restPrepared.prepared.finalTarget :=
        deferredEval_state_eq hDirect.1 hHead hTargetEval
      subst targetAfter
      let result :=
        PreparedArgs.direct restPrepared hHead hDirect.1
          hTargetEval hFinalRel
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      exact ⟨result⟩
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      rw [List.reverse_cons] at hRun
      obtain
          ⟨middle, restReversed, headValues, headFuel,
            hFuel, hRestRun, hHeadRun, hValues⟩ :=
        Yul.Source.Effectful.evalArgs_append_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      obtain ⟨exprFuel, value, hExprFuel, hHeadEval, hHeadValues⟩ :=
        Yul.Source.Effectful.evalArgs_singleton_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hHeadRun
      obtain ⟨restPrepared⟩ :=
        ih hExpr hRel hDomain hScope hRestRun
      obtain ⟨headPrepared⟩ :=
        hExpr (by omega) hHead restPrepared.prepared.rel
          restPrepared.prepared.domain restPrepared.prepared.scope
          hHeadEval
      let result :=
        PreparedArgs.bound restPrepared headPrepared hFresh
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      exact ⟨result⟩

end PreparedArgs

end FunctionsObserverExpression
end Yul
end EvmCompiler
