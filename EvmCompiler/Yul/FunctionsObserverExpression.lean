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

theorem append
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {base : Functions.ObserverSemantics.State transcript}
    {left right : List (Locals.Expr 1)}
    {leftValues rightValues : List Word}
    (hLeft : StableArgs contract transcript base left leftValues)
    (hRight : StableArgs contract transcript base right rightValues) :
    StableArgs contract transcript base
      (left ++ right) (leftValues ++ rightValues) := by
  intro candidate hExtends
  exact
    Functions.Source.Effectful.ArgList.eval_append
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      (hLeft candidate hExtends) (hRight candidate hExtends)

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
        values.length = results ∧
        source'.source.store = source.source.store
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
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store

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
                  refine ⟨target, ?_, hRel, by simp, rfl⟩
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
                      refine ⟨target, ?_, hRel, by simp, rfl⟩
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
                                            hArgsRel, hArgsStore⟩ :=
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
                                                hFinalRel, hPrimitiveStore⟩ :=
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
                                            ⟨targetFinal, ?_, hFinalRel, ?_,
                                              hPrimitiveStore.trans hArgsStore⟩
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
                exact ⟨target, rfl, hRel, rfl⟩
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
                                      hHeadRel, hHeadLength, hHeadStore⟩ :=
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
                                              hFinalRel, hRestStore⟩ :=
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
                                          ⟨targetFinal, ?_, hFinalRel,
                                            hRestStore.trans hHeadStore⟩
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
  by
    obtain ⟨target', hTarget, hFinalRel, hLength, _hStore⟩ :=
      (directAt contract transcript codeRel codeOverride fuel).evalValues
        hLower hRel hRun
    exact ⟨target', hTarget, hFinalRel, hLength⟩

theorem toLocals_forward_store
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
      values.length = results ∧
      source'.source.store = source.source.store :=
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
  by
    obtain ⟨target', hTarget, hFinalRel, _hStore⟩ :=
      (directAt contract transcript codeRel codeOverride fuel).evalArgs
        hLower hRel hRun
    exact ⟨target', hTarget, hFinalRel⟩

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

theorem toLocals_forward_targetDomain_store
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
      StateRelation.Vars.TargetDomainWithin used target'.source.vars ∧
      source'.source.store = source.source.store := by
  obtain ⟨target', hTarget, hFinalRel, hLength, hStore⟩ :=
    toLocals_forward_store hLower hRel hRun
  have hVars :
      target'.source.vars = target.source.vars :=
    Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hTarget
  exact
    ⟨target', hTarget, hFinalRel, hLength,
      hDomain.congr hVars, hStore⟩

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
  control : Functions.Source.Ctx.SameControl ctx finalCtx
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
      control := Functions.Source.Ctx.SameControl.refl ctx
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
      control :=
        Functions.Source.Ctx.SameControl.trans
          hLeft.control hRight.control
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
      control := Functions.Source.Ctx.SameControl.scopeUpdate ctx _
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
  control : Functions.Source.Ctx.SameControl ctx finalCtx
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

structure PreparedExpression
    {results : Nat}
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr results)
    (fresh : Fresh.State)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (values : List Word) where
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
      .ok (evalTarget, values)
  rel : StateRelation.Replay.Rel codeRel source evalTarget
  domain :
    StateRelation.Vars.TargetDomainWithin
      fresh.used evalTarget.source.vars
  scope : StateRelation.Vars.NamesWithin fresh.used finalCtx.scope
  control : Functions.Source.Ctx.SameControl ctx finalCtx
  varsExtends :
    StateRelation.Vars.TargetExtends
      target.source.vars preTarget.source.vars

structure ScopedPreparedExpression
    {results : Nat}
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr results)
    (fresh : Fresh.State)
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (values : List Word) where
  prepared :
    PreparedExpression contract transcript codeRel program pre lower
      fresh source target ctx values
  relation :
    StateRelation.Replay.ScopedExactRel codeRel layout
      source prepared.evalTarget

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

def evaluated
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {value : Word}
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (target', [value]))
    (hRel : StateRelation.Replay.Rel codeRel source target')
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target'.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope) :
    PreparedValue contract transcript codeRel program [] lower
      fresh source target ctx value :=
  { preTarget := target
    evalTarget := target'
    finalCtx := ctx
    run :=
      ⟨1, by
        simp [Functions.Source.Effectful.Block.runOpen,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular]⟩
    eval := hEval
    rel := hRel
    domain := hDomain
    scope := hScope
    control := Functions.Source.Ctx.SameControl.refl ctx
    varsExtends := StateRelation.Vars.TargetExtends.refl _ }

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
    evaluated hParts.1 hParts.2.1 hParts.2.2.2 hScope

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
      control :=
        Functions.Source.Ctx.SameControl.trans
          hValue.control generated.control
      varsExtends :=
        StateRelation.Vars.TargetExtends.trans
          hValue.varsExtends generated.varsExtends }
  refine
    { prepared := prepared
      lookup := ?_ }
  dsimp [prepared, generated, Prepared.generated]
  simp [Locals.Source.State.insert, Locals.Source.Store.insert]

def afterPrepared
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {fresh : Fresh.State}
    {sourceBefore sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal :
      Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {value : Word}
    (hPrepared :
      Prepared contract transcript codeRel program pre
        fresh sourceBefore target ctx)
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower hPrepared.finalTarget =
        .ok (targetFinal, [value]))
    (hRel : StateRelation.Replay.Rel codeRel sourceFinal targetFinal) :
    PreparedValue contract transcript codeRel program pre lower
      fresh sourceFinal target ctx value := by
  have hVars :
      targetFinal.source.vars = hPrepared.finalTarget.source.vars :=
    Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hEval
  exact
    { preTarget := hPrepared.finalTarget
      evalTarget := targetFinal
      finalCtx := hPrepared.finalCtx
      run := hPrepared.run
      eval := hEval
      rel := hRel
      domain := hPrepared.domain.congr hVars
      scope := hPrepared.scope
      control := hPrepared.control
      varsExtends := by
        intro name result hLookup
        exact hPrepared.varsExtends name result hLookup }

end PreparedValue

namespace PreparedExpression

def evaluated
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {results : Nat}
    {lower : Locals.Expr results}
    {fresh : Fresh.State}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (target', values))
    (hRel : StateRelation.Replay.Rel codeRel source target')
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target'.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope) :
    PreparedExpression contract transcript codeRel program [] lower
      fresh source target ctx values :=
  { preTarget := target
    evalTarget := target'
    finalCtx := ctx
    run :=
      ⟨1, by
        simp [Functions.Source.Effectful.Block.runOpen,
          Functions.Source.Effectful.Outcome.regular,
          Locals.Source.Effectful.Outcome.regular]⟩
    eval := hEval
    rel := hRel
    domain := hDomain
    scope := hScope
    control := Functions.Source.Ctx.SameControl.refl ctx
    varsExtends := StateRelation.Vars.TargetExtends.refl _ }

def afterPrepared
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {results : Nat}
    {pre : List Functions.Stmt} {lower : Locals.Expr results}
    {fresh : Fresh.State}
    {sourceBefore sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal :
      Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hPrepared :
      Prepared contract transcript codeRel program pre
        fresh sourceBefore target ctx)
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower hPrepared.finalTarget =
        .ok (targetFinal, values))
    (hRel : StateRelation.Replay.Rel codeRel sourceFinal targetFinal) :
    PreparedExpression contract transcript codeRel program pre lower
      fresh sourceFinal target ctx values := by
  have hVars :
      targetFinal.source.vars = hPrepared.finalTarget.source.vars :=
    Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hEval
  exact
    { preTarget := hPrepared.finalTarget
      evalTarget := targetFinal
      finalCtx := hPrepared.finalCtx
      run := hPrepared.run
      eval := hEval
      rel := hRel
      domain := hPrepared.domain.congr hVars
      scope := hPrepared.scope
      control := hPrepared.control
      varsExtends := hPrepared.varsExtends }

end PreparedExpression

namespace ScopedPreparedValue

noncomputable def direct
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat} {expr : AstExpr} {lower : Locals.Expr 1}
    {fresh : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 expr = some lower)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel expr codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            [] lower fresh layout source' target ctx value) := by
  obtain
      ⟨_target', _hTarget, _hFinalRel, hLength, _hFinalDomain,
        hStore⟩ :=
    toLocals_forward_targetDomain_store hLower
      (StateRelation.Replay.rel_of_scopedExact hRel)
      hDomain hRun
  cases values with
  | nil =>
      simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          let prepared :=
            PreparedValue.direct
              (contract := contract) (transcript := transcript)
              (codeRel := codeRel) (program := program)
              hLower (StateRelation.Replay.rel_of_scopedExact hRel)
              hDomain hScope hRun
          refine ⟨value, rfl, ⟨prepared, ?_⟩⟩
          exact
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.rel (by
                rw [hStore]
                exact
                  StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
      | cons next tail =>
          simp at hLength

noncomputable def evaluated
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : Locals.Expr 1}
    {fresh : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {value : Word}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin fresh.used ctx.scope)
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower target =
        .ok (target', [value]))
    (hFinalRel : StateRelation.Replay.Rel codeRel source' target')
    (hStore : source'.source.store = source.source.store) :
    ScopedPreparedValue contract transcript codeRel program
      [] lower fresh layout source' target ctx value := by
  have hFinalDomain :
      StateRelation.Vars.TargetDomainWithin fresh.used target'.source.vars :=
    hDomain.congr
      (Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hEval)
  let prepared :=
    PreparedValue.evaluated
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      hEval hFinalRel hFinalDomain hScope
  exact
    { prepared := prepared
      relation :=
        StateRelation.Replay.scopedExact_of_rel_store
          hFinalRel (by
            rw [hStore]
            exact
              StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel) }

noncomputable def ofGas
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call
            (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel
          (.Call
            (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx value) := by
  rw [EvmCompiler.Yul.Expr.lower1Unchecked?_gas before] at hLower
  rcases hLower with ⟨rfl, rfl, rfl⟩
  obtain ⟨primFuel, _hFuel, hPrimRun⟩ :=
    Yul.Source.Effectful.evalValues_prim_nil_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨target', hTargetPrim, hFinalRel, hStore⟩ :=
    EvmCompiler.Yul.FunctionsObserverPrimitive.gasSafe
      (StateRelation.Replay.rel_of_scopedExact hRel) hPrimRun
  have hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.prim .gas .nil : Locals.Expr 1) target =
        .ok (target', values) := by
    simpa [Functions.Source.Effectful.Expr.eval] using hTargetPrim
  have hLength : values.length = 1 := by
    simpa using
      Functions.ObserverSafety.SafeSemantics.eval_outputs_length hTargetPrim
  cases values with
  | nil =>
      simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          exact
            ⟨value, rfl,
              ⟨evaluated hRel hDomain hScope hTarget hFinalRel hStore⟩⟩
      | cons next tail =>
          simp at hLength

noncomputable def ofMsize
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call
            (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel
          (.Call
            (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx value) := by
  rw [EvmCompiler.Yul.Expr.lower1Unchecked?_msize before] at hLower
  rcases hLower with ⟨rfl, rfl, rfl⟩
  obtain ⟨primFuel, _hFuel, hPrimRun⟩ :=
    Yul.Source.Effectful.evalValues_prim_nil_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  obtain ⟨target', hTargetPrim, hFinalRel, hStore⟩ :=
    EvmCompiler.Yul.FunctionsObserverPrimitive.msizeSafe
      (StateRelation.Replay.rel_of_scopedExact hRel) hPrimRun
  have hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.prim .msize .nil : Locals.Expr 1) target =
        .ok (target', values) := by
    simpa [Functions.Source.Effectful.Expr.eval] using hTargetPrim
  have hLength : values.length = 1 := by
    simpa using
      Functions.ObserverSafety.SafeSemantics.eval_outputs_length hTargetPrim
  cases values with
  | nil =>
      simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          exact
            ⟨value, rfl,
              ⟨evaluated hRel hDomain hScope hTarget hFinalRel hStore⟩⟩
      | cons next tail =>
          simp at hLength

noncomputable def ofLiteral
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat} {value : Word}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before (.Lit value) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Lit value) codeOverride source =
        .ok (source', values)) :
    ∃ result,
      values = [result] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx result) := by
  obtain ⟨rfl, rfl, hToLocals⟩ :=
    EvmCompiler.Yul.Expr.lower1Unchecked?_direct_parts
      (offset := 0)
      (by
        simp [EvmCompiler.Yul.Expr.directPureArgSafeAt?,
          EvmCompiler.Yul.Expr.pureAliasArgSafe?,
          EvmCompiler.Yul.Expr.pendingStackDepth])
      hLower
  have hParts :=
    Yul.Source.Effectful.evalValues_lit_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  rcases hParts with ⟨rfl, rfl⟩
  exact
    direct hToLocals hRel hDomain hScope hRun

noncomputable def ofVariable
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat} {name : Name}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before (.Var name) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Var name) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx value) := by
  obtain ⟨rfl, rfl, hToLocals⟩ :=
    EvmCompiler.Yul.Expr.lower1Unchecked?_direct_parts
      (offset := 0)
      (by
        simp [EvmCompiler.Yul.Expr.directPureArgSafeAt?,
          EvmCompiler.Yul.Expr.pureAliasArgSafe?,
          EvmCompiler.Yul.Expr.pendingStackDepth])
      hLower
  obtain ⟨value, _hLookup, rfl, rfl⟩ :=
    Yul.Source.Effectful.evalValues_var_ok_parts
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      hRun
  exact
    direct hToLocals hRel hDomain hScope hRun

end ScopedPreparedValue

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
  stackStable :
    StableArgs contract transcript prepared.finalTarget
      lower.reverse values.reverse

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
      stable := StableArgs.nil prepared.finalTarget
      stackStable := StableArgs.nil prepared.finalTarget }

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
      control := hRest.prepared.control
      varsExtends := hRest.prepared.varsExtends }
  let stableHead :
      StableValue contract transcript prepared.finalTarget lowerHead value :=
    StableValue.deferred hSafe hLower hEval
  let result :
      PreparedArgs contract transcript codeRel program preRest
        (lowerHead :: lowerRest) stateHead sourceFinal target ctx
        (value :: restValues) :=
    { prepared := prepared
      stable := StableArgs.cons stableHead hRest.stable
      stackStable := by
        simpa using
          StableArgs.append hRest.stackStable
            (StableArgs.cons stableHead
              (StableArgs.nil prepared.finalTarget)) }
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
      stable := StableArgs.cons hHeadStable hRestStable
      stackStable := by
        simpa using
          StableArgs.append
            (by
              intro candidate hCandidate
              apply hRest.stackStable candidate
              exact
                StateRelation.Vars.TargetExtends.trans
                  boundValue.prepared.varsExtends hCandidate)
            (StableArgs.cons hHeadStable
              (StableArgs.nil prepared.finalTarget)) }
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

structure ScopedPreparedArgs
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (pre : List Functions.Stmt)
    (lower : List (Locals.Expr 1))
    (fresh : Fresh.State)
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    (values : List Word) where
  prepared :
    PreparedArgs contract transcript codeRel program pre lower
      fresh source target ctx values
  relation :
    StateRelation.Replay.ScopedExactRel codeRel layout
      source prepared.prepared.finalTarget

namespace ScopedPreparedArgs

theorem ofUncheckedLowering
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {initial final : Fresh.State}
    {layout : List Name}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {reversedValues : List Word}
    {Eligible : AstExpr → Prop}
    (hLowering :
      EvmCompiler.Yul.Expr.List.UncheckedBoundLowering
        initial args pre lowerArgs final)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {before after : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {lower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          Eligible expr →
          EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
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
            (ScopedPreparedValue contract transcript codeRel program
              exprPre lower after layout exprSource'
              exprTarget exprCtx value))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
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
      (ScopedPreparedArgs contract transcript codeRel program pre lowerArgs
        final layout source' target ctx reversedValues.reverse) := by
  induction hLowering generalizing fuel source source' target ctx reversedValues with
  | nil =>
      cases fuel with
      | zero =>
          simp [Yul.Source.Effectful.evalArgs,
            Yul.Source.Effectful.fail] at hRun
      | succ previous =>
          simp [Yul.Source.Effectful.evalArgs] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact
            ⟨PreparedArgs.empty
                (StateRelation.Replay.rel_of_scopedExact hRel)
                hDomain hScope,
              hRel⟩
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
        ih
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hExpr hRel hDomain hScope hRestRun
      have hSourceEq : source' = middle :=
        deferredSourceEval_state_eq hDirect.1 hHeadEval
      subst source'
      have hHeadEvalValues :=
        deferredSourceEvalValues_of_eval hDirect.1 hHeadEval
      obtain ⟨_hPre, _hState, hDirectLower⟩ :=
        EvmCompiler.Yul.Expr.lower1Unchecked?_deferred_parts
          hDirect.1 hHead
      obtain
          ⟨targetAfter, hTargetEval, hFinalRel, _hLength,
            _hFinalDomain⟩ :=
        toLocals_forward_targetDomain hDirectLower
          (StateRelation.Replay.rel_of_scopedExact
            restPrepared.relation)
          restPrepared.prepared.prepared.domain hHeadEvalValues
      have hTargetEq :
          targetAfter = restPrepared.prepared.prepared.finalTarget :=
        deferredEval_state_eq hDirect.1 hHead hTargetEval
      subst targetAfter
      let result :=
        PreparedArgs.direct restPrepared.prepared hHead hDirect.1
          hTargetEval hFinalRel
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      exact
        ⟨result,
          StateRelation.Replay.scopedExact_of_rel_store
            result.prepared.rel
            (StateRelation.Replay.sourceStoreDomain_of_scopedExact
              restPrepared.relation)⟩
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
        ih
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hExpr hRel hDomain hScope hRestRun
      obtain ⟨headPrepared⟩ :=
        hExpr (by omega) (hEligible expr (by simp)) hHead
          restPrepared.relation
          restPrepared.prepared.prepared.domain
          restPrepared.prepared.prepared.scope hHeadEval
      let result :=
        PreparedArgs.bound restPrepared.prepared
          headPrepared.prepared hFresh
      have hValues' :
          reversedValues.reverse =
            value :: restReversed.reverse := by
        rw [hValues, hHeadValues]
        simp
      rw [hValues']
      exact
        ⟨result,
          StateRelation.Replay.scopedExact_of_rel_store
            result.prepared.rel
            (StateRelation.Replay.sourceStoreDomain_of_scopedExact
              headPrepared.relation)⟩

end ScopedPreparedArgs

namespace ScopedPreparedValue

noncomputable def ofDirectPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    (hDirect : EvmCompiler.Yul.Expr.List.directPureArgsSafe? args = true)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx value) := by
  obtain ⟨rfl, rfl, hLowering⟩ :=
    EvmCompiler.Yul.Expr.uncheckedDirectPrimitiveLowering_of_lower1Unchecked?
      hDirect hLower
  cases hLowering with
  | @primitive op lowerArgs seq hOp hArgs hSeq hOutputs =>
      obtain
          ⟨callFuel, sourceAfterArgs, reversedValues,
            hFuel, hArgsRun, hPrimRun⟩ :=
        Yul.Source.Effectful.evalValues_primitive_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      cases callFuel with
      | zero =>
          obtain ⟨_hSafe, hPrimCall⟩ :=
            EvmCompiler.Yul.ObserverSafety.SafeSemantics.eval_ok_parts
              hPrimRun
          simp [ObserverSemantics.SourceReplay.primCall,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ primFuel =>
          have hArgsReverse :
              EvmCompiler.Yul.Expr.List.toLocals1? args.reverse =
                some lowerArgs.reverse :=
            EvmCompiler.Yul.Expr.List.toLocals1?_reverse hArgs
          obtain
              ⟨targetAfterArgs, hTargetArgList, hArgsRel, hArgsStore⟩ :=
            (directAt contract transcript codeRel codeOverride
              primFuel.succ).evalArgs
              hArgsReverse
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hArgsRun
          have hSeq' :
              EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) =
                some seq := by
            simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
          have hTargetArgs :
              Locals.Source.Effectful.Expr.ExprSeq.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  seq target =
                .ok (targetAfterArgs, reversedValues) :=
            argListEval_toSeq
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hSeq' hTargetArgList
          have hArgLength :
              reversedValues.length = lowerArgs.reverse.length :=
            Functions.Source.Effectful.ArgList.eval_length
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hTargetArgList
          have hSeqLength :
              lowerArgs.reverse.length =
                Expressions.Structured.BasicOp.inputs op :=
            EvmCompiler.Yul.Expr.List.toSeq?_length hSeq'
          have hArity :
              reversedValues.reverse.length =
                Expressions.Structured.BasicOp.inputs op := by
            simpa [List.length_reverse, hArgLength] using hSeqLength
          obtain
              ⟨targetFinal, hTargetPrimitive, hFinalRel,
                hPrimitiveStore⟩ :=
            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelected
              (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
              hOp hArity hArgsRel hPrimRun
          have hTargetPrimitive' :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).eval
                  op targetAfterArgs reversedValues =
                .ok (targetFinal, values) := by
            simpa using hTargetPrimitive
          have hTarget :
              Functions.Source.Effectful.Expr.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
                  target =
                .ok (targetFinal, values) := by
            rw [exprEval_cast]
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              hTargetArgs, hTargetPrimitive']
          have hLength : values.length = 1 := by
            have hResultLength :=
              Functions.ObserverSafety.SafeSemantics.eval_outputs_length
                hTargetPrimitive'
            simpa [hOutputs] using hResultLength
          cases values with
          | nil =>
              simp at hLength
          | cons value rest =>
              cases rest with
              | nil =>
                  exact
                    ⟨value, rfl,
                      ⟨evaluated hRel hDomain hScope hTarget hFinalRel
                        (hPrimitiveStore.trans hArgsStore)⟩⟩
              | cons next tail =>
                  simp at hLength

noncomputable def ofBoundPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    {Eligible : AstExpr → Prop}
    (hBound : EvmCompiler.Yul.Expr.List.directPureArgsSafe? args = false)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          Eligible expr →
          EvmCompiler.Yul.Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (ScopedPreparedValue contract transcript codeRel program
              exprPre exprLower exprAfter layout exprSource'
              exprTarget exprCtx value))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx value) := by
  let hLowering :=
    EvmCompiler.Yul.Expr.uncheckedBoundPrimitiveLowering_of_lower1Unchecked?
      hBound hLower
  cases hLowering with
  | @primitive _ _ _ op _ lowerArgs seq hOp hArgs hSeq hOutputs =>
      obtain
          ⟨callFuel, sourceAfterArgs, reversedValues,
            hFuel, hArgsRun, hPrimRun⟩ :=
        Yul.Source.Effectful.evalValues_primitive_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      cases callFuel with
      | zero =>
          obtain ⟨_hSafe, hPrimCall⟩ :=
            EvmCompiler.Yul.ObserverSafety.SafeSemantics.eval_ok_parts
              hPrimRun
          simp [ObserverSemantics.SourceReplay.primCall,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ primFuel =>
          obtain ⟨argsPrepared⟩ :=
            ScopedPreparedArgs.ofUncheckedLowering hArgs
              hEligible
              (fun hExprFuel hExprEligible hExprLower hExprRel hExprDomain
                  hExprScope hExprRun =>
                hExpr (by omega) hExprEligible hExprLower hExprRel hExprDomain
                  hExprScope hExprRun)
              hRel hDomain hScope hArgsRun
          let targetAfterArgs :=
            argsPrepared.prepared.prepared.finalTarget
          have hStackArgs :=
            argsPrepared.prepared.stackStable targetAfterArgs
              (StateRelation.Vars.TargetExtends.refl _)
          have hStackArgs' :
              Functions.Source.Effectful.ArgList.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  lowerArgs.reverse targetAfterArgs =
                .ok (targetAfterArgs, reversedValues) := by
            simpa [targetAfterArgs] using hStackArgs
          have hSeq' :
              EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) =
                some seq := by
            simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
          have hTargetArgs :
              Locals.Source.Effectful.Expr.ExprSeq.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  seq targetAfterArgs =
                .ok (targetAfterArgs, reversedValues) :=
            argListEval_toSeq
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hSeq' hStackArgs'
          have hArgLength :
              reversedValues.length = lowerArgs.reverse.length :=
            Functions.Source.Effectful.ArgList.eval_length
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hStackArgs'
          have hSeqLength :
              lowerArgs.reverse.length =
                Expressions.Structured.BasicOp.inputs op :=
            EvmCompiler.Yul.Expr.List.toSeq?_length hSeq'
          have hArity :
              reversedValues.reverse.length =
                Expressions.Structured.BasicOp.inputs op := by
            simpa [List.length_reverse, hArgLength] using hSeqLength
          obtain
              ⟨targetFinal, hTargetPrimitive, hFinalRel,
                hPrimitiveStore⟩ :=
            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelected
              (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
              hOp hArity
              (StateRelation.Replay.rel_of_scopedExact
                argsPrepared.relation)
              hPrimRun
          have hTargetPrimitive' :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).eval
                  op targetAfterArgs reversedValues =
                .ok (targetFinal, values) := by
            simpa using hTargetPrimitive
          have hTarget :
              Functions.Source.Effectful.Expr.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
                  targetAfterArgs =
                .ok (targetFinal, values) := by
            rw [exprEval_cast]
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              hTargetArgs, hTargetPrimitive']
          have hLength : values.length = 1 := by
            have hResultLength :=
              Functions.ObserverSafety.SafeSemantics.eval_outputs_length
                hTargetPrimitive'
            simpa [hOutputs] using hResultLength
          cases values with
          | nil =>
              simp at hLength
          | cons value rest =>
              cases rest with
              | nil =>
                  let prepared :=
                    PreparedValue.afterPrepared
                      argsPrepared.prepared.prepared
                      hTarget hFinalRel
                  refine ⟨value, rfl, ⟨prepared, ?_⟩⟩
                  exact
                    StateRelation.Replay.scopedExact_of_rel_store
                      prepared.rel (by
                        rw [hPrimitiveStore]
                        exact
                          StateRelation.Replay.sourceStoreDomain_of_scopedExact
                            argsPrepared.relation)
              | cons next tail =>
                  simp at hLength

noncomputable def ofPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    {Eligible : AstExpr → Prop}
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          Eligible expr →
          EvmCompiler.Yul.Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (ScopedPreparedValue contract transcript codeRel program
              exprPre exprLower exprAfter layout exprSource'
              exprTarget exprCtx value))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    ∃ value,
      values = [value] ∧
        Nonempty
          (ScopedPreparedValue contract transcript codeRel program
            pre lower after layout source' target ctx value) := by
  cases hDirect :
      EvmCompiler.Yul.Expr.List.directPureArgsSafe? args with
  | false =>
      exact
        ofBoundPrimitive hDirect hLower hEligible hExpr
          hRel hDomain hScope hRun
  | true =>
      exact
        ofDirectPrimitive hDirect hLower hRel hDomain hScope hRun

end ScopedPreparedValue

namespace ScopedPreparedExpression

noncomputable def ofPrimitive
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {fuel results : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr results}
    {before after : Fresh.State} {layout : List Name}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx} {values : List Word}
    {Eligible : AstExpr → Prop}
    (hLower :
      EvmCompiler.Yul.Expr.lowerUnchecked? results before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < fuel →
          Eligible expr →
          EvmCompiler.Yul.Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (ScopedPreparedValue contract transcript codeRel program
              exprPre exprLower exprAfter layout exprSource'
              exprTarget exprCtx value))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel (.Call (.inl prim) args) codeOverride source =
        .ok (source', values)) :
    Nonempty
      (ScopedPreparedExpression contract transcript codeRel program
        pre lower after layout source' target ctx values) := by
  cases
      EvmCompiler.Yul.Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
        hLower with
  | @direct _ _ op lowerArgs seq
      hDirect hOp hArgs hSeq hOutputs =>
      obtain
          ⟨callFuel, sourceAfterArgs, reversedValues,
            hFuel, hArgsRun, hPrimRun⟩ :=
        Yul.Source.Effectful.evalValues_primitive_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      cases callFuel with
      | zero =>
          obtain ⟨_hSafe, hPrimCall⟩ :=
            EvmCompiler.Yul.ObserverSafety.SafeSemantics.eval_ok_parts
              hPrimRun
          simp [ObserverSemantics.SourceReplay.primCall,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ primFuel =>
          have hArgsReverse :
              EvmCompiler.Yul.Expr.List.toLocals1? args.reverse =
                some lowerArgs.reverse :=
            EvmCompiler.Yul.Expr.List.toLocals1?_reverse hArgs
          obtain
              ⟨targetAfterArgs, hTargetArgList, hArgsRel, hArgsStore⟩ :=
            (directAt contract transcript codeRel codeOverride
              primFuel.succ).evalArgs
              hArgsReverse
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hArgsRun
          have hSeq' :
              EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) =
                some seq := by
            simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
          have hTargetArgs :
              Locals.Source.Effectful.Expr.ExprSeq.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  seq target =
                .ok (targetAfterArgs, reversedValues) :=
            argListEval_toSeq
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hSeq' hTargetArgList
          have hArgLength :
              reversedValues.length = lowerArgs.reverse.length :=
            Functions.Source.Effectful.ArgList.eval_length
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hTargetArgList
          have hSeqLength :
              lowerArgs.reverse.length =
                Expressions.Structured.BasicOp.inputs op :=
            EvmCompiler.Yul.Expr.List.toSeq?_length hSeq'
          have hArity :
              reversedValues.reverse.length =
                Expressions.Structured.BasicOp.inputs op := by
            simpa [List.length_reverse, hArgLength] using hSeqLength
          obtain
              ⟨targetFinal, hTargetPrimitive, hFinalRel,
                hPrimitiveStore⟩ :=
            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelected
              (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
              hOp hArity hArgsRel hPrimRun
          have hTargetPrimitive' :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).eval
                  op targetAfterArgs reversedValues =
                .ok (targetFinal, values) := by
            simpa using hTargetPrimitive
          have hTarget :
              Functions.Source.Effectful.Expr.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
                  target =
                .ok (targetFinal, values) := by
            rw [exprEval_cast]
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              hTargetArgs, hTargetPrimitive']
          have hVars :
              targetFinal.source.vars = target.source.vars :=
            Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hTarget
          let prepared :
              PreparedExpression contract transcript codeRel program []
                (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
                before source' target ctx values :=
            PreparedExpression.evaluated
              (program := program) hTarget hFinalRel
              (hDomain.congr hVars) hScope
          refine ⟨prepared, ?_⟩
          exact
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.rel (by
                rw [hPrimitiveStore, hArgsStore]
                exact
                  StateRelation.Replay.sourceStoreDomain_of_scopedExact hRel)
  | @bound _ _ _ op _ lowerArgs seq
      hBound hOp hArgs hSeq hOutputs =>
      obtain
          ⟨callFuel, sourceAfterArgs, reversedValues,
            hFuel, hArgsRun, hPrimRun⟩ :=
        Yul.Source.Effectful.evalValues_primitive_ok_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun
      cases callFuel with
      | zero =>
          obtain ⟨_hSafe, hPrimCall⟩ :=
            EvmCompiler.Yul.ObserverSafety.SafeSemantics.eval_ok_parts
              hPrimRun
          simp [ObserverSemantics.SourceReplay.primCall,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ primFuel =>
          obtain ⟨argsPrepared⟩ :=
            ScopedPreparedArgs.ofUncheckedLowering hArgs
              hEligible
              (fun hExprFuel hExprEligible hExprLower hExprRel hExprDomain
                  hExprScope hExprRun =>
                hExpr (by omega) hExprEligible hExprLower hExprRel hExprDomain
                  hExprScope hExprRun)
              hRel hDomain hScope hArgsRun
          let targetAfterArgs :=
            argsPrepared.prepared.prepared.finalTarget
          have hStackArgs :=
            argsPrepared.prepared.stackStable targetAfterArgs
              (StateRelation.Vars.TargetExtends.refl _)
          have hStackArgs' :
              Functions.Source.Effectful.ArgList.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  lowerArgs.reverse targetAfterArgs =
                .ok (targetAfterArgs, reversedValues) := by
            simpa [targetAfterArgs] using hStackArgs
          have hSeq' :
              EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) =
                some seq := by
            simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
          have hTargetArgs :
              Locals.Source.Effectful.Expr.ExprSeq.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  seq targetAfterArgs =
                .ok (targetAfterArgs, reversedValues) :=
            argListEval_toSeq
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hSeq' hStackArgs'
          have hArgLength :
              reversedValues.length = lowerArgs.reverse.length :=
            Functions.Source.Effectful.ArgList.eval_length
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hStackArgs'
          have hSeqLength :
              lowerArgs.reverse.length =
                Expressions.Structured.BasicOp.inputs op :=
            EvmCompiler.Yul.Expr.List.toSeq?_length hSeq'
          have hArity :
              reversedValues.reverse.length =
                Expressions.Structured.BasicOp.inputs op := by
            simpa [List.length_reverse, hArgLength] using hSeqLength
          obtain
              ⟨targetFinal, hTargetPrimitive, hFinalRel,
                hPrimitiveStore⟩ :=
            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelected
              (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
              hOp hArity
              (StateRelation.Replay.rel_of_scopedExact
                argsPrepared.relation)
              hPrimRun
          have hTargetPrimitive' :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).eval
                  op targetAfterArgs reversedValues =
                .ok (targetFinal, values) := by
            simpa using hTargetPrimitive
          have hTarget :
              Functions.Source.Effectful.Expr.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
                  targetAfterArgs =
                .ok (targetFinal, values) := by
            rw [exprEval_cast]
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              hTargetArgs, hTargetPrimitive']
          let prepared :=
            PreparedExpression.afterPrepared
              argsPrepared.prepared.prepared hTarget hFinalRel
          refine ⟨prepared, ?_⟩
          exact
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.rel (by
                rw [hPrimitiveStore]
                exact
                  StateRelation.Replay.sourceStoreDomain_of_scopedExact
                    argsPrepared.relation)

end ScopedPreparedExpression

end FunctionsObserverExpression
end Yul
end EvmCompiler
