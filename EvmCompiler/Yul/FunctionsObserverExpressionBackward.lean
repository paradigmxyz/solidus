import EvmCompiler.Yul.FunctionsObserverExpression
import EvmCompiler.Yul.SolcValidation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverExpressionBackward

open FunctionsObserverExpression

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

structure AlignedValueBackward
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat)
    (before after : Fresh.State)
    (layout : List Name)
    (expr : AstExpr)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript)
    (ctx finalCtx : Functions.Source.Ctx)
    (value : Word) where
  sourceFinal : ObserverSemantics.SourceReplay.State transcript
  sourceValuesRun :
    Yul.Source.Effectful.evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        fuel expr codeOverride source =
      .ok (sourceFinal, [value])
  sourceRun :
    Yul.Source.Effectful.eval
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        fuel expr codeOverride source =
      .ok (sourceFinal, value)
  prepared :
    ScopedPreparedValue contract transcript codeRel program
      pre lower after layout sourceFinal target ctx value
  preTarget_eq : prepared.prepared.preTarget = preTarget
  evalTarget_eq : prepared.prepared.evalTarget = evalTarget
  finalCtx_eq : prepared.prepared.finalCtx = finalCtx

structure AlignedArgsBackward
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat)
    (initial final : Fresh.State)
    (layout : List Name)
    (args : List AstExpr)
    (pre : List Functions.Stmt)
    (lower : List (Locals.Expr 1))
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target targetFinal : Functions.ObserverSemantics.State transcript)
    (ctx finalCtx : Functions.Source.Ctx) where
  sourceFinal : ObserverSemantics.SourceReplay.State transcript
  values : List Word
  sourceRun :
    Yul.Source.Effectful.evalArgs
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        fuel args.reverse codeOverride source =
      .ok (sourceFinal, values.reverse)
  prepared :
    ScopedPreparedArgs contract transcript codeRel program
      pre lower final layout sourceFinal target ctx values
  finalTarget_eq :
    prepared.prepared.prepared.finalTarget = targetFinal
  finalCtx_eq :
    prepared.prepared.prepared.finalCtx = finalCtx

structure AlignedExpressionBackward
    {results : Nat}
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (fuel : Nat)
    (before after : Fresh.State)
    (layout : List Name)
    (expr : AstExpr)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr results)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript)
    (ctx finalCtx : Functions.Source.Ctx)
    (values : List Word) where
  sourceFinal : ObserverSemantics.SourceReplay.State transcript
  sourceRun :
    Yul.Source.Effectful.evalValues
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        fuel expr codeOverride source =
      .ok (sourceFinal, values)
  prepared :
    ScopedPreparedExpression contract transcript codeRel program
      pre lower after layout sourceFinal target ctx values
  preTarget_eq : prepared.prepared.preTarget = preTarget
  evalTarget_eq : prepared.prepared.evalTarget = evalTarget
  finalCtx_eq : prepared.prepared.finalCtx = finalCtx

def RecursiveAlignedValueBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (layout : List Name) : Prop :=
  ∀ {exprFuel targetExprFuel : Nat}
    {before after : Fresh.State}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {value : Word},
    directFuel expr ≤ exprFuel →
    SolcValidation.ExprOk? profile sourceContract layout 1 expr = true →
    EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
      some (pre, lower, after) →
    StateRelation.Replay.ScopedExactRel
      codeRel layout source target →
    StateRelation.Vars.TargetDomainWithin
      before.used target.source.vars →
    StateRelation.Vars.NamesWithin before.used ctx.scope →
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx targetExprFuel { stmts := pre } target =
      .ok
        (Functions.Source.Effectful.Outcome.regular preTarget, finalCtx) →
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        lower preTarget =
      .ok (evalTarget, [value]) →
    Nonempty
      (AlignedValueBackward contract transcript codeRel program
        codeOverride exprFuel before after layout expr pre lower source
        target preTarget evalTarget ctx finalCtx value)

structure SomeAlignedValueBackward
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (before after : Fresh.State)
    (layout : List Name)
    (expr : AstExpr)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript)
    (ctx finalCtx : Functions.Source.Ctx)
    (value : Word) where
  sourceFuel : Nat
  result :
    AlignedValueBackward contract transcript codeRel program codeOverride
      sourceFuel before after layout expr pre lower source target preTarget
      evalTarget ctx finalCtx value

structure SomeAlignedArgsBackward
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (initial final : Fresh.State)
    (layout : List Name)
    (args : List AstExpr)
    (pre : List Functions.Stmt)
    (lower : List (Locals.Expr 1))
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target targetFinal : Functions.ObserverSemantics.State transcript)
    (ctx finalCtx : Functions.Source.Ctx) where
  sourceFuel : Nat
  result :
    AlignedArgsBackward contract transcript codeRel program codeOverride
      sourceFuel initial final layout args pre lower source target targetFinal
      ctx finalCtx

structure SomeAlignedExpressionBackward
    {results : Nat}
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (before after : Fresh.State)
    (layout : List Name)
    (expr : AstExpr)
    (pre : List Functions.Stmt)
    (lower : Locals.Expr results)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript)
    (ctx finalCtx : Functions.Source.Ctx)
    (values : List Word) where
  sourceFuel : Nat
  result :
    AlignedExpressionBackward contract transcript codeRel program
      codeOverride sourceFuel before after layout expr pre lower source target
      preTarget evalTarget ctx finalCtx values

def RecursiveAlignedValueBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (layout : List Name)
    (bound : Nat) : Prop :=
  ∀ {targetExprFuel : Nat}
    {before after : Fresh.State}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {value : Word},
    targetExprFuel < bound →
    SolcValidation.ExprOk? profile sourceContract layout 1 expr = true →
    EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
      some (pre, lower, after) →
    StateRelation.Replay.ScopedExactRel
      codeRel layout source target →
    StateRelation.Vars.TargetDomainWithin
      before.used target.source.vars →
    StateRelation.Vars.NamesWithin before.used ctx.scope →
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx targetExprFuel { stmts := pre } target =
      .ok
        (Functions.Source.Effectful.Outcome.regular preTarget, finalCtx) →
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        lower preTarget =
      .ok (evalTarget, [value]) →
    Nonempty
      (SomeAlignedValueBackward contract transcript codeRel program
        codeOverride before after layout expr pre lower source target
        preTarget evalTarget ctx finalCtx value)

theorem deferredBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {fuel : Nat} {before after : Fresh.State}
    {layout : List Name} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hFuel : directFuel expr ≤ fuel)
    (hOk :
      SolcValidation.ExprOk? profile sourceContract layout 1 expr = true)
    (hSafe : EvmCompiler.Yul.Expr.deferredBoundArgSafe? expr = true)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope) :
    ∃ value,
      Nonempty
        (AlignedValueBackward contract transcript codeRel program codeOverride
          fuel before after layout expr pre lower source target target target
          ctx ctx value) := by
  obtain ⟨rfl, rfl, hDirect⟩ :=
    EvmCompiler.Yul.Expr.lower1Unchecked?_deferred_parts hSafe hLower
  cases expr with
  | Lit literal =>
      simp [EvmCompiler.Yul.Expr.toLocals?,
        EvmCompiler.Yul.Expr.cast] at hDirect
      subst lower
      let hTarget :
          Functions.Source.Effectful.Expr.eval
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (.lit literal : Locals.Expr 1) target =
            .ok (target, [literal]) :=
        Functions.Source.Effectful.Expr.eval_lit
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          literal target
      have hSourceValues :
          Yul.Source.Effectful.evalValues
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              fuel (.Lit literal) codeOverride source =
            .ok (source, [literal]) := by
        cases fuel with
        | zero =>
            simp [directFuel] at hFuel
        | succ previous =>
            simp [Yul.Source.Effectful.evalValues]
      have hSourceOne :
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
              fuel (.Lit literal) codeOverride source =
            .ok (source, literal) := by
        cases fuel with
        | zero =>
            simp [directFuel] at hFuel
        | succ previous =>
            simp [Yul.Source.Effectful.eval,
              Yul.Source.Effectful.evalValues]
      let prepared :=
        PreparedValue.evaluated
          (program := program) hTarget
          (StateRelation.Replay.rel_of_scopedExact hRel)
          hDomain hScope
      exact
        ⟨literal,
          ⟨source, hSourceValues, hSourceOne,
            ⟨prepared, hRel⟩, rfl, rfl, rfl⟩⟩
  | Var name =>
      simp [EvmCompiler.Yul.Expr.toLocals?,
        EvmCompiler.Yul.Expr.cast] at hDirect
      subst lower
      simp only [SolcValidation.ExprOk?, Bool.and_eq_true,
        decide_eq_true_eq] at hOk
      rcases hOk with ⟨_hResults, hName⟩
      rcases hRel.2 with
        ⟨sourceShared, sourceVars, hSourceState, hShared,
          hScoped, hSourceDomain⟩
      have hTargetLookup :
          target.source.vars (identName name) =
            sourceVars.lookup name := by
        simpa [hSourceState] using
          (hScoped (identName name) hName).symm
      cases hLookup : sourceVars.lookup name with
      | none =>
          have hSome :=
            (hSourceDomain (identName name)).mpr hName
          simp [identName, hLookup] at hSome
      | some value =>
          have hTargetLookup' :
              target.source.vars (identName name) = some value := by
            simpa [hLookup] using hTargetLookup
          let hTarget :
              Functions.Source.Effectful.Expr.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (.var (identName name) : Locals.Expr 1) target =
                .ok (target, [value]) :=
            Functions.Source.Effectful.Expr.eval_var_of_lookup
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hTargetLookup'
          have hSourceValues :
              Yul.Source.Effectful.evalValues
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  fuel (.Var name) codeOverride source =
                .ok (source, [value]) := by
            cases fuel with
            | zero =>
                simp [directFuel] at hFuel
            | succ previous =>
                simp [Yul.Source.Effectful.evalValues,
                  ObserverSemantics.SourceReplay.stateModel,
                  hSourceState, EvmYul.Yul.State.lookup?, hLookup]
          have hSourceOne :
              Yul.Source.Effectful.eval
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  fuel (.Var name) codeOverride source =
                .ok (source, value) := by
            cases fuel with
            | zero =>
                simp [directFuel] at hFuel
            | succ previous =>
                simp [Yul.Source.Effectful.eval,
                  Yul.Source.Effectful.evalValues,
                  ObserverSemantics.SourceReplay.stateModel,
                  hSourceState, EvmYul.Yul.State.lookup?, hLookup]
          let prepared :=
            PreparedValue.evaluated
              (program := program) hTarget
              (StateRelation.Replay.rel_of_scopedExact hRel)
              hDomain hScope
          exact
            ⟨value,
              ⟨source, hSourceValues, hSourceOne,
                ⟨prepared, hRel⟩, rfl, rfl, rfl⟩⟩
  | Call callee args =>
      simp [EvmCompiler.Yul.Expr.deferredBoundArgSafe?] at hSafe

theorem boundArgsBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {initial final : Fresh.State}
    {layout : List Name} {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {fuel targetFuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    (hFuel : directArgsFuel args ≤ fuel)
    (hLowering :
      EvmCompiler.Yul.Expr.List.UncheckedBoundLowering
        initial args pre lower final)
    (hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr = true)
    (hExpr :
      RecursiveAlignedValueBackwardAt profile sourceContract contract
        transcript codeRel program codeOverride layout)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            finalCtx)) :
    Nonempty
      (AlignedArgsBackward contract transcript codeRel program codeOverride
        fuel initial final layout args pre lower source target targetFinal
        ctx finalCtx) := by
  induction hLowering generalizing fuel source target targetFinal ctx finalCtx
      targetFuel with
  | nil =>
      obtain ⟨hOutcome, hCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hRun
      injection hOutcome with hTarget
      subst targetFinal
      subst finalCtx
      have hSource :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              fuel [] codeOverride source =
            .ok (source, []) := by
        cases fuel with
        | zero =>
            have hOne := one_le_directArgsFuel []
            omega
        | succ previous =>
            simp [Yul.Source.Effectful.evalArgs]
      let prepared :=
        PreparedArgs.empty
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (program := program)
          (StateRelation.Replay.rel_of_scopedExact hRel)
          hDomain hScope
      exact
        ⟨source, [], hSource, ⟨prepared, hRel⟩, rfl, rfl⟩
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      obtain ⟨rfl, rfl, hHeadDirect⟩ :=
        EvmCompiler.Yul.Expr.lower1Unchecked?_deferred_parts
          hDirect.1 hHead
      have hRestFuel : directArgsFuel rest ≤ fuel := by
        unfold directArgsFuel at hFuel ⊢
        simp only [List.length_cons, maxDirectFuel] at hFuel
        have hMax :
            maxDirectFuel rest ≤
              max (directFuel expr) (maxDirectFuel rest) :=
          Nat.le_max_right _ _
        omega
      obtain ⟨restBackward⟩ :=
        ih hRestFuel
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hRel hDomain hScope (by simpa using hRun)
      let restTarget :=
        restBackward.prepared.prepared.prepared.finalTarget
      let restCtx :=
        restBackward.prepared.prepared.prepared.finalCtx
      let headFuel := fuel - (2 * rest.length + 1)
      have hHeadFuel :
          directFuel expr + 1 ≤ headFuel := by
        dsimp [headFuel]
        unfold directArgsFuel at hFuel
        simp only [List.length_cons, maxDirectFuel] at hFuel
        have hMax :
            directFuel expr ≤
              max (directFuel expr) (maxDirectFuel rest) :=
          Nat.le_max_left _ _
        omega
      obtain ⟨value, ⟨headBackward⟩⟩ :=
        deferredBackwardAt profile sourceContract contract transcript
          codeRel program codeOverride
          (le_trans (Nat.le_add_right _ _) hHeadFuel)
          (by
            exact
              hEligible expr (by simp))
          hDirect.1 hHead
          restBackward.prepared.relation
          restBackward.prepared.prepared.prepared.domain
          restBackward.prepared.prepared.prepared.scope
      have hHeadEval :=
        headBackward.prepared.prepared.eval
      rw [headBackward.preTarget_eq,
        headBackward.evalTarget_eq] at hHeadEval
      have hHeadRel :=
        StateRelation.Replay.rel_of_scopedExact
          headBackward.prepared.relation
      rw [headBackward.evalTarget_eq] at hHeadRel
      have hHeadScoped := headBackward.prepared.relation
      rw [headBackward.evalTarget_eq] at hHeadScoped
      let prepared :=
        PreparedArgs.direct restBackward.prepared.prepared
          hHead hDirect.1 hHeadEval hHeadRel
      let scopedPrepared :
          ScopedPreparedArgs contract transcript codeRel program
            (preRest ++ []) (lowerHead :: lowerRest) stateHead layout
            headBackward.sourceFinal target ctx
            (value :: restBackward.values) :=
        { prepared := prepared
          relation := by
            exact
              StateRelation.Replay.scopedExact_of_rel_store
                prepared.prepared.rel
                (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                  hHeadScoped) }
      have hHeadArgs :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (headFuel + 1) [expr] codeOverride
              restBackward.sourceFinal =
            .ok (headBackward.sourceFinal, [value]) :=
        Yul.Source.Effectful.evalArgs_singleton_of_eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (le_trans
            (Nat.add_le_add_right (one_le_directFuel expr) 1)
            hHeadFuel)
          headBackward.sourceRun
      have hFuelSplit :
          fuel = (headFuel + 1) + 2 * rest.reverse.length := by
        dsimp [headFuel]
        simp only [List.length_reverse]
        omega
      have hSource :=
        Yul.Source.Effectful.evalArgs_append_of_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hFuelSplit restBackward.sourceRun hHeadArgs
      have hSource' :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              fuel (expr :: rest).reverse codeOverride source =
            .ok
              (headBackward.sourceFinal,
                (value :: restBackward.values).reverse) := by
        simpa using hSource
      obtain ⟨preparedFuel, hPreparedRun⟩ :=
        scopedPrepared.prepared.prepared.run
      obtain ⟨hTargetEq, hCtxEq⟩ :=
        Functions.Source.Effectful.Block.runOpen_regular_unique
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPreparedRun hRun
      exact
        ⟨headBackward.sourceFinal, value :: restBackward.values,
          hSource', scopedPrepared, hTargetEq, hCtxEq⟩
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      obtain
          ⟨targetAfterRest, ctxAfterRest,
            ⟨restFuel, hRestRun⟩, ⟨suffixFuel, hSuffixRun⟩⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (left := preRest)
          (right := preHead ++ [.let_ tmp lowerHead])
          (by simpa [List.append_assoc] using hRun)
      obtain
          ⟨targetAfterHead, ctxAfterHead,
            ⟨headTargetFuel, hHeadRun⟩,
            ⟨letBlockFuel, hLetBlockRun⟩⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (left := preHead)
          (right := [.let_ tmp lowerHead])
          hSuffixRun
      obtain ⟨letFuel, hLetRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_singleton_regular_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hLetBlockRun
      obtain
          ⟨targetAfterValue, value, hHeadEval,
            hTargetFinal, hFinalCtx⟩ :=
        Functions.Source.Effectful.Stmt.run_let_regular_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hLetRun
      have hRestFuel : directArgsFuel rest ≤ fuel := by
        unfold directArgsFuel at hFuel ⊢
        simp only [List.length_cons, maxDirectFuel] at hFuel
        have hMax :
            maxDirectFuel rest ≤
              max (directFuel expr) (maxDirectFuel rest) :=
          Nat.le_max_right _ _
        omega
      obtain ⟨restBackward⟩ :=
        ih hRestFuel
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hRel hDomain hScope hRestRun
      have hRestTarget :
          restBackward.prepared.prepared.prepared.finalTarget =
            targetAfterRest :=
        restBackward.finalTarget_eq
      have hRestCtx :
          restBackward.prepared.prepared.prepared.finalCtx =
            ctxAfterRest :=
        restBackward.finalCtx_eq
      let headFuel := fuel - (2 * rest.length + 1)
      have hHeadFuel :
          directFuel expr + 1 ≤ headFuel := by
        dsimp [headFuel]
        unfold directArgsFuel at hFuel
        simp only [List.length_cons, maxDirectFuel] at hFuel
        have hMax :
            directFuel expr ≤
              max (directFuel expr) (maxDirectFuel rest) :=
          Nat.le_max_left _ _
        omega
      have hHeadRun' :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program
              restBackward.prepared.prepared.prepared.finalCtx
              headTargetFuel { stmts := preHead }
              restBackward.prepared.prepared.prepared.finalTarget =
            .ok
              (Functions.Source.Effectful.Outcome.regular targetAfterHead,
                ctxAfterHead) := by
        simpa [hRestTarget, hRestCtx] using hHeadRun
      obtain ⟨headBackward⟩ :=
        hExpr
          (le_trans (Nat.le_add_right _ _) hHeadFuel)
          (hEligible expr (by simp))
          hHead restBackward.prepared.relation
          restBackward.prepared.prepared.prepared.domain
          restBackward.prepared.prepared.prepared.scope
          hHeadRun' hHeadEval
      have hHeadPreTarget :
          headBackward.prepared.prepared.preTarget =
            targetAfterHead :=
        headBackward.preTarget_eq
      have hHeadEvalTarget :
          headBackward.prepared.prepared.evalTarget =
            targetAfterValue :=
        headBackward.evalTarget_eq
      have hHeadFinalCtx :
          headBackward.prepared.prepared.finalCtx =
            ctxAfterHead :=
        headBackward.finalCtx_eq
      let prepared :=
        PreparedArgs.bound
          restBackward.prepared.prepared
          headBackward.prepared.prepared hFresh
      let scopedPrepared :
          ScopedPreparedArgs contract transcript codeRel program
            (preRest ++ preHead ++ [.let_ tmp lowerHead])
            (.var tmp :: lowerRest) stateFresh layout
            headBackward.sourceFinal target ctx
            (value :: restBackward.values) :=
        { prepared := prepared
          relation := by
            exact
              StateRelation.Replay.scopedExact_of_rel_store
                prepared.prepared.rel
                (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                  headBackward.prepared.relation) }
      have hHeadArgs :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (headFuel + 1) [expr] codeOverride
              restBackward.sourceFinal =
            .ok (headBackward.sourceFinal, [value]) :=
        Yul.Source.Effectful.evalArgs_singleton_of_eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (le_trans
            (Nat.add_le_add_right (one_le_directFuel expr) 1)
            hHeadFuel)
          headBackward.sourceRun
      have hFuelSplit :
          fuel = (headFuel + 1) + 2 * rest.reverse.length := by
        dsimp [headFuel]
        simp only [List.length_reverse]
        omega
      have hSource :=
        Yul.Source.Effectful.evalArgs_append_of_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hFuelSplit restBackward.sourceRun hHeadArgs
      have hSource' :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              fuel (expr :: rest).reverse codeOverride source =
            .ok
              (headBackward.sourceFinal,
                (value :: restBackward.values).reverse) := by
        simpa using hSource
      obtain ⟨preparedFuel, hPreparedRun⟩ :=
        scopedPrepared.prepared.prepared.run
      obtain ⟨hTargetEq, hCtxEq⟩ :=
        Functions.Source.Effectful.Block.runOpen_regular_unique
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPreparedRun hRun
      exact
        ⟨headBackward.sourceFinal, value :: restBackward.values,
          hSource', scopedPrepared, hTargetEq, hCtxEq⟩

theorem boundArgsBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {initial final : Fresh.State}
    {layout : List Name} {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : List (Locals.Expr 1)}
    {targetFuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target targetFinal : Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    (hTargetFuel : targetFuel < bound)
    (hLowering :
      EvmCompiler.Yul.Expr.List.UncheckedBoundLowering
        initial args pre lower final)
    (hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr = true)
    (hExpr :
      RecursiveAlignedValueBackwardBelow profile sourceContract contract
        transcript codeRel program codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin initial.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin initial.used ctx.scope)
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetFinal,
            finalCtx)) :
    Nonempty
      (SomeAlignedArgsBackward contract transcript codeRel program
        codeOverride initial final layout args pre lower source target
        targetFinal ctx finalCtx) := by
  induction hLowering generalizing source target targetFinal ctx finalCtx
      targetFuel with
  | nil =>
      obtain ⟨hOutcome, hCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hRun
      injection hOutcome with hTarget
      subst targetFinal
      subst finalCtx
      have hSource :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              1 [] codeOverride source =
            .ok (source, []) := by
        simp [Yul.Source.Effectful.evalArgs]
      let prepared :=
        PreparedArgs.empty
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (program := program)
          (StateRelation.Replay.rel_of_scopedExact hRel)
          hDomain hScope
      exact
        ⟨⟨1,
          ⟨source, [], hSource, ⟨prepared, hRel⟩, rfl, rfl⟩⟩⟩
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      obtain ⟨rfl, rfl, hHeadDirect⟩ :=
        EvmCompiler.Yul.Expr.lower1Unchecked?_deferred_parts
          hDirect.1 hHead
      obtain ⟨restBackward⟩ :=
        ih hTargetFuel
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hRel hDomain hScope (by simpa using hRun)
      let restExact := restBackward.result
      let restTarget :=
        restExact.prepared.prepared.prepared.finalTarget
      let restCtx :=
        restExact.prepared.prepared.prepared.finalCtx
      let headFuel := max (directFuel expr) 2
      obtain ⟨value, ⟨headExact⟩⟩ :=
        deferredBackwardAt profile sourceContract contract transcript
          codeRel program codeOverride
          (Nat.le_max_left _ _) (hEligible expr (by simp))
          hDirect.1 hHead
          restExact.prepared.relation
          restExact.prepared.prepared.prepared.domain
          restExact.prepared.prepared.prepared.scope
      have hHeadEval :=
        headExact.prepared.prepared.eval
      rw [headExact.preTarget_eq, headExact.evalTarget_eq] at hHeadEval
      have hHeadRel :=
        StateRelation.Replay.rel_of_scopedExact
          headExact.prepared.relation
      rw [headExact.evalTarget_eq] at hHeadRel
      have hHeadScoped := headExact.prepared.relation
      rw [headExact.evalTarget_eq] at hHeadScoped
      let prepared :=
        PreparedArgs.direct restExact.prepared.prepared
          hHead hDirect.1 hHeadEval hHeadRel
      let scopedPrepared :
          ScopedPreparedArgs contract transcript codeRel program
            (preRest ++ []) (lowerHead :: lowerRest) stateHead layout
            headExact.sourceFinal target ctx
            (value :: restExact.values) :=
        { prepared := prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.prepared.rel
              (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                hHeadScoped) }
      let commonFuel := max headFuel restBackward.sourceFuel
      have hHeadFuelLe : headFuel ≤ commonFuel :=
        Nat.le_max_left _ _
      have hRestFuelLe : restBackward.sourceFuel ≤ commonFuel :=
        Nat.le_max_right _ _
      have hHeadSource :
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              commonFuel expr codeOverride restExact.sourceFinal =
            .ok (headExact.sourceFinal, value) :=
        Yul.Source.Effectful.eval_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          hHeadFuelLe headExact.sourceRun
      have hTwo : 2 ≤ commonFuel := by
        have : 2 ≤ headFuel := Nat.le_max_right _ _
        exact le_trans this hHeadFuelLe
      have hHeadArgs :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (commonFuel + 1) [expr] codeOverride restExact.sourceFinal =
            .ok (headExact.sourceFinal, [value]) :=
        Yul.Source.Effectful.evalArgs_singleton_of_eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hTwo hHeadSource
      let sourceFuel := (commonFuel + 1) + 2 * rest.reverse.length
      have hRestSource :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              sourceFuel rest.reverse codeOverride source =
            .ok (restExact.sourceFinal, restExact.values.reverse) :=
        Yul.Source.Effectful.evalArgs_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          (by
            dsimp [sourceFuel]
            omega)
          restExact.sourceRun
      have hSource :=
        Yul.Source.Effectful.evalArgs_append_of_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (fuel := sourceFuel) (remainingFuel := commonFuel + 1)
          (by rfl) hRestSource hHeadArgs
      have hSource' :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              sourceFuel (expr :: rest).reverse codeOverride source =
            .ok
              (headExact.sourceFinal,
                (value :: restExact.values).reverse) := by
        simpa using hSource
      obtain ⟨preparedFuel, hPreparedRun⟩ :=
        scopedPrepared.prepared.prepared.run
      obtain ⟨hTargetEq, hCtxEq⟩ :=
        Functions.Source.Effectful.Block.runOpen_regular_unique
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPreparedRun hRun
      exact
        ⟨⟨sourceFuel,
          ⟨headExact.sourceFinal, value :: restExact.values,
            hSource', scopedPrepared, hTargetEq, hCtxEq⟩⟩⟩
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      obtain
          ⟨targetAfterRest, ctxAfterRest, suffixFuel,
            hRestRun, hSuffixRun, hSuffixFuel⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (left := preRest)
          (right := preHead ++ [.let_ tmp lowerHead])
          (by simpa [List.append_assoc] using hRun)
      obtain
          ⟨targetAfterHead, ctxAfterHead, letBlockFuel,
            hHeadRun, hLetBlockRun, _hLetFuel⟩ :=
        Functions.Source.Effectful.Block.runOpen_append_regular_bounded_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          (left := preHead)
          (right := [.let_ tmp lowerHead])
          hSuffixRun
      obtain ⟨letFuel, hLetRun⟩ :=
        Functions.Source.Effectful.Block.runOpen_singleton_regular_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hLetBlockRun
      obtain
          ⟨targetAfterValue, value, hHeadEval,
            hTargetFinal, hFinalCtx⟩ :=
        Functions.Source.Effectful.Stmt.run_let_regular_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hLetRun
      obtain ⟨restBackward⟩ :=
        ih hTargetFuel
          (fun candidate hMem =>
            hEligible candidate (List.mem_cons_of_mem expr hMem))
          hRel hDomain hScope hRestRun
      let restExact := restBackward.result
      have hRestTarget :
          restExact.prepared.prepared.prepared.finalTarget =
            targetAfterRest :=
        restExact.finalTarget_eq
      have hRestCtx :
          restExact.prepared.prepared.prepared.finalCtx =
            ctxAfterRest :=
        restExact.finalCtx_eq
      have hHeadRun' :
          Functions.Source.Effectful.Block.runOpen
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program restExact.prepared.prepared.prepared.finalCtx
              suffixFuel { stmts := preHead }
              restExact.prepared.prepared.prepared.finalTarget =
            .ok
              (Functions.Source.Effectful.Outcome.regular targetAfterHead,
                ctxAfterHead) := by
        simpa [hRestTarget, hRestCtx] using hHeadRun
      obtain ⟨headBackward⟩ :=
        hExpr
          (lt_of_le_of_lt hSuffixFuel hTargetFuel)
          (hEligible expr (by simp))
          hHead restExact.prepared.relation
          restExact.prepared.prepared.prepared.domain
          restExact.prepared.prepared.prepared.scope
          hHeadRun' hHeadEval
      let headExact := headBackward.result
      have hHeadPreTarget :
          headExact.prepared.prepared.preTarget =
            targetAfterHead :=
        headExact.preTarget_eq
      have hHeadEvalTarget :
          headExact.prepared.prepared.evalTarget =
            targetAfterValue :=
        headExact.evalTarget_eq
      have hHeadFinalCtx :
          headExact.prepared.prepared.finalCtx =
            ctxAfterHead :=
        headExact.finalCtx_eq
      let prepared :=
        PreparedArgs.bound
          restExact.prepared.prepared
          headExact.prepared.prepared hFresh
      let scopedPrepared :
          ScopedPreparedArgs contract transcript codeRel program
            (preRest ++ preHead ++ [.let_ tmp lowerHead])
            (.var tmp :: lowerRest) stateFresh layout
            headExact.sourceFinal target ctx
            (value :: restExact.values) :=
        { prepared := prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.prepared.rel
              (StateRelation.Replay.sourceStoreDomain_of_scopedExact
                headExact.prepared.relation) }
      let commonFuel :=
        max (max headBackward.sourceFuel 2) restBackward.sourceFuel
      have hHeadFuelLe : headBackward.sourceFuel ≤ commonFuel :=
        le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      have hRestFuelLe : restBackward.sourceFuel ≤ commonFuel :=
        Nat.le_max_right _ _
      have hTwo : 2 ≤ commonFuel :=
        le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
      have hHeadSource :
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              commonFuel expr codeOverride restExact.sourceFinal =
            .ok (headExact.sourceFinal, value) :=
        Yul.Source.Effectful.eval_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          hHeadFuelLe headExact.sourceRun
      have hHeadArgs :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (commonFuel + 1) [expr] codeOverride restExact.sourceFinal =
            .ok (headExact.sourceFinal, [value]) :=
        Yul.Source.Effectful.evalArgs_singleton_of_eval
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hTwo hHeadSource
      let sourceFuel := (commonFuel + 1) + 2 * rest.reverse.length
      have hRestSource :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              sourceFuel rest.reverse codeOverride source =
            .ok (restExact.sourceFinal, restExact.values.reverse) :=
        Yul.Source.Effectful.evalArgs_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          (by
            dsimp [sourceFuel]
            omega)
          restExact.sourceRun
      have hSource :=
        Yul.Source.Effectful.evalArgs_append_of_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (fuel := sourceFuel) (remainingFuel := commonFuel + 1)
          (by rfl) hRestSource hHeadArgs
      have hSource' :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              sourceFuel (expr :: rest).reverse codeOverride source =
            .ok
              (headExact.sourceFinal,
                (value :: restExact.values).reverse) := by
        simpa using hSource
      obtain ⟨preparedFuel, hPreparedRun⟩ :=
        scopedPrepared.prepared.prepared.run
      obtain ⟨hTargetEq, hCtxEq⟩ :=
        Functions.Source.Effectful.Block.runOpen_regular_unique
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPreparedRun hRun
      exact
        ⟨⟨sourceFuel,
          ⟨headExact.sourceFinal, value :: restExact.values,
            hSource', scopedPrepared, hTargetEq, hCtxEq⟩⟩⟩

theorem boundPrimitiveExpressionBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {results targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {values : List Word}
    (hTargetFuel : targetFuel < bound)
    (hOk :
      SolcValidation.ExprOk? profile sourceContract layout results
          (.Call (.inl prim) args) =
        true)
    (hLower :
      EvmCompiler.Yul.Expr.lowerUnchecked? results before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hBound :
      EvmCompiler.Yul.Expr.List.directPureArgsSafe? args = false)
    (hExpr :
      RecursiveAlignedValueBackwardBelow profile sourceContract contract
        transcript codeRel program codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hPre :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget,
            finalCtx))
    (hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower preTarget =
        .ok (evalTarget, values)) :
    Nonempty
      (SomeAlignedExpressionBackward contract transcript codeRel program
        codeOverride before after layout (.Call (.inl prim) args)
        pre lower source target preTarget evalTarget ctx finalCtx values) := by
  have hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr =
          true := by
    intro expr hMem
    exact
      SolcValidation.exprOk_of_exprsOk_of_mem
        (SolcValidation.exprsOk_of_exprOk_primitive hOk) hMem
  cases
      EvmCompiler.Yul.Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
        hLower with
  | @direct _ _ op lowerArgs seq
      hDirect hOp hArgs hSeq hOutputs =>
      rw [hBound] at hDirect
      contradiction
  | @bound _ _ _ op _ lowerArgs seq
      hBound hOp hArgs hSeq hOutputs =>
      obtain ⟨argsBackward⟩ :=
        boundArgsBackwardBelow profile sourceContract contract transcript
          codeRel program codeOverride bound hTargetFuel hArgs hEligible
          hExpr hRel hDomain hScope hPre
      let exactArgs := argsBackward.result
      have hTarget' := hTarget
      rw [FunctionsObserverExpression.exprEval_cast] at hTarget'
      obtain
          ⟨targetAfterArgs, reversedValues,
            hTargetSeq, hTargetPrimitive⟩ :=
        Functions.Source.Effectful.Expr.eval_prim_ok_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hTarget'
      have hSeq' :
          EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) =
            some seq := by
        simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
      have hStableArgs :=
        exactArgs.prepared.prepared.stackStable
          exactArgs.prepared.prepared.prepared.finalTarget
          (StateRelation.Vars.TargetExtends.refl _)
      have hStableArgs' :
          Functions.Source.Effectful.ArgList.eval
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              lowerArgs.reverse
              exactArgs.prepared.prepared.prepared.finalTarget =
            .ok
              (exactArgs.prepared.prepared.prepared.finalTarget,
                exactArgs.values.reverse) := by
        simpa using hStableArgs
      have hPreparedSeq :=
        FunctionsObserverExpression.argListEval_toSeq
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hSeq' hStableArgs'
      have hPreTarget :
          exactArgs.prepared.prepared.prepared.finalTarget =
            preTarget :=
        exactArgs.finalTarget_eq
      rw [hPreTarget] at hPreparedSeq
      rw [hPreparedSeq] at hTargetSeq
      injection hTargetSeq with hArgsResult
      injection hArgsResult with hAfterArgs hValues
      subst targetAfterArgs
      subst reversedValues
      let callFuel := max argsBackward.sourceFuel 2
      have hArgsRun :
          Yul.Source.Effectful.evalArgs
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              callFuel args.reverse codeOverride source =
            .ok (exactArgs.sourceFinal, exactArgs.values.reverse) :=
        Yul.Source.Effectful.evalArgs_mono
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics_successMonotone
            contract transcript)
          (Nat.le_max_left _ _)
          exactArgs.sourceRun
      let primFuel := callFuel - 2
      have hCallFuel : primFuel + 2 = callFuel := by
        dsimp [primFuel, callFuel]
        omega
      have hTargetPrimitive' :
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript).eval
              op exactArgs.prepared.prepared.prepared.finalTarget
              exactArgs.values.reverse =
            .ok (evalTarget, values) := by
        rw [hPreTarget]
        exact hTargetPrimitive
      obtain
          ⟨sourceFinal, hSourcePrimitive, hFinalRel, hStore⟩ :=
        EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelectedBackwardAt
          primFuel
          (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
          hOp
          (StateRelation.Replay.rel_of_scopedExact
            exactArgs.prepared.relation)
          hTargetPrimitive'
      have hSourcePrimitive' :
          (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript).eval
              callFuel exactArgs.sourceFinal prim exactArgs.values =
            .ok (sourceFinal, values) := by
        simpa [hCallFuel] using hSourcePrimitive
      have hSourceRun :
          Yul.Source.Effectful.evalValues
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (callFuel + 1) (.Call (.inl prim) args)
              codeOverride source =
            .ok (sourceFinal, values) := by
        simp only [Yul.Source.Effectful.evalValues, hArgsRun]
        simpa using hSourcePrimitive'
      let prepared :=
        PreparedExpression.afterPrepared
          exactArgs.prepared.prepared.prepared
          (by
            rw [hPreTarget]
            exact hTarget)
          hFinalRel
      let scopedPrepared :
          ScopedPreparedExpression contract transcript codeRel program
            pre (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
            after layout sourceFinal target ctx values :=
        { prepared := by simpa using prepared
          relation :=
            StateRelation.Replay.scopedExact_of_rel_store
              prepared.rel (by
                rw [hStore]
                exact
                  StateRelation.Replay.sourceStoreDomain_of_scopedExact
                    exactArgs.prepared.relation) }
      exact
        ⟨⟨callFuel + 1,
          ⟨sourceFinal, hSourceRun, scopedPrepared,
            hPreTarget, rfl, exactArgs.finalCtx_eq⟩⟩⟩

theorem boundPrimitiveBackwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {fuel targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {value : Word}
    (hFuel : directFuel (.Call (.inl prim) args) ≤ fuel)
    (hOk :
      SolcValidation.ExprOk? profile sourceContract layout 1
          (.Call (.inl prim) args) =
        true)
    (hBound : EvmCompiler.Yul.Expr.List.directPureArgsSafe? args = false)
    (hLower :
      EvmCompiler.Yul.Expr.lower1Unchecked? before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hExpr :
      RecursiveAlignedValueBackwardAt profile sourceContract contract
        transcript codeRel program codeOverride layout)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hPre :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget,
            finalCtx))
    (hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower preTarget =
        .ok (evalTarget, [value])) :
    Nonempty
      (AlignedValueBackward contract transcript codeRel program codeOverride
        fuel before after layout (.Call (.inl prim) args) pre lower source
        target preTarget evalTarget ctx finalCtx value) := by
  cases fuel with
  | zero =>
      simp [directFuel] at hFuel
  | succ callFuel =>
      have hArgsFuel : directArgsFuel args ≤ callFuel := by
        unfold directFuel at hFuel
        unfold directArgsFuel
        have hMax :
            2 * args.length + maxDirectFuel args ≤
              max (2 * args.length + maxDirectFuel args) 2 :=
          Nat.le_max_left _ _
        omega
      have hPrimFuel : 2 ≤ callFuel := by
        unfold directFuel at hFuel
        have hMax :
            2 ≤ max (directArgsFuel args) 2 :=
          Nat.le_max_right _ _
        omega
      cases
          EvmCompiler.Yul.Expr.uncheckedBoundPrimitiveLowering_of_lower1Unchecked?
            hBound hLower with
      | @primitive _ _ _ op _ lowerArgs seq hOp hArgs hSeq hOutputs =>
          have hEligible :
              ∀ expr, expr ∈ args →
                SolcValidation.ExprOk? profile sourceContract layout 1 expr =
                  true := by
            intro expr hMem
            exact
              SolcValidation.exprOk_of_exprsOk_of_mem
                (SolcValidation.exprsOk_of_exprOk_primitive hOk)
                hMem
          obtain ⟨argsBackward⟩ :=
            boundArgsBackwardAt profile sourceContract contract transcript
              codeRel program codeOverride hArgsFuel hArgs hEligible hExpr
              hRel hDomain hScope hPre
          rw [FunctionsObserverExpression.exprEval_cast] at hTarget
          obtain
              ⟨targetAfterArgs, targetValues,
                hTargetArgs, hTargetPrimitive⟩ :=
            Functions.Source.Effectful.Expr.eval_prim_ok_parts
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hTarget
          have hSeq' :
              EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) =
                some seq := by
            simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
          have hStableArgs :=
            argsBackward.prepared.prepared.stackStable
              argsBackward.prepared.prepared.prepared.finalTarget
              (StateRelation.Vars.TargetExtends.refl _)
          have hStableArgs' :
              Functions.Source.Effectful.ArgList.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  lowerArgs.reverse
                  argsBackward.prepared.prepared.prepared.finalTarget =
                .ok
                  (argsBackward.prepared.prepared.prepared.finalTarget,
                    argsBackward.values.reverse) := by
            simpa using hStableArgs
          have hPreparedSeq :=
            FunctionsObserverExpression.argListEval_toSeq
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hSeq' hStableArgs'
          have hPreTarget :
              argsBackward.prepared.prepared.prepared.finalTarget =
                preTarget :=
            argsBackward.finalTarget_eq
          rw [hPreTarget] at hPreparedSeq
          rw [hPreparedSeq] at hTargetArgs
          injection hTargetArgs with hArgsResult
          injection hArgsResult with hAfterArgs hValues
          subst targetAfterArgs
          subst targetValues
          let primFuel := callFuel - 2
          have hCallFuel : primFuel + 2 = callFuel := by
            dsimp [primFuel]
            omega
          have hTargetPrimitive' :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).eval
                  op
                  argsBackward.prepared.prepared.prepared.finalTarget
                  argsBackward.values.reverse =
                .ok (evalTarget, [value]) := by
            rw [hPreTarget]
            exact hTargetPrimitive
          obtain
              ⟨sourceFinal, hSourcePrimitive, hFinalRel, hStore⟩ :=
            EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelectedBackwardAt
              primFuel
              (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
              hOp
              (StateRelation.Replay.rel_of_scopedExact
                argsBackward.prepared.relation)
              hTargetPrimitive'
          have hSourcePrimitive' :
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).eval callFuel
                  argsBackward.sourceFinal prim argsBackward.values =
                .ok (sourceFinal, [value]) := by
            simpa [hCallFuel] using hSourcePrimitive
          have hSourceValues :
              Yul.Source.Effectful.evalValues
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (callFuel + 1) (.Call (.inl prim) args)
                  codeOverride source =
                .ok (sourceFinal, [value]) := by
            simp only [Yul.Source.Effectful.evalValues,
              argsBackward.sourceRun]
            simpa using hSourcePrimitive'
          have hSource :
              Yul.Source.Effectful.eval
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  (callFuel + 1) (.Call (.inl prim) args)
                  codeOverride source =
                .ok (sourceFinal, value) := by
            simp [Yul.Source.Effectful.eval, hSourceValues]
          let prepared :=
            PreparedValue.afterPrepared
              (lower :=
                EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
              argsBackward.prepared.prepared.prepared
              (by
                rw [hPreTarget]
                rw [FunctionsObserverExpression.exprEval_cast]
                exact hTarget)
              hFinalRel
          let scopedPrepared :
              ScopedPreparedValue contract transcript codeRel program
                pre (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
                after layout sourceFinal target ctx value :=
            { prepared := by
                simpa using prepared
              relation :=
                StateRelation.Replay.scopedExact_of_rel_store
                  prepared.rel (by
                    rw [hStore]
                    exact
                      StateRelation.Replay.sourceStoreDomain_of_scopedExact
                        argsBackward.prepared.relation) }
          exact
            ⟨sourceFinal, hSourceValues, by simpa using hSource,
              scopedPrepared,
              hPreTarget, rfl, argsBackward.finalCtx_eq⟩

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

theorem directPrimitiveExpressionBackward
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {results targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {values : List Word}
    (hDirect :
      EvmCompiler.Yul.Expr.List.directPureArgsSafe? args = true)
    (hOk :
      SolcValidation.ExprOk? profile sourceContract layout results
          (.Call (.inl prim) args) =
        true)
    (hLower :
      EvmCompiler.Yul.Expr.lowerUnchecked? results before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hPre :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget,
            finalCtx))
    (hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower preTarget =
        .ok (evalTarget, values)) :
    Nonempty
      (SomeAlignedExpressionBackward contract transcript codeRel program
        codeOverride before after layout (.Call (.inl prim) args)
        pre lower source target preTarget evalTarget ctx finalCtx values) := by
  have hEligible :
      ∀ expr, expr ∈ args →
        SolcValidation.ExprOk? profile sourceContract layout 1 expr =
          true := by
    intro expr hMem
    exact
      SolcValidation.exprOk_of_exprsOk_of_mem
        (SolcValidation.exprsOk_of_exprOk_primitive hOk) hMem
  cases
      EvmCompiler.Yul.Expr.uncheckedPrimitiveLowering_of_lowerUnchecked?
        hLower with
  | @bound _ _ _ op preArgs lowerArgs seq
      hBound hOp hArgs hSeq hOutputs =>
      rw [hDirect] at hBound
      contradiction
  | @direct _ _ op lowerArgs seq
      _hDirect hOp hArgs hSeq hOutputs =>
      obtain ⟨hPreOutcome, hPreCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hPre
      injection hPreOutcome with hPreTarget
      subst preTarget
      subst finalCtx
      have hTarget' := hTarget
      rw [FunctionsObserverExpression.exprEval_cast] at hTarget'
      obtain
          ⟨targetAfterArgs, reversedValues,
            hTargetSeq, hTargetPrimitive⟩ :=
        Functions.Source.Effectful.Expr.eval_prim_ok_parts
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hTarget'
      have hSeq' :
          EvmCompiler.Yul.Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) =
            some seq := by
        simpa [EvmCompiler.Yul.Expr.List.toStackSeq?] using hSeq
      have hTargetArgs :
          Functions.Source.Effectful.ArgList.eval
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              lowerArgs.reverse target =
            .ok (targetAfterArgs, reversedValues) :=
        FunctionsObserverExpression.argListEval_of_toSeq
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (Functions.ObserverSafety.SafeSemantics.eval_outputs_length
            (contract := contract) (transcript := transcript))
          hSeq' hTargetSeq
      have hLowerReverse :
          EvmCompiler.Yul.Expr.List.toLocals1? args.reverse =
            some lowerArgs.reverse :=
        EvmCompiler.Yul.Expr.List.toLocals1?_reverse hArgs
      let callFuel := directArgsFuel args.reverse + 2
      obtain ⟨sourceAfterArgs, hSourceArgs, hArgsRel⟩ :=
        (directBackwardAt profile sourceContract contract transcript
          codeRel codeOverride callFuel).evalArgs
          (by
            dsimp [callFuel]
            omega)
          (by
            intro candidate hMem
            exact hEligible candidate (by simpa using hMem))
          hLowerReverse hRel hTargetArgs
      have hTargetPrimitive' :
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript).eval
              op targetAfterArgs
              (reversedValues.reverse.reverse) =
            .ok (evalTarget, values) := by
        simpa using hTargetPrimitive
      obtain
          ⟨sourceFinal, hSourcePrimitive, hFinalRel, hStore⟩ :=
        EvmCompiler.Yul.FunctionsObserverPrimitive.safeCompilerSelectedBackwardAt
          (directArgsFuel args.reverse)
          (contract := contract)
          (sourceValues := reversedValues.reverse)
          (Prim.toUncheckedBasicOp?_some_terminal_none hOp)
          hOp
          (StateRelation.Replay.rel_of_scopedExact hArgsRel)
          hTargetPrimitive'
      have hSourceRun :
          Yul.Source.Effectful.evalValues
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (EvmCompiler.Yul.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              (callFuel + 1) (.Call (.inl prim) args)
              codeOverride source =
            .ok (sourceFinal, values) := by
        simp only [Yul.Source.Effectful.evalValues, hSourceArgs]
        simpa [callFuel] using hSourcePrimitive
      have hFinalScoped :
          StateRelation.Replay.ScopedExactRel codeRel layout
            sourceFinal evalTarget :=
        StateRelation.Replay.scopedExact_of_rel_store hFinalRel (by
          rw [hStore]
          exact
            StateRelation.Replay.sourceStoreDomain_of_scopedExact hArgsRel)
      have hVars :
          evalTarget.source.vars = target.source.vars :=
        Functions.ObserverSafety.SafeSemantics.expr_eval_vars_eq hTarget
      let prepared :
          PreparedExpression contract transcript codeRel program []
            (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
            before sourceFinal target ctx values :=
        PreparedExpression.evaluated
          (program := program) hTarget
          (StateRelation.Replay.rel_of_scopedExact hFinalScoped)
          (hDomain.congr hVars) hScope
      let scopedPrepared :
          ScopedPreparedExpression contract transcript codeRel program []
            (EvmCompiler.Yul.Expr.cast hOutputs (.prim op seq))
            before layout sourceFinal target ctx values :=
        { prepared := prepared
          relation := hFinalScoped }
      exact
        ⟨⟨callFuel + 1,
          ⟨sourceFinal, hSourceRun, scopedPrepared, rfl, rfl, rfl⟩⟩⟩

theorem primitiveExpressionBackwardBelow
    (profile : SolcValidation.DialectProfile)
    (sourceContract : EvmYul.Yul.Ast.YulContract)
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (bound : Nat)
    {results targetFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target preTarget evalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx finalCtx : Functions.Source.Ctx}
    {values : List Word}
    (hTargetFuel : targetFuel < bound)
    (hOk :
      SolcValidation.ExprOk? profile sourceContract layout results
          (.Call (.inl prim) args) =
        true)
    (hLower :
      EvmCompiler.Yul.Expr.lowerUnchecked? results before
          (.Call (.inl prim) args) =
        some (pre, lower, after))
    (hExpr :
      RecursiveAlignedValueBackwardBelow profile sourceContract contract
        transcript codeRel program codeOverride layout bound)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin before.used target.source.vars)
    (hScope : StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hPre :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx targetFuel { stmts := pre } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular preTarget,
            finalCtx))
    (hTarget :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lower preTarget =
        .ok (evalTarget, values)) :
    Nonempty
      (SomeAlignedExpressionBackward contract transcript codeRel program
        codeOverride before after layout (.Call (.inl prim) args)
        pre lower source target preTarget evalTarget ctx finalCtx values) := by
  cases hDirect :
      EvmCompiler.Yul.Expr.List.directPureArgsSafe? args with
  | false =>
      exact
        boundPrimitiveExpressionBackwardBelow
          profile sourceContract contract transcript codeRel program
          codeOverride bound hTargetFuel hOk hLower hDirect hExpr
          hRel hDomain hScope hPre hTarget
  | true =>
      exact
        directPrimitiveExpressionBackward
          profile sourceContract contract transcript codeRel program
          codeOverride hDirect hOk hLower hRel hDomain hScope hPre hTarget

end FunctionsObserverExpressionBackward
end Yul
end EvmCompiler
