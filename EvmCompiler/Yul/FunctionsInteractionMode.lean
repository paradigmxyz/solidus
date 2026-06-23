import EvmCompiler.Yul.AllocationInteractionSafeRefinement
import EvmCompiler.Yul.FunctionsAllocationInteractionSafety
import EvmCompiler.Yul.FunctionsInteractionTerminal

/-!
Primitive-semantics mode for the adjacent Yul-to-Functions proof.

Both modes use the canonical parameterized control interpreters. The mode
selects only primitive handlers: ordinary compiler semantics, or allocation-
guarded semantics under one source memory contract. This lets one recursive
pass theorem serve both public capabilities without duplicating control or the
compiler.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionMode

noncomputable section

inductive Mode where
  | ordinary
  | guarded (contract : MemoryContract.Contract)

def sourcePrimitive : Mode →
    Yul.Source.Canonical.PrimitiveSemantics
      Yul.InteractionSemantics.Open Yul.InteractionSemantics.State
  | .ordinary => Yul.InteractionSemantics.primitiveSemantics
  | .guarded contract =>
      Yul.AllocationInteractionSafeSemantics.primitiveSemantics contract

def targetPrimitive : Mode →
    Functions.Source.Canonical.PrimitiveSemantics
      Functions.InteractionSemantics.Open
      Functions.InteractionSemantics.State
  | .ordinary => Functions.InteractionSemantics.primitiveSemantics
  | .guarded contract =>
      Functions.AllocationInteractionSafeSemantics.primitiveSemantics contract

theorem targetPrimitive_iszero (mode : Mode)
    (state : Functions.InteractionSemantics.State) (values : List Word) :
    (targetPrimitive mode).eval .iszero state values =
      Locals.InteractionSemantics.Primitive.openEval
        .iszero state values := by
  cases mode with
  | ordinary => rfl
  | guarded contract =>
      apply
        Functions.AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
      change True
      trivial

namespace Source

def evalArgs (mode : Mode) :=
  Yul.Source.Canonical.evalArgs Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def evalValues (mode : Mode) :=
  Yul.Source.Canonical.evalValues Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def eval (mode : Mode) :=
  Yul.Source.Canonical.eval Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def call (mode : Mode) :=
  Yul.Source.Canonical.call Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def execSeq (mode : Mode) :=
  Yul.Source.Canonical.execSeq Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def exec (mode : Mode) :=
  Yul.Source.Canonical.exec Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def loop (mode : Mode) :=
  Yul.Source.Canonical.loop Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

/-- One argument followed by exhausted list fuel, uniformly for both
primitive-semantics modes. -/
theorem evalArgs_one_cons (mode : Mode)
    (head : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (state : Yul.InteractionSemantics.State) :
    evalArgs mode 1 (head :: rest) code state =
      Simulation.Interaction.bind
        (evalValues mode 0 head code state) fun result =>
          Yul.InteractionSemantics.Primitive.fail result.1 .OutOfFuel := by
  unfold evalArgs evalValues Yul.Source.Canonical.evalArgs
    Yul.Source.Canonical.evalValues
  simp only [Yul.Source.Effectful.evalArgs,
    Yul.Source.Effectful.evalTail, Yul.Source.Effectful.eval]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.Source.Effectful.evalValues Yul.InteractionSemantics.stateModel
            (sourcePrimitive mode) 0 head code state)
          (fun result => pure (result.1, result.2.head!)))
        (fun result =>
          Yul.InteractionSemantics.Primitive.fail result.1 .OutOfFuel) = _
  rw [Simulation.Interaction.bind_assoc]
  rfl

/-- Positive residual list fuel exposes the head value and exact tail for both
primitive-semantics modes. -/
theorem evalArgs_succ_succ_cons (mode : Mode) (fuel : Nat)
    (head : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (state : Yul.InteractionSemantics.State) :
    evalArgs mode (fuel + 2) (head :: rest) code state =
      Simulation.Interaction.bind
        (evalValues mode (fuel + 1) head code state) fun headResult =>
          Simulation.Interaction.bind
            (evalArgs mode fuel rest code headResult.1) fun tailResult =>
              pure
                (tailResult.1, headResult.2.head! :: tailResult.2) := by
  unfold evalArgs evalValues Yul.Source.Canonical.evalArgs
    Yul.Source.Canonical.evalValues
  simp only [Yul.Source.Effectful.evalArgs,
    Yul.Source.Effectful.evalTail, Yul.Source.Effectful.eval]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.Source.Effectful.evalValues Yul.InteractionSemantics.stateModel
            (sourcePrimitive mode) (fuel + 1) head code state)
          (fun result => pure (result.1, result.2.head!)))
        (fun headResult =>
          Simulation.Interaction.bind
            (Yul.Source.Effectful.evalArgs Yul.InteractionSemantics.stateModel
              (sourcePrimitive mode) fuel rest code headResult.1)
            (fun tailResult =>
              pure (tailResult.1, headResult.2 :: tailResult.2))) = _
  rw [Simulation.Interaction.bind_assoc]
  rfl

/-- Split ordered argument evaluation at a list boundary for either primitive
mode. The suffix receives the exact residual list fuel. -/
theorem evalArgs_append (mode : Mode) {fuel : Nat}
    (left right : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (state : Yul.InteractionSemantics.State) :
    evalArgs mode fuel (left ++ right) code state =
      Simulation.Interaction.bind
        (evalArgs mode fuel left code state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (evalArgs mode (fuel - 2 * left.length)
              right code leftResult.1)
            (fun rightResult =>
              pure (rightResult.1,
                leftResult.2 ++ rightResult.2))) := by
  induction left generalizing fuel state with
  | nil =>
      cases fuel with
      | zero =>
          simp only [List.nil_append, List.length_nil, Nat.mul_zero,
            Nat.sub_zero]
          unfold evalArgs Yul.Source.Canonical.evalArgs
            Yul.Source.Effectful.evalArgs
          unfold Yul.Source.Effectful.Control.fail
          change
            Simulation.Interaction.error
                ({ exception := .OutOfFuel, state := state } :
                  Yul.InteractionSemantics.Failure) =
              Simulation.Interaction.bind
                (Simulation.Interaction.error
                  ({ exception := .OutOfFuel, state := state } :
                    Yul.InteractionSemantics.Failure)) _
          exact
            (Simulation.Interaction.monad_error_bind
              ({ exception := .OutOfFuel, state := state } :
                Yul.InteractionSemantics.Failure) _).symm
      | succ fuel =>
          simp only [List.nil_append, List.length_nil, Nat.mul_zero,
            Nat.sub_zero]
          rw [show evalArgs mode (fuel + 1) [] code state =
              pure (state, []) by
            simp [evalArgs, Yul.Source.Canonical.evalArgs,
              Yul.Source.Effectful.evalArgs]]
          change
            evalArgs mode (fuel + 1) right code state =
              Simulation.Interaction.bind
                (Simulation.Interaction.done (.ok (state, []))) _
          rw [Simulation.Interaction.bind_done_ok]
          change
            evalArgs mode (fuel + 1) right code state =
              Simulation.Interaction.bind
                (evalArgs mode (fuel + 1) right code state)
                Simulation.Interaction.pure
          exact
            (Simulation.Interaction.bind_pure
              (evalArgs mode (fuel + 1) right code state)).symm
  | cons head rest ih =>
      cases fuel with
      | zero =>
          unfold evalArgs Yul.Source.Canonical.evalArgs
            Yul.Source.Effectful.evalArgs
          unfold Yul.Source.Effectful.Control.fail
          change
            Simulation.Interaction.error
                ({ exception := .OutOfFuel, state := state } :
                  Yul.InteractionSemantics.Failure) =
              Simulation.Interaction.bind
                (Simulation.Interaction.error
                  ({ exception := .OutOfFuel, state := state } :
                    Yul.InteractionSemantics.Failure)) _
          exact
            (Simulation.Interaction.monad_error_bind
              ({ exception := .OutOfFuel, state := state } :
                Yul.InteractionSemantics.Failure) _).symm
      | succ fuel =>
          cases fuel with
          | zero =>
              rw [List.cons_append, evalArgs_one_cons, evalArgs_one_cons]
              have hZero :
                  evalValues mode 0 head code state =
                    Yul.InteractionSemantics.Primitive.fail
                      state .OutOfFuel := by
                unfold evalValues Yul.Source.Canonical.evalValues
                  Yul.Source.Effectful.evalValues
                rfl
              rw [hZero]
              unfold Yul.InteractionSemantics.Primitive.fail
              rfl
          | succ tailFuel =>
              rw [List.cons_append,
                show tailFuel + 1 + 1 = tailFuel + 2 by omega,
                evalArgs_succ_succ_cons, evalArgs_succ_succ_cons]
              rw [Simulation.Interaction.bind_assoc]
              apply congrArg
              funext headResult
              rw [ih headResult.1]
              have hResidual :
                  tailFuel + 2 - 2 * (head :: rest).length =
                    tailFuel - 2 * rest.length := by
                simp only [List.length_cons]
                omega
              rw [hResidual]
              simp only [Simulation.Interaction.bind_assoc,
                Simulation.Interaction.monad_pure_bind]
              apply congrArg
              funext restResult
              change
                Simulation.Interaction.bind
                    (evalArgs mode (tailFuel - 2 * rest.length)
                      right code restResult.1)
                    (fun rightResult =>
                      Simulation.Interaction.bind
                        (Simulation.Interaction.done
                          (.ok (rightResult.1,
                            restResult.2 ++ rightResult.2)))
                        (fun tailResult =>
                          pure (tailResult.1,
                            headResult.2.head! :: tailResult.2))) =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.done
                      (.ok (restResult.1,
                        headResult.2.head! :: restResult.2)))
                    (fun leftResult =>
                      Simulation.Interaction.bind
                        (evalArgs mode (tailFuel - 2 * rest.length)
                          right code leftResult.1)
                        (fun rightResult =>
                          pure (rightResult.1,
                            leftResult.2 ++ rightResult.2)))
              apply congrArg
              funext rightResult
              change
                Simulation.Interaction.bind
                    (Simulation.Interaction.done
                      (.ok (rightResult.1,
                        restResult.2 ++ rightResult.2)))
                    (fun tailResult =>
                      pure (tailResult.1,
                        headResult.2.head! :: tailResult.2)) =
                  pure (rightResult.1,
                    (headResult.2.head! :: restResult.2) ++ rightResult.2)
              rw [Simulation.Interaction.bind_done_ok]
              rfl

end Source

namespace Target

namespace ExprSeq

def openEval {results : Nat} (mode : Mode)
    (exprs : Locals.ExprSeq results)
    (state : Functions.InteractionSemantics.State) :=
  Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    exprs state

end ExprSeq

namespace Expr

def openEval {results : Nat} (mode : Mode)
    (expr : Functions.Expr results)
    (state : Functions.InteractionSemantics.State) :=
  Locals.Source.Effectful.Expr.Control.eval
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    expr state

def openEvalOne {results : Nat} (mode : Mode)
    (expr : Functions.Expr results)
    (state : Functions.InteractionSemantics.State) :=
  Locals.Source.Effectful.Expr.Control.evalOne
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    expr state

theorem openEvalOne_eq_bind {results : Nat} (mode : Mode)
    (expr : Functions.Expr results)
    (state : Functions.InteractionSemantics.State) :
    openEvalOne mode expr state =
      Simulation.Interaction.bind (openEval mode expr state) fun result =>
        match result.2 with
        | [value] => pure (result.1, value)
        | _ => throw .InvalidInstruction := by
  rfl

def openEvalCondition (mode : Mode) (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :=
  Locals.Source.Effectful.Expr.Control.evalCondition
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    expr state

theorem openEvalCondition_eq_map_openEvalOne (mode : Mode)
    (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :
    openEvalCondition mode expr state =
      Simulation.Interaction.map
        (fun result =>
          (result.1, result.2 != EvmYul.UInt256.ofNat 0))
        (openEvalOne mode expr state) := by
  rfl

theorem openEval_vars_eq (mode : Mode) {results : Nat}
    (expr : Functions.Expr results)
    (state : Functions.InteractionSemantics.State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval mode expr state) := by
  cases mode with
  | ordinary =>
      exact Locals.InteractionSemantics.Expr.openEval_vars_eq expr state
  | guarded contract =>
      exact
        Functions.AllocationInteractionSafeSemantics.Expr.openEval_vars_eq
          contract expr state

end Expr

namespace ArgList

def openEval (mode : Mode) (args : List (Functions.Expr 1))
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.ArgList.eval
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    args state

end ArgList

namespace Block

def openRun (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (block : Functions.Block)
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.Block.runOpen
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    program ctx fuel block state

end Block

namespace Stmt

def openRun (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (stmt : Functions.Stmt)
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.Stmt.run
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    program ctx fuel stmt state

theorem openRun_let (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (name : Functions.Name)
    (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx fuel (.let_ name expr) state =
      Simulation.Interaction.bind (Target.Expr.openEval mode expr state)
        (fun result =>
          match result.2 with
          | [value] =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (Functions.InteractionSemantics.stateModel.insert
                    result.1 name value),
                  { ctx with scope := name :: ctx.scope })
          | _ => throw .InvalidInstruction) := by
  unfold openRun Target.Expr.openEval Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  have hEvalOne :
      Locals.Source.Effectful.Expr.Control.evalOne
          Functions.InteractionSemantics.stateModel (targetPrimitive mode)
          expr state =
        Simulation.Interaction.bind
          (Locals.Source.Effectful.Expr.Control.eval
            Functions.InteractionSemantics.stateModel (targetPrimitive mode)
            expr state)
          (fun result =>
            match result.2 with
            | [value] => pure (result.1, value)
            | _ => throw .InvalidInstruction) := by
    rfl
  rw [hEvalOne]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Locals.Source.Effectful.Expr.Control.eval
            Functions.InteractionSemantics.stateModel (targetPrimitive mode)
            expr state)
          (fun result =>
            match result.2 with
            | [value] => pure (result.1, value)
            | _ => throw .InvalidInstruction))
        (fun result =>
          pure
            (Functions.Source.Effectful.Outcome.regular
              (Functions.InteractionSemantics.stateModel.insert
                result.1 name result.2),
              { ctx with scope := name :: ctx.scope })) = _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.Source.Effectful.Expr.Control.eval
        Functions.InteractionSemantics.stateModel (targetPrimitive mode)
        expr state))
  intro result _hResult
  cases result.2 with
  | nil => rfl
  | cons value rest =>
      cases rest <;> rfl

theorem openRun_assign_of_contains (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (name : Functions.Name) (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State)
    (hContains : state.vars.contains name = true) :
    openRun mode program ctx fuel (.assign name expr) state =
      Simulation.Interaction.bind (Target.Expr.openEvalOne mode expr state)
        (fun result =>
          pure
            (Functions.Source.Effectful.Outcome.regular
              (result.1.insert name result.2), ctx)) := by
  unfold openRun Target.Expr.openEvalOne
    Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run,
    Functions.InteractionSemantics.stateModel,
    Locals.InteractionSemantics.stateModel,
    Locals.Source.Effectful.Ordinary.stateModel,
    Locals.Source.Effectful.StateModel.vars, id_eq, hContains,
    ↓reduceIte, Locals.Source.Effectful.StateModel.withVars,
    Locals.Source.State.withVars,
    Locals.Source.Effectful.StateModel.insert]
  rfl

theorem openRun_if (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block)
    (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx (fuel + 1) (.if_ cond body) state =
      Simulation.Interaction.bind
        (Target.Expr.openEvalCondition mode cond state)
        (fun result =>
          if result.2 then
            openRun mode program ctx fuel (.block body) result.1
          else
            pure
              (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Target.Expr.openEvalCondition
    Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  rfl

theorem openRun_switch (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) state =
      Simulation.Interaction.bind
        (Target.Expr.openEvalOne mode scrutinee state)
        (fun result =>
          match Functions.Source.Switch.select
              result.2 cases defaultBody with
          | some body =>
              openRun mode program ctx fuel (.block body) result.1
          | none =>
              pure
                (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Target.Expr.openEvalOne
    Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.Source.Effectful.Expr.Control.evalOne
        Functions.InteractionSemantics.stateModel (targetPrimitive mode)
        scrutinee state))
  intro result _hResult
  cases Functions.Source.Switch.select result.2 cases defaultBody <;> rfl

theorem openRun_block (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (body : Functions.Block)
    (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx fuel (.block body) state =
      Simulation.Interaction.bind
        (Target.Block.openRun mode program ctx fuel body state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (Functions.InteractionSemantics.stateModel.restrictTo
                    ctx.scope result.1.state), ctx)
          | .brk | .cont | .leave | .halt _ =>
              pure (result.1, ctx)) := by
  unfold openRun Target.Block.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Canonical.Block.runOpen
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Functions.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Functions.Source.Effectful.Control.Block.runOpen
            Functions.InteractionSemantics.stateModel (targetPrimitive mode)
            program ctx fuel body state)
          (fun result =>
            match result.1.mode with
            | .regular =>
                pure
                  (Functions.Source.Effectful.Outcome.regular
                    (Functions.InteractionSemantics.stateModel.restrictTo
                      ctx.scope result.1.state))
            | .brk | .cont | .leave | .halt _ => pure result.1))
        (fun outcome => pure (outcome, ctx)) = _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.Source.Effectful.Control.Block.runOpen
        Functions.InteractionSemantics.stateModel (targetPrimitive mode)
        program ctx fuel body state))
  intro result _hResult
  cases result.1.mode <;> rfl

end Stmt

namespace Block

theorem openRun_cons (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (stmt : Functions.Stmt)
    (rest : List Functions.Stmt)
    (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx (fuel + 1) { stmts := stmt :: rest } state =
      Simulation.Interaction.bind
        (Stmt.openRun mode program ctx fuel stmt state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              openRun mode program result.2 fuel
                { stmts := rest } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) := by
  cases mode with
  | ordinary =>
      exact Functions.InteractionSemantics.Block.openRun_cons
        program ctx fuel stmt rest state
  | guarded contract =>
      exact
        Functions.AllocationInteractionSafeSemantics.Block.openRun_cons
          contract program ctx fuel stmt rest state

theorem openRun_nil (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat)
    (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx (fuel + 1) { stmts := [] } state =
      (pure (Functions.Source.Effectful.Outcome.regular state, ctx) :
        Functions.InteractionSemantics.Open
          (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)) := by
  cases mode with
  | ordinary =>
      exact Functions.InteractionSemantics.Block.openRun_nil
        program ctx fuel state
  | guarded contract =>
      exact
        Functions.AllocationInteractionSafeSemantics.Block.openRun_nil
          contract program ctx fuel state

theorem openRun_append (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (left right : List Functions.Stmt)
    (fuel : Nat) (state : Functions.InteractionSemantics.State) :
    openRun mode program ctx fuel { stmts := left ++ right } state =
      Simulation.Interaction.bind
        (openRun mode program ctx fuel { stmts := left } state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              openRun mode program result.2 (fuel - left.length)
                { stmts := right } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure result) := by
  cases mode with
  | ordinary =>
      exact Functions.InteractionSemantics.Block.openRun_append
        program left right ctx fuel state
  | guarded contract =>
      exact
        Functions.AllocationInteractionSafeSemantics.Block.openRun_append
          contract program left right ctx fuel state

end Block

namespace Program

def openRunState (mode : Mode) (fuel : Nat) (program : Functions.Program)
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.Program.runState
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    fuel program state

end Program

end Target

open FunctionsInteractionPrimitive

/-- The one primitive capability consumed by the mode-parametric recursive
Yul-to-Functions proof. -/
def CompilerSelected (mode : Mode) : Prop :=
  ∀ {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Assembly.Word},
    Prim.toUncheckedBasicOp? prim = some op →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    FunctionsInteractionRelation.StateRel source target →
    Simulation.Interaction.ForwardRel Truncated (PrimitiveDoneRel source op)
      ((sourcePrimitive mode).eval
        (fuel + 1) source prim sourceValues)
      ((targetPrimitive mode).eval op target sourceValues.reverse)

theorem compilerSelected (mode : Mode) : CompilerSelected mode := by
  cases mode with
  | ordinary =>
      exact FunctionsInteractionClosedPrimitive.compilerSelected
  | guarded contract =>
      exact FunctionsAllocationInteractionSafety.compilerSelectedSafe contract

/-- Terminal counterpart of `CompilerSelected`, shared by direct and prepared
terminal statements. -/
def TerminalSelected (mode : Mode) : Prop :=
  ∀ {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {kind : Assembly.HaltKind} {sourceValues : List Assembly.Word}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State},
    Prim.terminal? prim = some kind →
    sourceValues.length = kind.argCount →
    FunctionsInteractionRelation.StateRel source target →
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
      ((sourcePrimitive mode).eval
        (fuel + 2) source prim sourceValues)
      ((targetPrimitive mode).terminal kind target sourceValues.reverse)

theorem terminalSelected (mode : Mode) : TerminalSelected mode := by
  cases mode with
  | ordinary =>
      intro fuel prim kind values source target hTerminal hLength hRel
      exact FunctionsInteractionTerminal.of_terminal?
        fuel values hTerminal hLength hRel
  | guarded contract =>
      intro fuel prim kind values source target hTerminal hLength hRel
      change Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
        (AllocationInteractionSafeSemantics.openEval
          contract (fuel + 2) source prim values)
        (Functions.AllocationInteractionSafeSemantics.openTerminal
          contract kind target values.reverse)
      by_cases hSourceSafe :
          AllocationInteractionSafeSemantics.PrimitiveSafe
            contract prim source values
      · have hTargetSafe :=
          FunctionsAllocationInteractionSafety.Primitive.terminalSafe_to_functions
            hTerminal hSourceSafe
        rw [AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
            hSourceSafe,
          Functions.AllocationInteractionSafeSemantics.Primitive.openTerminal_eq_ordinary
            hTargetSafe]
        exact FunctionsInteractionTerminal.of_terminal?
          fuel values hTerminal hLength hRel
      · have hTargetUnsafe :
            ¬ Simulation.MemorySafety.TerminalMemorySafe
              contract kind values.reverse := by
          intro hTargetSafe
          apply hSourceSafe
          simpa [AllocationInteractionSafeSemantics.PrimitiveSafe, hTerminal]
            using hTargetSafe
        unfold AllocationInteractionSafeSemantics.openEval
          Functions.AllocationInteractionSafeSemantics.openTerminal
        simp only [hSourceSafe, hTargetUnsafe, ↓reduceIte]
        exact Simulation.Interaction.ForwardRel.done
          (.error (by simp [FunctionsInteractionPrimitive.ErrorRel]))

end
end FunctionsInteractionMode
end Yul
end EvmCompiler
