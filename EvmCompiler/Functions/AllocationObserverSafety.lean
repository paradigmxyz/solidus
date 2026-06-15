import EvmCompiler.Functions.AllocationObserverRelation
import EvmCompiler.Simulation.MemorySafety

namespace EvmCompiler
namespace Functions
namespace AllocationObserverSafety

abbrev Word := Assembly.Word

def RegionAllowed (contract : MemoryContract.Contract)
    (address size : Nat) : Prop :=
  Simulation.MemorySafety.RegionAllowed contract address size

def MemoryConsistent (machine : EvmYul.MachineState) : Prop :=
  Simulation.MemorySafety.MemoryConsistent machine

def PrimitiveExpansionSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  Simulation.MemorySafety.PrimitiveExpansionSafe op values

def PrimitiveHostSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  Simulation.MemorySafety.PrimitiveHostSafe op values

def PrimitiveMemorySafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  Simulation.MemorySafety.PrimitiveMemorySafe contract op machine values

def TerminalMemorySafe (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind) (values : List Word) : Prop :=
  Simulation.MemorySafety.TerminalMemorySafe contract kind values

@[simp] theorem regionAllowed_unrestricted (address size : Nat) :
    RegionAllowed MemoryContract.unrestricted address size :=
  Simulation.MemorySafety.regionAllowed_unrestricted address size

theorem primitiveMemorySafe_unrestricted_of_noExternal
    {op : Structured.BasicOp} {machine : EvmYul.MachineState}
    {values : List Word}
    (hNoExternal : op.toPrimOp.isExternalCallCreate = false) :
    MemoryConsistent machine →
      PrimitiveExpansionSafe op values →
      PrimitiveHostSafe op values →
      PrimitiveMemorySafe MemoryContract.unrestricted op machine values :=
  Simulation.MemorySafety.primitiveMemorySafe_unrestricted_of_noExternal
    hNoExternal

@[simp] theorem primitiveMemorySafe_gas
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .gas machine [] :=
  Simulation.MemorySafety.primitiveMemorySafe_gas contract machine

@[simp] theorem primitiveMemorySafe_msize
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .msize machine [] :=
  Simulation.MemorySafety.primitiveMemorySafe_msize contract machine

@[simp] theorem terminalMemorySafe_stop
    (contract : MemoryContract.Contract) :
    TerminalMemorySafe contract .stop [] :=
  Simulation.MemorySafety.terminalMemorySafe_stop contract

@[simp] theorem terminalMemorySafe_selfdestruct
    (contract : MemoryContract.Contract) (recipient : Word) :
    TerminalMemorySafe contract .selfdestruct [recipient] :=
  Simulation.MemorySafety.terminalMemorySafe_selfdestruct contract recipient

namespace SafeSemantics

/--
Source memory safety is enforced by specializing the canonical parameterized
Functions semantics at the primitive boundary. Control flow, calls, fuel, and
outcomes remain exactly those of `Functions.Source.Effectful`.
-/
noncomputable def primitiveSemantics
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace) :
    Functions.Source.Effectful.PrimitiveSemantics
      (Functions.ObserverSemantics.State transcript) := by
  classical
  exact
    { eval := fun op state values =>
        if PrimitiveMemorySafe contract op
            state.source.shared.toMachineState values then
          (Functions.ObserverSemantics.primitiveSemantics transcript).eval
            op state values
        else
          Functions.Source.invalid
      terminal := fun kind state values =>
        if TerminalMemorySafe contract kind values then
          (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
            kind state values
        else
          Functions.Source.invalid }

theorem eval_parts
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {op : Structured.BasicOp}
    {state final : Functions.ObserverSemantics.State transcript}
    {values outputs : List Word}
    (hEval :
      (primitiveSemantics contract transcript).eval op state values =
        .ok (final, outputs)) :
    PrimitiveMemorySafe contract op
        state.source.shared.toMachineState values ∧
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op state values =
        .ok (final, outputs) := by
  classical
  by_cases hSafe :
      PrimitiveMemorySafe contract op
        state.source.shared.toMachineState values
  · exact
      ⟨hSafe, by simpa [primitiveSemantics, hSafe] using hEval⟩
  · simp [primitiveSemantics, hSafe, Functions.Source.invalid,
      Structured.invalid] at hEval

theorem terminal_parts
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {kind : Assembly.HaltKind}
    {state final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      (primitiveSemantics contract transcript).terminal kind state values =
        .ok final) :
    TerminalMemorySafe contract kind values ∧
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind state values =
        .ok final := by
  classical
  by_cases hSafe : TerminalMemorySafe contract kind values
  · exact
      ⟨hSafe, by simpa [primitiveSemantics, hSafe] using hEval⟩
  · simp [primitiveSemantics, hSafe, Functions.Source.invalid,
      Structured.invalid] at hEval

theorem successRefines
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace) :
    (primitiveSemantics contract transcript).SuccessRefines
      (Functions.ObserverSemantics.primitiveSemantics transcript) := by
  constructor
  · intro op state values final outputs hEval
    exact (eval_parts hEval).2
  · intro kind state values final hEval
    exact (terminal_parts hEval).2

theorem block_runOpen_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {block : Functions.Block}
    {source : Functions.ObserverSemantics.State transcript}
    {outcome : Functions.ObserverSemantics.Outcome
      (Functions.ObserverSemantics.State transcript)}
    {finalCtx : Functions.Source.Ctx}
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          program ctx fuel block source =
        .ok (outcome, finalCtx)) :
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        program ctx fuel block source =
      .ok (outcome, finalCtx) :=
  Functions.Source.Effectful.Block.runOpen_of_successRefines
    (Functions.ObserverSemantics.stateModel transcript)
    (successRefines contract transcript) program hRun

theorem block_runScoped_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {fuel : Nat} {block : Functions.Block}
    {source : Functions.ObserverSemantics.State transcript}
    {outcome : Functions.ObserverSemantics.Outcome
      (Functions.ObserverSemantics.State transcript)}
    (hRun :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          program ctx block fuel source =
        .ok outcome) :
    Functions.Source.Effectful.Block.runScoped
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        program ctx block fuel source =
      .ok outcome :=
  Functions.Source.Effectful.Block.runScoped_of_successRefines
    (Functions.ObserverSemantics.stateModel transcript)
    (successRefines contract transcript) program hRun

theorem function_runBody_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program} {fn : Functions.FunDef}
    {args : List Word} {fuel : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {result : Functions.Source.Effectful.CallResult
      (Functions.ObserverSemantics.State transcript)}
    (hRun :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          program fn args fuel source =
        .ok result) :
    Functions.Source.Effectful.FunDef.runBody
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        program fn args fuel source =
      .ok result :=
  Functions.Source.Effectful.FunDef.runBody_of_successRefines
    (Functions.ObserverSemantics.stateModel transcript)
    (successRefines contract transcript) program hRun

theorem loop_run_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program}
    {loopCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1}
    {postBase : Functions.Source.Ctx} {post : Functions.Block}
    {bodyBase : Functions.Source.Ctx} {body : Functions.Block}
    {fuel : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {outcome : Functions.ObserverSemantics.Outcome
      (Functions.ObserverSemantics.State transcript)}
    (hRun :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          program loopCtx cond postBase post bodyBase body fuel source =
        .ok outcome) :
    Functions.Source.Effectful.Stmt.runForLoop
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        program loopCtx cond postBase post bodyBase body fuel source =
      .ok outcome :=
  Functions.Source.Effectful.Stmt.runForLoop_of_successRefines
    (Functions.ObserverSemantics.stateModel transcript)
    (successRefines contract transcript) program hRun

theorem stmt_run_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program} {ctx finalCtx : Functions.Source.Ctx}
    {fuel : Nat} {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {outcome : Functions.ObserverSemantics.Outcome
      (Functions.ObserverSemantics.State transcript)}
    (hRun :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          program ctx fuel stmt source =
        .ok (outcome, finalCtx)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        program ctx fuel stmt source =
      .ok (outcome, finalCtx) :=
  Functions.Source.Effectful.Stmt.run_of_successRefines
    (Functions.ObserverSemantics.stateModel transcript)
    (successRefines contract transcript) program hRun

theorem program_runState_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program} {fuel : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {outcome : Functions.ObserverSemantics.Outcome
      (Functions.ObserverSemantics.State transcript)}
    (hRun :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          fuel program source =
        .ok outcome) :
    Functions.Source.Effectful.Program.runState
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        fuel program source =
      .ok outcome :=
  block_runScoped_eq hRun

end SafeSemantics

mutual
  /--
  A successful canonical Functions expression evaluation whose every dynamic
  primitive memory access obeys the source-owned reservation contract.

  This is proof evidence over the existing effectful evaluator, not a second
  evaluator: each primitive constructor stores the actual canonical primitive
  result equation used by `Functions.Source.Effectful.Expr.eval`.
  -/
  inductive Expr.MemorySafeEval
      (contract : MemoryContract.Contract) (transcript : Assembly.ResourceTrace) :
      {results : Nat} →
        Functions.Expr results →
        Functions.ObserverSemantics.State transcript →
        Functions.ObserverSemantics.State transcript →
        List Word → Prop where
    | lit {value : Word}
        {state : Functions.ObserverSemantics.State transcript} :
        Expr.MemorySafeEval contract transcript (.lit value)
          state state [value]
    | var {name : Functions.Name} {value : Word}
        {state : Functions.ObserverSemantics.State transcript}
        (hValue : state.source.vars name = some value) :
        Expr.MemorySafeEval contract transcript (.var name)
          state state [value]
    | prim {op : Structured.BasicOp}
        {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
        {source afterArgs final :
          Functions.ObserverSemantics.State transcript}
        {values outputs : List Word}
        (hArgs :
          ExprSeq.MemorySafeEval contract transcript args
            source afterArgs values)
        (hMemory :
          PrimitiveMemorySafe contract op
            afterArgs.source.shared.toMachineState values)
        (hPrim :
          (Functions.ObserverSemantics.primitiveSemantics transcript).eval
              op afterArgs values =
            .ok (final, outputs)) :
        Expr.MemorySafeEval contract transcript (.prim op args)
          source final outputs

  /--
  Left-to-right safe evaluation for the canonical expression-sequence
  semantics. The resulting value list is exactly the concatenation returned by
  the existing evaluator.
  -/
  inductive ExprSeq.MemorySafeEval
      (contract : MemoryContract.Contract) (transcript : Assembly.ResourceTrace) :
      {results : Nat} →
        Locals.ExprSeq results →
        Functions.ObserverSemantics.State transcript →
        Functions.ObserverSemantics.State transcript →
        List Word → Prop where
    | nil {state : Functions.ObserverSemantics.State transcript} :
        ExprSeq.MemorySafeEval contract transcript .nil state state []
    | cons {left right : Nat}
        {head : Functions.Expr left} {tail : Locals.ExprSeq right}
        {source afterHead final :
          Functions.ObserverSemantics.State transcript}
        {headValues tailValues : List Word}
        (hHead :
          Expr.MemorySafeEval contract transcript head
            source afterHead headValues)
        (hTail :
          ExprSeq.MemorySafeEval contract transcript tail
            afterHead final tailValues) :
        ExprSeq.MemorySafeEval contract transcript (.cons head tail)
          source final (headValues ++ tailValues)
end

/--
Left-to-right source-facing safety for function-call arguments.

This relation follows the canonical `Functions.Source.Effectful.ArgList.eval`
recursion. It contains only source evaluation evidence; allocation lowering
and target execution remain owned by the adjacent compiler proof.
-/
inductive ArgList.MemorySafeEval
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace) :
    List (Functions.Expr 1) →
      Functions.ObserverSemantics.State transcript →
      Functions.ObserverSemantics.State transcript →
      List Word → Prop where
  | nil {state : Functions.ObserverSemantics.State transcript} :
      ArgList.MemorySafeEval contract transcript [] state state []
  | cons {arg : Functions.Expr 1} {rest : List (Functions.Expr 1)}
      {source afterArg final :
        Functions.ObserverSemantics.State transcript}
      {value : Word} {values : List Word}
      (hArg :
        Expr.MemorySafeEval contract transcript arg
          source afterArg [value])
      (hRest :
        ArgList.MemorySafeEval contract transcript rest
          afterArg final values) :
      ArgList.MemorySafeEval contract transcript (arg :: rest)
        source final (value :: values)

mutual
  theorem Expr.MemorySafeEval.of_safe_eval
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {expr : Functions.Expr results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        Functions.Source.Effectful.Expr.eval
            (Functions.ObserverSemantics.stateModel transcript)
            (SafeSemantics.primitiveSemantics contract transcript)
            expr source =
          .ok (final, values)) :
      Expr.MemorySafeEval contract transcript expr source final values := by
    cases expr with
    | lit value =>
        have hEq : (source, [value]) = (final, values) := by
          simpa [Functions.Source.Effectful.Expr.eval,
            Locals.Source.Effectful.Expr.eval] using hEval
        cases hEq
        exact .lit
    | var name =>
        cases hValue : source.source.vars name with
        | none =>
            simp [Functions.Source.Effectful.Expr.eval,
              Locals.Source.Effectful.Expr.eval,
              Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.vars, hValue,
              Functions.Source.invalid, Structured.invalid] at hEval
        | some value =>
            have hEq : (source, [value]) = (final, values) := by
              simpa [Functions.Source.Effectful.Expr.eval,
                Locals.Source.Effectful.Expr.eval,
                Functions.ObserverSemantics.stateModel,
                Locals.ObserverSemantics.stateModel,
                Locals.Source.Effectful.StateModel.vars, hValue] using hEval
            cases hEq
            exact .var hValue
    | code code =>
        simp [Functions.Source.Effectful.Expr.eval,
          Locals.Source.Effectful.Expr.eval,
          Functions.Source.invalid, Structured.invalid] at hEval
    | prim op args =>
        simp only [Functions.Source.Effectful.Expr.eval,
          Locals.Source.Effectful.Expr.eval] at hEval
        cases hArgs :
            Locals.Source.Effectful.Expr.ExprSeq.eval
              (Functions.ObserverSemantics.stateModel transcript)
              (SafeSemantics.primitiveSemantics contract transcript)
              args source with
        | error err =>
            simp [hArgs] at hEval
        | ok result =>
            rcases result with ⟨afterArgs, argValues⟩
            simp only [hArgs, Bind.bind, Except.bind] at hEval
            have hArgsSafe :=
              ExprSeq.MemorySafeEval.of_safe_eval hArgs
            obtain ⟨hMemory, hPrim⟩ :=
              SafeSemantics.eval_parts hEval
            exact .prim hArgsSafe hMemory hPrim

  theorem ExprSeq.MemorySafeEval.of_safe_eval
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {exprs : Locals.ExprSeq results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        Locals.Source.Effectful.Expr.ExprSeq.eval
            (Functions.ObserverSemantics.stateModel transcript)
            (SafeSemantics.primitiveSemantics contract transcript)
            exprs source =
          .ok (final, values)) :
      ExprSeq.MemorySafeEval contract transcript exprs source final values := by
    cases exprs with
    | nil =>
        have hEq : (source, []) = (final, values) := by
          simpa [Locals.Source.Effectful.Expr.ExprSeq.eval] using hEval
        cases hEq
        exact .nil
    | @cons left right head tail =>
        simp only [Locals.Source.Effectful.Expr.ExprSeq.eval] at hEval
        cases hHead :
            Locals.Source.Effectful.Expr.eval
              (Functions.ObserverSemantics.stateModel transcript)
              (SafeSemantics.primitiveSemantics contract transcript)
              head source with
        | error err =>
            simp [hHead] at hEval
        | ok headResult =>
            rcases headResult with ⟨afterHead, headValues⟩
            simp only [hHead, Bind.bind, Except.bind] at hEval
            cases hTail :
                Locals.Source.Effectful.Expr.ExprSeq.eval
                  (Functions.ObserverSemantics.stateModel transcript)
                  (SafeSemantics.primitiveSemantics contract transcript)
                  tail afterHead with
            | error err =>
                simp [hTail] at hEval
            | ok tailResult =>
                rcases tailResult with ⟨tailFinal, tailValues⟩
                simp only [hTail, Bind.bind, Except.bind] at hEval
                have hEq :
                    (tailFinal, headValues ++ tailValues) =
                      (final, values) := by
                  exact Except.ok.inj hEval
                cases hEq
                exact .cons
                  (Expr.MemorySafeEval.of_safe_eval hHead)
                  (ExprSeq.MemorySafeEval.of_safe_eval hTail)
end

theorem Expr.MemorySafeEval.of_safe_evalOne
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {results : Nat} {expr : Functions.Expr results}
    {source final : Functions.ObserverSemantics.State transcript}
    {value : Word}
    (hEval :
      Functions.Source.Effectful.Expr.evalOne
          (Functions.ObserverSemantics.stateModel transcript)
          (SafeSemantics.primitiveSemantics contract transcript)
          expr source =
        .ok (final, value)) :
    Expr.MemorySafeEval contract transcript expr source final [value] := by
  unfold Functions.Source.Effectful.Expr.evalOne at hEval
  unfold Locals.Source.Effectful.Expr.evalOne at hEval
  cases hExpr :
      Locals.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (SafeSemantics.primitiveSemantics contract transcript)
        expr source with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨exprFinal, values⟩
      simp only [hExpr, Bind.bind, Except.bind] at hEval
      cases values with
      | nil =>
          simp [Functions.Source.invalid, Structured.invalid] at hEval
      | cons head tail =>
          cases tail with
          | nil =>
              have hEq : (exprFinal, head) = (final, value) := by
                exact Except.ok.inj hEval
              cases hEq
              exact Expr.MemorySafeEval.of_safe_eval hExpr
          | cons next rest =>
              simp [Functions.Source.invalid, Structured.invalid] at hEval

theorem Expr.MemorySafeEval.of_safe_evalCondition
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {expr : Functions.Expr 1}
    {source final : Functions.ObserverSemantics.State transcript}
    {conditionTrue : Bool}
    (hEval :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (SafeSemantics.primitiveSemantics contract transcript)
          expr source =
        .ok (final, conditionTrue)) :
    ∃ value,
      Expr.MemorySafeEval contract transcript expr source final [value] ∧
        (value != EvmYul.UInt256.ofNat 0) = conditionTrue := by
  unfold Functions.Source.Effectful.Expr.evalCondition at hEval
  unfold Locals.Source.Effectful.Expr.evalCondition at hEval
  cases hOne :
      Locals.Source.Effectful.Expr.evalOne
        (Functions.ObserverSemantics.stateModel transcript)
        (SafeSemantics.primitiveSemantics contract transcript)
        expr source with
  | error err =>
      simp [hOne] at hEval
  | ok result =>
      rcases result with ⟨after, value⟩
      simp only [hOne, Bind.bind, Except.bind] at hEval
      have hEq :
          (after, value != EvmYul.UInt256.ofNat 0) =
            (final, conditionTrue) :=
        Except.ok.inj hEval
      cases hEq
      exact
        ⟨value, Expr.MemorySafeEval.of_safe_evalOne hOne, rfl⟩

theorem ArgList.MemorySafeEval.of_safe_eval
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {args : List (Functions.Expr 1)}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (SafeSemantics.primitiveSemantics contract transcript)
          args source =
        .ok (final, values)) :
    ArgList.MemorySafeEval contract transcript args source final values := by
  induction args generalizing source final values with
  | nil =>
      have hEq : (source, []) = (final, values) := by
        simpa [Functions.Source.Effectful.ArgList.eval] using hEval
      cases hEq
      exact .nil
  | cons arg rest ih =>
      unfold Functions.Source.Effectful.ArgList.eval at hEval
      cases hArg :
          Functions.Source.Effectful.Expr.evalOne
            (Functions.ObserverSemantics.stateModel transcript)
            (SafeSemantics.primitiveSemantics contract transcript)
            arg source with
      | error err =>
          simp [hArg] at hEval
      | ok argResult =>
          rcases argResult with ⟨afterArg, value⟩
          simp only [hArg, Bind.bind, Except.bind] at hEval
          cases hRest :
              Functions.Source.Effectful.ArgList.eval
                (Functions.ObserverSemantics.stateModel transcript)
                (SafeSemantics.primitiveSemantics contract transcript)
                rest afterArg with
          | error err =>
              simp [hRest] at hEval
          | ok restResult =>
              rcases restResult with ⟨restFinal, restValues⟩
              simp only [hRest, Bind.bind, Except.bind] at hEval
              have hEq :
                  (restFinal, value :: restValues) =
                    (final, values) := by
                exact Except.ok.inj hEval
              cases hEq
              exact .cons
                (Expr.MemorySafeEval.of_safe_evalOne hArg)
                (ih hRest)

mutual
  theorem Expr.MemorySafeEval.eval_eq
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {expr : Functions.Expr results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        Expr.MemorySafeEval contract transcript expr source final values) :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          expr source =
        .ok (final, values) := by
    cases hEval with
    | lit =>
        rfl
    | var hValue =>
        simp [Functions.Source.Effectful.Expr.eval,
          Locals.Source.Effectful.Expr.eval,
          Functions.ObserverSemantics.stateModel,
          Locals.ObserverSemantics.stateModel,
          Locals.Source.Effectful.StateModel.vars, hValue]
    | prim hArgs _hMemory hPrim =>
        simp only [Functions.Source.Effectful.Expr.eval,
          Locals.Source.Effectful.Expr.eval]
        rw [hArgs.eval_eq]
        simp [hPrim]

  theorem ExprSeq.MemorySafeEval.eval_eq
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {exprs : Locals.ExprSeq results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        ExprSeq.MemorySafeEval contract transcript exprs source final values) :
      Locals.Source.Effectful.Expr.ExprSeq.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          exprs source =
        .ok (final, values) := by
    cases hEval with
    | nil =>
        rfl
    | cons hHead hTail =>
        simp only [Locals.Source.Effectful.Expr.ExprSeq.eval]
        have hHeadEval := hHead.eval_eq
        change
          Locals.Source.Effectful.Expr.eval
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              _ _ =
            _ at hHeadEval
        rw [hHeadEval]
        simp only [Bind.bind, Except.bind]
        rw [hTail.eval_eq]
end

theorem ArgList.MemorySafeEval.values_length
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {args : List (Functions.Expr 1)}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      ArgList.MemorySafeEval contract transcript args
        source final values) :
    values.length = args.length := by
  induction hEval with
  | nil =>
      rfl
  | cons _hArg _hRest ih =>
      simp [ih]

mutual
  /--
  A safely evaluated expression accepted by the no-variable prelude compiler
  is a genuine source expression scoped by the empty environment.

  The helper accepts embedded code syntactically, but the canonical source
  evaluator has no successful embedded-code case. This theorem records that
  distinction once in the safety owner.
  -/
  theorem Expr.MemorySafeEval.scoped_of_compileNoVar
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {expr : Functions.Expr results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word} {code : Structured.Code}
      (hEval :
        Expr.MemorySafeEval contract transcript expr source final values)
      (hCompile :
        AllocationSupport.compileNoVarExprCode? expr = some code) :
      Functions.Scope.ExprScoped [] expr := by
    cases hEval with
    | lit =>
        trivial
    | var hValue =>
        simp [AllocationSupport.compileNoVarExprCode?] at hCompile
    | @prim op args source afterArgs final values outputs
        hArgs hMemory hPrim =>
        cases hArgsCode :
            AllocationSupport.compileNoVarExprSeqCode? args with
        | none =>
            simp [AllocationSupport.compileNoVarExprCode?, hArgsCode]
              at hCompile
        | some argsCode =>
            exact
              ExprSeq.MemorySafeEval.scoped_of_compileNoVar hArgs hArgsCode

  theorem ExprSeq.MemorySafeEval.scoped_of_compileNoVar
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {exprs : Locals.ExprSeq results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word} {code : Structured.Code}
      (hEval :
        ExprSeq.MemorySafeEval contract transcript exprs source final values)
      (hCompile :
        AllocationSupport.compileNoVarExprSeqCode? exprs = some code) :
      Functions.Scope.ExprSeqScoped [] exprs := by
    cases hEval with
    | nil =>
        trivial
    | @cons left right head tail source afterHead final
        headValues tailValues hHead hTail =>
        cases hHeadCode :
            AllocationSupport.compileNoVarExprCode? head with
        | none =>
            simp [AllocationSupport.compileNoVarExprSeqCode?, hHeadCode]
              at hCompile
        | some headCode =>
            cases hTailCode :
                AllocationSupport.compileNoVarExprSeqCode? tail with
            | none =>
                simp [AllocationSupport.compileNoVarExprSeqCode?,
                  hHeadCode, hTailCode] at hCompile
            | some tailCode =>
                exact
                  ⟨Expr.MemorySafeEval.scoped_of_compileNoVar
                      hHead hHeadCode,
                    ExprSeq.MemorySafeEval.scoped_of_compileNoVar
                      hTail hTailCode⟩
end

mutual
  theorem Expr.MemorySafeEval.vars_eq
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {expr : Functions.Expr results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        Expr.MemorySafeEval contract transcript expr source final values) :
      final.source.vars = source.source.vars := by
    cases hEval with
    | lit =>
        rfl
    | var _hValue =>
        rfl
    | prim hArgs _hMemory hPrim =>
        exact
          (Locals.ObserverSemantics.primitiveSemantics_eval_vars_eq
            hPrim).trans hArgs.vars_eq

  theorem ExprSeq.MemorySafeEval.vars_eq
      {contract : MemoryContract.Contract}
      {transcript : Assembly.ResourceTrace}
      {results : Nat} {exprs : Locals.ExprSeq results}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        ExprSeq.MemorySafeEval contract transcript exprs
          source final values) :
      final.source.vars = source.source.vars := by
    cases hEval with
    | nil =>
        rfl
    | cons hHead hTail =>
        exact hTail.vars_eq.trans hHead.vars_eq
end

theorem ArgList.MemorySafeEval.vars_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {args : List (Functions.Expr 1)}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      ArgList.MemorySafeEval contract transcript args
        source final values) :
    final.source.vars = source.source.vars := by
  induction hEval with
  | nil =>
      rfl
  | cons hArg _hRest ih =>
      exact ih.trans hArg.vars_eq

theorem Expr.MemorySafeEval.evalOne_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {results : Nat} {expr : Functions.Expr results}
    {source final : Functions.ObserverSemantics.State transcript}
    {value : Word}
    (hEval :
      Expr.MemorySafeEval contract transcript expr source final [value]) :
    Functions.Source.Effectful.Expr.evalOne
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        expr source =
      .ok (final, value) := by
  unfold Functions.Source.Effectful.Expr.evalOne
  unfold Locals.Source.Effectful.Expr.evalOne
  have hEvalEq := hEval.eval_eq
  change
    Locals.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        expr source =
      .ok (final, [value]) at hEvalEq
  rw [hEvalEq]
  rfl

theorem Expr.MemorySafeEval.evalCondition_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {expr : Functions.Expr 1}
    {source final : Functions.ObserverSemantics.State transcript}
    {value : Word}
    (hEval :
      Expr.MemorySafeEval contract transcript expr source final [value]) :
    Functions.Source.Effectful.Expr.evalCondition
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        expr source =
      .ok (final, value != EvmYul.UInt256.ofNat 0) := by
  unfold Functions.Source.Effectful.Expr.evalCondition
  unfold Locals.Source.Effectful.Expr.evalCondition
  have hEvalOne := hEval.evalOne_eq
  change
    Locals.Source.Effectful.Expr.evalOne
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        expr source =
      .ok (final, value) at hEvalOne
  rw [hEvalOne]
  rfl

theorem ArgList.MemorySafeEval.eval_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {args : List (Functions.Expr 1)}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      ArgList.MemorySafeEval contract transcript args
        source final values) :
    Functions.Source.Effectful.ArgList.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        args source =
      .ok (final, values) := by
  induction hEval with
  | nil =>
      rfl
  | cons hArg _hRest ih =>
      unfold Functions.Source.Effectful.ArgList.eval
      rw [hArg.evalOne_eq]
      simp only [Bind.bind, Except.bind]
      rw [ih]

namespace Stmt

/--
Dynamic safety evidence for the nonrecursive statement families.

Each constructor stores the canonical Functions expression or terminal
equation used by `Functions.Source.Effectful.Stmt.run`. This classifies source
runs without defining a second statement interpreter. Recursive blocks,
control flow, and calls compose this leaf family in the statement preservation
module.
-/
inductive LeafMemorySafeRun
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace)
    (program : Functions.Program)
    (ctx : Functions.Source.Ctx)
    (fuel : Nat) :
    Functions.Stmt →
      Functions.ObserverSemantics.State transcript →
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript) →
      Functions.Source.Ctx → Prop where
  | expr {expr : Functions.Expr 0}
      {source final : Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hEval :
        Expr.MemorySafeEval contract transcript expr source final values) :
      LeafMemorySafeRun contract transcript program ctx fuel
        (.expr expr) source
        (Functions.Source.Effectful.Outcome.regular final) ctx
  | let_ {name : Functions.Name} {valueExpr : Functions.Expr 1}
      {source final : Functions.ObserverSemantics.State transcript}
      {value : Word}
      (hEval :
        Expr.MemorySafeEval contract transcript valueExpr
          source final [value]) :
      LeafMemorySafeRun contract transcript program ctx fuel
        (.let_ name valueExpr) source
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).insert
            final name value))
        { ctx with scope := name :: ctx.scope }
  | assign {name : Functions.Name} {valueExpr : Functions.Expr 1}
      {source final : Functions.ObserverSemantics.State transcript}
      {value : Word}
      (hContains :
        Locals.Source.Store.contains
            ((Functions.ObserverSemantics.stateModel transcript).vars source)
            name =
          true)
      (hEval :
        Expr.MemorySafeEval contract transcript valueExpr
          source final [value]) :
      LeafMemorySafeRun contract transcript program ctx fuel
        (.assign name valueExpr) source
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).withVars
            final
            (Locals.Source.Store.insert
              ((Functions.ObserverSemantics.stateModel transcript).vars final)
              name value)))
        ctx
  | brk {source : Functions.ObserverSemantics.State transcript}
      {scope : List Functions.Name}
      (hScope : ctx.breakScope? = some scope) :
      LeafMemorySafeRun contract transcript program ctx fuel
        .brk source
        (Functions.Source.Effectful.Outcome.brk
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            scope source))
        ctx
  | cont {source : Functions.ObserverSemantics.State transcript}
      {scope : List Functions.Name}
      (hScope : ctx.continueScope? = some scope) :
      LeafMemorySafeRun contract transcript program ctx fuel
        .cont source
        (Functions.Source.Effectful.Outcome.cont
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            scope source))
        ctx
  | leave {source : Functions.ObserverSemantics.State transcript}
      {scope : List Functions.Name}
      (hScope : ctx.leaveScope? = some scope) :
      LeafMemorySafeRun contract transcript program ctx fuel
        .leave source
        (Functions.Source.Effectful.Outcome.leave
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            scope source))
        ctx
  | terminal {kind : Assembly.HaltKind}
      {source final : Functions.ObserverSemantics.State transcript}
      (hMemory : TerminalMemorySafe contract kind [])
      (hTerminal :
        (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
            kind source [] =
          .ok final) :
      LeafMemorySafeRun contract transcript program ctx fuel
        (.terminal kind) source
        (Functions.Source.Effectful.Outcome.halt kind final) ctx
  | terminalArgs {kind : Assembly.HaltKind}
      {args : Locals.ExprSeq kind.argCount}
      {source afterArgs final :
        Functions.ObserverSemantics.State transcript}
      {values : List Word}
      (hArgs :
        ExprSeq.MemorySafeEval contract transcript args
          source afterArgs values)
      (hMemory : TerminalMemorySafe contract kind values)
      (hTerminal :
        (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
            kind afterArgs values =
          .ok final) :
      LeafMemorySafeRun contract transcript program ctx fuel
        (.terminalArgs kind args) source
        (Functions.Source.Effectful.Outcome.halt kind final) ctx

theorem LeafMemorySafeRun.run_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {program : Functions.Program}
    {ctx : Functions.Source.Ctx}
    {fuel : Nat}
    {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {outcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {finalCtx : Functions.Source.Ctx}
    (hRun :
      LeafMemorySafeRun contract transcript program ctx fuel
        stmt source outcome finalCtx) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        program ctx fuel stmt source =
      .ok (outcome, finalCtx) := by
  cases hRun with
  | expr hEval =>
      simp only [Functions.Source.Effectful.Stmt.run]
      rw [hEval.eval_eq]
      rfl
  | let_ hEval =>
      simp only [Functions.Source.Effectful.Stmt.run]
      rw [hEval.evalOne_eq]
      rfl
  | assign hContains hEval =>
      simp only [Functions.Source.Effectful.Stmt.run]
      rw [hContains]
      simp only [if_true]
      rw [hEval.evalOne_eq]
      rfl
  | brk hScope =>
      simp [Functions.Source.Effectful.Stmt.run, hScope]
  | cont hScope =>
      simp [Functions.Source.Effectful.Stmt.run, hScope]
  | leave hScope =>
      simp [Functions.Source.Effectful.Stmt.run, hScope]
  | terminal _hMemory hTerminal =>
      simp only [Functions.Source.Effectful.Stmt.run]
      rw [hTerminal]
      rfl
  | terminalArgs hArgs _hMemory hTerminal =>
      simp only [Functions.Source.Effectful.Stmt.run]
      rw [hArgs.eval_eq]
      simp only [Bind.bind, Except.bind]
      rw [hTerminal]

end Stmt

end AllocationObserverSafety
end Functions
end EvmCompiler
