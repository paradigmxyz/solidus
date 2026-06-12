import EvmCompiler.Functions.AllocationObserverRelation

namespace EvmCompiler
namespace Functions
namespace AllocationObserverSafety

abbrev Word := Assembly.Word

/--
A dynamic source memory range is safe for allocation lowering when it does not
overlap the compiler-owned scratch reservation. Stack-only compilation has no
reserved interval and therefore permits every source range.
-/
def RegionAllowed (contract : MemoryContract.Contract)
    (address size : Nat) : Prop :=
  match contract.scratch? with
  | none => True
  | some reservation =>
      reservation.sourceAccessAllowed address size

/--
Ordinary EVM memory states do not contain materialized bytes beyond the active
memory extent. This source-facing invariant prevents target spill allocation
from exposing dormant source bytes through a later `mload`.
-/
def MemoryConsistent (machine : EvmYul.MachineState) : Prop :=
  Compiler.MemoryRelation.MemoryConsistent machine

/--
Every memory expansion performed by a primitive remains representable by the
ordinary EVM active-word counter and its `MSIZE` byte value.
-/
def PrimitiveExpansionSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mload, [address]
  | .mstore, [address, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat MemoryContract.wordBytes
  | .mstore8, [address, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat 1
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size]
  | .extcodecopy, [_, destination, _source, size] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat
  | .mcopy, [destination, source, size] =>
      Compiler.MemoryRelation.ExpansionNoWrap
        (max destination.toNat source.toNat) size.toNat
  | .keccak256, [address, size]
  | .log0, [address, size]
  | .log1, [address, size, _]
  | .log2, [address, size, _, _]
  | .log3, [address, size, _, _, _]
  | .log4, [address, size, _, _, _, _] =>
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat size.toNat
  | _, _ => True

/--
Memory writes and finite memory reads stay inside the host byte-array address
space used by the executable semantics.
-/
def PrimitiveHostSafe (op : Structured.BasicOp)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mstore, [address, _] =>
      address.toNat + MemoryContract.wordBytes < USize.size
  | .mstore8, [address, _] =>
      address.toNat + 1 < USize.size
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size]
  | .extcodecopy, [_, destination, _source, size] =>
      destination.toNat + size.toNat < USize.size
  | .mcopy, [destination, source, size] =>
      destination.toNat + size.toNat < USize.size ∧
        source.toNat + size.toNat < USize.size
  | .keccak256, [address, size]
  | .log0, [address, size]
  | .log1, [address, size, _]
  | .log2, [address, size, _, _]
  | .log3, [address, size, _, _, _]
  | .log4, [address, size, _, _, _, _] =>
      address.toNat + size.toNat < USize.size
  | _, _ => True

/--
Source-facing memory safety for one primitive application.

`values` is the argument list passed to the canonical stack-free Functions
primitive semantics. Reversing it reconstructs the concrete EVM pop order.
The predicate records every source memory range read or written by the
no-external-effects primitive surface. External call/create operations are
deliberately false here; they belong to the later request/response theorem.
-/
def PrimitiveMemorySafe (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  let stack := values.reverse
  match op, stack with
  | .mload, [address] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat MemoryContract.wordBytes ∧
        PrimitiveExpansionSafe op values
  | .mstore, [address, _value] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat MemoryContract.wordBytes ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .mstore8, [address, _value] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat 1 ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .calldatacopy, [destination, _source, size]
  | .codecopy, [destination, _source, size]
  | .returndatacopy, [destination, _source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .extcodecopy, [_account, destination, _source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .mcopy, [destination, source, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract destination.toNat size.toNat ∧
        RegionAllowed contract source.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .keccak256, [address, size] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .log0, [address, size]
  | .log1, [address, size, _topic0]
  | .log2, [address, size, _topic0, _topic1]
  | .log3, [address, size, _topic0, _topic1, _topic2]
  | .log4, [address, size, _topic0, _topic1, _topic2, _topic3] =>
      MemoryConsistent machine ∧
        RegionAllowed contract address.toNat size.toNat ∧
        PrimitiveExpansionSafe op values ∧
        PrimitiveHostSafe op values
  | .create, _
  | .call, _
  | .callcode, _
  | .delegatecall, _
  | .create2, _
  | .staticcall, _ =>
      False
  | _, _ => True

/--
Terminal source memory reads obey the same reservation contract. `RETURN` and
`REVERT` read a byte range; `STOP` and `SELFDESTRUCT` do not read memory.
-/
def TerminalMemorySafe (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind) (values : List Word) : Prop :=
  match kind, values.reverse with
  | .return, [address, size]
  | .revert, [address, size] =>
      RegionAllowed contract address.toNat size.toNat ∧
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat size.toNat ∧
        address.toNat + size.toNat < USize.size
  | .stop, []
  | .selfdestruct, [_recipient] =>
      True
  | _, _ => False

@[simp] theorem regionAllowed_unrestricted (address size : Nat) :
    RegionAllowed MemoryContract.unrestricted address size := by
  simp [RegionAllowed, MemoryContract.unrestricted]

theorem primitiveMemorySafe_unrestricted_of_noExternal
    {op : Structured.BasicOp} {machine : EvmYul.MachineState}
    {values : List Word}
    (hNoExternal : op.toPrimOp.isExternalCallCreate = false) :
    MemoryConsistent machine →
      PrimitiveExpansionSafe op values →
      PrimitiveHostSafe op values →
      PrimitiveMemorySafe MemoryContract.unrestricted op machine values := by
  intro hConsistent hExpansion hHost
  unfold PrimitiveMemorySafe
  simp only [RegionAllowed, MemoryContract.unrestricted]
  split <;>
    simp_all [MemoryConsistent, PrimitiveExpansionSafe, PrimitiveHostSafe,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.isExternalCallCreate]

@[simp] theorem primitiveMemorySafe_gas
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .gas machine [] := by
  simp [PrimitiveMemorySafe]

@[simp] theorem primitiveMemorySafe_msize
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    PrimitiveMemorySafe contract .msize machine [] := by
  simp [PrimitiveMemorySafe]

@[simp] theorem terminalMemorySafe_stop
    (contract : MemoryContract.Contract) :
    TerminalMemorySafe contract .stop [] := by
  simp [TerminalMemorySafe]

@[simp] theorem terminalMemorySafe_selfdestruct
    (contract : MemoryContract.Contract) (recipient : Word) :
    TerminalMemorySafe contract .selfdestruct [recipient] := by
  simp [TerminalMemorySafe]

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
