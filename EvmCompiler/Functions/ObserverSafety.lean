import EvmCompiler.Functions.ObserverSemantics
import EvmCompiler.Locals.PrimitivePreservation
import EvmCompiler.Simulation.MemorySafety

namespace EvmCompiler
namespace Functions
namespace ObserverSafety

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

@[simp] def PrimitivePermitted
    (op : Structured.BasicOp)
    (shared : EvmYul.SharedState .EVM) : Prop :=
  match op with
  | .sstore | .tstore
  | .log0 | .log1 | .log2 | .log3 | .log4 =>
      shared.executionEnv.perm = true
  | _ => True

theorem primitivePermitted_of_observer
    {op : Structured.BasicOp} {kind : Assembly.ResourceObserver}
    {shared : EvmYul.SharedState .EVM}
    (hObserver :
      Functions.ObserverSemantics.basicOpObserver? op = some kind) :
    PrimitivePermitted op shared := by
  cases op <;>
    simp [Functions.ObserverSemantics.basicOpObserver?,
      Locals.ObserverSemantics.basicOpObserver?,
      Assembly.ResourceObserver.ofPrimOp?,
      Structured.BasicOp.toPrimOp, PrimitivePermitted] at hObserver ⊢

def TerminalMemorySafe (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind) (values : List Word) : Prop :=
  Simulation.MemorySafety.TerminalMemorySafe contract kind values

def TerminalPermitted
    {transcript : Assembly.ResourceTrace}
    (kind : Assembly.HaltKind)
    (state : Functions.ObserverSemantics.State transcript) : Prop :=
  kind = .selfdestruct →
    state.source.shared.executionEnv.perm = true

def TerminalSafe
    {transcript : Assembly.ResourceTrace}
    (contract : MemoryContract.Contract)
    (kind : Assembly.HaltKind)
    (state : Functions.ObserverSemantics.State transcript)
    (values : List Word) : Prop :=
  TerminalMemorySafe contract kind values ∧
    TerminalPermitted kind state

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
              state.source.shared.toMachineState values ∧
            PrimitivePermitted op state.source.shared then
          (Functions.ObserverSemantics.primitiveSemantics transcript).eval
            op state values
        else
          Functions.Source.invalid
      terminal := fun kind state values =>
        if TerminalSafe contract kind state values then
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
      PrimitivePermitted op state.source.shared ∧
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op state values =
        .ok (final, outputs) := by
  classical
  by_cases hSafe :
      PrimitiveMemorySafe contract op
          state.source.shared.toMachineState values ∧
        PrimitivePermitted op state.source.shared
  · exact
      ⟨hSafe.1, hSafe.2,
        by
          simpa only [primitiveSemantics, if_pos hSafe] using hEval⟩
  · simp only [primitiveSemantics, if_neg hSafe,
      Functions.Source.invalid, Structured.invalid] at hEval
    cases hEval

theorem eval_outputs_length
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {op : Structured.BasicOp}
    {state final : Functions.ObserverSemantics.State transcript}
    {values outputs : List Word}
    (hEval :
      (primitiveSemantics contract transcript).eval op state values =
        .ok (final, outputs)) :
    outputs.length = Expressions.Structured.BasicOp.outputs op := by
  obtain ⟨_hSafe, _hPermitted, hRun⟩ := eval_parts hEval
  unfold Functions.ObserverSemantics.primitiveSemantics at hRun
  unfold Locals.ObserverSemantics.primitiveSemantics at hRun
  cases hObserver : Locals.ObserverSemantics.basicOpObserver? op with
  | none =>
      cases hPrimitive :
          Locals.Source.PrimitiveSemantics.structured.eval op
            state.source.shared values with
      | error err =>
          simp [hObserver, hPrimitive] at hRun
      | ok result =>
          rcases result with ⟨shared, results⟩
          simp [hObserver, hPrimitive] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact
            Locals.Source.PrimitiveSemantics.structured_eval_length
              hPrimitive
  | some kind =>
      cases values with
      | nil =>
          cases hConsume :
              Simulation.ResourceReplay.consume? kind state with
          | none =>
              simp [hObserver, hConsume, Structured.invalid] at hRun
          | some result =>
              rcases result with ⟨value, consumed⟩
              simp [hObserver, hConsume] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              cases op <;>
                simp [Locals.ObserverSemantics.basicOpObserver?,
                  Assembly.ResourceObserver.ofPrimOp?,
                  Structured.BasicOp.toPrimOp,
                  Expressions.Structured.BasicOp.outputs] at hObserver ⊢
      | cons head tail =>
          simp [hObserver, Structured.invalid] at hRun

theorem eval_observer_values_eq_nil
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver}
    {state final : Functions.ObserverSemantics.State transcript}
    {values outputs : List Word}
    (hObserver :
      Functions.ObserverSemantics.basicOpObserver? op = some kind)
    (hEval :
      (primitiveSemantics contract transcript).eval op state values =
        .ok (final, outputs)) :
    values = [] :=
  Functions.ObserverSemantics.primitiveSemantics_eval_observer_values_eq_nil
    hObserver (eval_parts hEval).2.2

theorem eval_of_safe
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {op : Structured.BasicOp}
    {state final : Functions.ObserverSemantics.State transcript}
    {values outputs : List Word}
    (hSafe :
      PrimitiveMemorySafe contract op
        state.source.shared.toMachineState values)
    (hPermitted :
      PrimitivePermitted op state.source.shared)
    (hEval :
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op state values =
        .ok (final, outputs)) :
    (primitiveSemantics contract transcript).eval op state values =
      .ok (final, outputs) := by
  have hGuard :
      PrimitiveMemorySafe contract op
          state.source.shared.toMachineState values ∧
        PrimitivePermitted op state.source.shared :=
    ⟨hSafe, hPermitted⟩
  simpa only [primitiveSemantics, if_pos hGuard] using hEval

theorem eval_iszero
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    (state : Functions.ObserverSemantics.State transcript)
    (value : Word) :
    (primitiveSemantics contract transcript).eval
        .iszero state [value] =
      .ok (state, [EvmYul.UInt256.isZero value]) := by
  classical
  apply eval_of_safe (by trivial) (by trivial)
  simp [Functions.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Assembly.ResourceObserver.ofPrimOp?,
    Structured.BasicOp.toPrimOp,
    Locals.Source.PrimitiveSemantics.structured,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Assembly.PrimOp.continuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Assembly.PrimStep.run, EvmYul.EVM.execUnOp,
    EvmYul.Stack.pop, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
    Locals.Source.State.withShared]
  rfl

theorem evalCondition_one
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    (state : Functions.ObserverSemantics.State transcript) :
    Functions.Source.Effectful.Expr.evalCondition
        (Functions.ObserverSemantics.stateModel transcript)
        (primitiveSemantics contract transcript)
        (.lit (EvmYul.UInt256.ofNat 1)) state =
      .ok (state, true) := by
  apply
    Functions.Source.Effectful.Expr.evalCondition_true_of_eval_singleton
      (value := EvmYul.UInt256.ofNat 1)
      (Functions.ObserverSemantics.stateModel transcript)
      (primitiveSemantics contract transcript)
  · rfl
  · decide

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
  by_cases hSafe : TerminalSafe contract kind state values
  · exact
      ⟨hSafe.1, by simpa [primitiveSemantics, hSafe] using hEval⟩
  · simp [primitiveSemantics, hSafe, Functions.Source.invalid,
      Structured.invalid] at hEval

theorem terminal_permitted_parts
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {kind : Assembly.HaltKind}
    {state final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      (primitiveSemantics contract transcript).terminal kind state values =
        .ok final) :
    TerminalPermitted kind state := by
  classical
  by_cases hSafe : TerminalSafe contract kind state values
  · exact hSafe.2
  · simp [primitiveSemantics, hSafe, Functions.Source.invalid,
      Structured.invalid] at hEval

theorem terminal_of_safe
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {kind : Assembly.HaltKind}
    {state final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe : TerminalSafe contract kind state values)
    (hEval :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind state values =
        .ok final) :
    (primitiveSemantics contract transcript).terminal kind state values =
      .ok final := by
  simpa [primitiveSemantics, hSafe] using hEval

theorem successRefines
    (contract : MemoryContract.Contract)
    (transcript : Assembly.ResourceTrace) :
    (primitiveSemantics contract transcript).SuccessRefines
      (Functions.ObserverSemantics.primitiveSemantics transcript) := by
  constructor
  · intro op state values final outputs hEval
    exact (eval_parts hEval).2.2
  · intro kind state values final hEval
    exact (terminal_parts hEval).2

theorem expr_eval_vars_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {results : Nat} {expr : Functions.Expr results}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          expr source =
        .ok (final, values)) :
    final.source.vars = source.source.vars := by
  have hObserver :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          expr source =
        .ok (final, values) :=
    Locals.Source.Effectful.Expr.eval_of_successRefines
      (Functions.ObserverSemantics.stateModel transcript)
      (successRefines contract transcript) hEval
  exact Functions.ObserverSemantics.expr_eval_vars_eq hObserver

theorem argList_eval_vars_eq
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {args : List (Functions.Expr 1)}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (primitiveSemantics contract transcript)
          args source =
        .ok (final, values)) :
    final.source.vars = source.source.vars := by
  have hObserver :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          args source =
        .ok (final, values) :=
    Functions.Source.Effectful.ArgList.eval_of_successRefines
      (Functions.ObserverSemantics.stateModel transcript)
      (successRefines contract transcript) hEval
  exact Functions.ObserverSemantics.argList_eval_vars_eq hObserver

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

end ObserverSafety
end Functions
end EvmCompiler
