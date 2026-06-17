import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Structured

namespace Code

theorem runState_returns_eq
    {code : Code} {state final : RunState}
    (hRun : runState code state = .ok final) :
    final.returns = state.returns := by
  unfold runState at hRun
  cases hCode : run code state.evm with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hRun
  | ok evm =>
      simp [hCode, Bind.bind, Except.bind] at hRun
      cases hRun
      rfl

theorem runConditionState_returns_eq
    {code : Code} {state final : RunState} {cond : Bool}
    (hRun : runConditionState code state = .ok (final, cond)) :
    final.returns = state.returns := by
  unfold runConditionState at hRun
  cases hCondition : runCondition code state.evm with
  | error err =>
      simp [hCondition, Bind.bind, Except.bind] at hRun
  | ok result =>
      rcases result with ⟨evm, condition⟩
      simp [hCondition, Bind.bind, Except.bind] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      rfl

end Code

namespace Code

/--
Semantic frame safety for straight-line code.

Running frame-safe code with an extra hidden stack suffix gives the same EVM
state as running it without that suffix, except that the suffix is preserved at
the bottom of the resulting stack. This is the key condition needed before the
procedure compiler may realize ghost return frames as hidden concrete stack
tokens.
-/
def FrameSafe (code : Code) : Prop :=
  ∀ (state final : EVMState) (hidden : EvmYul.Stack Word),
    run code state = .ok final →
      run code { state with stack := state.stack ++ hidden } =
        .ok { final with stack := final.stack ++ hidden }

end Code

namespace Switch

theorem wf_of_select {canBreak canContinue canLeave : Bool}
    {scrutinee : Word} {cases : List (Word × Block)}
    {defaultBody : Option Block} {selected : Block}
    (hCases :
      ∀ value body, (value, body) ∈ cases →
        Block.WF canBreak canContinue canLeave body)
    (hDefault :
      ∀ body, defaultBody = some body →
        Block.WF canBreak canContinue canLeave body)
    (hSelect : select scrutinee cases defaultBody = some selected) :
    Block.WF canBreak canContinue canLeave selected := by
  revert selected
  induction cases with
  | nil =>
      intro selected hSelect
      exact hDefault selected hSelect
  | cons head rest ih =>
      intro selected hSelect
      rcases head with ⟨value, headBody⟩
      by_cases hEq : value = scrutinee
      · simp [select, hEq] at hSelect
        cases hSelect
        exact hCases value selected (by simp)
      · have hTail :
            select scrutinee rest defaultBody = some selected := by
          simpa [select, hEq] using hSelect
        exact ih
          (fun value body hMem => hCases value body (by simp [hMem]))
          hTail

end Switch

mutual
  /--
  Relational source semantics for the procedure-aware structured layer.

  This mirrors the executable evaluator, but exposes the control cases that the
  compiler proof has to handle: regular fallthrough, loop exits,
  procedure-delimited `leave`, terminal EVM halts, and call-frame
  push/pop/return attachment.
  -/
  inductive Block.Eval (program : Program) :
      Nat → Block → RunState → Outcome → Prop where
    | nil {fuel : Nat} {state : RunState} :
        Block.Eval program (fuel + 1) { stmts := [] } state
          (Outcome.regular state)
    | cons_regular {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state mid : RunState} {outcome : Outcome}
        (hStmt :
          Stmt.Eval program fuel stmt state (Outcome.regular mid))
        (hRest :
          Block.Eval program fuel { stmts := rest } mid outcome) :
        Block.Eval program (fuel + 1) { stmts := stmt :: rest } state outcome
    | cons_brk {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : RunState}
        (hStmt : Stmt.Eval program fuel stmt state (Outcome.brk outState)) :
        Block.Eval program (fuel + 1) { stmts := stmt :: rest } state
          (Outcome.brk outState)
    | cons_cont {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : RunState}
        (hStmt : Stmt.Eval program fuel stmt state (Outcome.cont outState)) :
        Block.Eval program (fuel + 1) { stmts := stmt :: rest } state
          (Outcome.cont outState)
    | cons_leave {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : RunState}
        (hStmt : Stmt.Eval program fuel stmt state (Outcome.leave outState)) :
        Block.Eval program (fuel + 1) { stmts := stmt :: rest } state
          (Outcome.leave outState)
    | cons_halt {fuel : Nat} {stmt : Stmt} {rest : List Stmt}
        {state outState : RunState} {kind : Assembly.HaltKind}
        (hStmt :
          Stmt.Eval program fuel stmt state (Outcome.halt kind outState)) :
        Block.Eval program (fuel + 1) { stmts := stmt :: rest } state
          (Outcome.halt kind outState)

  inductive Stmt.Eval (program : Program) :
      Nat → Stmt → RunState → Outcome → Prop where
    | code {fuel : Nat} {code : Code} {state final : RunState}
        (hCode : Code.runState code state = .ok final) :
        Stmt.Eval program fuel (.code code) state (Outcome.regular final)
    | if_false {fuel : Nat} {cond : Code} {body : Block}
        {state stateAfterCond : RunState}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, false)) :
        Stmt.Eval program (fuel + 1) (.if_ cond body) state
          (Outcome.regular stateAfterCond)
    | if_true {fuel : Nat} {cond : Code} {body : Block}
        {state stateAfterCond : RunState} {outcome : Outcome}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody : Block.Eval program fuel body stateAfterCond outcome) :
        Stmt.Eval program (fuel + 1) (.if_ cond body) state outcome
    | switch_none {fuel : Nat} {scrutinee : Code}
        {cases : List (Word × Block)} {defaultBody : Option Block}
        {state stateAfterScrutinee : RunState}
        {stack : EvmYul.Stack Word} {value : Word}
        (hScrutinee : Code.runState scrutinee state = .ok stateAfterScrutinee)
        (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
        (hSelect : Switch.select value cases defaultBody = none) :
        Stmt.Eval program (fuel + 1)
          (.switch scrutinee cases defaultBody) state
          (Outcome.regular
            (stateAfterScrutinee.withEVM
              { stateAfterScrutinee.evm with stack := stack }))
    | switch_some {fuel : Nat} {scrutinee : Code}
        {cases : List (Word × Block)} {defaultBody : Option Block}
        {state stateAfterScrutinee stateAfterPop : RunState}
        {stack : EvmYul.Stack Word} {value : Word} {body : Block}
        {outcome : Outcome}
        (hScrutinee : Code.runState scrutinee state = .ok stateAfterScrutinee)
        (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
        (hStateAfterPop :
          stateAfterPop =
            stateAfterScrutinee.withEVM
              { stateAfterScrutinee.evm with stack := stack })
        (hSelect : Switch.select value cases defaultBody = some body)
        (hBody : Block.Eval program fuel body stateAfterPop outcome) :
        Stmt.Eval program (fuel + 1)
          (.switch scrutinee cases defaultBody) state outcome
    | for_init_regular {fuel : Nat} {init : Block} {cond : Code}
        {post body : Block} {state initState : RunState}
        {outcome : Outcome}
        (hInit : Block.Eval program fuel init state (Outcome.regular initState))
        (hLoop : For.Eval program fuel cond post body initState outcome) :
        Stmt.Eval program (fuel + 1) (.for_ init cond post body) state outcome
    | for_init_leave {fuel : Nat} {init : Block} {cond : Code}
        {post body : Block} {state outState : RunState}
        (hInit : Block.Eval program fuel init state (Outcome.leave outState)) :
        Stmt.Eval program (fuel + 1) (.for_ init cond post body) state
          (Outcome.leave outState)
    | for_init_halt {fuel : Nat} {init : Block} {cond : Code}
        {post body : Block} {state outState : RunState}
        {kind : Assembly.HaltKind}
        (hInit :
          Block.Eval program fuel init state (Outcome.halt kind outState)) :
        Stmt.Eval program (fuel + 1) (.for_ init cond post body) state
          (Outcome.halt kind outState)
    | brk {fuel : Nat} {state : RunState} :
        Stmt.Eval program fuel .brk state (Outcome.brk state)
    | cont {fuel : Nat} {state : RunState} :
        Stmt.Eval program fuel .cont state (Outcome.cont state)
    | leave {fuel : Nat} {state : RunState}
        (hReturns : state.returns ≠ []) :
        Stmt.Eval program fuel .leave state (Outcome.leave state)
    | call_regular {fuel : Nat} {name : Name} {state : RunState}
        {proc : Proc} {args callerStack stack : EvmYul.Stack Word}
        {bodyState returned : RunState} {frame : ReturnDest}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc state.evm.stack =
            some (args, callerStack))
        (hBody :
          Block.Eval program fuel proc.body
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Outcome.regular bodyState))
        (hPop : bodyState.popReturn? = some (frame, returned))
        (hAttach :
          StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
        Stmt.Eval program (fuel + 1) (.call name) state
          (Outcome.regular
            (returned.withEVM { bodyState.evm with stack := stack }))
    | call_leave {fuel : Nat} {name : Name} {state : RunState}
        {proc : Proc} {args callerStack stack : EvmYul.Stack Word}
        {bodyState returned : RunState} {frame : ReturnDest}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc state.evm.stack =
            some (args, callerStack))
        (hBody :
          Block.Eval program fuel proc.body
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Outcome.leave bodyState))
        (hPop : bodyState.popReturn? = some (frame, returned))
        (hAttach :
          StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
        Stmt.Eval program (fuel + 1) (.call name) state
          (Outcome.regular
            (returned.withEVM { bodyState.evm with stack := stack }))
    | call_halt {fuel : Nat} {name : Name} {state : RunState}
        {proc : Proc} {args callerStack : EvmYul.Stack Word}
        {bodyState : RunState} {kind : Assembly.HaltKind}
        (hLookup : ProcList.lookup? name program.procs = some proc)
        (hSplit :
          StackFrame.splitArgs? proc.argc state.evm.stack =
            some (args, callerStack))
        (hBody :
          Block.Eval program fuel proc.body
            ((state.withEVM { state.evm with stack := args }).pushReturn
              callerStack proc.retc)
            (Outcome.halt kind bodyState)) :
        Stmt.Eval program (fuel + 1) (.call name) state
          (Outcome.halt kind bodyState)
    | terminal {fuel : Nat} {kind : Assembly.HaltKind}
        {state : RunState} {evm : EVMState}
        (hStep : Terminal.step kind state.evm = .ok evm) :
        Stmt.Eval program fuel (.terminal kind) state
          (Outcome.halt kind (state.withEVM evm))

  inductive For.Eval (program : Program) :
      Nat → Code → Block → Block → RunState → Outcome → Prop where
    | false {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond : RunState}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, false)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.regular stateAfterCond)
    | body_brk {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : RunState}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.brk bodyState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.regular bodyState)
    | body_leave {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : RunState}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.leave bodyState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.leave bodyState)
    | body_halt {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState : RunState}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.halt kind bodyState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.halt kind bodyState)
    | regular_post_regular {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {outcome : Outcome}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.regular bodyState))
        (hPost :
          Block.Eval program fuel post bodyState
            (Outcome.regular postState))
        (hLoop : For.Eval program fuel cond post body postState outcome) :
        For.Eval program (fuel + 1) cond post body state outcome
    | cont_post_regular {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {outcome : Outcome}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.cont bodyState))
        (hPost :
          Block.Eval program fuel post bodyState
            (Outcome.regular postState))
        (hLoop : For.Eval program fuel cond post body postState outcome) :
        For.Eval program (fuel + 1) cond post body state outcome
    | regular_post_leave {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.regular bodyState))
        (hPost :
          Block.Eval program fuel post bodyState
            (Outcome.leave postState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.leave postState)
    | cont_post_leave {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.cont bodyState))
        (hPost :
          Block.Eval program fuel post bodyState
            (Outcome.leave postState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.leave postState)
    | regular_post_halt {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.regular bodyState))
        (hPost :
          Block.Eval program fuel post bodyState
            (Outcome.halt kind postState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.halt kind postState)
    | cont_post_halt {fuel : Nat} {cond : Code} {post body : Block}
        {state stateAfterCond bodyState postState : RunState}
        {kind : Assembly.HaltKind}
        (hCond :
          Code.runConditionState cond state = .ok (stateAfterCond, true))
        (hBody :
          Block.Eval program fuel body stateAfterCond
            (Outcome.cont bodyState))
        (hPost :
          Block.Eval program fuel post bodyState
            (Outcome.halt kind postState)) :
        For.Eval program (fuel + 1) cond post body state
          (Outcome.halt kind postState)
end

namespace Outcome

/-- A non-halting outcome cannot retain an unpopped procedure frame. -/
def Nonhalting (outcome : Outcome) : Prop :=
  match outcome.mode with
  | .halt _ => False
  | _ => True

end Outcome

mutual

  /--
  Structured block evaluation preserves the ghost return stack whenever it
  does not halt inside a procedure call.
  -/
  theorem Block.Eval.returns_eq_of_nonhalting
      {program : Program} {fuel : Nat} {block : Block}
      {state : RunState} {outcome : Outcome}
      (hEval : Block.Eval program fuel block state outcome)
      (hNonhalting : outcome.Nonhalting) :
      outcome.state.returns = state.returns := by
    cases hEval with
    | nil =>
        rfl
    | cons_regular hStmt hRest =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hRest hNonhalting).trans
            (Stmt.Eval.returns_eq_of_nonhalting hStmt (by
              simp [Outcome.Nonhalting]))
    | cons_brk hStmt =>
        exact
          Stmt.Eval.returns_eq_of_nonhalting hStmt (by
            simp [Outcome.Nonhalting])
    | cons_cont hStmt =>
        exact
          Stmt.Eval.returns_eq_of_nonhalting hStmt (by
            simp [Outcome.Nonhalting])
    | cons_leave hStmt =>
        exact
          Stmt.Eval.returns_eq_of_nonhalting hStmt (by
            simp [Outcome.Nonhalting])
    | cons_halt hStmt =>
        simp [Outcome.Nonhalting] at hNonhalting
  termination_by fuel

  /--
  Structured statement evaluation preserves the ghost return stack for every
  regular or lexical-control outcome.
  -/
  theorem Stmt.Eval.returns_eq_of_nonhalting
      {program : Program} {fuel : Nat} {stmt : Stmt}
      {state : RunState} {outcome : Outcome}
      (hEval : Stmt.Eval program fuel stmt state outcome)
      (hNonhalting : outcome.Nonhalting) :
      outcome.state.returns = state.returns := by
    cases hEval with
    | code hCode =>
        exact Code.runState_returns_eq hCode
    | if_false hCond =>
        exact Code.runConditionState_returns_eq hCond
    | if_true hCond hBody =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hBody hNonhalting).trans
            (Code.runConditionState_returns_eq hCond)
    | switch_none hScrutinee hPop hSelect =>
        simpa [RunState.withEVM] using Code.runState_returns_eq hScrutinee
    | switch_some hScrutinee hPop hStateAfterPop hSelect hBody =>
        have hBodyReturns :=
          Block.Eval.returns_eq_of_nonhalting hBody hNonhalting
        exact
          hBodyReturns.trans
            (by
              simpa [hStateAfterPop, RunState.withEVM] using
                Code.runState_returns_eq hScrutinee)
    | for_init_regular hInit hLoop =>
        exact
          (For.Eval.returns_eq_of_nonhalting hLoop hNonhalting).trans
            (Block.Eval.returns_eq_of_nonhalting hInit (by
              simp [Outcome.Nonhalting]))
    | for_init_leave hInit =>
        exact
          Block.Eval.returns_eq_of_nonhalting hInit (by
            simp [Outcome.Nonhalting])
    | for_init_halt hInit =>
        simp [Outcome.Nonhalting] at hNonhalting
    | brk =>
        rfl
    | cont =>
        rfl
    | leave hReturns =>
        rfl
    | call_regular hLookup hSplit hBody hPop hAttach =>
        have hBodyReturns :=
          Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])
        simp only [Outcome.regular_state, RunState.pushReturn_returns,
          RunState.withEVM_returns] at hBodyReturns
        unfold RunState.popReturn? at hPop
        rw [hBodyReturns] at hPop
        simp at hPop
        exact (congrArg RunState.returns hPop.2).symm
    | call_leave hLookup hSplit hBody hPop hAttach =>
        have hBodyReturns :=
          Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])
        simp only [Outcome.leave_state, RunState.pushReturn_returns,
          RunState.withEVM_returns] at hBodyReturns
        unfold RunState.popReturn? at hPop
        rw [hBodyReturns] at hPop
        simp at hPop
        exact (congrArg RunState.returns hPop.2).symm
    | call_halt hLookup hSplit hBody =>
        simp [Outcome.Nonhalting] at hNonhalting
    | terminal hStep =>
        simp [Outcome.Nonhalting] at hNonhalting
  termination_by fuel

  /--
  Loop evaluation preserves the ghost return stack for every non-halting
  outcome, including break-to-regular and continue recursion.
  -/
  theorem For.Eval.returns_eq_of_nonhalting
      {program : Program} {fuel : Nat} {cond : Code}
      {post body : Block} {state : RunState} {outcome : Outcome}
      (hEval : For.Eval program fuel cond post body state outcome)
      (hNonhalting : outcome.Nonhalting) :
      outcome.state.returns = state.returns := by
    cases hEval with
    | false hCond =>
        exact Code.runConditionState_returns_eq hCond
    | body_brk hCond hBody =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])).trans
            (Code.runConditionState_returns_eq hCond)
    | body_leave hCond hBody =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])).trans
            (Code.runConditionState_returns_eq hCond)
    | body_halt hCond hBody =>
        simp [Outcome.Nonhalting] at hNonhalting
    | regular_post_regular hCond hBody hPost hLoop =>
        exact
          (For.Eval.returns_eq_of_nonhalting hLoop hNonhalting).trans
            ((Block.Eval.returns_eq_of_nonhalting hPost (by
              simp [Outcome.Nonhalting])).trans
              ((Block.Eval.returns_eq_of_nonhalting hBody (by
                simp [Outcome.Nonhalting])).trans
                (Code.runConditionState_returns_eq hCond)))
    | cont_post_regular hCond hBody hPost hLoop =>
        exact
          (For.Eval.returns_eq_of_nonhalting hLoop hNonhalting).trans
            ((Block.Eval.returns_eq_of_nonhalting hPost (by
              simp [Outcome.Nonhalting])).trans
              ((Block.Eval.returns_eq_of_nonhalting hBody (by
                simp [Outcome.Nonhalting])).trans
                (Code.runConditionState_returns_eq hCond)))
    | regular_post_leave hCond hBody hPost =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hPost (by
            simp [Outcome.Nonhalting])).trans
            ((Block.Eval.returns_eq_of_nonhalting hBody (by
              simp [Outcome.Nonhalting])).trans
              (Code.runConditionState_returns_eq hCond))
    | cont_post_leave hCond hBody hPost =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hPost (by
            simp [Outcome.Nonhalting])).trans
            ((Block.Eval.returns_eq_of_nonhalting hBody (by
              simp [Outcome.Nonhalting])).trans
              (Code.runConditionState_returns_eq hCond))
    | regular_post_halt hCond hBody hPost =>
        simp [Outcome.Nonhalting] at hNonhalting
    | cont_post_halt hCond hBody hPost =>
        simp [Outcome.Nonhalting] at hNonhalting
  termination_by fuel

end

set_option linter.unusedSimpArgs false in
mutual
  theorem Block.eval_of_run {program : Program} {fuel : Nat} {block : Block}
      {state : RunState} {outcome : Outcome}
      (hRun : Block.run program fuel block state = .ok outcome) :
      Block.Eval program fuel block state outcome := by
    cases fuel with
    | zero =>
        simp [Block.run, EffectSemantics.Block.run, invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Block.run, EffectSemantics.Block.run] at hRun
                cases hRun
                exact Block.Eval.nil
            | cons stmt rest =>
                unfold Block.run EffectSemantics.Block.run at hRun
                rw [EffectSemantics.Stmt.ordinary_run] at hRun
                cases hStmtRun : Stmt.run program fuel stmt state with
                | error err =>
                    rw [hStmtRun] at hRun
                    cases hRun
                | ok stmtOutcome =>
                    rw [hStmtRun] at hRun
                    have hStmtEval := Stmt.eval_of_run hStmtRun
                    cases stmtOutcome with
                    | mk stmtState stmtMode =>
                        cases stmtMode with
                        | regular =>
                            exact
                              Block.Eval.cons_regular
                                (by
                                  simpa [Outcome.regular] using hStmtEval)
                                (Block.eval_of_run hRun)
                        | brk =>
                            cases hRun
                            exact
                              Block.Eval.cons_brk
                                (by simpa [Outcome.brk] using hStmtEval)
                        | cont =>
                            cases hRun
                            exact
                              Block.Eval.cons_cont
                                (by simpa [Outcome.cont] using hStmtEval)
                        | leave =>
                            cases hRun
                            exact
                              Block.Eval.cons_leave
                                (by simpa [Outcome.leave] using hStmtEval)
                        | halt kind =>
                            cases hRun
                            exact
                              Block.Eval.cons_halt
                                (by simpa [Outcome.halt] using hStmtEval)

  theorem Stmt.eval_of_run {program : Program} {fuel : Nat} {stmt : Stmt}
      {state : RunState} {outcome : Outcome}
      (hRun : Stmt.run program fuel stmt state = .ok outcome) :
      Stmt.Eval program fuel stmt state outcome := by
    cases stmt with
    | code code =>
        unfold Stmt.run EffectSemantics.Stmt.run at hRun
        rw [EffectSemantics.Code.ordinary_state_run] at hRun
        cases hCode : Code.runState code state with
        | error err =>
            simp [Stmt.run, EffectSemantics.Stmt.run, hCode, Bind.bind, Except.bind] at hRun
        | ok final =>
            simp [Stmt.run, EffectSemantics.Stmt.run, hCode, Bind.bind, Except.bind] at hRun
            cases hRun
            exact Stmt.Eval.code hCode
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, EffectSemantics.Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run EffectSemantics.Stmt.run at hRun
            rw [EffectSemantics.Code.ordinary_state_runCondition] at hRun
            cases hCond : Code.runConditionState cond state with
            | error err =>
                rw [hCond] at hRun
                cases hRun
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                rw [hCond] at hRun
                cases condTrue with
                | false =>
                    simp at hRun
                    cases hRun
                    exact Stmt.Eval.if_false hCond
                | true =>
                    exact
                      Stmt.Eval.if_true hCond
                        (Block.eval_of_run hRun)
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, EffectSemantics.Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run EffectSemantics.Stmt.run at hRun
            rw [EffectSemantics.Code.ordinary_state_run] at hRun
            cases hScrutinee : Code.runState scrutinee state with
            | error err =>
                simp [hScrutinee, Bind.bind, Except.bind] at hRun
            | ok stateAfterScrutinee =>
                simp [hScrutinee, Bind.bind, Except.bind] at hRun
                cases hPop : stateAfterScrutinee.evm.stack.pop with
                | none =>
                    simp [hPop] at hRun
                | some popped =>
                    rcases popped with ⟨stack, value⟩
                    simp [hPop] at hRun
                    let stateAfterPop :=
                      stateAfterScrutinee.withEVM
                        { stateAfterScrutinee.evm with stack := stack }
                    cases hSelect : Switch.select value cases defaultBody with
                    | none =>
                        simp [hSelect] at hRun
                        cases hRun
                        exact Stmt.Eval.switch_none hScrutinee hPop hSelect
                    | some body =>
                        simp [hSelect] at hRun
                        exact
                          Stmt.Eval.switch_some hScrutinee hPop
                            (show stateAfterPop =
                              stateAfterScrutinee.withEVM
                                { stateAfterScrutinee.evm with stack := stack } from
                              rfl)
                            hSelect (Block.eval_of_run hRun)
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, EffectSemantics.Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run EffectSemantics.Stmt.run at hRun
            rw [EffectSemantics.Block.ordinary_run] at hRun
            cases hInitRun : Block.run program fuel init state with
            | error err =>
                simp [hInitRun, Bind.bind, Except.bind] at hRun
            | ok initOutcome =>
                simp [hInitRun, Bind.bind, Except.bind] at hRun
                have hInitEval := Block.eval_of_run hInitRun
                cases initOutcome with
                | mk initState initMode =>
                    cases initMode with
                    | regular =>
                        exact
                          Stmt.Eval.for_init_regular
                            (by simpa [Outcome.regular] using hInitEval)
                            (For.eval_of_run hRun)
                    | brk =>
                        dsimp [Bind.bind, Except.bind, invalid] at hRun
                        cases hRun
                    | cont =>
                        dsimp [Bind.bind, Except.bind, invalid] at hRun
                        cases hRun
                    | leave =>
                        change
                          Except.ok (Outcome.leave initState) =
                            Except.ok outcome at hRun
                        cases hRun
                        exact
                          Stmt.Eval.for_init_leave
                            (by simpa [Outcome.leave] using hInitEval)
                    | halt kind =>
                        change
                          Except.ok (Outcome.halt kind initState) =
                            Except.ok outcome at hRun
                        cases hRun
                        exact
                          Stmt.Eval.for_init_halt
                            (by simpa [Outcome.halt] using hInitEval)
    | brk =>
        simp [Stmt.run, EffectSemantics.Stmt.run] at hRun
        cases hRun
        exact Stmt.Eval.brk
    | cont =>
        simp [Stmt.run, EffectSemantics.Stmt.run] at hRun
        cases hRun
        exact Stmt.Eval.cont
    | leave =>
        unfold Stmt.run EffectSemantics.Stmt.run at hRun
        simp only [EffectSemantics.Ordinary.runStateModel_returns] at hRun
        cases hReturns : state.returns with
        | nil =>
            simp [hReturns, invalid] at hRun
        | cons frame returns =>
            simp [hReturns] at hRun
            cases hRun
            exact Stmt.Eval.leave (by simp [hReturns])
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.run, EffectSemantics.Stmt.run, invalid] at hRun
        | succ fuel =>
            unfold Stmt.run EffectSemantics.Stmt.run at hRun
            simp only [EffectSemantics.Ordinary.runStateModel_evm,
              EffectSemantics.Ordinary.runStateModel_withEVM,
              EffectSemantics.Ordinary.runStateModel_pushReturn,
              EffectSemantics.Ordinary.runStateModel_popReturn?] at hRun
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                simp [hLookup, Bind.bind, Except.bind, invalid] at hRun
            | some proc =>
                simp [hLookup, Bind.bind, Except.bind] at hRun
                cases hSplit :
                    StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hSplit, Bind.bind, Except.bind] at hRun
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    simp [hSplit, Bind.bind, Except.bind] at hRun
                    let callState : RunState :=
                      (state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc
                    cases hBodyRun :
                        Block.run program fuel proc.body callState with
                    | error err =>
                        change
                          EffectSemantics.Block.run
                              EffectSemantics.Ordinary.runStateModel
                              EffectSemantics.Ordinary.handler
                              program fuel proc.body callState =
                            .error err at hBodyRun
                        simp [callState, hBodyRun, Bind.bind, Except.bind] at hRun
                    | ok bodyOutcome =>
                        have hBodyRunPublic :
                            Block.run program fuel proc.body callState =
                              .ok bodyOutcome := hBodyRun
                        change
                          EffectSemantics.Block.run
                              EffectSemantics.Ordinary.runStateModel
                              EffectSemantics.Ordinary.handler
                              program fuel proc.body callState =
                            .ok bodyOutcome at hBodyRun
                        simp [callState, hBodyRun, Bind.bind, Except.bind] at hRun
                        have hBodyEval := Block.eval_of_run hBodyRunPublic
                        cases bodyOutcome with
                        | mk bodyState bodyMode =>
                            cases bodyMode with
                            | regular =>
                                simp [Outcome.regular] at hRun
                                cases hPop : bodyState.popReturn? with
                                | none =>
                                    simp [hPop, invalid] at hRun
                                | some popped =>
                                    rcases popped with ⟨frame, returned⟩
                                    simp [hPop] at hRun
                                    cases hAttach :
                                        StackFrame.attachReturns? frame
                                          bodyState.evm.stack with
                                    | none =>
                                        simp [hAttach, invalid] at hRun
                                    | some stack =>
                                        simp [hAttach] at hRun
                                        cases hRun
                                        exact
                                          Stmt.Eval.call_regular hLookup hSplit
                                            (by
                                              simpa [callState, Outcome.regular]
                                                using hBodyEval)
                                            hPop hAttach
                            | brk =>
                                simp [Outcome.brk, invalid] at hRun
                            | cont =>
                                simp [Outcome.cont, invalid] at hRun
                            | leave =>
                                simp [Outcome.leave] at hRun
                                cases hPop : bodyState.popReturn? with
                                | none =>
                                    simp [hPop, invalid] at hRun
                                | some popped =>
                                    rcases popped with ⟨frame, returned⟩
                                    simp [hPop] at hRun
                                    cases hAttach :
                                        StackFrame.attachReturns? frame
                                          bodyState.evm.stack with
                                    | none =>
                                        simp [hAttach, invalid] at hRun
                                    | some stack =>
                                        simp [hAttach] at hRun
                                        cases hRun
                                        exact
                                          Stmt.Eval.call_leave hLookup hSplit
                                            (by
                                              simpa [callState, Outcome.leave]
                                                using hBodyEval)
                                            hPop hAttach
                            | halt kind =>
                                simp [Outcome.halt] at hRun
                                cases hRun
                                exact
                                  Stmt.Eval.call_halt hLookup hSplit
                                    (by
                                      simpa [callState, Outcome.halt]
                                        using hBodyEval)
    | terminal kind =>
        simp only [Stmt.run, EffectSemantics.Stmt.run,
          EffectSemantics.Ordinary.runStateModel_evm,
          EffectSemantics.Ordinary.runStateModel_withEVM] at hRun
        cases hStep : Terminal.step kind state.evm with
        | error err =>
            simp [hStep] at hRun
        | ok evm =>
            simp [hStep] at hRun
            cases hRun
            exact Stmt.Eval.terminal hStep

  theorem For.eval_of_run {program : Program} {fuel : Nat} {cond : Code}
      {post body : Block} {state : RunState} {outcome : Outcome}
      (hRun :
        Stmt.runForLoop program fuel cond post body state = .ok outcome) :
      For.Eval program fuel cond post body state outcome := by
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, EffectSemantics.Stmt.runForLoop, invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoop EffectSemantics.Stmt.runForLoop at hRun
        rw [EffectSemantics.Code.ordinary_state_runCondition] at hRun
        cases hCond : Code.runConditionState cond state with
        | error err =>
            simp [hCond, Bind.bind, Except.bind] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            simp [hCond, Bind.bind, Except.bind] at hRun
            cases condTrue with
            | false =>
                simp at hRun
                cases hRun
                exact For.Eval.false hCond
            | true =>
                cases hBodyRun :
                    Block.run program fuel body stateAfterCond with
                | error err =>
                    change
                      EffectSemantics.Block.run
                          EffectSemantics.Ordinary.runStateModel
                          EffectSemantics.Ordinary.handler
                          program fuel body stateAfterCond =
                        .error err at hBodyRun
                    simp [hBodyRun, Bind.bind, Except.bind] at hRun
                | ok bodyOutcome =>
                    have hBodyRunPublic :
                        Block.run program fuel body stateAfterCond =
                          .ok bodyOutcome := hBodyRun
                    change
                      EffectSemantics.Block.run
                          EffectSemantics.Ordinary.runStateModel
                          EffectSemantics.Ordinary.handler
                          program fuel body stateAfterCond =
                        .ok bodyOutcome at hBodyRun
                    simp [hBodyRun, Bind.bind, Except.bind] at hRun
                    have hBodyEval := Block.eval_of_run hBodyRunPublic
                    cases bodyOutcome with
                    | mk bodyState bodyMode =>
                        cases bodyMode with
                        | regular =>
                            simp [Outcome.regular] at hRun
                            cases hPostRun :
                                Block.run program fuel post bodyState with
                            | error err =>
                                change
                                  EffectSemantics.Block.run
                                      EffectSemantics.Ordinary.runStateModel
                                      EffectSemantics.Ordinary.handler
                                      program fuel post bodyState =
                                    .error err at hPostRun
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                            | ok postOutcome =>
                                have hPostRunPublic :
                                    Block.run program fuel post bodyState =
                                      .ok postOutcome := hPostRun
                                change
                                  EffectSemantics.Block.run
                                      EffectSemantics.Ordinary.runStateModel
                                      EffectSemantics.Ordinary.handler
                                      program fuel post bodyState =
                                    .ok postOutcome at hPostRun
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                                have hPostEval := Block.eval_of_run hPostRunPublic
                                cases postOutcome with
                                | mk postState postMode =>
                                    cases postMode with
                                    | regular =>
                                        exact
                                          For.Eval.regular_post_regular hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.regular]
                                                using hPostEval)
                                            (For.eval_of_run hRun)
                                    | brk =>
                                        simp [invalid] at hRun
                                    | cont =>
                                        simp [invalid] at hRun
                                    | leave =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.regular_post_leave hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.leave]
                                                using hPostEval)
                                    | halt kind =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.regular_post_halt hCond
                                            (by
                                              simpa [Outcome.regular]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.halt]
                                                using hPostEval)
                        | brk =>
                            simp [Outcome.brk] at hRun
                            cases hRun
                            exact
                              For.Eval.body_brk hCond
                                (by simpa [Outcome.brk] using hBodyEval)
                        | cont =>
                            simp [Outcome.cont] at hRun
                            cases hPostRun :
                                Block.run program fuel post bodyState with
                            | error err =>
                                change
                                  EffectSemantics.Block.run
                                      EffectSemantics.Ordinary.runStateModel
                                      EffectSemantics.Ordinary.handler
                                      program fuel post bodyState =
                                    .error err at hPostRun
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                            | ok postOutcome =>
                                have hPostRunPublic :
                                    Block.run program fuel post bodyState =
                                      .ok postOutcome := hPostRun
                                change
                                  EffectSemantics.Block.run
                                      EffectSemantics.Ordinary.runStateModel
                                      EffectSemantics.Ordinary.handler
                                      program fuel post bodyState =
                                    .ok postOutcome at hPostRun
                                simp [hPostRun, Bind.bind, Except.bind] at hRun
                                have hPostEval := Block.eval_of_run hPostRunPublic
                                cases postOutcome with
                                | mk postState postMode =>
                                    cases postMode with
                                    | regular =>
                                        exact
                                          For.Eval.cont_post_regular hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.regular]
                                                using hPostEval)
                                            (For.eval_of_run hRun)
                                    | brk =>
                                        simp [invalid] at hRun
                                    | cont =>
                                        simp [invalid] at hRun
                                    | leave =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.cont_post_leave hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.leave]
                                                using hPostEval)
                                    | halt kind =>
                                        simp at hRun
                                        cases hRun
                                        exact
                                          For.Eval.cont_post_halt hCond
                                            (by
                                              simpa [Outcome.cont]
                                                using hBodyEval)
                                            (by
                                              simpa [Outcome.halt]
                                                using hPostEval)
                        | leave =>
                            simp [Outcome.leave] at hRun
                            cases hRun
                            exact
                              For.Eval.body_leave hCond
                                (by simpa [Outcome.leave] using hBodyEval)
                        | halt kind =>
                            simp [Outcome.halt] at hRun
                            cases hRun
                            exact
                              For.Eval.body_halt hCond
                                (by simpa [Outcome.halt] using hBodyEval)
end

namespace Program

theorem eval_of_runState {fuel : Nat} {program : Program}
    {state : RunState} {outcome : Outcome}
    (hRun : program.runState fuel state = .ok outcome) :
    Block.Eval program fuel program.body state outcome := by
  exact Block.eval_of_run hRun

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : program.run fuel initial = .ok outcome) :
    Block.Eval program fuel program.body (Program.initialState initial)
      outcome := by
  exact eval_of_runState hRun

end Program

mutual
  inductive Block.FrameSafe : Block → Prop where
    | nil : Block.FrameSafe { stmts := [] }
    | cons {stmt : Stmt} {rest : List Stmt}
        (hStmt : Stmt.FrameSafe stmt)
        (hRest : Block.FrameSafe { stmts := rest }) :
        Block.FrameSafe { stmts := stmt :: rest }

  inductive Stmt.FrameSafe : Stmt → Prop where
    | code {code : Code} (hCode : Code.FrameSafe code) :
        Stmt.FrameSafe (.code code)
    | if_ {cond : Code} {body : Block}
        (hCond : Code.FrameSafe cond)
        (hBody : Block.FrameSafe body) :
        Stmt.FrameSafe (.if_ cond body)
    | switch {scrutinee : Code} {cases : List (Word × Block)}
        {defaultBody : Option Block}
        (hScrutinee : Code.FrameSafe scrutinee)
        (hCases :
          ∀ value body, (value, body) ∈ cases → Block.FrameSafe body)
        (hDefault :
          ∀ body, defaultBody = some body → Block.FrameSafe body) :
        Stmt.FrameSafe (.switch scrutinee cases defaultBody)
    | for_ {init post body : Block} {cond : Code}
        (hInit : Block.FrameSafe init)
        (hCond : Code.FrameSafe cond)
        (hPost : Block.FrameSafe post)
        (hBody : Block.FrameSafe body) :
        Stmt.FrameSafe (.for_ init cond post body)
    | brk : Stmt.FrameSafe .brk
    | cont : Stmt.FrameSafe .cont
    | leave : Stmt.FrameSafe .leave
    | call {name : Name} : Stmt.FrameSafe (.call name)
    | terminal {kind : Assembly.HaltKind} : Stmt.FrameSafe (.terminal kind)
end

namespace Proc

def FrameSafe (proc : Proc) : Prop :=
  proc.body.FrameSafe

end Proc

namespace ProcList

def FrameSafe : List Proc → Prop
  | [] => True
  | proc :: rest => proc.FrameSafe ∧ FrameSafe rest

theorem FrameSafe_of_lookup?
    {procs : List Proc} {name : Name} {proc : Proc}
    (hFrameSafe : FrameSafe procs)
    (hLookup : lookup? name procs = some proc) :
    proc.FrameSafe := by
  induction procs with
  | nil =>
      simp [lookup?] at hLookup
  | cons head rest ih =>
      unfold lookup? at hLookup
      by_cases hName : head.name = name
      · simp [hName] at hLookup
        cases hLookup
        exact hFrameSafe.1
      · simp [hName] at hLookup
        exact ih hFrameSafe.2 hLookup

end ProcList

namespace Program

def FrameSafe (program : Program) : Prop :=
  ProcList.FrameSafe program.procs ∧ program.body.FrameSafe

theorem procFrameSafe_of_lookup?
    {program : Program} {name : Name} {proc : Proc}
    (hFrameSafe : program.FrameSafe)
    (hLookup : ProcList.lookup? name program.procs = some proc) :
    proc.FrameSafe :=
  ProcList.FrameSafe_of_lookup? hFrameSafe.1 hLookup

end Program

namespace Observation

def eraseState (state : RunState) : EVMState :=
  state.evm

def eraseOutcome (outcome : Outcome) : EVMState × Mode :=
  (outcome.state.evm, outcome.mode)

end Observation

end Structured
end EvmCompiler
