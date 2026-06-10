import EvmCompiler.Locals.Compiler
import EvmCompiler.Locals.Semantics
import EvmCompiler.Expressions.Preservation

namespace EvmCompiler

namespace Expressions

set_option maxHeartbeats 800000 in
mutual
  theorem Block.run_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {block : Block} {state : RunState}
        {outcome : Outcome},
        fuel ≤ fuel' →
        Block.run program fuel block state = .ok outcome →
        Block.run program fuel' block state = .ok outcome := by
    intro fuel fuel' block state outcome hLe hRun
    cases fuel with
    | zero =>
        cases block
        simp [Block.run, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            cases block with
            | mk stmts =>
                cases stmts with
                | nil =>
                    simpa [Block.run] using hRun
                | cons stmt rest =>
                    cases hStmt : Stmt.run program fuel stmt state with
                    | error err =>
                        simp [Block.run, hStmt] at hRun
                    | ok stmtOutcome =>
                        have hStmt' :
                            Stmt.run program fuel' stmt state =
                              .ok stmtOutcome :=
                          Stmt.run_mono program hFuelLe hStmt
                        cases hMode : stmtOutcome.mode with
                        | regular =>
                            simp [Block.run, hStmt, hStmt', hMode] at hRun ⊢
                            exact
                              Block.run_mono program hFuelLe hRun
                        | brk =>
                            simp [Block.run, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun
                        | cont =>
                            simp [Block.run, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun
                        | leave =>
                            simp [Block.run, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [Block.run, hStmt, hStmt', hMode] at hRun ⊢
                            exact hRun

  theorem Stmt.runForLoop_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {cond : Expr 1} {post body : Block}
        {state : RunState} {outcome : Outcome},
        fuel ≤ fuel' →
        Stmt.runForLoop program fuel cond post body state = .ok outcome →
        Stmt.runForLoop program fuel' cond post body state = .ok outcome := by
    intro fuel fuel' cond post body state outcome hLe hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
            unfold Stmt.runForLoop at hRun ⊢
            cases hCond : Expr.runConditionState cond state with
            | error err =>
                simp [hCond] at hRun ⊢
            | ok condResult =>
                rcases condResult with ⟨stateAfterCond, condTrue⟩
                cases condTrue with
                | false =>
                    simp [hCond] at hRun ⊢
                    exact hRun
                | true =>
                    simp [hCond] at hRun ⊢
                    cases hBody :
                        Block.run program fuel body stateAfterCond with
                    | error err =>
                        simp [hBody] at hRun
                    | ok bodyOutcome =>
                        have hBody' :
                            Block.run program fuel' body stateAfterCond =
                              .ok bodyOutcome :=
                          Block.run_mono program hFuelLe hBody
                        cases hBodyMode : bodyOutcome.mode with
                        | brk =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | regular =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.run program fuel post bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.run program fuel' post
                                        bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.run_mono program hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono program hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | cont =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            cases hPost :
                                Block.run program fuel post bodyOutcome.state with
                            | error err =>
                                simp [hPost] at hRun
                            | ok postOutcome =>
                                have hPost' :
                                    Block.run program fuel' post
                                        bodyOutcome.state =
                                      .ok postOutcome :=
                                  Block.run_mono program hFuelLe hPost
                                cases hPostMode : postOutcome.mode with
                                | regular =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact
                                      Stmt.runForLoop_mono program hFuelLe hRun
                                | brk =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | cont =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | leave =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                                | halt kind =>
                                    simp [hPost, hPost', hPostMode] at hRun ⊢
                                    exact hRun
                        | leave =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun
                        | halt kind =>
                            simp [hBody, hBody', hBodyMode] at hRun ⊢
                            exact hRun

  theorem Stmt.run_mono (program : Program) :
      ∀ {fuel fuel' : Nat} {stmt : Stmt} {state : RunState}
        {outcome : Outcome},
        fuel ≤ fuel' →
        Stmt.run program fuel stmt state = .ok outcome →
        Stmt.run program fuel' stmt state = .ok outcome := by
    intro fuel fuel' stmt state outcome hLe hRun
    cases stmt with
    | code code =>
        simpa [Stmt.run] using hRun
    | expr expr =>
        simpa [Stmt.run] using hRun
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hCond : Expr.runConditionState cond state with
                | error err =>
                    simp [hCond] at hRun ⊢
                | ok condResult =>
                    rcases condResult with ⟨stateAfterCond, condTrue⟩
                    cases condTrue with
                    | false =>
                        simp [hCond] at hRun ⊢
                        exact hRun
                    | true =>
                        simp [hCond] at hRun ⊢
                        exact Block.run_mono program hFuelLe hRun
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hScrutinee : Expr.run scrutinee state.evm with
                | error err =>
                    simp [hScrutinee] at hRun ⊢
                | ok evmAfterScrutinee =>
                    cases hPop : evmAfterScrutinee.stack.pop with
                    | none =>
                        simp [hScrutinee, hPop] at hRun ⊢
                    | some pair =>
                        rcases pair with ⟨stack, value⟩
                        cases hSelected :
                            Switch.select value cases defaultBody with
                        | none =>
                            simp [hScrutinee, hPop, hSelected] at hRun ⊢
                            exact hRun
                        | some selected =>
                            simp [hScrutinee, hPop, hSelected] at hRun ⊢
                            exact Block.run_mono program hFuelLe hRun
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hInit : Block.run program fuel init state with
                | error err =>
                    simp [hInit] at hRun
                | ok initOutcome =>
                    have hInit' :
                        Block.run program fuel' init state = .ok initOutcome :=
                      Block.run_mono program hFuelLe hInit
                    cases hInitMode : initOutcome.mode with
                    | regular =>
                        simp [hInit, hInit', hInitMode] at hRun ⊢
                        exact Stmt.runForLoop_mono program hFuelLe hRun
                    | brk =>
                        simp [hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | cont =>
                        simp [hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | leave =>
                        simp [hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
                    | halt kind =>
                        simp [hInit, hInit', hInitMode] at hRun ⊢
                        exact hRun
    | brk =>
        simpa [Stmt.run] using hRun
    | cont =>
        simpa [Stmt.run] using hRun
    | leave =>
        cases state.returns <;>
          simpa [Stmt.run, invalid, Structured.invalid] using hRun
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hLe
                unfold Stmt.run at hRun ⊢
                cases hLookup : ProcList.lookup? name program.procs with
                | none =>
                    simp [hLookup] at hRun ⊢
                    exact hRun
                | some proc =>
                    cases hSplit :
                        Structured.StackFrame.splitArgs? proc.argc
                          state.evm.stack with
                    | none =>
                        simp [hLookup, hSplit] at hRun ⊢
                    | some split =>
                        rcases split with ⟨args, callerStack⟩
                        cases hBody :
                            Block.run program fuel proc.body
                              ((state.withEVM { state.evm with stack := args }).pushReturn
                                callerStack proc.retc) with
                        | error err =>
                            simp [hLookup, hSplit, hBody] at hRun
                        | ok bodyOutcome =>
                            have hBody' :
                                Block.run program fuel' proc.body
                                    ((state.withEVM
                                      { state.evm with stack := args }).pushReturn
                                      callerStack proc.retc) =
                                  .ok bodyOutcome :=
                              Block.run_mono program hFuelLe hBody
                            cases hBodyMode : bodyOutcome.mode <;>
                              simp [hLookup, hSplit, hBody, hBody',
                                hBodyMode] at hRun ⊢ <;>
                              exact hRun
    | terminal kind =>
        simpa [Stmt.run] using hRun
end

namespace Block

theorem run_single_exists (program : Program)
    {stmt : Stmt} {state : RunState} {outcome : Outcome}
    (hStmt : ∃ fuel, Stmt.run program fuel stmt state = .ok outcome) :
    ∃ fuel, Block.run program fuel { stmts := [stmt] } state =
      .ok outcome := by
  rcases hStmt with ⟨fuel, hStmt⟩
  refine ⟨fuel + 2, ?_⟩
  have hStmt' :
      Stmt.run program (fuel + 1) stmt state = .ok outcome :=
    Stmt.run_mono program (Nat.le_succ fuel) hStmt
  cases outcome with
  | mk outState outMode =>
      cases outMode <;>
        simp [Block.run, hStmt', Structured.Outcome.regular,
          Structured.Outcome.brk, Structured.Outcome.cont,
          Structured.Outcome.leave, Structured.Outcome.halt]

theorem run_nil_ok {program : Program} {fuel : Nat} {state : RunState}
    {outcome : Outcome}
    (hRun : Block.run program fuel { stmts := [] } state = .ok outcome) :
    outcome = Outcome.regular state := by
  cases fuel with
  | zero =>
      simp [Block.run, invalid, Structured.invalid] at hRun
  | succ fuel =>
      have h : Outcome.regular state = outcome := by
        simpa [Block.run] using hRun
      exact h.symm

theorem run_append_regular_exists (program : Program) :
    ∀ (left right : List Stmt) (state mid : RunState) (outcome : Outcome),
      (∃ fuel, Block.run program fuel { stmts := left } state =
        .ok (Outcome.regular mid)) →
      (∃ fuel, Block.run program fuel { stmts := right } mid =
        .ok outcome) →
      ∃ fuel, Block.run program fuel { stmts := left ++ right } state =
        .ok outcome := by
  intro left
  induction left with
  | nil =>
      intro right state mid outcome hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      have hMid : mid = state := by
        have hEq := run_nil_ok (program := program) hLeft
        cases hEq
        rfl
      subst mid
      simpa using hRight
  | cons stmt rest ih =>
      intro right state mid outcome hLeft hRight
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.run, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt : Stmt.run program fuelLeft stmt state with
          | error err =>
              simp [Block.run, hStmt] at hLeft
          | ok stmtOutcome =>
              cases hMode : stmtOutcome.mode with
              | regular =>
                  simp [Block.run, hStmt, hMode] at hLeft
                  have hRest :
                      ∃ fuel,
                        Block.run program fuel { stmts := rest }
                          stmtOutcome.state = .ok (Outcome.regular mid) :=
                    ⟨fuelLeft, hLeft⟩
                  rcases ih right stmtOutcome.state mid outcome hRest hRight with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run program (Nat.max fuelLeft fuelRest) stmt state =
                        .ok stmtOutcome :=
                    Stmt.run_mono program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.run program (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok outcome :=
                    Block.run_mono program (Nat.le_max_right _ _) hRestAppend
                  simp [fuel, Block.run, hStmt', hMode, hRestAppend']
              | brk =>
                  simp [Block.run, hStmt, hMode] at hLeft
                  cases hLeft
                  simp at hMode
              | cont =>
                  simp [Block.run, hStmt, hMode] at hLeft
                  cases hLeft
                  simp at hMode
              | leave =>
                  simp [Block.run, hStmt, hMode] at hLeft
                  cases hLeft
                  simp at hMode
              | halt kind =>
                  simp [Block.run, hStmt, hMode] at hLeft
                  cases hLeft
                  simp at hMode

theorem run_append_nonregular_exists (program : Program) :
    ∀ (left right : List Stmt) (state : RunState) (outcome : Outcome),
      (∃ fuel, Block.run program fuel { stmts := left } state =
        .ok outcome) →
      outcome.mode ≠ .regular →
      ∃ fuel, Block.run program fuel { stmts := left ++ right } state =
        .ok outcome := by
  intro left
  induction left with
  | nil =>
      intro right state outcome hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      have hOutcome := run_nil_ok (program := program) hLeft
      cases hOutcome
      simp at hMode
  | cons stmt rest ih =>
      intro right state outcome hLeft hMode
      rcases hLeft with ⟨fuelLeft, hLeft⟩
      cases fuelLeft with
      | zero =>
          simp [Block.run, invalid, Structured.invalid] at hLeft
      | succ fuelLeft =>
          cases hStmt : Stmt.run program fuelLeft stmt state with
          | error err =>
              simp [Block.run, hStmt] at hLeft
          | ok stmtOutcome =>
              cases hModeStmt : stmtOutcome.mode with
              | regular =>
                  simp [Block.run, hStmt, hModeStmt] at hLeft
                  rcases ih right stmtOutcome.state outcome ⟨fuelLeft, hLeft⟩
                      hMode with
                    ⟨fuelRest, hRestAppend⟩
                  let fuel := Nat.max fuelLeft fuelRest + 1
                  refine ⟨fuel, ?_⟩
                  have hStmt' :
                      Stmt.run program (Nat.max fuelLeft fuelRest) stmt state =
                        .ok stmtOutcome :=
                    Stmt.run_mono program (Nat.le_max_left _ _) hStmt
                  have hRestAppend' :
                      Block.run program (Nat.max fuelLeft fuelRest)
                          { stmts := rest ++ right } stmtOutcome.state =
                        .ok outcome :=
                    Block.run_mono program (Nat.le_max_right _ _) hRestAppend
                  simp [fuel, Block.run, hStmt', hModeStmt, hRestAppend']
              | brk =>
                  simp [Block.run, hStmt, hModeStmt] at hLeft
                  cases hLeft
                  exact ⟨fuelLeft + 1, by simp [Block.run, hStmt, hModeStmt]⟩
              | cont =>
                  simp [Block.run, hStmt, hModeStmt] at hLeft
                  cases hLeft
                  exact ⟨fuelLeft + 1, by simp [Block.run, hStmt, hModeStmt]⟩
              | leave =>
                  simp [Block.run, hStmt, hModeStmt] at hLeft
                  cases hLeft
                  exact ⟨fuelLeft + 1, by simp [Block.run, hStmt, hModeStmt]⟩
              | halt kind =>
                  simp [Block.run, hStmt, hModeStmt] at hLeft
                  cases hLeft
                  exact ⟨fuelLeft + 1, by simp [Block.run, hStmt, hModeStmt]⟩

end Block

namespace Program

theorem run_block {program : Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome} :
    program.run fuel initial = .ok outcome ↔
      Block.run program fuel program.body
        (Structured.Program.initialState initial) = .ok outcome := by
  rfl

end Program

end Expressions

namespace Locals

namespace Program

theorem procs_toExpressions_of_toExpressions? {program : Program}
    {lower : Expressions.Program}
    (hLower : program.toExpressions? = some lower) :
    Locals.ProcList.toExpressions? program.procs = some lower.procs := by
  unfold Program.toExpressions? at hLower
  cases hProcs : Locals.ProcList.toExpressions? program.procs with
  | none =>
      simp [hProcs] at hLower
  | some lowerProcs =>
      cases hBody : Locals.Block.compile Ctx.initial program.body with
      | none =>
          simp [hProcs, hBody] at hLower
      | some lowerBody =>
          simp [hProcs, hBody] at hLower
          cases hLower
          rfl

theorem body_toExpressions_of_toExpressions? {program : Program}
    {lower : Expressions.Program}
    (hLower : program.toExpressions? = some lower) :
    Locals.Block.compile Ctx.initial program.body = some lower.body := by
  unfold Program.toExpressions? at hLower
  cases hProcs : Locals.ProcList.toExpressions? program.procs with
  | none =>
      simp [hProcs] at hLower
  | some lowerProcs =>
      cases hBody : Locals.Block.compile Ctx.initial program.body with
      | none =>
          simp [hProcs, hBody] at hLower
      | some lowerBody =>
          simp [hProcs, hBody] at hLower
          cases hLower
          rfl

end Program

namespace Layout

theorem lookupDepthFrom_of_get?_nodup {layout : List Name} {name : Name}
    {idx depth : Nat}
    (hGet : layout[idx]? = some name)
    (hNoDup : layout.Nodup) :
    Locals.Layout.lookupDepthFrom name depth layout =
      some (depth + idx) := by
  revert idx depth
  induction layout with
  | nil =>
      intro idx depth hGet
      cases idx <;> simp at hGet
  | cons head tail ih =>
      intro idx depth hGet
      cases idx with
      | zero =>
          simp at hGet
          subst name
          simp [Locals.Layout.lookupDepthFrom]
      | succ idx =>
          have hTailGet : tail[idx]? = some name := by
            simpa using hGet
          have hTailNoDup : tail.Nodup :=
            (List.nodup_cons.mp hNoDup).2
          have hHeadNe : head ≠ name := by
            intro hEq
            have hNameMemTail : name ∈ tail :=
              List.mem_of_getElem? hTailGet
            have hHeadNotMemTail : head ∉ tail :=
              (List.nodup_cons.mp hNoDup).1
            exact hHeadNotMemTail (by simpa [hEq] using hNameMemTail)
          have hIH := ih hTailNoDup hTailGet (depth := depth + 1)
          simp [Locals.Layout.lookupDepthFrom, hHeadNe]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIH

theorem lookupDepth?_of_get?_nodup {layout : List Name} {name : Name}
    {idx : Nat}
    (hGet : layout[idx]? = some name)
    (hNoDup : layout.Nodup) :
    Locals.Layout.lookupDepth? name layout = some (idx + 1) := by
  have hDepth :=
    lookupDepthFrom_of_get?_nodup
      (layout := layout) (name := name) (idx := idx) (depth := 1)
      hGet hNoDup
  simpa [Locals.Layout.lookupDepth?, Nat.add_comm] using hDepth

end Layout

namespace ExprSeq

inductive VarSlotValuesAt (layout : List Name)
    (stack : EvmYul.Stack Word) :
    Nat → {results : Nat} → ExprSeq results → List Word → Prop where
  | nil {offset : Nat} :
      VarSlotValuesAt layout stack offset .nil []
  | cons_var {offset idx right : Nat} {name : Name}
      {value : Word} {tail : ExprSeq right} {values : List Word}
      (hName : layout[idx]? = some name)
      (hStack : stack[idx]? = some value)
      (hBound : offset + idx + 1 ≤ 16)
      (hTail :
        VarSlotValuesAt layout stack (offset + 1) tail values) :
      VarSlotValuesAt layout stack offset
        (ExprSeq.cons (left := 1) (right := right) (.var name) tail)
        (value :: values)

end ExprSeq

namespace Direct

@[simp] theorem RunState.withEVM_withEVM (state : RunState)
    (first second : EVMState) :
    (state.withEVM first).withEVM second = state.withEVM second := rfl

theorem code_run_append (left right : Structured.Code) (state : EVMState) :
    Structured.Code.run (left ++ right) state =
      (do
        let state' ← Structured.Code.run left state
        Structured.Code.run right state') := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [Structured.Code.run, ih]

theorem codeStmt_run_exists (lower : Expressions.Program)
    (code : Structured.Code) (state state' : RunState)
    (hRun : Structured.Code.runState code state = .ok state') :
    ∃ fuel, Expressions.Block.run lower fuel { stmts := codeStmt code } state =
      .ok (Outcome.regular state') := by
  refine ⟨2, ?_⟩
  simp [codeStmt, Expressions.Block.run, Expressions.Stmt.run, hRun]

theorem codeStmt_append_stmt_run_exists (lower : Expressions.Program)
    (code : Structured.Code) (stmt : Expressions.Stmt)
    (state mid : RunState) (outcome : Outcome)
    (hCode : Structured.Code.runState code state = .ok mid)
    (hStmt : ∃ fuel, Expressions.Stmt.run lower fuel stmt mid = .ok outcome) :
    ∃ fuel,
      Expressions.Block.run lower fuel { stmts := codeStmt code ++ [stmt] }
        state = .ok outcome := by
  exact
    Expressions.Block.run_append_regular_exists lower (codeStmt code) [stmt]
      state mid outcome
      (codeStmt_run_exists lower code state mid hCode)
      (Expressions.Block.run_single_exists lower hStmt)

namespace ProcList

theorem lookup?_toExpressions? {procs : List Proc}
    {lowerProcs : List Expressions.Proc} {name : Name} {proc : Proc}
    (hLower : Locals.ProcList.toExpressions? procs = some lowerProcs)
    (hLookup : lookup? name procs = some proc) :
    ∃ lowerProc,
      Expressions.ProcList.lookup? name lowerProcs = some lowerProc ∧
        proc.toExpressions? = some lowerProc := by
  induction procs generalizing lowerProcs with
  | nil =>
      simp [lookup?] at hLookup
  | cons head rest ih =>
      simp [Locals.ProcList.toExpressions?] at hLower
      cases hHead : head.toExpressions? with
      | none =>
          simp [hHead] at hLower
      | some lowerHead =>
          cases hRest : Locals.ProcList.toExpressions? rest with
          | none =>
              simp [hHead, hRest] at hLower
          | some lowerRest =>
              simp [hHead, hRest] at hLower
              cases hLower
              have hLowerHeadName : lowerHead.name = head.name := by
                unfold Locals.Proc.toExpressions? at hHead
                cases hBody :
                    Locals.Block.compileToPreserving
                      (Ctx.procEntryWithLayoutAndRetc head.entryLayout
                        head.retc) head.retc 0 head.body with
                | none =>
                    simp [hBody] at hHead
                | some body =>
                    simp [hBody] at hHead
                    cases hHead
                    rfl
              unfold lookup? at hLookup
              unfold Expressions.ProcList.lookup?
              by_cases hName : head.name = name
              · simp [hName] at hLookup
                cases hLookup
                simp [hLowerHeadName, hName]
                exact hHead
              · simp [hName] at hLookup
                simp [hLowerHeadName, hName]
                exact ih hRest hLookup

end ProcList

namespace Switch

theorem select_toExpressions? {ctx : Ctx}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {lowerCases : List (Word × Expressions.Block)}
    {lowerDefault : Option Expressions.Block} {value : Word}
    (hCases : Locals.CaseList.compile ctx cases = some lowerCases)
    (hDefault : Locals.Default.compile ctx defaultBody = some lowerDefault) :
    Expressions.Switch.select value lowerCases lowerDefault =
      match select value cases defaultBody with
      | none => none
      | some body => Locals.Block.compile ctx body := by
  induction cases generalizing lowerCases with
  | nil =>
      unfold Locals.CaseList.compile at hCases
      cases hCases
      cases defaultBody with
      | none =>
          unfold Locals.Default.compile at hDefault
          cases hDefault
          rfl
      | some body =>
          unfold Locals.Default.compile at hDefault
          cases hOpen : Locals.Block.compileOpen ctx body with
          | none =>
              simp [hOpen] at hDefault
          | some compiled =>
              rcases compiled with ⟨bodyCode, bodyCtx⟩
              cases hFinish : finishScoped ctx bodyCtx bodyCode with
              | none =>
                  simp [hOpen, hFinish] at hDefault
              | some lowerBody =>
                  simp [hOpen, hFinish] at hDefault
                  cases hDefault
                  simpa [select, Expressions.Switch.select,
                    Locals.Block.compile, hOpen, hFinish]
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      unfold Locals.CaseList.compile at hCases
      cases hHeadOpen : Locals.Block.compileOpen ctx headBody with
      | none =>
          simp [hHeadOpen] at hCases
      | some compiledHead =>
          rcases compiledHead with ⟨headCode, headCtx⟩
          cases hHeadFinish : finishScoped ctx headCtx headCode with
          | none =>
              simp [hHeadOpen, hHeadFinish] at hCases
          | some lowerHead =>
              cases hRest : Locals.CaseList.compile ctx rest with
              | none =>
                  simp [hHeadOpen, hHeadFinish, hRest] at hCases
              | some lowerRest =>
                  simp [hHeadOpen, hHeadFinish, hRest] at hCases
                  cases hCases
                  unfold select Expressions.Switch.select
                  by_cases hEq : headValue = value
                  · simp [hEq, Locals.Block.compile, hHeadOpen, hHeadFinish]
                  · simp [hEq, ih hRest]

end Switch

namespace Switch

theorem select_compile_some {ctx : Ctx}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {lowerCases : List (Word × Expressions.Block)}
    {lowerDefault : Option Expressions.Block} {value : Word} {body : Block}
    (hCases : Locals.CaseList.compile ctx cases = some lowerCases)
    (hDefault : Locals.Default.compile ctx defaultBody = some lowerDefault)
    (hSelected : select value cases defaultBody = some body) :
    ∃ lowerBody,
      Locals.Block.compile ctx body = some lowerBody ∧
        Expressions.Switch.select value lowerCases lowerDefault =
          some lowerBody := by
  induction cases generalizing lowerCases with
  | nil =>
      unfold Locals.CaseList.compile at hCases
      simp at hCases
      subst lowerCases
      cases defaultBody with
      | none =>
          simp [select] at hSelected
      | some defaultBody =>
          have hBodyEq : defaultBody = body := by
            simpa [select] using hSelected
          subst body
          unfold Locals.Default.compile at hDefault
          cases hOpen : Locals.Block.compileOpen ctx defaultBody with
          | none =>
              simp [hOpen] at hDefault
          | some compiled =>
              rcases compiled with ⟨bodyCode, bodyCtx⟩
              cases hFinish : finishScoped ctx bodyCtx bodyCode with
              | none =>
                  simp [hOpen, hFinish] at hDefault
              | some lowerBody =>
                  simp [hOpen, hFinish] at hDefault
                  subst lowerDefault
                  refine ⟨lowerBody, ?_, ?_⟩
                  · simp [Locals.Block.compile, hOpen, hFinish]
                  · simp [Expressions.Switch.select]
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      unfold Locals.CaseList.compile at hCases
      cases hHeadOpen : Locals.Block.compileOpen ctx headBody with
      | none =>
          simp [hHeadOpen] at hCases
      | some compiledHead =>
          rcases compiledHead with ⟨headCode, headCtx⟩
          cases hHeadFinish : finishScoped ctx headCtx headCode with
          | none =>
              simp [hHeadOpen, hHeadFinish] at hCases
          | some lowerHead =>
              cases hRest : Locals.CaseList.compile ctx rest with
              | none =>
                  simp [hHeadOpen, hHeadFinish, hRest] at hCases
              | some lowerRest =>
                  simp [hHeadOpen, hHeadFinish, hRest] at hCases
                  cases hCases
                  unfold select at hSelected
                  unfold Expressions.Switch.select
                  by_cases hEq : headValue = value
                  · have hBodyEq : headBody = body := by
                      simpa [hEq] using hSelected
                    subst body
                    refine ⟨lowerHead, ?_, ?_⟩
                    · simp [Locals.Block.compile, hHeadOpen, hHeadFinish]
                    · simp [hEq]
                  · simp [hEq] at hSelected ⊢
                    rcases ih hRest hSelected with
                      ⟨lowerBody, hCompileBody, hSelectBody⟩
                    exact ⟨lowerBody, hCompileBody, hSelectBody⟩

end Switch

theorem stackOp_dup?_step_eq_dup {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) (state : EVMState) :
    ∃ op, Locals.StackOp.dup? n = some op ∧
      Structured.BasicOp.step op state = EvmYul.dup n state := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> refine ⟨_, rfl, rfl⟩

theorem evm_dup_succ_get? {state : EVMState} {idx : Nat}
    {value : Word}
    (hStack : state.stack[idx]? = some value) :
    EvmYul.dup (idx + 1) state =
      .ok (state.replaceStackAndIncrPC (value :: state.stack)) := by
  have hLt : idx < state.stack.length := by
    rcases (List.getElem?_eq_some_iff.mp hStack) with ⟨hLt, _hValue⟩
    exact hLt
  have hLe : idx + 1 ≤ state.stack.length := by
    omega
  have hLen : (state.stack.take (idx + 1)).length = idx + 1 := by
    simp [List.length_take, Nat.min_eq_left hLe]
  have hLast? : (state.stack.take (idx + 1)).getLast? = some value := by
    rw [List.getLast?_take]
    simp [hStack]
  simp [EvmYul.dup, hLen, hLast?]

theorem Expr.runCode_var_layout_slot_value
    (ctx : Ctx) (state : EVMState) (name : Name)
    (layout : List Name) {idx offset : Nat} {value : Word}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hName : layout[idx]? = some name)
    (hStack : state.stack[offset + idx]? = some value)
    (hBound : offset + idx + 1 ≤ 16) :
    Expr.runCode ctx offset (.var name) state =
      .ok (state.replaceStackAndIncrPC (value :: state.stack)) := by
  let state' := state.replaceStackAndIncrPC (value :: state.stack)
  have hDepth :
      Locals.Layout.lookupDepth? name ctx.layout = some (idx + 1) := by
    simpa [hCtxLayout] using
      (Locals.Layout.lookupDepth?_of_get?_nodup hName hNoDup)
  have hOne : 1 ≤ offset + (idx + 1) := by
    omega
  have hBound' : offset + (idx + 1) ≤ 16 := by
    omega
  rcases
      stackOp_dup?_step_eq_dup
        (n := offset + (idx + 1)) hOne hBound' state with
    ⟨op, hDup, hStep⟩
  have hDupValue :
      EvmYul.dup (offset + (idx + 1)) state =
        .ok state' := by
    have hDupValue' :=
      evm_dup_succ_get? (state := state) (idx := offset + idx)
        hStack
    simpa [state', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hDupValue'
  simp [Expr.runCode, hDepth, hDup]
  rw [hStep, hDupValue]

theorem Expr.ExprSeq.runCode_of_varSlotValuesAt
    (ctx : Ctx) (baseState currentState : EVMState)
    (layout : List Name) (offset : Nat) (pushed : List Word)
    {results : Nat} {seq : ExprSeq results} {values : List Word}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hCurrentStack : currentState.stack = pushed ++ baseState.stack)
    (hPushedLen : pushed.length = offset)
    (hSlots :
      Locals.ExprSeq.VarSlotValuesAt layout baseState.stack offset seq
        values) :
    ∃ finalState : EVMState,
      Expr.ExprSeq.runCode ctx offset seq currentState =
        .ok finalState ∧
      finalState.stack = values.reverse ++ pushed ++ baseState.stack ∧
      finalState.toSharedState = currentState.toSharedState := by
  induction hSlots generalizing currentState pushed with
  | nil =>
      exact ⟨currentState, by simp [Expr.ExprSeq.runCode],
        by simp [hCurrentStack], rfl⟩
  | @cons_var offset idx right name value tail values hName hStack hBound
      hTail ih =>
      have hCurrentSlot :
          currentState.stack[offset + idx]? = some value := by
        rw [hCurrentStack]
        have hOffsetLen : offset = pushed.length := hPushedLen.symm
        subst offset
        rw [List.getElem?_append_right]
        · simp [hStack]
        · simp
      let afterHead : EVMState :=
        currentState.replaceStackAndIncrPC (value :: currentState.stack)
      have hRunHead :
          Expr.runCode ctx offset (.var name) currentState =
            .ok afterHead := by
        simpa [afterHead] using
          Expr.runCode_var_layout_slot_value ctx currentState name layout
            (idx := idx) (offset := offset) hCtxLayout hNoDup hName
            hCurrentSlot hBound
      have hAfterStack :
          afterHead.stack = (value :: pushed) ++ baseState.stack := by
        simp [afterHead, hCurrentStack,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterPrefixLen :
          (value :: pushed).length = offset + 1 := by
        simp [hPushedLen]
      rcases ih (currentState := afterHead) (pushed := value :: pushed)
          hAfterStack hAfterPrefixLen with
        ⟨finalState, hRunTail, hFinalStack, hFinalShared⟩
      exact
        ⟨finalState,
          by
            simp [Expr.ExprSeq.runCode, hRunHead, hRunTail],
          by
            simp [List.reverse_cons, List.append_assoc, hFinalStack],
          by
            simpa [afterHead, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] using hFinalShared⟩

mutual
  theorem Expr.runCode_eq_compileCode {results : Nat}
      (ctx : Ctx) (offset : Nat) (expr : Expr results)
      (code : Structured.Code) (state : EVMState)
      (hCompile : Expr.compileCode ctx offset expr = some code) :
      Expr.runCode ctx offset expr state =
        Structured.Code.run code state := by
    cases expr with
    | lit value =>
        simp [Expr.runCode, Locals.Expr.compileCode] at hCompile ⊢
        cases hCompile
        rfl
    | var name =>
        simp [Expr.runCode, Locals.Expr.compileCode] at hCompile ⊢
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth, invalid, Structured.invalid] at hCompile
        | some depth =>
            simp [hDepth] at hCompile ⊢
            cases hDup : StackOp.dup? (offset + depth) with
            | none =>
                simp [hDup, invalid, Structured.invalid] at hCompile
            | some op =>
                simp [hDup] at hCompile ⊢
                cases hCompile
                cases hStep : op.step state with
                | error err =>
                    simp [Structured.Code.run, Structured.BasicInstr.step, hStep]
                | ok state' =>
                    simp [Structured.Code.run, Structured.BasicInstr.step, hStep]
    | code code' =>
        simp [Expr.runCode, Locals.Expr.compileCode] at hCompile ⊢
        cases hCompile
        rfl
    | prim op args =>
        simp [Expr.runCode, Locals.Expr.compileCode]
        simp [Locals.Expr.compileCode] at hCompile
        cases hArgs : Locals.ExprSeq.compileCode ctx offset args with
        | none =>
            simp [hArgs] at hCompile
        | some argsCode =>
            simp [hArgs] at hCompile
            cases hCompile
            rw [code_run_append]
            simp [Expr.ExprSeq.runCode_eq_compileCode ctx offset args argsCode state
              hArgs]
            cases hRun : Structured.Code.run argsCode state with
            | error err =>
                simp [hRun]
            | ok state' =>
                simp [hRun, Structured.Code.run]
                cases hStep : op.step state' <;>
                  simp [Structured.BasicInstr.step, hStep]

  theorem Expr.ExprSeq.runCode_eq_compileCode {results : Nat}
      (ctx : Ctx) (offset : Nat) (exprs : ExprSeq results)
      (code : Structured.Code) (state : EVMState)
      (hCompile : ExprSeq.compileCode ctx offset exprs = some code) :
      Expr.ExprSeq.runCode ctx offset exprs state =
        Structured.Code.run code state := by
    cases exprs with
    | nil =>
        simp [Expr.ExprSeq.runCode, Locals.ExprSeq.compileCode] at hCompile ⊢
        cases hCompile
        rfl
    | @cons left right head tail =>
        simp [Expr.ExprSeq.runCode, Locals.ExprSeq.compileCode]
        simp [Locals.ExprSeq.compileCode] at hCompile
        cases hHead : Locals.Expr.compileCode ctx offset head with
        | none =>
            simp [hHead] at hCompile
        | some headCode =>
            cases hTail :
                Locals.ExprSeq.compileCode ctx (offset + left) tail with
            | none =>
                simp [hHead, hTail] at hCompile
            | some tailCode =>
                simp [hHead, hTail] at hCompile
                cases hCompile
                rw [code_run_append]
                simp [Expr.runCode_eq_compileCode ctx offset head headCode state
                    hHead]
                cases hRunHead : Structured.Code.run headCode state with
                | error err =>
                    simp [hRunHead]
                | ok state' =>
                    simp [hRunHead,
                      Expr.ExprSeq.runCode_eq_compileCode ctx (offset + left) tail
                        tailCode state' hTail]
end

namespace Expr

theorem runState_eq_compileCode {results : Nat}
    (ctx : Ctx) (expr : Expr results) (code : Structured.Code)
    (state : RunState)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code) :
    runState ctx expr state = Structured.Code.runState code state := by
  unfold runState Structured.Code.runState
  rw [runCode_eq_compileCode ctx 0 expr code state.evm hCompile]

theorem runCondition_eq_compileCode (ctx : Ctx) (cond : Expr 1)
    (code : Structured.Code) (state : RunState)
    (hCompile : Locals.Expr.compileCode ctx 0 cond = some code) :
    runCondition ctx cond state =
      Structured.Code.runConditionState code state := by
  unfold runCondition Structured.Code.runConditionState
  rw [runCode_eq_compileCode ctx 0 cond code state.evm hCompile]
  unfold Structured.Code.runCondition
  cases hRun : Structured.Code.run code state.evm <;> rfl

theorem runState_eq_compile {results : Nat}
    (ctx : Ctx) (expr : Expr results) (lower : Expressions.Expr results)
    (state : RunState)
    (hCompile : Locals.Expr.compile ctx expr = some lower) :
    runState ctx expr state = Expressions.Expr.runState lower state := by
  unfold Locals.Expr.compile at hCompile
  cases hCode : Locals.Expr.compileCode ctx 0 expr with
  | none =>
      simp [hCode] at hCompile
  | some code =>
      simp [hCode] at hCompile
      cases hCompile
      rw [runState_eq_compileCode ctx expr code state hCode]
      rfl

theorem runCondition_eq_compile (ctx : Ctx) (cond : Expr 1)
    (lower : Expressions.Expr 1) (state : RunState)
    (hCompile : Locals.Expr.compile ctx cond = some lower) :
    runCondition ctx cond state =
      Expressions.Expr.runConditionState lower state := by
  unfold Locals.Expr.compile at hCompile
  cases hCode : Locals.Expr.compileCode ctx 0 cond with
  | none =>
      simp [hCode] at hCompile
  | some code =>
      simp [hCode] at hCompile
      cases hCompile
      rw [runCondition_eq_compileCode ctx cond code state hCode]
      cases hRun : Structured.Code.run code state.evm <;>
        simp [Expressions.Expr.runConditionState, Expressions.Expr.runCondition,
          Expressions.Expr.run, Structured.Code.runConditionState,
          Structured.Code.runCondition, hRun]

end Expr

namespace Expr.ExprSeq

theorem runCode_eq_compileCode_zero {results : Nat}
    (ctx : Ctx) (exprs : ExprSeq results) (code : Structured.Code)
    (state : EVMState)
    (hCompile : Locals.ExprSeq.compileCode ctx 0 exprs = some code) :
    runCode ctx 0 exprs state = Structured.Code.run code state :=
  Direct.Expr.ExprSeq.runCode_eq_compileCode ctx 0 exprs code state hCompile

end Expr.ExprSeq

namespace Proc

theorem toExpressions?_body {proc : Proc} {lowerProc : Expressions.Proc}
    (hProc : proc.toExpressions? = some lowerProc) :
    Locals.Block.compileToPreserving
        (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
        proc.retc 0 proc.body =
        some lowerProc.body ∧
      lowerProc.name = proc.name ∧ lowerProc.argc = proc.argc ∧
        lowerProc.retc = proc.retc := by
  unfold Locals.Proc.toExpressions? at hProc
  cases hBody :
      Locals.Block.compileToPreserving
        (Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc)
        proc.retc 0 proc.body with
  | none =>
      simp [hBody] at hProc
  | some body =>
      simp [hBody] at hProc
      cases hProc
      simp

end Proc

theorem outcome_eq_regular_of_mode {outcome : Outcome}
    (hMode : outcome.mode = .regular) :
    outcome = Outcome.regular outcome.state := by
  cases outcome
  cases hMode
  rfl

set_option maxHeartbeats 1800000 in
mutual
  theorem Block.runOpen_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {ctx : Ctx} {fuel : Nat} {block : Block} {state : RunState}
        {outcome : Outcome} {runCtx compileCtx : Ctx}
        {code : List Expressions.Stmt},
        Locals.Block.compileOpen ctx block = some (code, compileCtx) →
        Block.runOpen program ctx fuel block state = .ok (outcome, runCtx) →
        (outcome.mode = .regular → runCtx = compileCtx) ∧
          ∃ lowerFuel,
            Expressions.Block.run lower lowerFuel { stmts := code } state =
              .ok outcome := by
    intro ctx fuel block state outcome runCtx compileCtx code hCompile hRun
    cases fuel with
    | zero =>
        simp [Block.runOpen, invalid, Structured.invalid] at hRun
    | succ fuel =>
        cases block with
        | mk stmts =>
            cases stmts with
            | nil =>
                simp [Locals.Block.compileOpen] at hCompile
                cases hCompile
                simp [Block.runOpen] at hRun
                cases hRun
                constructor
                · intro _h
                  simp_all
                · exact ⟨1, by simp_all [Expressions.Block.run]⟩
            | cons stmt rest =>
                simp [Locals.Block.compileOpen] at hCompile
                cases hStmtCompile : Locals.Stmt.compile ctx stmt with
                | none =>
                    simp [hStmtCompile] at hCompile
                | some stmtCompiled =>
                    rcases stmtCompiled with ⟨stmtCode, stmtCtx⟩
                    cases hRestCompile :
                        Locals.Block.compileOpen stmtCtx { stmts := rest } with
                    | none =>
                        simp [hStmtCompile, hRestCompile] at hCompile
                    | some restCompiled =>
                        rcases restCompiled with ⟨restCode, restCtx⟩
                        simp [hStmtCompile, hRestCompile] at hCompile
                        cases hCompile
                        subst code
                        subst compileCtx
                        unfold Block.runOpen at hRun
                        cases hStmtRun :
                            Stmt.run program ctx fuel stmt state with
                        | error err =>
                            simp [hStmtRun] at hRun
                        | ok stmtResult =>
                            rcases stmtResult with ⟨stmtOutcome, stmtRunCtx⟩
                            simp [hStmtRun] at hRun
                            have hStmtBridge :=
                              Stmt.run_toExpressions_exists program lower hLower
                                hStmtCompile hStmtRun
                            rcases hStmtBridge with
                              ⟨hStmtCtx, hStmtLower⟩
                            cases hMode : stmtOutcome.mode with
                            | regular =>
                                simp [hMode] at hRun
                                have hCtxEq : stmtRunCtx = stmtCtx :=
                                  hStmtCtx hMode
                                subst stmtRunCtx
                                cases hRestRun :
                                    Block.runOpen program stmtCtx fuel
                                      { stmts := rest } stmtOutcome.state with
                                | error err =>
                                    simp [hRestRun] at hRun
                                | ok restResult =>
                                    rcases restResult with
                                      ⟨restOutcome, restRunCtx⟩
                                    simp [hRestRun] at hRun
                                    cases hRun
                                    subst outcome
                                    subst runCtx
                                    have hRestBridge :=
                                      Block.runOpen_toExpressions_exists program
                                        lower hLower hRestCompile hRestRun
                                    rcases hRestBridge with
                                      ⟨hRestCtx, hRestLower⟩
                                    constructor
                                    · intro hRegular
                                      exact hRestCtx hRegular
                                    · exact
                                        let hStmtLowerRegular :
                                          ∃ lowerFuel,
                                              Expressions.Block.run lower
                                                  lowerFuel
                                                  { stmts := stmtCode } state =
                                                .ok
                                                  (Outcome.regular
                                                    stmtOutcome.state) := by
                                          rcases hStmtLower with ⟨lf, hLf⟩
                                          refine ⟨lf, ?_⟩
                                          rw [outcome_eq_regular_of_mode hMode]
                                            at hLf
                                          exact hLf
                                        Expressions.Block.run_append_regular_exists
                                          lower stmtCode restCode state
                                          stmtOutcome.state restOutcome
                                          hStmtLowerRegular hRestLower
                            | brk =>
                                simp [hMode] at hRun
                                cases hRun
                                subst outcome
                                subst runCtx
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.run_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          hStmtLower (by simp [hMode])
                            | cont =>
                                simp [hMode] at hRun
                                cases hRun
                                subst outcome
                                subst runCtx
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.run_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          hStmtLower (by simp [hMode])
                            | leave =>
                                simp [hMode] at hRun
                                cases hRun
                                subst outcome
                                subst runCtx
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.run_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          hStmtLower (by simp [hMode])
                            | halt kind =>
                                simp [hMode] at hRun
                                cases hRun
                                subst outcome
                                subst runCtx
                                constructor
                                · intro hRegular
                                  simp [hMode] at hRegular
                                · exact
                                    by
                                      simpa using
                                        Expressions.Block.run_append_nonregular_exists
                                          lower stmtCode restCode state stmtOutcome
                                          hStmtLower (by simp [hMode])
  termination_by
    _ctx fuel block _state _outcome _runCtx _compileCtx _code _hCompile
      _hRun => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Block.runScoped_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {ctx : Ctx} {fuel : Nat} {block : Block} {state : RunState}
        {outcome : Outcome} {lowerBlock : Expressions.Block},
        Locals.Block.compile ctx block = some lowerBlock →
        Block.runScoped program ctx block fuel state = .ok outcome →
        ∃ lowerFuel,
          Expressions.Block.run lower lowerFuel lowerBlock state =
            .ok outcome := by
    intro ctx fuel block state outcome lowerBlock hCompile hRun
    unfold Locals.Block.compile at hCompile
    cases hOpen : Locals.Block.compileOpen ctx block with
    | none =>
        simp [hOpen] at hCompile
    | some compiled =>
        rcases compiled with ⟨code, finalCtx⟩
        cases hFinish : finishScoped ctx finalCtx code with
        | none =>
            simp [hOpen, hFinish] at hCompile
        | some finished =>
            simp [hOpen, hFinish] at hCompile
            cases hCompile
            unfold Block.runScoped at hRun
            cases hOpenRun :
                Block.runOpen program ctx fuel block state with
            | error err =>
                simp [hOpenRun] at hRun
            | ok openResult =>
                rcases openResult with ⟨openOutcome, runCtx⟩
                simp [hOpenRun] at hRun
                have hOpenBridge :=
                  Block.runOpen_toExpressions_exists program lower hLower
                    hOpen hOpenRun
                rcases hOpenBridge with ⟨hRunCtx, hOpenLower⟩
                cases hMode : openOutcome.mode with
                | regular =>
                    simp [hMode] at hRun
                    have hCtxEq : runCtx = finalCtx := hRunCtx hMode
                    subst runCtx
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        cases hCleanupRun :
                            Ctx.runCleanupTo finalCtx ctx.layout.length
                              openOutcome.state with
                        | error err =>
                            simp [hCleanupRun] at hRun
                        | ok cleaned =>
                            simp [hCleanupRun] at hRun
                            cases hRun
                            have hCleanupCode :
                                Structured.Code.runState cleanup
                                  openOutcome.state = .ok cleaned := by
                              unfold Ctx.runCleanupTo at hCleanupRun
                              simp [hCleanup] at hCleanupRun
                              exact hCleanupRun
                            exact
                              let hOpenLowerRegular :
                                  ∃ lowerFuel,
                                    Expressions.Block.run lower lowerFuel
                                        { stmts := code } state =
                                      .ok
                                        (Outcome.regular openOutcome.state) := by
                                    rcases hOpenLower with ⟨lf, hLf⟩
                                    refine ⟨lf, ?_⟩
                                    rw [outcome_eq_regular_of_mode hMode] at hLf
                                    exact hLf
                              Expressions.Block.run_append_regular_exists lower
                                code (codeStmt cleanup) state openOutcome.state
                                (Outcome.regular cleaned) hOpenLowerRegular
                                (codeStmt_run_exists lower cleanup
                                  openOutcome.state cleaned hCleanupCode)
                | brk =>
                    simp [hMode] at hRun
                    cases hRun
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.run_append_nonregular_exists lower
                                code (codeStmt cleanup) state outcome hOpenLower
                                (by simp [hMode])
                | cont =>
                    simp [hMode] at hRun
                    cases hRun
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.run_append_nonregular_exists lower
                                code (codeStmt cleanup) state outcome hOpenLower
                                (by simp [hMode])
                | leave =>
                    simp [hMode] at hRun
                    cases hRun
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.run_append_nonregular_exists lower
                                code (codeStmt cleanup) state outcome hOpenLower
                                (by simp [hMode])
                | halt kind =>
                    simp [hMode] at hRun
                    cases hRun
                    unfold finishScoped at hFinish
                    cases hCleanup : finalCtx.cleanupTo? ctx.layout.length with
                    | none =>
                        simp [finishTo, hCleanup] at hFinish
                    | some cleanup =>
                        simp [finishTo, hCleanup] at hFinish
                        cases hFinish
                        exact
                          by
                            simpa using
                              Expressions.Block.run_append_nonregular_exists lower
                                code (codeStmt cleanup) state outcome hOpenLower
                                (by simp [hMode])
  termination_by
    _ctx fuel block _state _outcome _lowerBlock _hCompile _hRun =>
      (fuel, 1, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))

  theorem Stmt.runForLoop_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {loopCtx postBase bodyBase : Ctx} {fuel : Nat}
        {cond : Expr 1} {lowerCond : Expressions.Expr 1}
        {post body : Block} {lowerPost lowerBody : Expressions.Block}
        {state : RunState} {outcome : Outcome},
        Locals.Expr.compile loopCtx cond = some lowerCond →
        Locals.Block.compile postBase post = some lowerPost →
        Locals.Block.compile bodyBase body = some lowerBody →
        Stmt.runForLoop program loopCtx cond postBase post bodyBase body fuel
          state = .ok outcome →
        ∃ lowerFuel,
          Expressions.Stmt.runForLoop lower lowerFuel lowerCond lowerPost
            lowerBody state = .ok outcome := by
    intro loopCtx postBase bodyBase fuel cond lowerCond post body lowerPost
      lowerBody state outcome hCond hPost hBody hRun
    cases fuel with
    | zero =>
        simp [Stmt.runForLoop, invalid, Structured.invalid] at hRun
    | succ fuel =>
        unfold Stmt.runForLoop at hRun
        rw [Expr.runCondition_eq_compile loopCtx cond lowerCond state hCond]
          at hRun
        cases hCondRun :
            Expressions.Expr.runConditionState lowerCond state with
        | error err =>
            simp [hCondRun] at hRun
        | ok condResult =>
            rcases condResult with ⟨stateAfterCond, condTrue⟩
            cases condTrue with
            | false =>
                simp [hCondRun] at hRun
                cases hRun
                exact ⟨1, by simp [Expressions.Stmt.runForLoop, hCondRun]⟩
            | true =>
                simp [hCondRun] at hRun
                cases hBodyRun :
                    Block.runScoped program bodyBase body fuel stateAfterCond with
                | error err =>
                    simp [hBodyRun] at hRun
                | ok bodyOutcome =>
                    simp [hBodyRun] at hRun
                    rcases
                      Block.runScoped_toExpressions_exists program lower hLower
                        hBody hBodyRun with
                    ⟨bodyFuel, hBodyLower⟩
                    cases hBodyMode : bodyOutcome.mode with
                    | brk =>
                        simp [hBodyMode] at hRun
                        cases hRun
                        refine ⟨Nat.max bodyFuel fuel + 1, ?_⟩
                        have hBodyLower' :
                            Expressions.Block.run lower
                                (Nat.max bodyFuel fuel) lowerBody
                                stateAfterCond = .ok bodyOutcome :=
                          Expressions.Block.run_mono lower
                            (Nat.le_max_left _ _) hBodyLower
                        simp [Expressions.Stmt.runForLoop, hCondRun,
                          hBodyLower', hBodyMode]
                    | regular =>
                        simp [hBodyMode] at hRun
                        cases hPostRun :
                            Block.runScoped program postBase post fuel
                              bodyOutcome.state with
                        | error err =>
                            simp [hPostRun] at hRun
                        | ok postOutcome =>
                            simp [hPostRun] at hRun
                            rcases
                              Block.runScoped_toExpressions_exists program lower
                                hLower hPost hPostRun with
                            ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPostMode] at hRun
                                rcases
                                  Stmt.runForLoop_toExpressions_exists program
                                    lower hLower hCond hPost hBody hRun with
                                ⟨loopFuel, hLoopLower⟩
                                refine
                                  ⟨Nat.max bodyFuel (Nat.max postFuel loopFuel) + 1,
                                    ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerBody stateAfterCond =
                                      .ok bodyOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerPost bodyOutcome.state =
                                      .ok postOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_trans (Nat.le_max_left _ _)
                                      (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Expressions.Stmt.runForLoop lower
                                        (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerCond lowerPost lowerBody
                                        postOutcome.state = .ok outcome :=
                                  Expressions.Stmt.runForLoop_mono lower
                                    (Nat.le_trans (Nat.le_max_right _ _)
                                      (Nat.le_max_right _ _)) hLoopLower
                                simp [Expressions.Stmt.runForLoop, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | cont =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | leave =>
                                simp [hPostMode] at hRun
                                cases hRun
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerBody
                                        stateAfterCond = .ok bodyOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerPost
                                        bodyOutcome.state = .ok outcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoop, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                            | halt kind =>
                                simp [hPostMode] at hRun
                                cases hRun
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerBody
                                        stateAfterCond = .ok bodyOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerPost
                                        bodyOutcome.state = .ok outcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoop, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                    | cont =>
                        simp [hBodyMode] at hRun
                        cases hPostRun :
                            Block.runScoped program postBase post fuel
                              bodyOutcome.state with
                        | error err =>
                            simp [hPostRun] at hRun
                        | ok postOutcome =>
                            simp [hPostRun] at hRun
                            rcases
                              Block.runScoped_toExpressions_exists program lower
                                hLower hPost hPostRun with
                            ⟨postFuel, hPostLower⟩
                            cases hPostMode : postOutcome.mode with
                            | regular =>
                                simp [hPostMode] at hRun
                                rcases
                                  Stmt.runForLoop_toExpressions_exists program
                                    lower hLower hCond hPost hBody hRun with
                                ⟨loopFuel, hLoopLower⟩
                                refine
                                  ⟨Nat.max bodyFuel (Nat.max postFuel loopFuel) + 1,
                                    ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerBody stateAfterCond =
                                      .ok bodyOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerPost bodyOutcome.state =
                                      .ok postOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_trans (Nat.le_max_left _ _)
                                      (Nat.le_max_right _ _)) hPostLower
                                have hLoopLower' :
                                    Expressions.Stmt.runForLoop lower
                                        (Nat.max bodyFuel
                                          (Nat.max postFuel loopFuel))
                                        lowerCond lowerPost lowerBody
                                        postOutcome.state = .ok outcome :=
                                  Expressions.Stmt.runForLoop_mono lower
                                    (Nat.le_trans (Nat.le_max_right _ _)
                                      (Nat.le_max_right _ _)) hLoopLower
                                simp [Expressions.Stmt.runForLoop, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode, hLoopLower']
                            | brk =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | cont =>
                                simp [hPostMode, invalid, Structured.invalid]
                                  at hRun
                            | leave =>
                                simp [hPostMode] at hRun
                                cases hRun
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerBody
                                        stateAfterCond = .ok bodyOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerPost
                                        bodyOutcome.state = .ok outcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoop, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                            | halt kind =>
                                simp [hPostMode] at hRun
                                cases hRun
                                refine ⟨Nat.max bodyFuel postFuel + 1, ?_⟩
                                have hBodyLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerBody
                                        stateAfterCond = .ok bodyOutcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_left _ _) hBodyLower
                                have hPostLower' :
                                    Expressions.Block.run lower
                                        (Nat.max bodyFuel postFuel) lowerPost
                                        bodyOutcome.state = .ok outcome :=
                                  Expressions.Block.run_mono lower
                                    (Nat.le_max_right _ _) hPostLower
                                simp [Expressions.Stmt.runForLoop, hCondRun,
                                  hBodyLower', hBodyMode, hPostLower',
                                  hPostMode]
                    | leave =>
                        simp [hBodyMode] at hRun
                        cases hRun
                        refine ⟨Nat.max bodyFuel fuel + 1, ?_⟩
                        have hBodyLower' :
                            Expressions.Block.run lower (Nat.max bodyFuel fuel)
                                lowerBody stateAfterCond = .ok outcome :=
                          Expressions.Block.run_mono lower
                            (Nat.le_max_left _ _) hBodyLower
                        simp [Expressions.Stmt.runForLoop, hCondRun,
                          hBodyLower', hBodyMode]
                    | halt kind =>
                        simp [hBodyMode] at hRun
                        cases hRun
                        refine ⟨Nat.max bodyFuel fuel + 1, ?_⟩
                        have hBodyLower' :
                            Expressions.Block.run lower (Nat.max bodyFuel fuel)
                                lowerBody stateAfterCond = .ok outcome :=
                          Expressions.Block.run_mono lower
                            (Nat.le_max_left _ _) hBodyLower
                        simp [Expressions.Stmt.runForLoop, hCondRun,
                          hBodyLower', hBodyMode]
  termination_by
    _loopCtx _postBase _bodyBase fuel _cond _lowerCond _post _body
      _lowerPost _lowerBody _state _outcome _hCond _hPost _hBody _hRun =>
      (fuel, 2, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem Stmt.run_toExpressions_exists
      (program : Program) (lower : Expressions.Program)
      (hLower : program.toExpressions? = some lower) :
      ∀ {ctx : Ctx} {fuel : Nat} {stmt : Stmt} {state : RunState}
        {outcome : Outcome} {runCtx compileCtx : Ctx}
        {code : List Expressions.Stmt},
        Locals.Stmt.compile ctx stmt = some (code, compileCtx) →
        Stmt.run program ctx fuel stmt state = .ok (outcome, runCtx) →
        (outcome.mode = .regular → runCtx = compileCtx) ∧
          ∃ lowerFuel,
            Expressions.Block.run lower lowerFuel { stmts := code } state =
              .ok outcome := by
    intro ctx fuel stmt state outcome runCtx compileCtx code hCompile hRun
    cases stmt with
    | expr expr =>
        unfold Locals.Stmt.compile at hCompile
        cases hCode : Locals.Expr.compileCode ctx 0 expr with
        | none =>
            simp [hCode] at hCompile
        | some exprCode =>
            simp [hCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.run at hRun
            rw [Expr.runState_eq_compileCode ctx expr exprCode state hCode]
              at hRun
            cases hCodeRun : Structured.Code.runState exprCode state with
            | error err =>
                simp [hCodeRun] at hRun
            | ok state' =>
                simp [hCodeRun] at hRun
                cases hRun
                subst outcome
                subst runCtx
                constructor
                · intro _h
                  simp_all
                · simpa using
                    codeStmt_run_exists lower exprCode state state' hCodeRun
    | exprs exprs =>
        unfold Locals.Stmt.compile at hCompile
        cases hCode : Locals.ExprSeq.compileCode ctx 0 exprs with
        | none =>
            simp [hCode] at hCompile
        | some exprsCode =>
            simp [hCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.run at hRun
            rw [Expr.ExprSeq.runCode_eq_compileCode_zero ctx exprs exprsCode
                state.evm hCode] at hRun
            cases hCodeRun : Structured.Code.run exprsCode state.evm with
            | error err =>
                simp [hCodeRun] at hRun
            | ok evmAfterExprs =>
                simp [hCodeRun] at hRun
                cases hRun
                subst outcome
                subst runCtx
                have hCodeRunState :
                    Structured.Code.runState exprsCode state =
                      .ok (state.withEVM evmAfterExprs) := by
                  unfold Structured.Code.runState
                  simp [hCodeRun]
                constructor
                · intro _h
                  simp_all
                · simpa using
                    codeStmt_run_exists lower exprsCode state
                      (state.withEVM evmAfterExprs) hCodeRunState
    | let_ name value =>
        unfold Locals.Stmt.compile at hCompile
        cases hCode : Locals.Expr.compileCode ctx 0 value with
        | none =>
            simp [hCode] at hCompile
        | some valueCode =>
            simp [hCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.run at hRun
            rw [Expr.runState_eq_compileCode ctx value valueCode state hCode]
              at hRun
            cases hCodeRun : Structured.Code.runState valueCode state with
            | error err =>
                simp [hCodeRun] at hRun
            | ok state' =>
                simp [hCodeRun] at hRun
                cases hRun
                subst outcome
                subst runCtx
                constructor
                · intro _h
                  simp_all
                · simpa using
                    codeStmt_run_exists lower valueCode state state' hCodeRun
    | assign name value =>
        unfold Locals.Stmt.compile at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hValueCode : Locals.Expr.compileCode ctx 0 value with
            | none =>
                simp [hDepth, hValueCode] at hCompile
            | some valueCode =>
                cases hSwap : StackOp.swap? depth with
                | none =>
                    simp [hDepth, hValueCode, hSwap] at hCompile
                | some swapOp =>
                    simp [hDepth, hValueCode, hSwap] at hCompile
                    cases hCompile
                    subst code
                    subst compileCtx
                    unfold Stmt.run at hRun
                    rw [Expr.runCode_eq_compileCode ctx 0 value valueCode
                        state.evm hValueCode] at hRun
                    cases hValueRun : Structured.Code.run valueCode state.evm with
                    | error err =>
                        simp [hDepth, hSwap, hValueRun] at hRun
                    | ok evmAfterValue =>
                        cases hSwapRun : swapOp.step evmAfterValue with
                        | error err =>
                            simp [hDepth, hSwap, hValueRun, hSwapRun] at hRun
                        | ok evmAfterSwap =>
                            cases hPopRun :
                                Structured.BasicOp.pop.step evmAfterSwap with
                            | error err =>
                                simp [hDepth, hSwap, hValueRun, hSwapRun,
                                  hPopRun] at hRun
                            | ok evmAfterPop =>
                                simp [hDepth, hSwap, hValueRun, hSwapRun,
                                  hPopRun] at hRun
                                cases hRun
                                subst outcome
                                subst runCtx
                                have hCodeRun :
                                    Structured.Code.runState
                                        (valueCode ++
                                          [Structured.BasicInstr.op swapOp,
                                            Structured.BasicInstr.op .pop])
                                        state =
                                      .ok (state.withEVM evmAfterPop) := by
                                  unfold Structured.Code.runState
                                  rw [code_run_append]
                                  simp [hValueRun, Structured.Code.run,
                                    Structured.BasicInstr.step, hSwapRun,
                                    hPopRun]
                                constructor
                                · intro _h
                                  simp_all
                                · simpa using
                                    codeStmt_run_exists lower
                                      (valueCode ++
                                        [Structured.BasicInstr.op swapOp,
                                          Structured.BasicInstr.op .pop])
                                      state (state.withEVM evmAfterPop) hCodeRun
    | assignTop name =>
        unfold Locals.Stmt.compile at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hSwap : StackOp.swap? depth with
            | none =>
                simp [hDepth, hSwap] at hCompile
            | some swapOp =>
                simp [hDepth, hSwap] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.run at hRun
                cases hSwapRun : swapOp.step state.evm with
                | error err =>
                    simp [hDepth, hSwap, hSwapRun] at hRun
                | ok evmAfterSwap =>
                    cases hPopRun : Structured.BasicOp.pop.step evmAfterSwap with
                    | error err =>
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                    | ok evmAfterPop =>
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                        cases hRun
                        subst outcome
                        subst runCtx
                        have hCodeRun :
                            Structured.Code.runState
                                [Structured.BasicInstr.op swapOp,
                                  Structured.BasicInstr.op .pop] state =
                              .ok (state.withEVM evmAfterPop) := by
                          unfold Structured.Code.runState
                          simp [Structured.Code.run, Structured.BasicInstr.step,
                            hSwapRun, hPopRun]
                        constructor
                        · intro _h
                          simp_all
                        · simpa using
                            codeStmt_run_exists lower
                              [Structured.BasicInstr.op swapOp,
                                Structured.BasicInstr.op .pop]
                              state (state.withEVM evmAfterPop) hCodeRun
    | assignTopWithOffset offset name =>
        unfold Locals.Stmt.compile at hCompile
        cases hDepth : Layout.lookupDepth? name ctx.layout with
        | none =>
            simp [hDepth] at hCompile
        | some depth =>
            cases hSwap : StackOp.swap? (offset + depth) with
            | none =>
                simp [hDepth, hSwap] at hCompile
            | some swapOp =>
                simp [hDepth, hSwap] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.run at hRun
                cases hSwapRun : swapOp.step state.evm with
                | error err =>
                    simp [hDepth, hSwap, hSwapRun] at hRun
                | ok evmAfterSwap =>
                    cases hPopRun : Structured.BasicOp.pop.step evmAfterSwap with
                    | error err =>
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                    | ok evmAfterPop =>
                        simp [hDepth, hSwap, hSwapRun, hPopRun] at hRun
                        cases hRun
                        subst outcome
                        subst runCtx
                        have hCodeRun :
                            Structured.Code.runState
                                [Structured.BasicInstr.op swapOp,
                                  Structured.BasicInstr.op .pop] state =
                              .ok (state.withEVM evmAfterPop) := by
                          unfold Structured.Code.runState
                          simp [Structured.Code.run, Structured.BasicInstr.step,
                            hSwapRun, hPopRun]
                        constructor
                        · intro _h
                          simp_all
                        · simpa using
                            codeStmt_run_exists lower
                              [Structured.BasicInstr.op swapOp,
                                Structured.BasicInstr.op .pop]
                              state (state.withEVM evmAfterPop) hCodeRun
    | promoteName name =>
        unfold Locals.Stmt.compile at hCompile
        cases hPromote : ctx.promoteNameStackOnly? name with
        | none =>
            simp [hPromote] at hCompile
        | some promoteResult =>
            rcases promoteResult with ⟨promoteCode, promoted⟩
            simp [hPromote] at hCompile
            rcases hCompile with ⟨rfl, rfl⟩
            rcases CompilerFacts.Ctx.promoteNameStackOnly?_eq_some hPromote with
              ⟨depth, idx, hDepth, hIdx, hBound, hCode, hPromoted⟩
            have hDepthBound : depth ≤ 17 := by omega
            have hCodeDepth :
                Ctx.swapRestoreUpTo? (depth - 1) = some promoteCode := by
              rw [← hIdx]
              exact hCode
            have hPromotedDepth :
                Layout.promoteAt (depth - 1) ctx.layout = promoted := by
              rw [← hIdx]
              exact hPromoted.symm
            unfold Stmt.run at hRun
            simp [Stmt.run, hDepth, hDepthBound, hCodeDepth, hPromotedDepth]
              at hRun
            cases hRunCode :
                Structured.Code.run promoteCode state.evm with
            | error err =>
                simp [hRunCode] at hRun
            | ok evmAfterPromote =>
                simp [hRunCode] at hRun
                cases hRun
                subst outcome
                subst runCtx
                have hCodeRunState :
                    Structured.Code.runState promoteCode state =
                      .ok (state.withEVM evmAfterPromote) := by
                  unfold Structured.Code.runState
                  simp [hRunCode]
                constructor
                · intro _h
                  rfl
                · simpa using
                    codeStmt_run_exists lower promoteCode state
                      (state.withEVM evmAfterPromote) hCodeRunState
    | cleanupTo targetLayout =>
        unfold Locals.Stmt.compile at hCompile
        by_cases hTarget :
            targetLayout =
              ctx.layout.drop (ctx.layout.length - targetLayout.length)
        · rw [if_pos hTarget] at hCompile
          cases hCleanup : ctx.cleanupTo? targetLayout.length with
          | none =>
              simp [hCleanup] at hCompile
          | some cleanup =>
              simp [hCleanup] at hCompile
              cases hCompile
              subst code
              subst compileCtx
              cases fuel
              all_goals
                unfold Stmt.run at hRun
                change
                  (if targetLayout =
                      ctx.layout.drop
                        (ctx.layout.length - targetLayout.length) then
                    (do
                      let stateAfterCleanup ←
                        Ctx.runCleanupTo ctx targetLayout.length state
                      .ok (Outcome.regular stateAfterCleanup,
                        ctx.withLayout targetLayout))
                  else invalid) = .ok (outcome, runCtx) at hRun
                rw [if_pos hTarget] at hRun
                cases hCleanupRun :
                    Ctx.runCleanupTo ctx targetLayout.length state with
                | error err =>
                    simp [hCleanupRun] at hRun
                | ok cleaned =>
                    simp [hCleanupRun] at hRun
                    cases hRun
                    subst outcome
                    subst runCtx
                    have hCleanupCode :
                        Structured.Code.runState cleanup state = .ok cleaned := by
                      unfold Ctx.runCleanupTo at hCleanupRun
                      simp [hCleanup] at hCleanupRun
                      exact hCleanupRun
                    constructor
                    · intro _hRegular
                      rfl
                    · simpa using
                        codeStmt_run_exists lower cleanup state cleaned
                          hCleanupCode
        · rw [if_neg hTarget] at hCompile
          simp at hCompile
    | block body =>
        unfold Locals.Stmt.compile at hCompile
        cases hOpen : Locals.Block.compileOpen ctx body with
        | none =>
            simp [hOpen] at hCompile
        | some compiled =>
            rcases compiled with ⟨bodyCode, bodyCtx⟩
            cases hFinish : finishScoped ctx bodyCtx bodyCode with
            | none =>
                simp [hOpen, hFinish] at hCompile
            | some lowerBody =>
                simp [hOpen, hFinish] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.run at hRun
                cases hBodyRun :
                    Block.runScoped program ctx body fuel state with
                | error err =>
                    simp [hBodyRun] at hRun
                | ok bodyOutcome =>
                    simp [hBodyRun] at hRun
                    cases hRun
                    subst outcome
                    subst runCtx
                    have hBodyCompile :
                        Locals.Block.compile ctx body = some lowerBody := by
                      simp [Locals.Block.compile, hOpen, hFinish]
                    constructor
                    · intro _h
                      simp_all
                    · rcases
                        Block.runScoped_toExpressions_exists program lower
                          hLower hBodyCompile hBodyRun with
                      ⟨lf, hLf⟩
                      refine ⟨lf, ?_⟩
                      cases lowerBody
                      simpa using hLf
    | if_ cond body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            cases hCond : Locals.Expr.compile ctx cond with
            | none =>
                simp [hCond] at hCompile
            | some lowerCond =>
                cases hOpen : Locals.Block.compileOpen ctx body with
                | none =>
                    simp [hCond, hOpen] at hCompile
                | some compiledBody =>
                    rcases compiledBody with ⟨bodyCode, bodyCtx⟩
                    cases hFinish :
                        finishScoped ctx bodyCtx bodyCode with
                    | none =>
                        simp [hCond, hOpen, hFinish] at hCompile
                    | some lowerBody =>
                        simp [hCond, hOpen, hFinish] at hCompile
                        cases hCompile
                        subst code
                        subst compileCtx
                        unfold Stmt.run at hRun
                        rw [Expr.runCondition_eq_compile ctx cond lowerCond
                            state hCond] at hRun
                        cases hCondRun :
                            Expressions.Expr.runConditionState lowerCond state with
                        | error err =>
                            simp [hCondRun] at hRun
                        | ok condResult =>
                            rcases condResult with ⟨stateAfterCond, condTrue⟩
                            cases condTrue with
                            | false =>
                                simp [hCondRun] at hRun
                                cases hRun
                                subst outcome
                                subst runCtx
                                constructor
                                · intro _h
                                  simp_all
                                · refine
                                    Expressions.Block.run_single_exists lower
                                      ⟨1, ?_⟩
                                  simp [Expressions.Stmt.run, hCondRun]
                            | true =>
                                simp [hCondRun] at hRun
                                cases hBodyRun :
                                    Block.runScoped program ctx body fuel
                                      stateAfterCond with
                                | error err =>
                                    simp [hBodyRun] at hRun
                                | ok bodyOutcome =>
                                    simp [hBodyRun] at hRun
                                    cases hRun
                                    subst outcome
                                    subst runCtx
                                    have hBodyCompile :
                                        Locals.Block.compile ctx body =
                                          some lowerBody := by
                                      simp [Locals.Block.compile, hOpen, hFinish]
                                    rcases
                                      Block.runScoped_toExpressions_exists program
                                        lower hLower hBodyCompile hBodyRun with
                                    ⟨bodyFuel, hBodyLower⟩
                                    constructor
                                    · intro _h
                                      simp_all
                                    · refine
                                        Expressions.Block.run_single_exists lower
                                          ⟨bodyFuel + 1, ?_⟩
                                      have hBodyLower' :
                                          Expressions.Block.run lower bodyFuel
                                              lowerBody stateAfterCond =
                                            .ok bodyOutcome := hBodyLower
                                      simp [Expressions.Stmt.run, hCondRun,
                                        hBodyLower']
    | switch scrutinee cases defaultBody =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            cases hScrutinee : Locals.Expr.compile ctx scrutinee with
            | none =>
                simp [hScrutinee] at hCompile
            | some lowerScrutinee =>
                cases hCases :
                    Locals.CaseList.compile ctx cases with
                | none =>
                    simp [hScrutinee, hCases] at hCompile
                | some lowerCases =>
                    cases hDefault :
                        Locals.Default.compile ctx defaultBody with
                    | none =>
                        simp [hScrutinee, hCases, hDefault] at hCompile
                    | some lowerDefault =>
                        simp [hScrutinee, hCases, hDefault] at hCompile
                        cases hCompile
                        subst code
                        subst compileCtx
                        unfold Stmt.run at hRun
                        simp [Stmt.run] at hRun
                        rw [Expr.runState_eq_compile ctx scrutinee
                            lowerScrutinee state hScrutinee] at hRun
                        unfold Expressions.Expr.runState at hRun
                        cases hScrutineeRun :
                            Expressions.Expr.run lowerScrutinee state.evm with
                        | error err =>
                            simp [hScrutineeRun] at hRun
                        | ok evmAfterScrutinee =>
                            cases hPop : evmAfterScrutinee.stack.pop with
                            | none =>
                                simp [hScrutineeRun, hPop] at hRun
                            | some popped =>
                                rcases popped with ⟨stack, value⟩
                                let stateAfterPop :=
                                  state.withEVM
                                    { evmAfterScrutinee with stack := stack }
                                have hSelectLower :=
                                  Switch.select_toExpressions?
                                    (ctx := ctx) (cases := cases)
                                    (defaultBody := defaultBody) (value := value)
                                    hCases hDefault
                                cases hSelected :
                                    Switch.select value cases defaultBody with
                                | none =>
                                    simp [hScrutineeRun, hPop, hSelected] at hRun
                                    cases hRun
                                    subst outcome
                                    subst runCtx
                                    constructor
                                    · intro _h
                                      simp_all
                                    · refine
                                        Expressions.Block.run_single_exists lower
                                          ⟨1, ?_⟩
                                      simp [Expressions.Stmt.run,
                                        hScrutineeRun, hPop, hSelectLower,
                                        hSelected]
                                | some selected =>
                                    simp [hScrutineeRun, hPop, hSelected] at hRun
                                    rcases
                                      Switch.select_compile_some
                                        (ctx := ctx) (cases := cases)
                                        (defaultBody := defaultBody)
                                        (lowerCases := lowerCases)
                                        (lowerDefault := lowerDefault)
                                        (value := value) (body := selected)
                                        hCases hDefault hSelected with
                                    ⟨lowerSelected, hSelectedCompile,
                                      hSelectLowerSome⟩
                                    cases hBodyRun :
                                        Block.runScoped program ctx selected
                                          fuel stateAfterPop with
                                    | error err =>
                                        simp [stateAfterPop, hBodyRun] at hRun
                                    | ok bodyOutcome =>
                                        simp [stateAfterPop, hBodyRun] at hRun
                                        cases hRun
                                        subst outcome
                                        subst runCtx
                                        rcases
                                          Block.runScoped_toExpressions_exists
                                            program lower hLower
                                            hSelectedCompile hBodyRun with
                                        ⟨bodyFuel, hBodyLower⟩
                                        constructor
                                        · intro _h
                                          simp_all
                                        · refine
                                            Expressions.Block.run_single_exists
                                              lower ⟨bodyFuel + 1, ?_⟩
                                          have hBodyLower' :
                                              Expressions.Block.run lower
                                                  bodyFuel lowerSelected
                                                  (Structured.RunState.withEVM
                                                    state
                                                    { toSharedState :=
                                                        evmAfterScrutinee.toSharedState,
                                                      pc := evmAfterScrutinee.pc,
                                                      stack := stack,
                                                      execLength :=
                                                        evmAfterScrutinee.execLength }) =
                                                .ok bodyOutcome :=
                                            by
                                              simpa [stateAfterPop] using
                                                hBodyLower
                                          simp [Expressions.Stmt.run,
                                            hScrutineeRun, hPop,
                                            hSelectLowerSome, hBodyLower']
    | for_ init cond post body =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            let initBase := ctx.withoutLoopControl
            cases hInitOpen :
                Locals.Block.compileOpen initBase init with
            | none =>
                simp [initBase, hInitOpen] at hCompile
            | some initCompiled =>
                rcases initCompiled with ⟨initCode, initCompileCtx⟩
                cases hCond :
                    Locals.Expr.compile initCompileCtx cond with
                | none =>
                    simp [initBase, hInitOpen, hCond] at hCompile
                | some lowerCond =>
                    let postBase := initCompileCtx.withoutLoopControl
                    cases hPostOpen :
                        Locals.Block.compileOpen postBase post with
                    | none =>
                        simp [initBase, postBase, hInitOpen, hCond, hPostOpen]
                          at hCompile
                    | some postCompiled =>
                        rcases postCompiled with ⟨postCode, postCtx⟩
                        cases hPostFinish :
                            finishScoped postBase postCtx postCode with
                        | none =>
                            simp [initBase, postBase, hInitOpen, hCond,
                              hPostOpen, hPostFinish] at hCompile
                        | some lowerPost =>
                            let bodyBase :=
                              initCompileCtx.withLoopControl
                                initCompileCtx.layout.length
                            cases hBodyOpen :
                                Locals.Block.compileOpen bodyBase body with
                            | none =>
                                simp [initBase, postBase, bodyBase, hInitOpen,
                                  hCond, hPostOpen, hPostFinish, hBodyOpen]
                                  at hCompile
                            | some bodyCompiled =>
                                rcases bodyCompiled with ⟨bodyCode, bodyCtx⟩
                                cases hBodyFinish :
                                    finishScoped bodyBase bodyCtx bodyCode with
                                | none =>
                                    simp [initBase, postBase, bodyBase,
                                      hInitOpen, hCond, hPostOpen, hPostFinish,
                                      hBodyOpen, hBodyFinish] at hCompile
                                | some lowerBody =>
                                    cases hCleanup :
                                        initCompileCtx.cleanupTo?
                                          ctx.layout.length with
                                    | none =>
                                        simp [initBase, postBase, bodyBase,
                                          hInitOpen, hCond, hPostOpen,
                                          hPostFinish, hBodyOpen, hBodyFinish,
                                          hCleanup] at hCompile
                                    | some cleanup =>
                                        simp [initBase, postBase, bodyBase,
                                          hInitOpen, hCond, hPostOpen,
                                          hPostFinish, hBodyOpen, hBodyFinish,
                                          hCleanup] at hCompile
                                        cases hCompile
                                        subst code
                                        subst compileCtx
                                        unfold Stmt.run at hRun
                                        simp [Stmt.run] at hRun
                                        cases hInitRun :
                                            Block.runOpen program initBase fuel
                                              init state with
                                        | error err =>
                                            simp [initBase, hInitRun] at hRun
                                        | ok initResult =>
                                            rcases initResult with
                                              ⟨initOutcome, initRunCtx⟩
                                            simp [initBase, hInitRun] at hRun
                                            have hInitBridge :=
                                              Block.runOpen_toExpressions_exists
                                                program lower hLower hInitOpen
                                                hInitRun
                                            rcases hInitBridge with
                                              ⟨hInitCtx, hInitLower⟩
                                            let loopStmt :=
                                              Expressions.Stmt.for_
                                                { stmts := initCode } lowerCond
                                                lowerPost lowerBody
                                            have hPostCompile :
                                                Locals.Block.compile postBase post =
                                                  some lowerPost := by
                                              simp [Locals.Block.compile,
                                                hPostOpen, hPostFinish]
                                            have hBodyCompile :
                                                Locals.Block.compile bodyBase body =
                                                  some lowerBody := by
                                              simp [Locals.Block.compile,
                                                hBodyOpen, hBodyFinish]
                                            cases hInitMode :
                                                initOutcome.mode with
                                            | regular =>
                                                simp [hInitMode] at hRun
                                                have hCtxEq :
                                                    initRunCtx =
                                                      initCompileCtx :=
                                                  hInitCtx hInitMode
                                                subst initRunCtx
                                                cases hLoopRun :
                                                    Stmt.runForLoop program
                                                      initCompileCtx cond postBase
                                                      post bodyBase body fuel
                                                      initOutcome.state with
                                                | error err =>
                                                    simp [postBase, bodyBase,
                                                      hLoopRun] at hRun
                                                | ok loopOutcome =>
                                                    simp [postBase, bodyBase,
                                                      hLoopRun] at hRun
                                                    rcases
                                                      Stmt.runForLoop_toExpressions_exists
                                                        program lower hLower
                                                        hCond hPostCompile
                                                        hBodyCompile hLoopRun with
                                                    ⟨loopFuel, hLoopLower⟩
                                                    have hLoopStmtLower :
                                                        ∃ lf,
                                                          Expressions.Stmt.run
                                                            lower lf loopStmt
                                                            state =
                                                              .ok loopOutcome := by
                                                      rcases hInitLower with
                                                        ⟨initFuel, hInitLowerRun⟩
                                                      refine
                                                        ⟨Nat.max initFuel loopFuel + 1,
                                                          ?_⟩
                                                      have hInitLower' :
                                                          Expressions.Block.run
                                                              lower
                                                              (Nat.max initFuel
                                                                loopFuel)
                                                              { stmts := initCode }
                                                              state =
                                                            .ok initOutcome :=
                                                        Expressions.Block.run_mono
                                                          lower
                                                          (Nat.le_max_left _ _)
                                                          hInitLowerRun
                                                      have hLoopLower' :
                                                          Expressions.Stmt.runForLoop
                                                              lower
                                                              (Nat.max initFuel
                                                                loopFuel)
                                                              lowerCond lowerPost
                                                              lowerBody
                                                              initOutcome.state =
                                                            .ok loopOutcome :=
                                                        Expressions.Stmt.runForLoop_mono
                                                          lower
                                                          (Nat.le_max_right _ _)
                                                          hLoopLower
                                                      simp [loopStmt,
                                                        Expressions.Stmt.run,
                                                        hInitLower',
                                                        hInitMode, hLoopLower']
                                                    cases hLoopMode :
                                                        loopOutcome.mode with
                                                    | regular =>
                                                        simp [hLoopMode] at hRun
                                                        cases hCleanupRun :
                                                            Ctx.runCleanupTo
                                                              initCompileCtx
                                                              ctx.layout.length
                                                              loopOutcome.state with
                                                        | error err =>
                                                            simp [hCleanupRun]
                                                              at hRun
                                                        | ok cleaned =>
                                                            simp [hCleanupRun]
                                                              at hRun
                                                            cases hRun
                                                            subst outcome
                                                            subst runCtx
                                                            have hCleanupCode :
                                                                Structured.Code.runState
                                                                    cleanup
                                                                    loopOutcome.state =
                                                                  .ok cleaned := by
                                                              unfold Ctx.runCleanupTo
                                                                at hCleanupRun
                                                              simp [hCleanup]
                                                                at hCleanupRun
                                                              exact hCleanupRun
                                                            have hLoopStmtLowerRegular :
                                                                ∃ lf,
                                                                  Expressions.Stmt.run
                                                                    lower lf
                                                                    loopStmt state =
                                                                      .ok
                                                                        (Outcome.regular
                                                                          loopOutcome.state) := by
                                                              rcases hLoopStmtLower with
                                                                ⟨lf, hLf⟩
                                                              refine ⟨lf, ?_⟩
                                                              rw [outcome_eq_regular_of_mode
                                                                hLoopMode] at hLf
                                                              exact hLf
                                                            constructor
                                                            · intro _h
                                                              rfl
                                                            · exact
                                                                Expressions.Block.run_append_regular_exists
                                                                  lower
                                                                  [loopStmt]
                                                                  (codeStmt cleanup)
                                                                  state
                                                                  loopOutcome.state
                                                                  (Outcome.regular
                                                                    cleaned)
                                                                  (Expressions.Block.run_single_exists
                                                                    lower
                                                                    hLoopStmtLowerRegular)
                                                                  (codeStmt_run_exists
                                                                    lower cleanup
                                                                    loopOutcome.state
                                                                    cleaned
                                                                    hCleanupCode)
                                                    | brk =>
                                                        simp [hLoopMode,
                                                          invalid,
                                                          Structured.invalid]
                                                          at hRun
                                                    | cont =>
                                                        simp [hLoopMode,
                                                          invalid,
                                                          Structured.invalid]
                                                          at hRun
                                                    | leave =>
                                                        simp [hLoopMode] at hRun
                                                        cases hRun
                                                        subst outcome
                                                        subst runCtx
                                                        constructor
                                                        · intro hRegular
                                                          simp [hLoopMode]
                                                            at hRegular
                                                        · exact
                                                            Expressions.Block.run_append_nonregular_exists
                                                              lower [loopStmt]
                                                              (codeStmt cleanup)
                                                              state loopOutcome
                                                              (Expressions.Block.run_single_exists
                                                                lower hLoopStmtLower)
                                                              (by simp
                                                                [hLoopMode])
                                                    | halt kind =>
                                                        simp [hLoopMode] at hRun
                                                        cases hRun
                                                        subst outcome
                                                        subst runCtx
                                                        constructor
                                                        · intro hRegular
                                                          simp [hLoopMode]
                                                            at hRegular
                                                        · exact
                                                            Expressions.Block.run_append_nonregular_exists
                                                              lower [loopStmt]
                                                              (codeStmt cleanup)
                                                              state loopOutcome
                                                              (Expressions.Block.run_single_exists
                                                                lower hLoopStmtLower)
                                                              (by simp
                                                                [hLoopMode])
                                            | brk =>
                                                simp [hInitMode, invalid,
                                                  Structured.invalid] at hRun
                                            | cont =>
                                                simp [hInitMode, invalid,
                                                  Structured.invalid] at hRun
                                            | leave =>
                                                simp [hInitMode] at hRun
                                                cases hRun
                                                subst outcome
                                                subst runCtx
                                                have hLoopStmtLower :
                                                    ∃ lf,
                                                      Expressions.Stmt.run lower lf
                                                        loopStmt state =
                                                          .ok initOutcome := by
                                                  rcases hInitLower with
                                                    ⟨initFuel, hInitLowerRun⟩
                                                  refine ⟨initFuel + 1, ?_⟩
                                                  simp [loopStmt,
                                                    Expressions.Stmt.run,
                                                    hInitLowerRun, hInitMode]
                                                constructor
                                                · intro hRegular
                                                  simp [hInitMode] at hRegular
                                                · exact
                                                    Expressions.Block.run_append_nonregular_exists
                                                      lower [loopStmt]
                                                      (codeStmt cleanup) state
                                                      initOutcome
                                                      (Expressions.Block.run_single_exists
                                                        lower hLoopStmtLower)
                                                      (by simp [hInitMode])
                                            | halt kind =>
                                                simp [hInitMode] at hRun
                                                cases hRun
                                                subst outcome
                                                subst runCtx
                                                have hLoopStmtLower :
                                                    ∃ lf,
                                                      Expressions.Stmt.run lower lf
                                                        loopStmt state =
                                                          .ok initOutcome := by
                                                  rcases hInitLower with
                                                    ⟨initFuel, hInitLowerRun⟩
                                                  refine ⟨initFuel + 1, ?_⟩
                                                  simp [loopStmt,
                                                    Expressions.Stmt.run,
                                                    hInitLowerRun, hInitMode]
                                                constructor
                                                · intro hRegular
                                                  simp [hInitMode] at hRegular
                                                · exact
                                                    Expressions.Block.run_append_nonregular_exists
                                                      lower [loopStmt]
                                                      (codeStmt cleanup) state
                                                      initOutcome
                                                      (Expressions.Block.run_single_exists
                                                        lower hLoopStmtLower)
                                                      (by simp [hInitMode])
    | brk =>
        unfold Locals.Stmt.compile at hCompile
        cases hTarget : ctx.breakDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupTo? target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.run at hRun
                cases hCleanupRun :
                    Ctx.runCleanupTo ctx target state with
                | error err =>
                    simp [hTarget, hCleanupRun] at hRun
                | ok cleaned =>
                    simp [hTarget, hCleanupRun] at hRun
                    cases hRun
                    subst outcome
                    subst runCtx
                    have hCleanupCode :
                        Structured.Code.runState cleanup state = .ok cleaned := by
                      unfold Ctx.runCleanupTo at hCleanupRun
                      simp [hCleanup] at hCleanupRun
                      exact hCleanupRun
                    constructor
                    · intro hRegular
                      simp at hRegular
                    · simpa using
                        codeStmt_append_stmt_run_exists lower cleanup
                          Expressions.Stmt.brk state cleaned (Outcome.brk cleaned)
                          hCleanupCode ⟨1, by simp [Expressions.Stmt.run]⟩
    | cont =>
        unfold Locals.Stmt.compile at hCompile
        cases hTarget : ctx.continueDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupTo? target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.run at hRun
                cases hCleanupRun :
                    Ctx.runCleanupTo ctx target state with
                | error err =>
                    simp [hTarget, hCleanupRun] at hRun
                | ok cleaned =>
                    simp [hTarget, hCleanupRun] at hRun
                    cases hRun
                    subst outcome
                    subst runCtx
                    have hCleanupCode :
                        Structured.Code.runState cleanup state = .ok cleaned := by
                      unfold Ctx.runCleanupTo at hCleanupRun
                      simp [hCleanup] at hCleanupRun
                      exact hCleanupRun
                    constructor
                    · intro hRegular
                      simp at hRegular
                    · simpa using
                        codeStmt_append_stmt_run_exists lower cleanup
                          Expressions.Stmt.cont state cleaned
                          (Outcome.cont cleaned) hCleanupCode
                          ⟨1, by simp [Expressions.Stmt.run]⟩
    | leave =>
        unfold Locals.Stmt.compile at hCompile
        cases hTarget : ctx.leaveDepth? with
        | none =>
            simp [hTarget] at hCompile
        | some target =>
            cases hCleanup : ctx.cleanupToPreserving? ctx.leaveRetc target with
            | none =>
                simp [hTarget, hCleanup] at hCompile
            | some cleanup =>
                simp [hTarget, hCleanup] at hCompile
                cases hCompile
                subst code
                subst compileCtx
                unfold Stmt.run at hRun
                cases hCleanupRun :
                    Ctx.runCleanupToPreserving ctx ctx.leaveRetc target state with
                | error err =>
                    simp [hTarget, hCleanupRun] at hRun
                | ok cleaned =>
                    cases hReturns : cleaned.returns with
                    | nil =>
                        simp [hTarget, hCleanupRun, hReturns, invalid,
                          Structured.invalid] at hRun
                    | cons frame rest =>
                        simp [hTarget, hCleanupRun, hReturns] at hRun
                        cases hRun
                        subst outcome
                        subst runCtx
                        have hCleanupCode :
                            Structured.Code.runState cleanup state = .ok cleaned := by
                          unfold Ctx.runCleanupToPreserving at hCleanupRun
                          simp [hCleanup] at hCleanupRun
                          exact hCleanupRun
                        constructor
                        · intro hRegular
                          simp at hRegular
                        · simpa using
                            codeStmt_append_stmt_run_exists lower cleanup
                              Expressions.Stmt.leave state cleaned
                              (Outcome.leave cleaned) hCleanupCode
                              ⟨1, by simp [Expressions.Stmt.run, hReturns]⟩
    | call name =>
        cases fuel with
        | zero =>
            simp [Stmt.run, invalid, Structured.invalid] at hRun
        | succ fuel =>
            unfold Locals.Stmt.compile at hCompile
            simp at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.run at hRun
            simp [Stmt.run] at hRun
            cases hLookup : ProcList.lookup? name program.procs with
            | none =>
                simp [hLookup, invalid, Structured.invalid] at hRun
            | some proc =>
                cases hSplit :
                    Structured.StackFrame.splitArgs? proc.argc state.evm.stack with
                | none =>
                    simp [hLookup, hSplit] at hRun
                | some split =>
                    rcases split with ⟨args, callerStack⟩
                    let callState :=
                      (state.withEVM { state.evm with stack := args }).pushReturn
                        callerStack proc.retc
                    let entryCtx :=
                      Ctx.procEntryWithLayoutAndRetc proc.entryLayout proc.retc
                    cases hBodyRun :
                        Block.runOpen program entryCtx fuel proc.body
                          callState with
                    | error err =>
                        simp [entryCtx, hLookup, hSplit, callState, hBodyRun]
                          at hRun
                    | ok bodyResult =>
                        rcases bodyResult with ⟨bodyOutcome, bodyCtx⟩
                        simp [entryCtx, hLookup, hSplit, callState, hBodyRun]
                          at hRun
                        have hLowerProcs :=
                          Locals.Program.procs_toExpressions_of_toExpressions?
                            hLower
                        rcases
                          ProcList.lookup?_toExpressions?
                            hLowerProcs hLookup with
                        ⟨lowerProc, hLowerLookup, hProcLower⟩
                        rcases Proc.toExpressions?_body hProcLower with
                          ⟨hProcBody, hProcName, hProcArgc, hProcRetc⟩
                        change Locals.Block.compileToPreserving entryCtx
                          proc.retc 0 proc.body =
                          some lowerProc.body at hProcBody
                        unfold Locals.Block.compileToPreserving at hProcBody
                        cases hProcOpen :
                            Locals.Block.compileOpen entryCtx proc.body with
                        | none =>
                            simp [hProcOpen] at hProcBody
                        | some bodyCompiled =>
                            rcases bodyCompiled with
                              ⟨bodyCode, bodyCompileCtx⟩
                            cases hProcFinish :
                                finishToPreserving bodyCompileCtx proc.retc 0
                                  bodyCode with
                            | none =>
                                simp [hProcOpen, hProcFinish] at hProcBody
                            | some lowerBody =>
                                simp [hProcOpen, hProcFinish] at hProcBody
                                cases hProcBody
                                have hOpenBridge :=
                                  Block.runOpen_toExpressions_exists program
                                    lower hLower hProcOpen hBodyRun
                                rcases hOpenBridge with
                                  ⟨hBodyCtx, hBodyLowerOpen⟩
                                have hBodyLowerNonregular
                                    (hNon : bodyOutcome.mode ≠ .regular) :
                                    ∃ lowerFuel,
                                      Expressions.Block.run lower lowerFuel
                                        lowerProc.body callState =
                                          .ok bodyOutcome := by
                                  unfold finishToPreserving at hProcFinish
                                  cases hCleanup :
                                      bodyCompileCtx.cleanupToPreserving?
                                        proc.retc 0 with
                                  | none =>
                                      simp [hCleanup] at hProcFinish
                                  | some cleanup =>
                                      simp [hCleanup] at hProcFinish
                                      rcases
                                        Expressions.Block.run_append_nonregular_exists
                                          lower bodyCode (codeStmt cleanup)
                                          callState bodyOutcome
                                          hBodyLowerOpen hNon with
                                      ⟨lf, hLf⟩
                                      exact ⟨lf, by simpa [hProcFinish] using hLf⟩
                                cases hBodyMode : bodyOutcome.mode with
                                | regular =>
                                    simp [hBodyMode] at hRun
                                    have hCtxEq :
                                        bodyCtx = bodyCompileCtx := hBodyCtx hBodyMode
                                    subst bodyCtx
                                    unfold finishToPreserving at hProcFinish
                                    cases hCleanup :
                                        bodyCompileCtx.cleanupToPreserving?
                                          proc.retc 0 with
                                    | none =>
                                        simp [hCleanup] at hProcFinish
                                    | some cleanup =>
                                        simp [hCleanup] at hProcFinish
                                        cases hCleanupRun :
                                            Ctx.runCleanupToPreserving
                                              bodyCompileCtx proc.retc 0
                                                bodyOutcome.state with
                                        | error err =>
                                            simp [hCleanupRun] at hRun
                                        | ok cleaned =>
                                            simp [hCleanupRun] at hRun
                                            have hCleanupCode :
                                                Structured.Code.runState cleanup
                                                  bodyOutcome.state = .ok cleaned := by
                                              unfold Ctx.runCleanupToPreserving
                                                at hCleanupRun
                                              simp [hCleanup] at hCleanupRun
                                              exact hCleanupRun
                                            have hBodyLowerRegularOpen :
                                                ∃ lowerFuel,
                                                  Expressions.Block.run lower lowerFuel
                                                    { stmts := bodyCode } callState =
                                                      .ok
                                                        (Outcome.regular
                                                          bodyOutcome.state) := by
                                              rcases hBodyLowerOpen with ⟨lf, hLf⟩
                                              refine ⟨lf, ?_⟩
                                              rw [outcome_eq_regular_of_mode hBodyMode]
                                                at hLf
                                              exact hLf
                                            have hBodyLower :
                                                ∃ lowerFuel,
                                                  Expressions.Block.run lower lowerFuel
                                                    lowerProc.body callState =
                                                      .ok (Outcome.regular cleaned) :=
                                              by
                                                rcases
                                                  Expressions.Block.run_append_regular_exists
                                                    lower bodyCode (codeStmt cleanup)
                                                    callState bodyOutcome.state
                                                    (Outcome.regular cleaned)
                                                    hBodyLowerRegularOpen
                                                    (codeStmt_run_exists lower cleanup
                                                      bodyOutcome.state cleaned
                                                      hCleanupCode) with
                                                ⟨lf, hLf⟩
                                                exact ⟨lf,
                                                  by simpa [hProcFinish] using hLf⟩
                                            cases hPopReturn : cleaned.popReturn? with
                                            | none =>
                                                simp [hPopReturn, invalid,
                                                  Structured.invalid] at hRun
                                            | some popResult =>
                                                rcases popResult with
                                                  ⟨frame, returned⟩
                                                cases hAttach :
                                                    Structured.StackFrame.attachReturns?
                                                      frame cleaned.evm.stack with
                                                | none =>
                                                    simp [hPopReturn, hAttach, invalid,
                                                      Structured.invalid] at hRun
                                                | some stack =>
                                                    simp [hPopReturn, hAttach] at hRun
                                                    cases hRun
                                                    subst outcome
                                                    subst runCtx
                                                    constructor
                                                    · intro _h
                                                      simp_all
                                                    · rcases hBodyLower with
                                                        ⟨bodyFuel, hBodyLower⟩
                                                      refine
                                                        Expressions.Block.run_single_exists
                                                          lower ⟨bodyFuel + 1, ?_⟩
                                                      simp [Expressions.Stmt.run,
                                                        hLowerLookup, hProcArgc,
                                                        hProcRetc, hSplit, callState,
                                                        hBodyLower, hPopReturn, hAttach]
                                | brk =>
                                    simp [hBodyMode, invalid, Structured.invalid] at hRun
                                | cont =>
                                    simp [hBodyMode, invalid, Structured.invalid] at hRun
                                | leave =>
                                    simp [hBodyMode] at hRun
                                    have hBodyLower :=
                                      hBodyLowerNonregular (by simp [hBodyMode])
                                    cases hPopReturn : bodyOutcome.state.popReturn? with
                                    | none =>
                                        simp [hPopReturn, invalid, Structured.invalid]
                                          at hRun
                                    | some popResult =>
                                        rcases popResult with ⟨frame, returned⟩
                                        cases hAttach :
                                            Structured.StackFrame.attachReturns? frame
                                              bodyOutcome.state.evm.stack with
                                        | none =>
                                            simp [hPopReturn, hAttach, invalid,
                                              Structured.invalid] at hRun
                                        | some stack =>
                                            simp [hPopReturn, hAttach] at hRun
                                            cases hRun
                                            subst outcome
                                            subst runCtx
                                            constructor
                                            · intro _h
                                              simp_all
                                            · rcases hBodyLower with
                                                ⟨bodyFuel, hBodyLower⟩
                                              refine
                                                Expressions.Block.run_single_exists lower
                                                  ⟨bodyFuel + 1, ?_⟩
                                              simp [Expressions.Stmt.run, hLowerLookup,
                                                hProcArgc, hProcRetc, hSplit,
                                                callState, hBodyLower, hBodyMode,
                                                hPopReturn, hAttach]
                                | halt kind =>
                                    simp [hBodyMode] at hRun
                                    have hBodyLower :=
                                      hBodyLowerNonregular (by simp [hBodyMode])
                                    cases hRun
                                    subst outcome
                                    subst runCtx
                                    constructor
                                    · intro hRegular
                                      simp [hBodyMode] at hRegular
                                    · rcases hBodyLower with ⟨bodyFuel, hBodyLower⟩
                                      refine
                                        Expressions.Block.run_single_exists lower
                                          ⟨bodyFuel + 1, ?_⟩
                                      simp [Expressions.Stmt.run, hLowerLookup,
                                        hProcArgc, hProcRetc, hSplit, callState,
                                        hBodyLower, hBodyMode]
    | terminal kind =>
            unfold Locals.Stmt.compile at hCompile
            simp at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.run at hRun
            cases hCleanupRun : Ctx.runCleanupAll ctx state with
        | error err =>
            simp [hCleanupRun] at hRun
        | ok cleaned =>
            cases hTerminal :
                Structured.Terminal.step kind cleaned.evm with
            | error err =>
                simp [hCleanupRun, hTerminal] at hRun
            | ok evm =>
                simp [hCleanupRun, hTerminal] at hRun
                cases hRun
                subst outcome
                subst runCtx
                have hCleanupCode :
                    Structured.Code.runState ctx.cleanupAll state = .ok cleaned := by
                  unfold Ctx.runCleanupAll at hCleanupRun
                  exact hCleanupRun
                constructor
                · intro hRegular
                  simp_all
                · simpa using
                    codeStmt_append_stmt_run_exists lower ctx.cleanupAll
                      (Expressions.Stmt.terminal kind) state cleaned
                      (Outcome.halt kind (cleaned.withEVM evm)) hCleanupCode
                      ⟨1, by simp [Expressions.Stmt.run, hTerminal]⟩
    | terminalArgs kind args =>
        unfold Locals.Stmt.compile at hCompile
        cases hArgsCode : Locals.ExprSeq.compileCode ctx 0 args with
        | none =>
            simp [hArgsCode] at hCompile
        | some argsCode =>
            simp [hArgsCode] at hCompile
            cases hCompile
            subst code
            subst compileCtx
            unfold Stmt.run at hRun
            rw [Expr.ExprSeq.runCode_eq_compileCode_zero ctx args argsCode
                state.evm hArgsCode] at hRun
            cases hArgsRun : Structured.Code.run argsCode state.evm with
            | error err =>
                simp [hArgsRun] at hRun
            | ok evmAfterArgs =>
                cases hTerminal :
                    Structured.Terminal.step kind evmAfterArgs with
                | error err =>
                    simp [hArgsRun, hTerminal] at hRun
                | ok evm =>
                    simp [hArgsRun, hTerminal] at hRun
                    cases hRun
                    subst outcome
                    subst runCtx
                    have hArgsCodeRun :
                        Structured.Code.runState argsCode state =
                          .ok (state.withEVM evmAfterArgs) := by
                      unfold Structured.Code.runState
                      simp [hArgsRun]
                    constructor
                    · intro hRegular
                      simp_all
                    · simpa using
                        codeStmt_append_stmt_run_exists lower argsCode
                          (Expressions.Stmt.terminal kind) state
                          (state.withEVM evmAfterArgs)
                          (Outcome.halt kind (state.withEVM evm)) hArgsCodeRun
                          ⟨1, by simp [Expressions.Stmt.run, hTerminal]⟩
  termination_by
    _ctx fuel stmt _state _outcome _runCtx _compileCtx _code _hCompile
      _hRun => (fuel, 3, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

theorem runState_toExpressions_exists {program : Program}
    {lower : Expressions.Program} {fuel : Nat} {state : RunState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hRun : Direct.Program.runState fuel program state = .ok outcome) :
    ∃ lowerFuel,
      Expressions.Block.run lower lowerFuel lower.body state = .ok outcome := by
  have hBody := Locals.Program.body_toExpressions_of_toExpressions? hLower
  exact
    Block.runScoped_toExpressions_exists program lower hLower hBody hRun

theorem run_toExpressions_exists {program : Program}
    {lower : Expressions.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hRun : Direct.Program.run fuel program initial = .ok outcome) :
    ∃ lowerFuel, lower.run lowerFuel initial = .ok outcome := by
  exact runState_toExpressions_exists hLower hRun

end Program

end Direct

namespace Program

theorem run_toExpressions_exists {program : Program}
    {lower : Expressions.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ lowerFuel, lower.run lowerFuel initial = .ok outcome := by
  exact
    Direct.Program.run_toExpressions_exists hLower
      (by simpa [Locals.Program.run] using hRun)

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Expressions.Program.compileChecked? lower

theorem compileChecked?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Expressions.Program.compileChecked? lower = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileChecked?_noCallCreate {program : Program}
    {asm : Assembly.Program}
    (hProgram : program.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  exact
    Expressions.Program.compileChecked?_noCallCreate
      (program := lower) (asm := asm)
      (CompilerFacts.Program.toExpressions?_noCallCreate program hProgram
        hLower)
      hLowerCompile

theorem compile_preserves {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases run_toExpressions_exists hLower hRun with ⟨lowerFuel, hLowerRun⟩
  exact
    Expressions.Program.compile_preserves hCompile hInitialPc hLowerRun

theorem compile_preserves_endPc {program : Program}
    {lower : Expressions.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases run_toExpressions_exists hLower hRun with ⟨lowerFuel, hLowerRun⟩
  exact
    Expressions.Program.compile_preserves_endPc hCompile hInitialPc hLowerRun

theorem compile_preserves_checked {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  rcases run_toExpressions_exists hLower hRun with ⟨lowerFuel, hLowerRun⟩
  exact
    Expressions.Program.compile_preserves_of_compileChecked
      hLowerCompile hInitialPc hLowerRun

theorem compile_preserves_checked_endPc {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  rcases run_toExpressions_exists hLower hRun with ⟨lowerFuel, hLowerRun⟩
  exact
    Expressions.Program.compile_preserves_of_compileChecked_endPc
      hLowerCompile hInitialPc hLowerRun

end Program

end Locals
end EvmCompiler
