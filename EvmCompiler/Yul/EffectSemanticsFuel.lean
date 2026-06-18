import EvmCompiler.Yul.EffectSemantics

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

attribute [local simp] Bind.bind Except.bind

/-!
Successful canonical Yul executions are monotone in fuel whenever the selected
primitive semantics is itself success-monotone. The primitive condition is
necessary: `PrimitiveSemantics.eval` is intentionally parameterized by fuel and
an arbitrary handler may assign different meanings at different fuel values.
-/

namespace PrimitiveSemantics

structure SuccessMonotone {σ : Type} (prim : PrimitiveSemantics σ) : Prop where
  eval :
    ∀ {fuel fuel' : Nat} {state final : σ}
      {op : EvmYul.Operation .Yul} {args values : List Word},
      fuel ≤ fuel' →
      prim.eval fuel state op args = .ok (final, values) →
      prim.eval fuel' state op args = .ok (final, values)

end PrimitiveSemantics

set_option maxHeartbeats 2000000 in
mutual
  theorem evalTail_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {args : List EvmYul.Yul.Ast.Expr}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {input : Result σ (σ × Word)} {final : σ} {values : List Word},
        fuel ≤ fuel' →
        evalTail model prim fuel args codeOverride input =
          .ok (final, values) →
        evalTail model prim fuel' args codeOverride input =
          .ok (final, values) := by
    intro fuel fuel' args codeOverride input final values hLe hRun
    cases input with
    | error failure =>
        simp [evalTail] at hRun
    | ok result =>
        rcases result with ⟨state, value⟩
        cases fuel with
        | zero =>
            simp [evalTail, fail] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                have hFuelLe : fuel ≤ fuel' :=
                  Nat.succ_le_succ_iff.mp hLe
                cases hArgs :
                    evalArgs model prim fuel args codeOverride state with
                | error failure =>
                    simp [evalTail, hArgs] at hRun
                | ok result =>
                    rcases result with ⟨stateAfterArgs, argsValues⟩
                    have hArgs' :
                        evalArgs model prim fuel' args codeOverride state =
                          .ok (stateAfterArgs, argsValues) :=
                      evalArgs_mono model prim hPrim hFuelLe hArgs
                    simpa [evalTail, hArgs, hArgs'] using hRun
  termination_by
    fuel _fuel' args _codeOverride _input _final _values _hLe _hRun =>
      (fuel, 0, sizeOf args)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem evalArgs_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {args : List EvmYul.Yul.Ast.Expr}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ} {values : List Word},
        fuel ≤ fuel' →
        evalArgs model prim fuel args codeOverride state =
          .ok (final, values) →
        evalArgs model prim fuel' args codeOverride state =
          .ok (final, values) := by
    intro fuel fuel' args codeOverride state final values hLe hRun
    cases fuel with
    | zero =>
        simp [evalArgs, fail] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' :=
              Nat.succ_le_succ_iff.mp hLe
            cases args with
            | nil =>
                simpa [evalArgs] using hRun
            | cons arg rest =>
                cases hEval :
                    Effectful.eval model prim fuel arg codeOverride state with
                | error failure =>
                    simp [evalArgs, evalTail, hEval] at hRun
                | ok result =>
                    rcases result with ⟨stateAfterArg, value⟩
                    have hEval' :
                        Effectful.eval model prim fuel' arg codeOverride state =
                          .ok (stateAfterArg, value) :=
                      eval_mono model prim hPrim hFuelLe hEval
                    have hTail :
                        evalTail model prim fuel rest codeOverride
                            (.ok (stateAfterArg, value)) =
                          .ok (final, values) := by
                      simpa [evalArgs, hEval] using hRun
                    have hTail' :=
                      evalTail_mono model prim hPrim hFuelLe hTail
                    simpa [evalArgs, hEval'] using hTail'
  termination_by
    fuel _fuel' args _codeOverride _state _final _values _hLe _hRun =>
      (fuel, 1, sizeOf args)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem evalValues_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {expr : EvmYul.Yul.Ast.Expr}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ} {values : List Word},
        fuel ≤ fuel' →
        evalValues model prim fuel expr codeOverride state =
          .ok (final, values) →
        evalValues model prim fuel' expr codeOverride state =
          .ok (final, values) := by
    intro fuel fuel' expr codeOverride state final values hLe hRun
    cases fuel with
    | zero =>
        simp [evalValues, fail] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' :=
              Nat.succ_le_succ_iff.mp hLe
            cases expr with
            | Call callee args =>
                cases callee with
                | inl op =>
                    cases hArgs :
                        evalArgs model prim fuel args.reverse codeOverride
                          state with
                    | error failure =>
                        simp [evalValues, hArgs] at hRun
                    | ok result =>
                        rcases result with ⟨stateAfterArgs, argsValues⟩
                        have hArgs' :
                            evalArgs model prim fuel' args.reverse
                                codeOverride state =
                              .ok (stateAfterArgs, argsValues) :=
                          evalArgs_mono model prim hPrim hFuelLe hArgs
                        have hEval :
                            prim.eval fuel stateAfterArgs op
                                argsValues.reverse =
                              .ok (final, values) := by
                          simpa [evalValues, hArgs] using hRun
                        have hEval' :=
                          hPrim.eval hFuelLe hEval
                        simpa [evalValues, hArgs, hArgs'] using hEval'
                | inr functionName =>
                    cases hArgs :
                        evalArgs model prim fuel args.reverse codeOverride
                          state with
                    | error failure =>
                        simp [evalValues, hArgs] at hRun
                    | ok result =>
                        rcases result with ⟨stateAfterArgs, argsValues⟩
                        have hArgs' :
                            evalArgs model prim fuel' args.reverse
                                codeOverride state =
                              .ok (stateAfterArgs, argsValues) :=
                          evalArgs_mono model prim hPrim hFuelLe hArgs
                        have hCall :
                            call model prim fuel argsValues.reverse
                                (some functionName) codeOverride
                                stateAfterArgs =
                              .ok (final, values) := by
                          simpa [evalValues, hArgs] using hRun
                        have hCall' :
                            call model prim fuel' argsValues.reverse
                                (some functionName) codeOverride
                                stateAfterArgs =
                              .ok (final, values) :=
                          call_mono model prim hPrim hFuelLe hCall
                        simpa [evalValues, hArgs, hArgs'] using hCall'
            | Var name =>
                simpa [evalValues] using hRun
            | Lit value =>
                simpa [evalValues] using hRun
  termination_by
    fuel _fuel' expr _codeOverride _state _final _values _hLe _hRun =>
      (fuel, 2, sizeOf expr)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem eval_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {expr : EvmYul.Yul.Ast.Expr}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ} {value : Word},
        fuel ≤ fuel' →
        Effectful.eval model prim fuel expr codeOverride state =
          .ok (final, value) →
        Effectful.eval model prim fuel' expr codeOverride state =
          .ok (final, value) := by
    intro fuel fuel' expr codeOverride state final value hLe hRun
    cases hValues :
        evalValues model prim fuel expr codeOverride state with
    | error failure =>
        simp [Effectful.eval, hValues] at hRun
    | ok result =>
        rcases result with ⟨stateAfterValues, values⟩
        have hValues' :
            evalValues model prim fuel' expr codeOverride state =
              .ok (stateAfterValues, values) :=
          evalValues_mono model prim hPrim hLe hValues
        simpa [Effectful.eval, hValues, hValues'] using hRun
  termination_by
    fuel _fuel' expr _codeOverride _state _final _value _hLe _hRun =>
      (fuel, 3, sizeOf expr)
  decreasing_by
    all_goals simp_wf
    all_goals
      exact Prod.Lex.right _
        (Prod.Lex.left _ _ (by omega))

  theorem call_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {args : List Word}
        {functionName? : Option EvmYul.Yul.Ast.YulFunctionName}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ} {values : List Word},
        fuel ≤ fuel' →
        call model prim fuel args functionName? codeOverride state =
          .ok (final, values) →
        call model prim fuel' args functionName? codeOverride state =
          .ok (final, values) := by
    intro fuel fuel' args functionName? codeOverride state final values
      hLe hRun
    cases fuel with
    | zero =>
        simp [call, fail] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' :=
              Nat.succ_le_succ_iff.mp hLe
            cases hCode :
                resolveActiveCode? (model.source state) codeOverride with
            | none =>
                simp [call, hCode, fail] at hRun
            | some code =>
                cases functionName? with
                | none =>
                    let body :=
                      [code.dispatcher]
                    let sourceAtEntry :=
                      EvmYul.Yul.State.mkOk
                        ((model.source state).initcall [] [] args)
                    cases hBody :
                        exec model prim fuel (.Block body) codeOverride
                          (model.withSource state sourceAtEntry) with
                    | error failure =>
                        simp [call, hCode, body, sourceAtEntry, hBody]
                          at hRun
                    | ok stateAfterBody =>
                        have hBody' :
                            exec model prim fuel' (.Block body) codeOverride
                                (model.withSource state sourceAtEntry) =
                              .ok stateAfterBody :=
                          exec_mono model prim hPrim hFuelLe hBody
                        simpa [call, hCode, body, sourceAtEntry, hBody,
                          hBody'] using hRun
                | some functionName =>
                    cases hLookup :
                        code.functions.lookup functionName with
                    | none =>
                        simp [call, hCode, hLookup, fail] at hRun
                    | some function =>
                        cases function with
                        | Def params rets body =>
                            let sourceAtEntry :=
                              EvmYul.Yul.State.mkOk
                                ((model.source state).initcall
                                  params rets args)
                            cases hBody :
                                exec model prim fuel (.Block body)
                                  codeOverride
                                  (model.withSource state sourceAtEntry) with
                            | error failure =>
                                simp [call, hCode, hLookup, sourceAtEntry,
                                  hBody] at hRun
                            | ok stateAfterBody =>
                                have hBody' :
                                    exec model prim fuel' (.Block body)
                                        codeOverride
                                        (model.withSource state
                                          sourceAtEntry) =
                                      .ok stateAfterBody :=
                                  exec_mono model prim hPrim hFuelLe hBody
                                simpa [call, hCode, hLookup, sourceAtEntry,
                                  hBody, hBody'] using hRun
  termination_by
    fuel _fuel' args _functionName _codeOverride _state _final _values
        _hLe _hRun =>
      (fuel, 4, sizeOf args)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem callDispatcher_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ} {values : List Word},
        fuel ≤ fuel' →
        callDispatcher model prim fuel codeOverride state =
          .ok (final, values) →
        callDispatcher model prim fuel' codeOverride state =
          .ok (final, values) := by
    intro fuel fuel' codeOverride state final values hLe hRun
    cases fuel with
    | zero =>
        simp [callDispatcher, fail] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' :=
              Nat.succ_le_succ_iff.mp hLe
            let source := model.source state
            let sourceAtEntry :=
              EvmYul.Yul.State.mkOk (source.initcall [] [] [])
            cases hBody :
                exec model prim fuel
                  (.Block [source.executionEnv.code.dispatcher])
                  codeOverride (model.withSource state sourceAtEntry) with
            | error failure =>
                simp [callDispatcher, source, sourceAtEntry, hBody] at hRun
            | ok stateAfterBody =>
                have hBody' :
                    exec model prim fuel'
                        (.Block [source.executionEnv.code.dispatcher])
                        codeOverride
                        (model.withSource state sourceAtEntry) =
                      .ok stateAfterBody :=
                  exec_mono model prim hPrim hFuelLe hBody
                simpa [callDispatcher, source, sourceAtEntry, hBody, hBody']
                  using hRun
  termination_by
    fuel _fuel' _codeOverride _state _final _values _hLe _hRun =>
      (fuel, 5, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem execSeq_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {stmts : List EvmYul.Yul.Ast.Stmt}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ},
        fuel ≤ fuel' →
        execSeq model prim fuel stmts codeOverride state = .ok final →
        execSeq model prim fuel' stmts codeOverride state = .ok final := by
    intro fuel fuel' stmts codeOverride state final hLe hRun
    cases fuel with
    | zero =>
        simp [execSeq, fail] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' :=
              Nat.succ_le_succ_iff.mp hLe
            cases stmts with
            | nil =>
                simpa [execSeq] using hRun
            | cons stmt rest =>
                cases hStmt :
                    exec model prim fuel stmt codeOverride state with
                | error failure =>
                    simp [execSeq, hStmt] at hRun
                | ok stateAfterStmt =>
                    have hStmt' :
                        exec model prim fuel' stmt codeOverride state =
                          .ok stateAfterStmt :=
                      exec_mono model prim hPrim hFuelLe hStmt
                    cases hSource : model.source stateAfterStmt with
                    | Ok shared vars =>
                        have hRest :
                            execSeq model prim fuel rest codeOverride
                                stateAfterStmt =
                              .ok final := by
                          simpa [execSeq, hStmt, hSource] using hRun
                        have hRest' :=
                          execSeq_mono model prim hPrim hFuelLe hRest
                        simpa [execSeq, hStmt', hSource] using hRest'
                    | OutOfFuel =>
                        simpa [execSeq, hStmt, hStmt', hSource] using hRun
                    | Checkpoint jump =>
                        simpa [execSeq, hStmt, hStmt', hSource] using hRun
  termination_by
    fuel _fuel' stmts _codeOverride _state _final _hLe _hRun =>
      (fuel, 6, sizeOf stmts)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem exec_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {stmt : EvmYul.Yul.Ast.Stmt}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ},
        fuel ≤ fuel' →
        exec model prim fuel stmt codeOverride state = .ok final →
        exec model prim fuel' stmt codeOverride state = .ok final := by
    intro fuel fuel' stmt codeOverride state final hLe hRun
    cases fuel with
    | zero =>
        simp [exec, fail] at hRun
    | succ fuel =>
        cases fuel' with
        | zero =>
            omega
        | succ fuel' =>
            have hFuelLe : fuel ≤ fuel' :=
              Nat.succ_le_succ_iff.mp hLe
            let source := model.source state
            cases stmt with
            | Block stmts =>
                cases hBody :
                    execSeq model prim fuel stmts codeOverride state with
                | error failure =>
                    simp [exec, hBody] at hRun
                | ok stateAfterBody =>
                    have hBody' :
                        execSeq model prim fuel' stmts codeOverride state =
                          .ok stateAfterBody :=
                      execSeq_mono model prim hPrim hFuelLe hBody
                    simpa [exec, hBody, hBody'] using hRun
            | Let vars expr? =>
                cases expr? with
                | none =>
                    cases hDeclaration :
                        EvmYul.Yul.checkDeclaration source vars with
                    | error err =>
                        rw [exec.eq_3] at hRun
                        simp [source, hDeclaration, fail] at hRun
                    | ok unit =>
                        simpa [exec, source, hDeclaration] using hRun
                | some expr =>
                    cases hDeclaration :
                        EvmYul.Yul.checkDeclaration source vars with
                    | error err =>
                        rw [exec.eq_4] at hRun
                        simp [source, hDeclaration, fail] at hRun
                    | ok unit =>
                        cases hValues :
                            evalValues model prim fuel expr codeOverride
                              state with
                        | error failure =>
                            simp [exec, source, hDeclaration, multifill,
                              hValues] at hRun
                        | ok result =>
                            rcases result with ⟨stateAfterValues, values⟩
                            have hValues' :
                                evalValues model prim fuel' expr codeOverride
                                    state =
                                  .ok (stateAfterValues, values) :=
                              evalValues_mono model prim hPrim hFuelLe
                                hValues
                            simpa [exec, source, hDeclaration, multifill,
                              hValues, hValues'] using hRun
            | Assign vars expr =>
                cases hAssignment :
                    EvmYul.Yul.checkAssignment source vars with
                | error err =>
                    simp [exec, source, hAssignment, fail] at hRun
                | ok unit =>
                    cases hValues :
                        evalValues model prim fuel expr codeOverride state with
                    | error failure =>
                        simp [exec, source, hAssignment, multifill,
                          hValues] at hRun
                    | ok result =>
                        rcases result with ⟨stateAfterValues, values⟩
                        have hValues' :
                            evalValues model prim fuel' expr codeOverride
                                state =
                              .ok (stateAfterValues, values) :=
                          evalValues_mono model prim hPrim hFuelLe hValues
                        simpa [exec, source, hAssignment, multifill,
                          hValues, hValues'] using hRun
            | If cond body =>
                cases hCond :
                    Effectful.eval model prim fuel cond codeOverride state with
                | error failure =>
                    simp [exec, source, hCond] at hRun
                | ok result =>
                    rcases result with ⟨stateAfterCond, condValue⟩
                    have hCond' :
                        Effectful.eval model prim fuel' cond codeOverride
                            state =
                          .ok (stateAfterCond, condValue) :=
                      eval_mono model prim hPrim hFuelLe hCond
                    by_cases hTrue : condValue ≠ ⟨0⟩
                    · have hBody :
                          exec model prim fuel (.Block body) codeOverride
                              stateAfterCond =
                            .ok final := by
                        simpa [exec, source, hCond, hTrue] using hRun
                      have hBody' :=
                        exec_mono model prim hPrim hFuelLe hBody
                      simpa [exec, source, hCond', hTrue] using hBody'
                    · simpa [exec, source, hCond, hCond', hTrue,
                        Bind.bind, Except.bind] using hRun
            | ExprStmtCall expr =>
                cases expr with
                | Call callee args =>
                    cases callee with
                    | inl op =>
                        cases hArgs :
                            evalArgs model prim fuel args.reverse codeOverride
                              state with
                        | error failure =>
                            simp [exec, source, hArgs] at hRun
                        | ok result =>
                            rcases result with
                              ⟨stateAfterArgs, argsValues⟩
                            have hArgs' :
                                evalArgs model prim fuel' args.reverse
                                    codeOverride state =
                                  .ok (stateAfterArgs, argsValues) :=
                              evalArgs_mono model prim hPrim hFuelLe hArgs
                            cases hPrimitive :
                                prim.eval fuel stateAfterArgs op
                                  argsValues.reverse with
                            | error failure =>
                                simp [exec, source, hArgs, multifill,
                                  hPrimitive] at hRun
                            | ok result =>
                                rcases result with
                                  ⟨stateAfterPrimitive, outputs⟩
                                have hPrimitive' :
                                    prim.eval fuel' stateAfterArgs op
                                        argsValues.reverse =
                                      .ok
                                        (stateAfterPrimitive, outputs) :=
                                  hPrim.eval hFuelLe hPrimitive
                                simpa [exec, source, hArgs, hArgs',
                                  multifill, hPrimitive, hPrimitive']
                                  using hRun
                    | inr functionName =>
                        cases hArgs :
                            evalArgs model prim fuel args.reverse codeOverride
                              state with
                        | error failure =>
                            simp [exec, source, hArgs] at hRun
                        | ok result =>
                            rcases result with
                              ⟨stateAfterArgs, argsValues⟩
                            have hArgs' :
                                evalArgs model prim fuel' args.reverse
                                    codeOverride state =
                                  .ok (stateAfterArgs, argsValues) :=
                              evalArgs_mono model prim hPrim hFuelLe hArgs
                            cases fuel with
                            | zero =>
                                simp [exec, source, hArgs, fail] at hRun
                            | succ callFuel =>
                                cases fuel' with
                                | zero =>
                                    omega
                                | succ callFuel' =>
                                    have hCallFuelLe :
                                        callFuel ≤ callFuel' :=
                                      Nat.succ_le_succ_iff.mp hFuelLe
                                    cases hCall :
                                        call model prim callFuel
                                          argsValues.reverse
                                          (some functionName) codeOverride
                                          stateAfterArgs with
                                    | error failure =>
                                        simp [exec, source, hArgs, hCall,
                                          multifill] at hRun
                                    | ok result =>
                                        rcases result with
                                          ⟨stateAfterCall, outputs⟩
                                        have hCall' :
                                            call model prim callFuel'
                                                argsValues.reverse
                                                (some functionName)
                                                codeOverride stateAfterArgs =
                                              .ok
                                                (stateAfterCall, outputs) :=
                                          call_mono model prim hPrim
                                            hCallFuelLe hCall
                                        simpa [exec, source, hArgs, hArgs',
                                          hCall, hCall', multifill]
                                          using hRun
                | Var name =>
                    simp [exec, source, fail] at hRun
                | Lit value =>
                    simp [exec, source, fail] at hRun
            | Switch cond cases default =>
                cases hCond :
                    Effectful.eval model prim fuel cond codeOverride state with
                | error failure =>
                    simp [exec, source, hCond] at hRun
                | ok result =>
                    rcases result with ⟨stateAfterCond, condValue⟩
                    have hCond' :
                        Effectful.eval model prim fuel' cond codeOverride
                            state =
                          .ok (stateAfterCond, condValue) :=
                      eval_mono model prim hPrim hFuelLe hCond
                    have hBody :
                        exec model prim fuel
                            (.Block
                              (EvmYul.Yul.selectSwitchCase condValue default
                                cases))
                            codeOverride stateAfterCond =
                          .ok final := by
                      simpa [exec, source, hCond] using hRun
                    have hBody' :=
                      exec_mono model prim hPrim hFuelLe hBody
                    simpa [exec, source, hCond'] using hBody'
            | For cond post body =>
                simpa [exec, source] using
                  (loop_mono model prim hPrim hFuelLe
                    (by simpa [exec, source] using hRun))
            | Continue =>
                simpa [exec, source] using hRun
            | Break =>
                simpa [exec, source] using hRun
            | Leave =>
                simpa [exec, source] using hRun
  termination_by
    fuel _fuel' stmt _codeOverride _state _final _hLe _hRun =>
      (fuel, 7, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem loop_mono {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {cond : EvmYul.Yul.Ast.Expr}
        {post body : List EvmYul.Yul.Ast.Stmt}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {state final : σ},
        fuel ≤ fuel' →
        loop model prim fuel cond post body codeOverride state = .ok final →
        loop model prim fuel' cond post body codeOverride state = .ok final := by
    intro fuel fuel' cond post body codeOverride state final hLe hRun
    cases fuel with
    | zero =>
        simp [loop, fail] at hRun
    | succ fuel =>
        cases fuel with
        | zero =>
            simp [loop, fail] at hRun
        | succ fuel =>
            cases fuel' with
            | zero =>
                omega
            | succ fuel' =>
                cases fuel' with
                | zero =>
                    omega
                | succ fuel' =>
                    have hFuelLe : fuel ≤ fuel' := by omega
                    let source := model.source state
                    let stateAtCond :=
                      model.withSource state (EvmYul.Yul.State.mkOk source)
                    cases hCond :
                        Effectful.eval model prim fuel cond codeOverride
                          stateAtCond with
                    | error failure =>
                        simp [loop, source, stateAtCond, hCond] at hRun
                    | ok result =>
                        rcases result with ⟨stateAfterCond, condValue⟩
                        have hCond' :
                            Effectful.eval model prim fuel' cond codeOverride
                                stateAtCond =
                              .ok (stateAfterCond, condValue) :=
                          eval_mono model prim hPrim hFuelLe hCond
                        by_cases hZero : condValue = ⟨0⟩
                        · simpa [loop, source, stateAtCond, hCond, hCond',
                            hZero] using hRun
                        · cases hBody :
                              exec model prim fuel (.Block body) codeOverride
                                stateAfterCond with
                          | error failure =>
                              simp [loop, source, stateAtCond, hCond, hZero,
                                hBody] at hRun
                          | ok stateAfterBody =>
                              have hBody' :
                                  exec model prim fuel' (.Block body)
                                      codeOverride stateAfterCond =
                                    .ok stateAfterBody :=
                                exec_mono model prim hPrim hFuelLe hBody
                              let bodySource := model.source stateAfterBody
                              cases hBodySource : bodySource with
                              | OutOfFuel =>
                                  simpa [loop, source, stateAtCond, hCond,
                                    hCond', hZero, hBody, hBody', bodySource,
                                    hBodySource] using hRun
                              | Checkpoint jump =>
                                  cases jump with
                                  | Break shared vars =>
                                      simpa [loop, source, stateAtCond, hCond,
                                        hCond', hZero, hBody, hBody',
                                        bodySource, hBodySource] using hRun
                                  | Leave shared vars =>
                                      simpa [loop, source, stateAtCond, hCond,
                                        hCond', hZero, hBody, hBody',
                                        bodySource, hBodySource] using hRun
                                  | Continue shared vars =>
                                      cases hPost :
                                            exec model prim fuel (.Block post)
                                              codeOverride
                                              (model.withSource stateAfterBody
                                                bodySource.reviveJump) with
                                      | error failure =>
                                          simp [hBodySource] at hPost
                                          simp [loop, source, stateAtCond,
                                            hCond, hZero, hBody, bodySource,
                                            hBodySource, hPost] at hRun
                                      | ok stateAfterPost =>
                                          have hPost' :
                                              exec model prim fuel'
                                                  (.Block post) codeOverride
                                                  (model.withSource
                                                    stateAfterBody
                                                    bodySource.reviveJump) =
                                                .ok stateAfterPost :=
                                            exec_mono model prim hPrim hFuelLe
                                              hPost
                                          simp [bodySource, hBodySource]
                                            at hPost hPost'
                                          have hTail :
                                              (match
                                                  model.source stateAfterPost
                                                with
                                                | .OutOfFuel =>
                                                    Except.ok
                                                      (model.withSource
                                                        stateAfterPost
                                                        (EvmYul.Yul.State.overwrite?
                                                          (model.source
                                                            stateAfterPost)
                                                          source))
                                                | .Checkpoint (.Leave _ _) =>
                                                    Except.ok
                                                      (model.withSource
                                                        stateAfterPost
                                                        (EvmYul.Yul.State.overwrite?
                                                          (model.source
                                                            stateAfterPost)
                                                          source))
                                                | _ =>
                                                    (fun stateAfterLoop =>
                                                      model.withSource
                                                        stateAfterLoop
                                                        (EvmYul.Yul.State.overwrite?
                                                          (model.source
                                                            stateAfterLoop)
                                                          source)) <$>
                                                      exec model prim fuel
                                                        (.For cond post body)
                                                        codeOverride
                                                        (model.withSource
                                                          stateAfterPost
                                                          (EvmYul.Yul.State.overwrite?
                                                            (model.source
                                                              stateAfterPost)
                                                            source))
                                                : Result σ σ) =
                                                Except.ok final := by
                                            simpa [loop, source, stateAtCond,
                                              hCond, hZero, hBody, bodySource,
                                              hBodySource, hPost, Bind.bind,
                                              Except.bind, Except.map] using hRun
                                          have hTail' :=
                                            loop_post_mono_finish
                                              model prim hPrim hFuelLe hTail
                                          simpa [loop, source, stateAtCond,
                                            hCond', hZero, hBody', bodySource,
                                            hBodySource, hPost', Bind.bind,
                                            Except.bind, Except.map] using hTail'
                              | Ok shared vars =>
                                  cases hPost :
                                      exec model prim fuel (.Block post)
                                        codeOverride
                                        (model.withSource stateAfterBody
                                          bodySource.reviveJump) with
                                  | error failure =>
                                      simp [hBodySource] at hPost
                                      simp [loop, source, stateAtCond, hCond,
                                        hZero, hBody, bodySource,
                                        hBodySource, hPost] at hRun
                                  | ok stateAfterPost =>
                                      have hPost' :
                                          exec model prim fuel' (.Block post)
                                              codeOverride
                                              (model.withSource stateAfterBody
                                                bodySource.reviveJump) =
                                            .ok stateAfterPost :=
                                        exec_mono model prim hPrim hFuelLe
                                          hPost
                                      simp [bodySource, hBodySource]
                                        at hPost hPost'
                                      have hTail :
                                          (match model.source stateAfterPost with
                                          | .OutOfFuel =>
                                              Except.ok
                                                (model.withSource stateAfterPost
                                                  (EvmYul.Yul.State.overwrite?
                                                    (model.source
                                                      stateAfterPost)
                                                    source))
                                          | .Checkpoint (.Leave _ _) =>
                                              Except.ok
                                                (model.withSource stateAfterPost
                                                  (EvmYul.Yul.State.overwrite?
                                                    (model.source
                                                      stateAfterPost)
                                                    source))
                                          | _ =>
                                              (fun stateAfterLoop =>
                                                model.withSource
                                                  stateAfterLoop
                                                  (EvmYul.Yul.State.overwrite?
                                                    (model.source
                                                      stateAfterLoop)
                                                    source)) <$>
                                                exec model prim fuel
                                                  (.For cond post body)
                                                  codeOverride
                                                  (model.withSource
                                                    stateAfterPost
                                                    (EvmYul.Yul.State.overwrite?
                                                      (model.source
                                                        stateAfterPost)
                                                      source))
                                          : Result σ σ) =
                                            Except.ok final := by
                                        simpa [loop, source, stateAtCond,
                                          hCond, hZero, hBody, bodySource,
                                          hBodySource, hPost, Bind.bind,
                                          Except.bind, Except.map] using hRun
                                      have hTail' :=
                                        loop_post_mono_finish
                                          model prim hPrim hFuelLe hTail
                                      simpa [loop, source, stateAtCond,
                                        hCond', hZero, hBody', bodySource,
                                        hBodySource, hPost', Bind.bind,
                                        Except.bind, Except.map] using hTail'
  termination_by
    fuel _fuel' cond post body _codeOverride _state _final _hLe _hRun =>
      (fuel, 9, sizeOf cond + sizeOf post + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem loop_post_mono_finish {σ : Type}
      (model : StateModel σ) (prim : PrimitiveSemantics σ)
      (hPrim : prim.SuccessMonotone) :
      ∀ {fuel fuel' : Nat} {cond : EvmYul.Yul.Ast.Expr}
        {post body : List EvmYul.Yul.Ast.Stmt}
        {codeOverride : Option EvmYul.Yul.Ast.YulContract}
        {stateAfterPost : σ} {source : EvmYul.Yul.State} {final : σ},
        fuel ≤ fuel' →
        (match model.source stateAfterPost with
        | .OutOfFuel =>
            Except.ok
              (model.withSource stateAfterPost
                ((model.source stateAfterPost).overwrite? source))
        | .Checkpoint (.Leave _ _) =>
            Except.ok
              (model.withSource stateAfterPost
                ((model.source stateAfterPost).overwrite? source))
        | _ =>
            (fun stateAfterLoop =>
              model.withSource stateAfterLoop
                ((model.source stateAfterLoop).overwrite? source)) <$>
              exec model prim fuel (.For cond post body) codeOverride
                (model.withSource stateAfterPost
                  ((model.source stateAfterPost).overwrite? source))
          : Result σ σ) =
          Except.ok final →
        (match model.source stateAfterPost with
        | .OutOfFuel =>
            Except.ok
              (model.withSource stateAfterPost
                ((model.source stateAfterPost).overwrite? source))
        | .Checkpoint (.Leave _ _) =>
            Except.ok
              (model.withSource stateAfterPost
                ((model.source stateAfterPost).overwrite? source))
        | _ =>
            (fun stateAfterLoop =>
              model.withSource stateAfterLoop
                ((model.source stateAfterLoop).overwrite? source)) <$>
              exec model prim fuel' (.For cond post body) codeOverride
                (model.withSource stateAfterPost
                  ((model.source stateAfterPost).overwrite? source))
          : Result σ σ) =
          Except.ok final := by
    intro fuel fuel' cond post body codeOverride stateAfterPost source final
      hFuelLe hRun
    let postSource := model.source stateAfterPost
    let sourceAfterPost := postSource.overwrite? source
    cases hPostSource : postSource with
    | OutOfFuel =>
        dsimp [postSource, sourceAfterPost] at hPostSource hRun ⊢
        rw [hPostSource] at hRun ⊢
        exact hRun
    | Checkpoint jump =>
        cases jump with
        | Leave shared vars =>
            dsimp [postSource, sourceAfterPost] at hPostSource hRun ⊢
            rw [hPostSource] at hRun ⊢
            exact hRun
        | Break shared vars =>
            cases hLoop :
                exec model prim fuel (.For cond post body) codeOverride
                  (model.withSource stateAfterPost sourceAfterPost) with
            | error failure =>
                dsimp [postSource, sourceAfterPost] at hPostSource hLoop hRun ⊢
                rw [hPostSource] at hLoop hRun ⊢
                simp [hLoop] at hRun
            | ok stateAfterLoop =>
                have hLoop' :
                    exec model prim fuel' (.For cond post body) codeOverride
                        (model.withSource stateAfterPost sourceAfterPost) =
                      .ok stateAfterLoop :=
                  exec_mono model prim hPrim hFuelLe hLoop
                dsimp [postSource, sourceAfterPost] at hPostSource hLoop hLoop' hRun ⊢
                rw [hPostSource] at hLoop hLoop' hRun ⊢
                simpa [hLoop, hLoop'] using hRun
        | Continue shared vars =>
            cases hLoop :
                exec model prim fuel (.For cond post body) codeOverride
                  (model.withSource stateAfterPost sourceAfterPost) with
            | error failure =>
                dsimp [postSource, sourceAfterPost] at hPostSource hLoop hRun ⊢
                rw [hPostSource] at hLoop hRun ⊢
                simp [hLoop] at hRun
            | ok stateAfterLoop =>
                have hLoop' :
                    exec model prim fuel' (.For cond post body) codeOverride
                        (model.withSource stateAfterPost sourceAfterPost) =
                      .ok stateAfterLoop :=
                  exec_mono model prim hPrim hFuelLe hLoop
                dsimp [postSource, sourceAfterPost] at hPostSource hLoop hLoop' hRun ⊢
                rw [hPostSource] at hLoop hLoop' hRun ⊢
                simpa [hLoop, hLoop'] using hRun
    | Ok shared vars =>
        cases hLoop :
            exec model prim fuel (.For cond post body) codeOverride
              (model.withSource stateAfterPost sourceAfterPost) with
        | error failure =>
            dsimp [postSource, sourceAfterPost] at hPostSource hLoop hRun ⊢
            rw [hPostSource] at hLoop hRun ⊢
            simp [hLoop] at hRun
        | ok stateAfterLoop =>
            have hLoop' :
                exec model prim fuel' (.For cond post body) codeOverride
                    (model.withSource stateAfterPost sourceAfterPost) =
                  .ok stateAfterLoop :=
              exec_mono model prim hPrim hFuelLe hLoop
            dsimp [postSource, sourceAfterPost] at hPostSource hLoop hLoop' hRun ⊢
            rw [hPostSource] at hLoop hLoop' hRun ⊢
            simpa [hLoop, hLoop'] using hRun
  termination_by
    fuel _fuel' cond post body _codeOverride _stateAfterPost _source _final
        _hFuelLe _hRun =>
      (fuel, 8, sizeOf cond + sizeOf post + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals
      exact Prod.Lex.right _
        (Prod.Lex.left _ _ (by omega))

end

end Effectful
end Source
end Yul
end EvmCompiler
