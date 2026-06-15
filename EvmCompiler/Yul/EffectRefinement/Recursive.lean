import EvmCompiler.Yul.EffectRefinement.Loop

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

/--
All canonical Yul control computations at one source-fuel index refine after
replacing the primitive handler.

This is an internally constructed induction package, not an assumption at any
compiler theorem boundary.
-/
structure RefinementAt
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) : Prop where
  evalTail :
    ∀ args codeOverride sourceInput targetInput,
      Result.Refines sourceInput targetInput →
      Result.Refines
        (Effectful.evalTail model sourcePrim fuel args
          codeOverride sourceInput)
        (Effectful.evalTail model targetPrim fuel args
          codeOverride targetInput)
  evalArgs :
    ∀ args codeOverride state,
      Result.Refines
        (Effectful.evalArgs model sourcePrim fuel args
          codeOverride state)
        (Effectful.evalArgs model targetPrim fuel args
          codeOverride state)
  evalValues :
    ∀ expr codeOverride state,
      Result.Refines
        (Effectful.evalValues model sourcePrim fuel expr
          codeOverride state)
        (Effectful.evalValues model targetPrim fuel expr
          codeOverride state)
  eval :
    ∀ expr codeOverride state,
      Result.Refines
        (Effectful.eval model sourcePrim fuel expr
          codeOverride state)
        (Effectful.eval model targetPrim fuel expr
          codeOverride state)
  call :
    ∀ args functionName? codeOverride state,
      Result.Refines
        (Effectful.call model sourcePrim fuel args functionName?
          codeOverride state)
        (Effectful.call model targetPrim fuel args functionName?
          codeOverride state)
  callDispatcher :
    ∀ codeOverride state,
      Result.Refines
        (Effectful.callDispatcher model sourcePrim fuel
          codeOverride state)
        (Effectful.callDispatcher model targetPrim fuel
          codeOverride state)
  execSeq :
    ∀ stmts codeOverride state,
      Result.Refines
        (Effectful.execSeq model sourcePrim fuel stmts
          codeOverride state)
        (Effectful.execSeq model targetPrim fuel stmts
          codeOverride state)
  exec :
    ∀ stmt codeOverride state,
      Result.Refines
        (Effectful.exec model sourcePrim fuel stmt
          codeOverride state)
        (Effectful.exec model targetPrim fuel stmt
          codeOverride state)
  loop :
    ∀ cond post body codeOverride state,
      Result.Refines
        (Effectful.loop model sourcePrim fuel cond post body
          codeOverride state)
        (Effectful.loop model targetPrim fuel cond post body
          codeOverride state)

theorem refinementAt
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (hPrim : sourcePrim.ObservableRefines targetPrim)
    (fuel : Nat) :
    RefinementAt model sourcePrim targetPrim fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          exact
            { evalTail := fun args codeOverride sourceInput targetInput hInput =>
                evalTail_zero_refines model sourcePrim targetPrim
                  args codeOverride hInput
              evalArgs := fun args codeOverride state =>
                evalArgs_zero_refines model sourcePrim targetPrim
                  args codeOverride state
              evalValues := fun expr codeOverride state => by
                simpa [evalValues] using
                  (Result.Refines.refl
                    (fail state .OutOfFuel :
                      Result σ (σ × List Word)))
              eval := fun expr codeOverride state =>
                eval_refines_of_evalValues model sourcePrim targetPrim
                  0 expr codeOverride state
                  (by
                    simpa [evalValues] using
                      (Result.Refines.refl
                        (fail state .OutOfFuel :
                          Result σ (σ × List Word))))
              call := fun args functionName? codeOverride state =>
                call_zero_refines model sourcePrim targetPrim
                  args functionName? codeOverride state
              callDispatcher := fun codeOverride state =>
                callDispatcher_zero_refines model sourcePrim targetPrim
                  codeOverride state
              execSeq := fun stmts codeOverride state =>
                execSeq_zero_refines model sourcePrim targetPrim
                  stmts codeOverride state
              exec := fun stmt codeOverride state =>
                exec_zero_refines model sourcePrim targetPrim
                  stmt codeOverride state
              loop := fun cond post body codeOverride state =>
                loop_zero_refines model sourcePrim targetPrim
                  cond post body codeOverride state }
      | succ previous =>
          have hPrevious :
              RefinementAt model sourcePrim targetPrim previous :=
            ih previous (Nat.lt_succ_self previous)
          let evalTailRefines :
              ∀ args codeOverride sourceInput targetInput,
                Result.Refines sourceInput targetInput →
                Result.Refines
                  (Effectful.evalTail model sourcePrim previous.succ args
                    codeOverride sourceInput)
                  (Effectful.evalTail model targetPrim previous.succ args
                    codeOverride targetInput) :=
            fun args codeOverride sourceInput targetInput hInput =>
              evalTail_succ_refines model sourcePrim targetPrim previous
                args codeOverride hInput
                (fun state => hPrevious.evalArgs args codeOverride state)
          let evalArgsRefines :
              ∀ args codeOverride state,
                Result.Refines
                  (Effectful.evalArgs model sourcePrim previous.succ args
                    codeOverride state)
                  (Effectful.evalArgs model targetPrim previous.succ args
                    codeOverride state) :=
            fun args codeOverride state => by
              cases args with
              | nil =>
                  exact evalArgs_nil_succ_refines model
                    sourcePrim targetPrim previous codeOverride state
              | cons arg rest =>
                  exact evalArgs_cons_succ_refines model
                    sourcePrim targetPrim previous arg rest
                    codeOverride state
                    (hPrevious.evalTail rest codeOverride
                      (Effectful.eval model sourcePrim previous arg
                        codeOverride state)
                      (Effectful.eval model targetPrim previous arg
                        codeOverride state)
                      (hPrevious.eval arg codeOverride state))
          let evalValuesRefines :
              ∀ expr codeOverride state,
                Result.Refines
                  (Effectful.evalValues model sourcePrim previous.succ expr
                    codeOverride state)
                  (Effectful.evalValues model targetPrim previous.succ expr
                    codeOverride state) :=
            fun expr codeOverride state => by
              cases expr with
              | Call callee args =>
                  cases callee with
                  | inl op =>
                      exact evalValues_primitive_succ_refines model
                        sourcePrim targetPrim hPrim previous op args
                        codeOverride state
                        (hPrevious.evalArgs args.reverse
                          codeOverride state)
                  | inr functionName =>
                      exact evalValues_function_succ_refines model
                        sourcePrim targetPrim previous functionName args
                        codeOverride state
                        (hPrevious.evalArgs args.reverse
                          codeOverride state)
                        (fun callArgs callState =>
                          hPrevious.call callArgs (some functionName)
                            codeOverride callState)
              | Var name =>
                  exact evalValues_var_succ_refines model
                    sourcePrim targetPrim previous name codeOverride state
              | Lit value =>
                  exact evalValues_lit_succ_refines model
                    sourcePrim targetPrim previous value codeOverride state
          let evalRefines :
              ∀ expr codeOverride state,
                Result.Refines
                  (Effectful.eval model sourcePrim previous.succ expr
                    codeOverride state)
                  (Effectful.eval model targetPrim previous.succ expr
                    codeOverride state) :=
            fun expr codeOverride state =>
              eval_refines_of_evalValues model sourcePrim targetPrim
                previous.succ expr codeOverride state
                (evalValuesRefines expr codeOverride state)
          let callRefines :
              ∀ args functionName? codeOverride state,
                Result.Refines
                  (Effectful.call model sourcePrim previous.succ args
                    functionName? codeOverride state)
                  (Effectful.call model targetPrim previous.succ args
                    functionName? codeOverride state) :=
            fun args functionName? codeOverride state =>
              call_succ_refines model sourcePrim targetPrim previous
                args functionName? codeOverride state
                (fun body entryState =>
                  hPrevious.exec (.Block body) codeOverride entryState)
          let callDispatcherRefines :
              ∀ codeOverride state,
                Result.Refines
                  (Effectful.callDispatcher model sourcePrim previous.succ
                    codeOverride state)
                  (Effectful.callDispatcher model targetPrim previous.succ
                    codeOverride state) :=
            fun codeOverride state =>
              callDispatcher_succ_refines model sourcePrim targetPrim
                previous codeOverride state
                (hPrevious.exec
                  (.Block
                    [(model.source state).executionEnv.code.dispatcher])
                  codeOverride
                  (model.withSource state
                    (EvmYul.Yul.State.mkOk
                      ((model.source state).initcall [] [] []))))
          let execSeqRefines :
              ∀ stmts codeOverride state,
                Result.Refines
                  (Effectful.execSeq model sourcePrim previous.succ stmts
                    codeOverride state)
                  (Effectful.execSeq model targetPrim previous.succ stmts
                    codeOverride state) :=
            fun stmts codeOverride state => by
              cases stmts with
              | nil =>
                  exact execSeq_nil_succ_refines model
                    sourcePrim targetPrim previous codeOverride state
              | cons stmt rest =>
                  exact execSeq_cons_succ_refines model
                    sourcePrim targetPrim previous stmt rest
                    codeOverride state
                    (hPrevious.exec stmt codeOverride state)
                    (fun stateAfterStmt =>
                      hPrevious.execSeq rest codeOverride stateAfterStmt)
          let execRefines :
              ∀ stmt codeOverride state,
                Result.Refines
                  (Effectful.exec model sourcePrim previous.succ stmt
                    codeOverride state)
                  (Effectful.exec model targetPrim previous.succ stmt
                    codeOverride state) :=
            fun stmt codeOverride state => by
              cases stmt with
              | Block stmts =>
                  exact exec_block_succ_refines model
                    sourcePrim targetPrim previous stmts
                    codeOverride state
                    (hPrevious.execSeq stmts codeOverride state)
              | Let vars expr? =>
                  cases expr? with
                  | none =>
                      exact exec_let_none_succ_refines model
                        sourcePrim targetPrim previous vars
                        codeOverride state
                  | some expr =>
                      exact exec_let_some_succ_refines model
                        sourcePrim targetPrim previous vars expr
                        codeOverride state
                        (hPrevious.evalValues expr codeOverride state)
              | Assign vars expr =>
                  exact exec_assign_succ_refines model
                    sourcePrim targetPrim previous vars expr
                    codeOverride state
                    (hPrevious.evalValues expr codeOverride state)
              | If cond body =>
                  exact exec_if_succ_refines model
                    sourcePrim targetPrim previous cond body
                    codeOverride state
                    (hPrevious.eval cond codeOverride state)
                    (fun stateAfterCond =>
                      hPrevious.exec (.Block body)
                        codeOverride stateAfterCond)
              | ExprStmtCall expr =>
                  cases expr with
                  | Call callee args =>
                      cases callee with
                      | inl op =>
                          exact exec_exprPrimitive_succ_refines model
                            sourcePrim targetPrim hPrim previous op args
                            codeOverride state
                            (hPrevious.evalArgs args.reverse
                              codeOverride state)
                      | inr functionName =>
                          cases previous with
                          | zero =>
                              exact exec_exprFunction_one_refines model
                                sourcePrim targetPrim functionName args
                                codeOverride state
                          | succ lower =>
                              have hLower :
                                  RefinementAt model sourcePrim targetPrim
                                    lower :=
                                ih lower (by omega)
                              exact
                                exec_exprFunction_succ_succ_refines model
                                  sourcePrim targetPrim lower functionName
                                  args codeOverride state
                                  (hPrevious.evalArgs args.reverse
                                    codeOverride state)
                                  (fun callArgs callState =>
                                    hLower.call callArgs
                                      (some functionName)
                                      codeOverride callState)
                  | Var name =>
                      exact exec_exprInvalid_succ_refines model
                        sourcePrim targetPrim previous (.Var name)
                        (by
                          constructor
                          · intro op args hEq
                            cases hEq
                          · intro functionName args hEq
                            cases hEq)
                        codeOverride state
                  | Lit value =>
                      exact exec_exprInvalid_succ_refines model
                        sourcePrim targetPrim previous (.Lit value)
                        (by
                          constructor
                          · intro op args hEq
                            cases hEq
                          · intro functionName args hEq
                            cases hEq)
                        codeOverride state
              | Switch cond cases default =>
                  exact exec_switch_succ_refines model
                    sourcePrim targetPrim previous cond cases default
                    codeOverride state
                    (hPrevious.eval cond codeOverride state)
                    (fun condValue stateAfterCond =>
                      hPrevious.exec
                        (.Block
                          (EvmYul.Yul.selectSwitchCase
                            condValue default cases))
                        codeOverride stateAfterCond)
              | For cond post body =>
                  exact exec_for_succ_refines model
                    sourcePrim targetPrim previous cond post body
                    codeOverride state
                    (hPrevious.loop cond post body codeOverride state)
              | Continue =>
                  exact exec_continue_succ_refines model
                    sourcePrim targetPrim previous codeOverride state
              | Break =>
                  exact exec_break_succ_refines model
                    sourcePrim targetPrim previous codeOverride state
              | Leave =>
                  exact exec_leave_succ_refines model
                    sourcePrim targetPrim previous codeOverride state
          let loopRefines :
              ∀ cond post body codeOverride state,
                Result.Refines
                  (Effectful.loop model sourcePrim previous.succ
                    cond post body codeOverride state)
                  (Effectful.loop model targetPrim previous.succ
                    cond post body codeOverride state) :=
            fun cond post body codeOverride state => by
              cases previous with
              | zero =>
                  exact loop_one_refines model sourcePrim targetPrim
                    cond post body codeOverride state
              | succ lower =>
                  have hLower :
                      RefinementAt model sourcePrim targetPrim lower :=
                    ih lower (by omega)
                  exact loop_succ_succ_refines model
                    sourcePrim targetPrim lower cond post body
                    codeOverride state
                    (hLower.eval cond codeOverride
                      (model.withSource state
                        (EvmYul.Yul.State.mkOk (model.source state))))
                    (fun stateAfterCond =>
                      hLower.exec (.Block body)
                        codeOverride stateAfterCond)
                    (fun stateAfterBody =>
                      hLower.exec (.Block post) codeOverride
                        (model.withSource stateAfterBody
                          (model.source stateAfterBody).reviveJump))
                    (fun stateAfterPost sourceAfterPost =>
                      hLower.exec (.For cond post body) codeOverride
                        (model.withSource stateAfterPost sourceAfterPost))
          exact
            { evalTail := evalTailRefines
              evalArgs := evalArgsRefines
              evalValues := evalValuesRefines
              eval := evalRefines
              call := callRefines
              callDispatcher := callDispatcherRefines
              execSeq := execSeqRefines
              exec := execRefines
              loop := loopRefines }

theorem callDispatcher_refines
    {σ : Type} (model : StateModel σ)
    {sourcePrim targetPrim : PrimitiveSemantics σ}
    (hPrim : sourcePrim.ObservableRefines targetPrim)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (Effectful.callDispatcher model sourcePrim fuel
        codeOverride state)
      (Effectful.callDispatcher model targetPrim fuel
        codeOverride state) :=
  (refinementAt model sourcePrim targetPrim hPrim fuel).callDispatcher
    codeOverride state

end Effectful
end Source
end Yul
end EvmCompiler
