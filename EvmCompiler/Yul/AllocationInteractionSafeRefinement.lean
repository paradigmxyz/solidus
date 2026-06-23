import EvmCompiler.Yul.AllocationInteractionSafeSemantics

/-!
Successful-or-terminal refinement for canonical guarded Yul semantics.

The proof is over the shared parameterized control interpreter. It establishes
that enforcing allocation safety at the primitive boundary does not alter any
accepted open interaction tree; no control evaluator is reimplemented.
-/

namespace EvmCompiler
namespace Yul
namespace AllocationInteractionSafeRefinement

open AllocationInteractionSafeSemantics

noncomputable section

abbrev SafePrim (contract : MemoryContract.Contract) :=
  AllocationInteractionSafeSemantics.primitiveSemantics contract

/-- Equality package for every mutually recursive canonical Yul computation at
one fuel index. Each field is conditional only on the actual guarded tree. -/
structure RefinementAt (contract : MemoryContract.Contract)
    (fuel : Nat) : Prop where
  evalArgs : ∀ args code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.evalArgs Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel args code state) →
      Yul.Source.Effectful.evalArgs Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel args code state =
        Yul.InteractionSemantics.evalArgs fuel args code state
  evalValues : ∀ expr code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.evalValues Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel expr code state) →
      Yul.Source.Effectful.evalValues Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel expr code state =
        Yul.InteractionSemantics.evalValues fuel expr code state
  eval : ∀ expr code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.eval Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel expr code state) →
      Yul.Source.Effectful.eval Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel expr code state =
        Yul.InteractionSemantics.eval fuel expr code state
  call : ∀ args functionName code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.call Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel args functionName code state) →
      Yul.Source.Effectful.call Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel args functionName code state =
        Yul.InteractionSemantics.call fuel args functionName code state
  callDispatcher : ∀ code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.callDispatcher
          Yul.InteractionSemantics.stateModel (SafePrim contract)
          fuel code state) →
      Yul.Source.Effectful.callDispatcher
          Yul.InteractionSemantics.stateModel (SafePrim contract)
          fuel code state =
        Yul.Source.Effectful.callDispatcher
          Yul.InteractionSemantics.stateModel
          Yul.InteractionSemantics.primitiveSemantics fuel code state
  execSeq : ∀ stmts code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.execSeq Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel stmts code state) →
      Yul.Source.Effectful.execSeq Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel stmts code state =
        Yul.InteractionSemantics.execSeq fuel stmts code state
  exec : ∀ stmt code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.exec Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel stmt code state) →
      Yul.Source.Effectful.exec Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel stmt code state =
        Yul.InteractionSemantics.exec fuel stmt code state
  loop : ∀ cond post body code state,
    Simulation.Interaction.AllDone Completed
        (Yul.Source.Effectful.loop Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel cond post body code state) →
      Yul.Source.Effectful.loop Yul.InteractionSemantics.stateModel
          (SafePrim contract) fuel cond post body code state =
        Yul.InteractionSemantics.loop fuel cond post body code state

set_option maxHeartbeats 2000000 in
theorem refinementAt (contract : MemoryContract.Contract) (fuel : Nat) :
    RefinementAt contract fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      cases fuel with
      | zero =>
          refine
            { evalArgs := ?_
              evalValues := ?_
              eval := ?_
              call := ?_
              callDispatcher := ?_
              execSeq := ?_
              exec := ?_
              loop := ?_ }
          all_goals intros
          all_goals
            simp [Yul.InteractionSemantics.evalArgs,
              Yul.InteractionSemantics.evalValues,
              Yul.InteractionSemantics.eval,
              Yul.InteractionSemantics.call,
              Yul.InteractionSemantics.execSeq,
              Yul.InteractionSemantics.exec,
              Yul.InteractionSemantics.loop,
              Yul.Source.Effectful.evalArgs,
              Yul.Source.Effectful.evalValues,
              Yul.Source.Effectful.eval,
              Yul.Source.Effectful.call,
              Yul.Source.Effectful.callDispatcher,
              Yul.Source.Effectful.execSeq,
              Yul.Source.Effectful.exec,
              Yul.Source.Effectful.loop]
      | succ previous =>
          have hPrevious : RefinementAt contract previous :=
            ih previous (Nat.lt_succ_self previous)
          let evalArgsEq : ∀ args code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.evalArgs
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ args code state) →
                Yul.Source.Effectful.evalArgs
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ args code state =
                  Yul.InteractionSemantics.evalArgs
                    previous.succ args code state := by
            intro args code state hCompleted
            unfold Yul.InteractionSemantics.evalArgs
              Yul.Source.Canonical.evalArgs
            cases args with
            | nil => simp [Yul.Source.Effectful.evalArgs]
            | cons head rest =>
                cases previous with
                | zero =>
                    simp only [Yul.Source.Effectful.evalArgs,
                      Yul.Source.Effectful.evalTail] at hCompleted ⊢
                    apply bind_eq_of_completed hCompleted
                    · exact hPrevious.eval head code state
                    · intro _ _
                      rfl
                | succ lower =>
                    have hLower : RefinementAt contract lower :=
                      ih lower (by omega)
                    simp only [Yul.Source.Effectful.evalArgs,
                      Yul.Source.Effectful.evalTail] at hCompleted ⊢
                    apply bind_eq_of_completed hCompleted
                    · exact hPrevious.eval head code state
                    · intro headResult hTail
                      apply bind_eq_of_completed hTail
                      · exact hLower.evalArgs rest code headResult.1
                      · intro _ _
                        rfl
          let evalValuesEq : ∀ expr code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.evalValues
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ expr code state) →
                Yul.Source.Effectful.evalValues
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ expr code state =
                  Yul.InteractionSemantics.evalValues
                    previous.succ expr code state := by
            intro expr code state hCompleted
            unfold Yul.InteractionSemantics.evalValues
              Yul.Source.Canonical.evalValues
            cases expr with
            | Var name => simp [Yul.Source.Effectful.evalValues]
            | Lit value => simp [Yul.Source.Effectful.evalValues]
            | Call callee args =>
                cases callee with
                | inl prim =>
                    simp only [Yul.Source.Effectful.evalValues] at hCompleted ⊢
                    apply bind_eq_of_completed hCompleted
                    · exact hPrevious.evalArgs args.reverse code state
                    · intro result hPrimitive
                      exact
                        AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary_of_completed
                          hPrimitive
                | inr functionName =>
                    simp only [Yul.Source.Effectful.evalValues] at hCompleted ⊢
                    apply bind_eq_of_completed hCompleted
                    · exact hPrevious.evalArgs args.reverse code state
                    · intro result hCall
                      exact hPrevious.call result.2.reverse
                        (some functionName) code result.1 hCall
          let evalEq : ∀ expr code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.eval
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ expr code state) →
                Yul.Source.Effectful.eval
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ expr code state =
                  Yul.InteractionSemantics.eval
                    previous.succ expr code state := by
            intro expr code state hCompleted
            unfold Yul.InteractionSemantics.eval
              Yul.Source.Canonical.eval
            simp only [Yul.Source.Effectful.eval] at hCompleted ⊢
            apply bind_eq_of_completed hCompleted
            · exact evalValuesEq expr code state
            · intro _ _
              rfl
          let callEq : ∀ args functionName code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.call
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ args functionName code state) →
                Yul.Source.Effectful.call
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ args functionName code state =
                  Yul.InteractionSemantics.call
                    previous.succ args functionName code state := by
            intro args functionName code state hCompleted
            unfold Yul.InteractionSemantics.call
              Yul.Source.Canonical.call
            simp only [Yul.Source.Effectful.call] at hCompleted ⊢
            split <;> rename_i hCode
            · rfl
            · simp only [hCode] at hCompleted
              split <;> rename_i hFunction
              · rfl
              · simp only [hFunction] at hCompleted
                rename_i function
                cases function with
                | Def params returns body =>
                    apply bind_eq_of_completed hCompleted
                    · exact hPrevious.exec (.Block body) code _
                    · intro _ _
                      rfl
          let callDispatcherEq : ∀ code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.callDispatcher
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ code state) →
                Yul.Source.Effectful.callDispatcher
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ code state =
                  Yul.Source.Effectful.callDispatcher
                    Yul.InteractionSemantics.stateModel
                    Yul.InteractionSemantics.primitiveSemantics
                    previous.succ code state := by
            intro code state hCompleted
            simp only [Yul.Source.Effectful.callDispatcher] at hCompleted ⊢
            apply bind_eq_of_completed hCompleted
            · exact hPrevious.exec _ code _
            · intro _ _
              rfl
          let execSeqEq : ∀ stmts code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.execSeq
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ stmts code state) →
                Yul.Source.Effectful.execSeq
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ stmts code state =
                  Yul.InteractionSemantics.execSeq
                    previous.succ stmts code state := by
            intro stmts code state hCompleted
            unfold Yul.InteractionSemantics.execSeq
              Yul.Source.Canonical.execSeq
            cases stmts with
            | nil => simp [Yul.Source.Effectful.execSeq]
            | cons head rest =>
                simp only [Yul.Source.Effectful.execSeq] at hCompleted ⊢
                apply bind_eq_of_completed hCompleted
                · exact hPrevious.exec head code state
                · intro stateAfter hRest
                  cases stateAfter with
                  | OutOfFuel => rfl
                  | Checkpoint jump => rfl
                  | Ok shared vars =>
                      change
                        Yul.Source.Effectful.execSeq
                            Yul.InteractionSemantics.stateModel
                            (SafePrim contract) previous rest code
                            (.Ok shared vars) =
                          Yul.Source.Effectful.execSeq
                            Yul.InteractionSemantics.stateModel
                            Yul.InteractionSemantics.primitiveSemantics
                            previous rest code (.Ok shared vars)
                      apply hPrevious.execSeq rest code (.Ok shared vars)
                      simpa [Yul.InteractionSemantics.stateModel] using hRest
          let execEq : ∀ stmt code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.exec
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ stmt code state) →
                Yul.Source.Effectful.exec
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ stmt code state =
                  Yul.InteractionSemantics.exec
                    previous.succ stmt code state := by
            intro stmt code state hCompleted
            unfold Yul.InteractionSemantics.exec
              Yul.Source.Canonical.exec
            cases stmt with
            | Block stmts =>
                simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                apply bind_eq_of_completed hCompleted
                · exact hPrevious.execSeq stmts code state
                · intro _ _
                  rfl
            | Let vars expr? =>
                cases expr? with
                | none => simp [Yul.Source.Effectful.exec]
                | some expr =>
                    simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                    split <;> rename_i hDeclaration
                    · rfl
                    · simp only [hDeclaration] at hCompleted
                      unfold Yul.Source.Effectful.Control.multifill
                      apply bind_eq_of_completed hCompleted
                      · exact hPrevious.evalValues expr code state
                      · intro _ _
                        rfl
            | Assign vars expr =>
                simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                split <;> rename_i hAssignment
                · rfl
                · simp only [hAssignment] at hCompleted
                  unfold Yul.Source.Effectful.Control.multifill
                  apply bind_eq_of_completed hCompleted
                  · exact hPrevious.evalValues expr code state
                  · intro _ _
                    rfl
            | If cond body =>
                simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                apply bind_eq_of_completed hCompleted
                · exact hPrevious.eval cond code state
                · intro result hBody
                  split <;> rename_i hCond
                  · rw [if_pos hCond] at hBody
                    exact hPrevious.exec (.Block body) code result.1 hBody
                  · rfl
            | ExprStmtCall expr =>
                cases expr with
                | Var _ => simp [Yul.Source.Effectful.exec]
                | Lit _ => simp [Yul.Source.Effectful.exec]
                | Call callee args =>
                    cases callee with
                    | inl prim =>
                        simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                        apply bind_eq_of_completed hCompleted
                        · exact hPrevious.evalArgs args.reverse code state
                        · intro result hPrimitive
                          unfold Yul.Source.Effectful.Control.multifill
                          apply bind_eq_of_completed hPrimitive
                          · exact
                              AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary_of_completed
                          · intro _ _
                            rfl
                    | inr functionName =>
                        cases previous with
                        | zero =>
                            simp only [Yul.Source.Effectful.exec]
                              at hCompleted ⊢
                            apply bind_eq_of_completed hCompleted
                            · exact hPrevious.evalArgs args.reverse code state
                            · intro _ _
                              rfl
                        | succ lower =>
                            have hLower : RefinementAt contract lower :=
                              ih lower (by omega)
                            simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                            apply bind_eq_of_completed hCompleted
                            · exact hPrevious.evalArgs args.reverse code state
                            · intro result hCall
                              unfold Yul.Source.Effectful.Control.multifill
                              apply bind_eq_of_completed hCall
                              · exact hLower.call result.2.reverse
                                  (some functionName) code result.1
                              · intro _ _
                                rfl
            | Switch cond cases defaultBody =>
                simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                apply bind_eq_of_completed hCompleted
                · exact hPrevious.eval cond code state
                · intro result hBody
                  exact hPrevious.exec
                    (.Block
                      (EvmYul.Yul.selectSwitchCase result.2 defaultBody cases))
                    code result.1 hBody
            | For cond post body =>
                simp only [Yul.Source.Effectful.exec] at hCompleted ⊢
                exact hPrevious.loop cond post body code state hCompleted
            | Continue => simp [Yul.Source.Effectful.exec]
            | Break => simp [Yul.Source.Effectful.exec]
            | Leave => simp [Yul.Source.Effectful.exec]
          let loopEq : ∀ cond post body code state,
              Simulation.Interaction.AllDone Completed
                  (Yul.Source.Effectful.loop
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ cond post body code state) →
                Yul.Source.Effectful.loop
                    Yul.InteractionSemantics.stateModel (SafePrim contract)
                    previous.succ cond post body code state =
                  Yul.InteractionSemantics.loop
                    previous.succ cond post body code state := by
            intro cond post body code state hCompleted
            unfold Yul.InteractionSemantics.loop
              Yul.Source.Canonical.loop
            cases previous with
            | zero => simp [Yul.Source.Effectful.loop]
            | succ lower =>
                have hLower : RefinementAt contract lower :=
                  ih lower (by omega)
                simp only [Yul.Source.Effectful.loop] at hCompleted ⊢
                apply bind_eq_of_completed hCompleted
                · exact hLower.eval cond code _
                · intro condResult hAfterCond
                  split <;> rename_i hCond
                  · rfl
                  · simp only [hCond] at hAfterCond
                    apply bind_eq_of_completed hAfterCond
                    · exact hLower.exec (.Block body) code condResult.1
                    · intro stateAfterBody hAfterBody
                      cases hBodySource :
                          Yul.InteractionSemantics.stateModel.source
                            stateAfterBody with
                      | OutOfFuel => simp [hBodySource]
                      | Checkpoint jump =>
                          simp only [hBodySource] at hAfterBody ⊢
                          cases jump with
                          | Break _ _ => rfl
                          | Leave _ _ => rfl
                          | Continue _ _ =>
                              apply bind_eq_of_completed hAfterBody
                              · exact hLower.exec (.Block post) code _
                              · intro stateAfterPost hAfterPost
                                cases hPostSource :
                                    Yul.InteractionSemantics.stateModel.source
                                      stateAfterPost with
                                | OutOfFuel => simp [hPostSource]
                                | Checkpoint postJump =>
                                    simp only [hPostSource] at hAfterPost ⊢
                                    cases postJump with
                                    | Leave _ _ => rfl
                                    | Break _ _ | Continue _ _ =>
                                        apply bind_eq_of_completed hAfterPost
                                        · exact hLower.exec
                                            (.For cond post body) code _
                                        · intro _ _
                                          rfl
                                | Ok _ _ =>
                                    simp only [hPostSource] at hAfterPost ⊢
                                    apply bind_eq_of_completed hAfterPost
                                    · exact hLower.exec
                                        (.For cond post body) code _
                                    · intro _ _
                                      rfl
                      | Ok _ _ =>
                          simp only [hBodySource] at hAfterBody ⊢
                          apply bind_eq_of_completed hAfterBody
                          · exact hLower.exec (.Block post) code _
                          · intro stateAfterPost hAfterPost
                            cases hPostSource :
                                Yul.InteractionSemantics.stateModel.source
                                  stateAfterPost with
                            | OutOfFuel => simp [hPostSource]
                            | Checkpoint postJump =>
                                simp only [hPostSource] at hAfterPost ⊢
                                cases postJump with
                                | Leave _ _ => rfl
                                | Break _ _ | Continue _ _ =>
                                    apply bind_eq_of_completed hAfterPost
                                    · exact hLower.exec
                                        (.For cond post body) code _
                                    · intro _ _
                                      rfl
                            | Ok _ _ =>
                                simp only [hPostSource] at hAfterPost ⊢
                                apply bind_eq_of_completed hAfterPost
                                · exact hLower.exec
                                    (.For cond post body) code _
                                · intro _ _
                                  rfl
          exact
            { evalArgs := evalArgsEq
              evalValues := evalValuesEq
              eval := evalEq
              call := callEq
              callDispatcher := callDispatcherEq
              execSeq := execSeqEq
              exec := execEq
              loop := loopEq }

theorem exec_eq_ordinary_of_executionSafe
    (contract : MemoryContract.Contract) (fuel : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hSafe : AllocationInteractionSafeSemantics.Stmt.ExecutionSafe
      contract fuel stmt code state) :
    AllocationInteractionSafeSemantics.exec contract fuel stmt code state =
      Yul.InteractionSemantics.exec fuel stmt code state :=
  (refinementAt contract fuel).exec stmt code state hSafe

end
end AllocationInteractionSafeRefinement
end Yul
end EvmCompiler
