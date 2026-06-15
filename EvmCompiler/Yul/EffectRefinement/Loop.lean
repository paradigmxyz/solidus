import EvmCompiler.Yul.EffectRefinement.Statement

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

theorem loop_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (loop model sourcePrim 0 cond post body codeOverride state)
      (loop model targetPrim 0 cond post body codeOverride state) := by
  simpa [loop] using
    (Result.Refines.refl (fail state .OutOfFuel : Result σ σ))

theorem loop_one_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (loop model sourcePrim 1 cond post body codeOverride state)
      (loop model targetPrim 1 cond post body codeOverride state) := by
  simpa [loop] using
    (Result.Refines.refl (fail state .OutOfFuel : Result σ σ))

private theorem loopRecurResult_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (outerSource : EvmYul.Yul.State)
    (stateAfterPost : σ) (sourceAfterPost : EvmYul.Yul.State)
    (hRecur :
      Result.Refines
        (exec model sourcePrim fuel (.For cond post body)
          codeOverride
          (model.withSource stateAfterPost sourceAfterPost))
        (exec model targetPrim fuel (.For cond post body)
          codeOverride
          (model.withSource stateAfterPost sourceAfterPost))) :
    Result.Refines
      (match
        exec model sourcePrim fuel (.For cond post body)
          codeOverride
          (model.withSource stateAfterPost sourceAfterPost)
      with
      | .error failure => .error failure
      | .ok stateAfterLoop =>
          .ok
            (model.withSource stateAfterLoop
              ((model.source stateAfterLoop).overwrite? outerSource)))
      (match
        exec model targetPrim fuel (.For cond post body)
          codeOverride
          (model.withSource stateAfterPost sourceAfterPost)
      with
      | .error failure => .error failure
      | .ok stateAfterLoop =>
          .ok
            (model.withSource stateAfterLoop
              ((model.source stateAfterLoop).overwrite? outerSource))) := by
  intro hObservable
  generalize hSourceRecur :
    exec model sourcePrim fuel (.For cond post body)
      codeOverride
      (model.withSource stateAfterPost sourceAfterPost) = sourceRecur
  cases sourceRecur with
  | error failure =>
      have hRecurObservable :
          Result.Observable (.error failure : Result σ σ) := by
        simpa only [hSourceRecur] using hObservable
      have hSourceRecurObservable :
          Result.Observable
            (exec model sourcePrim fuel (.For cond post body)
              codeOverride
              (model.withSource stateAfterPost sourceAfterPost)) := by
        rw [hSourceRecur]
        exact hRecurObservable
      have hTargetRecur := hRecur hSourceRecurObservable
      rw [hSourceRecur] at hTargetRecur
      simpa only [hSourceRecur, hTargetRecur]
  | ok stateAfterLoop =>
      have hSourceRecurObservable :
          Result.Observable
            (exec model sourcePrim fuel (.For cond post body)
              codeOverride
              (model.withSource stateAfterPost sourceAfterPost)) := by
        rw [hSourceRecur]
        simp [Result.Observable]
      have hTargetRecur := hRecur hSourceRecurObservable
      rw [hSourceRecur] at hTargetRecur
      simpa only [hSourceRecur, hTargetRecur]

private theorem loopPostResult_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (outerSource : EvmYul.Yul.State) (stateAfterBody : σ)
    (hPost :
      Result.Refines
        (exec model sourcePrim fuel (.Block post) codeOverride
          (model.withSource stateAfterBody
            (model.source stateAfterBody).reviveJump))
        (exec model targetPrim fuel (.Block post) codeOverride
          (model.withSource stateAfterBody
            (model.source stateAfterBody).reviveJump)))
    (hRecur :
      ∀ stateAfterPost sourceAfterPost,
        Result.Refines
          (exec model sourcePrim fuel (.For cond post body)
            codeOverride
            (model.withSource stateAfterPost sourceAfterPost))
          (exec model targetPrim fuel (.For cond post body)
            codeOverride
            (model.withSource stateAfterPost sourceAfterPost))) :
    Result.Refines
      (match
        exec model sourcePrim fuel (.Block post) codeOverride
          (model.withSource stateAfterBody
            (model.source stateAfterBody).reviveJump)
      with
      | .error failure => .error failure
      | .ok stateAfterPost =>
          let postSource := model.source stateAfterPost
          let sourceAfterPost := postSource.overwrite? outerSource
          match postSource with
          | .OutOfFuel =>
              .ok
                (model.withSource stateAfterPost sourceAfterPost)
          | .Checkpoint (.Leave _ _) =>
              .ok
                (model.withSource stateAfterPost sourceAfterPost)
          | _ =>
              match
                exec model sourcePrim fuel (.For cond post body)
                  codeOverride
                  (model.withSource stateAfterPost sourceAfterPost)
              with
              | .error failure => .error failure
              | .ok stateAfterLoop =>
                  .ok
                    (model.withSource stateAfterLoop
                      ((model.source stateAfterLoop).overwrite?
                        outerSource)))
      (match
        exec model targetPrim fuel (.Block post) codeOverride
          (model.withSource stateAfterBody
            (model.source stateAfterBody).reviveJump)
      with
      | .error failure => .error failure
      | .ok stateAfterPost =>
          let postSource := model.source stateAfterPost
          let sourceAfterPost := postSource.overwrite? outerSource
          match postSource with
          | .OutOfFuel =>
              .ok
                (model.withSource stateAfterPost sourceAfterPost)
          | .Checkpoint (.Leave _ _) =>
              .ok
                (model.withSource stateAfterPost sourceAfterPost)
          | _ =>
              match
                exec model targetPrim fuel (.For cond post body)
                  codeOverride
                  (model.withSource stateAfterPost sourceAfterPost)
              with
              | .error failure => .error failure
              | .ok stateAfterLoop =>
                  .ok
                    (model.withSource stateAfterLoop
                      ((model.source stateAfterLoop).overwrite?
                        outerSource))) := by
  intro hObservable
  generalize hSourcePost :
    exec model sourcePrim fuel (.Block post) codeOverride
      (model.withSource stateAfterBody
        (model.source stateAfterBody).reviveJump) = sourcePost
  cases sourcePost with
  | error failure =>
      have hPostObservable :
          Result.Observable (.error failure : Result σ σ) := by
        simpa only [hSourcePost] using hObservable
      have hSourcePostObservable :
          Result.Observable
            (exec model sourcePrim fuel (.Block post) codeOverride
              (model.withSource stateAfterBody
                (model.source stateAfterBody).reviveJump)) := by
        rw [hSourcePost]
        exact hPostObservable
      have hTargetPost := hPost hSourcePostObservable
      rw [hSourcePost] at hTargetPost
      simpa only [hSourcePost, hTargetPost]
  | ok stateAfterPost =>
      have hSourcePostObservable :
          Result.Observable
            (exec model sourcePrim fuel (.Block post) codeOverride
              (model.withSource stateAfterBody
                (model.source stateAfterBody).reviveJump)) := by
        rw [hSourcePost]
        simp [Result.Observable]
      have hTargetPost := hPost hSourcePostObservable
      rw [hSourcePost] at hTargetPost
      let postSource := model.source stateAfterPost
      let sourceAfterPost := postSource.overwrite? outerSource
      cases hPostSource : postSource with
      | OutOfFuel =>
          simpa only [hSourcePost, hTargetPost, postSource,
            sourceAfterPost, hPostSource]
      | Ok shared store =>
          have hRecurResult :=
            loopRecurResult_refines model sourcePrim targetPrim
              fuel cond post body codeOverride outerSource
              stateAfterPost sourceAfterPost
              (hRecur stateAfterPost sourceAfterPost)
          have hTargetRecurResult := hRecurResult (by
            simpa only [hSourcePost, postSource,
              sourceAfterPost, hPostSource] using hObservable)
          simpa only [hSourcePost, hTargetPost, postSource,
            sourceAfterPost, hPostSource] using hTargetRecurResult
      | Checkpoint jump =>
          cases jump with
          | Leave shared store =>
              simpa only [hSourcePost, hTargetPost, postSource,
                sourceAfterPost, hPostSource]
          | Continue shared store =>
              have hRecurResult :=
                loopRecurResult_refines model sourcePrim targetPrim
                  fuel cond post body codeOverride outerSource
                  stateAfterPost sourceAfterPost
                  (hRecur stateAfterPost sourceAfterPost)
              have hTargetRecurResult := hRecurResult (by
                simpa only [hSourcePost, postSource,
                  sourceAfterPost, hPostSource] using hObservable)
              simpa only [hSourcePost, hTargetPost, postSource,
                sourceAfterPost, hPostSource] using hTargetRecurResult
          | Break shared store =>
              have hRecurResult :=
                loopRecurResult_refines model sourcePrim targetPrim
                  fuel cond post body codeOverride outerSource
                  stateAfterPost sourceAfterPost
                  (hRecur stateAfterPost sourceAfterPost)
              have hTargetRecurResult := hRecurResult (by
                simpa only [hSourcePost, postSource,
                  sourceAfterPost, hPostSource] using hObservable)
              simpa only [hSourcePost, hTargetPost, postSource,
                sourceAfterPost, hPostSource] using hTargetRecurResult

theorem loop_succ_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hCond :
      Result.Refines
        (eval model sourcePrim fuel cond codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state))))
        (eval model targetPrim fuel cond codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state)))))
    (hBody :
      ∀ stateAfterCond,
        Result.Refines
          (exec model sourcePrim fuel (.Block body)
            codeOverride stateAfterCond)
          (exec model targetPrim fuel (.Block body)
            codeOverride stateAfterCond))
    (hPost :
      ∀ stateAfterBody,
        Result.Refines
          (exec model sourcePrim fuel (.Block post) codeOverride
            (model.withSource stateAfterBody
              (model.source stateAfterBody).reviveJump))
          (exec model targetPrim fuel (.Block post) codeOverride
            (model.withSource stateAfterBody
              (model.source stateAfterBody).reviveJump)))
    (hRecur :
      ∀ stateAfterPost sourceAfterPost,
        Result.Refines
          (exec model sourcePrim fuel (.For cond post body)
            codeOverride
            (model.withSource stateAfterPost sourceAfterPost))
          (exec model targetPrim fuel (.For cond post body)
            codeOverride
            (model.withSource stateAfterPost sourceAfterPost))) :
    Result.Refines
      (loop model sourcePrim fuel.succ.succ cond post body
        codeOverride state)
      (loop model targetPrim fuel.succ.succ cond post body
        codeOverride state) := by
  intro hObservable
  let outerSource := model.source state
  let condState :=
    model.withSource state (EvmYul.Yul.State.mkOk outerSource)
  generalize hSourceCond :
    eval model sourcePrim fuel cond codeOverride condState = sourceCond
  cases sourceCond with
  | error failure =>
      have hCondObservable :
          Result.Observable
            (.error failure : Result σ (σ × Word)) := by
        simpa only [loop, outerSource, condState, hSourceCond]
          using hObservable
      have hSourceCondObservable :
          Result.Observable
            (eval model sourcePrim fuel cond codeOverride condState) := by
        rw [hSourceCond]
        exact hCondObservable
      have hTargetCond := hCond hSourceCondObservable
      rw [show
        model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state)) =
          condState from rfl] at hTargetCond
      rw [hSourceCond] at hTargetCond
      simpa only [loop, outerSource, condState, hSourceCond,
        hTargetCond]
  | ok result =>
      rcases result with ⟨stateAfterCond, condValue⟩
      have hSourceCondObservable :
          Result.Observable
            (eval model sourcePrim fuel cond codeOverride condState) := by
        rw [hSourceCond]
        simp [Result.Observable]
      have hTargetCond := hCond hSourceCondObservable
      rw [show
        model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state)) =
          condState from rfl] at hTargetCond
      rw [hSourceCond] at hTargetCond
      by_cases hZero : condValue = ⟨0⟩
      · simpa only [loop, outerSource, condState, hSourceCond,
          hTargetCond, if_pos hZero]
      · generalize hSourceBody :
          exec model sourcePrim fuel (.Block body)
            codeOverride stateAfterCond = sourceBody
        cases sourceBody with
        | error failure =>
            have hBodyObservable :
                Result.Observable (.error failure : Result σ σ) := by
              simpa only [loop, outerSource, condState, hSourceCond,
                hTargetCond, if_neg hZero, hSourceBody]
                using hObservable
            have hSourceBodyObservable :
                Result.Observable
                  (exec model sourcePrim fuel (.Block body)
                    codeOverride stateAfterCond) := by
              rw [hSourceBody]
              exact hBodyObservable
            have hTargetBody :=
              hBody stateAfterCond hSourceBodyObservable
            rw [hSourceBody] at hTargetBody
            simpa only [loop, outerSource, condState, hSourceCond,
              hTargetCond, if_neg hZero, hSourceBody, hTargetBody]
        | ok stateAfterBody =>
            have hSourceBodyObservable :
                Result.Observable
                  (exec model sourcePrim fuel (.Block body)
                    codeOverride stateAfterCond) := by
              rw [hSourceBody]
              simp [Result.Observable]
            have hTargetBody :=
              hBody stateAfterCond hSourceBodyObservable
            rw [hSourceBody] at hTargetBody
            let bodySource := model.source stateAfterBody
            cases hBodySource : bodySource with
            | OutOfFuel =>
                simpa only [loop, outerSource, condState, hSourceCond,
                  hTargetCond, if_neg hZero, hSourceBody, hTargetBody,
                  bodySource, hBodySource]
            | Ok shared store =>
                have hPostResult :=
                  loopPostResult_refines model sourcePrim targetPrim
                    fuel cond post body codeOverride outerSource
                    stateAfterBody (hPost stateAfterBody) hRecur
                have hTargetPostResult := hPostResult (by
                  simpa only [loop, outerSource, condState,
                    hSourceCond, hTargetCond, if_neg hZero,
                    hSourceBody, bodySource, hBodySource]
                    using hObservable)
                simpa only [loop, outerSource, condState, hSourceCond,
                  hTargetCond, if_neg hZero, hSourceBody, hTargetBody,
                  bodySource, hBodySource] using hTargetPostResult
            | Checkpoint jump =>
                cases jump with
                | Break shared store =>
                    simpa only [loop, outerSource, condState,
                      hSourceCond, hTargetCond, if_neg hZero,
                      hSourceBody, hTargetBody, bodySource, hBodySource]
                | Leave shared store =>
                    simpa only [loop, outerSource, condState,
                      hSourceCond, hTargetCond, if_neg hZero,
                      hSourceBody, hTargetBody, bodySource, hBodySource]
                | Continue shared store =>
                    have hPostResult :=
                      loopPostResult_refines model sourcePrim targetPrim
                        fuel cond post body codeOverride outerSource
                        stateAfterBody (hPost stateAfterBody) hRecur
                    have hTargetPostResult := hPostResult (by
                      simpa only [loop, outerSource, condState,
                        hSourceCond, hTargetCond, if_neg hZero,
                        hSourceBody, bodySource, hBodySource]
                        using hObservable)
                    simpa only [loop, outerSource, condState,
                      hSourceCond, hTargetCond, if_neg hZero,
                      hSourceBody, hTargetBody, bodySource, hBodySource]
                      using hTargetPostResult

end Effectful
end Source
end Yul
end EvmCompiler
