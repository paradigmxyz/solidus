import EvmCompiler.Yul.EffectRefinement

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

theorem call_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (args : List Word)
    (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (call model sourcePrim 0 args functionName? codeOverride state)
      (call model targetPrim 0 args functionName? codeOverride state) := by
  simpa [call] using
    (Result.Refines.refl
      (fail state .OutOfFuel : Result σ (σ × List Word)))

private theorem callBody_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (args : List Word)
    (params rets : List EvmYul.Identifier)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hExec :
      Result.Refines
        (exec model sourcePrim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params rets args))))
        (exec model targetPrim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params rets args))))) :
    Result.Refines
      (match
        exec model sourcePrim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params rets args)))
      with
      | .error failure => .error failure
      | .ok stateAfterBody =>
          let bodySource := model.source stateAfterBody
          let sourceAfterCall :=
            (bodySource.reviveJump.overwrite?
              (model.source state)).setStore (model.source state)
          .ok
            (model.withSource stateAfterBody sourceAfterCall,
              List.map bodySource.lookup! rets))
      (match
        exec model targetPrim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params rets args)))
      with
      | .error failure => .error failure
      | .ok stateAfterBody =>
          let bodySource := model.source stateAfterBody
          let sourceAfterCall :=
            (bodySource.reviveJump.overwrite?
              (model.source state)).setStore (model.source state)
          .ok
            (model.withSource stateAfterBody sourceAfterCall,
              List.map bodySource.lookup! rets)) := by
  intro hObservable
  generalize hSourceExec :
    exec model sourcePrim fuel (.Block body) codeOverride
      (model.withSource state
        (EvmYul.Yul.State.mkOk
          ((model.source state).initcall params rets args))) = sourceExec
  cases sourceExec with
  | error failure =>
      have hExecObservable :
          Result.Observable (.error failure : Result σ σ) := by
        simpa only [hSourceExec] using hObservable
      have hSourceExecObservable :
          Result.Observable
            (exec model sourcePrim fuel (.Block body) codeOverride
              (model.withSource state
                (EvmYul.Yul.State.mkOk
                  ((model.source state).initcall params rets args)))) := by
        rw [hSourceExec]
        exact hExecObservable
      have hTargetExec := hExec hSourceExecObservable
      rw [hSourceExec] at hTargetExec
      simpa only [hSourceExec, hTargetExec]
  | ok stateAfterBody =>
      have hSourceExecObservable :
          Result.Observable
            (exec model sourcePrim fuel (.Block body) codeOverride
              (model.withSource state
                (EvmYul.Yul.State.mkOk
                  ((model.source state).initcall params rets args)))) := by
        rw [hSourceExec]
        simp [Result.Observable]
      have hTargetExec := hExec hSourceExecObservable
      rw [hSourceExec] at hTargetExec
      simpa only [hSourceExec, hTargetExec]

theorem call_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (args : List Word)
    (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hExec :
      ∀ body entryState,
        Result.Refines
          (exec model sourcePrim fuel (.Block body)
            codeOverride entryState)
          (exec model targetPrim fuel (.Block body)
            codeOverride entryState)) :
    Result.Refines
      (call model sourcePrim fuel.succ args functionName?
        codeOverride state)
      (call model targetPrim fuel.succ args functionName?
        codeOverride state) := by
  let source := model.source state
  generalize hCode : resolveActiveCode? source codeOverride = code?
  cases code? with
  | none =>
      simpa only [call, source, hCode] using
        (Result.Refines.refl
          (fail state (.MissingContract
            (s!"{source.executionEnv.codeOwner}")) :
            Result σ (σ × List Word)))
  | some code =>
      cases functionName? with
      | none =>
          simpa only [call, source, hCode] using
            (callBody_refines model sourcePrim targetPrim fuel args
              [] []
              [code.dispatcher]
              codeOverride state
              (hExec
                [code.dispatcher]
                (model.withSource state
                  (EvmYul.Yul.State.mkOk
                    (source.initcall [] [] args)))))
      | some functionName =>
          generalize hLookup :
            code.functions.lookup functionName = function?
          cases function? with
          | none =>
              simpa only [call, source, hCode, hLookup] using
                (Result.Refines.refl
                  (fail state
                    (.MissingContractFunction functionName) :
                    Result σ (σ × List Word)))
          | some function =>
              rcases function with ⟨params, rets, body⟩
              simpa only [call, source, hCode, hLookup] using
                (callBody_refines model sourcePrim targetPrim fuel args
                  params rets body codeOverride state
                  (hExec body
                    (model.withSource state
                      (EvmYul.Yul.State.mkOk
                        (source.initcall params rets args)))))

theorem callDispatcher_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (callDispatcher model sourcePrim 0 codeOverride state)
      (callDispatcher model targetPrim 0 codeOverride state) := by
  simpa [callDispatcher] using
    (Result.Refines.refl
      (fail state .OutOfFuel : Result σ (σ × List Word)))

theorem callDispatcher_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hExec :
      Result.Refines
        (exec model sourcePrim fuel
          (.Block [(model.source state).executionEnv.code.dispatcher])
          codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] []))))
        (exec model targetPrim fuel
          (.Block [(model.source state).executionEnv.code.dispatcher])
          codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] []))))) :
    Result.Refines
      (callDispatcher model sourcePrim fuel.succ codeOverride state)
      (callDispatcher model targetPrim fuel.succ codeOverride state) := by
  intro hObservable
  let source := model.source state
  let entryState :=
    model.withSource state
      (EvmYul.Yul.State.mkOk (source.initcall [] [] []))
  generalize hSourceExec :
    exec model sourcePrim fuel
      (.Block [source.executionEnv.code.dispatcher])
      codeOverride entryState = sourceExec
  cases sourceExec with
  | error failure =>
      have hExecObservable :
          Result.Observable (.error failure : Result σ σ) := by
        simpa only [callDispatcher, source, entryState, hSourceExec]
          using hObservable
      have hSourceExecObservable :
          Result.Observable
            (exec model sourcePrim fuel
              (.Block [source.executionEnv.code.dispatcher])
              codeOverride entryState) := by
        rw [hSourceExec]
        exact hExecObservable
      have hTargetExec := hExec hSourceExecObservable
      rw [show model.source state = source from rfl] at hTargetExec
      rw [show
        model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] [])) =
          entryState from rfl] at hTargetExec
      rw [hSourceExec] at hTargetExec
      simpa only [callDispatcher, source, entryState, hSourceExec,
        hTargetExec]
  | ok stateAfterBody =>
      have hSourceExecObservable :
          Result.Observable
            (exec model sourcePrim fuel
              (.Block [source.executionEnv.code.dispatcher])
              codeOverride entryState) := by
        rw [hSourceExec]
        simp [Result.Observable]
      have hTargetExec := hExec hSourceExecObservable
      rw [show model.source state = source from rfl] at hTargetExec
      rw [show
        model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] [])) =
          entryState from rfl] at hTargetExec
      rw [hSourceExec] at hTargetExec
      simpa only [callDispatcher, source, entryState, hSourceExec,
        hTargetExec]

theorem execSeq_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (execSeq model sourcePrim 0 stmts codeOverride state)
      (execSeq model targetPrim 0 stmts codeOverride state) := by
  simpa [execSeq] using
    (Result.Refines.refl (fail state .OutOfFuel : Result σ σ))

theorem execSeq_nil_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (execSeq model sourcePrim fuel.succ [] codeOverride state)
      (execSeq model targetPrim fuel.succ [] codeOverride state) := by
  simpa [execSeq] using
    (Result.Refines.refl (.ok state : Result σ σ))

theorem execSeq_cons_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hHead :
      Result.Refines
        (exec model sourcePrim fuel stmt codeOverride state)
        (exec model targetPrim fuel stmt codeOverride state))
    (hTail :
      ∀ stateAfterStmt,
        Result.Refines
          (execSeq model sourcePrim fuel stmts
            codeOverride stateAfterStmt)
          (execSeq model targetPrim fuel stmts
            codeOverride stateAfterStmt)) :
    Result.Refines
      (execSeq model sourcePrim fuel.succ (stmt :: stmts)
        codeOverride state)
      (execSeq model targetPrim fuel.succ (stmt :: stmts)
        codeOverride state) := by
  intro hObservable
  generalize hSourceHead :
    exec model sourcePrim fuel stmt codeOverride state = sourceHead
  cases sourceHead with
  | error failure =>
      have hHeadObservable :
          Result.Observable (.error failure : Result σ σ) := by
        simpa only [execSeq, hSourceHead] using hObservable
      have hSourceHeadObservable :
          Result.Observable
            (exec model sourcePrim fuel stmt codeOverride state) := by
        rw [hSourceHead]
        exact hHeadObservable
      have hTargetHead := hHead hSourceHeadObservable
      rw [hSourceHead] at hTargetHead
      simpa only [execSeq, hSourceHead, hTargetHead]
  | ok stateAfterStmt =>
      have hSourceHeadObservable :
          Result.Observable
            (exec model sourcePrim fuel stmt codeOverride state) := by
        rw [hSourceHead]
        simp [Result.Observable]
      have hTargetHead := hHead hSourceHeadObservable
      rw [hSourceHead] at hTargetHead
      cases hSourceState : model.source stateAfterStmt with
      | Ok shared store =>
          have hTailObservable :
              Result.Observable
                (execSeq model sourcePrim fuel stmts
                  codeOverride stateAfterStmt) := by
            simpa only [execSeq, hSourceHead, hSourceState]
              using hObservable
          have hTargetTail := hTail stateAfterStmt hTailObservable
          simpa only [execSeq, hSourceHead, hTargetHead,
            hSourceState] using hTargetTail
      | OutOfFuel =>
          simpa only [execSeq, hSourceHead, hTargetHead, hSourceState]
      | Checkpoint jump =>
          simpa only [execSeq, hSourceHead, hTargetHead, hSourceState]

end Effectful
end Source
end Yul
end EvmCompiler
