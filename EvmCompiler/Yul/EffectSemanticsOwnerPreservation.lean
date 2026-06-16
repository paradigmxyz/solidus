import EvmCompiler.Yul.EffectSemanticsOwner

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

/-!
Successful executions of the canonical parameterized Yul semantics preserve
availability of the active code owner whenever the state model is lawful and
its primitive handler preserves that invariant.
-/

private theorem ownerAvailable_withSource
    {σ : Type} {model : StateModel σ}
    (hModel : model.Lawful)
    (state : σ) (source : EvmYul.Yul.State)
    (hOwner : ActiveOwnerAvailable source) :
    OwnerAvailable model (model.withSource state source) := by
  unfold OwnerAvailable
  rw [hModel.source_withSource]
  exact hOwner

private theorem ownerAvailable_multifill
    {σ : Type} {model : StateModel σ}
    (hModel : model.Lawful)
    {state : σ} {names : List EvmYul.Identifier} {values : List Word}
    (hOwner : OwnerAvailable model state) :
    OwnerAvailable model (model.multifill names state values) := by
  apply ownerAvailable_withSource hModel
  unfold OwnerAvailable at hOwner
  simpa using
    (activeOwnerAvailable_multifill (model.source state) names values).2
      hOwner

private theorem activeOwnerAvailable_overwrite
    {left right : EvmYul.Yul.State}
    (hLeft : ActiveOwnerAvailable left)
    (hRight : ActiveOwnerAvailable right) :
    ActiveOwnerAvailable (left.overwrite? right) := by
  cases right with
  | Ok shared store =>
      simpa [EvmYul.Yul.State.overwrite?] using hLeft
  | OutOfFuel =>
      simpa [ActiveOwnerAvailable, activeShared?] using hRight
  | Checkpoint jump =>
      simpa [EvmYul.Yul.State.overwrite?] using hRight

private theorem activeOwnerAvailable_mkOk_of_ok
    {source : EvmYul.Yul.State}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
    (hSource : source = .Ok shared store)
    (hOwner : ActiveOwnerAvailable source) :
    ActiveOwnerAvailable source.mkOk := by
  subst source
  simpa [EvmYul.Yul.State.mkOk] using hOwner

private theorem zeroFill_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (names : List EvmYul.Identifier) :
    ∃ store',
      (EvmYul.Yul.State.Ok shared store).zeroFill names =
        .Ok shared store' := by
  induction names with
  | nil => exact ⟨store, rfl⟩
  | cons name names ih =>
      rcases ih with ⟨store', hStore⟩
      refine ⟨store'.insert name ⟨0⟩, ?_⟩
      simp only [EvmYul.Yul.State.zeroFill, List.foldr_cons]
      change
        ((EvmYul.Yul.State.Ok shared store).zeroFill names).insert
            name ⟨0⟩ =
          .Ok shared (store'.insert name ⟨0⟩)
      rw [hStore]
      rfl

private theorem foldrInsert_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (entries : List (EvmYul.Identifier × Word)) :
    ∃ store',
      entries.foldr
          (fun entry (result : EvmYul.Yul.State) =>
            result.insert entry.1 entry.2)
          (EvmYul.Yul.State.Ok shared store) =
        EvmYul.Yul.State.Ok shared store' := by
  induction entries with
  | nil => exact ⟨store, rfl⟩
  | cons entry entries ih =>
      rcases ih with ⟨store', hStore⟩
      refine ⟨store'.insert entry.1 entry.2, ?_⟩
      simp only [List.foldr_cons]
      rw [hStore]
      rfl

private theorem multifill_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (names : List EvmYul.Identifier) (values : List Word) :
    ∃ store',
      (EvmYul.Yul.State.Ok shared store).multifill names values =
        .Ok shared store' := by
  exact foldrInsert_ok shared store (List.zip names values)

private theorem initcall_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (params returns : List EvmYul.Identifier) (args : List Word) :
    ∃ store',
      (EvmYul.Yul.State.Ok shared store).initcall params returns args =
        .Ok shared store' := by
  obtain ⟨zeroStore, hZero⟩ :=
    zeroFill_ok shared default returns
  obtain ⟨entryStore, hEntries⟩ :=
    multifill_ok shared zeroStore params args
  refine ⟨entryStore, ?_⟩
  simpa [EvmYul.Yul.State.initcall, EvmYul.Yul.State.setStore, hZero]
    using hEntries

mutual

theorem evalArgs_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hOwner : OwnerAvailable model state)
    (hRun :
      evalArgs model prim fuel args codeOverride state =
        .ok (final, values)) :
    OwnerAvailable model final := by
  cases fuel with
  | zero =>
      simp [evalArgs, fail] at hRun
  | succ previous =>
      cases args with
      | nil =>
          simp [evalArgs] at hRun
          exact hRun.1 ▸ hOwner
      | cons arg rest =>
          cases hHead :
              eval model prim previous arg codeOverride state with
          | error failure =>
              simp [evalArgs, evalTail, hHead] at hRun
          | ok result =>
              rcases result with ⟨stateAfterHead, value⟩
              have hHeadOwner :=
                eval_preserves_owner hModel hPrim hOwner hHead
              cases previous with
              | zero =>
                  simp [evalArgs, evalTail, hHead, fail] at hRun
              | succ tailFuel =>
                  cases hTail :
                      evalArgs model prim tailFuel rest codeOverride
                        stateAfterHead with
                  | error failure =>
                      simp [evalArgs, evalTail, hHead, hTail] at hRun
                  | ok result =>
                      rcases result with ⟨stateAfterTail, tailValues⟩
                      have hTailOwner :=
                        evalArgs_preserves_owner hModel hPrim hHeadOwner hTail
                      simp [evalArgs, evalTail, hHead, hTail] at hRun
                      exact hRun.1 ▸ hTailOwner
  termination_by (fuel, 1, sizeOf args)

theorem evalValues_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hOwner : OwnerAvailable model state)
    (hRun :
      evalValues model prim fuel expr codeOverride state =
        .ok (final, values)) :
    OwnerAvailable model final := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ previous =>
      cases expr with
      | Lit value =>
          simp [evalValues] at hRun
          exact hRun.1 ▸ hOwner
      | Var name =>
          cases hLookup : (model.source state).lookup? name with
          | none =>
              simp [evalValues, hLookup, fail] at hRun
          | some value =>
              simp [evalValues, hLookup] at hRun
              exact hRun.1 ▸ hOwner
      | Call target args =>
          cases target with
          | inl op =>
              cases hArgs :
                  evalArgs model prim previous args.reverse codeOverride
                    state with
              | error failure =>
                  simp [evalValues, hArgs] at hRun
              | ok result =>
                  rcases result with ⟨stateAfterArgs, reversedValues⟩
                  have hArgsOwner :=
                    evalArgs_preserves_owner hModel hPrim hOwner hArgs
                  have hPrimRun :
                      prim.eval previous stateAfterArgs op
                          reversedValues.reverse =
                        .ok (final, values) := by
                    simpa [evalValues, hArgs] using hRun
                  exact hPrim.eval hArgsOwner hPrimRun
          | inr functionName =>
              cases hArgs :
                  evalArgs model prim previous args.reverse codeOverride
                    state with
              | error failure =>
                  simp [evalValues, hArgs] at hRun
              | ok result =>
                  rcases result with ⟨stateAfterArgs, reversedValues⟩
                  have hArgsOwner :=
                    evalArgs_preserves_owner hModel hPrim hOwner hArgs
                  have hCall :
                      call model prim previous reversedValues.reverse
                          (some functionName) codeOverride stateAfterArgs =
                        .ok (final, values) := by
                    simpa [evalValues, hArgs] using hRun
                  exact
                    call_preserves_owner hModel hPrim hArgsOwner hCall
  termination_by (fuel, 2, sizeOf expr)

theorem eval_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {value : Word}
    (hOwner : OwnerAvailable model state)
    (hRun :
      eval model prim fuel expr codeOverride state =
        .ok (final, value)) :
    OwnerAvailable model final := by
  obtain ⟨values, hValues, _hValue⟩ :=
    eval_ok_parts model prim hRun
  exact evalValues_preserves_owner hModel hPrim hOwner hValues
  termination_by (fuel, 3, sizeOf expr)

theorem call_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {args : List Word}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hOwner : OwnerAvailable model state)
    (hRun :
      call model prim fuel args (some functionName) codeOverride state =
        .ok (final, values)) :
    OwnerAvailable model final := by
  cases fuel with
  | zero =>
      simp [call, fail] at hRun
  | succ bodyFuel =>
      obtain
          ⟨_contract, params, returns, body, stateAfterBody,
            _hContract, _hFunction, hBody, hFinal, _hValues⟩ :=
        call_succ_ok_parts model prim hRun
      rw [hFinal]
      unfold OwnerAvailable at hOwner
      cases hSource : model.source state with
      | OutOfFuel =>
          rw [hSource] at hOwner
          simp [ActiveOwnerAvailable, activeShared?] at hOwner
      | Checkpoint jump =>
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?,
            EvmYul.Yul.State.setStore] using hOwner
      | Ok shared store =>
          have hEntryActive :
              ActiveOwnerAvailable
                (EvmYul.Yul.State.mkOk
                  ((model.source state).initcall params returns args)) := by
            have hInitial : ActiveOwnerAvailable (.Ok shared store) := by
              simpa [hSource] using hOwner
            rw [hSource]
            have hInit :
                ActiveOwnerAvailable
                  ((.Ok shared store : EvmYul.Yul.State).initcall
                    params returns args) :=
              (activeOwnerAvailable_initcall (.Ok shared store)
                params returns args).2 hInitial
            obtain ⟨entryStore, hEntry⟩ :=
              initcall_ok shared store params returns args
            rw [hEntry] at hInit ⊢
            simpa [EvmYul.Yul.State.mkOk] using hInit
          have hEntryOwner :
              OwnerAvailable model
                (model.withSource state
                  (EvmYul.Yul.State.mkOk
                    ((model.source state).initcall params returns args))) :=
            ownerAvailable_withSource hModel state _ hEntryActive
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hEntryOwner hBody
          unfold OwnerAvailable at hBodyOwner
          apply ownerAvailable_withSource hModel
          apply (activeOwnerAvailable_setStore _ _).2
          apply activeOwnerAvailable_overwrite
          · exact
              (activeOwnerAvailable_reviveJump
                (model.source stateAfterBody)).2 hBodyOwner
          · simpa [hSource] using hOwner
  termination_by (fuel, 4, sizeOf args)

theorem callDispatcher_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hOwner : OwnerAvailable model state)
    (hRun :
      callDispatcher model prim fuel codeOverride state =
        .ok (final, values)) :
    OwnerAvailable model final := by
  obtain ⟨previous, stateAfterBody, hFuel, hBody, hFinal, _hValues⟩ :=
    callDispatcher_ok_parts model prim hRun
  rw [hFinal]
  unfold OwnerAvailable at hOwner
  cases hSource : model.source state with
  | OutOfFuel =>
      rw [hSource] at hOwner
      simp [ActiveOwnerAvailable, activeShared?] at hOwner
  | Checkpoint jump =>
      apply ownerAvailable_withSource hModel
      simpa [hSource, EvmYul.Yul.State.overwrite?,
        EvmYul.Yul.State.setStore] using hOwner
  | Ok shared store =>
      have hEntryActive :
          ActiveOwnerAvailable
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] [])) := by
        have hInitial : ActiveOwnerAvailable (.Ok shared store) := by
          simpa [hSource] using hOwner
        rw [hSource]
        simpa [EvmYul.Yul.State.mkOk] using
          (activeOwnerAvailable_initcall (.Ok shared store) [] [] []).2
            hInitial
      have hEntryOwner :
          OwnerAvailable model
            (model.withSource state
              (EvmYul.Yul.State.mkOk
                ((model.source state).initcall [] [] []))) :=
        ownerAvailable_withSource hModel state _ hEntryActive
      have hPrevious : previous < fuel := by omega
      have hBodyOwner :=
        exec_preserves_owner hModel hPrim hEntryOwner hBody
      unfold OwnerAvailable at hBodyOwner
      apply ownerAvailable_withSource hModel
      apply (activeOwnerAvailable_setStore _ _).2
      apply activeOwnerAvailable_overwrite
      · exact
          (activeOwnerAvailable_reviveJump
            (model.source stateAfterBody)).2 hBodyOwner
      · simpa [hSource] using hOwner
  termination_by (fuel, 5, 0)

theorem execSeq_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {stmts : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hOwner : OwnerAvailable model state)
    (hRun :
      execSeq model prim fuel stmts codeOverride state = .ok final) :
    OwnerAvailable model final := by
  cases stmts with
  | nil =>
      obtain ⟨_previous, _hFuel, rfl⟩ :=
        execSeq_nil_ok_parts model prim hRun
      exact hOwner
  | cons stmt rest =>
      obtain ⟨previous, stateAfterStmt, hFuel, hStmt, hRest⟩ :=
        execSeq_cons_ok_parts model prim hRun
      have hStmtOwner :=
        exec_preserves_owner hModel hPrim hOwner hStmt
      cases hSource : model.source stateAfterStmt with
      | Ok shared store =>
          have hTail :
              execSeq model prim previous rest codeOverride stateAfterStmt =
                .ok final := by
            simpa [hSource] using hRest
          exact
            execSeq_preserves_owner hModel hPrim hStmtOwner hTail
      | OutOfFuel =>
          have hFinal : final = stateAfterStmt := by
            simpa [hSource] using hRest
          exact hFinal ▸ hStmtOwner
      | Checkpoint jump =>
          have hFinal : final = stateAfterStmt := by
            simpa [hSource] using hRest
          exact hFinal ▸ hStmtOwner
  termination_by (fuel, 6, sizeOf stmts)

theorem exec_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {stmt : EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hOwner : OwnerAvailable model state)
    (hRun : exec model prim fuel stmt codeOverride state = .ok final) :
    OwnerAvailable model final := by
  cases stmt with
  | Block body =>
      obtain ⟨previous, stateAfterBody, _hFuel, hBody, hFinal⟩ :=
        exec_block_ok_parts model prim hRun
      have hBodyOwner :=
        execSeq_preserves_owner hModel hPrim hOwner hBody
      rw [hFinal]
      apply ownerAvailable_withSource hModel
      unfold OwnerAvailable at hBodyOwner
      exact
        (activeOwnerAvailable_restrictStoreTo
          (model.source stateAfterBody) (model.source state).store).2
          hBodyOwner
  | Let names expr? =>
      cases expr? with
      | none =>
          obtain ⟨_previous, _hFuel, _hCheck, hFinal⟩ :=
            exec_let_none_ok_parts model prim hRun
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          unfold OwnerAvailable at hOwner
          exact
            (activeOwnerAvailable_zeroFill (model.source state) names).2
              hOwner
      | some expr =>
          obtain
              ⟨previous, stateAfterValue, values, _hFuel, _hCheck,
                hValues, hFinal⟩ :=
            exec_let_some_ok_parts model prim hRun
          have hValueOwner :=
            evalValues_preserves_owner hModel hPrim hOwner hValues
          rw [hFinal]
          exact ownerAvailable_multifill hModel hValueOwner
  | Assign names expr =>
      obtain
          ⟨previous, stateAfterValue, values, _hFuel, _hCheck,
            hValues, hFinal⟩ :=
        exec_assign_ok_parts model prim hRun
      have hValueOwner :=
        evalValues_preserves_owner hModel hPrim hOwner hValues
      rw [hFinal]
      exact ownerAvailable_multifill hModel hValueOwner
  | If cond body =>
      obtain
          ⟨previous, stateAfterCond, condValue, _hFuel, hCond, hCase⟩ :=
        exec_if_ok_parts model prim hRun
      have hCondOwner :=
        eval_preserves_owner hModel hPrim hOwner hCond
      rcases hCase with hTrue | hFalse
      · exact
          exec_preserves_owner hModel hPrim hCondOwner hTrue.2
      · exact hFalse.2 ▸ hCondOwner
  | ExprStmtCall expr =>
      cases expr with
      | Lit value =>
          cases fuel <;> simp [exec, fail] at hRun
      | Var name =>
          cases fuel <;> simp [exec, fail] at hRun
      | Call target args =>
          cases target with
          | inl op =>
              cases fuel with
              | zero =>
                  simp [exec, fail] at hRun
              | succ previous =>
                  cases hArgs :
                      evalArgs model prim previous args.reverse
                        codeOverride state with
                  | error failure =>
                      simp [exec, hArgs] at hRun
                  | ok result =>
                      rcases result with
                        ⟨stateAfterArgs, reversedValues⟩
                      have hArgsOwner :=
                        evalArgs_preserves_owner hModel hPrim hOwner hArgs
                      cases hPrimitive :
                          prim.eval previous stateAfterArgs op
                            reversedValues.reverse with
                      | error failure =>
                          simp [exec, hArgs, hPrimitive, multifill] at hRun
                      | ok result =>
                          rcases result with ⟨stateAfterPrim, values⟩
                          have hPrimOwner :=
                            hPrim.eval hArgsOwner hPrimitive
                          simp [exec, hArgs, hPrimitive, multifill] at hRun
                          rw [← hRun]
                          exact ownerAvailable_multifill hModel hPrimOwner
          | inr functionName =>
              obtain
                  ⟨argsFuel, callFuel, stateAfterArgs, reversedValues,
                    stateAfterCall, returnValues, hFuel, _hArgsFuel,
                    hArgs, hCall, hFinal⟩ :=
                exec_expr_function_ok_parts model prim hRun
              have hArgsOwner :=
                evalArgs_preserves_owner hModel hPrim hOwner hArgs
              have hCallOwner :=
                call_preserves_owner hModel hPrim hArgsOwner hCall
              rw [hFinal]
              exact ownerAvailable_multifill hModel hCallOwner
  | Switch scrutinee cases defaultBody =>
      obtain
          ⟨previous, stateAfterScrutinee, value, _hFuel, hScrutinee,
            hBody⟩ :=
        exec_switch_ok_parts model prim hRun
      have hScrutineeOwner :=
        eval_preserves_owner hModel hPrim hOwner hScrutinee
      exact
        exec_preserves_owner hModel hPrim hScrutineeOwner hBody
  | For cond post body =>
      obtain ⟨previous, _hFuel, hLoop⟩ :=
        exec_for_ok_parts model prim hRun
      exact loop_preserves_owner hModel hPrim hOwner hLoop
  | Continue =>
      obtain ⟨_previous, _hFuel, hFinal⟩ :=
        exec_continue_ok_parts model prim hRun
      rw [hFinal]
      apply ownerAvailable_withSource hModel
      unfold OwnerAvailable at hOwner
      exact (activeOwnerAvailable_setContinue (model.source state)).2 hOwner
  | Break =>
      obtain ⟨_previous, _hFuel, hFinal⟩ :=
        exec_break_ok_parts model prim hRun
      rw [hFinal]
      apply ownerAvailable_withSource hModel
      unfold OwnerAvailable at hOwner
      exact (activeOwnerAvailable_setBreak (model.source state)).2 hOwner
  | Leave =>
      obtain ⟨_previous, _hFuel, hFinal⟩ :=
        exec_leave_ok_parts model prim hRun
      rw [hFinal]
      apply ownerAvailable_withSource hModel
      unfold OwnerAvailable at hOwner
      exact (activeOwnerAvailable_setLeave (model.source state)).2 hOwner
  termination_by (fuel, 7, sizeOf stmt)

theorem loop_preserves_owner
    {σ : Type} {model : StateModel σ} {prim : PrimitiveSemantics σ}
    (hModel : model.Lawful) (hPrim : prim.PreservesOwner model)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {post body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hOwner : OwnerAvailable model state)
    (hRun :
      loop model prim fuel cond post body codeOverride state = .ok final) :
    OwnerAvailable model final := by
  obtain
      ⟨previous, afterCond, condValue, hFuel, hCond, hCase⟩ :=
    loop_ok_parts model prim hRun
  unfold OwnerAvailable at hOwner
  cases hSource : model.source state with
  | OutOfFuel =>
      rw [hSource] at hOwner
      simp [ActiveOwnerAvailable, activeShared?] at hOwner
  | Checkpoint jump =>
      cases hCase with
      | false hZero hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
      | bodyOutOfFuel hNonzero hBody hBodySource hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
      | @bodyBreak hNonzero afterBody shared store hBody hBodySource hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
      | bodyLeave hNonzero hBody hBodySource hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
      | @postOutOfFuel hNonzero afterBody afterPost hBody hContinues hPost
          hPostSource hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
      | @postLeave hNonzero afterBody afterPost shared store hBody hContinues
          hPost hPostSource hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
      | @recurse hNonzero afterBody afterPost afterLoop hBody hContinues
          hPost hRecurs hLoop hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          simpa [hSource, EvmYul.Yul.State.overwrite?] using hOwner
  | Ok shared store =>
      have hInitial : ActiveOwnerAvailable (.Ok shared store) := by
        simpa [hSource] using hOwner
      have hCondEntryActive :
          ActiveOwnerAvailable
            (EvmYul.Yul.State.mkOk (model.source state)) := by
        exact activeOwnerAvailable_mkOk_of_ok hSource hOwner
      have hCondEntryOwner :
          OwnerAvailable model
            (model.withSource state
              (EvmYul.Yul.State.mkOk (model.source state))) :=
        ownerAvailable_withSource hModel state _ hCondEntryActive
      have hCondStateOwner :=
        eval_preserves_owner hModel hPrim hCondEntryOwner hCond
      have hCondOwner : ActiveOwnerAvailable (model.source afterCond) :=
        hCondStateOwner
      cases hCase with
      | false hZero hFinal =>
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          apply activeOwnerAvailable_overwrite hCondOwner
          simpa [hSource] using hOwner
      | bodyOutOfFuel hNonzero hBody hBodySource hFinal =>
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hCondStateOwner hBody
          unfold OwnerAvailable at hBodyOwner
          rw [hBodySource] at hBodyOwner
          simp [ActiveOwnerAvailable, activeShared?] at hBodyOwner
      | @bodyBreak hNonzero afterBody shared store hBody hBodySource hFinal =>
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hCondStateOwner hBody
          unfold OwnerAvailable at hBodyOwner
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          apply activeOwnerAvailable_overwrite
          · exact
              (activeOwnerAvailable_reviveJump
                (model.source afterBody)).2 hBodyOwner
          · simpa [hSource] using hOwner
      | bodyLeave hNonzero hBody hBodySource hFinal =>
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hCondStateOwner hBody
          unfold OwnerAvailable at hBodyOwner
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          exact
            activeOwnerAvailable_overwrite hBodyOwner
              (by simpa [hSource] using hOwner)
      | @postOutOfFuel hNonzero afterBody afterPost hBody hContinues hPost
          hPostSource hFinal =>
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hCondStateOwner hBody
          unfold OwnerAvailable at hBodyOwner
          have hPostEntryOwner :
              OwnerAvailable model
                (model.withSource afterBody
                  (model.source afterBody).reviveJump) :=
            ownerAvailable_withSource hModel afterBody _
              ((activeOwnerAvailable_reviveJump
                (model.source afterBody)).2 hBodyOwner)
          have hPostOwner :=
            exec_preserves_owner hModel hPrim hPostEntryOwner hPost
          unfold OwnerAvailable at hPostOwner
          rw [hPostSource] at hPostOwner
          simp [ActiveOwnerAvailable, activeShared?] at hPostOwner
      | @postLeave hNonzero afterBody afterPost shared store hBody hContinues
          hPost hPostSource hFinal =>
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hCondStateOwner hBody
          unfold OwnerAvailable at hBodyOwner
          have hPostEntryOwner :
              OwnerAvailable model
                (model.withSource afterBody
                  (model.source afterBody).reviveJump) :=
            ownerAvailable_withSource hModel afterBody _
              ((activeOwnerAvailable_reviveJump
                (model.source afterBody)).2 hBodyOwner)
          have hPostOwner :=
            exec_preserves_owner hModel hPrim hPostEntryOwner hPost
          unfold OwnerAvailable at hPostOwner
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          exact
            activeOwnerAvailable_overwrite hPostOwner
              (by simpa [hSource] using hOwner)
      | @recurse hNonzero afterBody afterPost afterLoop hBody hContinues
          hPost hRecurs hLoop hFinal =>
          have hBodyOwner :=
            exec_preserves_owner hModel hPrim hCondStateOwner hBody
          unfold OwnerAvailable at hBodyOwner
          have hPostEntryOwner :
              OwnerAvailable model
                (model.withSource afterBody
                  (model.source afterBody).reviveJump) :=
            ownerAvailable_withSource hModel afterBody _
              ((activeOwnerAvailable_reviveJump
                (model.source afterBody)).2 hBodyOwner)
          have hPostOwner :=
            exec_preserves_owner hModel hPrim hPostEntryOwner hPost
          unfold OwnerAvailable at hPostOwner
          have hLoopEntryOwner :
              OwnerAvailable model
                (model.withSource afterPost
                  ((model.source afterPost).overwrite?
                    (model.source state))) :=
            ownerAvailable_withSource hModel afterPost _
              (activeOwnerAvailable_overwrite hPostOwner
                (by simpa [hSource] using hOwner))
          have hLoopOwner :=
            exec_preserves_owner hModel hPrim hLoopEntryOwner hLoop
          unfold OwnerAvailable at hLoopOwner
          rw [hFinal]
          apply ownerAvailable_withSource hModel
          exact
            activeOwnerAvailable_overwrite hLoopOwner
              (by simpa [hSource] using hOwner)
  termination_by
    (fuel, 8, sizeOf cond + sizeOf post + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

end

end Effectful
end Source
end Yul
end EvmCompiler
