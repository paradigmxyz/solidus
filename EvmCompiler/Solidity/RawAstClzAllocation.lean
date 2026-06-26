import EvmCompiler.Solidity.RawAst

namespace EvmCompiler.Solidity.RawAst.Elab

/-- The generated `clz` names are either all absent or all present. This is a
reachable-state invariant: the elaborator initializes all three fields to
`none`, and `ensureClzHelper` writes all three in one state update. -/
def ClzAllocationValid (state : State) : Prop :=
  (state.clzHelperName? = none ∧ state.clzArgName? = none ∧
      state.clzReturnName? = none) ∨
    ∃ helper arg ret,
      state.clzHelperName? = some helper ∧
        state.clzArgName? = some arg ∧
          state.clzReturnName? = some ret

/-- Exact generated names retained in an elaborator state. -/
structure ClzAllocatedAs (state : State)
    (helper arg ret : Name) : Prop where
  helper_eq : state.clzHelperName? = some helper
  arg_eq : state.clzArgName? = some arg
  ret_eq : state.clzReturnName? = some ret

/-- A successful elaborator transition may allocate `clz` names once, but may
never invalidate a reachable allocation or replace names already allocated. -/
structure ClzAllocationExtends (before after : State) : Prop where
  before_valid : ClzAllocationValid before
  after_valid : ClzAllocationValid after
  allocated : ∀ {helper arg ret},
    ClzAllocatedAs before helper arg ret →
      ClzAllocatedAs after helper arg ret

namespace ClzAllocationExtends

theorem refl (state : State) (hValid : ClzAllocationValid state) :
    ClzAllocationExtends state state where
  before_valid := hValid
  after_valid := hValid
  allocated := fun h => h

theorem trans {first second third : State}
    (hFirst : ClzAllocationExtends first second)
    (hSecond : ClzAllocationExtends second third) :
    ClzAllocationExtends first third where
  before_valid := hFirst.before_valid
  after_valid := hSecond.after_valid
  allocated := fun h => hSecond.allocated (hFirst.allocated h)

theorem of_fields_eq {before after : State}
    (hValid : ClzAllocationValid before)
    (hHelper : after.clzHelperName? = before.clzHelperName?)
    (hArg : after.clzArgName? = before.clzArgName?)
    (hRet : after.clzReturnName? = before.clzReturnName?) :
    ClzAllocationExtends before after := by
  have hAfter : ClzAllocationValid after := by
    unfold ClzAllocationValid at *
    simpa [hHelper, hArg, hRet] using hValid
  refine
    { before_valid := hValid
      after_valid := hAfter
      allocated := ?_ }
  intro helper arg ret hAllocated
  exact
    { helper_eq := hHelper.trans hAllocated.helper_eq
      arg_eq := hArg.trans hAllocated.arg_eq
      ret_eq := hRet.trans hAllocated.ret_eq }

end ClzAllocationExtends

/-- Generic state-monad effect interface used to compose the allocation
invariant through the recursive raw elaborator. -/
def PreservesClzAllocation {α : Type} (action : ElabM α) : Prop :=
  ∀ {state state' : State} {value : α},
    action.run state = .ok (value, state') →
      ClzAllocationValid state →
        ClzAllocationExtends state state'

namespace PreservesClzAllocation

theorem bind {α β : Type} {action : ElabM α} {next : α → ElabM β}
    (hAction : PreservesClzAllocation action)
    (hNext : ∀ value, PreservesClzAllocation (next value)) :
    PreservesClzAllocation (action >>= next) := by
  intro state state' value hRun hValid
  simp [StateT.run_bind] at hRun
  cases hActionRun : action.run state with
  | error _ => simp [hActionRun] at hRun
  | ok result =>
      rcases result with ⟨midValue, midState⟩
      have hFirst := hAction hActionRun hValid
      simp [hActionRun] at hRun
      exact hFirst.trans (hNext midValue hRun hFirst.after_valid)

theorem map {α β : Type} {action : ElabM α}
    (f : α → β) (hAction : PreservesClzAllocation action) :
    PreservesClzAllocation (f <$> action) := by
  intro state state' value hRun hValid
  simp [StateT.run_map] at hRun
  cases hActionRun : action.run state with
  | error _ => simp [hActionRun] at hRun
  | ok result =>
      rcases result with ⟨midValue, midState⟩
      have hPreserved := hAction hActionRun hValid
      simp [hActionRun] at hRun
      rcases hRun with ⟨_hValue, hState⟩
      subst state'
      exact hPreserved

theorem pure {α : Type} (value : α) :
    PreservesClzAllocation (pure value : ElabM α) := by
  intro state state' result hRun hValid
  simp [StateT.run_pure] at hRun
  cases hRun
  exact ClzAllocationExtends.refl state hValid

theorem throw {α : Type} (message : String) :
    PreservesClzAllocation (throw message : ElabM α) := by
  intro state state' value hRun _hValid
  unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
  change (Except.error message : DecodeM (α × State)) =
    .ok (value, state') at hRun
  cases hRun

end PreservesClzAllocation

theorem initial_clzAllocationValid : ClzAllocationValid ({} : State) := by
  exact Or.inl ⟨rfl, rfl, rfl⟩

theorem ensureClzHelper_preserves_clzAllocation :
    PreservesClzAllocation ensureClzHelper := by
  intro state state' value hRun hValid
  unfold ensureClzHelper at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  rcases hValid with hEmpty | hAllocated
  · rcases hEmpty with ⟨hHelper, hArg, hRet⟩
    simp [hHelper] at hRun
    cases hFreshHelper : (freshGeneratedFunctionName "clz").run state with
    | error _ => simp [hFreshHelper] at hRun
    | ok helperResult =>
        rcases helperResult with ⟨helper, helperState⟩
        simp [hFreshHelper] at hRun
        cases hFreshArg :
            (freshNonFunctionBindingName "clz_arg").run helperState with
        | error _ => simp [hFreshArg] at hRun
        | ok argResult =>
            rcases argResult with ⟨arg, argState⟩
            simp [hFreshArg] at hRun
            cases hFreshRet :
                (freshNonFunctionBindingName "clz_ret").run argState with
            | error _ => simp [hFreshRet] at hRun
            | ok retResult =>
                rcases retResult with ⟨ret, retState⟩
                simp [hFreshRet, StateT.run_modify] at hRun
                rcases hRun with ⟨hValue, hState⟩
                subst value
                subst state'
                refine
                  { before_valid := Or.inl ⟨hHelper, hArg, hRet⟩
                    after_valid := Or.inr ⟨helper, arg, ret, rfl, rfl, rfl⟩
                    allocated := ?_ }
                intro existingHelper existingArg existingRet hExisting
                have hImpossible := hExisting.helper_eq
                rw [hHelper] at hImpossible
                cases hImpossible
  · rcases hAllocated with
      ⟨allocatedHelper, arg, ret, hHelper, hArg, hRet⟩
    simp [hHelper, StateT.run_pure] at hRun
    rcases hRun with ⟨_hValue, hState⟩
    exact ClzAllocationExtends.refl state
      (Or.inr ⟨value, arg, ret, hHelper, hArg, hRet⟩)

theorem ensureClzHelper_result_helper_eq
    {state state' : State} {helper : Name}
    (hRun : ensureClzHelper.run state = .ok (helper, state')) :
    state'.clzHelperName? = some helper := by
  unfold ensureClzHelper at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hBefore : state.clzHelperName? with
  | some existing =>
      simp [hBefore] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hBefore
  | none =>
      simp [hBefore] at hRun
      cases hFreshHelper : (freshGeneratedFunctionName "clz").run state with
      | error _ => simp [hFreshHelper] at hRun
      | ok helperResult =>
          rcases helperResult with ⟨freshHelper, helperState⟩
          simp [hFreshHelper] at hRun
          cases hFreshArg :
              (freshNonFunctionBindingName "clz_arg").run helperState with
          | error _ => simp [hFreshArg] at hRun
          | ok argResult =>
              rcases argResult with ⟨freshArg, argState⟩
              simp [hFreshArg] at hRun
              cases hFreshRet :
                  (freshNonFunctionBindingName "clz_ret").run argState with
              | error _ => simp [hFreshRet] at hRun
              | ok retResult =>
                  rcases retResult with ⟨freshRet, retState⟩
                  simp [hFreshRet] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  rfl

theorem ensureClzHelper_allocated
    {state state' : State} {helper : Name}
    (hRun : ensureClzHelper.run state = .ok (helper, state'))
    (hValid : ClzAllocationValid state) :
    ∃ arg ret, ClzAllocatedAs state' helper arg ret := by
  have hExt := ensureClzHelper_preserves_clzAllocation hRun hValid
  have hResult := ensureClzHelper_result_helper_eq hRun
  rcases hExt.after_valid with hEmpty | hAllocated
  · rcases hEmpty with ⟨hHelper, _hArg, _hRet⟩
    rw [hHelper] at hResult
    cases hResult
  · rcases hAllocated with
      ⟨allocatedHelper, arg, ret, hHelper, hArg, hRet⟩
    have hName : allocatedHelper = helper :=
      Option.some.inj (hHelper.symm.trans hResult)
    subst allocatedHelper
    exact ⟨arg, ret, ⟨hHelper, hArg, hRet⟩⟩

theorem requireIdentifierVisible_preserves_clzAllocation
    (name : Name) (what : String) :
    PreservesClzAllocation (requireIdentifierVisible name what) := by
  intro state state' value hRun hValid
  unfold requireIdentifierVisible identifierVisible at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hVisible : identifierVisibleIn name state.identifierScopes with
  | false =>
      simp [hVisible] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error s!"unknown Yul identifier {name} in {what}" :
        DecodeM (Unit × State)) = .ok (value, state') at hRun
      cases hRun
  | true =>
      simp [hVisible] at hRun
      cases hRun
      exact ClzAllocationExtends.refl state hValid

theorem resolveFunction_preserves_clzAllocation (name : Name) :
    PreservesClzAllocation (resolveFunction name) := by
  intro state state' value hRun hValid
  unfold resolveFunction at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hResolve : resolveFunctionIn name state.functionScopes with
  | none =>
      simp [hResolve] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error s!"unknown Yul function {name}" :
        DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | some _ =>
      simp [hResolve] at hRun
      cases hRun
      exact ClzAllocationExtends.refl state hValid

theorem requireIdentifiersVisible_preserves_clzAllocation
    (names : List Name) (what : String) :
    PreservesClzAllocation (requireIdentifiersVisible names what) := by
  induction names with
  | nil =>
      simp [requireIdentifiersVisible]
      exact PreservesClzAllocation.pure ()
  | cons name rest ih =>
      change PreservesClzAllocation
        (requireIdentifierVisible name what >>= fun _ =>
          requireIdentifiersVisible rest what)
      exact
        PreservesClzAllocation.bind
          (requireIdentifierVisible_preserves_clzAllocation name what)
          (fun _ => ih)

theorem declareIdentifiers_preserves_clzAllocation
    (names : List Name) (description : String) :
    PreservesClzAllocation (declareIdentifiers names description) := by
  intro state state' value hRun hValid
  unfold declareIdentifiers at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hScopes : state.identifierScopes with
  | nil =>
      cases hCollect : collectDeclaredIdentifiers names description [[]] with
      | error err =>
          simp [hScopes, hCollect] at hRun
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
          change (Except.error err : DecodeM (Unit × State)) =
            .ok (value, state') at hRun
          cases hRun
      | ok seen =>
          simp [hScopes, hCollect, StateT.run_set] at hRun
          cases hRun
          exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl
  | cons scope rest =>
      cases hCollect :
          collectDeclaredIdentifiers names description (scope :: rest) with
      | error err =>
          simp [hScopes, hCollect] at hRun
          unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
          change (Except.error err : DecodeM (Unit × State)) =
            .ok (value, state') at hRun
          cases hRun
      | ok seen =>
          simp [hScopes, hCollect, StateT.run_set] at hRun
          cases hRun
          exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem hoistFunctionEntry_preserves_clzAllocation
    (generated : Name) (fn : Frontend.FunctionDef) :
    PreservesClzAllocation (modify fun state =>
      { state with hoistedFunctions := (generated, fn) ::
        state.hoistedFunctions }) := by
  intro state state' value hRun hValid
  simp [StateT.run_modify] at hRun
  cases hRun
  exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem pushIdentifierScope_preserves_clzAllocation :
    PreservesClzAllocation pushIdentifierScope := by
  intro state state' value hRun hValid
  unfold pushIdentifierScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem popIdentifierScope_preserves_clzAllocation :
    PreservesClzAllocation popIdentifierScope := by
  intro state state' value hRun hValid
  unfold popIdentifierScope at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hScopes : state.identifierScopes with
  | nil =>
      simp [hScopes] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "internal frontend error: no identifier scope to pop" :
          DecodeM (Unit × State)) = .ok (value, state') at hRun
      cases hRun
  | cons _ rest =>
      simp [hScopes, StateT.run_set] at hRun
      cases hRun
      exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem pushFunctionScope_preserves_clzAllocation
    (scope : List (Name × Name)) :
    PreservesClzAllocation (pushFunctionScope scope) := by
  intro state state' value hRun hValid
  unfold pushFunctionScope at hRun
  simp [StateT.run_modify] at hRun
  cases hRun
  exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem popFunctionScope_preserves_clzAllocation :
    PreservesClzAllocation popFunctionScope := by
  intro state state' value hRun hValid
  unfold popFunctionScope at hRun
  simp [StateT.run_bind, StateT.run_get] at hRun
  cases hScopes : state.functionScopes with
  | nil =>
      simp [hScopes] at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "internal frontend error: no function scope to pop" :
          DecodeM (Unit × State)) = .ok (value, state') at hRun
      cases hRun
  | cons _ rest =>
      simp [hScopes, StateT.run_set] at hRun
      cases hRun
      exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem freshGeneratedFunctionNameFrom_preserves_clzAllocation
    (stem : Name) (fuel : Nat) :
    PreservesClzAllocation (freshGeneratedFunctionNameFrom stem fuel) := by
  induction fuel with
  | zero =>
      intro state state' value hRun _hValid
      unfold freshGeneratedFunctionNameFrom at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "could not allocate fresh generated Yul function name" :
          DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | succ fuel ih =>
      intro state state' value hRun hValid
      unfold freshGeneratedFunctionNameFrom at hRun
      simp [StateT.run_bind, StateT.run_get, StateT.run_set] at hRun
      let candidate : Name :=
        "__yul_gen_" ++ toString state.nextGeneratedFunctionId ++ "_" ++ stem
      let bumpedState : State :=
        { state with
          nextGeneratedFunctionId := state.nextGeneratedFunctionId + 1 }
      change StateT.run
          (if candidate ∈ state.usedFunctionNames then
            freshGeneratedFunctionNameFrom stem fuel
          else
            (fun _ => candidate) <$> set
              { bumpedState with
                usedFunctionNames := candidate :: state.usedFunctionNames })
          bumpedState = .ok (value, state') at hRun
      have hBumped : ClzAllocationExtends state bumpedState :=
        ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl
      by_cases hContains : candidate ∈ state.usedFunctionNames
      · simp [hContains] at hRun
        exact hBumped.trans (ih hRun hBumped.after_valid)
      · simp [hContains, StateT.run_map, StateT.run_set] at hRun
        simp [pure, Except.pure] at hRun
        rcases hRun with ⟨_hValue, hState⟩
        subst state'
        exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem freshGeneratedFunctionName_preserves_clzAllocation
    (base : Name) :
    PreservesClzAllocation (freshGeneratedFunctionName base) := by
  unfold freshGeneratedFunctionName
  exact
    freshGeneratedFunctionNameFrom_preserves_clzAllocation
      (generatedIdentifierPart base) maxDecodeFuel

theorem freshNonFunctionBindingNameFrom_preserves_clzAllocation
    (stem : Name) (index fuel : Nat) :
    PreservesClzAllocation
      (freshNonFunctionBindingNameFrom stem index fuel) := by
  induction fuel generalizing index with
  | zero =>
      intro state state' value hRun _hValid
      unfold freshNonFunctionBindingNameFrom at hRun
      unfold EvmCompiler.Solidity.RawAst.Elab.throw at hRun
      change (Except.error
        "could not allocate fresh generated Yul binding name" :
          DecodeM (Name × State)) = .ok (value, state') at hRun
      cases hRun
  | succ fuel ih =>
      intro state state' value hRun hValid
      unfold freshNonFunctionBindingNameFrom at hRun
      simp [StateT.run_bind, StateT.run_get] at hRun
      let candidate : Name :=
        if index = 0 then "__yul_" ++ stem else
          "__yul_" ++ stem ++ "_" ++ toString index
      change StateT.run
          (if candidate ∈ state.usedFunctionNames then
            freshNonFunctionBindingNameFrom stem (index + 1) fuel
          else
            (fun _ => candidate) <$> set
              { state with
                usedFunctionNames := candidate :: state.usedFunctionNames })
          state = .ok (value, state') at hRun
      by_cases hContains : candidate ∈ state.usedFunctionNames
      · simp [hContains] at hRun
        exact ih (index + 1) hRun hValid
      · simp [hContains, StateT.run_map, StateT.run_set] at hRun
        simp [pure, Except.pure] at hRun
        rcases hRun with ⟨_hValue, hState⟩
        subst state'
        exact ClzAllocationExtends.of_fields_eq hValid rfl rfl rfl

theorem freshNonFunctionBindingName_preserves_clzAllocation
    (base : Name) :
    PreservesClzAllocation (freshNonFunctionBindingName base) := by
  unfold freshNonFunctionBindingName
  exact
    freshNonFunctionBindingNameFrom_preserves_clzAllocation
      (generatedIdentifierPart base) 0 maxDecodeFuel

namespace Expr

mutual

theorem elaborate_preserves_clzAllocation
    (expr : Raw.Expr) : PreservesClzAllocation (Expr.elaborate expr) := by
  intro state state' value hRun hValid
  cases expr with
  | literal literal =>
      cases literal <;>
        simp [Expr.elaborate, Literal.elaborate] at hRun <;>
        cases hRun <;>
        exact ClzAllocationExtends.refl state hValid
  | identifier name =>
      unfold Expr.elaborate at hRun
      exact
        PreservesClzAllocation.map (fun _ => Frontend.Expr.var name)
          (requireIdentifierVisible_preserves_clzAllocation
            name "expression") hRun hValid
  | functionCall name args =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases args with
        | nil =>
            unfold Expr.elaborate at hRun
            exact PreservesClzAllocation.throw
              "memoryguard expects one argument" hRun hValid
        | cons arg rest =>
            cases rest with
            | nil =>
                unfold Expr.elaborate at hRun
                exact
                  PreservesClzAllocation.map
                    (fun arg =>
                      Frontend.Expr.call .objectBuiltin "memoryguard" [arg])
                    (elaborate_preserves_clzAllocation arg)
                    hRun hValid
            | cons _ _ =>
                unfold Expr.elaborate at hRun
                exact PreservesClzAllocation.throw
                  "memoryguard expects one argument" hRun hValid
      · by_cases hClz : name = "clz"
        · subst name
          cases args with
          | nil =>
              unfold Expr.elaborate at hRun
              exact PreservesClzAllocation.throw "clz expects one argument"
                hRun hValid
          | cons arg rest =>
              cases rest with
              | nil =>
                  unfold Expr.elaborate at hRun
                  exact
                    PreservesClzAllocation.bind
                      (elaborate_preserves_clzAllocation arg)
                      (fun arg =>
                        PreservesClzAllocation.bind
                          ensureClzHelper_preserves_clzAllocation
                          (fun helper => PreservesClzAllocation.pure
                            (Frontend.Expr.call .user helper [arg])))
                      hRun hValid
              | cons _ _ =>
                  unfold Expr.elaborate at hRun
                  exact PreservesClzAllocation.throw "clz expects one argument"
                    hRun hValid
        · unfold Expr.elaborate at hRun
          simp [hMemoryguard, hClz, StateT.run_bind] at hRun
          cases hArgs : (Expr.List.elaborate args).run state with
          | error _ => simp [hArgs] at hRun
          | ok result =>
              rcases result with ⟨args', argState⟩
              have hArgsExt :=
                List.elaborate_preserves_clzAllocation args hArgs hValid
              simp [hArgs] at hRun
              cases hClass : CallClass.classifyCall name with
              | primitive =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hArgsExt
              | user =>
                  simp [hClass] at hRun
                  have hResolveExt :=
                    PreservesClzAllocation.map
                      (fun callee => Frontend.Expr.call .user callee args')
                      (resolveFunction_preserves_clzAllocation name)
                      hRun hArgsExt.after_valid
                  exact hArgsExt.trans hResolveExt
              | objectBuiltin =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hArgsExt
              | dialectBuiltin =>
                  simp [hClass] at hRun
                  cases hRun
                  exact hArgsExt
  termination_by 2 * sizeOf expr
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem List.elaborate_preserves_clzAllocation
    (exprs : List Raw.Expr) :
    PreservesClzAllocation (Expr.List.elaborate exprs) := by
  cases exprs with
  | nil =>
      intro state state' value hRun hValid
      unfold Expr.List.elaborate at hRun
      simp [StateT.run_pure] at hRun
      cases hRun
      exact ClzAllocationExtends.refl state hValid
  | cons expr rest =>
      exact
        PreservesClzAllocation.bind
          (elaborate_preserves_clzAllocation expr)
          (fun head =>
            PreservesClzAllocation.bind
              (List.elaborate_preserves_clzAllocation rest)
              (fun tail => PreservesClzAllocation.pure (head :: tail)))
  termination_by 2 * sizeOf exprs + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end

end Expr

theorem Stmt.List.localFunctionScope_preserves_clzAllocation
    (stmts : List Raw.Stmt) :
    PreservesClzAllocation (Stmt.List.localFunctionScope stmts) := by
  induction stmts with
  | nil =>
      simp [Stmt.List.localFunctionScope]
      exact PreservesClzAllocation.pure []
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest >>= fun tail =>
              if tail.any fun entry => entry.fst == name then
                throw s!"duplicate Yul function {name} in block"
              else
                declareIdentifiers [name] "function" >>= fun _ =>
                  freshGeneratedFunctionName name >>= fun generated =>
                    pure ((name, generated) :: tail))
          exact
            PreservesClzAllocation.bind ih (fun tail => by
              cases hDuplicate :
                  (tail.any fun entry => entry.fst == name) with
              | false =>
                  simp [hDuplicate]
                  exact
                    PreservesClzAllocation.bind
                      (declareIdentifiers_preserves_clzAllocation
                        [name] "function")
                      (fun _ =>
                        PreservesClzAllocation.bind
                          (freshGeneratedFunctionName_preserves_clzAllocation
                            name)
                          (fun generated =>
                            PreservesClzAllocation.pure
                              ((name, generated) :: tail)))
              | true =>
                  simp [hDuplicate]
                  exact PreservesClzAllocation.throw
                    s!"duplicate Yul function {name} in block")
      | block stmts =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | variableDeclaration names value? =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | assignment names value =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | expressionStatement expr =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | switch scrutinee cases default =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | forLoop pre condition post body =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | ifThen condition body =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | «break» =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | «continue» =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih
      | «leave» =>
          change PreservesClzAllocation
            (Stmt.List.localFunctionScope rest)
          exact ih

mutual

theorem Stmt.elaborate_preserves_clzAllocation
    (stmt : Raw.Stmt) : PreservesClzAllocation (Stmt.elaborate stmt) := by
  cases stmt with
  | block stmts =>
      simp only [Stmt.elaborate]
      exact
        PreservesClzAllocation.bind
          (Stmt.List.elaborateBlock_preserves_clzAllocation stmts true)
          (fun stmts => PreservesClzAllocation.pure
            (Frontend.Stmt.block stmts))
  | variableDeclaration names value? =>
      cases value? with
      | none =>
          simp only [Stmt.elaborate]
          exact
            PreservesClzAllocation.bind
              (declareIdentifiers_preserves_clzAllocation names "variable")
              (fun _ => PreservesClzAllocation.pure
                (Frontend.Stmt.letDecl names none))
      | some value =>
          simp only [Stmt.elaborate]
          exact
            PreservesClzAllocation.bind
              (PreservesClzAllocation.map some
                (Expr.elaborate_preserves_clzAllocation value))
              (fun value? =>
                PreservesClzAllocation.bind
                  (declareIdentifiers_preserves_clzAllocation
                    names "variable")
                  (fun _ => PreservesClzAllocation.pure
                    (Frontend.Stmt.letDecl names value?)))
  | assignment names value =>
      simp only [Stmt.elaborate]
      exact
        PreservesClzAllocation.bind
          (requireIdentifiersVisible_preserves_clzAllocation
            names "assignment")
          (fun _ =>
            PreservesClzAllocation.bind
              (Expr.elaborate_preserves_clzAllocation value)
              (fun value => PreservesClzAllocation.pure
                (Frontend.Stmt.assign names value)))
  | expressionStatement expr =>
      simp only [Stmt.elaborate]
      exact
        PreservesClzAllocation.bind
          (Expr.elaborate_preserves_clzAllocation expr)
          (fun expr => PreservesClzAllocation.pure
            (Frontend.Stmt.exprStmt expr))
  | functionDefinition name params returns body =>
      simp only [Stmt.elaborate]
      exact
        PreservesClzAllocation.bind
          (resolveFunction_preserves_clzAllocation name)
          (fun generated =>
            PreservesClzAllocation.bind
              (FunctionDef.elaborate_preserves_clzAllocation
                params returns body)
              (fun fn => PreservesClzAllocation.pure
                (Frontend.Stmt.functionDef generated params returns fn.body)))
  | switch scrutinee cases defaultBody =>
      simp only [Stmt.elaborate]
      exact
        PreservesClzAllocation.bind
          (Expr.elaborate_preserves_clzAllocation scrutinee)
          (fun scrutinee =>
            PreservesClzAllocation.bind
              (Stmt.CaseList.elaborate_preserves_clzAllocation cases)
              (fun cases =>
                PreservesClzAllocation.bind
                  (Stmt.List.elaborateBlock_preserves_clzAllocation
                    defaultBody true)
                  (fun defaultBody => PreservesClzAllocation.pure
                    (Frontend.Stmt.switch scrutinee cases defaultBody))))
  | forLoop pre condition post body =>
      cases hPre : Stmt.List.hasImmediateFunctionDefinition pre with
      | false =>
          simp only [Stmt.elaborate, hPre, Bool.false_eq_true, ↓reduceIte]
          exact
            PreservesClzAllocation.bind
              pushIdentifierScope_preserves_clzAllocation
              (fun _ =>
                PreservesClzAllocation.bind
                  (Stmt.List.elaborateBlock_preserves_clzAllocation pre false)
                  (fun pre =>
                    PreservesClzAllocation.bind
                      (Expr.elaborate_preserves_clzAllocation condition)
                      (fun condition =>
                        PreservesClzAllocation.bind
                          (Stmt.List.elaborateBlock_preserves_clzAllocation
                            post true)
                          (fun post =>
                            PreservesClzAllocation.bind
                              (Stmt.List.elaborateBlock_preserves_clzAllocation
                                body true)
                              (fun body =>
                                PreservesClzAllocation.bind
                                  popIdentifierScope_preserves_clzAllocation
                                  (fun _ => PreservesClzAllocation.pure
                                    (Frontend.Stmt.forLoop
                                      pre condition post body)))))))
      | true =>
          simp only [Stmt.elaborate, hPre, Bool.true_eq_false, ↓reduceIte]
          exact
            PreservesClzAllocation.bind
              pushIdentifierScope_preserves_clzAllocation
              (fun _ =>
                PreservesClzAllocation.bind
                  (Stmt.List.elaborateForInitBlockWithScope_preserves_clzAllocation
                    pre)
                  (fun pre =>
                    PreservesClzAllocation.bind
                      (Expr.elaborate_preserves_clzAllocation condition)
                      (fun condition =>
                        PreservesClzAllocation.bind
                          (Stmt.List.elaborateBlock_preserves_clzAllocation
                            post true)
                          (fun post =>
                            PreservesClzAllocation.bind
                              (Stmt.List.elaborateBlock_preserves_clzAllocation
                                body true)
                              (fun body =>
                                PreservesClzAllocation.bind
                                  popFunctionScope_preserves_clzAllocation
                                  (fun _ =>
                                    PreservesClzAllocation.bind
                                      popIdentifierScope_preserves_clzAllocation
                                      (fun _ => PreservesClzAllocation.pure
                                        (Frontend.Stmt.forLoop
                                          pre condition post body))))))))
  | ifThen condition body =>
      simp only [Stmt.elaborate]
      exact
        PreservesClzAllocation.bind
          (Expr.elaborate_preserves_clzAllocation condition)
          (fun condition =>
            PreservesClzAllocation.bind
              (Stmt.List.elaborateBlock_preserves_clzAllocation body true)
              (fun body => PreservesClzAllocation.pure
                (Frontend.Stmt.ifThen condition body)))
  | «break» =>
      simp only [Stmt.elaborate]
      exact PreservesClzAllocation.pure Frontend.Stmt.break
  | «continue» =>
      simp only [Stmt.elaborate]
      exact PreservesClzAllocation.pure Frontend.Stmt.continue
  | «leave» =>
      simp only [Stmt.elaborate]
      exact PreservesClzAllocation.pure Frontend.Stmt.leave
  termination_by 20 * sizeOf stmt + 18
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborate_preserves_clzAllocation
    (stmts : List Raw.Stmt) :
    PreservesClzAllocation (Stmt.List.elaborate stmts) := by
  cases stmts with
  | nil =>
      simp [Stmt.List.elaborate]
      exact PreservesClzAllocation.pure []
  | cons stmt rest =>
      simp [Stmt.List.elaborate]
      exact
        PreservesClzAllocation.bind
          (Stmt.elaborate_preserves_clzAllocation stmt)
          (fun head =>
            PreservesClzAllocation.bind
              (Stmt.List.elaborate_preserves_clzAllocation rest)
              (fun tail => PreservesClzAllocation.pure (head :: tail)))
  termination_by 20 * sizeOf stmts + 10
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.hoistLocalFunctions_preserves_clzAllocation
    (stmts : List Raw.Stmt) (scope : List (Name × Name)) :
    PreservesClzAllocation (Stmt.List.hoistLocalFunctions stmts scope) := by
  cases stmts with
  | nil =>
      simp [Stmt.List.hoistLocalFunctions]
      exact PreservesClzAllocation.pure ()
  | cons stmt rest =>
      cases stmt with
      | functionDefinition name params returns body =>
          cases hLookup : lookupFunctionInScope name scope with
          | none =>
              simp [Stmt.List.hoistLocalFunctions, hLookup]
              exact PreservesClzAllocation.throw
                s!"internal frontend error: missing generated name for {name}"
          | some generated =>
              simp [Stmt.List.hoistLocalFunctions, hLookup]
              exact
                PreservesClzAllocation.bind
                  (FunctionDef.elaborate_preserves_clzAllocation
                    params returns body)
                  (fun fn =>
                    PreservesClzAllocation.bind
                      (hoistFunctionEntry_preserves_clzAllocation generated fn)
                      (fun _ =>
                        Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                          rest scope))
      | block stmts =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | variableDeclaration names value? =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | assignment names value =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | expressionStatement expr =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | switch scrutinee cases default =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | forLoop pre condition post body =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | ifThen condition body =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | «break» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | «continue» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
      | «leave» =>
          simp [Stmt.List.hoistLocalFunctions]
          exact
            Stmt.List.hoistLocalFunctions_preserves_clzAllocation rest scope
  termination_by 20 * sizeOf stmts + 12
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateBlock_preserves_clzAllocation
    (stmts : List Raw.Stmt) (createsScope : Bool) :
    PreservesClzAllocation (Stmt.List.elaborateBlock stmts createsScope) := by
  cases createsScope with
  | false =>
      simp only [Stmt.List.elaborateBlock, Bool.false_eq_true, ↓reduceIte]
      exact
        PreservesClzAllocation.bind
          (Stmt.List.localFunctionScope_preserves_clzAllocation stmts)
          (fun scope =>
            PreservesClzAllocation.bind
              (pushFunctionScope_preserves_clzAllocation scope)
              (fun _ =>
                PreservesClzAllocation.bind
                  (Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                    stmts scope)
                  (fun _ =>
                    PreservesClzAllocation.bind
                      (Stmt.List.elaborate_preserves_clzAllocation stmts)
                      (fun result =>
                        PreservesClzAllocation.bind
                          popFunctionScope_preserves_clzAllocation
                          (fun _ => PreservesClzAllocation.pure result)))))
  | true =>
      simp only [Stmt.List.elaborateBlock, Bool.true_eq_false, ↓reduceIte]
      exact
        PreservesClzAllocation.bind
          pushIdentifierScope_preserves_clzAllocation
          (fun _ =>
            PreservesClzAllocation.bind
              (Stmt.List.localFunctionScope_preserves_clzAllocation stmts)
              (fun scope =>
                PreservesClzAllocation.bind
                  (pushFunctionScope_preserves_clzAllocation scope)
                  (fun _ =>
                    PreservesClzAllocation.bind
                      (Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                        stmts scope)
                      (fun _ =>
                        PreservesClzAllocation.bind
                          (Stmt.List.elaborate_preserves_clzAllocation stmts)
                          (fun result =>
                            PreservesClzAllocation.bind
                              popFunctionScope_preserves_clzAllocation
                              (fun _ =>
                                PreservesClzAllocation.bind
                                  popIdentifierScope_preserves_clzAllocation
                                  (fun _ =>
                                    PreservesClzAllocation.pure result)))))))
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.List.elaborateForInitBlockWithScope_preserves_clzAllocation
    (stmts : List Raw.Stmt) :
    PreservesClzAllocation
      (Stmt.List.elaborateForInitBlockWithScope stmts) := by
  simp only [Stmt.List.elaborateForInitBlockWithScope]
  exact
    PreservesClzAllocation.bind
      (Stmt.List.localFunctionScope_preserves_clzAllocation stmts)
      (fun scope =>
        PreservesClzAllocation.bind
          (pushFunctionScope_preserves_clzAllocation scope)
          (fun _ =>
            PreservesClzAllocation.bind
              (Stmt.List.hoistLocalFunctions_preserves_clzAllocation
                stmts scope)
              (fun _ => Stmt.List.elaborate_preserves_clzAllocation stmts)))
  termination_by 20 * sizeOf stmts + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem Stmt.CaseList.elaborate_preserves_clzAllocation
    (cases : List (Raw.SwitchCaseValue × List Raw.Stmt)) :
    PreservesClzAllocation (Stmt.CaseList.elaborate cases) := by
  cases cases with
  | nil =>
      simp [Stmt.CaseList.elaborate]
      exact PreservesClzAllocation.pure []
  | cons head rest =>
      rcases head with ⟨value, body⟩
      cases value with
      | literal literal =>
          cases literal <;>
            simp [Stmt.CaseList.elaborate, SwitchCaseValue.elaborate] <;>
            exact
              PreservesClzAllocation.bind
                (Stmt.List.elaborateBlock_preserves_clzAllocation body true)
                (fun body =>
                  PreservesClzAllocation.bind
                    (Stmt.CaseList.elaborate_preserves_clzAllocation rest)
                    (fun rest => PreservesClzAllocation.pure (_ :: rest)))
  termination_by 20 * sizeOf cases + 14
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

theorem FunctionDef.elaborate_preserves_clzAllocation
    (params returns : List Name) (body : List Raw.Stmt) :
    PreservesClzAllocation
      (FunctionDef.elaborate params returns body) := by
  simp only [FunctionDef.elaborate]
  exact
    PreservesClzAllocation.bind
      pushIdentifierScope_preserves_clzAllocation
      (fun _ =>
        PreservesClzAllocation.bind
          (declareIdentifiers_preserves_clzAllocation
            (params ++ returns) "function parameter/result")
          (fun _ =>
            PreservesClzAllocation.bind
              (Stmt.List.elaborateBlock_preserves_clzAllocation body true)
              (fun body =>
                PreservesClzAllocation.bind
                  popIdentifierScope_preserves_clzAllocation
                  (fun _ => PreservesClzAllocation.pure
                    ({ params, returns, body } : Frontend.FunctionDef)))))
  termination_by 20 * sizeOf body + 16
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end

end EvmCompiler.Solidity.RawAst.Elab
