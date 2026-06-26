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

end EvmCompiler.Solidity.RawAst.Elab
