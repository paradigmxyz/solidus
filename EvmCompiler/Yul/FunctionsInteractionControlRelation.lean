import EvmCompiler.Yul.FunctionsInteractionRelation
import EvmCompiler.Yul.FunctionsInteractionPrimitive

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionControlRelation

open FunctionsInteractionRelation

/-- A source lexical destination is represented by the exact variable-domain
snapshot used by Yul's later `restrictStoreTo`. -/
structure SourceScope where
  layout : List Functions.Name
  store : EvmYul.Yul.VarStore
  domain : VarsDomainWithin layout store
  defined : VarsDefinedOn layout store

structure SourceScopes where
  breakScope? : Option SourceScope
  continueScope? : Option SourceScope
  leaveScope? : Option SourceScope

def LayoutWithinScope
    (layout : List Functions.Name) (ctx : Functions.Source.Ctx) : Prop :=
  ∀ name, name ∈ layout → name ∈ ctx.scope

/-- One enabled source control destination and its corresponding target scope.
The source destination may be an outer prefix of the current lexical domain. -/
def ScopeOptionRel (enabled : Bool)
    (sourceScope? : Option SourceScope)
    (targetScope? : Option (List Functions.Name))
    (current : List Functions.Name) : Prop :=
  if enabled then
    ∃ sourceScope targetScope,
      sourceScope? = some sourceScope ∧
        targetScope? = some targetScope ∧
        (∀ name, name ∈ sourceScope.layout → name ∈ current) ∧
        ∀ name, name ∈ sourceScope.layout → name ∈ targetScope
  else
    sourceScope? = none ∧ targetScope? = none

structure ControlContextRel
    (sourceScopes : SourceScopes)
    (layout : List Functions.Name)
    (canBreak canContinue canLeave : Bool)
    (ctx : Functions.Source.Ctx) : Prop where
  scope : LayoutWithinScope layout ctx
  breakScope : ScopeOptionRel canBreak sourceScopes.breakScope?
    ctx.breakScope? layout
  continueScope : ScopeOptionRel canContinue sourceScopes.continueScope?
    ctx.continueScope? layout
  leaveScope : ScopeOptionRel canLeave sourceScopes.leaveScope?
    ctx.leaveScope? layout

namespace ScopeOptionRel

theorem mono
    {enabled : Bool} {sourceScope? : Option SourceScope}
    {targetScope? : Option (List Functions.Name)}
    {before after : List Functions.Name}
    (hRel : ScopeOptionRel enabled sourceScope? targetScope? before)
    (hSubset : ∀ name, name ∈ before → name ∈ after) :
    ScopeOptionRel enabled sourceScope? targetScope? after := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionRel, hEnabled] at hRel ⊢
    obtain ⟨sourceScope, targetScope, hSource, hTarget,
      hCurrent, hTargetScope⟩ := hRel
    exact ⟨sourceScope, targetScope, hSource, hTarget,
      fun name hName => hSubset name (hCurrent name hName), hTargetScope⟩
  · simp [ScopeOptionRel, hEnabled] at hRel ⊢
    exact hRel

theorem enabled_parts
    {sourceScope? : Option SourceScope}
    {targetScope? : Option (List Functions.Name)}
    {current : List Functions.Name}
    (hRel : ScopeOptionRel true sourceScope? targetScope? current) :
    ∃ sourceScope targetScope,
      sourceScope? = some sourceScope ∧
        targetScope? = some targetScope ∧
        (∀ name, name ∈ sourceScope.layout → name ∈ current) ∧
        ∀ name, name ∈ sourceScope.layout → name ∈ targetScope := by
  simpa [ScopeOptionRel] using hRel

theorem source_subset_of_some
    {enabled : Bool} {sourceScope? : Option SourceScope}
    {targetScope? : Option (List Functions.Name)}
    {current : List Functions.Name} {sourceScope : SourceScope}
    (hRel : ScopeOptionRel enabled sourceScope? targetScope? current)
    (hSome : sourceScope? = some sourceScope) :
    ∀ name, name ∈ sourceScope.layout → name ∈ current := by
  cases hEnabled : enabled with
  | false =>
      simp [ScopeOptionRel, hEnabled] at hRel
      rw [hRel.1] at hSome
      simp at hSome
  | true =>
      obtain ⟨candidate, targetScope, hCandidate, _hTarget,
          hCurrent, _hTargetScope⟩ := by
        simpa [hEnabled] using hRel
      rw [hSome] at hCandidate
      cases hCandidate
      exact hCurrent

end ScopeOptionRel

/-- Abrupt control relates the already handler-restricted target state to the
source checkpoint after applying the exact source lexical-scope snapshot.
The source evaluator may apply enclosing block restrictions later; this view
is stable under those compatible restrictions. -/
structure AbruptOutcomeRel
    (scope : SourceScope)
    (source : Yul.InteractionSemantics.State)
    (target : Functions.InteractionSemantics.Outcome) : Prop where
  mode : FunctionsInteractionRelation.ModeRel source target
  state : ScopedStateRel scope.layout
    ((source.restrictStoreTo scope.store).reviveJump) target.state

namespace AbruptOutcomeRel

theorem restrict_outer
    {scope : SourceScope}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.Outcome}
    {outerStore : EvmYul.Yul.VarStore}
    (hRel : AbruptOutcomeRel scope source target)
    (hNonregular : target.mode ≠ .regular)
    (hOuterDefined : ∀ name, name ∈ scope.layout →
      ∃ value, outerStore.lookup name = some value) :
    AbruptOutcomeRel scope (source.restrictStoreTo outerStore) target := by
  obtain ⟨jump, rfl⟩ :=
    ModeRel.target_nonregular_source_checkpoint hRel.mode hNonregular
  cases jump with
  | Break shared vars | Continue shared vars | Leave shared vars =>
      have hStores :
          EvmYul.Yul.State.restrictVarStore
              (EvmYul.Yul.State.restrictVarStore vars outerStore)
              scope.store =
            EvmYul.Yul.State.restrictVarStore vars scope.store := by
        apply VarStoreRestriction.restrict_restrict_of_inner_defined
        intro name value hLookup
        exact hOuterDefined name (scope.domain name value hLookup)
      refine ⟨?_, ?_⟩
      · have hMode := hRel.mode
        cases hTarget : target.mode <;>
          simp [FunctionsInteractionRelation.ModeRel, hTarget,
            EvmYul.Yul.State.restrictStoreTo] at hMode ⊢
      · simpa [EvmYul.Yul.State.restrictStoreTo,
          EvmYul.Yul.State.reviveJump, hStores] using hRel.state

theorem brk
    {current targetScope : List Functions.Name}
    {scope : SourceScope}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {target : Functions.InteractionSemantics.State}
    (hRel : ScopedStateRel current (.Ok sourceShared sourceVars) target)
    (hCurrent : ∀ name, name ∈ scope.layout → name ∈ current)
    (hTarget : ∀ name, name ∈ scope.layout → name ∈ targetScope) :
    AbruptOutcomeRel scope
      (.Checkpoint (.Break sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.brk
        (target.restrictTo targetScope)) := by
  refine ⟨by simp [FunctionsInteractionRelation.ModeRel], ?_⟩
  simpa [EvmYul.Yul.State.restrictStoreTo] using
    hRel.restrictBoth scope.domain scope.defined hCurrent hTarget

theorem cont
    {current targetScope : List Functions.Name}
    {scope : SourceScope}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {target : Functions.InteractionSemantics.State}
    (hRel : ScopedStateRel current (.Ok sourceShared sourceVars) target)
    (hCurrent : ∀ name, name ∈ scope.layout → name ∈ current)
    (hTarget : ∀ name, name ∈ scope.layout → name ∈ targetScope) :
    AbruptOutcomeRel scope
      (.Checkpoint (.Continue sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.cont
        (target.restrictTo targetScope)) := by
  refine ⟨by simp [FunctionsInteractionRelation.ModeRel], ?_⟩
  simpa [EvmYul.Yul.State.restrictStoreTo] using
    hRel.restrictBoth scope.domain scope.defined hCurrent hTarget

theorem leave
    {current targetScope : List Functions.Name}
    {scope : SourceScope}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {target : Functions.InteractionSemantics.State}
    (hRel : ScopedStateRel current (.Ok sourceShared sourceVars) target)
    (hCurrent : ∀ name, name ∈ scope.layout → name ∈ current)
    (hTarget : ∀ name, name ∈ scope.layout → name ∈ targetScope) :
    AbruptOutcomeRel scope
      (.Checkpoint (.Leave sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.leave
        (target.restrictTo targetScope)) := by
  refine ⟨by simp [FunctionsInteractionRelation.ModeRel], ?_⟩
  simpa [EvmYul.Yul.State.restrictStoreTo] using
    hRel.restrictBoth scope.domain scope.defined hCurrent hTarget

end AbruptOutcomeRel

/-- Control-aware completion relation for recursive statements and lists.
Regular completion exposes the statically known outgoing lexical layout;
abrupt completion instead uses its source scope snapshot. -/
inductive ControlDoneRel
    (regularUsed regularLayout : List Functions.Name)
    (sourceScopes : SourceScopes)
    (canBreak canContinue canLeave : Bool) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      FunctionsInteractionPrimitive.ErrorRel source target →
      ControlDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave
        (.error source) (.error target)
  | regular {source target ctx} :
      ScopedStateRel regularLayout source target →
      TargetDomainWithin regularUsed target.vars →
      ControlContextRel sourceScopes regularLayout
        canBreak canContinue canLeave ctx →
      ControlDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source)
        (.ok (Functions.Source.Effectful.Outcome.regular target, ctx))
  | brk {source target ctx scope} :
      sourceScopes.breakScope? = some scope →
      target.mode = .brk →
      AbruptOutcomeRel scope source target →
      ControlDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source) (.ok (target, ctx))
  | cont {source target ctx scope} :
      sourceScopes.continueScope? = some scope →
      target.mode = .cont →
      AbruptOutcomeRel scope source target →
      ControlDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source) (.ok (target, ctx))
  | leave {source target ctx scope} :
      sourceScopes.leaveScope? = some scope →
      target.mode = .leave →
      AbruptOutcomeRel scope source target →
      ControlDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source) (.ok (target, ctx))
  | terminal {source target ctx} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
      ControlDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave
        (.error source) (.ok (target, ctx))

namespace ControlDoneRel

/-- Later compiler phases may reserve additional private locals even when the
selected control path does not execute their lowering. Only regular outcomes
carry the target-domain obligation; abrupt and terminal outcomes are unchanged. -/
theorem monoUsed
    {beforeUsed afterUsed regularLayout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Except EVMException
      (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hSubset : ∀ name, name ∈ beforeUsed → name ∈ afterUsed)
    (hRel : ControlDoneRel beforeUsed regularLayout sourceScopes
      canBreak canContinue canLeave sourceDone targetDone) :
    ControlDoneRel afterUsed regularLayout sourceScopes
      canBreak canContinue canLeave sourceDone targetDone := by
  cases hRel with
  | error hError => exact .error hError
  | regular hScoped hDomain hControl =>
      exact .regular hScoped (hDomain.mono hSubset) hControl
  | brk hScope hMode hAbrupt => exact .brk hScope hMode hAbrupt
  | cont hScope hMode hAbrupt => exact .cont hScope hMode hAbrupt
  | leave hScope hMode hAbrupt => exact .leave hScope hMode hAbrupt
  | terminal hTerminal => exact .terminal hTerminal

end ControlDoneRel

/-- Control-aware completion after a canonical Functions scoped block has
erased its lexical context from the result. This is the adjacent interface
consumed by loop bodies and posts; it retains the same source scopes and
outcome-indexed state relations as `ControlDoneRel`. -/
inductive ControlOutcomeDoneRel
    (regularUsed regularLayout : List Functions.Name)
    (sourceScopes : SourceScopes)
    (canBreak canContinue canLeave : Bool) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except EVMException Functions.InteractionSemantics.Outcome → Prop where
  | error {source target} :
      FunctionsInteractionPrimitive.ErrorRel source target →
      ControlOutcomeDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.error source) (.error target)
  | regular {source target} :
      ScopedStateRel regularLayout source target →
      TargetDomainWithin regularUsed target.vars →
      ControlOutcomeDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source)
        (.ok (Functions.Source.Effectful.Outcome.regular target))
  | brk {source target scope} :
      sourceScopes.breakScope? = some scope →
      target.mode = .brk →
      AbruptOutcomeRel scope source target →
      ControlOutcomeDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source) (.ok target)
  | cont {source target scope} :
      sourceScopes.continueScope? = some scope →
      target.mode = .cont →
      AbruptOutcomeRel scope source target →
      ControlOutcomeDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source) (.ok target)
  | leave {source target scope} :
      sourceScopes.leaveScope? = some scope →
      target.mode = .leave →
      AbruptOutcomeRel scope source target →
      ControlOutcomeDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.ok source) (.ok target)
  | terminal {source target} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
      ControlOutcomeDoneRel regularUsed regularLayout sourceScopes
        canBreak canContinue canLeave (.error source) (.ok target)

namespace ControlOutcomeDoneRel

theorem monoUsed
    {beforeUsed afterUsed regularLayout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Except EVMException Functions.InteractionSemantics.Outcome}
    (hSubset : ∀ name, name ∈ beforeUsed → name ∈ afterUsed)
    (hRel : ControlOutcomeDoneRel beforeUsed regularLayout sourceScopes
      canBreak canContinue canLeave sourceDone targetDone) :
    ControlOutcomeDoneRel afterUsed regularLayout sourceScopes
      canBreak canContinue canLeave sourceDone targetDone := by
  cases hRel with
  | error hError => exact .error hError
  | regular hScoped hDomain =>
      exact .regular hScoped (hDomain.mono hSubset)
  | brk hScope hMode hAbrupt => exact .brk hScope hMode hAbrupt
  | cont hScope hMode hAbrupt => exact .cont hScope hMode hAbrupt
  | leave hScope hMode hAbrupt => exact .leave hScope hMode hAbrupt
  | terminal hTerminal => exact .terminal hTerminal

end ControlOutcomeDoneRel

namespace ControlContextRel

theorem transport
    {sourceScopes : SourceScopes}
    {beforeLayout afterLayout : List Functions.Name}
    {canBreak canContinue canLeave : Bool}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    (hRel : ControlContextRel sourceScopes beforeLayout
      canBreak canContinue canLeave beforeCtx)
    (hSubset : ∀ name, name ∈ beforeLayout → name ∈ afterLayout)
    (hControl : Functions.Source.Ctx.SameControl beforeCtx afterCtx)
    (hScope : LayoutWithinScope afterLayout afterCtx) :
    ControlContextRel sourceScopes afterLayout
      canBreak canContinue canLeave afterCtx := by
  refine
    { scope := hScope
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · rw [← hControl.breakScope]
    exact hRel.breakScope.mono hSubset
  · rw [← hControl.continueScope]
    exact hRel.continueScope.mono hSubset
  · rw [← hControl.leaveScope]
    exact hRel.leaveScope.mono hSubset

def forBodyScopes
    (scope : SourceScope) (outer : SourceScopes) : SourceScopes :=
  { breakScope? := some scope
    continueScope? := some scope
    leaveScope? := outer.leaveScope? }

def forPostScopes (outer : SourceScopes) : SourceScopes :=
  { breakScope? := none
    continueScope? := none
    leaveScope? := outer.leaveScope? }

theorem forBody
    {sourceScopes : SourceScopes}
    {layout : List Functions.Name}
    {canBreak canContinue canLeave : Bool}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hState : ScopedStateRel layout source target)
    (hRel : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx) :
    ∃ sourceScope,
      ControlContextRel (forBodyScopes sourceScope sourceScopes) layout
        true true canLeave
        (ctx.withLoopControl ctx.scope ctx.scope) := by
  rcases hState.state with
    ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
  let sourceScope : SourceScope :=
    { layout := layout
      store := sourceVars
      domain := hState.domain sourceShared sourceVars hSource
      defined := hState.defined sourceShared sourceVars hSource }
  refine ⟨sourceScope, ?_⟩
  refine
    { scope := ?_
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · simpa [Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simp [ScopeOptionRel, forBodyScopes,
      Functions.Source.Ctx.withLoopControl, sourceScope]
    exact hRel.scope
  · simp [ScopeOptionRel, forBodyScopes,
      Functions.Source.Ctx.withLoopControl, sourceScope]
    exact hRel.scope
  · simpa [forBodyScopes, Functions.Source.Ctx.withLoopControl] using
      hRel.leaveScope

theorem forPost
    {sourceScopes : SourceScopes}
    {layout : List Functions.Name}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    (hRel : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx) :
    ControlContextRel (forPostScopes sourceScopes) layout
      false false canLeave ctx.withoutLoopControl := by
  refine
    { scope := ?_
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · simpa [Functions.Source.Ctx.withoutLoopControl] using hRel.scope
  · simp [forPostScopes, ScopeOptionRel,
      Functions.Source.Ctx.withoutLoopControl]
  · simp [forPostScopes, ScopeOptionRel,
      Functions.Source.Ctx.withoutLoopControl]
  · simpa [forPostScopes, Functions.Source.Ctx.withoutLoopControl] using
      hRel.leaveScope

end ControlContextRel

namespace ControlOutcomeDoneRel

/-- Close the loop kernel back into its enclosing statement. The post context
has no break/continue destinations, so those two nominal result constructors
are impossible; regular completion performs the compiler's outer lexical
cleanup while leave and terminal outcomes propagate unchanged. -/
theorem closeFor
    {used layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Except EVMException Functions.InteractionSemantics.Outcome}
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hRel : ControlOutcomeDoneRel used layout
      (ControlContextRel.forPostScopes sourceScopes)
      false false canLeave sourceDone targetDone) :
    ControlDoneRel used layout sourceScopes
      canBreak canContinue canLeave sourceDone
      (match targetDone with
      | .error targetError => .error targetError
      | .ok targetOutcome =>
          match targetOutcome.mode with
          | .regular =>
              .ok
                (Functions.Source.Effectful.Outcome.regular
                  (targetOutcome.state.restrictTo ctx.scope), ctx)
          | .brk | .cont => .error .InvalidInstruction
          | .leave | .halt _ => .ok (targetOutcome, ctx)) := by
  cases hRel with
  | error hError => exact .error hError
  | regular hScoped hDomain =>
      simp only [Functions.Source.Effectful.Outcome.regular_mode]
      exact .regular
        (hScoped.restrictTargetScoped hControl.scope)
        hDomain.restrictTo hControl
  | brk hScope hMode hAbrupt =>
      simp [ControlContextRel.forPostScopes] at hScope
  | cont hScope hMode hAbrupt =>
      simp [ControlContextRel.forPostScopes] at hScope
  | @leave source target scope hScope hMode hAbrupt =>
      have hOuterScope : sourceScopes.leaveScope? = some scope := by
        simpa [ControlContextRel.forPostScopes] using hScope
      simp only [hMode]
      exact .leave hOuterScope hMode hAbrupt
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState => exact .terminal (.stop hState)
      | return_ hState => exact .terminal (.return_ hState)
      | selfdestruct hState => exact .terminal (.selfdestruct hState)
      | revert hState => exact .terminal (.revert hState)

end ControlOutcomeDoneRel

end FunctionsInteractionControlRelation
end Yul
end EvmCompiler
