import EvmCompiler.Functions.ObserverSafety
import EvmCompiler.Yul.FunctionsObserverCompiler
import EvmCompiler.Yul.ObserverSafety
import EvmCompiler.Yul.StateRelation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverOutcome

/-!
Outcome-indexed interfaces for the adjacent Yul-to-Functions observer proof.

Open statement and statement-list proofs retain declarations until the owning
Yul block closes them. This module records control agreement and exact lexical
state without defining a compiler, interpreter, replay certificate, or call
oracle.
-/

abbrev Trace := Assembly.ResourceTrace

inductive ProgramInputRel
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript) : Prop where
  | intro :
      source.cursor = target.cursor →
      ∀ (sourceShared : EvmYul.SharedState .Yul)
        (sourceVars : EvmYul.Yul.VarStore),
        source.source = .Ok sourceShared sourceVars →
        StateRelation.Shared.Rel codeRel sourceShared target.source.shared →
        target.source.vars = Locals.Source.Store.empty →
        ProgramInputRel codeRel source target

namespace ProgramInputRel

theorem dispatcherEntry
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel : ProgramInputRel codeRel source target) :
    StateRelation.Replay.ScopedExactRel codeRel []
      (source.withSource
        (EvmYul.Yul.State.mkOk
          (source.source.initcall [] [] [])))
      target := by
  rcases hRel with
    ⟨hCursor, sourceShared, sourceVars, hSource, hShared, hTargetVars⟩
  refine
    ⟨hCursor, sourceShared, default, ?_, hShared, ?_,
      StateRelation.Vars.domainExact_empty⟩
  · rw [hSource]
    rfl
  · rw [hTargetVars]
    exact StateRelation.Vars.scoped_empty

theorem targetDomainWithin
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel : ProgramInputRel codeRel source target)
    (used : List Name) :
    StateRelation.Vars.TargetDomainWithin used target.source.vars := by
  rcases hRel with
    ⟨_hCursor, sourceShared, sourceVars, hSource, hShared, hTargetVars⟩
  intro name value hLookup
  rw [hTargetVars] at hLookup
  simp [Locals.Source.Store.empty] at hLookup

end ProgramInputRel

inductive ProgramStateRel
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript) : Prop where
  | intro :
      source.cursor = target.cursor →
      ∀ (sourceShared : EvmYul.SharedState .Yul)
        (sourceVars : EvmYul.Yul.VarStore),
        source.source = .Ok sourceShared sourceVars →
        StateRelation.Shared.Rel codeRel sourceShared target.source.shared →
        ProgramStateRel codeRel source target

namespace ProgramStateRel

theorem restoreDispatcher
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {caller body :
      ObserverSemantics.SourceReplay.State transcript}
    {targetEntry targetFinal :
      Functions.ObserverSemantics.State transcript}
    (hCaller : ProgramInputRel codeRel caller targetEntry)
    (hBody :
      StateRelation.Replay.ScopedExactRel codeRel []
        (body.withSource body.source.reviveJump) targetFinal) :
    ProgramStateRel codeRel
      (body.withSource
        ((body.source.reviveJump.overwrite? caller.source).setStore
          caller.source))
      targetFinal := by
  rcases hCaller with
    ⟨_hCallerCursor, callerShared, callerVars, hCallerSource,
      _hCallerShared, _hTargetVars⟩
  rcases hBody.2 with
    ⟨bodyShared, bodyVars, hBodySource, hBodyShared,
      _hBodyVars, _hBodyDomain⟩
  have hRevive :
      body.source.reviveJump = .Ok bodyShared bodyVars := by
    simpa using hBodySource
  refine ⟨hBody.1, bodyShared, callerVars, ?_, hBodyShared⟩
  rw [hCallerSource, hRevive]
  rfl

end ProgramStateRel

def ProgramTerminalStateRel
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript) : Prop :=
  source.cursor = target.cursor ∧
    ∃ sourceShared sourceVars,
      source.source = .Ok sourceShared sourceVars ∧
        StateRelation.TerminalShared.Rel codeRel
          sourceShared target.source.shared

inductive ProgramOutcomeRel
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    : ObserverSemantics.SourceReplay.Result transcript →
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript) → Prop where
  | regular
      {source : ObserverSemantics.SourceReplay.State transcript}
      {target : Functions.ObserverSemantics.State transcript}
      (state : ProgramStateRel codeRel source target) :
      ProgramOutcomeRel codeRel
        (.regular source)
        (Functions.Source.Effectful.Outcome.regular target)
  | stop
      {source : ObserverSemantics.SourceReplay.State transcript}
      {value : Word}
      {target : Functions.ObserverSemantics.State transcript}
      (state : ProgramTerminalStateRel codeRel source target) :
      ProgramOutcomeRel codeRel
        (.yulHalt source value)
        (Functions.Source.Effectful.Outcome.halt .stop target)
  | return
      {source : ObserverSemantics.SourceReplay.State transcript}
      {value : Word}
      {target : Functions.ObserverSemantics.State transcript}
      (state : ProgramTerminalStateRel codeRel source target) :
      ProgramOutcomeRel codeRel
        (.yulHalt source value)
        (Functions.Source.Effectful.Outcome.halt .return target)
  | selfdestruct
      {source : ObserverSemantics.SourceReplay.State transcript}
      {value : Word}
      {target : Functions.ObserverSemantics.State transcript}
      (state : ProgramTerminalStateRel codeRel source target) :
      ProgramOutcomeRel codeRel
        (.yulHalt source value)
        (Functions.Source.Effectful.Outcome.halt .selfdestruct target)
  | revert
      {source : ObserverSemantics.SourceReplay.State transcript}
      {target : Functions.ObserverSemantics.State transcript}
      (state : ProgramTerminalStateRel codeRel source target) :
      ProgramOutcomeRel codeRel
        (.revert source)
        (Functions.Source.Effectful.Outcome.halt .revert target)

inductive TerminalFailureRel
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    : Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript) →
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript) → Prop where
  | stop
      {failureState :
        ObserverSemantics.SourceReplay.State transcript}
      {source : EvmYul.Yul.State}
      {value : Word}
      {target : Functions.ObserverSemantics.State transcript}
      (state :
        ProgramTerminalStateRel codeRel
          (failureState.withSource source) target) :
      TerminalFailureRel codeRel
        { exception := .YulHalt source value
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .stop target)
  | return
      {failureState :
        ObserverSemantics.SourceReplay.State transcript}
      {source : EvmYul.Yul.State}
      {value : Word}
      {target : Functions.ObserverSemantics.State transcript}
      (state :
        ProgramTerminalStateRel codeRel
          (failureState.withSource source) target) :
      TerminalFailureRel codeRel
        { exception := .YulHalt source value
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .return target)
  | selfdestruct
      {failureState :
        ObserverSemantics.SourceReplay.State transcript}
      {source : EvmYul.Yul.State}
      {value : Word}
      {target : Functions.ObserverSemantics.State transcript}
      (state :
        ProgramTerminalStateRel codeRel
          (failureState.withSource source) target) :
      TerminalFailureRel codeRel
        { exception := .YulHalt source value
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .selfdestruct target)
  | revert
      {failureState :
        ObserverSemantics.SourceReplay.State transcript}
      {source : EvmYul.Yul.State}
      {target : Functions.ObserverSemantics.State transcript}
      (state :
        ProgramTerminalStateRel codeRel
          (failureState.withSource source) target) :
      TerminalFailureRel codeRel
        { exception := .Revert source
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .revert target)

namespace TerminalFailureRel

theorem program
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hRel : TerminalFailureRel codeRel failure target) :
    ∃ sourceResult,
      ObserverSemantics.SourceReplay.Program.finish (.error failure) =
        .ok sourceResult ∧
      ProgramOutcomeRel codeRel sourceResult target := by
  cases hRel with
  | stop state =>
      exact
        ⟨.yulHalt _ _, rfl, ProgramOutcomeRel.stop state⟩
  | «return» state =>
      exact
        ⟨.yulHalt _ _, rfl, ProgramOutcomeRel.return state⟩
  | selfdestruct state =>
      exact
        ⟨.yulHalt _ _, rfl, ProgramOutcomeRel.selfdestruct state⟩
  | revert state =>
      exact
        ⟨.revert _, rfl, ProgramOutcomeRel.revert state⟩

end TerminalFailureRel

structure SourceControlScopes where
  breakScope? : Option (List Name)
  continueScope? : Option (List Name)
  leaveScope? : Option (List Name)

def LayoutWithinScope
    (layout : List Name) (ctx : Functions.Source.Ctx) : Prop :=
  ∀ name, name ∈ layout → name ∈ ctx.scope

def TargetRestrictedTo
    {transcript : Trace}
    (scope : List Name)
    (target : Functions.ObserverSemantics.State transcript) : Prop :=
  ∃ before : Functions.ObserverSemantics.State transcript,
    target =
      before.withSource (before.source.restrictTo scope)

def AbruptTargetRestriction
    {transcript : Trace}
    (ctx : Functions.Source.Ctx)
    (outcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)) : Prop :=
  match outcome.mode with
  | .regular => True
  | .brk =>
      ∃ scope,
        ctx.breakScope? = some scope ∧
          TargetRestrictedTo scope outcome.state
  | .cont =>
      ∃ scope,
        ctx.continueScope? = some scope ∧
          TargetRestrictedTo scope outcome.state
  | .leave =>
      ∃ scope,
        ctx.leaveScope? = some scope ∧
          TargetRestrictedTo scope outcome.state
  | .halt _ => True

def ScopedTargetRestriction
    {transcript : Trace}
    (ctx : Functions.Source.Ctx)
    (outcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)) : Prop :=
  match outcome.mode with
  | .regular => TargetRestrictedTo ctx.scope outcome.state
  | .brk | .cont | .leave | .halt _ =>
      AbruptTargetRestriction ctx outcome

theorem TargetRestrictedTo.domain
    {transcript : Trace}
    {scope used : List Name}
    {target : Functions.ObserverSemantics.State transcript}
    (hRestricted : TargetRestrictedTo scope target)
    (hScope : StateRelation.Vars.NamesWithin used scope) :
    StateRelation.Vars.TargetDomainWithin used target.source.vars := by
  rcases hRestricted with ⟨before, rfl⟩
  intro name value hLookup
  simp only [Simulation.ResourceReplay.State.withSource_source,
    Locals.Source.State.restrictTo] at hLookup
  by_cases hMem : name ∈ scope
  · exact hScope name hMem
  · rw [Locals.Source.Store.restrictTo_not_mem hMem] at hLookup
    contradiction

theorem AbruptTargetRestriction.transport
    {transcript : Trace}
    {before after : Functions.Source.Ctx}
    {outcome :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hControl : Functions.Source.Ctx.SameControl before after)
    (hRestricted : AbruptTargetRestriction after outcome) :
    AbruptTargetRestriction before outcome := by
  cases hMode : outcome.mode <;>
    simp [AbruptTargetRestriction, hMode] at hRestricted ⊢
  · obtain ⟨scope, hScope, hState⟩ := hRestricted
    exact ⟨scope, hControl.breakScope.trans hScope, hState⟩
  · obtain ⟨scope, hScope, hState⟩ := hRestricted
    exact ⟨scope, hControl.continueScope.trans hScope, hState⟩
  · obtain ⟨scope, hScope, hState⟩ := hRestricted
    exact ⟨scope, hControl.leaveScope.trans hScope, hState⟩

def SourceDefined
    {transcript : Trace}
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript) : Prop :=
  ∀ name, name ∈ layout →
    (source.source.reviveJump.lookup? name).isSome = true

def SourceWithin
    {transcript : Trace}
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript) : Prop :=
  ∀ name, (source.source.reviveJump.lookup? name).isSome = true →
    name ∈ layout

theorem SourceDefined.of_scopedExact
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target) :
    SourceDefined layout source := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource,
      _hShared, _hScoped, hDomain⟩
  intro name hMem
  rw [hSource]
  exact (hDomain name).mpr hMem

theorem SourceWithin.of_scopedExact
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target) :
    SourceWithin layout source := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource,
      _hShared, _hScoped, hDomain⟩
  intro name hSome
  rw [hSource] at hSome
  exact (hDomain name).mp hSome

theorem SourceDefined.restrictStoreTo
    {transcript : Trace}
    {retained outer : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {scope : EvmYul.Yul.VarStore}
    (hDefined : SourceDefined retained source)
    (hScope : StateRelation.Vars.DomainExact outer scope)
    (hSubset : ∀ name, name ∈ retained → name ∈ outer) :
    SourceDefined retained
      (source.withSource (source.source.restrictStoreTo scope)) := by
  rcases source with ⟨source, cursor⟩
  intro name hMem
  have hScopeSome : (scope.lookup name).isSome = true :=
    (hScope name).mpr (hSubset name hMem)
  cases hScopeLookup : scope.lookup name with
  | none =>
      simp [hScopeLookup] at hScopeSome
  | some scopeValue =>
      have hSourceSome := hDefined name hMem
      cases hSource : source with
      | Ok shared vars =>
          simp only [ObserverSemantics.SourceReplay.State.withSource_source,
            EvmYul.Yul.State.restrictStoreTo,
            EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.lookup?]
          rw [StateRelation.VarStore.lookup_restrict_of_some
            vars scope name hScopeLookup]
          simpa [SourceDefined, hSource,
            EvmYul.Yul.State.reviveJump,
            EvmYul.Yul.State.lookup?] using hSourceSome
      | OutOfFuel =>
          simpa [SourceDefined, hSource,
            EvmYul.Yul.State.restrictStoreTo,
            EvmYul.Yul.State.reviveJump,
            EvmYul.Yul.State.lookup?] using hSourceSome
      | Checkpoint jump =>
          cases jump with
          | Continue shared vars =>
              simp only [ObserverSemantics.SourceReplay.State.withSource_source,
                EvmYul.Yul.State.restrictStoreTo,
                EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
                EvmYul.Yul.State.lookup?]
              rw [StateRelation.VarStore.lookup_restrict_of_some
                vars scope name hScopeLookup]
              simpa [SourceDefined, hSource,
                EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
                EvmYul.Yul.State.lookup?] using hSourceSome
          | Break shared vars =>
              simp only [ObserverSemantics.SourceReplay.State.withSource_source,
                EvmYul.Yul.State.restrictStoreTo,
                EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
                EvmYul.Yul.State.lookup?]
              rw [StateRelation.VarStore.lookup_restrict_of_some
                vars scope name hScopeLookup]
              simpa [SourceDefined, hSource,
                EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
                EvmYul.Yul.State.lookup?] using hSourceSome
          | Leave shared vars =>
              simp only [ObserverSemantics.SourceReplay.State.withSource_source,
                EvmYul.Yul.State.restrictStoreTo,
                EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
                EvmYul.Yul.State.lookup?]
              rw [StateRelation.VarStore.lookup_restrict_of_some
                vars scope name hScopeLookup]
              simpa [SourceDefined, hSource,
                EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
                EvmYul.Yul.State.lookup?] using hSourceSome

theorem SourceWithin.restrictStoreTo
    {transcript : Trace}
    {outer : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {scope : EvmYul.Yul.VarStore}
    (hScope : StateRelation.Vars.DomainExact outer scope) :
    SourceWithin outer
      (source.withSource (source.source.restrictStoreTo scope)) := by
  rcases source with ⟨source, cursor⟩
  intro name hSome
  by_contra hNotMem
  have hScopeNone : scope.lookup name = none :=
    StateRelation.Vars.domainExact_isNone_of_not_mem hScope hNotMem
  cases source with
  | Ok shared vars =>
      simp only [ObserverSemantics.SourceReplay.State.withSource_source,
        EvmYul.Yul.State.restrictStoreTo,
        EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.lookup?] at hSome
      rw [StateRelation.VarStore.lookup_restrict_of_none
        vars scope name hScopeNone] at hSome
      simp at hSome
  | OutOfFuel =>
      simp [ObserverSemantics.SourceReplay.State.withSource,
        EvmYul.Yul.State.restrictStoreTo,
        EvmYul.Yul.State.reviveJump,
        EvmYul.Yul.State.lookup?] at hSome
  | Checkpoint jump =>
      cases jump with
      | Continue shared vars =>
          simp only [ObserverSemantics.SourceReplay.State.withSource_source,
            EvmYul.Yul.State.restrictStoreTo,
            EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
            EvmYul.Yul.State.lookup?] at hSome
          rw [StateRelation.VarStore.lookup_restrict_of_none
            vars scope name hScopeNone] at hSome
          simp at hSome
      | Break shared vars =>
          simp only [ObserverSemantics.SourceReplay.State.withSource_source,
            EvmYul.Yul.State.restrictStoreTo,
            EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
            EvmYul.Yul.State.lookup?] at hSome
          rw [StateRelation.VarStore.lookup_restrict_of_none
            vars scope name hScopeNone] at hSome
          simp at hSome
      | Leave shared vars =>
          simp only [ObserverSemantics.SourceReplay.State.withSource_source,
            EvmYul.Yul.State.restrictStoreTo,
            EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive,
            EvmYul.Yul.State.lookup?] at hSome
          rw [StateRelation.VarStore.lookup_restrict_of_none
            vars scope name hScopeNone] at hSome
          simp at hSome

theorem sourceDomainExact_of_source
    {transcript : Trace}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hDefined : SourceDefined layout source)
    (hWithin : SourceWithin layout source)
    (hSource : source.source.reviveJump = .Ok shared store) :
    StateRelation.Vars.DomainExact layout store := by
  intro name
  constructor
  · intro hSome
    apply hWithin name
    simpa [hSource] using hSome
  · intro hMem
    have hSome := hDefined name hMem
    simpa [hSource] using hSome

namespace LayoutWithinScope

theorem monoLayout
    {before after : List Name}
    {ctx : Functions.Source.Ctx}
    (hWithin : LayoutWithinScope after ctx)
    (hSubset : ∀ name, name ∈ before → name ∈ after) :
    LayoutWithinScope before ctx :=
  fun name hMem => hWithin name (hSubset name hMem)

end LayoutWithinScope

def ExitScopeRel
    (sourceControl : SourceControlScopes)
    (ctx : Functions.Source.Ctx)
    (mode : Locals.Source.Mode)
    (layout : List Name) : Prop :=
  match mode with
  | .regular => True
  | .brk =>
      sourceControl.breakScope? = some layout ∧
        ∃ targetScope,
          ctx.breakScope? = some targetScope ∧
            ∀ name, name ∈ layout → name ∈ targetScope
  | .cont =>
      sourceControl.continueScope? = some layout ∧
        ∃ targetScope,
          ctx.continueScope? = some targetScope ∧
            ∀ name, name ∈ layout → name ∈ targetScope
  | .leave =>
      sourceControl.leaveScope? = some layout ∧
        ∃ targetScope,
          ctx.leaveScope? = some targetScope ∧
            ∀ name, name ∈ layout → name ∈ targetScope
  | .halt _ => False

namespace ExitScopeRel

theorem transportTarget
    {sourceControl : SourceControlScopes}
    {before after : Functions.Source.Ctx}
    {mode : Locals.Source.Mode}
    {layout : List Name}
    (hControl : Functions.Source.Ctx.SameControl before after)
    (hExit : ExitScopeRel sourceControl after mode layout) :
    ExitScopeRel sourceControl before mode layout := by
  cases hMode : mode <;>
    simp [ExitScopeRel, hMode] at hExit ⊢
  · obtain ⟨hSource, targetScope, hTarget, hContains⟩ := hExit
    exact
      ⟨hSource, targetScope,
        hControl.breakScope.trans hTarget, hContains⟩
  · obtain ⟨hSource, targetScope, hTarget, hContains⟩ := hExit
    exact
      ⟨hSource, targetScope,
        hControl.continueScope.trans hTarget, hContains⟩
  · obtain ⟨hSource, targetScope, hTarget, hContains⟩ := hExit
    exact
      ⟨hSource, targetScope,
        hControl.leaveScope.trans hTarget, hContains⟩

end ExitScopeRel

def ScopeOptionWithin (enabled : Bool)
    (sourceScope? targetScope? : Option (List Name))
    (layout : List Name) : Prop :=
  if enabled then
    ∃ sourceScope targetScope,
      sourceScope? = some sourceScope ∧
        targetScope? = some targetScope ∧
        (∀ name, name ∈ sourceScope → name ∈ layout) ∧
        ∀ name, name ∈ sourceScope → name ∈ targetScope
  else
    sourceScope? = none ∧ targetScope? = none

namespace ScopeOptionWithin

theorem mono
    {enabled : Bool}
    {sourceScope? targetScope? : Option (List Name)}
    {before after : List Name}
    (hWithin :
      ScopeOptionWithin enabled sourceScope? targetScope? before)
    (hSubset : ∀ name, name ∈ before → name ∈ after) :
    ScopeOptionWithin enabled sourceScope? targetScope? after := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin ⊢
    obtain
      ⟨sourceScope, targetScope, hSource, hTarget,
        hNames, hTargetNames⟩ := hWithin
    exact
      ⟨sourceScope, targetScope, hSource, hTarget,
        fun name hMem => hSubset name (hNames name hMem),
        hTargetNames⟩
  · simp [ScopeOptionWithin, hEnabled] at hWithin ⊢
    exact hWithin

theorem source_subset_of_some
    {enabled : Bool}
    {sourceScope targetScope layout : List Name}
    (hWithin :
      ScopeOptionWithin enabled (some sourceScope)
        (some targetScope) layout) :
    ∀ name, name ∈ sourceScope → name ∈ layout := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin
    exact hWithin.1
  · simp [ScopeOptionWithin, hEnabled] at hWithin

theorem target_contains_of_some
    {enabled : Bool}
    {sourceScope targetScope layout : List Name}
    (hWithin :
      ScopeOptionWithin enabled (some sourceScope)
        (some targetScope) layout) :
    ∀ name, name ∈ sourceScope → name ∈ targetScope := by
  by_cases hEnabled : enabled = true
  · simp [ScopeOptionWithin, hEnabled] at hWithin
    exact hWithin.2
  · simp [ScopeOptionWithin, hEnabled] at hWithin

end ScopeOptionWithin

structure ControlContextRel
    (sourceControl : SourceControlScopes)
    (layout : List Name)
    (canBreak canContinue canLeave : Bool)
    (ctx : Functions.Source.Ctx) : Prop where
  scope : LayoutWithinScope layout ctx
  breakScope :
    ScopeOptionWithin canBreak sourceControl.breakScope?
      ctx.breakScope? layout
  continueScope :
    ScopeOptionWithin canContinue sourceControl.continueScope?
      ctx.continueScope? layout
  leaveScope :
    ScopeOptionWithin canLeave sourceControl.leaveScope?
      ctx.leaveScope? layout

namespace ControlContextRel

def forBodySourceControl
    (layout : List Name)
    (outer : SourceControlScopes) :
    SourceControlScopes :=
  { breakScope? := some layout
    continueScope? := some layout
    leaveScope? := outer.leaveScope? }

def forPostSourceControl
    (outer : SourceControlScopes) :
    SourceControlScopes :=
  { breakScope? := none
    continueScope? := none
    leaveScope? := outer.leaveScope? }

theorem forBody
    {sourceControl : SourceControlScopes}
    {layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx) :
    ControlContextRel (forBodySourceControl layout sourceControl) layout
      true true canLeave
      (ctx.withLoopControl ctx.scope ctx.scope) := by
  refine
    { scope := ?_
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · simpa [Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simpa [forBodySourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simpa [forBodySourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withLoopControl] using hRel.scope
  · simpa [forBodySourceControl, Functions.Source.Ctx.withLoopControl] using
      hRel.leaveScope

theorem forPost
    {sourceControl : SourceControlScopes}
    {layout : List Name}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx) :
    ControlContextRel (forPostSourceControl sourceControl) layout
      false false canLeave ctx.withoutLoopControl := by
  refine
    { scope := ?_
      breakScope := ?_
      continueScope := ?_
      leaveScope := ?_ }
  · simpa [Functions.Source.Ctx.withoutLoopControl] using hRel.scope
  · simp [forPostSourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withoutLoopControl]
  · simp [forPostSourceControl, ScopeOptionWithin,
      Functions.Source.Ctx.withoutLoopControl]
  · simpa [forPostSourceControl, Functions.Source.Ctx.withoutLoopControl] using
      hRel.leaveScope

theorem transport
    {beforeLayout afterLayout : List Name}
    {sourceControl : SourceControlScopes}
    {canBreak canContinue canLeave : Bool}
    {beforeCtx afterCtx : Functions.Source.Ctx}
    (hRel :
      ControlContextRel sourceControl beforeLayout
        canBreak canContinue canLeave beforeCtx)
    (hSubset :
      ∀ name, name ∈ beforeLayout → name ∈ afterLayout)
    (hControl : Functions.Source.Ctx.SameControl beforeCtx afterCtx)
    (hScope : LayoutWithinScope afterLayout afterCtx) :
    ControlContextRel sourceControl afterLayout
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

theorem exitSubset
    {layout exitLayout : List Name}
    {sourceControl : SourceControlScopes}
    {canBreak canContinue canLeave : Bool}
    {ctx : Functions.Source.Ctx}
    {mode : Locals.Source.Mode}
    (hRel :
      ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hExit : ExitScopeRel sourceControl ctx mode exitLayout)
    (hNonregular : mode ≠ .regular) :
    ∀ name, name ∈ exitLayout → name ∈ layout := by
  cases hMode : mode with
  | regular => exact False.elim (hNonregular hMode)
  | brk =>
      simp [ExitScopeRel, hMode] at hExit
      have hWithin := hRel.breakScope
      rcases hExit with
        ⟨hSource, targetScope, hTarget, _hTargetContains⟩
      rw [hSource, hTarget] at hWithin
      exact ScopeOptionWithin.source_subset_of_some hWithin
  | cont =>
      simp [ExitScopeRel, hMode] at hExit
      have hWithin := hRel.continueScope
      rcases hExit with
        ⟨hSource, targetScope, hTarget, _hTargetContains⟩
      rw [hSource, hTarget] at hWithin
      exact ScopeOptionWithin.source_subset_of_some hWithin
  | leave =>
      simp [ExitScopeRel, hMode] at hExit
      have hWithin := hRel.leaveScope
      rcases hExit with
        ⟨hSource, targetScope, hTarget, _hTargetContains⟩
      rw [hSource, hTarget] at hWithin
      exact ScopeOptionWithin.source_subset_of_some hWithin
  | halt kind =>
      simp [ExitScopeRel, hMode] at hExit

end ControlContextRel

def ModeRel {σ : Type} (source : EvmYul.Yul.State)
    (target : Functions.Source.Effectful.Outcome σ) : Prop :=
  match source, target.mode with
  | .Ok _ _, .regular => True
  | .Checkpoint (.Break _ _), .brk => True
  | .Checkpoint (.Continue _ _), .cont => True
  | .Checkpoint (.Leave _ _), .leave => True
  | _, _ => False

namespace ModeRel

theorem regular {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore} {state : σ} :
    ModeRel (.Ok shared vars)
      (Functions.Source.Effectful.Outcome.regular state) := by
  simp only [ModeRel, Functions.Source.Effectful.Outcome.regular_mode]

theorem brk {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore} {state : σ} :
    ModeRel (.Checkpoint (.Break shared vars))
      (Functions.Source.Effectful.Outcome.brk state) := by
  simp only [ModeRel, Functions.Source.Effectful.Outcome.brk_mode]

theorem cont {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore} {state : σ} :
    ModeRel (.Checkpoint (.Continue shared vars))
      (Functions.Source.Effectful.Outcome.cont state) := by
  simp only [ModeRel, Functions.Source.Effectful.Outcome.cont_mode]

theorem leave {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore} {state : σ} :
    ModeRel (.Checkpoint (.Leave shared vars))
      (Functions.Source.Effectful.Outcome.leave state) := by
  simp only [ModeRel, Functions.Source.Effectful.Outcome.leave_mode]

theorem target_regular_source_ok
    {σ : Type} {source : EvmYul.Yul.State}
    {target : Functions.Source.Effectful.Outcome σ}
    (hMode : ModeRel source target)
    (hRegular : target.mode = .regular) :
    ∃ shared vars, source = .Ok shared vars := by
  cases source with
  | Ok shared vars =>
      exact ⟨shared, vars, rfl⟩
  | OutOfFuel =>
      simp [ModeRel, hRegular] at hMode
  | Checkpoint jump =>
      cases jump <;> simp [ModeRel, hRegular] at hMode

theorem source_ok_target_regular
    {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {target : Functions.Source.Effectful.Outcome σ}
    (hMode : ModeRel (.Ok shared vars) target) :
    target.mode = .regular := by
  cases hTarget : target.mode <;>
    simp [ModeRel, hTarget] at hMode ⊢

theorem source_break_target_brk
    {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {target : Functions.Source.Effectful.Outcome σ}
    (hMode : ModeRel (.Checkpoint (.Break shared vars)) target) :
    target.mode = .brk := by
  cases hTarget : target.mode <;>
    simp [ModeRel, hTarget] at hMode ⊢

theorem source_continue_target_cont
    {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {target : Functions.Source.Effectful.Outcome σ}
    (hMode : ModeRel (.Checkpoint (.Continue shared vars)) target) :
    target.mode = .cont := by
  cases hTarget : target.mode <;>
    simp [ModeRel, hTarget] at hMode ⊢

theorem source_leave_target_leave
    {σ : Type} {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {target : Functions.Source.Effectful.Outcome σ}
    (hMode : ModeRel (.Checkpoint (.Leave shared vars)) target) :
    target.mode = .leave := by
  cases hTarget : target.mode <;>
    simp [ModeRel, hTarget] at hMode ⊢

theorem target_nonregular_source_checkpoint
    {σ : Type} {source : EvmYul.Yul.State}
    {target : Functions.Source.Effectful.Outcome σ}
    (hMode : ModeRel source target)
    (hNonregular : target.mode ≠ .regular) :
    ∃ jump, source = .Checkpoint jump := by
  cases source with
  | Ok shared vars =>
      have hRegular :=
        source_ok_target_regular
          (shared := shared) (vars := vars) hMode
      contradiction
  | OutOfFuel =>
      cases hTarget : target.mode <;>
        simp [ModeRel, hTarget] at hMode
  | Checkpoint jump =>
      exact ⟨jump, rfl⟩

end ModeRel

structure ScopedOutcomeRel
    {transcript : Trace}
    (codeRel : StateRelation.CodeRel)
    (layout : List Name)
    (source : ObserverSemantics.SourceReplay.State transcript)
    (target :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)) : Prop where
  mode : ModeRel source.source target
  state :
    StateRelation.Replay.ScopedRel codeRel layout
      (source.withSource source.source.reviveJump) target.state
  exact :
    target.mode = .regular →
      StateRelation.Replay.ScopedExactRel codeRel layout
        (source.withSource source.source.reviveJump) target.state

namespace ScopedOutcomeRel

theorem regular
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hSource : source.source = .Ok shared vars)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target) :
    ScopedOutcomeRel codeRel layout source
      (Functions.Source.Effectful.Outcome.regular target) := by
  have hRevive : source.source.reviveJump = source.source := by
    rw [hSource]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hSource]
    exact ModeRel.regular
  · exact
      StateRelation.Replay.scopedRel_of_scopedExact
        (by simpa [hRevive] using hRel)
  · intro _hRegular
    simpa [hRevive] using hRel

theorem brk
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hSource : source.source = .Checkpoint (.Break shared vars))
    (hRel :
      StateRelation.Replay.ScopedRel codeRel layout
        (source.withSource (.Ok shared vars)) target) :
    ScopedOutcomeRel codeRel layout source
      (Functions.Source.Effectful.Outcome.brk target) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hSource]
    exact ModeRel.brk
  · simpa [hSource] using hRel
  · intro hRegular
    exact
      (Functions.Source.Effectful.Outcome.brk_not_regular target
        hRegular).elim

theorem cont
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hSource : source.source = .Checkpoint (.Continue shared vars))
    (hRel :
      StateRelation.Replay.ScopedRel codeRel layout
        (source.withSource (.Ok shared vars)) target) :
    ScopedOutcomeRel codeRel layout source
      (Functions.Source.Effectful.Outcome.cont target) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hSource]
    exact ModeRel.cont
  · simpa [hSource] using hRel
  · intro hRegular
    exact
      (Functions.Source.Effectful.Outcome.cont_not_regular target
        hRegular).elim

theorem leave
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hSource : source.source = .Checkpoint (.Leave shared vars))
    (hRel :
      StateRelation.Replay.ScopedRel codeRel layout
        (source.withSource (.Ok shared vars)) target) :
    ScopedOutcomeRel codeRel layout source
      (Functions.Source.Effectful.Outcome.leave target) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hSource]
    exact ModeRel.leave
  · simpa [hSource] using hRel
  · intro hRegular
    exact
      (Functions.Source.Effectful.Outcome.leave_not_regular target
        hRegular).elim

/--
Close a nonregular source block against an outer lexical store while leaving
the already handler-restricted target outcome unchanged.
-/
theorem restrictNonregularSource
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {retained outer : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target :
      Functions.Source.Effectful.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {scopeVars : EvmYul.Yul.VarStore}
    (hRel : ScopedOutcomeRel codeRel retained source target)
    (hNonregular : target.mode ≠ .regular)
    (hScope : StateRelation.Vars.DomainExact outer scopeVars)
    (hSubset : ∀ name, name ∈ retained → name ∈ outer) :
    ScopedOutcomeRel codeRel retained
      (source.withSource
        (source.source.restrictStoreTo scopeVars))
      target := by
  obtain ⟨jump, hSource⟩ :=
    ModeRel.target_nonregular_source_checkpoint hRel.mode hNonregular
  cases jump with
  | Continue shared vars =>
      refine ⟨?_, ?_, ?_⟩
      · have hModeRel := hRel.mode
        cases hMode : target.mode <;>
          simp [ModeRel, hSource, hMode,
            EvmYul.Yul.State.restrictStoreTo] at hModeRel ⊢
      · have hRevived :
            (source.withSource source.source.reviveJump).source =
              .Ok shared vars := by
          change source.source.reviveJump = .Ok shared vars
          rw [hSource]
          rfl
        have hRestricted :=
          StateRelation.Replay.scopedRel_restrict_source_outer
            (source :=
              source.withSource source.source.reviveJump)
            (hSource := hRevived)
            hRel.state hScope hSubset
        simpa [hSource, EvmYul.Yul.State.restrictStoreTo] using hRestricted
      · exact fun hRegular => False.elim (hNonregular hRegular)
  | Break shared vars =>
      refine ⟨?_, ?_, ?_⟩
      · have hModeRel := hRel.mode
        cases hMode : target.mode <;>
          simp [ModeRel, hSource, hMode,
            EvmYul.Yul.State.restrictStoreTo] at hModeRel ⊢
      · have hRevived :
            (source.withSource source.source.reviveJump).source =
              .Ok shared vars := by
          change source.source.reviveJump = .Ok shared vars
          rw [hSource]
          rfl
        have hRestricted :=
          StateRelation.Replay.scopedRel_restrict_source_outer
            (source :=
              source.withSource source.source.reviveJump)
            (hSource := hRevived)
            hRel.state hScope hSubset
        simpa [hSource, EvmYul.Yul.State.restrictStoreTo] using hRestricted
      · exact fun hRegular => False.elim (hNonregular hRegular)
  | Leave shared vars =>
      refine ⟨?_, ?_, ?_⟩
      · have hModeRel := hRel.mode
        cases hMode : target.mode <;>
          simp [ModeRel, hSource, hMode,
            EvmYul.Yul.State.restrictStoreTo] at hModeRel ⊢
      · have hRevived :
            (source.withSource source.source.reviveJump).source =
              .Ok shared vars := by
          change source.source.reviveJump = .Ok shared vars
          rw [hSource]
          rfl
        have hRestricted :=
          StateRelation.Replay.scopedRel_restrict_source_outer
            (source :=
              source.withSource source.source.reviveJump)
            (hSource := hRevived)
            hRel.state hScope hSubset
        simpa [hSource, EvmYul.Yul.State.restrictStoreTo] using hRestricted
      · exact fun hRegular => False.elim (hNonregular hRegular)

end ScopedOutcomeRel

structure ScopedOpenResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (lower : List Functions.Stmt)
    (initial final : Fresh.State)
    (entryLayout : List Name)
    (sourceFinal : ObserverSemantics.SourceReplay.State transcript)
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx)
    {sourceControl : SourceControlScopes} where
  finalLayout : List Name
  outcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  finalCtx : Functions.Source.Ctx
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel { stmts := lower } target =
        .ok (outcome, finalCtx)
  relation :
    ScopedOutcomeRel codeRel finalLayout sourceFinal outcome
  domain :
    StateRelation.Vars.TargetDomainWithin
      final.used outcome.state.source.vars
  scope :
    StateRelation.Vars.NamesWithin final.used finalCtx.scope
  control : Functions.Source.Ctx.SameControl ctx finalCtx
  freshExtends : Fresh.Extends initial final
  retains :
    outcome.mode = .regular →
      ∀ name, name ∈ entryLayout → name ∈ finalLayout
  layoutWithin :
    StateRelation.Vars.NamesWithin final.used finalLayout
  sourceDefined : SourceDefined finalLayout sourceFinal
  abruptTargetRestriction : AbruptTargetRestriction ctx outcome
  layoutScope :
    outcome.mode = .regular →
      LayoutWithinScope finalLayout finalCtx
  exitScope : ExitScopeRel sourceControl ctx outcome.mode finalLayout

namespace ScopedOpenResult

def appendRegular
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceMiddle sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      ScopedOpenResult contract codeRel program leftLower
        initial middle entryLayout sourceMiddle target ctx
        (sourceControl := sourceControl))
    (hRegular : left.outcome.mode = .regular)
    (right :
      ScopedOpenResult contract codeRel program rightLower
        middle final left.finalLayout sourceFinal
        left.outcome.state left.finalCtx
        (sourceControl := sourceControl)) :
    ScopedOpenResult contract codeRel program
      (leftLower ++ rightLower) initial final entryLayout
      sourceFinal target ctx (sourceControl := sourceControl) := by
  have hLeftOutcome :
      left.outcome =
        Functions.Source.Effectful.Outcome.regular
          left.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  have hLeftRun :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx fuel { stmts := leftLower } target =
          .ok
            (Functions.Source.Effectful.Outcome.regular
              left.outcome.state,
              left.finalCtx) := by
    rcases left.run with ⟨fuel, hRun⟩
    rw [hLeftOutcome] at hRun
    exact ⟨fuel, hRun⟩
  exact
    { finalLayout := right.finalLayout
      outcome := right.outcome
      finalCtx := right.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program leftLower rightLower ctx left.finalCtx target
          left.outcome.state right.outcome right.finalCtx
          hLeftRun right.run
      relation := right.relation
      domain := right.domain
      scope := right.scope
      control :=
        Functions.Source.Ctx.SameControl.trans
          left.control right.control
      freshExtends :=
        Fresh.Extends.trans left.freshExtends right.freshExtends
      retains := fun hRightRegular name hMem =>
        right.retains hRightRegular name
          (left.retains hRegular name hMem)
      layoutWithin := right.layoutWithin
      sourceDefined := right.sourceDefined
      abruptTargetRestriction :=
        AbruptTargetRestriction.transport left.control
          right.abruptTargetRestriction
      layoutScope := right.layoutScope
      exitScope := by
        have hExit := right.exitScope
        cases hMode : right.outcome.mode <;>
          simp [ExitScopeRel, hMode] at hExit ⊢
        · rcases hExit with
            ⟨hSource, targetScope, hTarget, hWithin⟩
          exact
            ⟨hSource, targetScope,
              left.control.breakScope.trans hTarget,
              hWithin⟩
        · rcases hExit with
            ⟨hSource, targetScope, hTarget, hWithin⟩
          exact
            ⟨hSource, targetScope,
              left.control.continueScope.trans hTarget,
              hWithin⟩
        · rcases hExit with
            ⟨hSource, targetScope, hTarget, hWithin⟩
          exact
            ⟨hSource, targetScope,
              left.control.leaveScope.trans hTarget,
              hWithin⟩ }

def appendNonregular
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      ScopedOpenResult contract codeRel program leftLower
        initial middle entryLayout sourceFinal target ctx
        (sourceControl := sourceControl))
    (hNonregular : left.outcome.mode ≠ .regular)
    (hSuffixFresh : Fresh.Extends middle final) :
    ScopedOpenResult contract codeRel program
      (leftLower ++ rightLower) initial final entryLayout
      sourceFinal target ctx (sourceControl := sourceControl) := by
  exact
    { finalLayout := left.finalLayout
      outcome := left.outcome
      finalCtx := left.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_nonregular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program leftLower rightLower ctx target left.outcome
          left.finalCtx left.run hNonregular
      relation := left.relation
      domain := left.domain.mono hSuffixFresh
      scope := left.scope.mono hSuffixFresh
      control := left.control
      freshExtends :=
        Fresh.Extends.trans left.freshExtends hSuffixFresh
      retains := fun hRegular =>
        False.elim (hNonregular hRegular)
      layoutWithin := left.layoutWithin.mono hSuffixFresh
      sourceDefined := left.sourceDefined
      abruptTargetRestriction := left.abruptTargetRestriction
      layoutScope := fun hRegular =>
        False.elim (hNonregular hRegular)
      exitScope := left.exitScope }

def empty
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : SourceControlScopes}
    {fresh : Fresh.State}
    {layout : List Name}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        fresh.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin fresh.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin fresh.used layout)
    (hLayoutScope : LayoutWithinScope layout ctx) :
    ScopedOpenResult contract codeRel program [] fresh fresh layout
      source target ctx (sourceControl := sourceControl) := by
  have hOutcomeRel :
      ScopedOutcomeRel codeRel layout source
        (Functions.Source.Effectful.Outcome.regular target) := by
    obtain
        ⟨sourceShared, sourceVars, hSource,
          _hShared, _hScoped, _hSourceDomain⟩ :=
      hRel.2
    exact ScopedOutcomeRel.regular hSource hRel
  exact
    { finalLayout := layout
      outcome := Functions.Source.Effectful.Outcome.regular target
      finalCtx := ctx
      run :=
        ⟨1,
          Functions.Source.Effectful.Block.runOpen_nil
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx 0 target⟩
      relation := hOutcomeRel
      domain := hDomain
      scope := hScope
      control := Functions.Source.Ctx.SameControl.refl ctx
      freshExtends := Fresh.Extends.refl fresh
      retains := fun _hRegular _name hMem => hMem
      layoutWithin := hLayout
      sourceDefined := SourceDefined.of_scopedExact hRel
      abruptTargetRestriction := by
        simp [AbruptTargetRestriction]
      layoutScope := fun _hRegular => hLayoutScope
      exitScope := by
        simp [ExitScopeRel] }

end ScopedOpenResult

end FunctionsObserverOutcome
end Yul
end EvmCompiler
