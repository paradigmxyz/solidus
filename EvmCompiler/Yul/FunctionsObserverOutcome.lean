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
    (ctx : Functions.Source.Ctx) where
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
  freshExtends : Fresh.Extends initial final
  retains :
    outcome.mode = .regular →
      ∀ name, name ∈ entryLayout → name ∈ finalLayout
  layoutWithin :
    StateRelation.Vars.NamesWithin final.used finalLayout

namespace ScopedOpenResult

def appendRegular
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceMiddle sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      ScopedOpenResult contract codeRel program leftLower
        initial middle entryLayout sourceMiddle target ctx)
    (hRegular : left.outcome.mode = .regular)
    (right :
      ScopedOpenResult contract codeRel program rightLower
        middle final left.finalLayout sourceFinal
        left.outcome.state left.finalCtx) :
    ScopedOpenResult contract codeRel program
      (leftLower ++ rightLower) initial final entryLayout
      sourceFinal target ctx := by
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
      freshExtends :=
        Fresh.Extends.trans left.freshExtends right.freshExtends
      retains := fun hRightRegular name hMem =>
        right.retains hRightRegular name
          (left.retains hRegular name hMem)
      layoutWithin := right.layoutWithin }

def appendNonregular
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle final : Fresh.State}
    {entryLayout : List Name}
    {sourceFinal :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      ScopedOpenResult contract codeRel program leftLower
        initial middle entryLayout sourceFinal target ctx)
    (hNonregular : left.outcome.mode ≠ .regular)
    (hSuffixFresh : Fresh.Extends middle final) :
    ScopedOpenResult contract codeRel program
      (leftLower ++ rightLower) initial final entryLayout
      sourceFinal target ctx := by
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
      freshExtends :=
        Fresh.Extends.trans left.freshExtends hSuffixFresh
      retains := fun hRegular =>
        False.elim (hNonregular hRegular)
      layoutWithin := left.layoutWithin.mono hSuffixFresh }

def empty
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
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
      StateRelation.Vars.NamesWithin fresh.used layout) :
    ScopedOpenResult contract codeRel program [] fresh fresh layout
      source target ctx := by
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
      freshExtends := Fresh.Extends.refl fresh
      retains := fun _hRegular _name hMem => hMem
      layoutWithin := hLayout }

end ScopedOpenResult

end FunctionsObserverOutcome
end Yul
end EvmCompiler
