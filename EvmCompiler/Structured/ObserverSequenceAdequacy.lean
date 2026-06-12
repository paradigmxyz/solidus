import EvmCompiler.Structured.ObserverAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Block

/-!
Backward adequacy for adjacent Structured statement sequencing.

This module owns the sequence composition boundary while reusing the shared
Structured-to-TypedCfg observer relation and compiler decomposition facts.
-/

/--
Private regular-fallthrough composition for adjacent statements. Compiler
decomposition and recursive adequacy instances are supplied by the enclosing
mutual theorem.
-/
private theorem adequateWithin_cons_withTail
    {transcript : Trace} {program : Structured.Program}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input tailInput : TypedCfg.Shape}
    {headResult tailResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hFallthrough :
      headResult.fallthrough? = some tailInput)
    (hEntryNotAccepted :
      ∀ targetState,
        ¬ OutcomeSimulation.JumpAt source tokens
            (TypedCfgCompiler.restLabel supply) tailInput accept
            (.jump entry targetState))
    (hTailEntryNotAccepted :
      ∀ targetState,
        ¬ accept
            (.jump (TypedCfgCompiler.restLabel supply) targetState))
    (hHeadAdequate :
      OutcomeSimulation.AdequateWithin
        (fun sourceFuel sourceOutcome =>
          ObserverSemantics.Stmt.Eval
            program sourceFuel stmt source sourceOutcome)
        headResult ctx cfg
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx (TypedCfgCompiler.restLabel supply))
        (OutcomeSimulation.JumpAt source tokens
          (TypedCfgCompiler.restLabel supply) tailInput accept)
        entry input source tokens)
    (hTailAdequate :
      ∀ {tailSource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel { stmts := rest }
              tailSource sourceOutcome)
          tailResult ctx cfg
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx regular)
          accept (TypedCfgCompiler.restLabel supply)
          tailInput tailSource tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := stmt :: rest }
          source sourceOutcome)
      (headResult.append tailResult) ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  have hFinalAccepted :
      OutcomeSimulation.JumpAt source tokens
        (TypedCfgCompiler.restLabel supply) tailInput
        accept targetOutcome :=
    OutcomeSimulation.JumpAt.of_accept hReach.boundary
  obtain
      ⟨prefixFuel, prefixOutcome, prefixTrace,
        hPrefixLe, hPrefix⟩ :=
    OutcomeSimulation.FirstReaches.exists_of_run
      hReach.run hFinalAccepted
  have hPrefixPositive : 0 < prefixFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hPrefix (hEntryNotAccepted target)
  cases prefixFuel with
  | zero =>
      omega
  | succ headTargetFuel =>
      obtain
          ⟨headSourceFuel, headOutcome,
            hHeadEval, hHeadRel, hHeadArtifact⟩ :=
        hHeadAdequate
          (fun headFuel headOutcome targetOutcome headTrace
              hHeadEval hHeadRel hHeadArtifact => by
            rcases headOutcome with ⟨headSource, headMode⟩
            cases headMode with
            | regular =>
                obtain ⟨targetState, rfl, hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                    hHeadRel
                obtain ⟨headOutput, hHeadOutput, hHeadFits⟩ :=
                  hHeadArtifact
                rw [hFallthrough] at hHeadOutput
                have hOutputEq : headOutput = tailInput :=
                  Option.some.inj hHeadOutput.symm
                subst headOutput
                exact
                  OutcomeSimulation.JumpAt.of_rel
                    (ObserverSemantics.Stmt.Eval.returns_eq_of_nonhalting
                      hHeadEval (by simp [ObserverSemantics.Outcome.Nonhalting]))
                    hStateRel hHeadFits
            | brk =>
                obtain ⟨label, targetState, _hLabel, rfl, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.brk_elim
                    hHeadRel
                apply OutcomeSimulation.JumpAt.of_accept
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.brk headSource)
                    (.jump label targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_brk
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    (by simpa [OutcomeSimulation.OutcomeArtifact] using
                      hHeadArtifact)
            | cont =>
                obtain ⟨label, targetState, _hLabel, rfl, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.cont_elim
                    hHeadRel
                apply OutcomeSimulation.JumpAt.of_accept
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.cont headSource)
                    (.jump label targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_cont
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    (by simpa [OutcomeSimulation.OutcomeArtifact] using
                      hHeadArtifact)
            | leave =>
                obtain ⟨label, targetState, _hLabel, rfl, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.leave_elim
                    hHeadRel
                apply OutcomeSimulation.JumpAt.of_accept
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.leave headSource)
                    (.jump label targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_leave
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    (by simpa [OutcomeSimulation.OutcomeArtifact] using
                      hHeadArtifact)
            | halt kind =>
                obtain
                    ⟨targetState, _targetFinal, rfl, _hStep, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.halt_elim
                    hHeadRel
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.halt kind headSource)
                    (.halt kind targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_halt
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    (by simpa [OutcomeSimulation.OutcomeArtifact] using
                      hHeadArtifact))
          hRel hPrefix
      rcases headOutcome with ⟨headSource, headMode⟩
      cases headMode with
      | regular =>
          obtain
              ⟨tailTarget, hPrefixOutcome, hTailRel⟩ :=
            ObserverPreservation.OutcomeSimulation.Rel.regular_elim
              hHeadRel
          subst prefixOutcome
          obtain
              ⟨headOutput, hHeadFallthrough, hHeadBound⟩ :=
            hHeadArtifact
          rw [hFallthrough] at hHeadFallthrough
          have hOutputEq : headOutput = tailInput :=
            Option.some.inj hHeadFallthrough.symm
          subst headOutput
          have hTailAt :
              ObserverPreservation.StateRel.At
                tailInput headSource tokens
                tailTarget prefixTrace :=
            ObserverPreservation.StateRel.At.ofFits
              hTailRel hHeadBound
          have hTailReach :=
            OutcomeSimulation.FirstReaches.tail_of_prefix_jump
              hReach hPrefix hPrefixLe
          have hTailPositive :
              0 < targetFuel + 1 - (headTargetFuel + 1) :=
            OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
              hTailReach (hTailEntryNotAccepted tailTarget)
          cases hResidual :
              targetFuel + 1 - (headTargetFuel + 1) with
          | zero =>
              omega
          | succ tailTargetFuel =>
              obtain
                  ⟨tailSourceFuel, tailOutcome,
                    hTailEval, hTailOutcomeRel, hTailArtifact⟩ :=
                hTailAdequate
                  (fun tailFuel tailOutcome targetOutcome tailTrace
                      hTailEval hTailRel hTailArtifact => by
                    let sourceFuel :=
                      Nat.max headSourceFuel tailFuel
                    have hBlockEval :
                        ObserverSemantics.Block.Eval
                          program (sourceFuel + 1)
                          { stmts := stmt :: rest } source
                          tailOutcome :=
                      Structured.EffectSemantics.Block.Eval.cons_regular
                        (Structured.EffectSemantics.Stmt.Eval.mono
                          hHeadEval (Nat.le_max_left _ _))
                        (Structured.EffectSemantics.Block.Eval.mono
                          hTailEval (Nat.le_max_right _ _))
                    have hArtifact :
                        OutcomeSimulation.OutcomeArtifact
                          (headResult.append tailResult) ctx
                          tailOutcome :=
                      OutcomeSimulation.OutcomeArtifact.replaceRegular
                        hTailArtifact (by
                        intro hMode
                        obtain
                            ⟨output, hTailFallthrough, hOutputBound⟩ :=
                          OutcomeSimulation.OutcomeArtifact.regular
                            hTailArtifact hMode
                        exact
                          ⟨output,
                            by
                              simpa [TypedCfgCompiler.Result.append] using
                                hTailFallthrough,
                            hOutputBound⟩)
                    exact
                      hAccept (sourceFuel + 1) tailOutcome
                        targetOutcome tailTrace hBlockEval
                        hTailRel hArtifact)
                  hTailAt
                  (by simpa [hResidual] using hTailReach)
              let sourceFuel := Nat.max headSourceFuel tailSourceFuel
              have hBlockEval :
                  ObserverSemantics.Block.Eval
                    program (sourceFuel + 1)
                    { stmts := stmt :: rest } source tailOutcome :=
                Structured.EffectSemantics.Block.Eval.cons_regular
                  (Structured.EffectSemantics.Stmt.Eval.mono
                    hHeadEval (Nat.le_max_left _ _))
                  (Structured.EffectSemantics.Block.Eval.mono
                    hTailEval (Nat.le_max_right _ _))
              exact
                ⟨sourceFuel + 1, tailOutcome,
                  hBlockEval, hTailOutcomeRel,
                  OutcomeSimulation.OutcomeArtifact.replaceRegular
                    hTailArtifact (by
                    intro hMode
                    obtain
                        ⟨output, hTailFallthrough, hOutputBound⟩ :=
                      OutcomeSimulation.OutcomeArtifact.regular
                        hTailArtifact hMode
                    exact
                      ⟨output,
                        by
                          simpa [TypedCfgCompiler.Result.append] using
                            hTailFallthrough,
                        hOutputBound⟩)⟩
      | brk =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.brk headSource)
                prefixOutcome prefixTrace := by
            exact
              OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.brk headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_brk hHeadEval)
                hOuterRel
                (by simpa [OutcomeSimulation.OutcomeArtifact] using
                  hHeadArtifact))
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1, Structured.OutcomeT.brk headSource,
              Structured.EffectSemantics.Block.Eval.cons_brk hHeadEval,
              hOuterRel, hHeadArtifact⟩
      | cont =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.cont headSource)
                prefixOutcome prefixTrace := by
            exact
              OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.cont headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_cont hHeadEval)
                hOuterRel
                (by simpa [OutcomeSimulation.OutcomeArtifact] using
                  hHeadArtifact))
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1, Structured.OutcomeT.cont headSource,
              Structured.EffectSemantics.Block.Eval.cons_cont hHeadEval,
              hOuterRel, hHeadArtifact⟩
      | leave =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.leave headSource)
                prefixOutcome prefixTrace := by
            exact
              OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.leave headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_leave hHeadEval)
                hOuterRel
                (by simpa [OutcomeSimulation.OutcomeArtifact] using
                  hHeadArtifact))
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1, Structured.OutcomeT.leave headSource,
              Structured.EffectSemantics.Block.Eval.cons_leave hHeadEval,
              hOuterRel, hHeadArtifact⟩
      | halt kind =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.halt kind headSource)
                prefixOutcome prefixTrace := by
            exact
              OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.halt kind headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_halt hHeadEval)
                hOuterRel
                (by simpa [OutcomeSimulation.OutcomeArtifact] using
                  hHeadArtifact))
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1,
              Structured.OutcomeT.halt kind headSource,
              Structured.EffectSemantics.Block.Eval.cons_halt hHeadEval,
              hOuterRel, hHeadArtifact⟩

/--
Private composition for a head statement whose compiler result has no regular
fallthrough. The strengthened regular artifact makes a regular source result
impossible; every abrupt result is transported to the enclosing continuations.
-/
private theorem adequateWithin_cons_noTail
    {transcript : Trace} {program : Structured.Program}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {headResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hFallthrough : headResult.fallthrough? = none)
    (hEntryNotAccepted :
      ∀ targetState,
        ¬ OutcomeSimulation.JumpAt source tokens
            (TypedCfgCompiler.restLabel supply) input accept
            (.jump entry targetState))
    (hHeadAdequate :
      OutcomeSimulation.AdequateWithin
        (fun sourceFuel sourceOutcome =>
          ObserverSemantics.Stmt.Eval
            program sourceFuel stmt source sourceOutcome)
        headResult ctx cfg
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx (TypedCfgCompiler.restLabel supply))
        (OutcomeSimulation.JumpAt source tokens
          (TypedCfgCompiler.restLabel supply) input accept)
        entry input source tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := stmt :: rest }
          source sourceOutcome)
      headResult ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  have hFinalAccepted :
      OutcomeSimulation.JumpAt source tokens
        (TypedCfgCompiler.restLabel supply) input
        accept targetOutcome :=
    OutcomeSimulation.JumpAt.of_accept hReach.boundary
  obtain
      ⟨prefixFuel, prefixOutcome, prefixTrace,
        hPrefixLe, hPrefix⟩ :=
    OutcomeSimulation.FirstReaches.exists_of_run
      hReach.run hFinalAccepted
  have hPrefixPositive : 0 < prefixFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hPrefix (hEntryNotAccepted target)
  cases prefixFuel with
  | zero =>
      omega
  | succ headTargetFuel =>
      obtain
          ⟨headSourceFuel, headOutcome,
            hHeadEval, hHeadRel, hHeadArtifact⟩ :=
        hHeadAdequate
          (fun headFuel headOutcome targetOutcome headTrace
              hHeadEval hHeadRel hHeadArtifact => by
            rcases headOutcome with ⟨headSource, headMode⟩
            cases headMode with
            | regular =>
                obtain ⟨output, hOutput, _hFits⟩ :=
                  hHeadArtifact
                rw [hFallthrough] at hOutput
                cases hOutput
            | brk =>
                obtain ⟨label, targetState, _hLabel, rfl, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.brk_elim
                    hHeadRel
                apply OutcomeSimulation.JumpAt.of_accept
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.brk headSource)
                    (.jump label targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_brk
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    hHeadArtifact
            | cont =>
                obtain ⟨label, targetState, _hLabel, rfl, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.cont_elim
                    hHeadRel
                apply OutcomeSimulation.JumpAt.of_accept
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.cont headSource)
                    (.jump label targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_cont
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    hHeadArtifact
            | leave =>
                obtain ⟨label, targetState, _hLabel, rfl, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.leave_elim
                    hHeadRel
                apply OutcomeSimulation.JumpAt.of_accept
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.leave headSource)
                    (.jump label targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_leave
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    hHeadArtifact
            | halt kind =>
                obtain
                    ⟨targetState, _targetFinal, rfl, _hStep, _hStateRel⟩ :=
                  ObserverPreservation.OutcomeSimulation.Rel.halt_elim
                    hHeadRel
                exact
                  hAccept (headFuel + 1)
                    (Structured.OutcomeT.halt kind headSource)
                    (.halt kind targetState) headTrace
                    (Structured.EffectSemantics.Block.Eval.cons_halt
                      hHeadEval)
                    (OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
                      (leftRegular := TypedCfgCompiler.restLabel supply)
                      (rightRegular := regular) (by simp) hHeadRel)
                    hHeadArtifact)
          hRel hPrefix
      rcases headOutcome with ⟨headSource, headMode⟩
      cases headMode with
      | regular =>
          obtain
              ⟨headOutput, hHeadFallthrough, _hHeadBound⟩ :=
            hHeadArtifact
          rw [hFallthrough] at hHeadFallthrough
          cases hHeadFallthrough
      | brk =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.brk headSource)
                prefixOutcome prefixTrace :=
            OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
              (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.brk headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_brk hHeadEval)
                hOuterRel hHeadArtifact)
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1, Structured.OutcomeT.brk headSource,
              Structured.EffectSemantics.Block.Eval.cons_brk hHeadEval,
              hOuterRel, hHeadArtifact⟩
      | cont =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.cont headSource)
                prefixOutcome prefixTrace :=
            OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
              (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.cont headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_cont hHeadEval)
                hOuterRel hHeadArtifact)
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1, Structured.OutcomeT.cont headSource,
              Structured.EffectSemantics.Block.Eval.cons_cont hHeadEval,
              hOuterRel, hHeadArtifact⟩
      | leave =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.leave headSource)
                prefixOutcome prefixTrace :=
            OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
              (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.leave headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_leave hHeadEval)
                hOuterRel hHeadArtifact)
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1, Structured.OutcomeT.leave headSource,
              Structured.EffectSemantics.Block.Eval.cons_leave hHeadEval,
              hOuterRel, hHeadArtifact⟩
      | halt kind =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
                  ctx regular)
                tokens (Structured.OutcomeT.halt kind headSource)
                prefixOutcome prefixTrace :=
            OutcomeSimulation.rel_ofContext_change_regular_of_nonregular
              (by simp) hHeadRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hPrefix hPrefixLe
              (hAccept (headSourceFuel + 1)
                (Structured.OutcomeT.halt kind headSource)
                prefixOutcome prefixTrace
                (Structured.EffectSemantics.Block.Eval.cons_halt hHeadEval)
                hOuterRel hHeadArtifact)
          subst targetOutcome
          subst traceFinal
          exact
            ⟨headSourceFuel + 1,
              Structured.OutcomeT.halt kind headSource,
              Structured.EffectSemantics.Block.Eval.cons_halt hHeadEval,
              hOuterRel, hHeadArtifact⟩

/--
Compiler-driven statement-list composition. The recursive statement and tail
instances are private callbacks; successful compiler decomposition and ambient
block inheritance are discharged here.
-/
theorem adequateWithin_cons_of_compileStmtListFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
          (stmt :: rest) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hEntryNotAccepted :
      ∀ joinShape targetState,
        ¬ OutcomeSimulation.JumpAt source tokens
            (TypedCfgCompiler.restLabel supply) joinShape accept
            (.jump entry targetState))
    (hTailEntryNotAccepted :
      ∀ targetState,
        ¬ accept
            (.jump (TypedCfgCompiler.restLabel supply) targetState))
    (hHead :
      ∀ {headResult : TypedCfgCompiler.Result}
        {headAccept : TypedCfg.Outcome → Prop},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        TypedCfgPreservation.BlocksInProgram headResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Stmt.Eval
              program sourceFuel stmt source sourceOutcome)
          headResult ctx cfg
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx (TypedCfgCompiler.restLabel supply))
          headAccept entry input source tokens)
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape}
        {tailSource : ObserverSemantics.State transcript},
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        TypedCfgPreservation.BlocksInProgram tailResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel { stmts := rest }
              tailSource sourceOutcome)
          tailResult ctx cfg
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx regular)
          accept (TypedCfgCompiler.restLabel supply)
          tailInput tailSource tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := stmt :: rest }
          source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens := by
  rcases
      TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
        hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    exact
      adequateWithin_cons_noTail
        hFallthrough (hEntryNotAccepted input)
        (hHead hHeadCompile hBlocks)
  · rcases hWithTail with
      ⟨tailInput, tailResult,
        hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
    exact
      adequateWithin_cons_withTail
        hFallthrough (hEntryNotAccepted tailInput) hTailEntryNotAccepted
        (hHead hHeadCompile hHeadBlocks)
        (fun {_tailSource} =>
          hTail hFallthrough hTailCompile hTailBlocks)

end Block


end ObserverAdequacy
end Structured
end EvmCompiler
