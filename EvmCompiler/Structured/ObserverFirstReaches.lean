import EvmCompiler.Structured.ObserverGeneratedBoundary

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace OutcomeSimulation

/--
Execution to the first target outcome owned by the Structured fragment.

This is stated entirely with the existing TypedCfg observer interpreter.
Minimality supplies the compositional stopping rule needed by backward
adequacy; it is not a replay trace or a second control interpreter.
-/
structure FirstReaches
    (program : TypedCfg.Program)
    (accept : TypedCfg.Outcome → Prop)
    (fuel : Nat) (entry : Assembly.Label)
    (initial : EVMState) (initialTrace : Trace)
    (outcome : TypedCfg.Outcome) (finalTrace : Trace) : Prop where
  run :
    TypedCfg.ObserverSemantics.Program.runN
        program fuel entry initial initialTrace =
      .ok (outcome, finalTrace)
  boundary : accept outcome
  minimal :
    ∀ prefixFuel, prefixFuel < fuel →
      ∀ prefixOutcome prefixTrace,
        TypedCfg.ObserverSemantics.Program.runN
            program prefixFuel entry initial initialTrace =
          .ok (prefixOutcome, prefixTrace) →
        ¬ accept prefixOutcome

abbrev ReachesBoundary
    (program : TypedCfg.Program) (continuations : Continuations) :=
  FirstReaches program (TargetBoundary continuations)

namespace ReachesBoundary

theorem fuel_pos_of_entry_not_boundary
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations fuel
        entry initial initialTrace outcome finalTrace)
    (hEntry :
      ¬ TargetBoundary continuations (.jump entry initial)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      have hRun := hReach.run
      simp only
        [TypedCfg.ObserverSemantics.Program.runN_zero] at hRun
      cases hRun
      exact False.elim (hEntry hReach.boundary)
  | succ fuel =>
      omega

theorem tail_of_step_jump
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry next : Assembly.Label}
    {initial middle : EVMState}
    {initialTrace middleTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (.jump next middle, middleTrace)) :
    ReachesBoundary program continuations fuel
      next middle middleTrace outcome finalTrace := by
  refine ⟨?_, hReach.boundary, ?_⟩
  · have hRun := hReach.run
    rw [TypedCfg.ObserverSemantics.Program.runN_succ,
      hStep] at hRun
    exact hRun
  · intro prefixFuel hPrefix prefixOutcome prefixTrace
      hPrefixRun hPrefixBoundary
    have hOriginalPrefix :
        TypedCfg.ObserverSemantics.Program.runN
            program (prefixFuel + 1) entry initial initialTrace =
          .ok (prefixOutcome, prefixTrace) := by
      rw [TypedCfg.ObserverSemantics.Program.runN_succ, hStep]
      exact hPrefixRun
    exact
      hReach.minimal (prefixFuel + 1) (by omega)
        prefixOutcome prefixTrace hOriginalPrefix hPrefixBoundary

theorem fuel_eq_one_of_step_boundary
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace firstTrace : Trace}
    {outcome firstOutcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (firstOutcome, firstTrace))
    (hBoundary : TargetBoundary continuations firstOutcome) :
    fuel = 0 := by
  by_contra hFuel
  have hOneLt : 1 < fuel + 1 := by omega
  exact
    hReach.minimal 1 hOneLt firstOutcome firstTrace
      (TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep)
      hBoundary

theorem outcome_eq_of_step_boundary
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace firstTrace : Trace}
    {outcome firstOutcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (firstOutcome, firstTrace))
    (hBoundary : TargetBoundary continuations firstOutcome) :
    outcome = firstOutcome ∧ finalTrace = firstTrace := by
  have hFuel :=
    fuel_eq_one_of_step_boundary hReach hStep hBoundary
  subst fuel
  have hOne :=
    TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep
  have hRun := hReach.run
  rw [hOne] at hRun
  simpa only [Prod.mk.injEq] using Except.ok.inj hRun.symm

end ReachesBoundary

namespace FirstReaches

theorem fuel_pos_of_entry_not_accepted
    {program : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hReach :
      FirstReaches program accept fuel
        entry initial initialTrace outcome finalTrace)
    (hEntry : ¬ accept (.jump entry initial)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      have hRun := hReach.run
      simp only
        [TypedCfg.ObserverSemantics.Program.runN_zero] at hRun
      cases hRun
      exact False.elim (hEntry hReach.boundary)
  | succ fuel =>
      omega

theorem tail_of_step_jump
    {program : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {fuel : Nat} {entry next : Assembly.Label}
    {initial middle : EVMState}
    {initialTrace middleTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hReach :
      FirstReaches program accept (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (.jump next middle, middleTrace)) :
    FirstReaches program accept fuel
      next middle middleTrace outcome finalTrace := by
  refine ⟨?_, hReach.boundary, ?_⟩
  · have hRun := hReach.run
    rw [TypedCfg.ObserverSemantics.Program.runN_succ,
      hStep] at hRun
    exact hRun
  · intro prefixFuel hPrefix prefixOutcome prefixTrace
      hPrefixRun hPrefixBoundary
    have hOriginalPrefix :
        TypedCfg.ObserverSemantics.Program.runN
            program (prefixFuel + 1) entry initial initialTrace =
          .ok (prefixOutcome, prefixTrace) := by
      rw [TypedCfg.ObserverSemantics.Program.runN_succ, hStep]
      exact hPrefixRun
    exact
      hReach.minimal (prefixFuel + 1) (by omega)
        prefixOutcome prefixTrace hOriginalPrefix hPrefixBoundary

theorem outcome_eq_of_step_accepted
    {program : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace firstTrace : Trace}
    {outcome firstOutcome : TypedCfg.Outcome}
    (hReach :
      FirstReaches program accept (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (firstOutcome, firstTrace))
    (hAccept : accept firstOutcome) :
    outcome = firstOutcome ∧ finalTrace = firstTrace := by
  have hFuel : fuel = 0 := by
    by_contra hFuel
    exact
      hReach.minimal 1 (by omega) firstOutcome firstTrace
        (TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep)
        hAccept
  subst fuel
  have hOne :=
    TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep
  have hRun := hReach.run
  rw [hOne] at hRun
  simpa only [Prod.mk.injEq] using Except.ok.inj hRun.symm

theorem exists_of_run
    {program : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hRun :
      TypedCfg.ObserverSemantics.Program.runN
          program fuel entry initial initialTrace =
        .ok (outcome, finalTrace))
    (hAccept : accept outcome) :
    ∃ prefixFuel prefixOutcome prefixTrace,
      prefixFuel ≤ fuel ∧
        FirstReaches program accept prefixFuel
          entry initial initialTrace prefixOutcome prefixTrace := by
  classical
  let P : Nat → Prop :=
    fun currentFuel =>
      ∃ currentOutcome currentTrace,
        TypedCfg.ObserverSemantics.Program.runN
            program currentFuel entry initial initialTrace =
          .ok (currentOutcome, currentTrace) ∧
        accept currentOutcome
  have hExists : ∃ currentFuel, P currentFuel :=
    ⟨fuel, outcome, finalTrace, hRun, hAccept⟩
  let prefixFuel := Nat.find hExists
  have hSpec : P prefixFuel := by
    simpa [prefixFuel] using Nat.find_spec hExists
  rcases hSpec with
    ⟨prefixOutcome, prefixTrace, hPrefixRun, hPrefixAccept⟩
  refine
    ⟨prefixFuel, prefixOutcome, prefixTrace, ?_,
      hPrefixRun, hPrefixAccept, ?_⟩
  · exact
      Nat.find_min' hExists
        ⟨outcome, finalTrace, hRun, hAccept⟩
  · intro currentFuel hCurrent currentOutcome currentTrace
      hCurrentRun hCurrentAccept
    exact
      Nat.find_min hExists hCurrent
        ⟨currentOutcome, currentTrace,
          hCurrentRun, hCurrentAccept⟩

theorem remaining_run_of_jump
    {program : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {fullFuel prefixFuel : Nat} {entry next : Assembly.Label}
    {initial middle : EVMState}
    {initialTrace middleTrace finalTrace : Trace}
    {finalOutcome : TypedCfg.Outcome}
    (hFull :
      TypedCfg.ObserverSemantics.Program.runN
          program fullFuel entry initial initialTrace =
        .ok (finalOutcome, finalTrace))
    (hPrefix :
      FirstReaches program accept prefixFuel
        entry initial initialTrace
        (.jump next middle) middleTrace)
    (hLe : prefixFuel ≤ fullFuel) :
    TypedCfg.ObserverSemantics.Program.runN
        program (fullFuel - prefixFuel)
        next middle middleTrace =
      .ok (finalOutcome, finalTrace) := by
  have hCompose :=
    TypedCfg.ObserverSemantics.Program.runN_add_of_jump
      (restFuel := fullFuel - prefixFuel) hPrefix.run
  have hFuel :
      prefixFuel + (fullFuel - prefixFuel) = fullFuel := by
    omega
  rw [hFuel, hFull] at hCompose
  exact hCompose.symm

theorem tail_of_prefix_jump
    {program : TypedCfg.Program}
    {accept prefixAccept : TypedCfg.Outcome → Prop}
    {fullFuel prefixFuel : Nat} {entry next : Assembly.Label}
    {initial middle : EVMState}
    {initialTrace middleTrace finalTrace : Trace}
    {finalOutcome : TypedCfg.Outcome}
    (hFull :
      FirstReaches program accept fullFuel
        entry initial initialTrace finalOutcome finalTrace)
    (hPrefix :
      FirstReaches program prefixAccept prefixFuel
        entry initial initialTrace
        (.jump next middle) middleTrace)
    (hLe : prefixFuel ≤ fullFuel) :
    FirstReaches program accept (fullFuel - prefixFuel)
      next middle middleTrace finalOutcome finalTrace := by
  refine
    ⟨remaining_run_of_jump hFull.run hPrefix hLe,
      hFull.boundary, ?_⟩
  intro tailFuel hTailLt tailOutcome tailTrace
    hTailRun hTailAccepted
  have hOriginalRun :
      TypedCfg.ObserverSemantics.Program.runN
          program (prefixFuel + tailFuel)
          entry initial initialTrace =
        .ok (tailOutcome, tailTrace) := by
    rw [TypedCfg.ObserverSemantics.Program.runN_add_of_jump
      hPrefix.run]
    exact hTailRun
  exact
    hFull.minimal (prefixFuel + tailFuel) (by omega)
      tailOutcome tailTrace hOriginalRun hTailAccepted

theorem outcome_eq_of_prefix_accepted
    {program : TypedCfg.Program}
    {accept prefixAccept : TypedCfg.Outcome → Prop}
    {fullFuel prefixFuel : Nat} {entry : Assembly.Label}
    {initial : EVMState}
    {initialTrace prefixTrace finalTrace : Trace}
    {prefixOutcome finalOutcome : TypedCfg.Outcome}
    (hFull :
      FirstReaches program accept fullFuel
        entry initial initialTrace finalOutcome finalTrace)
    (hPrefix :
      FirstReaches program prefixAccept prefixFuel
        entry initial initialTrace prefixOutcome prefixTrace)
    (hLe : prefixFuel ≤ fullFuel)
    (hAccepted : accept prefixOutcome) :
    prefixFuel = fullFuel ∧
      finalOutcome = prefixOutcome ∧ finalTrace = prefixTrace := by
  have hFuel : prefixFuel = fullFuel := by
    by_contra hNe
    exact
      hFull.minimal prefixFuel (by omega)
        prefixOutcome prefixTrace hPrefix.run hAccepted
  subst fullFuel
  have hRuns :
      (.ok (finalOutcome, finalTrace) :
          Except TypedCfg.EVMException
            (TypedCfg.Outcome × Trace)) =
        .ok (prefixOutcome, prefixTrace) :=
    hFull.run.symm.trans hPrefix.run
  have hEq :
      finalOutcome = prefixOutcome ∧
        finalTrace = prefixTrace := by
    simpa only [Prod.mk.injEq] using Except.ok.inj hRuns
  exact ⟨rfl, hEq.1, hEq.2⟩

end FirstReaches

end OutcomeSimulation
end ObserverAdequacy
end Structured
end EvmCompiler
