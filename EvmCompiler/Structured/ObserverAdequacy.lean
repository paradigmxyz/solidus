import EvmCompiler.Structured.ObserverActivationBoundary

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy

/-!
Backward adequacy for the adjacent Structured-to-TypedCfg pass.

This module consumes only the existing Structured compiler, its TypedCfg
typing facts, the shared observer semantics, and the pass-owned state relation.
It does not reason about Assembly or bytecode execution.
-/

namespace OutcomeSimulation

abbrev Continuations :=
  TypedCfgPreservation.OutcomeSimulation.Continuations

/--
A target outcome has reached one of the Structured fragment's semantic
continuations or has halted. Fallthrough, return dispatch, and invalid target
outcomes are internal to lower control machinery and are not Structured
statement outcomes.
-/
def TargetBoundary (continuations : Continuations) :
    TypedCfg.Outcome → Prop
  | .jump label _ =>
      label = continuations.regular ∨
        continuations.breakLabel? = some label ∨
        continuations.continueLabel? = some label ∨
        continuations.leaveLabel? = some label
  | .halt _ _ => True
  | .fallthrough _ | .returnDispatch _ | .invalid _ => False

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

theorem targetBoundary_of_rel
    {transcript : Trace}
    {continuations : Continuations}
    {tokens : List Word}
    {sourceOutcome :
      ObserverSemantics.Outcome (transcript := transcript)}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        continuations tokens sourceOutcome targetOutcome trace) :
    TargetBoundary continuations targetOutcome := by
  rcases sourceOutcome with ⟨source, mode⟩
  cases mode with
  | regular =>
      obtain ⟨target, rfl, _hState⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.regular_elim hRel
      exact Or.inl rfl
  | brk =>
      obtain ⟨label, target, hLabel, rfl, _hState⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.brk_elim hRel
      exact Or.inr (Or.inl hLabel)
  | cont =>
      obtain ⟨label, target, hLabel, rfl, _hState⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.cont_elim hRel
      exact Or.inr (Or.inr (Or.inl hLabel))
  | leave =>
      obtain ⟨label, target, hLabel, rfl, _hState⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.leave_elim hRel
      exact Or.inr (Or.inr (Or.inr hLabel))
  | halt kind =>
      obtain ⟨target, targetFinal, rfl, _hStep, _hState⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.halt_elim hRel
      trivial

theorem rel_ofContext_change_regular_of_nonregular
    {transcript : Trace}
    {ctx : TypedCfgCompiler.Context}
    {leftRegular rightRegular : Assembly.Label}
    {tokens : List Word}
    {sourceOutcome :
      ObserverSemantics.Outcome (transcript := transcript)}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hNonregular : sourceOutcome.mode ≠ .regular)
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx leftRegular)
        tokens sourceOutcome targetOutcome trace) :
    ObserverPreservation.OutcomeSimulation.Rel
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx rightRegular)
      tokens sourceOutcome targetOutcome trace := by
  rcases sourceOutcome with ⟨source, mode⟩
  cases mode <;> cases targetOutcome <;>
    simp [ObserverPreservation.OutcomeSimulation.Rel,
      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
      at hNonregular hRel ⊢
  all_goals exact hRel

def AdequateWithin {transcript : Trace}
    (eval :
      Nat →
        ObserverSemantics.Outcome (transcript := transcript) → Prop)
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (program : TypedCfg.Program) (continuations : Continuations)
    (accept : TypedCfg.Outcome → Prop)
    (entry : Assembly.Label) (input : TypedCfg.Shape)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) : Prop :=
  (∀ sourceFuel sourceOutcome targetOutcome trace,
      eval sourceFuel sourceOutcome →
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome trace →
        OutcomeArtifact result ctx sourceOutcome →
          accept targetOutcome) →
    ∀ {targetFuel : Nat} {target : EVMState}
      {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome},
      ObserverPreservation.StateRel.At
          input source tokens target trace →
        FirstReaches program accept (targetFuel + 1)
            entry target trace targetOutcome traceFinal →
          ∃ sourceFuel sourceOutcome,
            eval sourceFuel sourceOutcome ∧
              ObserverPreservation.OutcomeSimulation.Rel
                continuations tokens sourceOutcome
                targetOutcome traceFinal ∧
              OutcomeArtifact result ctx sourceOutcome

/--
Fixed-target-fuel form of `AdequateWithin`.

Recursive procedure adequacy uses this interface to expose the strict decrease
in target execution fuel without adding a public all-callees obligation.
-/
def AdequateWithinFuel {transcript : Trace}
    (eval :
      Nat →
        ObserverSemantics.Outcome (transcript := transcript) → Prop)
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (program : TypedCfg.Program) (continuations : Continuations)
    (accept : TypedCfg.Outcome → Prop)
    (entry : Assembly.Label) (input : TypedCfg.Shape)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (targetFuel : Nat) : Prop :=
  (∀ sourceFuel sourceOutcome targetOutcome trace,
      eval sourceFuel sourceOutcome →
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome trace →
        OutcomeArtifact result ctx sourceOutcome →
          accept targetOutcome) →
    ∀ {target : EVMState}
      {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome},
      ObserverPreservation.StateRel.At
          input source tokens target trace →
        FirstReaches program accept (targetFuel + 1)
            entry target trace targetOutcome traceFinal →
          ∃ sourceFuel sourceOutcome,
            eval sourceFuel sourceOutcome ∧
              ObserverPreservation.OutcomeSimulation.Rel
                continuations tokens sourceOutcome
                targetOutcome traceFinal ∧
              OutcomeArtifact result ctx sourceOutcome

/--
Stable backward-adequacy interface for a source evaluation relation at a typed
Structured-to-TypedCfg boundary.
-/
def AdequateAt {transcript : Trace}
    (eval :
      Nat →
        ObserverSemantics.Outcome (transcript := transcript) → Prop)
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (program : TypedCfg.Program) (continuations : Continuations)
    (entry : Assembly.Label) (input : TypedCfg.Shape)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) : Prop :=
  ∀ {targetFuel : Nat} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome},
    ObserverPreservation.StateRel.At
        input source tokens target trace →
      ReachesBoundary
          program continuations (targetFuel + 1)
          entry target trace targetOutcome traceFinal →
        ∃ sourceFuel sourceOutcome,
          eval sourceFuel sourceOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens sourceOutcome
              targetOutcome traceFinal ∧
            OutcomeArtifact result ctx sourceOutcome

namespace AdequateWithin

theorem fuel
    {transcript : Trace}
    {eval :
      Nat →
        ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {program : TypedCfg.Program} {continuations : Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hAdequate :
      AdequateWithin eval result ctx program continuations accept
        entry input source tokens)
    (targetFuel : Nat) :
    AdequateWithinFuel eval result ctx program continuations accept
      entry input source tokens targetFuel := by
  intro hAccept
  exact hAdequate hAccept

theorem toAdequateAt
    {transcript : Trace}
    {eval :
      Nat →
        ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {program : TypedCfg.Program} {continuations : Continuations}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hAdequate :
      AdequateWithin eval result ctx program continuations
        (TargetBoundary continuations)
        entry input source tokens) :
    AdequateAt eval result ctx program continuations
      entry input source tokens :=
  hAdequate (fun _ _ _ _ _ hRel _ =>
    targetBoundary_of_rel hRel)

end AdequateWithin

end OutcomeSimulation

namespace BasicInstr

theorem output_length_pos_of_observer
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {kind : Assembly.ResourceObserver}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hObserver :
      (match instr with
       | .op op => ObserverSemantics.basicOpObserver? op
       | _ => none) = some kind) :
    1 ≤ output.length := by
  cases instr with
  | push value | bindLocals value names
  | bindScratch value name slot =>
      simp at hObserver
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            _hInputBound, hOutputLength⟩ :=
        TypedCfgPreservation.BasicOp.type_length_toCfg hType
      have hCases : op = .gas ∨ op = .msize := by
        cases op <;>
          simp [ObserverSemantics.basicOpObserver?,
            Assembly.ResourceObserver.ofPrimOp?,
            Structured.BasicOp.toPrimOp] at hObserver ⊢
      rcases hCases with rfl | rfl <;>
        simp [Structured.BasicOp.toPrimOp,
          Assembly.PrimOp.stackArity?,
          Assembly.PrimOp.toEVM,
          EvmYul.EVM.δ, EvmYul.EVM.α] at hArity <;>
        omega

end BasicInstr

namespace Code

/--
Backward frame adequacy indexed by the checked input shape.

Unlike the former unindexed source predicate, this interface quantifies only
over states whose visible stack satisfies the actual compiler typing judgment.
The conclusion uses the pass's existing replay relation, which intentionally
forgets compiler-owned control counters.
-/
def FrameReflectingAt (code : Structured.Code)
    (input : TypedCfg.Shape) : Prop :=
  ∀ {transcript : Trace} {output : TypedCfg.Shape}
      {state framedFinal : ObserverSemantics.State transcript}
      {hidden : EvmYul.Stack Word},
    TypedCfgCompiler.Code.type? code input = some output →
      TypedCfgCompiler.Shape.sourceLength input ≤
        state.source.evm.stack.length →
      ObserverSemantics.Code.run code
          (ObserverSemantics.Code.withHidden state hidden) =
        .ok framedFinal →
      ∃ final,
        ObserverSemantics.Code.run code state = .ok final ∧
          ObserverPreservation.ReplayStateRel
            framedFinal
            (ObserverSemantics.Code.withHidden final hidden)

/--
Every straight-line fragment accepted by the existing pass typer reflects
execution through compiler-owned frame suffixes at its checked input shape.
-/
theorem frameReflectingAt
    (code : Structured.Code) (input : TypedCfg.Shape) :
    FrameReflectingAt code input := by
  intro transcript output state framedFinal hidden
    hType hBound hFramed
  induction code generalizing input output state framedFinal with
  | nil =>
      simp [TypedCfgCompiler.Code.type?,
        TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?,
        ObserverSemantics.Code.run,
        EffectSemantics.Code.run] at hType hFramed
      cases hType
      cases hFramed
      exact
        ⟨state, rfl,
          ObserverPreservation.ReplayStateRel.refl
            (ObserverSemantics.Code.withHidden state hidden)⟩
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
        cases hSafe :
            TypedCfgCompiler.BasicInstr.sourceSafe? instr input middle with
        | false =>
          simp [hHeadType, hSafe] at hType
        | true =>
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [hHeadType, hSafe] using hType
          unfold ObserverSemantics.Code.run
            EffectSemantics.Code.run at hFramed
          simp only [ObserverSemantics.stateModel_evm,
            ObserverSemantics.stateModel_withEVM] at hFramed
          simp only [ObserverSemantics.Code.withHidden_source,
            RunState.withEVM_evm] at hFramed
          cases hFramedStep :
              instr.step
                { state.source.evm with
                  stack := state.source.evm.stack ++ hidden } with
          | error err =>
              simp [hFramedStep, Bind.bind, Except.bind] at hFramed
          | ok framedEVM =>
              simp only [hFramedStep,
                Bind.bind, Except.bind] at hFramed
              obtain ⟨sourceEVM, hSourceStep⟩ :=
                TypedCfgPreservation.BasicInstr.exists_step_of_type_bound_append
                  (TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe)
                  hBound hFramedStep
              have hStepRel :
                  Assembly.SameRuntimeData
                    framedEVM
                    { sourceEVM with
                      stack := sourceEVM.stack ++ hidden } :=
                TypedCfgPreservation.BasicInstr.step_append_stack_rel_of_type
                  (TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe hSafe)
                  hBound hSourceStep hFramedStep
              let sourceMiddle : ObserverSemantics.State transcript :=
                state.withSource
                  (state.source.withEVM sourceEVM)
              let framedMiddle : ObserverSemantics.State transcript :=
                (ObserverSemantics.Code.withHidden state hidden).withSource
                  ((ObserverSemantics.Code.withHidden state hidden).source.withEVM
                    framedEVM)
              let expectedMiddle : ObserverSemantics.State transcript :=
                ObserverSemantics.Code.withHidden sourceMiddle hidden
              have hNormalizeFramedMiddle :
                  (ObserverSemantics.Code.withHidden state hidden).withSource
                      ((state.source.withEVM
                        { state.source.evm with
                          stack := state.source.evm.stack ++ hidden }).withEVM
                        framedEVM) =
                    framedMiddle := by
                simp [framedMiddle,
                  ObserverSemantics.Code.withHidden,
                  RunState.withEVM]
              rw [hNormalizeFramedMiddle] at hFramed
              have hMiddleRel :
                  ObserverPreservation.ReplayStateRel
                    framedMiddle expectedMiddle := by
                refine ⟨rfl, ?_, ?_⟩
                · simp [framedMiddle, expectedMiddle, sourceMiddle,
                    ObserverSemantics.Code.withHidden, RunState.withEVM]
                · simpa [framedMiddle, expectedMiddle, sourceMiddle,
                    ObserverSemantics.Code.withHidden, RunState.withEVM]
                    using hStepRel
              cases hFramedAfter :
                  (ObserverSemantics.handler transcript).afterInstr
                    instr framedMiddle with
              | error err =>
                  rw [hFramedAfter] at hFramed
                  contradiction
              | ok framedAfter =>
                  rw [hFramedAfter] at hFramed
                  obtain
                      ⟨expectedAfter, hExpectedAfter, hAfterRel⟩ :=
                    ObserverPreservation.handler_of_rel
                      hMiddleRel hFramedAfter
                  have hSourceStepBound :
                      TypedCfgCompiler.Shape.sourceLength middle ≤
                        sourceEVM.stack.length :=
                    TypedCfgPreservation.BasicInstr.step_sourceLength_bound_of_type
                      hSafe hBound hSourceStep
                  have hObserverTop :
                      ∀ op kind,
                        instr = .op op →
                        ObserverSemantics.basicOpObserver? op = some kind →
                        sourceMiddle.source.evm.stack ≠ [] := by
                    intro op kind hInstr hObserver
                    subst instr
                    have hOutputPos :
                        1 ≤ TypedCfgCompiler.Shape.sourceLength middle :=
                      BasicInstr.output_length_pos_of_observer
                        (TypedCfgCompiler.BasicInstr.sourceType_of_sourceSafe
                          hSafe)
                        hObserver
                    have hStackPos :
                        1 ≤ sourceEVM.stack.length :=
                      Nat.le_trans hOutputPos hSourceStepBound
                    intro hNil
                    have hSourceNil : sourceEVM.stack = [] := by
                      simpa [sourceMiddle] using hNil
                    simp [hSourceNil] at hStackPos
                  obtain
                      ⟨sourceAfter, hSourceAfter, hExpectedEq⟩ :=
                    ObserverSemantics.Code.handler_frameReflecting
                      hObserverTop
                      (by simpa [expectedMiddle] using hExpectedAfter)
                  subst expectedAfter
                  have hAfterBound :
                      TypedCfgCompiler.Shape.sourceLength middle ≤
                        sourceAfter.source.evm.stack.length := by
                    have hLength :=
                      ObserverSemantics.handler_stack_length hSourceAfter
                    have hSourceLength :
                        sourceMiddle.source.evm.stack.length =
                          sourceEVM.stack.length := by
                      simp [sourceMiddle]
                    omega
                  obtain
                      ⟨expectedFinal, hExpectedTail, hTailRel⟩ :=
                    ObserverPreservation.Code.run_of_rel
                      hAfterRel hFramed
                  obtain
                      ⟨final, hSourceTail, hExpectedFinalRel⟩ :=
                    ih middle hTailType hAfterBound hExpectedTail
                  refine ⟨final, ?_, ?_⟩
                  · unfold ObserverSemantics.Code.run
                      EffectSemantics.Code.run
                    simp only [ObserverSemantics.stateModel_evm,
                      ObserverSemantics.stateModel_withEVM]
                    rw [hSourceStep]
                    simp only [Bind.bind, Except.bind]
                    change
                      (ObserverSemantics.handler transcript).afterInstr
                          instr sourceMiddle =
                        .ok sourceAfter at hSourceAfter
                    rw [hSourceAfter]
                    exact hSourceTail
                  · exact
                      ObserverPreservation.ReplayStateRel.trans
                        hTailRel hExpectedFinalRel

/--
Backward straight-line adequacy across realized procedure frames.

The target run is transported to the source state with its concrete hidden
suffix, then the checked input shape derives reflection through only that
compiler-owned suffix. Return-frame representation remains inside the adjacent
pass proof.
-/
theorem run_of_runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hRun :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetFinal, output), traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.run code source = .ok final ∧
        ObserverPreservation.StateRel
          final tokens targetFinal traceFinal := by
  rcases hRel.rel.1 with ⟨realized, hRealize, hSame⟩
  have hAppend :=
    TypedCfgPreservation.realizeStack_append_prefix
      source.source.evm.stack [] source.source.returns tokens
  cases hHidden :
      TypedCfgPreservation.realizeStack
        [] source.source.returns tokens with
  | none =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
  | some hidden =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
      let targetState : ObserverSemantics.State transcript :=
        source.withSource (source.source.withEVM target)
      let framedSource :=
        ObserverSemantics.Code.withHidden source hidden
      have hReplay :
          ObserverPreservation.ReplayStateRel targetState framedSource := by
        exact
          ⟨rfl, by simp [targetState, framedSource],
            by simpa [targetState, framedSource,
                ObserverSemantics.Code.withHidden,
                RunState.withEVM] using hSame⟩
      have hTargetBody :
          TypedCfg.ObserverSemantics.Block.runBody
              (TypedCfgCompiler.Code.toCfg code) input
              targetState.source.evm targetState.remaining =
            .ok ((targetFinal, output), traceFinal) := by
        simpa [targetState, hRel.rel.2] using hRun
      obtain
          ⟨targetFinalState, hTargetCode, hTargetEVM, hTargetTrace⟩ :=
        ObserverPreservation.Code.run_of_runBody_toCfg
          hType hTargetBody
      obtain ⟨framedFinal, hFramedRun, hFinalReplay⟩ :=
        ObserverPreservation.Code.run_of_rel hReplay hTargetCode
      obtain ⟨final, hSourceRun, hFrameReplay⟩ :=
        frameReflectingAt code input hType hRel.sourceStack
          (by simpa [framedSource] using hFramedRun)
      have hFinalReplay' :
          ObserverPreservation.ReplayStateRel
            targetFinalState
            (ObserverSemantics.Code.withHidden final hidden) :=
        ObserverPreservation.ReplayStateRel.trans
          hFinalReplay hFrameReplay
      have hFinalReturns :
          final.source.returns = source.source.returns :=
        ObserverSemantics.Code.run_returns_eq hSourceRun
      refine ⟨final, hSourceRun, ?_⟩
      refine ⟨?_, ?_⟩
      · refine ⟨final.source.evm.stack ++ hidden, ?_, ?_⟩
        · have hFinalAppend :=
            TypedCfgPreservation.realizeStack_append_prefix
              final.source.evm.stack [] final.source.returns tokens
          simpa [hFinalReturns, hHidden] using hFinalAppend
        · rw [← hTargetEVM]
          simpa [ObserverSemantics.Code.withHidden,
              RunState.withEVM] using hFinalReplay'.source.2
      · rw [← hTargetTrace]
        exact
          (ObserverPreservation.ReplayStateRel.remaining_eq
            hFinalReplay').symm

/--
Backward adequacy for a compiled condition across active procedure frames.

The shape-soundness fact prevents the condition pop from consuming a hidden
return token or caller-stack value.
-/
theorem runCondition_of_runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {target targetAfter targetFinal : EVMState}
    {trace traceFinal : Trace} {cond : Bool}
    {condition : TypedCfg.Slot}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 output = some ())
    (hHead : output.slots.head? = some condition)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetAfter, output), traceFinal))
    (hPop :
      Structured.Code.popCondition targetAfter =
        .ok (targetFinal, cond)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.runCondition code source =
          .ok (final, cond) ∧
        ObserverPreservation.StateRel.At
          { output with slots := output.slots.tail }
          final tokens targetFinal traceFinal := by
  obtain ⟨after, hSourceCode, hAfterRel⟩ :=
    run_of_runBody_toCfg
      hType hRel hBody
  have hOutputBound :
      TypedCfgCompiler.Shape.sourceLength output ≤
        after.source.evm.stack.length :=
    shapeSound code hType hRel.sourceStack hSourceCode
  have hOutputPos :
      1 ≤ TypedCfgCompiler.Shape.sourceLength output :=
    TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
      hSource
  have hAfterPos : 1 ≤ after.source.evm.stack.length :=
    Nat.le_trans hOutputPos hOutputBound
  cases hAfterStack : after.source.evm.stack with
  | nil =>
      simp [hAfterStack] at hAfterPos
  | cons value stack =>
      let final : ObserverSemantics.State transcript :=
        after.withSource
          (after.source.withEVM
            { after.source.evm with stack := stack })
      have hSourcePop :
          EffectSemantics.Code.popCondition
              (ObserverSemantics.stateModel transcript) after =
            .ok
              (final,
                value != EvmYul.UInt256.ofNat 0) := by
        unfold EffectSemantics.Code.popCondition
        simp only [ObserverSemantics.stateModel_evm,
          ObserverSemantics.stateModel_withEVM]
        rw [hAfterStack]
        rfl
      obtain ⟨producedTarget, hProducedPop, hFinalRel⟩ :=
        ObserverPreservation.StateRel.popCondition
          hSourcePop hAfterRel
      rw [hPop] at hProducedPop
      cases hProducedPop
      have hAfterFits :
          TypedCfgCompiler.Shape.SourceFrameFits output
            after.source.evm.stack.length :=
        sourceFrameFits code hType hRel.sourceFrameFits hSourceCode
      have hTailFits :
          TypedCfgCompiler.Shape.SourceFrameFits
              { output with slots := output.slots.tail }
            stack.length := by
        apply TypedCfgCompilerFacts.Shape.sourceFrameFits_tail hOutputPos
        simpa [hAfterStack] using hAfterFits
      refine
        ⟨final, ?_,
          ObserverPreservation.StateRel.At.ofFits hFinalRel
            (by simpa [final, hAfterStack] using hTailFits)⟩
      · unfold ObserverSemantics.Code.runCondition
          EffectSemantics.Code.runCondition
        have hEffectRun :
            EffectSemantics.Code.run
                (ObserverSemantics.stateModel transcript)
                (ObserverSemantics.handler transcript)
                code source =
              .ok after :=
          hSourceCode
        rw [hEffectRun]
        exact hSourcePop

/--
Backward straight-line adequacy at a source boundary with no active ghost
return frames. This is the top-level case used by the first closed-program
theorem; recursive procedure frames require the stronger shape-indexed
induction still under construction.
-/
theorem run_of_runBody_toCfg_noFrames
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel
        source [] target trace)
    (hRun :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetFinal, output), traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.run code source = .ok final ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  rcases hRel.1 with ⟨realized, hRealize, hSame⟩
  simp [hReturns, TypedCfgPreservation.realizeStack] at hRealize
  subst realized
  let targetState : ObserverSemantics.State transcript :=
    source.withSource (source.source.withEVM target)
  have hReplay :
      ObserverPreservation.ReplayStateRel targetState source := by
    exact
      ⟨rfl, by simp [targetState], by simpa [targetState] using hSame⟩
  have hTargetBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input
          targetState.source.evm targetState.remaining =
        .ok ((targetFinal, output), traceFinal) := by
    simpa [targetState, hRel.2] using hRun
  obtain
      ⟨targetFinalState, hTargetCode, hTargetEVM, hTargetTrace⟩ :=
    ObserverPreservation.Code.run_of_runBody_toCfg
      hType hTargetBody
  obtain ⟨final, hSourceCode, hFinalReplay⟩ :=
    ObserverPreservation.Code.run_of_rel hReplay hTargetCode
  have hFinalReturns : final.source.returns = [] := by
    rw [ObserverSemantics.Code.run_returns_eq hSourceCode, hReturns]
  refine ⟨final, hSourceCode, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨final.source.evm.stack, ?_, ?_⟩
    · simp [hFinalReturns, TypedCfgPreservation.realizeStack]
    · rw [← hTargetEVM]
      simpa using hFinalReplay.source.2
  · rw [← hTargetTrace]
    exact
      (ObserverPreservation.ReplayStateRel.remaining_eq
        hFinalReplay).symm

/--
Backward adequacy for a compiled condition at a no-frame boundary.
-/
theorem runCondition_of_runBody_toCfg_noFrames
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {target targetAfter targetFinal : EVMState}
    {trace traceFinal : Trace} {cond : Bool}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel
        source [] target trace)
    (hBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetAfter, output), traceFinal))
    (hPop :
      Structured.Code.popCondition targetAfter =
        .ok (targetFinal, cond)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.runCondition code source =
          .ok (final, cond) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  obtain ⟨after, hSourceCode, hAfterRel⟩ :=
    run_of_runBody_toCfg_noFrames
      hType hReturns hRel hBody
  have hAfterReturns : after.source.returns = [] := by
    rw [ObserverSemantics.Code.run_returns_eq hSourceCode, hReturns]
  rcases hAfterRel.1 with ⟨realized, hRealize, hSame⟩
  simp [hAfterReturns, TypedCfgPreservation.realizeStack] at hRealize
  subst realized
  have hStack :
      targetAfter.stack = after.source.evm.stack :=
    Assembly.SameRuntimeData.stack_eq hSame
  unfold Structured.Code.popCondition
    EffectSemantics.Code.popCondition at hPop
  cases hTargetStack : targetAfter.stack with
  | nil =>
      simp [hTargetStack, EvmYul.Stack.pop] at hPop
  | cons value stack =>
      simp [hTargetStack, EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      have hSourceStack :
          after.source.evm.stack = value :: stack := by
        rw [← hStack, hTargetStack]
      let final : ObserverSemantics.State transcript :=
        after.withSource
          (after.source.withEVM
            { after.source.evm with stack := stack })
      refine ⟨final, ?_, ?_⟩
      · unfold ObserverSemantics.Code.runCondition
          EffectSemantics.Code.runCondition
        have hEffectRun :
            EffectSemantics.Code.run
                (ObserverSemantics.stateModel transcript)
                (ObserverSemantics.handler transcript)
                code source =
              .ok after :=
          hSourceCode
        rw [hEffectRun]
        simp only [Bind.bind, Except.bind]
        unfold EffectSemantics.Code.popCondition
        simp only [ObserverSemantics.stateModel_evm,
          ObserverSemantics.stateModel_withEVM]
        rw [hSourceStack]
        rfl
      · refine ⟨?_, ?_⟩
        · refine ⟨stack, ?_, ?_⟩
          · simp [final, hAfterReturns,
              TypedCfgPreservation.realizeStack]
          · simpa [final] using
              Assembly.SameRuntimeData.replaceStack hSame
                (targetStack := stack)
                (sourceStack := stack) rfl
        · simpa [final] using hAfterRel.2

end Code

namespace Block

/--
Backward adequacy for the empty Structured block up to its first semantic
continuation. The generated jump block and its one-step execution are
constructed from the existing compiler result.
-/
theorem outcome_nil_of_compileBlockFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Block.Eval
            program sourceFuel { stmts := [] } source sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches
        cfg accept (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval
          program sourceFuel { stmts := [] } source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  have hFallthrough :
      result.fallthrough? = some input :=
    TypedCfgCompilerFacts.Block.fallthrough_nil_of_compileBlockFuel?
      hCompile
  unfold TypedCfgCompiler.compileBlockFuel? at hCompile
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump regular }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular target, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    change
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.jump regular target, trace)
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hFirstBoundary :
      OutcomeSimulation.TargetBoundary continuations
        (.jump regular target) :=
    Or.inl hRegular.symm
  have hEval :
      ObserverSemantics.Block.Eval
        program 1 { stmts := [] } source
          (Structured.OutcomeT.regular source) :=
    Structured.EffectSemantics.Block.Eval.nil
  have hOutcomeRel :
      ObserverPreservation.OutcomeSimulation.Rel
        continuations tokens (Structured.OutcomeT.regular source)
          (.jump regular target) trace :=
    ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
      ⟨hRegular.symm, hRel.rel⟩
  have hArtifact :
      OutcomeSimulation.OutcomeArtifact
        { blocks := [generated]
          next := supply
          calls := []
          fallthrough? := some input }
        ctx
        (Structured.OutcomeT.regular source) :=
    ⟨input, rfl, hRel.sourceFrameFits⟩
  obtain ⟨hTargetOutcome, hTraceFinal⟩ :=
    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
      hReach hStep
        (hAccept 1 _ _ _ hEval hOutcomeRel hArtifact)
  subst targetOutcome
  subst traceFinal
  exact
    ⟨1, Structured.OutcomeT.regular source,
      Structured.EffectSemantics.Block.Eval.nil,
      ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
        ⟨hRegular.symm, hRel.rel⟩⟩

theorem outcome_nil_of_compileBlockFuel?_and_reachesBoundary
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.ReachesBoundary
        cfg continuations (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval
          program sourceFuel { stmts := [] } source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal :=
  outcome_nil_of_compileBlockFuel?_and_firstReaches
    hCompile hBlocks hRegular
      (fun _ _ _ _ _ hRel _ =>
        OutcomeSimulation.targetBoundary_of_rel hRel)
      hRel hReach

theorem adequateWithin_nil_of_compileBlockFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := [] } source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  obtain ⟨sourceFuel, sourceOutcome, hEval, hOutcomeRel⟩ :=
    outcome_nil_of_compileBlockFuel?_and_firstReaches
      (program := program)
      hCompile hBlocks hRegular hAccept hRel hReach
  have hFallthrough :
      result.fallthrough? = some input :=
    TypedCfgCompilerFacts.Block.fallthrough_nil_of_compileBlockFuel?
      hCompile
  cases hEval
  exact
    ⟨1, Structured.OutcomeT.regular source,
      Structured.EffectSemantics.Block.Eval.nil, hOutcomeRel,
      ⟨input, hFallthrough, hRel.sourceFrameFits⟩⟩

theorem adequate_nil_of_compileBlockFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.AdequateAt
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := [] } source sourceOutcome)
      result ctx cfg continuations entry input source tokens := by
  exact
    OutcomeSimulation.AdequateWithin.toAdequateAt
      (adequateWithin_nil_of_compileBlockFuel?
        (accept :=
          OutcomeSimulation.TargetBoundary continuations)
        hCompile hBlocks hRegular)

end Block

namespace Switch

abbrev casesEntryLabel :=
  TypedCfgCompilerFacts.Switch.casesEntryLabel

/--
One generated switch-head step reconstructs the source scrutinee execution and
the source value consumed by the generated case chain.
-/
private theorem head_of_compileStmtFuel?_and_step
    {transcript : Trace} {compilerFuel : Nat}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {firstOutcome : TypedCfg.Outcome}
    {trace traceAfter : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (firstOutcome, traceAfter)) :
    ∃ valueShape valueSlot caseResult defaultResult
        afterScrutinee stack value targetAfter,
      firstOutcome =
        .jump (casesEntryLabel supply 0 cases) targetAfter ∧
      TypedCfgCompiler.Code.type? scrutinee input = some valueShape ∧
      TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape =
        some () ∧
      valueShape.slots.head? = some valueSlot ∧
      TypedCfgCompiler.compileCasesFuel? compilerFuel
          cases ctx supply (supply + 1) 0 valueShape
          { valueShape with slots := valueShape.slots.tail }
          regular =
        some caseResult ∧
      TypedCfgCompiler.compileDefaultFuel? compilerFuel
          defaultBody ctx caseResult.next
          (LabelSupply.label supply 1) valueShape
          { valueShape with slots := valueShape.slots.tail }
          regular =
        some defaultResult ∧
      result =
        { blocks :=
            { label := entry
              input := input
              body := TypedCfgCompiler.Code.toCfg scrutinee
              output := valueShape
              term := .jump (casesEntryLabel supply 0 cases) } ::
              caseResult.blocks ++ defaultResult.blocks
          next := defaultResult.next
          calls := caseResult.calls ++ defaultResult.calls
          fallthrough? :=
            some { valueShape with slots := valueShape.slots.tail } } ∧
      ObserverSemantics.Code.run scrutinee source =
        .ok afterScrutinee ∧
      afterScrutinee.source.evm.stack.pop = some (stack, value) ∧
      ObserverPreservation.StateRel.At
        valueShape afterScrutinee tokens targetAfter traceAfter := by
  obtain
      ⟨valueShape, valueSlot, caseResult, defaultResult,
        hType, hSource, hValue, hCases, hDefault, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
      hCompile
  subst result
  let head : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg scrutinee
      output := valueShape
      term := .jump (casesEntryLabel supply 0 cases) }
  have hFind : cfg.findBlock? entry = some head := by
    apply hBlocks head
    simp [head]
  unfold TypedCfg.ObserverSemantics.Program.step at hStep
  rw [hFind] at hStep
  change
    TypedCfg.ObserverSemantics.Block.run head target trace =
      .ok (firstOutcome, traceAfter) at hStep
  unfold TypedCfg.ObserverSemantics.Block.run at hStep
  dsimp [head] at hStep
  cases hBody :
      TypedCfg.ObserverSemantics.Block.runBody
        (TypedCfgCompiler.Code.toCfg scrutinee)
        input target trace with
  | error err =>
      rw [hBody] at hStep
      simp [Bind.bind, Except.bind] at hStep
  | ok bodyResult =>
      rcases bodyResult with ⟨⟨bodyFinal, bodyOutput⟩, bodyTrace⟩
      rw [hBody] at hStep
      simp only [Bind.bind, Except.bind] at hStep
      by_cases hOutput : bodyOutput = valueShape
      · subst bodyOutput
        simp [TypedCfg.Block.runTerm] at hStep
        rcases hStep with ⟨rfl, rfl⟩
        obtain ⟨afterScrutinee, hScrutinee, hAfterRel⟩ :=
          Code.run_of_runBody_toCfg
            hType hRel hBody
        have hAfterAt :
            ObserverPreservation.StateRel.At
              valueShape afterScrutinee tokens bodyFinal bodyTrace := by
          exact ObserverPreservation.StateRel.At.ofFits hAfterRel
            (Code.sourceFrameFits scrutinee
              hType hRel.sourceFrameFits hScrutinee)
        have hShapeOne :
            1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
          TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
            hSource
        have hSourceOne :
            1 ≤ afterScrutinee.source.evm.stack.length :=
          Nat.le_trans hShapeOne hAfterAt.sourceStack
        cases hStack : afterScrutinee.source.evm.stack with
        | nil =>
            simp [hStack] at hSourceOne
        | cons value stack =>
            have hPop :
                afterScrutinee.source.evm.stack.pop =
                  some (stack, value) := by
              simp [hStack, EvmYul.Stack.pop]
            exact
              ⟨valueShape, valueSlot, caseResult, defaultResult,
                afterScrutinee, stack, value, bodyFinal, rfl,
                hType, hSource, hValue, hCases, hDefault,
                rfl, hScrutinee, hPop, hAfterAt⟩
      · simp [hOutput] at hStep

/--
Backward composition for a matched switch head. Generated test and pop blocks
are discharged locally; the recursive body theorem remains private proof
machinery.
-/
private theorem outcome_cases_head_of_compileCasesFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {caseValue : Word} {body : Structured.Block}
    {rest : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx
          valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hEq : caseValue = value)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Block.Eval program sourceFuel body
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack }))
            sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hCaseEntryNotAccepted :
      ∀ targetState,
        ¬ accept (.jump (LabelSupply.label base (idx + 2)) targetState))
    (hBodyEntryNotAccepted :
      ∀ targetState,
        ¬ accept (.jump (.generated base (2000 + idx)) targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        valueShape source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        (TypedCfgCompiler.switchTestLabel base idx)
        target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            supply (.generated base (2000 + idx))
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel body
              (source.withSource
                (source.source.withEVM
                  { source.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept
          (.generated base (2000 + idx)) bodyShape
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          tokens) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval program sourceFuel body
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome := by
  obtain
      ⟨bodyResult, tail, hBodyCompile, hRequire, _hTailCompile, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
      hHead hPopType hCompile
  subst result
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  obtain ⟨targetAfterTest, hTestStep, hAfterTestRel⟩ :=
    ObserverPreservation.Switch.step_test
      (testLabel := TypedCfgCompiler.switchTestLabel base idx)
      (caseLabel := LabelSupply.label base (idx + 2))
      (nextTest :=
        TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
      (caseValue := caseValue) (value := value)
      hBlocks (by left) hHead hRel.rel hPop
  have hSelectedStep :
      TypedCfg.ObserverSemantics.Program.step cfg
          (TypedCfgCompiler.switchTestLabel base idx)
          target trace =
        .ok
          (.jump (LabelSupply.label base (idx + 2))
            targetAfterTest,
            trace) := by
    simpa [hEq] using hTestStep
  have hAfterTestReach :=
    OutcomeSimulation.FirstReaches.tail_of_step_jump
      hReach hSelectedStep
  have hCasePositive : 0 < targetFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hAfterTestReach (hCaseEntryNotAccepted targetAfterTest)
  cases targetFuel with
  | zero =>
      omega
  | succ popFuel =>
      obtain ⟨targetAfterPop, hPopStep, hAfterPopRel⟩ :=
        ObserverPreservation.BlocksInProgram.step_pop_jump
          (entry := LabelSupply.label base (idx + 2))
          (regular := .generated base (2000 + idx))
          (input := valueShape) (output := bodyShape)
          hBlocks (by simp) hPopType hAfterTestRel hPop
      have hAfterPopReach :=
        OutcomeSimulation.FirstReaches.tail_of_step_jump
          hAfterTestReach hPopStep
      have hPopLength :
          source.source.evm.stack.length = stack.length + 1 := by
        cases hStack : source.source.evm.stack with
        | nil =>
            simp [hStack, EvmYul.Stack.pop] at hPop
        | cons head tail =>
            simp [hStack, EvmYul.Stack.pop] at hPop
            rcases hPop with ⟨rfl, rfl⟩
            simp [hStack]
      have hPopShape :=
        TypedCfgCompilerFacts.Shape.sourceLength_of_type?_pop
          hSourceOne hPopType
      have hInputBound :
          TypedCfgCompiler.Shape.sourceLength valueShape ≤
            source.source.evm.stack.length :=
        hRel.sourceStack
      have hOutputLength :
          TypedCfgCompiler.Shape.sourceLength bodyShape =
            TypedCfgCompiler.Shape.sourceLength valueShape - 1 :=
        hPopShape
      have hBodyBound :
          TypedCfgCompiler.Shape.sourceLength bodyShape ≤
            stack.length := by
        omega
      have hAfterPopAt :
          ObserverPreservation.StateRel.At bodyShape
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack }))
            tokens targetAfterPop trace :=
        ObserverPreservation.StateRel.At.ofFits hAfterPopRel (by
          have hTailFits :=
            TypedCfgCompilerFacts.Shape.sourceFrameFits_tail
              hSourceOne
              (show
                TypedCfgCompiler.Shape.SourceFrameFits valueShape
                  (stack.length + 1) by
                simpa [hPopLength] using hRel.sourceFrameFits)
          rw [TypedCfgCompilerFacts.Shape.eq_tail_of_type?_pop hPopType]
          exact hTailFits)
      have hBodyPositive : 0 < popFuel :=
        OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
          hAfterPopReach (hBodyEntryNotAccepted targetAfterPop)
      cases popFuel with
      | zero =>
          omega
      | succ bodyFuel =>
          obtain
              ⟨sourceFuel, sourceOutcome,
                hBodyEval, hOutcomeRel, hBodyArtifact⟩ :=
            hBodyAdequate hBodyCompile hBodyBlocks
              (fun bodySourceFuel bodyOutcome bodyTargetOutcome bodyTrace
                  hBodyEval hBodyRel hBodyArtifact => by
                have hArtifact :
                    OutcomeSimulation.OutcomeArtifact
                      { blocks :=
                          { label :=
                              TypedCfgCompiler.switchTestLabel base idx
                            input := valueShape
                            body := [.dup 0, .push caseValue, .prim .eq]
                            output :=
                              TypedCfgCompilerFacts.Switch.testOutput
                                valueShape
                            term :=
                              .jumpi (LabelSupply.label base (idx + 2))
                                (TypedCfgCompilerFacts.Switch.nextTestLabel
                                  base idx rest) } ::
                            { label := LabelSupply.label base (idx + 2)
                              input := valueShape
                              body := [.pop]
                              output := bodyShape
                              term :=
                                .jump (.generated base (2000 + idx)) } ::
                              bodyResult.blocks ++ tail.blocks
                        next := tail.next
                        calls := bodyResult.calls ++ tail.calls
                        fallthrough? := some bodyShape }
                      ctx bodyOutcome := by
                  apply
                    OutcomeSimulation.OutcomeArtifact.replaceRegular
                      hBodyArtifact
                  intro hRegular
                  obtain
                      ⟨bodyOutput, hBodyFallthrough, hBodyBound⟩ :=
                    OutcomeSimulation.OutcomeArtifact.regular
                      hBodyArtifact hRegular
                  rcases
                      TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
                        hRequire with
                    hNoFallthrough | hMatchingFallthrough
                  · rw [hNoFallthrough] at hBodyFallthrough
                    cases hBodyFallthrough
                  · have hOutputEq : bodyOutput = bodyShape :=
                      Option.some.inj
                        (hBodyFallthrough.symm.trans
                          hMatchingFallthrough)
                    subst bodyOutput
                    exact ⟨bodyShape, rfl, hBodyBound⟩
                exact
                  hAccept bodySourceFuel bodyOutcome
                    bodyTargetOutcome bodyTrace
                    hBodyEval hBodyRel hArtifact)
              hAfterPopAt hAfterPopReach
          have hArtifact :
              OutcomeSimulation.OutcomeArtifact
                { blocks :=
                    { label := TypedCfgCompiler.switchTestLabel base idx
                      input := valueShape
                      body := [.dup 0, .push caseValue, .prim .eq]
                      output :=
                        TypedCfgCompilerFacts.Switch.testOutput valueShape
                      term :=
                        .jumpi (LabelSupply.label base (idx + 2))
                          (TypedCfgCompilerFacts.Switch.nextTestLabel
                            base idx rest) } ::
                      { label := LabelSupply.label base (idx + 2)
                        input := valueShape
                        body := [.pop]
                        output := bodyShape
                        term :=
                          .jump (.generated base (2000 + idx)) } ::
                        bodyResult.blocks ++ tail.blocks
                  next := tail.next
                  calls := bodyResult.calls ++ tail.calls
                  fallthrough? := some bodyShape }
                ctx sourceOutcome := by
            apply
              OutcomeSimulation.OutcomeArtifact.replaceRegular
                hBodyArtifact
            intro hRegular
            obtain
                ⟨bodyOutput, hBodyFallthrough, hBodyBound⟩ :=
              OutcomeSimulation.OutcomeArtifact.regular
                hBodyArtifact hRegular
            rcases
                TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
                  hRequire with
              hNoFallthrough | hMatchingFallthrough
            · rw [hNoFallthrough] at hBodyFallthrough
              cases hBodyFallthrough
            · have hOutputEq : bodyOutput = bodyShape := by
                exact
                  Option.some.inj
                    (hBodyFallthrough.symm.trans hMatchingFallthrough)
              subst bodyOutput
              exact ⟨bodyShape, rfl, hBodyBound⟩
          exact
            ⟨sourceFuel, sourceOutcome,
              hBodyEval, hOutcomeRel, hArtifact⟩

/--
Backward composition for a skipped switch head. The generated test step is
removed and the recursive case-chain theorem receives the exact residual fuel.
-/
private theorem outcome_cases_tail_of_compileCasesFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {caseValue : Word} {body : Structured.Block}
    {rest : List (Word × Structured.Block)}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx
          valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hNe : caseValue ≠ value)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Block.Eval program sourceFuel selected
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack }))
            sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hNextEntryNotAccepted :
      ∀ targetState,
        ¬ accept
          (.jump
            (TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
            targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        valueShape source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        (TypedCfgCompiler.switchTestLabel base idx)
        target trace targetOutcome traceFinal)
    (hTailAdequate :
      ∀ {tailSupply : Nat} {tail : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx
            base tailSupply (idx + 1) valueShape bodyShape regular =
          some tail →
        TypedCfgPreservation.BlocksInProgram tail cfg →
        (∀ tailSourceFuel tailOutcome tailTargetOutcome tailFinalTrace,
          ObserverSemantics.Block.Eval program tailSourceFuel selected
              (source.withSource
                (source.source.withEVM
                  { source.source.evm with stack := stack }))
              tailOutcome →
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens tailOutcome
                tailTargetOutcome tailFinalTrace →
            OutcomeSimulation.OutcomeArtifact tail ctx tailOutcome →
            accept tailTargetOutcome) →
        ∀ {tailTargetFuel : Nat} {tailTarget : EVMState}
          {tailTrace : Trace},
          ObserverPreservation.StateRel.At
              valueShape source tokens tailTarget tailTrace →
          OutcomeSimulation.FirstReaches cfg accept (tailTargetFuel + 1)
              (TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
              tailTarget tailTrace targetOutcome traceFinal →
          ∃ sourceFuel sourceOutcome,
            ObserverSemantics.Block.Eval program sourceFuel selected
                (source.withSource
                  (source.source.withEVM
                    { source.source.evm with stack := stack }))
                sourceOutcome ∧
              ObserverPreservation.OutcomeSimulation.Rel
                continuations tokens sourceOutcome
                targetOutcome traceFinal ∧
              OutcomeSimulation.OutcomeArtifact tail ctx sourceOutcome) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval program sourceFuel selected
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome := by
  obtain
      ⟨bodyResult, tail, _hBodyCompile, _hRequire,
        hTailCompile, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
      hHead hPopType hCompile
  subst result
  have hTailBlocks :
      TypedCfgPreservation.BlocksInProgram tail cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  obtain ⟨targetAfterTest, hTestStep, hAfterTestRel⟩ :=
    ObserverPreservation.Switch.step_test
      (testLabel := TypedCfgCompiler.switchTestLabel base idx)
      (caseLabel := LabelSupply.label base (idx + 2))
      (nextTest :=
        TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
      (caseValue := caseValue) (value := value)
      hBlocks (by left) hHead hRel.rel hPop
  have hSkippedStep :
      TypedCfg.ObserverSemantics.Program.step cfg
          (TypedCfgCompiler.switchTestLabel base idx)
          target trace =
        .ok
          (.jump
            (TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
            targetAfterTest,
            trace) := by
    simpa [hNe] using hTestStep
  have hTailReach :=
    OutcomeSimulation.FirstReaches.tail_of_step_jump
      hReach hSkippedStep
  have hTailPositive : 0 < targetFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hTailReach (hNextEntryNotAccepted targetAfterTest)
  cases targetFuel with
  | zero =>
      omega
  | succ tailFuel =>
      have hAfterTestAt :
          ObserverPreservation.StateRel.At
            valueShape source tokens targetAfterTest trace :=
        ObserverPreservation.StateRel.At.ofFits
          hAfterTestRel hRel.sourceFrameFits
      obtain
          ⟨sourceFuel, sourceOutcome,
            hBodyEval, hOutcomeRel, hTailArtifact⟩ :=
        hTailAdequate hTailCompile hTailBlocks
          (fun tailSourceFuel tailOutcome tailTargetOutcome tailFinalTrace
              hTailEval hTailRel hTailArtifact => by
            have hTailFallthrough :
                tail.fallthrough? = some bodyShape :=
              TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
                hHead hPopType hTailCompile
            have hArtifact :
                OutcomeSimulation.OutcomeArtifact
                  { blocks :=
                      { label :=
                          TypedCfgCompiler.switchTestLabel base idx
                        input := valueShape
                        body := [.dup 0, .push caseValue, .prim .eq]
                        output :=
                          TypedCfgCompilerFacts.Switch.testOutput
                            valueShape
                        term :=
                          .jumpi (LabelSupply.label base (idx + 2))
                            (TypedCfgCompilerFacts.Switch.nextTestLabel
                              base idx rest) } ::
                        { label := LabelSupply.label base (idx + 2)
                          input := valueShape
                          body := [.pop]
                          output := bodyShape
                          term :=
                            .jump (.generated base (2000 + idx)) } ::
                          bodyResult.blocks ++ tail.blocks
                    next := tail.next
                    calls := bodyResult.calls ++ tail.calls
                    fallthrough? := some bodyShape }
                  ctx tailOutcome := by
              apply
                OutcomeSimulation.OutcomeArtifact.replaceRegular
                  hTailArtifact
              intro hRegular
              obtain ⟨tailOutput, hTailOutput, hTailBound⟩ :=
                OutcomeSimulation.OutcomeArtifact.regular
                  hTailArtifact hRegular
              have hOutputEq : tailOutput = bodyShape :=
                Option.some.inj
                  (hTailOutput.symm.trans hTailFallthrough)
              subst tailOutput
              exact ⟨bodyShape, rfl, hTailBound⟩
            exact
              hAccept tailSourceFuel tailOutcome
                tailTargetOutcome tailFinalTrace
                hTailEval hTailRel hArtifact)
          hAfterTestAt hTailReach
      have hTailFallthrough :
          tail.fallthrough? = some bodyShape :=
        TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
          hHead hPopType hTailCompile
      have hArtifact :
          OutcomeSimulation.OutcomeArtifact
            { blocks :=
                { label := TypedCfgCompiler.switchTestLabel base idx
                  input := valueShape
                  body := [.dup 0, .push caseValue, .prim .eq]
                  output :=
                    TypedCfgCompilerFacts.Switch.testOutput valueShape
                  term :=
                    .jumpi (LabelSupply.label base (idx + 2))
                      (TypedCfgCompilerFacts.Switch.nextTestLabel
                        base idx rest) } ::
                  { label := LabelSupply.label base (idx + 2)
                    input := valueShape
                    body := [.pop]
                    output := bodyShape
                    term :=
                      .jump (.generated base (2000 + idx)) } ::
                    bodyResult.blocks ++ tail.blocks
              next := tail.next
              calls := bodyResult.calls ++ tail.calls
              fallthrough? := some bodyShape }
            ctx sourceOutcome := by
        apply
          OutcomeSimulation.OutcomeArtifact.replaceRegular
            hTailArtifact
        intro hRegular
        obtain ⟨tailOutput, hTailOutput, hTailBound⟩ :=
          OutcomeSimulation.OutcomeArtifact.regular
            hTailArtifact hRegular
        have hOutputEq : tailOutput = bodyShape := by
          exact
            Option.some.inj
              (hTailOutput.symm.trans hTailFallthrough)
        subst tailOutput
        exact ⟨bodyShape, rfl, hTailBound⟩
      exact
        ⟨sourceFuel, sourceOutcome,
          hBodyEval, hOutcomeRel, hArtifact⟩

/--
Backward adequacy for a nonempty switch default. The generated pop adapter and
the selected body are composed with the checked default join.
-/
private theorem outcome_default_some_of_compileDefaultFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Block.Eval program sourceFuel body
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack }))
            sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hBodyEntryNotAccepted :
      ∀ targetState,
        ¬ accept (.jump (.generated supply 2000) targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        valueShape source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        entry target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000)
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel body
              (source.withSource
                (source.source.withEVM
                  { source.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept
          (.generated supply 2000) bodyShape
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          tokens) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval program sourceFuel body
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome := by
  obtain ⟨bodyResult, hBodyCompile, hRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
      hPopType hCompile
  subst result
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  obtain ⟨targetAfterPop, hPopStep, hAfterPopRel⟩ :=
    ObserverPreservation.BlocksInProgram.step_pop_jump
      (entry := entry) (regular := .generated supply 2000)
      (input := valueShape) (output := bodyShape)
      hBlocks (by left) hPopType hRel.rel hPop
  have hAfterPopReach :=
    OutcomeSimulation.FirstReaches.tail_of_step_jump
      hReach hPopStep
  have hBodyPositive : 0 < targetFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hAfterPopReach (hBodyEntryNotAccepted targetAfterPop)
  cases targetFuel with
  | zero =>
      omega
  | succ bodyFuel =>
      have hPopLength :
          source.source.evm.stack.length = stack.length + 1 := by
        cases hStack : source.source.evm.stack with
        | nil =>
            simp [hStack, EvmYul.Stack.pop] at hPop
        | cons head tail =>
            simp [hStack, EvmYul.Stack.pop] at hPop
            rcases hPop with ⟨rfl, rfl⟩
            simp [hStack]
      have hPopShape :=
        TypedCfgCompilerFacts.Shape.sourceLength_of_type?_pop
          hSourceOne hPopType
      have hInputBound :
          TypedCfgCompiler.Shape.sourceLength valueShape ≤
            source.source.evm.stack.length :=
        hRel.sourceStack
      have hOutputLength :
          TypedCfgCompiler.Shape.sourceLength bodyShape =
            TypedCfgCompiler.Shape.sourceLength valueShape - 1 :=
        hPopShape
      have hBodyBound :
          TypedCfgCompiler.Shape.sourceLength bodyShape ≤
            stack.length := by
        omega
      have hAfterPopAt :
          ObserverPreservation.StateRel.At bodyShape
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack }))
            tokens targetAfterPop trace :=
        ObserverPreservation.StateRel.At.ofFits hAfterPopRel (by
          have hTailFits :=
            TypedCfgCompilerFacts.Shape.sourceFrameFits_tail
              hSourceOne
              (show
                TypedCfgCompiler.Shape.SourceFrameFits valueShape
                  (stack.length + 1) by
                simpa [hPopLength] using hRel.sourceFrameFits)
          rw [TypedCfgCompilerFacts.Shape.eq_tail_of_type?_pop hPopType]
          exact hTailFits)
      obtain
          ⟨sourceFuel, sourceOutcome,
            hBodyEval, hOutcomeRel, hBodyArtifact⟩ :=
        hBodyAdequate hBodyCompile hBodyBlocks
          (fun bodySourceFuel bodyOutcome bodyTargetOutcome bodyTrace
              hBodyEval hBodyRel hBodyArtifact => by
            have hArtifact :
                OutcomeSimulation.OutcomeArtifact
                  { blocks :=
                      { label := entry
                        input := valueShape
                        body := [.pop]
                        output := bodyShape
                        term := .jump (.generated supply 2000) } ::
                        bodyResult.blocks
                    next := bodyResult.next
                    calls := bodyResult.calls
                    fallthrough? := some bodyShape }
                  ctx bodyOutcome := by
              apply
                OutcomeSimulation.OutcomeArtifact.replaceRegular
                  hBodyArtifact
              intro hRegular
              obtain
                  ⟨bodyOutput, hBodyFallthrough, hBodyBound⟩ :=
                OutcomeSimulation.OutcomeArtifact.regular
                  hBodyArtifact hRegular
              rcases
                  TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
                    hRequire with
                hNoFallthrough | hMatchingFallthrough
              · rw [hNoFallthrough] at hBodyFallthrough
                cases hBodyFallthrough
              · have hOutputEq : bodyOutput = bodyShape :=
                  Option.some.inj
                    (hBodyFallthrough.symm.trans hMatchingFallthrough)
                subst bodyOutput
                exact ⟨bodyShape, rfl, hBodyBound⟩
            exact
              hAccept bodySourceFuel bodyOutcome
                bodyTargetOutcome bodyTrace
                hBodyEval hBodyRel hArtifact)
          hAfterPopAt hAfterPopReach
      have hArtifact :
          OutcomeSimulation.OutcomeArtifact
            { blocks :=
                { label := entry
                  input := valueShape
                  body := [.pop]
                  output := bodyShape
                  term := .jump (.generated supply 2000) } ::
                  bodyResult.blocks
              next := bodyResult.next
              calls := bodyResult.calls
              fallthrough? := some bodyShape }
            ctx sourceOutcome := by
        apply
          OutcomeSimulation.OutcomeArtifact.replaceRegular
            hBodyArtifact
        intro hRegular
        obtain
            ⟨bodyOutput, hBodyFallthrough, hBodyBound⟩ :=
          OutcomeSimulation.OutcomeArtifact.regular
            hBodyArtifact hRegular
        rcases
            TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
              hRequire with
          hNoFallthrough | hMatchingFallthrough
        · rw [hNoFallthrough] at hBodyFallthrough
          cases hBodyFallthrough
        · have hOutputEq : bodyOutput = bodyShape := by
            exact
              Option.some.inj
                (hBodyFallthrough.symm.trans hMatchingFallthrough)
          subst bodyOutput
          exact ⟨bodyShape, rfl, hBodyBound⟩
      exact
        ⟨sourceFuel, sourceOutcome,
          hBodyEval, hOutcomeRel, hArtifact⟩

/--
Backward adequacy for an empty switch default. The generated adapter removes
the scrutinee value and immediately reaches the regular continuation.
-/
private theorem outcome_default_none_of_compileDefaultFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          none ctx supply entry valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hRegular : continuations.regular = regular)
    (hAccept :
      ∀ targetState acceptedTrace,
        ObserverPreservation.StateRel.At bodyShape
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          tokens targetState acceptedTrace →
        accept (.jump regular targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        valueShape source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ObserverPreservation.OutcomeSimulation.Rel
        continuations tokens
        (Structured.OutcomeT.regular
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack })))
        targetOutcome traceFinal ∧
      OutcomeSimulation.OutcomeArtifact result ctx
        (Structured.OutcomeT.regular
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))) := by
  have hResult :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_none
      hPopType hCompile
  subst result
  obtain ⟨targetAfterPop, hPopStep, hAfterPopRel⟩ :=
    ObserverPreservation.BlocksInProgram.step_pop_jump
      (entry := entry) (regular := regular)
      (input := valueShape) (output := bodyShape)
      hBlocks (by simp) hPopType hRel.rel hPop
  have hPopLength :
      source.source.evm.stack.length = stack.length + 1 := by
    cases hStack : source.source.evm.stack with
    | nil =>
        simp [hStack, EvmYul.Stack.pop] at hPop
    | cons head tail =>
        simp [hStack, EvmYul.Stack.pop] at hPop
        rcases hPop with ⟨rfl, rfl⟩
        simp [hStack]
  have hPopShape :=
    TypedCfgCompilerFacts.Shape.sourceLength_of_type?_pop
      hSourceOne hPopType
  have hInputBound :
      TypedCfgCompiler.Shape.sourceLength valueShape ≤
        source.source.evm.stack.length :=
    hRel.sourceStack
  have hOutputLength :
      TypedCfgCompiler.Shape.sourceLength bodyShape =
        TypedCfgCompiler.Shape.sourceLength valueShape - 1 :=
    hPopShape
  have hBodyBound :
      TypedCfgCompiler.Shape.sourceLength bodyShape ≤ stack.length := by
    omega
  have hBodyFits :
      TypedCfgCompiler.Shape.SourceFrameFits bodyShape stack.length := by
    have hTailFits :=
      TypedCfgCompilerFacts.Shape.sourceFrameFits_tail
        hSourceOne
        (show
          TypedCfgCompiler.Shape.SourceFrameFits valueShape
            (stack.length + 1) by
          simpa [hPopLength] using hRel.sourceFrameFits)
    rw [TypedCfgCompilerFacts.Shape.eq_tail_of_type?_pop hPopType]
    exact hTailFits
  have hAfterPopAt :
      ObserverPreservation.StateRel.At bodyShape
        (source.withSource
          (source.source.withEVM
            { source.source.evm with stack := stack }))
        tokens targetAfterPop trace :=
    ObserverPreservation.StateRel.At.ofFits
      hAfterPopRel hBodyFits
  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
      hReach hPopStep (hAccept targetAfterPop trace hAfterPopAt)
  subst targetOutcome
  subst traceFinal
  exact
    ⟨ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
        ⟨hRegular.symm, hAfterPopRel⟩,
      by
        show ∃ output,
          (some bodyShape : Option TypedCfg.Shape) = some output ∧
            TypedCfgCompiler.Shape.SourceFrameFits output stack.length
        exact ⟨bodyShape, rfl, hBodyFits⟩⟩

/--
Recursive backward adequacy for a switch case chain with no selected body.
Each failed test preserves the source state; the default callback owns the
single scrutinee pop at the end of the chain.
-/
private theorem outcome_cases_none_of_compileCasesFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = none)
    (hDispatchEntryNotAccepted :
      ∀ caseIdx remaining targetState,
        ¬ accept
          (.jump
            (TypedCfgCompilerFacts.Switch.casesEntryLabel
              base caseIdx remaining)
            targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        valueShape source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases)
        target trace targetOutcome traceFinal)
    (hDefaultAdequate :
      defaultBody = none →
        ∀ {defaultTargetFuel : Nat} {defaultTarget : EVMState}
          {defaultTrace : Trace},
          ObserverPreservation.StateRel.At
              valueShape source tokens defaultTarget defaultTrace →
          OutcomeSimulation.FirstReaches cfg accept
              (defaultTargetFuel + 1)
              (LabelSupply.label base 1)
              defaultTarget defaultTrace targetOutcome traceFinal →
          ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens
              (Structured.OutcomeT.regular
                (source.withSource
                  (source.source.withEVM
                    { source.source.evm with stack := stack })))
              targetOutcome traceFinal ∧
            TypedCfgCompiler.Shape.SourceFrameFits bodyShape stack.length) :
    ObserverPreservation.OutcomeSimulation.Rel
        continuations tokens
        (Structured.OutcomeT.regular
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack })))
        targetOutcome traceFinal ∧
      OutcomeSimulation.OutcomeArtifact result ctx
        (Structured.OutcomeT.regular
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))) := by
  induction cases generalizing
      compilerFuel supply idx result targetFuel target trace with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = none := by
            simpa [Structured.Switch.select] using hSelect
          obtain ⟨hOutcomeRel, hBodyFits⟩ :=
            hDefaultAdequate hDefault hRel hReach
          exact
            ⟨hOutcomeRel,
              by
                show ∃ output,
                  (some bodyShape : Option TypedCfg.Shape) = some output ∧
                    TypedCfgCompiler.Shape.SourceFrameFits output stack.length
                exact ⟨bodyShape, rfl, hBodyFits⟩⟩
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          have hNe : caseValue ≠ value := by
            intro hEq
            simp [Structured.Switch.select, hEq] at hSelect
          have hTailSelect :
              Structured.Switch.select value rest defaultBody = none := by
            simpa [Structured.Switch.select, hNe] using hSelect
          obtain
              ⟨bodyResult, tail, _hBodyCompile, _hRequire,
                hTailCompile, hResult⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          subst result
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro block hMem
            apply hBlocks block
            simp [hMem]
          obtain ⟨targetAfterTest, hTestStep, hAfterTestRel⟩ :=
            ObserverPreservation.Switch.step_test
              (testLabel := TypedCfgCompiler.switchTestLabel base idx)
              (caseLabel := LabelSupply.label base (idx + 2))
              (nextTest :=
                TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
              (caseValue := caseValue) (value := value)
              hBlocks (by left) hHead hRel.rel hPop
          have hSkippedStep :
              TypedCfg.ObserverSemantics.Program.step cfg
                  (TypedCfgCompiler.switchTestLabel base idx)
                  target trace =
                .ok
                  (.jump
                    (TypedCfgCompilerFacts.Switch.nextTestLabel
                      base idx rest)
                    targetAfterTest,
                    trace) := by
            simpa [hNe] using hTestStep
          have hTailReach :=
            OutcomeSimulation.FirstReaches.tail_of_step_jump
              hReach hSkippedStep
          have hTailPositive : 0 < targetFuel :=
            OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
              hTailReach
              (hDispatchEntryNotAccepted
                (idx + 1) rest targetAfterTest)
          cases targetFuel with
          | zero =>
              omega
          | succ tailFuel =>
              have hAfterTestAt :
                  ObserverPreservation.StateRel.At
                    valueShape source tokens targetAfterTest trace :=
                ObserverPreservation.StateRel.At.ofFits
                  hAfterTestRel hRel.sourceFrameFits
              obtain ⟨hOutcomeRel, hTailArtifact⟩ :=
                ih hTailCompile hTailBlocks hTailSelect
                  hAfterTestAt hTailReach
              have hTailFallthrough :
                  tail.fallthrough? = some bodyShape :=
                TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
                  hHead hPopType hTailCompile
              have hArtifact :
                  OutcomeSimulation.OutcomeArtifact
                    { blocks :=
                        { label :=
                            TypedCfgCompiler.switchTestLabel base idx
                          input := valueShape
                          body := [.dup 0, .push caseValue, .prim .eq]
                          output :=
                            TypedCfgCompilerFacts.Switch.testOutput
                              valueShape
                          term :=
                            .jumpi
                              (LabelSupply.label base (idx + 2))
                              (TypedCfgCompilerFacts.Switch.nextTestLabel
                                base idx rest) } ::
                          { label := LabelSupply.label base (idx + 2)
                            input := valueShape
                            body := [.pop]
                            output := bodyShape
                            term :=
                              .jump (.generated base (2000 + idx)) } ::
                            bodyResult.blocks ++ tail.blocks
                      next := tail.next
                      calls := bodyResult.calls ++ tail.calls
                      fallthrough? := some bodyShape }
                    ctx (Structured.OutcomeT.regular
                      (source.withSource
                        (source.source.withEVM
                          { source.source.evm with stack := stack }))) := by
                obtain ⟨tailOutput, hTailOutput, hTailBound⟩ :=
                  OutcomeSimulation.OutcomeArtifact.regular
                    hTailArtifact rfl
                have hOutputEq : tailOutput = bodyShape := by
                  exact
                    Option.some.inj
                      (hTailOutput.symm.trans hTailFallthrough)
                subst tailOutput
                exact ⟨bodyShape, rfl, hTailBound⟩
              exact ⟨hOutcomeRel, hArtifact⟩

/--
Recursive backward adequacy for a switch case chain selecting a body. The
selected body and default proofs are private recursive instances; generated
dispatch labels are never part of the public adjacent-pass boundary.
-/
private theorem outcome_cases_some_of_compileCasesFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType :
      TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hSourceOne :
      1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hPop : source.source.evm.stack.pop = some (stack, value))
    (hSelect :
      Structured.Switch.select value cases defaultBody = some selected)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Block.Eval program sourceFuel selected
            (source.withSource
              (source.source.withEVM
                { source.source.evm with stack := stack }))
            sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hDispatchEntryNotAccepted :
      ∀ caseIdx remaining targetState,
        ¬ accept
          (.jump
            (TypedCfgCompilerFacts.Switch.casesEntryLabel
              base caseIdx remaining)
            targetState))
    (hCaseEntryNotAccepted :
      ∀ caseIdx targetState,
        ¬ accept
          (.jump (LabelSupply.label base (caseIdx + 2)) targetState))
    (hBodyEntryNotAccepted :
      ∀ caseIdx targetState,
        ¬ accept
          (.jump (.generated base (2000 + caseIdx)) targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        valueShape source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        (TypedCfgCompilerFacts.Switch.casesEntryLabel base idx cases)
        target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (.generated base (2000 + caseIdx))
            bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel selected
              (source.withSource
                (source.source.withEVM
                  { source.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept
          (.generated base (2000 + caseIdx)) bodyShape
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          tokens)
    (hDefaultAdequate :
      defaultBody = some selected →
        ∀ {defaultTargetFuel : Nat} {defaultTarget : EVMState}
          {defaultTrace : Trace},
          ObserverPreservation.StateRel.At
              valueShape source tokens defaultTarget defaultTrace →
          OutcomeSimulation.FirstReaches cfg accept
              (defaultTargetFuel + 1)
              (LabelSupply.label base 1)
              defaultTarget defaultTrace targetOutcome traceFinal →
          ∃ sourceFuel sourceOutcome,
            ObserverSemantics.Block.Eval program sourceFuel selected
                (source.withSource
                  (source.source.withEVM
                    { source.source.evm with stack := stack }))
                sourceOutcome ∧
              ObserverPreservation.OutcomeSimulation.Rel
                continuations tokens sourceOutcome
                targetOutcome traceFinal ∧
              OutcomeSimulation.JoinArtifact
                ctx bodyShape sourceOutcome) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval program sourceFuel selected
          (source.withSource
            (source.source.withEVM
              { source.source.evm with stack := stack }))
          sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome := by
  induction cases generalizing
      compilerFuel supply idx result selected targetFuel target trace with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = some selected := by
            simpa [Structured.Switch.select] using hSelect
          obtain
              ⟨sourceFuel, sourceOutcome,
                hBodyEval, hOutcomeRel, hDefaultArtifact⟩ :=
            hDefaultAdequate hDefault hRel hReach
          exact
            ⟨sourceFuel, sourceOutcome,
              hBodyEval, hOutcomeRel,
              OutcomeSimulation.OutcomeArtifact.ofJoin
                rfl hDefaultArtifact⟩
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          by_cases hEq : caseValue = value
          · have hSelected : body = selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            subst selected
            exact
              outcome_cases_head_of_compileCasesFuel?_and_firstReaches
                hCompile hBlocks hHead hPopType hSourceOne hPop hEq hAccept
                (hCaseEntryNotAccepted idx)
                (hBodyEntryNotAccepted idx)
                hRel hReach
                (fun hBodyCompile hBodyBlocks =>
                  hBodyAdequate hBodyCompile hBodyBlocks)
          · have hTailSelect :
                Structured.Switch.select value rest defaultBody =
                  some selected := by
              simpa [Structured.Switch.select, hEq] using hSelect
            exact
              outcome_cases_tail_of_compileCasesFuel?_and_firstReaches
                (selected := selected)
                hCompile hBlocks hHead hPopType hSourceOne hPop hEq
                hAccept
                (hDispatchEntryNotAccepted (idx + 1) rest)
                hRel hReach
                (fun {_tailSupply} {_tail} hTailCompile hTailBlocks
                    hTailAccept
                    {_tailTargetFuel} {_tailTarget} {_tailTrace}
                    hTailRel hTailReach =>
                  ih hTailCompile hTailBlocks hTailSelect
                    hTailAccept hTailRel hTailReach
                    hBodyAdequate hDefaultAdequate)

/--
Top-level backward adequacy for a checked switch. Scrutinee inversion, case
dispatch, default dispatch, and the source evaluation constructor are composed
inside the owning Structured-to-TypedCfg boundary.
-/
private theorem outcome_switch_of_compileStmtFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Stmt.Eval program sourceFuel
            (.switch scrutinee cases defaultBody) source sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hDispatchEntryNotAccepted :
      ∀ caseIdx remaining targetState,
        ¬ accept
          (.jump
            (TypedCfgCompilerFacts.Switch.casesEntryLabel
              supply caseIdx remaining)
            targetState))
    (hCaseEntryNotAccepted :
      ∀ caseIdx targetState,
        ¬ accept
          (.jump (LabelSupply.label supply (caseIdx + 2)) targetState))
    (hGeneratedEntryNotAccepted :
      ∀ generatedSupply generatedOffset targetState,
        ¬ accept
          (.jump
            (.generated generatedSupply generatedOffset)
            targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        entry target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {selected : Structured.Block}
        {afterScrutinee : ObserverSemantics.State transcript}
        {stack : EvmYul.Stack Word} {value : Word}
        {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        ObserverSemantics.Code.run scrutinee source =
          .ok afterScrutinee →
        afterScrutinee.source.evm.stack.pop = some (stack, value) →
        Structured.Switch.select value cases defaultBody =
          some selected →
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel selected
              (afterScrutinee.withSource
                (afterScrutinee.source.withEVM
                  { afterScrutinee.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept bodyEntry bodyShape
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval program sourceFuel
          (.switch scrutinee cases defaultBody) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome := by
  obtain ⟨firstOutcome, firstTrace, hStep, _hAfterStep⟩ :=
    TypedCfg.ObserverSemantics.Program.runN_succ_elim hReach.run
  obtain
      ⟨valueShape, valueSlot, caseResult, defaultResult,
        afterScrutinee, stack, value, targetAfterScrutinee,
        hFirstOutcome, hType, hSource, hHead, hCasesCompile, hDefaultCompile,
        hResult, hScrutinee, hPop, hAfterScrutineeRel⟩ :=
    head_of_compileStmtFuel?_and_step
      (by simpa [Nat.add_assoc] using hCompile)
      hBlocks hRel hStep
  subst firstOutcome
  have hDispatchReach :
      OutcomeSimulation.FirstReaches cfg accept targetFuel
        (TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases)
        targetAfterScrutinee firstTrace targetOutcome traceFinal :=
    OutcomeSimulation.FirstReaches.tail_of_step_jump
      hReach hStep
  have hDispatchPositive : 0 < targetFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hDispatchReach
      (hDispatchEntryNotAccepted 0 cases targetAfterScrutinee)
  cases targetFuel with
  | zero =>
      omega
  | succ dispatchFuel =>
      let bodyShape : TypedCfg.Shape :=
        { valueShape with slots := valueShape.slots.tail }
      have hSourceOne :
          1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
        TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
          hSource
      have hPopType :
          TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
        cases valueShape with
        | mk slots tail =>
            cases slots with
            | nil =>
                simp at hHead
            | cons slot rest =>
                simp [bodyShape, TypedCfg.Instr.type?]
      have hCasesCompile' :
          TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
              cases ctx supply (supply + 1) 0 valueShape
              bodyShape regular =
            some caseResult := by
        simpa [bodyShape] using hCasesCompile
      have hDefaultCompile' :
          TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
              defaultBody ctx caseResult.next
              (LabelSupply.label supply 1) valueShape
              bodyShape regular =
            some defaultResult := by
        simpa [bodyShape] using hDefaultCompile
      subst result
      have hCaseBlocks :
          TypedCfgPreservation.BlocksInProgram caseResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hMem]
      have hDefaultBlocks :
          TypedCfgPreservation.BlocksInProgram defaultResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hMem]
      cases hSelect :
          Structured.Switch.select value cases defaultBody with
      | none =>
          obtain ⟨hOutcomeRel, hCaseArtifact⟩ :=
            outcome_cases_none_of_compileCasesFuel?_and_firstReaches
              hCasesCompile' hCaseBlocks hHead hPopType hSourceOne hPop
              hSelect
              hDispatchEntryNotAccepted
              hAfterScrutineeRel hDispatchReach
              (by
                intro hDefaultNone defaultTargetFuel defaultTarget
                  defaultTrace hDefaultRel hDefaultReach
                have hDefaultNoneCompile :
                    TypedCfgCompiler.compileDefaultFuel?
                        (compilerFuel + 1) none ctx caseResult.next
                        (LabelSupply.label supply 1)
                        valueShape bodyShape regular =
                      some defaultResult := by
                  simpa [hDefaultNone] using hDefaultCompile'
                obtain ⟨hDefaultOutcomeRel, hDefaultArtifact⟩ :=
                  outcome_default_none_of_compileDefaultFuel?_and_firstReaches
                    hDefaultNoneCompile hDefaultBlocks hPopType hSourceOne hPop
                    hRegular
                    (fun defaultTarget defaultTrace hDefaultAt =>
                      hAccept 1
                        (Structured.OutcomeT.regular
                          (afterScrutinee.withSource
                            (afterScrutinee.source.withEVM
                              { afterScrutinee.source.evm with
                                stack := stack })))
                        (.jump regular defaultTarget) defaultTrace
                        (Structured.EffectSemantics.Stmt.Eval.switch_none
                          (fuel := 0) hScrutinee hPop hSelect)
                        (ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                          ⟨hRegular.symm, hDefaultAt.rel⟩)
                        ⟨bodyShape, rfl,
                          hDefaultAt.sourceFrameFits⟩)
                    hDefaultRel hDefaultReach
                obtain
                    ⟨defaultOutput, hDefaultFallthrough,
                      hDefaultBound⟩ :=
                  OutcomeSimulation.OutcomeArtifact.regular
                    hDefaultArtifact rfl
                have hExpectedFallthrough :
                    defaultResult.fallthrough? = some bodyShape :=
                  TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
                    hPopType hDefaultNoneCompile
                have hOutputEq : defaultOutput = bodyShape :=
                  Option.some.inj
                    (hDefaultFallthrough.symm.trans
                      hExpectedFallthrough)
                subst defaultOutput
                exact ⟨hDefaultOutcomeRel, hDefaultBound⟩)
          have hCaseFallthrough :
              caseResult.fallthrough? = some bodyShape :=
            TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
              hHead hPopType hCasesCompile'
          have hArtifact :
              OutcomeSimulation.OutcomeArtifact
                { blocks :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term :=
                        .jump
                          (TypedCfgCompilerFacts.Switch.casesEntryLabel
                            supply 0 cases) } ::
                      caseResult.blocks ++ defaultResult.blocks
                  next := defaultResult.next
                  calls := caseResult.calls ++ defaultResult.calls
                  fallthrough? := some bodyShape }
                ctx (Structured.OutcomeT.regular
                  (afterScrutinee.withSource
                    (afterScrutinee.source.withEVM
                      { afterScrutinee.source.evm with stack := stack }))) := by
            obtain ⟨caseOutput, hCaseOutput, hCaseBound⟩ :=
              OutcomeSimulation.OutcomeArtifact.regular
                hCaseArtifact rfl
            have hOutputEq : caseOutput = bodyShape :=
              Option.some.inj
                (hCaseOutput.symm.trans hCaseFallthrough)
            subst caseOutput
            exact ⟨bodyShape, rfl, hCaseBound⟩
          exact
            ⟨1,
              Structured.OutcomeT.regular
                (afterScrutinee.withSource
                  (afterScrutinee.source.withEVM
                    { afterScrutinee.source.evm with stack := stack })),
              Structured.EffectSemantics.Stmt.Eval.switch_none
                (fuel := 0) hScrutinee hPop hSelect,
              hOutcomeRel, hArtifact⟩
      | some selected =>
          have hCaseFallthrough :
              caseResult.fallthrough? = some bodyShape :=
            TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
              hHead hPopType hCasesCompile'
          obtain
              ⟨bodyFuel, sourceOutcome,
                hBodyEval, hOutcomeRel, hCaseArtifact⟩ :=
            outcome_cases_some_of_compileCasesFuel?_and_firstReaches
              hCasesCompile' hCaseBlocks hHead hPopType hSourceOne hPop
              hSelect
              (fun selectedFuel selectedOutcome selectedTarget
                  selectedTrace hSelectedEval hSelectedRel
                  hSelectedArtifact => by
                have hParentArtifact :
                    OutcomeSimulation.OutcomeArtifact
                      { blocks :=
                          { label := entry
                            input := input
                            body := TypedCfgCompiler.Code.toCfg scrutinee
                            output := valueShape
                            term :=
                              .jump
                                (TypedCfgCompilerFacts.Switch.casesEntryLabel
                                  supply 0 cases) } ::
                            caseResult.blocks ++ defaultResult.blocks
                        next := defaultResult.next
                        calls := caseResult.calls ++ defaultResult.calls
                        fallthrough? := some bodyShape }
                      ctx selectedOutcome := by
                  apply
                    OutcomeSimulation.OutcomeArtifact.replaceRegular
                      hSelectedArtifact
                  intro hMode
                  obtain
                      ⟨caseOutput, hCaseOutput, hCaseBound⟩ :=
                    OutcomeSimulation.OutcomeArtifact.regular
                      hSelectedArtifact hMode
                  have hOutputEq : caseOutput = bodyShape :=
                    Option.some.inj
                      (hCaseOutput.symm.trans hCaseFallthrough)
                  subst caseOutput
                  exact ⟨bodyShape, rfl, hCaseBound⟩
                exact
                  hAccept (selectedFuel + 1) selectedOutcome
                    selectedTarget selectedTrace
                    (Structured.EffectSemantics.Stmt.Eval.switch_some
                      hScrutinee hPop rfl hSelect hSelectedEval)
                    hSelectedRel hParentArtifact)
              hDispatchEntryNotAccepted hCaseEntryNotAccepted
              (fun caseIdx =>
                hGeneratedEntryNotAccepted supply (2000 + caseIdx))
              hAfterScrutineeRel hDispatchReach
              (by
                intro bodyCompilerFuel caseSupply caseIdx bodyResult
                  hBodyCompile hBodyBlocks
                exact
                  hBodyAdequate hScrutinee hPop hSelect
                    hBodyCompile hBodyBlocks)
              (by
                intro hDefaultSelected defaultTargetFuel defaultTarget
                  defaultTrace hDefaultRel hDefaultReach
                have hDefaultSelectedCompile :
                    TypedCfgCompiler.compileDefaultFuel?
                        (compilerFuel + 1) (some selected) ctx
                        caseResult.next (LabelSupply.label supply 1)
                        valueShape bodyShape regular =
                      some defaultResult := by
                  simpa [hDefaultSelected] using hDefaultCompile'
                have hDefaultFallthrough :
                    defaultResult.fallthrough? = some bodyShape :=
                  TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
                    hPopType hDefaultSelectedCompile
                obtain
                    ⟨defaultBodyFuel, defaultOutcome,
                      hDefaultEval, hDefaultOutcomeRel,
                      hDefaultArtifact⟩ :=
                  outcome_default_some_of_compileDefaultFuel?_and_firstReaches
                    hDefaultSelectedCompile hDefaultBlocks hPopType
                    hSourceOne hPop
                    (fun selectedFuel selectedOutcome selectedTarget
                        selectedTrace hSelectedEval hSelectedRel
                        hSelectedArtifact => by
                      have hParentArtifact :
                          OutcomeSimulation.OutcomeArtifact
                            { blocks :=
                                { label := entry
                                  input := input
                                  body :=
                                    TypedCfgCompiler.Code.toCfg scrutinee
                                  output := valueShape
                                  term :=
                                    .jump
                                      (TypedCfgCompilerFacts.Switch.casesEntryLabel
                                        supply 0 cases) } ::
                                  caseResult.blocks ++ defaultResult.blocks
                              next := defaultResult.next
                              calls :=
                                caseResult.calls ++ defaultResult.calls
                              fallthrough? := some bodyShape }
                            ctx selectedOutcome := by
                        apply
                          OutcomeSimulation.OutcomeArtifact.replaceRegular
                            hSelectedArtifact
                        intro hMode
                        obtain
                            ⟨defaultOutput, hDefaultOutput,
                              hDefaultBound⟩ :=
                          OutcomeSimulation.OutcomeArtifact.regular
                            hSelectedArtifact hMode
                        have hOutputEq : defaultOutput = bodyShape :=
                          Option.some.inj
                            (hDefaultOutput.symm.trans
                              hDefaultFallthrough)
                        subst defaultOutput
                        exact ⟨bodyShape, rfl, hDefaultBound⟩
                      exact
                        hAccept (selectedFuel + 1) selectedOutcome
                          selectedTarget selectedTrace
                          (Structured.EffectSemantics.Stmt.Eval.switch_some
                            hScrutinee hPop rfl hSelect hSelectedEval)
                          hSelectedRel hParentArtifact)
                    (hGeneratedEntryNotAccepted caseResult.next 2000)
                    hDefaultRel hDefaultReach
                    (by
                      intro bodyResult hBodyCompile hBodyBlocks
                      exact
                        hBodyAdequate hScrutinee hPop hSelect
                          hBodyCompile hBodyBlocks)
                have hExpectedFallthrough :
                    defaultResult.fallthrough? = some bodyShape :=
                  TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
                    hPopType hDefaultSelectedCompile
                exact
                  ⟨defaultBodyFuel, defaultOutcome,
                    hDefaultEval, hDefaultOutcomeRel,
                    OutcomeSimulation.OutcomeArtifact.toJoin
                      hExpectedFallthrough hDefaultArtifact⟩)
          have hCaseFallthrough :
              caseResult.fallthrough? = some bodyShape :=
            TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
              hHead hPopType hCasesCompile'
          have hArtifact :
              OutcomeSimulation.OutcomeArtifact
                { blocks :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term :=
                        .jump
                          (TypedCfgCompilerFacts.Switch.casesEntryLabel
                            supply 0 cases) } ::
                      caseResult.blocks ++ defaultResult.blocks
                  next := defaultResult.next
                  calls := caseResult.calls ++ defaultResult.calls
                  fallthrough? := some bodyShape }
                ctx sourceOutcome := by
            apply
              OutcomeSimulation.OutcomeArtifact.replaceRegular
                hCaseArtifact
            intro hMode
            obtain ⟨caseOutput, hCaseOutput, hCaseBound⟩ :=
              OutcomeSimulation.OutcomeArtifact.regular
                hCaseArtifact hMode
            have hOutputEq : caseOutput = bodyShape :=
              Option.some.inj
                (hCaseOutput.symm.trans hCaseFallthrough)
            subst caseOutput
            exact ⟨bodyShape, rfl, hCaseBound⟩
          exact
            ⟨bodyFuel + 1, sourceOutcome,
              Structured.EffectSemantics.Stmt.Eval.switch_some
                hScrutinee hPop rfl hSelect hBodyEval,
              hOutcomeRel, hArtifact⟩

/--
Pass-owned `AdequateWithin` interface for checked switches. The generated
context theorem supplies the selected-body instance and generated-label
freshness facts.
-/
theorem adequateWithin_switch_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hDispatchEntryNotAccepted :
      ∀ caseIdx remaining targetState,
        ¬ accept
          (.jump
            (TypedCfgCompilerFacts.Switch.casesEntryLabel
              supply caseIdx remaining)
            targetState))
    (hCaseEntryNotAccepted :
      ∀ caseIdx targetState,
        ¬ accept
          (.jump (LabelSupply.label supply (caseIdx + 2)) targetState))
    (hGeneratedEntryNotAccepted :
      ∀ generatedSupply generatedOffset targetState,
        ¬ accept
          (.jump
            (.generated generatedSupply generatedOffset)
            targetState))
    (hBodyAdequate :
      ∀ {selected : Structured.Block}
        {afterScrutinee : ObserverSemantics.State transcript}
        {stack : EvmYul.Stack Word} {value : Word}
        {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label} {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        ObserverSemantics.Code.run scrutinee source =
          .ok afterScrutinee →
        afterScrutinee.source.evm.stack.pop = some (stack, value) →
        Structured.Switch.select value cases defaultBody =
          some selected →
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel selected
              (afterScrutinee.withSource
                (afterScrutinee.source.withEVM
                  { afterScrutinee.source.evm with stack := stack }))
              sourceOutcome)
          bodyResult ctx cfg continuations accept bodyEntry bodyShape
          (afterScrutinee.withSource
            (afterScrutinee.source.withEVM
              { afterScrutinee.source.evm with stack := stack }))
          tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.switch scrutinee cases defaultBody) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  exact
    outcome_switch_of_compileStmtFuel?_and_firstReaches
      hCompile hBlocks hRegular hAccept
      hDispatchEntryNotAccepted hCaseEntryNotAccepted
      hGeneratedEntryNotAccepted hRel hReach hBodyAdequate

end Switch

namespace Stmt

/--
Compiler-facing backward adequacy for a straight-line statement across active
procedure frames.
-/
theorem outcome_code_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program fuel
          (.code code) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final tokens targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? code input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (.jump regular targetFinal, traceFinal) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with ⟨⟨bodyFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            rcases hStep with ⟨hFinal, hTrace⟩
            subst bodyOutput
            simp [TypedCfg.Block.runTerm] at hFinal
            subst targetFinal
            subst traceFinal
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg
                hType hRel hBody
            exact
              ⟨final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                hFinalRel⟩
          · simp [generated, hOutput] at hStep

/--
First-boundary backward adequacy for a straight-line statement.
-/
theorem outcome_code_of_compileStmtFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Stmt.Eval
            program sourceFuel (.code code) source sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches
        cfg accept (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  obtain ⟨firstOutcome, firstTrace, hStep, _hAfterStep⟩ :=
    TypedCfg.ObserverSemantics.Program.runN_succ_elim hReach.run
  have hHeadStep := hStep
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? code input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (firstOutcome, firstTrace) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with
            ⟨⟨targetFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            subst bodyOutput
            rcases hStep with ⟨hFirst, hFirstTrace⟩
            subst firstOutcome
            subst firstTrace
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg
                hType hRel hBody
            have hFirstBoundary :
                OutcomeSimulation.TargetBoundary continuations
                  (.jump regular targetFinal) :=
              Or.inl hRegular.symm
            have hEval :
                ObserverSemantics.Stmt.Eval
                  program compilerFuel (.code code) source
                    (Structured.OutcomeT.regular final) :=
              Structured.EffectSemantics.Stmt.Eval.code hSourceRun
            have hOutcomeRel :
                ObserverPreservation.OutcomeSimulation.Rel
                  continuations tokens
                    (Structured.OutcomeT.regular final)
                    (.jump regular targetFinal) bodyTrace :=
              ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                ⟨hRegular.symm, hFinalRel⟩
            have hArtifact :
                OutcomeSimulation.OutcomeArtifact
                  { blocks := [generated]
                    next := supply + 1
                    calls := []
                    fallthrough? := some output }
                  ctx (Structured.OutcomeT.regular final) :=
              ⟨output, rfl,
                Code.sourceFrameFits code hType
                  hRel.sourceFrameFits hSourceRun⟩
            obtain ⟨hTargetOutcome, hTraceFinal⟩ :=
              OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
                hReach hHeadStep
                  (hAccept compilerFuel _ _ _
                    hEval hOutcomeRel hArtifact)
            subst targetOutcome
            subst traceFinal
            exact
              ⟨compilerFuel,
                Structured.OutcomeT.regular final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                  ⟨hRegular.symm, hFinalRel⟩⟩
          · simp [generated, hOutput] at hStep

theorem outcome_code_of_compileStmtFuel?_and_reachesBoundary
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.ReachesBoundary
        cfg continuations (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal :=
  outcome_code_of_compileStmtFuel?_and_firstReaches
    hCompile hBlocks hRegular
      (fun _ _ _ _ _ hRel _ =>
        OutcomeSimulation.targetBoundary_of_rel hRel)
      hRel hReach

theorem adequateWithin_code_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  obtain ⟨sourceFuel, sourceOutcome, hEval, hOutcomeRel⟩ :=
    outcome_code_of_compileStmtFuel?_and_firstReaches
      (program := program)
      hCompile hBlocks hRegular hAccept hRel hReach
  obtain ⟨output, hType, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code
      hCompile
  subst result
  cases hEval with
  | code hSourceRun =>
      exact
          ⟨sourceFuel, Structured.OutcomeT.regular _,
          Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
          hOutcomeRel,
          ⟨output, rfl,
            Code.sourceFrameFits code hType
              hRel.sourceFrameFits hSourceRun⟩⟩

theorem adequate_code_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.AdequateAt
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome)
      result ctx cfg continuations entry input source tokens := by
  exact
    OutcomeSimulation.AdequateWithin.toAdequateAt
      (adequateWithin_code_of_compileStmtFuel?
        (accept :=
          OutcomeSimulation.TargetBoundary continuations)
        hCompile hBlocks hRegular)

/--
Backward adequacy for a checked `break` continuation.
-/
theorem adequateWithin_brk_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular targetLabel : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : ctx.breakLabel? = some targetLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel .brk source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens := by
  obtain ⟨hShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_brk
      hTarget hCompile
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump targetLabel }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump targetLabel target, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    simp [generated, TypedCfg.ObserverSemantics.Block.run,
      TypedCfg.ObserverSemantics.Block.runBody_nil,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]
  have hBoundary :
      OutcomeSimulation.TargetBoundary
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        (.jump targetLabel target) :=
    Or.inr (Or.inl hTarget)
  have hEval :
      ObserverSemantics.Stmt.Eval
        program compilerFuel .brk source
          (Structured.OutcomeT.brk source) :=
    Structured.EffectSemantics.Stmt.Eval.brk
  have hOutcomeRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        tokens (Structured.OutcomeT.brk source)
          (.jump targetLabel target) trace :=
    ObserverPreservation.OutcomeSimulation.Rel.brk_iff.mpr
      ⟨hTarget, hRel.rel⟩
  have hArtifact :
      OutcomeSimulation.OutcomeArtifact
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx (Structured.OutcomeT.brk source) :=
    ⟨input, hShape, hRel.sourceFrameFits⟩
  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
      hReach hStep
        (hAccept compilerFuel _ _ _ hEval hOutcomeRel hArtifact)
  subst targetOutcome
  subst traceFinal
  exact
    ⟨compilerFuel, Structured.OutcomeT.brk source,
      Structured.EffectSemantics.Stmt.Eval.brk,
      ObserverPreservation.OutcomeSimulation.Rel.brk_iff.mpr
        ⟨hTarget, hRel.rel⟩,
      ⟨input, hShape, hRel.sourceFrameFits⟩⟩

/--
Backward adequacy for a checked `continue` continuation.
-/
theorem adequateWithin_cont_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular targetLabel : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : ctx.continueLabel? = some targetLabel)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel .cont source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens := by
  obtain ⟨hShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_cont
      hTarget hCompile
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump targetLabel }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump targetLabel target, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    simp [generated, TypedCfg.ObserverSemantics.Block.run,
      TypedCfg.ObserverSemantics.Block.runBody_nil,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]
  have hBoundary :
      OutcomeSimulation.TargetBoundary
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        (.jump targetLabel target) :=
    Or.inr (Or.inr (Or.inl hTarget))
  have hEval :
      ObserverSemantics.Stmt.Eval
        program compilerFuel .cont source
          (Structured.OutcomeT.cont source) :=
    Structured.EffectSemantics.Stmt.Eval.cont
  have hOutcomeRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        tokens (Structured.OutcomeT.cont source)
          (.jump targetLabel target) trace :=
    ObserverPreservation.OutcomeSimulation.Rel.cont_iff.mpr
      ⟨hTarget, hRel.rel⟩
  have hArtifact :
      OutcomeSimulation.OutcomeArtifact
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx (Structured.OutcomeT.cont source) :=
    ⟨input, hShape, hRel.sourceFrameFits⟩
  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
      hReach hStep
        (hAccept compilerFuel _ _ _ hEval hOutcomeRel hArtifact)
  subst targetOutcome
  subst traceFinal
  exact
    ⟨compilerFuel, Structured.OutcomeT.cont source,
      Structured.EffectSemantics.Stmt.Eval.cont,
      ObserverPreservation.OutcomeSimulation.Rel.cont_iff.mpr
        ⟨hTarget, hRel.rel⟩,
      ⟨input, hShape, hRel.sourceFrameFits⟩⟩

/--
Backward adequacy for a checked procedure `leave` continuation.
-/
theorem adequateWithin_leave_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular targetLabel : Assembly.Label}
    {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hTarget : ctx.leaveLabel? = some targetLabel)
    (hReturns : source.source.returns ≠ [])
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel .leave source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept entry input source tokens := by
  obtain ⟨hShape, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_leave
      hTarget hCompile
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump targetLabel }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump targetLabel target, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    simp [generated, TypedCfg.ObserverSemantics.Block.run,
      TypedCfg.ObserverSemantics.Block.runBody_nil,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]
  have hBoundary :
      OutcomeSimulation.TargetBoundary
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        (.jump targetLabel target) :=
    Or.inr (Or.inr (Or.inr hTarget))
  have hEval :
      ObserverSemantics.Stmt.Eval
        program compilerFuel .leave source
          (Structured.OutcomeT.leave source) :=
    Structured.EffectSemantics.Stmt.Eval.leave hReturns
  have hOutcomeRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular)
        tokens (Structured.OutcomeT.leave source)
          (.jump targetLabel target) trace :=
    ObserverPreservation.OutcomeSimulation.Rel.leave_iff.mpr
      ⟨hTarget, hRel.rel⟩
  have hArtifact :
      OutcomeSimulation.OutcomeArtifact
        { blocks := [generated]
          next := supply + 1
          calls := []
          fallthrough? := none }
        ctx (Structured.OutcomeT.leave source) :=
    ⟨input, hShape, hRel.sourceFrameFits⟩
  obtain ⟨hOutcomeEq, hTraceEq⟩ :=
    OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
      hReach hStep
        (hAccept compilerFuel _ _ _ hEval hOutcomeRel hArtifact)
  subst targetOutcome
  subst traceFinal
  exact
    ⟨compilerFuel, Structured.OutcomeT.leave source,
      Structured.EffectSemantics.Stmt.Eval.leave hReturns,
      ObserverPreservation.OutcomeSimulation.Rel.leave_iff.mpr
        ⟨hTarget, hRel.rel⟩,
      ⟨input, hShape, hRel.sourceFrameFits⟩⟩

/--
Compiler-facing backward adequacy for a straight-line statement at a boundary
with no active procedure frames.
-/
theorem outcome_code_of_compileStmtFuel?_and_step_noFrames
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel.At
        input source [] target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program fuel
          (.code code) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? code input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (.jump regular targetFinal, traceFinal) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with ⟨⟨bodyFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            rcases hStep with ⟨hFinal, hTrace⟩
            subst bodyOutput
            simp [TypedCfg.Block.runTerm] at hFinal
            subst targetFinal
            subst traceFinal
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg_noFrames
                hType hReturns hRel.rel hBody
            exact
              ⟨final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                hFinalRel⟩
          · simp [generated, hOutput] at hStep

/--
Backward adequacy for the false branch of a compiled conditional across active
procedure frames.
-/
theorem outcome_if_false_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program (fuel + 1)
          (.if_ cond body) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final tokens targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? cond input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      have hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 output =
            some () := by
        cases hCheck :
            TypedCfgCompiler.Shape.requireSourceWords? 1 output with
        | none =>
            simp [TypedCfgCompiler.mkCodeBlock?, hType, hCheck] at hCompile
        | some unit =>
            cases unit
            rfl
      simp only [TypedCfgCompiler.mkCodeBlock?, hType, Bind.bind,
        Option.bind] at hCompile
      rw [hSource] at hCompile
      simp at hCompile
      cases hHead : output.slots.head? with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkCodeBlock?, hBody] at hCompile
          | some bodyResult =>
              have hRequire :
                  bodyResult.requireFallthrough?
                      { output with slots := output.slots.tail } =
                    some () := by
                cases hCheck :
                    bodyResult.requireFallthrough?
                      { output with slots := output.slots.tail } with
                | none =>
                    simp [hType, hHead, TypedCfgCompiler.mkCodeBlock?,
                      hBody, hCheck] at hCompile
                | some unit =>
                    cases unit
                    rfl
              simp [hType, hHead, TypedCfgCompiler.mkCodeBlock?,
                hBody, hRequire] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok (.jump regular targetFinal, traceFinal) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    unfold TypedCfg.Block.runTerm at hTerm
                    cases hStack : targetAfter.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hTerm
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          subst targetFinal
                          subst traceFinal
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                false := by
                            rw [hZero]
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_self
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    false) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hSource hHead hRel
                              hCondBody hPop
                          exact
                            ⟨final,
                              Structured.EffectSemantics.Stmt.Eval.if_false
                                hCond,
                              hFinalRel.rel⟩
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          exact False.elim (hDistinct hTerm.1)
                  · simp [hOutput] at hStep

/--
Backward inversion for the taken head of a compiled conditional.

The generated `jumpi` block, its recursively generated body artifact, and the
post-pop body-entry shape are all reconstructed from the existing compiler
result. No body-preservation witness is accepted here.
-/
theorem condition_if_true_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok
          (.jump (LabelSupply.label supply 0) targetFinal,
            traceFinal)) :
    ∃ output condition bodyResult final,
      TypedCfgCompiler.Code.type? cond input = some output ∧
        output.slots.head? = some condition ∧
        TypedCfgCompiler.compileBlockFuel? fuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            { output with slots := output.slots.tail } regular =
          some bodyResult ∧
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ∧
        ObserverSemantics.Code.runCondition cond source =
          .ok (final, true) ∧
        ObserverPreservation.StateRel.At
          { output with slots := output.slots.tail }
          final tokens targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? cond input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      have hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 output =
            some () := by
        cases hCheck :
            TypedCfgCompiler.Shape.requireSourceWords? 1 output with
        | none =>
            simp [TypedCfgCompiler.mkCodeBlock?, hType, hCheck] at hCompile
        | some unit =>
            cases unit
            rfl
      simp only [TypedCfgCompiler.mkCodeBlock?, hType, Bind.bind,
        Option.bind] at hCompile
      rw [hSource] at hCompile
      simp at hCompile
      cases hHead : output.slots.head? with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkCodeBlock?, hBody] at hCompile
          | some bodyResult =>
              have hRequire :
                  bodyResult.requireFallthrough?
                      { output with slots := output.slots.tail } =
                    some () := by
                cases hCheck :
                    bodyResult.requireFallthrough?
                      { output with slots := output.slots.tail } with
                | none =>
                    simp [hType, hHead, TypedCfgCompiler.mkCodeBlock?,
                      hBody, hCheck] at hCompile
                | some unit =>
                    cases unit
                    rfl
              simp [hType, hHead, TypedCfgCompiler.mkCodeBlock?,
                hBody, hRequire] at hCompile
              cases hCompile
              have hBodyBlocks :
                  TypedCfgPreservation.BlocksInProgram
                    bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok
                    (.jump (LabelSupply.label supply 0)
                      targetFinal, traceFinal) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    unfold TypedCfg.Block.runTerm at hTerm
                    cases hStack : targetAfter.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hTerm
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          exact
                            False.elim (hDistinct hTerm.1.symm)
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          subst targetFinal
                          subst traceFinal
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                true := by
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_of_ne
                                value hZero
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    true) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hSource hHead hRel hCondBody hPop
                          exact
                            ⟨output, condition, bodyResult, final,
                              by simpa [TypedCfgCompiler.Code.type?]
                                using hType,
                              hHead, hBody, hBodyBlocks,
                              hCond, hFinalRel⟩
                  · simp [hOutput] at hStep

/--
Classify one successful generated conditional-head step and reconstruct the
corresponding source condition. The body compilation evidence is returned
existentially only in the taken branch.
-/
theorem condition_if_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace firstTrace : Trace} {firstOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (firstOutcome, firstTrace)) :
    (∃ output condition bodyResult final targetFinal,
        firstOutcome = .jump regular targetFinal ∧
          TypedCfgCompiler.Code.type? cond input = some output ∧
          output.slots.head? = some condition ∧
          TypedCfgCompiler.compileBlockFuel? fuel body ctx
              (supply + 1) (LabelSupply.label supply 0)
              { output with slots := output.slots.tail } regular =
            some bodyResult ∧
          bodyResult.requireFallthrough?
              { output with slots := output.slots.tail } =
            some () ∧
          result.fallthrough? =
            some { output with slots := output.slots.tail } ∧
          ObserverSemantics.Code.runCondition cond source =
            .ok (final, false) ∧
          ObserverPreservation.StateRel.At
            { output with slots := output.slots.tail }
            final tokens targetFinal firstTrace) ∨
      ∃ output condition bodyResult final targetFinal,
        firstOutcome =
            .jump (LabelSupply.label supply 0) targetFinal ∧
          TypedCfgCompiler.Code.type? cond input = some output ∧
          output.slots.head? = some condition ∧
          TypedCfgCompiler.compileBlockFuel? fuel body ctx
              (supply + 1) (LabelSupply.label supply 0)
              { output with slots := output.slots.tail } regular =
            some bodyResult ∧
          bodyResult.requireFallthrough?
              { output with slots := output.slots.tail } =
            some () ∧
          result.fallthrough? =
            some { output with slots := output.slots.tail } ∧
          TypedCfgPreservation.BlocksInProgram bodyResult cfg ∧
          ObserverSemantics.Code.runCondition cond source =
            .ok (final, true) ∧
          ObserverPreservation.StateRel.At
            { output with slots := output.slots.tail }
            final tokens targetFinal firstTrace := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? cond input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      have hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 output =
            some () := by
        cases hCheck :
            TypedCfgCompiler.Shape.requireSourceWords? 1 output with
        | none =>
            simp [TypedCfgCompiler.mkCodeBlock?, hType, hCheck] at hCompile
        | some unit =>
            cases unit
            rfl
      simp only [TypedCfgCompiler.mkCodeBlock?, hType, Bind.bind,
        Option.bind] at hCompile
      rw [hSource] at hCompile
      simp at hCompile
      cases hHead : output.slots.head? with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkCodeBlock?, hBody] at hCompile
          | some bodyResult =>
              have hRequire :
                  bodyResult.requireFallthrough?
                      { output with slots := output.slots.tail } =
                    some () := by
                cases hCheck :
                    bodyResult.requireFallthrough?
                      { output with slots := output.slots.tail } with
                | none =>
                    simp [hType, hHead, TypedCfgCompiler.mkCodeBlock?,
                      hBody, hCheck] at hCompile
                | some unit =>
                    cases unit
                    rfl
              simp [hType, hHead, TypedCfgCompiler.mkCodeBlock?,
                hBody, hRequire] at hCompile
              cases hCompile
              have hBodyBlocks :
                  TypedCfgPreservation.BlocksInProgram
                    bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok (firstOutcome, firstTrace) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    subst firstTrace
                    unfold TypedCfg.Block.runTerm at hTerm
                    obtain
                        ⟨afterCode, hSourceCode, hAfterCodeRel⟩ :=
                      Code.run_of_runBody_toCfg
                        (by simpa [TypedCfgCompiler.Code.type?]
                          using hType)
                        hRel hCondBody
                    have hOutputBound :
                        TypedCfgCompiler.Shape.sourceLength output ≤
                          afterCode.source.evm.stack.length :=
                      Code.shapeSound cond
                        (by simpa [TypedCfgCompiler.Code.type?]
                          using hType)
                        hRel.sourceStack hSourceCode
                    have hAfterCodeAt :
                        ObserverPreservation.StateRel.At
                          output afterCode tokens
                          targetAfter targetTrace :=
                      ObserverPreservation.StateRel.At.ofFits hAfterCodeRel
                        (Code.sourceFrameFits cond
                          (by simpa [TypedCfgCompiler.Code.type?]
                            using hType)
                          hRel.sourceFrameFits hSourceCode)
                    obtain ⟨hidden, hTargetStack⟩ :=
                      ObserverPreservation.StateRel.targetStack_eq_source_append_hidden
                        hAfterCodeAt
                    cases hStack : targetAfter.stack with
                    | nil =>
                        rw [hStack] at hTargetStack
                        simp at hTargetStack
                        have hOutputPos :
                            1 ≤
                              TypedCfgCompiler.Shape.sourceLength output :=
                          TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                            hSource
                        have hSourcePos :
                            1 ≤ afterCode.source.evm.stack.length :=
                          Nat.le_trans hOutputPos hOutputBound
                        simp [hTargetStack.1] at hSourcePos
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                false := by
                            rw [hZero]
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_self
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    false) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hSource hHead hRel hCondBody hPop
                          exact
                            Or.inl
                              ⟨output, condition, bodyResult, final,
                                { targetAfter with stack := stack },
                                hTerm.symm,
                                by simpa [TypedCfgCompiler.Code.type?]
                                  using hType,
                                hHead, hBody, hRequire, rfl,
                                hCond, hFinalRel⟩
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                true := by
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_of_ne
                                value hZero
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    true) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hSource hHead hRel hCondBody hPop
                          exact
                            Or.inr
                              ⟨output, condition, bodyResult, final,
                                { targetAfter with stack := stack },
                                hTerm.symm,
                                by simpa [TypedCfgCompiler.Code.type?]
                                  using hType,
                                hHead, hBody, hRequire, rfl, hBodyBlocks,
                                hCond, hFinalRel⟩
                  · simp [hOutput] at hStep

/--
Private structural composition for a taken conditional.

The eventual public recursive theorem supplies `hBodyAdequate` by induction;
the adjacent-pass API does not expose this callback.
-/
private theorem outcome_if_true_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations :
      TypedCfgPreservation.OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetAfter : EVMState}
    {trace traceAfter traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok
          (.jump (LabelSupply.label supply 0) targetAfter,
            traceAfter))
    (hBodyEventually :
      TypedCfg.ObserverSemantics.Program.Eventually
        cfg (LabelSupply.label supply 0) targetAfter traceAfter
        targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript}
        {bodyTarget : EVMState} {bodyTrace : Trace},
        TypedCfgCompiler.compileBlockFuel? fuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        ObserverPreservation.StateRel.At
          bodyInput afterCond tokens bodyTarget bodyTrace →
        TypedCfg.ObserverSemantics.Program.Eventually
          cfg (LabelSupply.label supply 0) bodyTarget bodyTrace
          targetOutcome traceFinal →
        ∃ bodyFuel bodyOutcome,
          ObserverSemantics.Block.Eval
              program bodyFuel body afterCond bodyOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens bodyOutcome
              targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  obtain
      ⟨output, condition, bodyResult, afterCond,
        _hType, _hHead, hBodyCompile, hBodyBlocks,
        hCond, hAfterCondRel⟩ :=
    condition_if_true_of_compileStmtFuel?_and_step
      (program := program)
      hCompile hBlocks hDistinct hRel hStep
  obtain ⟨bodyFuel, bodyOutcome, hBodyEval, hOutcomeRel⟩ :=
    hBodyAdequate hBodyCompile hBodyBlocks
      hAfterCondRel hBodyEventually
  exact
    ⟨bodyFuel + 1, bodyOutcome,
      Structured.EffectSemantics.Stmt.Eval.if_true
        hCond hBodyEval,
      hOutcomeRel⟩

/--
Fuel-decreasing backward adequacy for a compiled conditional up to the first
Structured continuation or halt. The recursive body premise is private proof
machinery and is discharged by the mutual block theorem.
-/
private theorem outcome_if_of_compileStmtFuel?_and_firstReaches
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hAccept :
      ∀ sourceFuel sourceOutcome acceptedOutcome acceptedTrace,
        ObserverSemantics.Stmt.Eval
            program sourceFuel (.if_ cond body) source sourceOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            continuations tokens sourceOutcome
              acceptedOutcome acceptedTrace →
          OutcomeSimulation.OutcomeArtifact result ctx sourceOutcome →
          accept acceptedOutcome)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches
        cfg accept (targetFuel + 1)
        entry target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript}
        {bodyTarget : EVMState} {bodyTrace : Trace}
        {bodyTargetFuel : Nat},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        (∀ bodySourceFuel bodyOutcome bodyTargetOutcome bodyFinalTrace,
          ObserverSemantics.Block.Eval
              program bodySourceFuel body afterCond bodyOutcome →
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens bodyOutcome
                bodyTargetOutcome bodyFinalTrace →
            OutcomeSimulation.OutcomeArtifact
              bodyResult ctx bodyOutcome →
            accept bodyTargetOutcome) →
        ObserverPreservation.StateRel.At
          bodyInput afterCond tokens bodyTarget bodyTrace →
        OutcomeSimulation.FirstReaches
          cfg accept bodyTargetFuel
          (LabelSupply.label supply 0)
          bodyTarget bodyTrace targetOutcome traceFinal →
        ∃ bodySourceFuel bodyOutcome,
          ObserverSemantics.Block.Eval
              program bodySourceFuel body afterCond bodyOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens bodyOutcome
              targetOutcome traceFinal ∧
            OutcomeSimulation.OutcomeArtifact
              bodyResult ctx bodyOutcome) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal ∧
        OutcomeSimulation.OutcomeArtifact
          result ctx sourceOutcome := by
  obtain ⟨firstOutcome, firstTrace, hStep, _hAfterStep⟩ :=
    TypedCfg.ObserverSemantics.Program.runN_succ_elim
      hReach.run
  rcases
      condition_if_of_compileStmtFuel?_and_step
        (program := program)
        hCompile hBlocks hRel hStep with
    hFalse | hTrue
  · rcases hFalse with
      ⟨output, condition, bodyResult, final, targetFinal,
        hFirst, _hType, _hHead, _hBodyCompile, _hRequire,
        hParentFallthrough, hCond, hFinalRel⟩
    subst firstOutcome
    have hFirstBoundary :
        OutcomeSimulation.TargetBoundary continuations
          (.jump regular targetFinal) :=
      Or.inl hRegular.symm
    have hEval :
        ObserverSemantics.Stmt.Eval
          program 1 (.if_ cond body) source
            (Structured.OutcomeT.regular final) :=
      Structured.EffectSemantics.Stmt.Eval.if_false
        (fuel := 0) hCond
    have hOutcomeRel :
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens (Structured.OutcomeT.regular final)
            (.jump regular targetFinal) firstTrace :=
      ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
        ⟨hRegular.symm, hFinalRel.rel⟩
    have hArtifact :
        OutcomeSimulation.OutcomeArtifact result ctx
          (Structured.OutcomeT.regular final) :=
      ⟨{ output with slots := output.slots.tail },
        hParentFallthrough, hFinalRel.sourceFrameFits⟩
    obtain ⟨hTargetOutcome, hTraceFinal⟩ :=
      OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
        hReach hStep
          (hAccept 1 _ _ _ hEval hOutcomeRel hArtifact)
    subst targetOutcome
    subst traceFinal
    exact
      ⟨1, Structured.OutcomeT.regular final,
        Structured.EffectSemantics.Stmt.Eval.if_false
          (fuel := 0) hCond,
        ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
          ⟨hRegular.symm, hFinalRel.rel⟩,
        by
          show ∃ regularOutput,
            result.fallthrough? = some regularOutput ∧
              TypedCfgCompiler.Shape.SourceFrameFits regularOutput
                final.source.evm.stack.length
          exact
            ⟨{ output with slots := output.slots.tail },
              hParentFallthrough, hFinalRel.sourceFrameFits⟩⟩
  · rcases hTrue with
      ⟨output, condition, bodyResult, afterCond, bodyTarget,
        hFirst, _hType, _hHead, hBodyCompile, hRequire,
        hParentFallthrough, hBodyBlocks, hCond, hAfterCondRel⟩
    subst firstOutcome
    have hBodyReach :
        OutcomeSimulation.FirstReaches
          cfg accept targetFuel
          (LabelSupply.label supply 0)
          bodyTarget firstTrace targetOutcome traceFinal :=
      OutcomeSimulation.FirstReaches.tail_of_step_jump
        hReach hStep
    obtain
        ⟨bodySourceFuel, bodyOutcome,
          hBodyEval, hOutcomeRel, hBodyArtifact⟩ :=
      hBodyAdequate hBodyCompile hBodyBlocks
        (fun bodyFuel bodyOutcome bodyTargetOutcome bodyFinalTrace
            hBodyEval hBodyRel hBodyArtifact => by
          have hParentArtifact :
              OutcomeSimulation.OutcomeArtifact
                result ctx bodyOutcome := by
            apply
              OutcomeSimulation.OutcomeArtifact.replaceRegular
                hBodyArtifact
            intro hMode
            obtain
                ⟨bodyOutput, hBodyFallthrough, hBodyBound⟩ :=
              OutcomeSimulation.OutcomeArtifact.regular
                hBodyArtifact hMode
            rcases
                TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
                  hRequire with
              hNoFallthrough | hMatchingFallthrough
            · rw [hNoFallthrough] at hBodyFallthrough
              cases hBodyFallthrough
            · rw [hMatchingFallthrough] at hBodyFallthrough
              have hOutputEq :
                  bodyOutput =
                    { output with slots := output.slots.tail } :=
                Option.some.inj hBodyFallthrough.symm
              subst bodyOutput
              exact
                ⟨{ output with slots := output.slots.tail },
                  hParentFallthrough, hBodyBound⟩
          exact
            hAccept (bodyFuel + 1) bodyOutcome
              bodyTargetOutcome bodyFinalTrace
              (Structured.EffectSemantics.Stmt.Eval.if_true
                hCond hBodyEval)
              hBodyRel hParentArtifact)
        hAfterCondRel hBodyReach
    have hArtifact :
        OutcomeSimulation.OutcomeArtifact result ctx bodyOutcome := by
      apply
        OutcomeSimulation.OutcomeArtifact.replaceRegular
          hBodyArtifact
      intro hMode
      obtain
          ⟨bodyOutput, hBodyFallthrough, hBodyBound⟩ :=
        OutcomeSimulation.OutcomeArtifact.regular
          hBodyArtifact hMode
      rcases
          TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
            hRequire with
        hNoFallthrough | hMatchingFallthrough
      · rw [hNoFallthrough] at hBodyFallthrough
        cases hBodyFallthrough
      · rw [hMatchingFallthrough] at hBodyFallthrough
        have hOutputEq :
            bodyOutput =
              { output with slots := output.slots.tail } := by
          exact Option.some.inj hBodyFallthrough.symm
        subst bodyOutput
        exact
          ⟨{ output with slots := output.slots.tail },
            hParentFallthrough, hBodyBound⟩
    exact
      ⟨bodySourceFuel + 1, bodyOutcome,
        Structured.EffectSemantics.Stmt.Eval.if_true
          hCond hBodyEval,
        hOutcomeRel, hArtifact⟩

/--
Pass-owned `AdequateWithin` composition rule for conditionals. The generated
context theorem supplies the body instance.
-/
theorem adequateWithin_if_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hBodyEntry :
      ∀ targetState,
        ¬ accept
            (.jump (LabelSupply.label supply 0) targetState))
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel body afterCond sourceOutcome)
          bodyResult ctx cfg continuations accept
          (LabelSupply.label supply 0)
          bodyInput afterCond tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome)
      result ctx cfg continuations accept entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  obtain
      ⟨sourceFuel, sourceOutcome,
        hEval, hOutcomeRel, hArtifact⟩ :=
    outcome_if_of_compileStmtFuel?_and_firstReaches
      hCompile hBlocks hRegular hAccept hRel hReach
      (by
        intro bodyInput bodyResult afterCond bodyTarget bodyTrace
          bodyTargetFuel hBodyCompile hBodyBlocks hBodyAccept hAfterCondRel
          hBodyReach
        have hPositive :
            0 < bodyTargetFuel :=
          OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
            hBodyReach (hBodyEntry bodyTarget)
        cases bodyTargetFuel with
        | zero =>
            omega
        | succ bodyTargetFuel =>
            obtain
                ⟨bodySourceFuel, bodyOutcome,
                  hBodyEval, hOutcomeRel, hBodyArtifact⟩ :=
              hBodyAdequate hBodyCompile hBodyBlocks
                hBodyAccept hAfterCondRel hBodyReach
            exact
              ⟨bodySourceFuel, bodyOutcome,
                hBodyEval, hOutcomeRel, hBodyArtifact⟩)
  exact
    ⟨sourceFuel, sourceOutcome, hEval, hOutcomeRel, hArtifact⟩

end Stmt

end ObserverAdequacy
end Structured
end EvmCompiler
