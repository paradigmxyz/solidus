import EvmCompiler.Yul.Compiler
import EvmCompiler.Yul.Semantics
import EvmCompiler.Yul.SolcValidation
import EvmCompiler.Objects.Preservation

namespace EvmCompiler
namespace Yul

namespace SourceLowered

abbrev WholeProgramOutcomeRel :=
  Objects.Source.WholeProgramOutcomeRel

end SourceLowered

namespace Program

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Structured.Preservation.ProcedurePreservation.compileChecked?
    lower.toStructured

noncomputable def compileLiveNoInternalCallChecked?
    (program : Program) : Option Assembly.Program := do
  let obj ← program.toObjects?
  Objects.Source.Program.compileLiveNoInternalCallChecked? obj

noncomputable def compileCheckedWithConservativeSpillSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Program) : Option Assembly.Program := do
  let obj ← program.toObjects?
  Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?
    range obj

noncomputable def compileCheckedWithAdaptiveSpillSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Program) : Option Assembly.Program := do
  let obj ← program.toObjects?
  Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
    range obj

noncomputable def compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
    (maxWords : Nat) (program : Program) :
    Option (Locals.SourceLowering.StateRel.SpillScratch.ScratchRange ×
      Assembly.Program) := do
  let obj ← program.toObjects?
  Objects.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
    maxWords obj

noncomputable def compileStackGuardedSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Program) : Option Assembly.Program :=
  match compileLiveNoInternalCallChecked? program with
  | some asm => some asm
  | none => compileCheckedWithAdaptiveSpillSourceOwned? range program

def StackGuardedSourceOwnedProgramOutcomeRel
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (initial : EVMState)
    (source : Objects.Source.Outcome) (target : Assembly.StepResult) : Prop :=
  SourceLowered.WholeProgramOutcomeRel source target ∨
    Locals.Source.Program.AdaptiveSpillProgramOutcomeRel range initial source
      target

def StackGuardedSourceOwnedObservableOutcomeRel
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (source : Objects.Source.Outcome) (target : Assembly.StepResult) : Prop :=
  SourceLowered.WholeProgramOutcomeRel source target ∨
    Locals.Source.Program.AdaptiveSpillObservableOutcomeRel range source target

/--
Scratch policy for the source-owned stack-guarded compiler.

The exact live-layout branch does not use private scratch memory.  The adaptive
fallback branch does, so the caller must prove the declared scratch range is
ready only when live-layout compilation fails.
-/
abbrev StackGuardedSourceOwnedFallbackScratchReady
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Program) (initial : EVMState) : Prop :=
  compileLiveNoInternalCallChecked? program = none →
    Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
        initial.toMachineState range [] [] [] =
      true

theorem StackGuardedSourceOwnedFallbackScratchReady.of_liveLayout
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {initial : EVMState} {asm : Assembly.Program}
    (hLiveLayout :
      compileLiveNoInternalCallChecked? program = some asm) :
    StackGuardedSourceOwnedFallbackScratchReady range program initial := by
  intro hFallback
  simp [hLiveLayout] at hFallback

theorem StackGuardedSourceOwnedFallbackScratchReady.of_scratchCheck
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {initial : EVMState}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true) :
    StackGuardedSourceOwnedFallbackScratchReady range program initial := by
  intro _hFallback
  exact hScratch

noncomputable def compileSolcChecked? (program : Program) :
    Option Assembly.Program :=
  if SolcValidation.ProgramOk? program then
    compileChecked? program
  else
    none

theorem compileSolcChecked?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileSolcChecked? program = some asm) :
    SolcValidation.ProgramOk program ∧
      compileChecked? program = some asm := by
  unfold compileSolcChecked? at hCompile
  cases hValid : SolcValidation.ProgramOk? program <;> simp [hValid] at hCompile
  exact ⟨hValid, hCompile⟩

theorem compileChecked?_eq_some {program : Program} {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Structured.Preservation.ProcedurePreservation.compileChecked?
          lower.toStructured = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileLiveNoInternalCallChecked?_eq_some
    {program : Program} {asm : Assembly.Program}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm) :
    ∃ obj : Objects.Program,
      program.toObjects? = some obj ∧
        Objects.Source.Program.compileLiveNoInternalCallChecked? obj =
          some asm := by
  unfold compileLiveNoInternalCallChecked? at hCompile
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hCompile
  | some obj =>
      simp [hObj] at hCompile
      exact ⟨obj, rfl, hCompile⟩

theorem compileCheckedWithConservativeSpillSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm) :
    ∃ obj : Objects.Program,
      program.toObjects? = some obj ∧
        Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?
            range obj =
          some asm := by
  unfold compileCheckedWithConservativeSpillSourceOwned? at hCompile
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hCompile
  | some obj =>
      simp [hObj] at hCompile
      exact ⟨obj, rfl, hCompile⟩

theorem compileCheckedWithConservativeSpillSourceOwned?_of_toObjects_compileBlockOpen?
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {obj : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    {asm : Assembly.Program}
    (hObj : program.toObjects? = some obj)
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          obj.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] obj.toFunctions.toLocals.body =
        some plan)
    (hCompile :
      Expressions.Program.compileChecked?
          (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
            plan) =
        some asm) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some asm := by
  unfold compileCheckedWithConservativeSpillSourceOwned?
  simp [hObj,
    Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?
      hOwnedCheck hPlan hCompile]

theorem compileCheckedWithConservativeSpillSourceOwned?_of_toObjects_compileBlockOpen?_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {obj : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hObj : program.toObjects? = some obj)
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          obj.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] obj.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  unfold compileCheckedWithConservativeSpillSourceOwned?
  simp [hObj,
    Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds
      hOwnedCheck hPlan hBounds]

theorem compileCheckedWithConservativeSpillSourceOwned?_of_toObjects_scopedFallback_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {obj : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hObj : program.toObjects? = some obj)
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          obj.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?
          range [] [] [] obj.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  unfold compileCheckedWithConservativeSpillSourceOwned?
  simp [hObj,
    Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds
      hOwnedCheck hPlan hBounds]

theorem compileCheckedWithAdaptiveSpillSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm) :
    ∃ obj : Objects.Program,
      program.toObjects? = some obj ∧
        Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
            range obj =
          some asm := by
  unfold compileCheckedWithAdaptiveSpillSourceOwned? at hCompile
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hCompile
  | some obj =>
      simp [hObj] at hCompile
      exact ⟨obj, rfl, hCompile⟩

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
    {maxWords : Nat} {program : Program}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm)) :
    ∃ obj : Objects.Program,
      program.toObjects? = some obj ∧
        Objects.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
            maxWords obj =
          some (range, asm) := by
  unfold compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned? at hCompile
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hCompile
  | some obj =>
      simp [hObj] at hCompile
      exact ⟨obj, rfl, hCompile⟩

theorem compileStackGuardedSourceOwned?_of_liveLayout
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hLive : compileLiveNoInternalCallChecked? program = some asm) :
    compileStackGuardedSourceOwned? range program = some asm := by
  simp [compileStackGuardedSourceOwned?, hLive]

theorem compileStackGuardedSourceOwned?_of_adaptiveFallback
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hLive : compileLiveNoInternalCallChecked? program = none)
    (hAdaptive :
      compileCheckedWithAdaptiveSpillSourceOwned? range program = some asm) :
    compileStackGuardedSourceOwned? range program = some asm := by
  simp [compileStackGuardedSourceOwned?, hLive, hAdaptive]

theorem compileStackGuardedSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hCompile :
      compileStackGuardedSourceOwned? range program = some asm) :
    compileLiveNoInternalCallChecked? program = some asm ∨
      compileLiveNoInternalCallChecked? program = none ∧
        compileCheckedWithAdaptiveSpillSourceOwned? range program =
          some asm := by
  unfold compileStackGuardedSourceOwned? at hCompile
  cases hLive : compileLiveNoInternalCallChecked? program with
  | none =>
      simp [hLive] at hCompile
      exact Or.inr ⟨rfl, hCompile⟩
  | some liveAsm =>
      simp [hLive] at hCompile
      cases hCompile
      exact Or.inl rfl

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_toObjects_compileBlockOpen?
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {obj : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    {asm : Assembly.Program}
    (hObj : program.toObjects? = some obj)
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          obj.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] obj.toFunctions.toLocals.body =
        some plan)
    (hCompile :
      Expressions.Program.compileChecked?
          (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
            plan) =
        some asm) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some asm := by
  unfold compileCheckedWithAdaptiveSpillSourceOwned?
  simp [hObj,
    Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?
      hOwnedCheck hPlan hCompile]

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_toObjects_compileBlockOpen?_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {obj : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hObj : program.toObjects? = some obj)
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          obj.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] obj.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  unfold compileCheckedWithAdaptiveSpillSourceOwned?
  simp [hObj,
    Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds
      hOwnedCheck hPlan hBounds]

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_toObjects_adaptiveFallback_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {obj : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hObj : program.toObjects? = some obj)
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          obj.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?
          range [] [] [] obj.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  unfold compileCheckedWithAdaptiveSpillSourceOwned?
  simp [hObj,
    Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds
      hOwnedCheck hPlan hBounds]

theorem accepted_of_sourceAccepted_compileChecked? {program : Program}
    {asm : Assembly.Program}
    (hSourceAccepted : program.SourceAccepted)
    (hCompile : compileChecked? program = some asm) :
    program.Accepted := by
  rcases hSourceAccepted with
    ⟨hWF, hSupported, lowerObj, hLowerObj, hObjSourceAccepted⟩
  rcases compileChecked?_eq_some hCompile with
    ⟨lowerExpr, hLowerExpr, hLowerCompile⟩
  have hObjExpr : lowerObj.toExpressions? = some lowerExpr := by
    unfold Program.toExpressions? at hLowerExpr
    simp [hLowerObj] at hLowerExpr
    exact hLowerExpr
  have hExprAccepted : lowerExpr.Accepted :=
    Structured.Preservation.ProcedurePreservation.accepted_of_compileChecked?
      hLowerCompile
  have hLocalsExpr :
      lowerObj.toFunctions.toLocals.toExpressions? = some lowerExpr := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?, Functions.Program.toExpressions?]
      using hObjExpr
  have hLocalsAccepted : lowerObj.toFunctions.toLocals.Accepted :=
    ⟨lowerExpr, hLocalsExpr, hExprAccepted⟩
  have hFunctionsAccepted :
      Functions.Inline.Program.Accepted lowerObj.toFunctions := by
    change Functions.Program.Accepted lowerObj.toFunctions
    exact
      ⟨hObjSourceAccepted.2.1, hObjSourceAccepted.2.2,
        hLocalsAccepted⟩
  exact
    ⟨hWF, hSupported, lowerObj, hLowerObj,
      ⟨hObjSourceAccepted.1, hFunctionsAccepted⟩⟩

theorem compileChecked?_noCallCreate_of_loweredFunctions
    {program : Program} {asm : Assembly.Program}
    (hLoweredFunctionsNoCall :
      ∀ obj : Objects.Program,
        program.toObjects? = some obj →
          obj.toFunctions.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  unfold Program.toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hLower
  | some obj =>
      simp [hObj] at hLower
      exact
        Objects.Source.Program.compileChecked?_noCallCreate
          (program := obj) (asm := asm)
          (hLoweredFunctionsNoCall obj hObj)
          (by
            unfold Objects.Source.Program.compileChecked?
            simp [hLower, hLowerCompile])

theorem compileLiveNoInternalCallChecked?_noCallCreate_of_loweredFunctions
    {program : Program} {asm : Assembly.Program}
    (hLoweredFunctionsNoCall :
      ∀ obj : Objects.Program,
        program.toObjects? = some obj →
          obj.toFunctions.usesCallCreate = false)
    (hCompile : compileLiveNoInternalCallChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  exact
    Objects.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
      (program := obj) (asm := asm)
      (hLoweredFunctionsNoCall obj hObj) hObjCompile

theorem compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile with
    ⟨obj, _hObj, hObjCompile⟩
  exact
    Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate
      hObjCompile

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_noCallCreate
    {maxWords : Nat} {program : Program}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm)) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
        hCompile with
    ⟨obj, _hObj, hObjCompile⟩
  exact
    Objects.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_noCallCreate
      hObjCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileCheckedWithConservativeSpillSourceOwned?_eq_some
      hCompile with
    ⟨obj, _hObj, hObjCompile⟩
  exact
    Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_noCallCreate
      hObjCompile

theorem compileStackGuardedSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    (hLoweredFunctionsNoCall :
      ∀ obj : Objects.Program,
        program.toObjects? = some obj →
          obj.toFunctions.usesCallCreate = false)
    (hCompile : compileStackGuardedSourceOwned? range program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  cases compileStackGuardedSourceOwned?_eq_some hCompile with
  | inl hLive =>
      exact
        compileLiveNoInternalCallChecked?_noCallCreate_of_loweredFunctions
          hLoweredFunctionsNoCall hLive
  | inr hFallback =>
      exact
        compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate hFallback.2

theorem compile_preserves {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Lowered.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  unfold Lowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun : obj.run fuel initial = .ok outcome := by
        simpa [hObj] using hRun
      exact
        Objects.Program.compile_preserves hLower hCompile hInitialPc hObjRun

theorem compile_preserves_checked {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Lowered.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  unfold Lowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun : obj.run fuel initial = .ok outcome := by
        simpa [hObj] using hRun
      have hObjCompile :
          Objects.Program.compileChecked? obj = some asm := by
        unfold Objects.Program.compileChecked?
        unfold Expressions.Program.compileChecked?
        simp [hLower, hStructuredCompile]
      exact
        Objects.Program.compile_preserves_checked
          hObjCompile hInitialPc hObjRun

theorem compileSolcChecked?_preserves {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileSolcChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : Lowered.run fuel program initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileSolcChecked?_eq_some hCompile with ⟨_hSolc, hCompileCore⟩
  exact compile_preserves_checked hCompileCore hInitialPc hRun

/--
Source-facing compiler theorem for the compiler-facing Yul adapter.

Unlike `Lowered.run`, this starts from `SourceLowered.run`, whose object and
function path uses the repaired stack-free source tower.  The remaining
frame-bound premise is a lower compiler obligation for the generated object,
not part of the Yul source semantics.
-/
theorem compile_source_preserves {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hSourceAccepted : program.SourceAccepted)
    (hFrameBound :
      ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
        Functions.SourceDirect.FrameBound.Program lowerObj.toFunctions)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      have hObjSourceAccepted : obj.SourceAccepted := by
        rcases hSourceAccepted with
          ⟨_hWF, _hSupported, witness, hWitness, hWitnessAccepted⟩
        have hEq : witness = obj := by
          have hSome : some witness = some obj := by
            rw [← hWitness, hObj]
          injection hSome
        simpa [hEq] using hWitnessAccepted
      exact
        Objects.Source.Program.compile_preserves
          (prim := prim) hPrim (program := obj) (lower := lower)
          (asm := asm) (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) hObjSourceAccepted
          (hFrameBound obj hObj) hLower hCompile hInitialPc hInitialStack
          hObjRun

theorem compile_source_preserves_checked
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hFrameBound :
      ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
        Functions.SourceDirect.FrameBound.Program lowerObj.toFunctions)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_source_preserves hPrim hSourceAccepted hFrameBound hLower
      hStructuredCompile hInitialPc hInitialStack hRun

theorem compileSolcChecked?_source_preserves
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileSolcChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hFrameBound :
      ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
        Functions.SourceDirect.FrameBound.Program lowerObj.toFunctions)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileSolcChecked?_eq_some hCompile with ⟨_hSolc, hCompileCore⟩
  exact
    compile_source_preserves_checked hPrim hCompileCore hSourceAccepted
      hFrameBound hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_source_preserves_checked
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  unfold SourceLowered.run at hRun
  simp [hObj] at hRun
  have hObjSourceAccepted : obj.SourceAccepted := by
    rcases hSourceAccepted with
      ⟨_hWF, _hSupported, witness, hWitness, hWitnessAccepted⟩
    have hEq : witness = obj := by
      have hSome : some witness = some obj := by
        rw [← hWitness, hObj]
      injection hSome
    simpa [hEq] using hWitnessAccepted
  exact
    Objects.Source.Program.compile_live_noInternalCall_preserves_checked
      (prim := prim) hPrim (program := obj) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hObjCompile hObjSourceAccepted
      hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_source_preserves_checked_endPc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  unfold SourceLowered.run at hRun
  simp [hObj] at hRun
  have hObjSourceAccepted : obj.SourceAccepted := by
    rcases hSourceAccepted with
      ⟨_hWF, _hSupported, witness, hWitness, hWitnessAccepted⟩
    have hEq : witness = obj := by
      have hSome : some witness = some obj := by
        rw [← hWitness, hObj]
      injection hSome
    simpa [hEq] using hWitnessAccepted
  exact
    Objects.Source.Program.compile_live_noInternalCall_preserves_checked_endPc
      (prim := prim) hPrim (program := obj) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hObjCompile hObjSourceAccepted
      hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_source_preserves_checked_anyFuel
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, _hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run prim fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  have hObjRunSucc :
      Objects.Source.Program.run prim (fuel + 1) obj initial =
        .ok sourceOutcome := by
    have hFunctionRun :
        Functions.Source.Program.run prim fuel obj.toFunctions initial =
          .ok sourceOutcome := by
      cases obj with
      | mk root =>
          cases root with
          | mk name code data objects =>
              simpa [Objects.Source.Program.run, Objects.Source.Object.run,
                Objects.Program.toFunctions, Objects.Object.toFunctions]
                using hObjRun
    have hFunctionRunSucc :
        Functions.Source.Program.run prim (fuel + 1) obj.toFunctions initial =
          .ok sourceOutcome := by
      simpa [Functions.Source.Program.run,
        Functions.Source.Program.runState] using
        Functions.Source.Block.runScoped_mono prim obj.toFunctions
          (Nat.le_succ fuel) hFunctionRun
    cases obj with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Objects.Source.Program.run, Objects.Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions]
              using hFunctionRunSucc
  have hRunSucc :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hObjRunSucc
  exact
    compile_live_noInternalCall_source_preserves_checked
      (prim := prim) hPrim (program := program) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted hInitialPc
      hInitialStack hRunSucc

theorem compile_live_noInternalCall_source_preserves_checked_endPc_anyFuel
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileLiveNoInternalCallChecked?_eq_some hCompile with
    ⟨obj, hObj, _hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run prim fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  have hObjRunSucc :
      Objects.Source.Program.run prim (fuel + 1) obj initial =
        .ok sourceOutcome := by
    have hFunctionRun :
        Functions.Source.Program.run prim fuel obj.toFunctions initial =
          .ok sourceOutcome := by
      cases obj with
      | mk root =>
          cases root with
          | mk name code data objects =>
              simpa [Objects.Source.Program.run, Objects.Source.Object.run,
                Objects.Program.toFunctions, Objects.Object.toFunctions]
                using hObjRun
    have hFunctionRunSucc :
        Functions.Source.Program.run prim (fuel + 1) obj.toFunctions initial =
          .ok sourceOutcome := by
      simpa [Functions.Source.Program.run,
        Functions.Source.Program.runState] using
        Functions.Source.Block.runScoped_mono prim obj.toFunctions
          (Nat.le_succ fuel) hFunctionRun
    cases obj with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Objects.Source.Program.run, Objects.Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions]
              using hFunctionRunSucc
  have hRunSucc :
      SourceLowered.run prim (fuel + 1) program initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hObjRunSucc
  exact
    compile_live_noInternalCall_source_preserves_checked_endPc
      (prim := prim) hPrim (program := program) (asm := asm)
      (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted hInitialPc
      hInitialStack hRunSucc

theorem compileCheckedWithConservativeSpillSourceOwned?_source_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.ConservativeSpillProgramOutcomeRel range initial
        sourceOutcome targetOutcome := by
  rcases compileCheckedWithConservativeSpillSourceOwned?_eq_some
      hCompile with
    ⟨obj, hObj, hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  exact
    Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_preserves
      hSpec hWordBytes hObjCompile hBoundary hInitialPc hObjRun

theorem compileCheckedWithConservativeSpillSourceOwned?_source_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.ConservativeSpillObservableOutcomeRel range
        sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileCheckedWithConservativeSpillSourceOwned?_eq_some
      hCompile with
    ⟨obj, hObj, hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  exact
    Objects.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_observations
      hSpec hWordBytes hObjCompile hBoundary hInitialPc hObjRun

theorem compileCheckedWithAdaptiveSpillSourceOwned?_source_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillProgramOutcomeRel range initial
        sourceOutcome targetOutcome := by
  rcases compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  exact
    Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_preserves
      hSpec hWordBytes hObjCompile hBoundary hInitialPc hObjRun

theorem compileCheckedWithAdaptiveSpillSourceOwned?_source_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillObservableOutcomeRel range
        sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile with
    ⟨obj, hObj, hObjCompile⟩
  have hObjRun :
      Objects.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  exact
    Objects.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_observations
      hSpec hWordBytes hObjCompile hBoundary hInitialPc hObjRun

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_source_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {maxWords : Nat}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm))
    (hInitialMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchInitialMemoryEmpty
        initial.toMachineState)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillPrivateObservableProgramOutcomeRel
        range sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
        hCompile with
    ⟨obj, hObj, hObjCompile⟩
  have hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec :=
    Locals.SourceLowering.StateRel.SpillScratch.wordByteEncoding_of_zeroPadding
      hSpec
  have hObjRun :
      Objects.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel obj initial =
        .ok sourceOutcome := by
    simpa [SourceLowered.run, hObj] using hRun
  exact
    Objects.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_observations
      hSpec hWordBytes hObjCompile hInitialMemory hInitialPc hObjRun

theorem compileStackGuardedSourceOwned?_source_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileStackGuardedSourceOwned? range program = some asm)
    (hBoundary :
      StackGuardedSourceOwnedFallbackScratchReady range program initial)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      StackGuardedSourceOwnedProgramOutcomeRel range initial sourceOutcome
        targetOutcome := by
  cases compileStackGuardedSourceOwned?_eq_some hCompile with
  | inl hLive =>
      rcases
        compile_live_noInternalCall_source_preserves_checked_anyFuel
          Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound hLive
          hSourceAccepted hInitialPc hInitialStack hRun with
      ⟨targetFuel, targetOutcome, hTargetRun, hRel⟩
      exact
        ⟨targetFuel, targetOutcome, hTargetRun,
          Or.inl hRel⟩
  | inr hFallback =>
      rcases hFallback with ⟨hLiveNone, hAdaptive⟩
      rcases
        compileCheckedWithAdaptiveSpillSourceOwned?_source_preserves
          hSpec hWordBytes hAdaptive (hBoundary hLiveNone) hInitialPc hRun with
      ⟨targetFuel, targetOutcome, hTargetRun, hRel⟩
      exact
        ⟨targetFuel, targetOutcome, hTargetRun,
          Or.inr hRel⟩

theorem compileStackGuardedSourceOwned?_source_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileStackGuardedSourceOwned? range program = some asm)
    (hBoundary :
      StackGuardedSourceOwnedFallbackScratchReady range program initial)
    (hSourceAccepted : program.SourceAccepted)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      StackGuardedSourceOwnedObservableOutcomeRel range sourceOutcome
        targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  cases compileStackGuardedSourceOwned?_eq_some hCompile with
  | inl hLive =>
      rcases
        compile_live_noInternalCall_source_preserves_checked_endPc_anyFuel
          Locals.SourceLowering.PrimitiveSemantics.structured_primitiveSound hLive
          hSourceAccepted hInitialPc hInitialStack hRun with
      ⟨targetFuel, targetOutcome, hTargetRun, hRel, hEndPc⟩
      exact
        ⟨targetFuel, targetOutcome, hTargetRun,
          Or.inl hRel, hEndPc⟩
  | inr hFallback =>
      rcases hFallback with ⟨hLiveNone, hAdaptive⟩
      rcases
        compileCheckedWithAdaptiveSpillSourceOwned?_source_observations
          hSpec hWordBytes hAdaptive (hBoundary hLiveNone) hInitialPc hRun with
      ⟨targetFuel, targetOutcome, hTargetRun, hRel, hEndPc⟩
      exact
        ⟨targetFuel, targetOutcome, hTargetRun,
          Or.inr hRel, hEndPc⟩

/--
Source-facing compiler acceptance for the Yul adapter.

This is not the imported Nethermind source semantics itself. It is the
compiler-side acceptance package for the lowering into the repaired source
tower: Yul source acceptedness plus object/function compiler resource bounds
for the object actually produced by `toObjects?`.
-/
structure SourceCompileAccepted (program : Program) : Prop where
  source : program.SourceAccepted
  objects :
    ∀ lowerObj : Objects.Program, program.toObjects? = some lowerObj →
      Objects.Source.Program.CompileAccepted lowerObj

theorem compile_source_preserves_of_compileAccepted
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hAccepted : SourceCompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      exact
        Objects.Source.Program.compile_preserves_of_compileAccepted
          (prim := prim) hPrim (program := obj) (lower := lower)
          (asm := asm) (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) (hAccepted.objects obj hObj)
          hLower hCompile hInitialPc hInitialStack hObjRun

theorem compile_source_preserves_of_compileAccepted_endPc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Objects.Source.Outcome}
    (hAccepted : SourceCompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      exact
        Objects.Source.Program.compile_preserves_of_compileAccepted_endPc
          (prim := prim) hPrim (program := obj) (lower := lower)
          (asm := asm) (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) (hAccepted.objects obj hObj)
          hLower hCompile hInitialPc hInitialStack hObjRun

theorem compile_source_preserves_checked_of_compileAccepted
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : SourceCompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      have hObjCompile :
          Objects.Source.Program.compileChecked? obj = some asm := by
        unfold Objects.Source.Program.compileChecked?
        simp [hLower, hStructuredCompile]
      exact
        Objects.Source.Program.compile_preserves_checked_of_compileAccepted
          (prim := prim) hPrim (program := obj) (asm := asm)
          (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) hObjCompile
          (hAccepted.objects obj hObj) hInitialPc hInitialStack hObjRun

theorem compile_source_preserves_checked_of_compileAccepted_endPc
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : SourceCompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  unfold SourceLowered.run at hRun
  unfold toExpressions? at hLower
  cases hObj : program.toObjects? with
  | none =>
      simp [hObj] at hRun
  | some obj =>
      simp [hObj] at hLower
      have hObjRun :
          Objects.Source.Program.run prim fuel obj initial =
            .ok sourceOutcome := by
        simpa [hObj] using hRun
      have hObjCompile :
          Objects.Source.Program.compileChecked? obj = some asm := by
        unfold Objects.Source.Program.compileChecked?
        simp [hLower, hStructuredCompile]
      exact
        Objects.Source.Program.compile_preserves_checked_of_compileAccepted_endPc
          (prim := prim) hPrim (program := obj) (asm := asm)
          (fuel := fuel) (initial := initial)
          (sourceOutcome := sourceOutcome) hObjCompile
          (hAccepted.objects obj hObj) hInitialPc hInitialStack hObjRun

theorem compileSolcChecked?_source_preserves_of_compileAccepted
    {prim : Objects.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Objects.Source.Outcome}
    (hCompile : compileSolcChecked? program = some asm)
    (hAccepted : SourceCompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      SourceLowered.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      SourceLowered.WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileSolcChecked?_eq_some hCompile with ⟨_hSolc, hCompileCore⟩
  exact
    compile_source_preserves_checked_of_compileAccepted hPrim hCompileCore
      hAccepted hInitialPc hInitialStack hRun

end Program

end Yul
end EvmCompiler
