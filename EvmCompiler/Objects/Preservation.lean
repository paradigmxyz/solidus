import EvmCompiler.Objects.Compiler
import EvmCompiler.Objects.Semantics
import EvmCompiler.Objects.SourceSemantics
import EvmCompiler.Functions.Preservation
import EvmCompiler.Functions.LiveLayoutPreservation
import EvmCompiler.Functions.CallAwareSpill
import EvmCompiler.Functions.ScratchFrameSpill
import EvmCompiler.Functions.ScratchFrameMemory

namespace EvmCompiler
namespace Objects

namespace Program

theorem run_toFunctions {fuel : Nat} {program : Program}
    {initial : EVMState} :
    program.run fuel initial =
      Functions.Program.run fuel program.toFunctions initial := by
  cases program with
  | mk root =>
      cases root with
      | mk name code data objects =>
          rfl

theorem eval_toFunctions {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hEval : Program.Eval fuel program initial outcome) :
    Functions.Program.Eval fuel program.toFunctions initial outcome := by
  cases hEval with
  | ofRun hRun =>
      exact Functions.Program.eval_of_run
        (by simpa [run_toFunctions] using hRun)

noncomputable def compileChecked? (program : Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Expressions.Program.compileChecked? lower

theorem compileChecked?_eq_some {program : Program}
    {asm : Assembly.Program}
    (hCompile : compileChecked? program = some asm) :
    ∃ lower : Expressions.Program,
      program.toExpressions? = some lower ∧
        Expressions.Program.compileChecked? lower = some asm := by
  unfold compileChecked? at hCompile
  cases hLower : program.toExpressions? with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact ⟨lower, rfl, hCompile⟩

theorem compileChecked?_noCallCreate {program : Program}
    {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hFunctionCompile :
      Functions.Program.compileChecked? program.toFunctions = some asm := by
    unfold Functions.Program.compileChecked?
    have hFunctionLower :
        program.toFunctions.toExpressions? = some lower := by
      simpa [Program.toExpressions?, Functions.Inline.Program.toExpressions?]
        using hLower
    simp [hFunctionLower, hLowerCompile]
  exact
    Functions.Program.compileChecked?_noCallCreate hProgram hFunctionCompile

theorem compile_preserves {program : Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  exact
    Functions.Inline.Program.compile_preserves hLower hCompile hInitialPc
      (by simpa [run_toFunctions] using hRun)

theorem compile_preserves_endPc {program : Program}
    {lower : Expressions.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {outcome : Outcome}
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  exact
    Functions.Inline.Program.compile_preserves_endPc hLower hCompile
      hInitialPc (by simpa [run_toFunctions] using hRun)

theorem compile_preserves_checked {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hFunctionCompile :
      Functions.Program.compileChecked? program.toFunctions = some asm := by
    unfold Functions.Program.compileChecked?
    have hFunctionLower :
        program.toFunctions.toExpressions? = some lower := by
      simpa [Program.toExpressions?, Functions.Inline.Program.toExpressions?]
        using hLower
    simp [hFunctionLower, hLowerCompile]
  exact
    Functions.Program.compile_preserves_checked
      hFunctionCompile hInitialPc (by simpa [run_toFunctions] using hRun)

theorem compile_preserves_checked_endPc {program : Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {outcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun : program.run fuel initial = .ok outcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel outcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hFunctionCompile :
      Functions.Program.compileChecked? program.toFunctions = some asm := by
    unfold Functions.Program.compileChecked?
    have hFunctionLower :
        program.toFunctions.toExpressions? = some lower := by
      simpa [Program.toExpressions?, Functions.Inline.Program.toExpressions?]
        using hLower
    simp [hFunctionLower, hLowerCompile]
  exact
    Functions.Program.compile_preserves_checked_endPc
      hFunctionCompile hInitialPc (by simpa [run_toFunctions] using hRun)

end Program

namespace Source

abbrev WholeProgramOutcomeRel :=
  Functions.Source.WholeProgramOutcomeRel

namespace Program

/--
Source-facing compiler acceptance for objects.

The object source semantics remains a root-object adapter over
`Functions.Source`.  Function-frame resource bounds are bundled as compiler
acceptance for the extracted function program rather than exposed as object
source semantics.
-/
structure CompileAccepted (program : Objects.Program) : Prop where
  source : Objects.Program.SourceAccepted program
  functions : Functions.Source.Program.CompileAccepted program.toFunctions

noncomputable def compileChecked? (program : Objects.Program) :
    Option Assembly.Program := do
  let lower ← program.toExpressions?
  Structured.Preservation.ProcedurePreservation.compileChecked?
    lower.toStructured

noncomputable def compileLiveNoInternalCallChecked?
    (program : Objects.Program) : Option Assembly.Program :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?
    program.toFunctions

noncomputable def compileCheckedWithConservativeSpillSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Objects.Program) : Option Assembly.Program :=
  Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?
    range program.toFunctions

noncomputable def compileCheckedWithAdaptiveSpillSourceOwned?
    (range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange)
    (program : Objects.Program) : Option Assembly.Program :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
    range program.toFunctions

noncomputable def compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
    (maxWords : Nat) (program : Objects.Program) :
    Option (Locals.SourceLowering.StateRel.SpillScratch.ScratchRange ×
      Assembly.Program) :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
    maxWords program.toFunctions

noncomputable def compileCheckedWithCallAwareSpillPlannedPrealloc?
    (maxWords : Nat) (program : Objects.Program) :
    Option (Functions.CallAwareSpill.ScratchRange ×
      Functions.CallAwareSpill.Plan × Expressions.Program × Assembly.Program) :=
  Functions.CallAwareSpill.compileCheckedPlannedPrealloc? maxWords
    program.toFunctions

noncomputable def compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?
    (maxWords : Nat) (program : Objects.Program) :
    Option (Functions.CallAwareSpill.ScratchRange ×
      Functions.CallAwareSpill.Plan × Expressions.Program × Assembly.Program) :=
  Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?
    maxWords program.toFunctions

noncomputable def compileCheckedWithScratchFrameSpill?
    (maxFrameWords : Nat) (program : Objects.Program) :
    Option (Expressions.Program × Assembly.Program) :=
  Functions.ScratchFrameSpill.compileChecked? maxFrameWords
    program.toFunctions

noncomputable def compileCheckedAssemblyWithScratchFrameSpill?
    (maxFrameWords : Nat) (program : Objects.Program) :
    Option Assembly.Program := do
  let (_exprProgram, asm) ←
    compileCheckedWithScratchFrameSpill? maxFrameWords program
  some asm

theorem compileChecked?_eq_some {program : Objects.Program}
    {asm : Assembly.Program}
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

theorem compileChecked?_noCallCreate {program : Objects.Program}
    {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile : compileChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hLowerCompile⟩
  have hLowerNo :
      lower.usesCallCreate = false := by
    have hLocalsNo :
        program.toFunctions.toLocals.usesCallCreate = false :=
      Functions.CompilerFacts.Program.toLocals_noCallCreate
        program.toFunctions hProgram
    exact
      Locals.CompilerFacts.Program.toExpressions?_noCallCreate
        program.toFunctions.toLocals hLocalsNo
        (by
          simpa [Program.toExpressions?,
            Functions.Inline.Program.toExpressions?,
            Functions.Program.toExpressions?] using hLower)
  exact
    Structured.Preservation.ProcedurePreservation.compileChecked?_noCallCreate
      (program := lower.toStructured) (asm := asm)
      (by
        simpa [Expressions.CompilerFacts.Program.toStructured_usesCallCreate]
          using hLowerNo)
      hLowerCompile

theorem compileLiveNoInternalCallChecked?_noCallCreate
    {program : Objects.Program} {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile : compileLiveNoInternalCallChecked? program = some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
    hProgram hCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm) :
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?
        range program.toFunctions =
      some asm := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using hCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    {asm : Assembly.Program}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hCompile :
      Expressions.Program.compileChecked?
          (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
            plan) =
        some asm) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some asm := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?
      hOwnedCheck hPlan hCompile

theorem compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_compileBlockOpen?_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeScopedSpill?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithConservativeSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithConservativeSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_of_scopedFallback_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithConservativeSpillSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_noCallCreate
    (compileCheckedWithConservativeSpillSourceOwned?_eq_some hCompile)

theorem compileCheckedWithAdaptiveSpillSourceOwned?_eq_some
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm) :
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?
        range program.toFunctions =
      some asm := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using hCompile

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    {asm : Assembly.Program}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hCompile :
      Expressions.Program.compileChecked?
          (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
            plan) =
        some asm) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some asm := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?
      hOwnedCheck hPlan hCompile

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_compileBlockOpen?_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program}
    {plan : Locals.SourceLowering.StateRel.SpillScratch.SpillPlan}
    (hOwnedCheck :
      Functions.SourceLowering.SourceToLocals.Block.sourceOwned? []
          program.toFunctions.body =
        true)
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?
          range [] [] [] program.toFunctions.toLocals.body =
        some plan)
    (hBounds :
      Structured.Preservation.ProcedurePreservation.CompilationBounds
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).toStructured) :
    compileCheckedWithAdaptiveSpillSourceOwned? range program =
      some
        (Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram
          plan).compile := by
  simpa [compileCheckedWithAdaptiveSpillSourceOwned?] using
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_of_adaptiveFallback_bounds
      hOwnedCheck hPlan hBounds

theorem compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_noCallCreate
    (compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile)

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
    {maxWords : Nat} {program : Objects.Program}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm)) :
    Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
        maxWords program.toFunctions =
      some (range, asm) := by
  simpa [compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?]
    using hCompile

theorem compileCheckedWithCallAwareSpillPlannedPrealloc?_eq_some
    {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithCallAwareSpillPlannedPrealloc? maxWords program =
        some (range, plan, exprProgram, asm)) :
    Functions.CallAwareSpill.compileCheckedPlannedPrealloc? maxWords
        program.toFunctions =
      some (range, plan, exprProgram, asm) := by
  simpa [compileCheckedWithCallAwareSpillPlannedPrealloc?] using hCompile

theorem compileCheckedWithCallAwareSpillPlannedPrealloc?_noCallCreate
    {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithCallAwareSpillPlannedPrealloc? maxWords program =
        some (range, plan, exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.CallAwareSpill.compileCheckedPlannedPrealloc?_noCallCreate
    (compileCheckedWithCallAwareSpillPlannedPrealloc?_eq_some hCompile)

theorem compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_eq_some
    {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc? maxWords
          program =
        some (range, plan, exprProgram, asm)) :
    Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?
        maxWords program.toFunctions =
      some (range, plan, exprProgram, asm) := by
  simpa [compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?]
    using hCompile

theorem compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_sourceAccepted
    {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc? maxWords
          program =
        some (range, plan, exprProgram, asm)) :
    program.toFunctions.SourceAccepted :=
  Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?_sourceAccepted
    (compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_eq_some
      hCompile)

theorem compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_noCallCreate
    {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile :
      compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc? maxWords
          program =
        some (range, plan, exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?_noCallCreate
    hProgram
    (compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_eq_some
      hCompile)

theorem compileCheckedWithScratchFrameSpill?_eq_some
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    Functions.ScratchFrameSpill.compileExpressionsProgram? maxFrameWords
        program.toFunctions =
      some exprProgram ∧
      Expressions.Program.compileChecked? exprProgram = some asm := by
  exact
    Functions.ScratchFrameSpill.compileChecked?_eq_some
      (by
        simpa [compileCheckedWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithScratchFrameSpill?_bounded_passes_state_eq
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    ∃ functionSlots stateAfterSignatures probeProcs
        stateAfterFunctions mainProbe procs stateAfterFunctionsFinal main,
      Functions.ScratchFrameSpill.allocateFunctionSignatures
          program.toFunctions.functions
          ({ env := [], nextSlot := 0 } :
            Functions.ScratchFrameSpill.CompileState) =
        (functionSlots, stateAfterSignatures) ∧
      Functions.ScratchFrameSpill.FunSlotListBounded
        functionSlots maxFrameWords ∧
      Functions.ScratchFrameSpill.StateSlotsBounded
        stateAfterSignatures ∧
      Functions.ScratchFrameSpill.compileFunctions?
          { functions := functionSlots, frameWords := 0 }
          stateAfterSignatures program.toFunctions.functions =
            some (probeProcs, stateAfterFunctions) ∧
      Functions.ScratchFrameSpill.StateSlotsBounded
        stateAfterFunctions ∧
      Functions.ScratchFrameSpill.compileMain?
          { functions := functionSlots, frameWords := 0 }
          0 { env := [], nextSlot := stateAfterFunctions.nextSlot }
          program.toFunctions.body = some mainProbe ∧
      Functions.ScratchFrameSpill.StateSlotsBounded
        mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      Functions.ScratchFrameSpill.compileFunctions?
          { functions := functionSlots,
            frameWords := mainProbe.state.nextSlot }
          stateAfterSignatures program.toFunctions.functions =
            some (procs, stateAfterFunctionsFinal) ∧
      stateAfterFunctionsFinal = stateAfterFunctions ∧
      Functions.ScratchFrameSpill.StateSlotsBounded
        stateAfterFunctionsFinal ∧
      Functions.ScratchFrameSpill.compileMain?
          { functions := functionSlots,
            frameWords := mainProbe.state.nextSlot }
          mainProbe.state.nextSlot
          { env := [], nextSlot := stateAfterFunctions.nextSlot }
          program.toFunctions.body = some main ∧
      main.state = mainProbe.state ∧
      Functions.ScratchFrameSpill.StateSlotsBounded main.state ∧
      exprProgram = { procs := procs, body := main.block } := by
  exact
    Functions.ScratchFrameSpill.compileExpressionsProgram?_bounded_passes_state_eq
      (compileCheckedWithScratchFrameSpill?_eq_some hCompile).1

theorem compileCheckedWithScratchFrameSpill?_nodup_passes
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    ∃ functionSlots stateAfterSignatures probeProcs
        stateAfterFunctions mainProbe procs stateAfterFunctionsFinal main,
      Functions.ScratchFrameSpill.allocateFunctionSignatures
          program.toFunctions.functions
          ({ env := [], nextSlot := 0 } :
            Functions.ScratchFrameSpill.CompileState) =
        (functionSlots, stateAfterSignatures) ∧
      Functions.ScratchFrameSpill.FunSlotListNodup functionSlots ∧
      Functions.ScratchFrameSpill.StateSlotsNodup stateAfterSignatures ∧
      Functions.ScratchFrameSpill.compileFunctions?
          { functions := functionSlots, frameWords := 0 }
          stateAfterSignatures program.toFunctions.functions =
            some (probeProcs, stateAfterFunctions) ∧
      Functions.ScratchFrameSpill.StateSlotsNodup stateAfterFunctions ∧
      Functions.ScratchFrameSpill.compileMain?
          { functions := functionSlots, frameWords := 0 }
          0 { env := [], nextSlot := stateAfterFunctions.nextSlot }
          program.toFunctions.body = some mainProbe ∧
      Functions.ScratchFrameSpill.StateSlotsNodup mainProbe.state ∧
      Functions.ScratchFrameSpill.compileFunctions?
          { functions := functionSlots,
            frameWords := mainProbe.state.nextSlot }
          stateAfterSignatures program.toFunctions.functions =
            some (procs, stateAfterFunctionsFinal) ∧
      Functions.ScratchFrameSpill.StateSlotsNodup
        stateAfterFunctionsFinal ∧
      Functions.ScratchFrameSpill.compileMain?
          { functions := functionSlots,
            frameWords := mainProbe.state.nextSlot }
          mainProbe.state.nextSlot
          { env := [], nextSlot := stateAfterFunctions.nextSlot }
          program.toFunctions.body = some main ∧
      Functions.ScratchFrameSpill.StateSlotsNodup main.state ∧
      exprProgram = { procs := procs, body := main.block } := by
  exact
    Functions.ScratchFrameSpill.compileExpressionsProgram?_nodup_passes
      (compileCheckedWithScratchFrameSpill?_eq_some hCompile).1

theorem compileCheckedWithScratchFrameSpill?_noCallCreate
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hExprNo : exprProgram.usesCallCreate = false)
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false := by
  exact
    Functions.ScratchFrameSpill.compileChecked?_noCallCreate hExprNo
      (by
        simpa [compileCheckedWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithScratchFrameSpill?_noCallCreate_of_source
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.ScratchFrameSpill.compileChecked?_noCallCreate_of_source
    hProgram
    (by
      simpa [compileCheckedWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithScratchFrameSpill?_lookup_of_find?
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {name : Name} {fn : Functions.FunDef}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hFind :
      Functions.FunList.find? name program.toFunctions.functions =
        some fn) :
    ∃ proc,
      Expressions.ProcList.lookup? name exprProgram.procs = some proc ∧
        proc.name = fn.name ∧ proc.argc = 1 ∧
          proc.retc = fn.returns.length :=
  Functions.ScratchFrameSpill.compileChecked?_lookup_of_find?
    (by
      simpa [compileCheckedWithScratchFrameSpill?] using hCompile)
    hFind

theorem compileCheckedWithScratchFrameSpill?_program_run_main_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState} {runState : Expressions.RunState}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicStmtListSafe
        program.toFunctions.body.stmts)
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final,
          Expressions.Block.run exprProgram
              ((blockFuel + 2 * rest.length + 2) + prelude.length)
              exprProgram.body { runState with evm := initial } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  rcases compileCheckedWithScratchFrameSpill?_bounded_passes_state_eq
      hCompile with
    ⟨functionSlots, stateAfterSignatures, probeProcs,
      stateAfterFunctions, mainProbe, procs, stateAfterFunctionsFinal, main,
      _hSignatures, _hFunctionSlotsBound, _hSignatureStateBound,
      _hProbeFunctions, _hProbeFunctionsBound, _hMainProbe,
      _hMainProbeBound, hMainProbeBound, _hFinalFunctions,
      _hFinalFunctionsState, _hFinalFunctionsBound, hMain,
      hMainState, _hMainBound, hExprProgram⟩
  cases hSplit :
      Functions.ScratchFrameSpill.splitPrelude
        program.toFunctions.body.stmts with
  | mk prelude rest =>
      have hFrameWords :
          main.state.nextSlot ≤ mainProbe.state.nextSlot := by
        simp [hMainState]
      have hFunctionRun :
          Functions.Source.Program.run
              Locals.Source.PrimitiveSemantics.structured
              sourceFuel program.toFunctions initial =
            .ok (Functions.Source.Outcome.regular publicSource') := by
        cases program with
        | mk root =>
            cases root with
            | mk name code data objects =>
                simpa [Source.Program.run, Source.Object.run,
                  Objects.Program.toFunctions, Objects.Object.toFunctions]
                  using hRun
      have hFunctionRunState :
          Functions.Source.Program.runState
              Locals.Source.PrimitiveSemantics.structured
              sourceFuel program.toFunctions
              (Functions.Source.Program.initialState
                initial.toSharedState) =
            .ok (Functions.Source.Outcome.regular publicSource') := by
        simpa [Functions.Source.Program.run] using hFunctionRun
      rcases
          Functions.ScratchFrameSpill.FrameMemory.run_compileMain?_atomic_withPrelude_empty_frame_of_program_runState_regular_privateScratch_cont
            hSpec hWordBytes
            (ctx :=
              { functions := functionSlots,
                frameWords := mainProbe.state.nextSlot })
            (startSlot := stateAfterFunctions.nextSlot)
            (words := mainProbe.state.nextSlot)
            (stmts := program.toFunctions.body.stmts)
            (rest := rest)
            (prelude := prelude)
            (mainPlan := main)
            (sourceProgram := program.toFunctions)
            (compiledProgram := exprProgram)
            (source :=
              Functions.Source.Program.initialState initial.toSharedState)
            (publicSource' := publicSource')
            (sourceFuel := sourceFuel)
            (blockFuel := blockFuel)
            (runState := runState)
            (evmState := initial)
            (hBody := by
              cases program.toFunctions.body
              rfl)
            (hSplit := hSplit)
            (hCompile := by
              cases program with
              | mk root =>
                  cases root with
                  | mk name code data objects =>
                      cases code with
                      | mk functions body =>
                          cases body with
                          | mk bodyStmts =>
                              simpa [Objects.Program.toFunctions,
                                Objects.Object.toFunctions] using hMain)
            (hSafe := hSafe)
            (hRun := hFunctionRunState)
            (hFrameWords := hFrameWords)
            (hSharedStart := rfl)
        with
      ⟨innerSource, innerCtx, hPublic, sourceAfterPrelude,
        sourceCtxAfterPrelude, preludeEvm, restFuel, hPreludeShared,
        hPreludeStack, hRestRun, hCont⟩
      have hExprBody : exprProgram.body = main.block := by
        simp [hExprProgram]
      refine
        ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
          sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
          hMainState, hMainProbeBound, hExprBody, rfl, hPublic,
          hPreludeShared, hPreludeStack, hRestRun, ?_⟩
      intro initState base hInitRun hInitStack hReady hInitInvariant
      rcases hCont hInitRun hInitStack hReady hInitInvariant with
        ⟨final, hMainRun, hStack, hReadyFinal, hObservable, hRel⟩
      have hRunBody :
          Expressions.Block.run exprProgram
              ((blockFuel + 2 * rest.length + 2) + prelude.length)
              exprProgram.body { runState with evm := initial } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) := by
        simpa [hExprBody] using hMainRun
      exact ⟨final, hRunBody, hStack, hReadyFinal, hObservable, hRel⟩

theorem compileCheckedWithScratchFrameSpill?_program_run_main_atomicOrBlock_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState} {runState : Expressions.RunState}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockStmtListSafe
        program.toFunctions.body.stmts)
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final,
          Expressions.Block.run exprProgram
              ((blockFuel +
                  Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockStmtListFuel
                    rest + 2) + prelude.length)
              exprProgram.body { runState with evm := initial } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  rcases compileCheckedWithScratchFrameSpill?_bounded_passes_state_eq
      hCompile with
    ⟨functionSlots, stateAfterSignatures, probeProcs,
      stateAfterFunctions, mainProbe, procs, stateAfterFunctionsFinal, main,
      _hSignatures, _hFunctionSlotsBound, _hSignatureStateBound,
      _hProbeFunctions, _hProbeFunctionsBound, _hMainProbe,
      _hMainProbeBound, hMainProbeBound, _hFinalFunctions,
      _hFinalFunctionsState, _hFinalFunctionsBound, hMain,
      hMainState, _hMainBound, hExprProgram⟩
  cases hSplit :
      Functions.ScratchFrameSpill.splitPrelude
        program.toFunctions.body.stmts with
  | mk prelude rest =>
      have hFrameWords :
          main.state.nextSlot ≤ mainProbe.state.nextSlot := by
        simp [hMainState]
      have hFunctionRun :
          Functions.Source.Program.run
              Locals.Source.PrimitiveSemantics.structured
              sourceFuel program.toFunctions initial =
            .ok (Functions.Source.Outcome.regular publicSource') := by
        cases program with
        | mk root =>
            cases root with
            | mk name code data objects =>
                simpa [Source.Program.run, Source.Object.run,
                  Objects.Program.toFunctions, Objects.Object.toFunctions]
                  using hRun
      have hFunctionRunState :
          Functions.Source.Program.runState
              Locals.Source.PrimitiveSemantics.structured
              sourceFuel program.toFunctions
              (Functions.Source.Program.initialState
                initial.toSharedState) =
            .ok (Functions.Source.Outcome.regular publicSource') := by
        simpa [Functions.Source.Program.run] using hFunctionRun
      have hScopedRun :
          EvmCompiler.Functions.Source.Block.runScoped
              Locals.Source.PrimitiveSemantics.structured
              program.toFunctions EvmCompiler.Functions.Source.Ctx.initial
              program.toFunctions.body sourceFuel
              (Functions.Source.Program.initialState initial.toSharedState) =
            .ok (EvmCompiler.Functions.Source.Outcome.regular
              publicSource') := by
        simpa [EvmCompiler.Functions.Source.Program.runState]
          using hFunctionRunState
      rcases
          EvmCompiler.Functions.Source.Block.runScoped_regular_eq_restrict
            hScopedRun with
        ⟨innerSource, innerCtx, hOpen, hPublic⟩
      rcases
          Functions.ScratchFrameSpill.FrameMemory.run_compileMain?_atomicOrBlock_withPrelude_block_frameStore_of_full_source_run_open_regular_privateScratch
            hSpec hWordBytes
            (ctx :=
              { functions := functionSlots,
                frameWords := mainProbe.state.nextSlot })
            (compileState :=
              ({ env := [], nextSlot := stateAfterFunctions.nextSlot } :
                Functions.ScratchFrameSpill.CompileState))
            (stmts := program.toFunctions.body.stmts)
            (rest := rest)
            (prelude := prelude)
            (mainPlan := main)
            (sourceProgram := program.toFunctions)
            (compiledProgram := exprProgram)
            (source :=
              Functions.Source.Program.initialState initial.toSharedState)
            (source' := innerSource)
            (sourceCtx := EvmCompiler.Functions.Source.Ctx.initial)
            (sourceCtx' := innerCtx)
            (sourceFuel := sourceFuel)
            (blockFuel := blockFuel)
            (runState := runState)
            (evmState := initial)
            (words := mainProbe.state.nextSlot)
            hSplit
            (by
              cases program with
              | mk root =>
                  cases root with
                  | mk name code data objects =>
                      cases code with
                      | mk functions body =>
                          cases body with
                          | mk bodyStmts =>
                              simpa [Objects.Program.toFunctions,
                                Objects.Object.toFunctions] using hMain)
            hScoped hSafe
            (by
              cases hBody : program.toFunctions.body with
              | mk bodyStmts =>
                  rw [hBody] at hOpen
                  simpa [hBody] using hOpen)
            (Functions.ScratchFrameSpill.FrameMemory.StateSlotsBounded.empty
              stateAfterFunctions.nextSlot)
            (Functions.ScratchFrameSpill.FrameMemory.StateSlotsNodup.empty
              stateAfterFunctions.nextSlot)
            Functions.ScratchFrameSpill.FrameMemory.EnvNamesInScope.empty
            hFrameWords rfl with
        ⟨sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
          hPreludeShared, hPreludeStack, _hCtxAfter, hRestRun, hCont⟩
      have hExprBody : exprProgram.body = main.block := by
        simp [hExprProgram]
      refine
        ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
          sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
          hMainState, hMainProbeBound, hExprBody, rfl, hPublic,
          hPreludeShared, hPreludeStack, hRestRun, ?_⟩
      intro initState base hInitRun hInitStack hReady hInitInvariant
      rcases
          hCont hInitRun hInitStack hReady hInitInvariant
            Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel.empty with
        ⟨final, hMainRun, hStack, hReadyFinal, hObservable, hRel⟩
      have hRunBody :
          Expressions.Block.run exprProgram
              ((blockFuel +
                  Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockStmtListFuel
                    rest + 2) + prelude.length)
              exprProgram.body { runState with evm := initial } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) := by
        simpa [hExprBody] using hMainRun
      have hSharedPublic :
          publicSource'.shared = innerSource.shared := by
        rw [hPublic]
        rfl
      exact
        ⟨final, hRunBody, hStack, hReadyFinal,
          by simpa [hSharedPublic] using hObservable, hRel⟩

theorem compileCheckedWithScratchFrameSpill?_program_run_main_atomicOrBlockFor_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState} {runState : Expressions.RunState}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockForStmtListSafe
        program.toFunctions.body.stmts)
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final,
          Expressions.Block.run exprProgram
              ((blockFuel +
                  Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockForStmtListFuel
                    sourceFuel rest + 2) + prelude.length)
              exprProgram.body { runState with evm := initial } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  rcases compileCheckedWithScratchFrameSpill?_bounded_passes_state_eq
      hCompile with
    ⟨functionSlots, stateAfterSignatures, probeProcs,
      stateAfterFunctions, mainProbe, procs, stateAfterFunctionsFinal, main,
      _hSignatures, _hFunctionSlotsBound, _hSignatureStateBound,
      _hProbeFunctions, _hProbeFunctionsBound, _hMainProbe,
      _hMainProbeBound, hMainProbeBound, _hFinalFunctions,
      _hFinalFunctionsState, _hFinalFunctionsBound, hMain,
      hMainState, _hMainBound, hExprProgram⟩
  cases hSplit :
      Functions.ScratchFrameSpill.splitPrelude
        program.toFunctions.body.stmts with
  | mk prelude rest =>
      have hFrameWords :
          main.state.nextSlot ≤ mainProbe.state.nextSlot := by
        simp [hMainState]
      have hFunctionRun :
          Functions.Source.Program.run
              Locals.Source.PrimitiveSemantics.structured
              sourceFuel program.toFunctions initial =
            .ok (Functions.Source.Outcome.regular publicSource') := by
        cases program with
        | mk root =>
            cases root with
            | mk name code data objects =>
                simpa [Source.Program.run, Source.Object.run,
                  Objects.Program.toFunctions, Objects.Object.toFunctions]
                  using hRun
      have hFunctionRunState :
          Functions.Source.Program.runState
              Locals.Source.PrimitiveSemantics.structured
              sourceFuel program.toFunctions
              (Functions.Source.Program.initialState
                initial.toSharedState) =
            .ok (Functions.Source.Outcome.regular publicSource') := by
        simpa [Functions.Source.Program.run] using hFunctionRun
      have hScopedRun :
          EvmCompiler.Functions.Source.Block.runScoped
              Locals.Source.PrimitiveSemantics.structured
              program.toFunctions EvmCompiler.Functions.Source.Ctx.initial
              program.toFunctions.body sourceFuel
              (Functions.Source.Program.initialState initial.toSharedState) =
            .ok (EvmCompiler.Functions.Source.Outcome.regular
              publicSource') := by
        simpa [EvmCompiler.Functions.Source.Program.runState]
          using hFunctionRunState
      rcases
          EvmCompiler.Functions.Source.Block.runScoped_regular_eq_restrict
            hScopedRun with
        ⟨innerSource, innerCtx, hOpen, hPublic⟩
      rcases
          Functions.ScratchFrameSpill.FrameMemory.run_compileMain?_atomicOrBlockFor_withPrelude_block_frameStore_of_full_source_run_open_regular_privateScratch
            hSpec hWordBytes
            (ctx :=
              { functions := functionSlots,
                frameWords := mainProbe.state.nextSlot })
            (compileState :=
              ({ env := [], nextSlot := stateAfterFunctions.nextSlot } :
                Functions.ScratchFrameSpill.CompileState))
            (stmts := program.toFunctions.body.stmts)
            (rest := rest)
            (prelude := prelude)
            (mainPlan := main)
            (sourceProgram := program.toFunctions)
            (compiledProgram := exprProgram)
            (source :=
              Functions.Source.Program.initialState initial.toSharedState)
            (source' := innerSource)
            (sourceCtx := EvmCompiler.Functions.Source.Ctx.initial)
            (sourceCtx' := innerCtx)
            (sourceFuel := sourceFuel)
            (blockFuel := blockFuel)
            (runState := runState)
            (evmState := initial)
            (words := mainProbe.state.nextSlot)
            hSplit
            (by
              cases program with
              | mk root =>
                  cases root with
                  | mk name code data objects =>
                      cases code with
                      | mk functions body =>
                          cases body with
                          | mk bodyStmts =>
                              simpa [Objects.Program.toFunctions,
                                Objects.Object.toFunctions] using hMain)
            hScoped hSafe
            (by
              cases hBody : program.toFunctions.body with
              | mk bodyStmts =>
                  rw [hBody] at hOpen
                  simpa [hBody] using hOpen)
            (Functions.ScratchFrameSpill.FrameMemory.StateSlotsBounded.empty
              stateAfterFunctions.nextSlot)
            (Functions.ScratchFrameSpill.FrameMemory.StateSlotsNodup.empty
              stateAfterFunctions.nextSlot)
            Functions.ScratchFrameSpill.FrameMemory.EnvNamesInScope.empty
            hFrameWords rfl with
        ⟨sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
          hPreludeShared, hPreludeStack, _hCtxAfter, hRestRun, hCont⟩
      have hExprBody : exprProgram.body = main.block := by
        simp [hExprProgram]
      refine
        ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
          sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
          hMainState, hMainProbeBound, hExprBody, rfl, hPublic,
          hPreludeShared, hPreludeStack, hRestRun, ?_⟩
      intro initState base hInitRun hInitStack hReady hInitInvariant
      rcases
          hCont hInitRun hInitStack hReady hInitInvariant
            Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel.empty with
        ⟨final, hMainRun, hStack, hReadyFinal, hObservable, hRel⟩
      have hRunBody :
          Expressions.Block.run exprProgram
              ((blockFuel +
                  Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockForStmtListFuel
                    sourceFuel rest + 2) + prelude.length)
              exprProgram.body { runState with evm := initial } =
            .ok (Expressions.Outcome.regular
              ({ runState with evm := final })) := by
        simpa [hExprBody] using hMainRun
      have hSharedPublic :
          publicSource'.shared = innerSource.shared := by
        rw [hPublic]
        rfl
      exact
        ⟨final, hRunBody, hStack, hReadyFinal,
          by simpa [hSharedPublic] using hObservable, hRel⟩

theorem compileCheckedWithScratchFrameSpill?_program_run_assembly_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  have hAsm :
      Expressions.Program.compileChecked? exprProgram = some asm :=
    (compileCheckedWithScratchFrameSpill?_eq_some hCompile).2
  rcases
      compileCheckedWithScratchFrameSpill?_program_run_main_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (exprProgram := exprProgram)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        (runState := Structured.Program.initialState initial)
        hCompile hSafe hRun with
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro initState base hInitRun hInitStack hReady hInitInvariant
  rcases hCont hInitRun hInitStack hReady hInitInvariant with
    ⟨final, hExprBlockRun, hStack, hReadyFinal, hObservable, hRel⟩
  let exprFuel := (blockFuel + 2 * rest.length + 2) + prelude.length
  have hExprRun :
      Expressions.Program.run exprFuel exprProgram initial =
        .ok (Expressions.Outcome.regular
          ({ Structured.Program.initialState initial with evm := final })) := by
    simpa [exprFuel, Expressions.Program.run,
      Structured.Program.initialState, Structured.RunState.initial] using
      hExprBlockRun
  rcases
      Expressions.Program.compile_preserves_of_compileChecked_endPc
        hAsm hInitialPc hExprRun with
    ⟨targetFuel, targetOutcome, hTargetRun, hWhole, hEndPc⟩
  exact
    ⟨final, targetFuel, targetOutcome, hTargetRun, hWhole, hEndPc,
      hStack, hReadyFinal, hObservable, hRel⟩

theorem compileCheckedWithScratchFrameSpill?_program_run_assembly_atomicOrBlock_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  have hAsm :
      Expressions.Program.compileChecked? exprProgram = some asm :=
    (compileCheckedWithScratchFrameSpill?_eq_some hCompile).2
  rcases
      compileCheckedWithScratchFrameSpill?_program_run_main_atomicOrBlock_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (exprProgram := exprProgram)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        (runState := Structured.Program.initialState initial)
        hCompile hScoped hSafe hRun with
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro initState base hInitRun hInitStack hReady hInitInvariant
  rcases hCont hInitRun hInitStack hReady hInitInvariant with
    ⟨final, hExprBlockRun, hStack, hReadyFinal, hObservable, hRel⟩
  let exprFuel :=
    (blockFuel +
        Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockStmtListFuel
          rest + 2) + prelude.length
  have hExprRun :
      Expressions.Program.run exprFuel exprProgram initial =
        .ok (Expressions.Outcome.regular
          ({ Structured.Program.initialState initial with evm := final })) := by
    simpa [exprFuel, Expressions.Program.run,
      Structured.Program.initialState, Structured.RunState.initial] using
      hExprBlockRun
  rcases
      Expressions.Program.compile_preserves_of_compileChecked_endPc
        hAsm hInitialPc hExprRun with
    ⟨targetFuel, targetOutcome, hTargetRun, hWhole, hEndPc⟩
  exact
    ⟨final, targetFuel, targetOutcome, hTargetRun, hWhole, hEndPc,
      hStack, hReadyFinal, hObservable, hRel⟩

theorem compileCheckedWithScratchFrameSpill?_program_run_assembly_atomicOrBlockFor_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm))
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockForStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  have hAsm :
      Expressions.Program.compileChecked? exprProgram = some asm :=
    (compileCheckedWithScratchFrameSpill?_eq_some hCompile).2
  rcases
      compileCheckedWithScratchFrameSpill?_program_run_main_atomicOrBlockFor_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (exprProgram := exprProgram)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        (runState := Structured.Program.initialState initial)
        hCompile hScoped hSafe hRun with
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro initState base hInitRun hInitStack hReady hInitInvariant
  rcases hCont hInitRun hInitStack hReady hInitInvariant with
    ⟨final, hExprBlockRun, hStack, hReadyFinal, hObservable, hRel⟩
  let exprFuel :=
    (blockFuel +
        Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockForStmtListFuel
          sourceFuel rest + 2) + prelude.length
  have hExprRun :
      Expressions.Program.run exprFuel exprProgram initial =
        .ok (Expressions.Outcome.regular
          ({ Structured.Program.initialState initial with evm := final })) := by
    simpa [exprFuel, Expressions.Program.run,
      Structured.Program.initialState, Structured.RunState.initial] using
      hExprBlockRun
  rcases
      Expressions.Program.compile_preserves_of_compileChecked_endPc
        hAsm hInitialPc hExprRun with
    ⟨targetFuel, targetOutcome, hTargetRun, hWhole, hEndPc⟩
  exact
    ⟨final, targetFuel, targetOutcome, hTargetRun, hWhole, hEndPc,
      hStack, hReadyFinal, hObservable, hRel⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_checked_eq_some
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    ∃ exprProgram,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) := by
  unfold compileCheckedAssemblyWithScratchFrameSpill? at hCompile
  cases hScratch :
      compileCheckedWithScratchFrameSpill? maxFrameWords program with
  | none =>
      simp [hScratch] at hCompile
  | some result =>
      rcases result with ⟨exprProgram, asm'⟩
      simp [hScratch] at hCompile
      cases hCompile
      exact ⟨exprProgram, by simp⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  rcases compileCheckedAssemblyWithScratchFrameSpill?_checked_eq_some
      hCompile with
    ⟨exprProgram, hChecked⟩
  rcases
      compileCheckedWithScratchFrameSpill?_program_run_assembly_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (exprProgram := exprProgram)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        hChecked hSafe hInitialPc hRun with
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  exact
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlock_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  rcases compileCheckedAssemblyWithScratchFrameSpill?_checked_eq_some
      hCompile with
    ⟨exprProgram, hChecked⟩
  rcases
      compileCheckedWithScratchFrameSpill?_program_run_assembly_atomicOrBlock_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (exprProgram := exprProgram)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        hChecked hScoped hSafe hInitialPc hRun with
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  exact
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlockFor_privateScratch_cont
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockForStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (∀ {initState : EVMState} {base : Word},
        Structured.Code.run
            (Functions.ScratchFrameSpill.frameInitCode
              mainProbe.state.nextSlot) preludeEvm =
          .ok initState →
        initState.stack = base :: preludeEvm.stack →
        Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
          initState.toMachineState
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range base
            mainProbe.state.nextSlot).words →
        Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
          sourceAfterPrelude.shared initState.toSharedState →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack = base :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range base
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState base) := by
  rcases compileCheckedAssemblyWithScratchFrameSpill?_checked_eq_some
      hCompile with
    ⟨exprProgram, hChecked⟩
  rcases
      compileCheckedWithScratchFrameSpill?_program_run_assembly_atomicOrBlockFor_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (exprProgram := exprProgram)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        hChecked hScoped hSafe hInitialPc hRun with
    ⟨mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  exact
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_of_frameInit_ready_check
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
          (Functions.ScratchFrameSpill.FrameMemory.frameInitMachine
            mainProbe.state.nextSlot preludeEvm.toMachineState)
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).words = true →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack =
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1 :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1) := by
  rcases
      compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        hCompile hSafe hInitialPc hRun with
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro hFrameInitReady
  rcases
      Functions.ScratchFrameSpill.FrameMemory.run_frameInitCode
        preludeEvm mainProbe.state.nextSlot with
    ⟨initState, hInitRun, hInitStack, hInitMachine, hInitInvariant,
      _hInitObservable⟩
  have hReady :
      Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
        initState.toMachineState
        (Functions.ScratchFrameSpill.FrameMemory.range
          (preludeEvm.toMachineState.mload
            Functions.ScratchFrameSpill.freePtrWord).1
          mainProbe.state.nextSlot).base
        (Functions.ScratchFrameSpill.FrameMemory.range
          (preludeEvm.toMachineState.mload
            Functions.ScratchFrameSpill.freePtrWord).1
          mainProbe.state.nextSlot).words := by
    rw [hInitMachine]
    exact
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_sound
        hFrameInitReady
  have hInitInvariantSource :
      Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
        sourceAfterPrelude.shared initState.toSharedState := by
    simpa [← hPreludeShared] using hInitInvariant
  exact
    hCont hInitRun hInitStack hReady hInitInvariantSource

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlock_privateScratch_of_frameInit_ready_check
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
          (Functions.ScratchFrameSpill.FrameMemory.frameInitMachine
            mainProbe.state.nextSlot preludeEvm.toMachineState)
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).words = true →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack =
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1 :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1) := by
  rcases
      compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlock_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        hCompile hScoped hSafe hInitialPc hRun with
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro hFrameInitReady
  rcases
      Functions.ScratchFrameSpill.FrameMemory.run_frameInitCode
        preludeEvm mainProbe.state.nextSlot with
    ⟨initState, hInitRun, hInitStack, hInitMachine, hInitInvariant,
      _hInitObservable⟩
  have hReady :
      Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
        initState.toMachineState
        (Functions.ScratchFrameSpill.FrameMemory.range
          (preludeEvm.toMachineState.mload
            Functions.ScratchFrameSpill.freePtrWord).1
          mainProbe.state.nextSlot).base
        (Functions.ScratchFrameSpill.FrameMemory.range
          (preludeEvm.toMachineState.mload
            Functions.ScratchFrameSpill.freePtrWord).1
          mainProbe.state.nextSlot).words := by
    rw [hInitMachine]
    exact
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_sound
        hFrameInitReady
  have hInitInvariantSource :
      Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
        sourceAfterPrelude.shared initState.toSharedState := by
    simpa [← hPreludeShared] using hInitInvariant
  exact
    hCont hInitRun hInitStack hReady hInitInvariantSource

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlockFor_privateScratch_of_frameInit_ready_check
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hSafe :
      Functions.ScratchFrameSpill.FrameMemory.AtomicOrBlockForStmtListSafe
        program.toFunctions.body.stmts)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
          (Functions.ScratchFrameSpill.FrameMemory.frameInitMachine
            mainProbe.state.nextSlot preludeEvm.toMachineState)
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).words = true →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack =
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1 :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1) := by
  rcases
      compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlockFor_privateScratch_cont
        hSpec hWordBytes
        (maxFrameWords := maxFrameWords)
        (program := program)
        (asm := asm)
        (publicSource' := publicSource')
        (sourceFuel := sourceFuel)
        (blockFuel := blockFuel)
        (initial := initial)
        hCompile hScoped hSafe hInitialPc hRun with
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, hCont⟩
  refine
    ⟨exprProgram, mainProbe, main, prelude, rest, innerSource, innerCtx,
      sourceAfterPrelude, sourceCtxAfterPrelude, preludeEvm, restFuel,
      hChecked, hMainState, hFrameBound, hExprBody, hSplit, hPublic,
      hPreludeShared, hPreludeStack, hRestRun, ?_⟩
  intro hFrameInitReady
  rcases
      Functions.ScratchFrameSpill.FrameMemory.run_frameInitCode
        preludeEvm mainProbe.state.nextSlot with
    ⟨initState, hInitRun, hInitStack, hInitMachine, hInitInvariant,
      _hInitObservable⟩
  have hReady :
      Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
        initState.toMachineState
        (Functions.ScratchFrameSpill.FrameMemory.range
          (preludeEvm.toMachineState.mload
            Functions.ScratchFrameSpill.freePtrWord).1
          mainProbe.state.nextSlot).base
        (Functions.ScratchFrameSpill.FrameMemory.range
          (preludeEvm.toMachineState.mload
            Functions.ScratchFrameSpill.freePtrWord).1
          mainProbe.state.nextSlot).words := by
    rw [hInitMachine]
    exact
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_sound
        hFrameInitReady
  have hInitInvariantSource :
      Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchInvariant
        sourceAfterPrelude.shared initState.toSharedState := by
    simpa [← hPreludeShared] using hInitInvariant
  exact
    hCont hInitRun hInitStack hReady hInitInvariantSource

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_of_checked_atomic_frameInit
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hAtomicSafe :
      Functions.ScratchFrameSpill.FrameMemory.atomicStmtListSafe?
        program.toFunctions.body.stmts = true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
          (Functions.ScratchFrameSpill.FrameMemory.frameInitMachine
            mainProbe.state.nextSlot preludeEvm.toMachineState)
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).words = true →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack =
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1 :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1) := by
  exact
    compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_of_frameInit_ready_check
      hSpec hWordBytes
      (maxFrameWords := maxFrameWords)
      (program := program)
      (asm := asm)
      (publicSource' := publicSource')
      (sourceFuel := sourceFuel)
      (blockFuel := blockFuel)
      (initial := initial)
      hCompile
      (Functions.ScratchFrameSpill.FrameMemory.atomicStmtListSafe?_sound
        hAtomicSafe)
      hInitialPc hRun

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_of_checked_atomicOrBlock_frameInit
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hAtomicOrBlockSafe :
      Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockStmtListSafe?
        program.toFunctions.body.stmts = true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
          (Functions.ScratchFrameSpill.FrameMemory.frameInitMachine
            mainProbe.state.nextSlot preludeEvm.toMachineState)
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).words = true →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack =
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1 :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1) := by
  exact
    compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlock_privateScratch_of_frameInit_ready_check
      hSpec hWordBytes
      (maxFrameWords := maxFrameWords)
      (program := program)
      (asm := asm)
      (publicSource' := publicSource')
      (sourceFuel := sourceFuel)
      (blockFuel := blockFuel)
      (initial := initial)
      hCompile hScoped
      (Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockStmtListSafe?_sound
        hAtomicOrBlockSafe)
      hInitialPc hRun

theorem compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_privateScratch_of_checked_atomicOrBlockFor_frameInit
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    {publicSource' : Functions.Source.State}
    {sourceFuel blockFuel : Nat}
    {initial : EVMState}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm)
    (hScoped :
      Functions.Scope.StmtList.Scoped Functions.Source.Ctx.initial.scope
        program.toFunctions.body.stmts)
    (hAtomicOrBlockForSafe :
      Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockForStmtListSafe?
        program.toFunctions.body.stmts = true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured
          sourceFuel program initial =
        .ok (Functions.Source.Outcome.regular publicSource')) :
    ∃ exprProgram : Expressions.Program,
    ∃ mainProbe : Functions.ScratchFrameSpill.Plan,
    ∃ main : Functions.ScratchFrameSpill.Plan,
    ∃ prelude : List Expressions.Stmt,
    ∃ rest : List Functions.Stmt,
    ∃ innerSource : Functions.Source.State,
    ∃ innerCtx : Functions.Source.Ctx,
    ∃ sourceAfterPrelude : Functions.Source.State,
    ∃ sourceCtxAfterPrelude : Functions.Source.Ctx,
    ∃ preludeEvm : EVMState, ∃ restFuel : Nat,
      compileCheckedWithScratchFrameSpill? maxFrameWords program =
        some (exprProgram, asm) ∧
      main.state = mainProbe.state ∧
      mainProbe.state.nextSlot ≤ maxFrameWords ∧
      exprProgram.body = main.block ∧
      Functions.ScratchFrameSpill.splitPrelude
          program.toFunctions.body.stmts = (prelude, rest) ∧
      publicSource' =
        innerSource.restrictTo EvmCompiler.Functions.Source.Ctx.initial.scope ∧
      preludeEvm.toSharedState = sourceAfterPrelude.shared ∧
      preludeEvm.stack = initial.stack ∧
      EvmCompiler.Functions.Source.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured
          program.toFunctions sourceCtxAfterPrelude restFuel
          { stmts := rest } sourceAfterPrelude =
        .ok (EvmCompiler.Functions.Source.Outcome.regular innerSource,
          innerCtx) ∧
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
          (Functions.ScratchFrameSpill.FrameMemory.frameInitMachine
            mainProbe.state.nextSlot preludeEvm.toMachineState)
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).base
          (Functions.ScratchFrameSpill.FrameMemory.range
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1
            mainProbe.state.nextSlot).words = true →
        ∃ final targetFuel targetOutcome,
          Assembly.Source.runNResult asm targetFuel initial =
            .ok targetOutcome ∧
          Structured.Preservation.WholeProgramOutcomeRel
            (Expressions.Outcome.regular
              ({ Structured.Program.initialState initial with
                evm := final }))
            targetOutcome ∧
          Structured.Preservation.TargetOutcomeEndPc asm targetOutcome ∧
          final.stack =
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1 :: initial.stack ∧
          Functions.ScratchFrameSpill.FrameMemory.ScratchRegionReady
            final.toMachineState
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).base
            (Functions.ScratchFrameSpill.FrameMemory.range
              (preludeEvm.toMachineState.mload
                Functions.ScratchFrameSpill.freePtrWord).1
              mainProbe.state.nextSlot).words ∧
          Functions.ScratchFrameSpill.FrameMemory.SharedStatePrivateScratchObservable
            publicSource'.shared final.toSharedState ∧
          Functions.ScratchFrameSpill.FrameMemory.FrameStoreRel
            main.state.env innerSource.vars final.toMachineState
            (preludeEvm.toMachineState.mload
              Functions.ScratchFrameSpill.freePtrWord).1) := by
  exact
    compileCheckedAssemblyWithScratchFrameSpill?_program_run_assembly_atomicOrBlockFor_privateScratch_of_frameInit_ready_check
      hSpec hWordBytes
      (maxFrameWords := maxFrameWords)
      (program := program)
      (asm := asm)
      (publicSource' := publicSource')
      (sourceFuel := sourceFuel)
      (blockFuel := blockFuel)
      (initial := initial)
      hCompile hScoped
      (Functions.ScratchFrameSpill.FrameMemory.atomicOrBlockForStmtListSafe?_sound
        hAtomicOrBlockForSafe)
      hInitialPc hRun

theorem compileCheckedAssemblyWithScratchFrameSpill?_eq_some
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    ∃ exprProgram : Expressions.Program,
      Functions.ScratchFrameSpill.compileExpressionsProgram? maxFrameWords
          program.toFunctions =
        some exprProgram ∧
        Expressions.Program.compileChecked? exprProgram = some asm := by
  unfold compileCheckedAssemblyWithScratchFrameSpill? at hCompile
  cases hScratch :
      compileCheckedWithScratchFrameSpill? maxFrameWords program with
  | none =>
      simp [hScratch] at hCompile
  | some result =>
      rcases result with ⟨exprProgram, asm'⟩
      simp [hScratch] at hCompile
      cases hCompile
      exact ⟨exprProgram,
        compileCheckedWithScratchFrameSpill?_eq_some hScratch⟩

theorem compileCheckedAssemblyWithScratchFrameSpill?_noCallCreate
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hExprNo :
      ∀ exprProgram : Expressions.Program,
        Functions.ScratchFrameSpill.compileExpressionsProgram? maxFrameWords
            program.toFunctions =
          some exprProgram →
          exprProgram.usesCallCreate = false)
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false := by
  rcases compileCheckedAssemblyWithScratchFrameSpill?_eq_some hCompile with
    ⟨exprProgram, hExpr, hAsm⟩
  exact Expressions.Program.compileChecked?_noCallCreate
    (hExprNo exprProgram hExpr) hAsm

theorem compileCheckedAssemblyWithScratchFrameSpill?_noCallCreate_of_source
    {maxFrameWords : Nat} {program : Objects.Program}
    {asm : Assembly.Program}
    (hProgram : program.toFunctions.usesCallCreate = false)
    (hCompile :
      compileCheckedAssemblyWithScratchFrameSpill? maxFrameWords program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.ScratchFrameSpill.compileCheckedAssembly?_noCallCreate_of_source
    hProgram
    (by
      simpa [compileCheckedAssemblyWithScratchFrameSpill?] using hCompile)

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_noCallCreate
    {maxWords : Nat} {program : Objects.Program}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {asm : Assembly.Program}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_noCallCreate
    (compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
      hCompile)

theorem compile_preserves {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hFrameBound :
      Functions.SourceDirect.FrameBound.Program program.toFunctions)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves
      (prim := prim) hPrim (program := program.toFunctions) (lower := lower)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hSourceAccepted.2.2 hFrameBound
      hFunctionLower hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_endPc {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hFrameBound :
      Functions.SourceDirect.FrameBound.Program program.toFunctions)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves_endPc
      (prim := prim) hPrim (program := program.toFunctions) (lower := lower)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hSourceAccepted.2.2 hFrameBound
      hFunctionLower hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves_of_compileAccepted
      (prim := prim) hPrim (program := program.toFunctions)
      (lower := lower) (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hAccepted.functions hFunctionLower
      hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_of_compileAccepted_endPc
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {lower : Expressions.Program}
    {asm : Assembly.Program} {fuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (hAccepted : CompileAccepted program)
    (hLower : program.toExpressions? = some lower)
    (hCompile :
      Structured.Preservation.ProcedurePreservation.compileChecked?
        lower.toStructured = some asm)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionLower :
      program.toFunctions.toExpressions? = some lower := by
    simpa [Objects.Program.toExpressions?,
      Functions.Inline.Program.toExpressions?] using hLower
  exact
    Functions.Source.Program.compile_preserves_of_compileAccepted_endPc
      (prim := prim) hPrim (program := program.toFunctions)
      (lower := lower) (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hAccepted.functions hFunctionLower
      hCompile hInitialPc hInitialStack hFunctionRun

theorem compile_preserves_checked_of_compileAccepted
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : CompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_preserves_of_compileAccepted hPrim hAccepted hLower
      hStructuredCompile hInitialPc hInitialStack hRun

theorem compile_preserves_checked_of_compileAccepted_endPc
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileChecked? program = some asm)
    (hAccepted : CompileAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun : Source.Program.run prim fuel program initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  rcases compileChecked?_eq_some hCompile with
    ⟨lower, hLower, hStructuredCompile⟩
  exact
    compile_preserves_of_compileAccepted_endPc hPrim hAccepted hLower
      hStructuredCompile hInitialPc hInitialStack hRun

theorem compile_live_noInternalCall_preserves_checked
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      Source.Program.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim (fuel + 1) program.toFunctions
          initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves
      (prim := prim) hPrim (sourceProgram := program.toFunctions)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted.2.2
      hInitialPc hInitialStack hFunctionRun

theorem compile_live_noInternalCall_preserves_checked_endPc
    {prim : PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {program : Objects.Program} {asm : Assembly.Program} {fuel : Nat}
    {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile : compileLiveNoInternalCallChecked? program = some asm)
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hInitialStack : initial.stack = [])
    (hRun :
      Source.Program.run prim (fuel + 1) program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run prim (fuel + 1) program.toFunctions
          initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.LiveLayout.SourceTarget.Program.compileLiveNoInternalCallChecked_preserves_endPc
      (prim := prim) hPrim (sourceProgram := program.toFunctions)
      (asm := asm) (fuel := fuel) (initial := initial)
      (sourceOutcome := sourceOutcome) hCompile hSourceAccepted.2.2
      hInitialPc hInitialStack hFunctionRun

theorem compileCheckedWithConservativeSpillSourceOwned?_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.ConservativeSpillProgramOutcomeRel range initial
        sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_preserves
      hSpec hWordBytes
      (compileCheckedWithConservativeSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithConservativeSpillSourceOwned?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithConservativeSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.ConservativeSpillObservableOutcomeRel range
        sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithConservativeSpillSourceOwned?_observations
      hSpec hWordBytes
      (compileCheckedWithConservativeSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithAdaptiveSpillSourceOwned?_preserves
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillProgramOutcomeRel range initial
        sourceOutcome targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_preserves
      hSpec hWordBytes
      (compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithAdaptiveSpillSourceOwned?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillSourceOwned? range program =
        some asm)
    (hBoundary :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
          initial.toMachineState range [] [] [] =
        true)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillObservableOutcomeRel range
        sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillSourceOwned?_observations
      hSpec hWordBytes
      (compileCheckedWithAdaptiveSpillSourceOwned?_eq_some hCompile)
      hBoundary hInitialPc hFunctionRun

theorem compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxWords : Nat}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?
          maxWords program =
        some (range, asm))
    (hInitialMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchInitialMemoryEmpty
        initial.toMachineState)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillPrivateObservableProgramOutcomeRel
        range sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  exact
    Functions.Source.Program.compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_observations
      hSpec hWordBytes
      (compileCheckedWithAdaptiveSpillPlannedPreallocSourceOwned?_eq_some
        hCompile)
      hInitialMemory hInitialPc hFunctionRun

theorem compileCheckedWithCallAwareSpillPlannedPrealloc?_observations
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {maxWords : Nat}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program}
    {program : Objects.Program} {asm : Assembly.Program}
    {fuel : Nat} {initial : EVMState} {sourceOutcome : Outcome}
    (hCompile :
      compileCheckedWithCallAwareSpillPlannedPrealloc? maxWords program =
        some (range, plan, exprProgram, asm))
    (hSourceAccepted : Objects.Program.SourceAccepted program)
    (hInitialMemory :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchInitialMemoryEmpty
        initial.toMachineState)
    (hInitialStack : initial.stack = [])
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hRun :
      Source.Program.run Locals.Source.PrimitiveSemantics.structured fuel
          program initial =
        .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel initial =
        .ok targetOutcome ∧
      Locals.Source.Program.AdaptiveSpillPrivateObservableProgramOutcomeRel
        range sourceOutcome targetOutcome ∧
      Structured.Preservation.TargetOutcomeEndPc asm targetOutcome := by
  have hFunctionRun :
      Functions.Source.Program.run Locals.Source.PrimitiveSemantics.structured
          fuel program.toFunctions initial =
        .ok sourceOutcome := by
    cases program with
    | mk root =>
        cases root with
        | mk name code data objects =>
            simpa [Source.Program.run, Source.Object.run,
              Objects.Program.toFunctions, Objects.Object.toFunctions] using
              hRun
  have hFunctionAccepted :
      Functions.Program.SourceAccepted program.toFunctions := by
    simpa [Functions.Inline.Program.SourceAccepted] using hSourceAccepted.2
  exact
    Functions.CallAwareSpill.compileCheckedPlannedPrealloc?_sourceAccepted_preserves_initialState_emptyMemory_privateObservable_endPc
      hSpec hWordBytes
      (compileCheckedWithCallAwareSpillPlannedPrealloc?_eq_some hCompile)
      hFunctionAccepted hInitialMemory hInitialStack hInitialPc hFunctionRun

end Program
end Source

end Objects
end EvmCompiler
