import EvmCompiler.Objects.Syntax
import EvmCompiler.Compiler.AllocatedTypedCfg
import EvmCompiler.Compiler.Artifact
import EvmCompiler.Functions.Compiler
import EvmCompiler.Functions.ScratchFrameSpill

namespace EvmCompiler
namespace Objects

namespace Object

theorem toFunctions_wf {object : Object}
    (hWF : object.WF) :
    object.toFunctions.WF := by
  cases object with
  | mk name code data objects =>
      exact hWF.left

end Object

namespace Program

def toExpressions? (program : Program) : Option Expressions.Program :=
  Functions.Inline.Program.toExpressions? program.toFunctions

def scratchFrameSpillFallbackWords : Nat :=
  8192

inductive Backend where
  | inlineStack
  | scratchFrameSpill
  deriving DecidableEq, Repr

structure BackendConfig where
  scratchFrameWords : Nat := scratchFrameSpillFallbackWords
  deriving DecidableEq, Repr

structure BackendPolicy where
  order : List Backend
  config : BackendConfig := {}
  deriving DecidableEq, Repr

def defaultBackendPolicy : BackendPolicy where
  order := [.inlineStack, .scratchFrameSpill]

structure CompileMetadata where
  backend : Backend
  allocation : Locals.Allocation.ProgramPlan
  typedCfg : TypedCfg.Program
  certificate : Compiler.AllocatedTypedCfg.Certificate
  deriving DecidableEq, Repr

namespace CompileMetadata

def AllocationValid (metadata : CompileMetadata) : Prop :=
  metadata.allocation.WellFormed

def TypedCfgValid (metadata : CompileMetadata) : Prop :=
  metadata.certificate.ValidFor
    { allocation := metadata.allocation
      cfg := metadata.typedCfg }

end CompileMetadata

abbrev CompileArtifact :=
  Compiler.Artifact Assembly.TargetProgram CompileMetadata

structure PlannedProgram where
  source : Functions.Program
  allocation : Locals.Allocation.ProgramPlan

namespace PlannedProgram

def mainAllocation? (planned : PlannedProgram) :
    Option Locals.Allocation.Plan :=
  planned.allocation.find? .main

/--
Result of the single allocation-driven Functions-to-Expressions lowerer.

The selected backend is an output derived from the accepted canonical plan,
not an input that chooses a separate lowering implementation.
-/
structure AllocationLoweringResult where
  backend : Backend
  expressions : Expressions.Program

/--
The single allocation-aware Functions-to-Expressions lowerer.

It first recognizes the exact canonical stack plan. Every other accepted plan
is offered to the scratch-capable allocation lowerer, which independently
checks that the plan is the source-derived scratch recipe. Backend policy does
not participate in this choice.
-/
def lowerAllocation? (source : Functions.Program)
    (allocation : Locals.Allocation.ProgramPlan) :
    Option AllocationLoweringResult :=
  if
      Functions.ScratchFrameSpill.stackAllocationPlanner.plan? source =
        some allocation
  then do
    let expressions ← Functions.Inline.Program.toExpressions? source
    some { backend := .inlineStack, expressions := expressions }
  else do
    let expressions ←
      Functions.ScratchFrameSpill.allocationLowerer.lower?
        source allocation
    some { backend := .scratchFrameSpill, expressions := expressions }

def allocationLowerer :
    Locals.Allocation.Lowerer Functions.Program AllocationLoweringResult where
  lower? := lowerAllocation?

def loweringResult? (planned : PlannedProgram) :
    Option AllocationLoweringResult :=
  allocationLowerer.lower? planned.source planned.allocation

def lowerWithAllocation? (planned : PlannedProgram) :
    Option Expressions.Program :=
  planned.loweringResult?.map AllocationLoweringResult.expressions

def lowerExpressions? (planned : PlannedProgram) :
    Option Expressions.Program :=
  planned.lowerWithAllocation?

theorem loweringResult?_inlineStack_allocation
    {planned : PlannedProgram} {expressions : Expressions.Program}
    (hLower :
      planned.loweringResult? =
        some { backend := .inlineStack, expressions := expressions }) :
    Functions.ScratchFrameSpill.stackAllocationPlanner.plan?
        planned.source =
      some planned.allocation := by
  unfold loweringResult? allocationLowerer lowerAllocation? at hLower
  by_cases hPlan :
      Functions.ScratchFrameSpill.stackAllocationPlanner.plan?
          planned.source =
        some planned.allocation
  · exact hPlan
  · cases hScratch :
        Functions.ScratchFrameSpill.allocationLowerer.lower?
          planned.source planned.allocation with
    | none =>
        simp [hPlan, hScratch] at hLower
    | some scratchExpressions =>
        simp [hPlan, hScratch] at hLower

theorem loweringResult?_scratchFrame_exact
    {planned : PlannedProgram} {expressions : Expressions.Program}
    (hLower :
      planned.loweringResult? =
        some { backend := .scratchFrameSpill, expressions := expressions }) :
    Functions.ScratchFrameSpill.allocationLowerer.lower?
        planned.source planned.allocation =
      some expressions := by
  unfold loweringResult? allocationLowerer lowerAllocation? at hLower
  by_cases hPlan :
      Functions.ScratchFrameSpill.stackAllocationPlanner.plan?
          planned.source =
        some planned.allocation
  · cases hInline :
        Functions.Inline.Program.toExpressions? planned.source with
    | none =>
        simp [hPlan, hInline] at hLower
    | some inlineExpressions =>
        simp [hPlan, hInline] at hLower
  · cases hScratch :
        Functions.ScratchFrameSpill.allocationLowerer.lower?
          planned.source planned.allocation with
    | none =>
        simp [hPlan, hScratch] at hLower
    | some scratchExpressions =>
        simp [hPlan, hScratch] at hLower
        cases hLower
        rfl

theorem lowerWithAllocation?_eq (planned : PlannedProgram) :
    planned.lowerWithAllocation? = planned.lowerExpressions? := by
  rfl

def inlineProcEntryShape?
    (allocation : Locals.Allocation.ProgramPlan)
    (proc : Expressions.Proc) :
    Option (Expressions.Name × TypedCfg.Shape) := do
  let plan ← allocation.find? (.function proc.name)
  if proc.argc ≤ plan.stackOrder.length then
    let sourceParams :=
      plan.stackOrder.drop (plan.stackOrder.length - proc.argc)
    let shape ←
      Structured.TypedCfgCompiler.Shape.namedProcEntry?
        proc.toStructured sourceParams.reverse
    some (proc.name, shape)
  else
    none

def inlineProcEntryShapes?
    (allocation : Locals.Allocation.ProgramPlan) :
    List Expressions.Proc →
      Option Structured.TypedCfgCompiler.ProcEntryShapes
  | [] => some []
  | proc :: rest => do
      let entry ← inlineProcEntryShape? allocation proc
      let tail ← inlineProcEntryShapes? allocation rest
      some (entry :: tail)

def procEntryShapesFromAllocation?
    (source : Functions.Program)
    (allocation : Locals.Allocation.ProgramPlan)
    (expressions : Expressions.Program) :
    Option Structured.TypedCfgCompiler.ProcEntryShapes :=
  if
      Functions.ScratchFrameSpill.stackAllocationPlanner.plan? source =
        some allocation
  then
    inlineProcEntryShapes? allocation expressions.procs
  else
    some []

def procEntryShapes? (planned : PlannedProgram)
    (expressions : Expressions.Program) :
    Option Structured.TypedCfgCompiler.ProcEntryShapes :=
  procEntryShapesFromAllocation?
    planned.source planned.allocation expressions

def lowerTypedCfg? (planned : PlannedProgram)
    (expressions : Expressions.Program) : Option TypedCfg.Program := do
  let entryShapes ← planned.procEntryShapes? expressions
  Structured.TypedCfgCompiler.lowerWithProcEntryShapes?
    expressions.toStructured entryShapes

theorem lowerTypedCfg?_sourceArtifact
    {planned : PlannedProgram} {expressions : Expressions.Program}
    {cfg : TypedCfg.Program}
    (hLower : planned.lowerTypedCfg? expressions = some cfg) :
    ∃ entryShapes sourceArtifact,
      planned.procEntryShapes? expressions = some entryShapes ∧
        Structured.TypedCfgCompiler.artifactWithProcEntryShapes?
            expressions.toStructured entryShapes =
          some sourceArtifact ∧
        sourceArtifact.cfg = cfg := by
  unfold lowerTypedCfg? at hLower
  cases hShapes : planned.procEntryShapes? expressions with
  | none =>
      simp [hShapes] at hLower
  | some entryShapes =>
      simp [hShapes] at hLower
      unfold Structured.TypedCfgCompiler.lowerWithProcEntryShapes? at hLower
      cases hArtifact :
          Structured.TypedCfgCompiler.artifactWithProcEntryShapes?
            expressions.toStructured entryShapes with
      | none =>
          simp [hArtifact] at hLower
      | some sourceArtifact =>
          simp [hArtifact] at hLower
          cases hLower
          exact ⟨entryShapes, sourceArtifact, rfl, hArtifact, rfl⟩

def lowerArtifact? (planned : PlannedProgram) :
    Option CompileArtifact := do
  if planned.allocation.wellFormed? then pure () else none
  let lowered ← planned.loweringResult?
  let expressions := lowered.expressions
  let cfg ← planned.lowerTypedCfg? expressions
  let allocated :=
    Compiler.AllocatedTypedCfg.Program.ofAllocation planned.allocation cfg
  let compiled ← allocated.compileCertified?
  let target ← Assembly.compileExecutable? compiled.target
  some
    { target := target
      metadata :=
        { backend := lowered.backend
          allocation := planned.allocation
          typedCfg := cfg
          certificate := compiled.metadata } }

theorem lowerArtifact?_metadataValid
    {planned : PlannedProgram} {artifact : CompileArtifact}
    (hCompile : planned.lowerArtifact? = some artifact) :
    artifact.metadata.AllocationValid ∧
      artifact.metadata.TypedCfgValid := by
  unfold lowerArtifact? at hCompile
  by_cases hValid : planned.allocation.wellFormed? = true
  · simp [hValid] at hCompile
    cases hLower : planned.loweringResult? with
    | none =>
        simp [hLower] at hCompile
    | some lowered =>
        simp [hLower] at hCompile
        let expressions := lowered.expressions
        cases hCfg : planned.lowerTypedCfg? expressions with
        | none =>
            rw [hCfg] at hCompile
            simp at hCompile
        | some cfg =>
            rw [hCfg] at hCompile
            simp only [Option.bind_some] at hCompile
            simp only
              [Compiler.AllocatedTypedCfg.Program.ofAllocation]
              at hCompile
            unfold
              Compiler.AllocatedTypedCfg.Program.compileCertified?
              at hCompile
            rw [if_pos hValid] at hCompile
            rw [if_pos rfl] at hCompile
            cases hCfgCompiled : cfg.compileCertified? with
            | none =>
                rw [hCfgCompiled] at hCompile
                simp at hCompile
            | some cfgCompiled =>
                rw [hCfgCompiled] at hCompile
                simp at hCompile
                cases hTarget :
                    Assembly.compileExecutable? cfgCompiled.target with
                | none =>
                    rw [hTarget] at hCompile
                    simp at hCompile
                | some target =>
                    rw [hTarget] at hCompile
                    simp only [Option.bind_some, Option.some.injEq] at hCompile
                    cases hCompile
                    have hAllocation :=
                      Locals.Allocation.ProgramPlan.wellFormed_of_check
                        hValid
                    have hCfgCertificate :
                        TypedCfg.Program.ProgramCert.ValidFor
                          cfgCompiled.metadata cfg :=
                      ⟨TypedCfg.Program.compileCertified?_wellTyped
                          hCfgCompiled,
                        TypedCfg.Program.compileCertified?_certificate
                          hCfgCompiled⟩
                    exact
                      ⟨hAllocation,
                        ⟨hAllocation, rfl, rfl, hCfgCertificate⟩⟩
  · simp [hValid] at hCompile

end PlannedProgram

namespace CompileArtifact

/--
The executable certificate relation for the allocation boundary.

Unlike `CompileMetadata.AllocationValid`, this records that the selected
canonical allocation was consumed by the one public Functions-to-Expressions
lowerer and that the resulting Expressions program produced the stored
TypedCfg certificate and executable target.
-/
def LoweredFrom (artifact : CompileArtifact)
    (source : Functions.Program) : Prop :=
  ∃ expressions compiled,
    let planned : PlannedProgram :=
      { source := source
        allocation := artifact.metadata.allocation }
    planned.lowerWithAllocation? = some expressions ∧
      planned.lowerTypedCfg? expressions = some artifact.metadata.typedCfg ∧
      (Compiler.AllocatedTypedCfg.Program.ofAllocation
        artifact.metadata.allocation
        artifact.metadata.typedCfg).compileCertified? =
        some compiled ∧
      Assembly.compileExecutable? compiled.target =
        some artifact.target ∧
      artifact.metadata.certificate = compiled.metadata

end CompileArtifact

theorem PlannedProgram.lowerArtifact?_loweredFrom
    {planned : PlannedProgram} {artifact : CompileArtifact}
    (hCompile : planned.lowerArtifact? = some artifact) :
    artifact.LoweredFrom planned.source := by
  unfold PlannedProgram.lowerArtifact? at hCompile
  by_cases hValid : planned.allocation.wellFormed? = true
  · simp [hValid] at hCompile
    cases hLower : planned.loweringResult? with
    | none =>
        simp [hLower] at hCompile
    | some lowered =>
        simp [hLower] at hCompile
        let expressions := lowered.expressions
        cases hCfg : planned.lowerTypedCfg? expressions with
        | none =>
            rw [hCfg] at hCompile
            simp at hCompile
        | some cfg =>
            rw [hCfg] at hCompile
            simp only [Option.bind_some] at hCompile
            simp only
              [Compiler.AllocatedTypedCfg.Program.ofAllocation]
              at hCompile
            unfold
              Compiler.AllocatedTypedCfg.Program.compileCertified?
              at hCompile
            rw [if_pos hValid] at hCompile
            rw [if_pos rfl] at hCompile
            cases hCfgCompiled : cfg.compileCertified? with
            | none =>
                rw [hCfgCompiled] at hCompile
                simp at hCompile
            | some cfgCompiled =>
                rw [hCfgCompiled] at hCompile
                simp at hCompile
                cases hTarget :
                    Assembly.compileExecutable? cfgCompiled.target with
                | none =>
                    rw [hTarget] at hCompile
                    simp at hCompile
                | some target =>
                    rw [hTarget] at hCompile
                    simp only [Option.bind_some, Option.some.injEq] at hCompile
                    cases hCompile
                    let compiled :
                        Compiler.AllocatedTypedCfg.CertifiedArtifact :=
                      { target := cfgCompiled.target
                        metadata :=
                          { scopeLayouts :=
                              Compiler.AllocatedTypedCfg.scopeLayoutsOf
                                planned.allocation
                            cfg := cfgCompiled.metadata } }
                    exact
                      ⟨expressions, compiled, by
                          simp [lowerWithAllocation?, hLower, expressions],
                        hCfg,
                        by
                          simp [compiled,
                            Compiler.AllocatedTypedCfg.Program.ofAllocation,
                            Compiler.AllocatedTypedCfg.Program.compileCertified?,
                            hValid, hCfgCompiled],
                        hTarget, rfl⟩
  · simp [hValid] at hCompile

def planInlineStack? (program : Program) : Option PlannedProgram := do
  let allocation ←
    Functions.ScratchFrameSpill.stackAllocationPlanner.plan?
      program.toFunctions
  some
    { source := program.toFunctions
      allocation := allocation }

theorem planInlineStack?_source
    {program : Program} {planned : PlannedProgram}
    (hPlan : planInlineStack? program = some planned) :
    planned.source = program.toFunctions := by
  unfold planInlineStack? at hPlan
  cases hAllocation :
      Functions.ScratchFrameSpill.stackAllocationPlanner.plan?
        program.toFunctions with
  | none =>
      simp [hAllocation] at hPlan
  | some allocation =>
      simp [hAllocation] at hPlan
      cases hPlan
      rfl

def planScratchFrame? (config : BackendConfig) (program : Program) :
    Option PlannedProgram := do
  let allocation ←
    (Functions.ScratchFrameSpill.allocationPlanner
      config.scratchFrameWords).plan? program.toFunctions
  some
    { source := program.toFunctions
      allocation := allocation }

theorem planScratchFrame?_source
    {config : BackendConfig} {program : Program}
    {planned : PlannedProgram}
    (hPlan : planScratchFrame? config program = some planned) :
    planned.source = program.toFunctions := by
  unfold planScratchFrame? at hPlan
  cases hAllocation :
      (Functions.ScratchFrameSpill.allocationPlanner
        config.scratchFrameWords).plan? program.toFunctions with
  | none =>
      simp [hAllocation] at hPlan
  | some allocation =>
      simp [hAllocation] at hPlan
      cases hPlan
      rfl

def compilePlannedAs? (backend : Backend)
    (planned : PlannedProgram) : Option CompileArtifact := do
  let artifact ← planned.lowerArtifact?
  if artifact.metadata.backend = backend then
    some artifact
  else
    none

def Backend.compileArtifact? (config : BackendConfig) (program : Program) :
    Backend → Option CompileArtifact
  | .inlineStack =>
      match planInlineStack? program with
      | none => none
      | some planned => compilePlannedAs? .inlineStack planned
  | .scratchFrameSpill =>
      match planScratchFrame? config program with
      | none => none
      | some planned => compilePlannedAs? .scratchFrameSpill planned

theorem Backend.compileArtifact?_metadataValid
    {config : BackendConfig} {program : Program} {backend : Backend}
    {artifact : CompileArtifact}
    (hCompile : backend.compileArtifact? config program = some artifact) :
    artifact.metadata.backend = backend ∧
      artifact.metadata.AllocationValid ∧
      artifact.metadata.TypedCfgValid := by
  cases backend with
  | inlineStack =>
      unfold Backend.compileArtifact? at hCompile
      cases hPlan : planInlineStack? program with
      | none =>
          simp [hPlan] at hCompile
      | some planned =>
          simp [hPlan] at hCompile
          unfold compilePlannedAs? at hCompile
          cases hArtifact : planned.lowerArtifact? with
          | none =>
              simp [hArtifact] at hCompile
          | some selected =>
              by_cases hBackend :
                  selected.metadata.backend = .inlineStack
              · simp [hArtifact, hBackend] at hCompile
                cases hCompile
                exact
                  ⟨hBackend,
                    PlannedProgram.lowerArtifact?_metadataValid hArtifact⟩
              · simp [hArtifact, hBackend] at hCompile
  | scratchFrameSpill =>
      unfold Backend.compileArtifact? at hCompile
      cases hPlan : planScratchFrame? config program with
      | none =>
          simp [hPlan] at hCompile
      | some planned =>
          simp [hPlan] at hCompile
          unfold compilePlannedAs? at hCompile
          cases hArtifact : planned.lowerArtifact? with
          | none =>
              simp [hArtifact] at hCompile
          | some selected =>
              by_cases hBackend :
                  selected.metadata.backend = .scratchFrameSpill
              · simp [hArtifact, hBackend] at hCompile
                cases hCompile
                exact
                  ⟨hBackend,
                    PlannedProgram.lowerArtifact?_metadataValid hArtifact⟩
              · simp [hArtifact, hBackend] at hCompile

theorem Backend.compileArtifact?_loweredFrom
    {config : BackendConfig} {program : Program} {backend : Backend}
    {artifact : CompileArtifact}
    (hCompile : backend.compileArtifact? config program = some artifact) :
    artifact.LoweredFrom program.toFunctions := by
  cases backend with
  | inlineStack =>
      unfold Backend.compileArtifact? at hCompile
      cases hPlan : planInlineStack? program with
      | none =>
          simp [hPlan] at hCompile
      | some planned =>
          simp [hPlan] at hCompile
          unfold compilePlannedAs? at hCompile
          cases hArtifact : planned.lowerArtifact? with
          | none =>
              simp [hArtifact] at hCompile
          | some selected =>
            by_cases hBackend :
                selected.metadata.backend = .inlineStack
            · simp [hArtifact, hBackend] at hCompile
              cases hCompile
              have hLowered :=
                PlannedProgram.lowerArtifact?_loweredFrom hArtifact
              rw [planInlineStack?_source hPlan] at hLowered
              exact hLowered
            · simp [hArtifact, hBackend] at hCompile
  | scratchFrameSpill =>
      unfold Backend.compileArtifact? at hCompile
      cases hPlan : planScratchFrame? config program with
      | none =>
          simp [hPlan] at hCompile
      | some planned =>
          simp [hPlan] at hCompile
          unfold compilePlannedAs? at hCompile
          cases hArtifact : planned.lowerArtifact? with
          | none =>
              simp [hArtifact] at hCompile
          | some selected =>
            by_cases hBackend :
                selected.metadata.backend = .scratchFrameSpill
            · simp [hArtifact, hBackend] at hCompile
              cases hCompile
              have hLowered :=
                PlannedProgram.lowerArtifact?_loweredFrom hArtifact
              rw [planScratchFrame?_source hPlan] at hLowered
              exact hLowered
            · simp [hArtifact, hBackend] at hCompile

def compileFirst? (config : BackendConfig) (program : Program) :
    List Backend → Option CompileArtifact
  | [] => none
  | backend :: rest =>
      match backend.compileArtifact? config program with
      | some artifact => some artifact
      | none => compileFirst? config program rest

def CompileMetadata.Valid (policy : BackendPolicy)
    (metadata : CompileMetadata) : Prop :=
  metadata.backend ∈ policy.order ∧
    metadata.AllocationValid ∧
    metadata.TypedCfgValid

def CompileArtifact.Valid (policy : BackendPolicy) (program : Program)
    (artifact : CompileArtifact) : Prop :=
  artifact.metadata.Valid policy ∧
    artifact.LoweredFrom program.toFunctions

theorem compileFirst?_metadataValid
    {config : BackendConfig} {program : Program}
    {backends : List Backend} {artifact : CompileArtifact}
    (hCompile : compileFirst? config program backends = some artifact) :
    artifact.metadata.backend ∈ backends ∧
      artifact.metadata.AllocationValid ∧
      artifact.metadata.TypedCfgValid := by
  induction backends with
  | nil =>
      simp [compileFirst?] at hCompile
  | cons backend rest ih =>
      cases hBackend : backend.compileArtifact? config program with
      | none =>
          simp [compileFirst?, hBackend] at hCompile
          rcases ih hCompile with ⟨hMember, hAllocation, hTyped⟩
          exact ⟨by simp [hMember], hAllocation, hTyped⟩
      | some selected =>
          simp [compileFirst?, hBackend] at hCompile
          cases hCompile
          rcases Backend.compileArtifact?_metadataValid hBackend with
            ⟨hBackendEq, hAllocation, hTyped⟩
          exact ⟨by simp [hBackendEq], hAllocation, hTyped⟩

theorem compileFirst?_loweredFrom
    {config : BackendConfig} {program : Program}
    {backends : List Backend} {artifact : CompileArtifact}
    (hCompile : compileFirst? config program backends = some artifact) :
    artifact.LoweredFrom program.toFunctions := by
  induction backends with
  | nil =>
      simp [compileFirst?] at hCompile
  | cons backend rest ih =>
      cases hBackend : backend.compileArtifact? config program with
      | none =>
          simp [compileFirst?, hBackend] at hCompile
          exact ih hCompile
      | some selected =>
          simp [compileFirst?, hBackend] at hCompile
          cases hCompile
          exact Backend.compileArtifact?_loweredFrom hBackend

def compileArtifactWithPolicy? (policy : BackendPolicy)
    (program : Program) : Option CompileArtifact :=
  compileFirst? policy.config program policy.order

theorem compileArtifactWithPolicy?_metadataValid
    {policy : BackendPolicy} {program : Program}
    {artifact : CompileArtifact}
    (hCompile :
      compileArtifactWithPolicy? policy program = some artifact) :
    artifact.metadata.Valid policy := by
  exact compileFirst?_metadataValid hCompile

theorem compileArtifactWithPolicy?_valid
    {policy : BackendPolicy} {program : Program}
    {artifact : CompileArtifact}
    (hCompile :
      compileArtifactWithPolicy? policy program = some artifact) :
    artifact.Valid policy program := by
  exact
    ⟨compileArtifactWithPolicy?_metadataValid hCompile,
      compileFirst?_loweredFrom hCompile⟩

def compileArtifact? (program : Program) : Option CompileArtifact :=
  compileArtifactWithPolicy? defaultBackendPolicy program

def compilePass (policy : BackendPolicy) :
    Compiler.Pass Program Assembly.TargetProgram CompileMetadata where
  compile? := compileArtifactWithPolicy? policy

def compile? (program : Program) :
    Option Assembly.TargetProgram :=
  Compiler.Artifact.target? (compileArtifact? program)

theorem compileFirst?_head {config : BackendConfig} {program : Program}
    {backend : Backend} {rest : List Backend}
    {artifact : CompileArtifact}
    (hCompile :
      backend.compileArtifact? config program = some artifact) :
    compileFirst? config program (backend :: rest) = some artifact := by
  simp [compileFirst?, hCompile]

theorem compile?_of_artifact {program : Program}
    {artifact : CompileArtifact}
    (hCompile : compileArtifact? program = some artifact) :
    compile? program = some artifact.target := by
  simp [compile?, hCompile]

def Accepted (program : Program) : Prop :=
  program.WF ∧ Functions.Inline.Program.Accepted program.toFunctions

def SourceAccepted (program : Program) : Prop :=
  program.WF ∧ Functions.Inline.Program.SourceAccepted program.toFunctions

def compileContract (policy : BackendPolicy) :
    Compiler.PassContract Program Assembly.TargetProgram CompileMetadata where
  pass := compilePass policy
  Accepted := SourceAccepted
  MetaValid := fun program artifact =>
    CompileArtifact.Valid policy program artifact

theorem compileArtifactWithPolicy?_checked
    {policy : BackendPolicy} {program : Program}
    {artifact : CompileArtifact}
    (hAccepted : SourceAccepted program)
    (hCompile :
      compileArtifactWithPolicy? policy program = some artifact) :
    Compiler.PassContract.Checked (compileContract policy) program artifact := by
  exact
    { accepted := hAccepted
      compiles := hCompile
      metadataValid :=
        compileArtifactWithPolicy?_valid hCompile }

theorem sourceAccepted_of_accepted {program : Program}
    (hAccepted : Accepted program) :
    SourceAccepted program :=
  ⟨hAccepted.1,
    Functions.Inline.Program.sourceAccepted_of_accepted hAccepted.2⟩

theorem toFunctions_wf {program : Program}
    (hWF : program.WF) :
    program.toFunctions.WF := by
  exact Object.toFunctions_wf hWF

end Program

namespace SourceAcceptedCheck

mutual
  def Object.wf? : Objects.Object → Bool
    | .mk _name code _data objects =>
        Functions.SourceAcceptedCheck.Program.wf? code &&
          ObjectList.wf? objects

  def ObjectList.wf? : List Objects.Object → Bool
    | [] => true
    | object :: rest => Object.wf? object && ObjectList.wf? rest
end

namespace Program

def wf? (program : Objects.Program) : Bool :=
  Object.wf? program.root

def sourceAccepted? (program : Objects.Program) : Bool :=
  wf? program &&
    Functions.SourceAcceptedCheck.Program.sourceAccepted? program.toFunctions

end Program

mutual
  theorem Object.wf_of_check :
      ∀ {object : Objects.Object},
        Object.wf? object = true →
          object.WF := by
    intro object hCheck
    cases object with
    | mk name code data objects =>
        have hAnd :
            Functions.SourceAcceptedCheck.Program.wf? code = true ∧
              ObjectList.wf? objects = true :=
          by simpa [Object.wf?] using hCheck
        exact
          ⟨Functions.SourceAcceptedCheck.Program.wf_of_check hAnd.1,
            ObjectList.wf_of_check hAnd.2⟩

  theorem ObjectList.wf_of_check :
      ∀ {objects : List Objects.Object},
        ObjectList.wf? objects = true →
          Objects.ObjectList.WF objects := by
    intro objects hCheck
    cases objects with
    | nil =>
        trivial
    | cons object rest =>
        have hAnd :
            Object.wf? object = true ∧ ObjectList.wf? rest = true :=
          by simpa [ObjectList.wf?] using hCheck
        exact
          ⟨Object.wf_of_check hAnd.1,
            ObjectList.wf_of_check hAnd.2⟩
end

theorem Program.wf_of_check {program : Objects.Program}
    (hCheck : Program.wf? program = true) :
    program.WF := by
  exact Object.wf_of_check hCheck

theorem Program.sourceAccepted_of_check {program : Objects.Program}
    (hCheck : Program.sourceAccepted? program = true) :
    program.SourceAccepted := by
  have hAnd :
      Program.wf? program = true ∧
        Functions.SourceAcceptedCheck.Program.sourceAccepted?
            program.toFunctions =
          true :=
    by simpa [Program.sourceAccepted?] using hCheck
  exact
    ⟨Program.wf_of_check hAnd.1,
      Functions.SourceAcceptedCheck.Program.sourceAccepted_of_check hAnd.2⟩

end SourceAcceptedCheck

end Objects
end EvmCompiler
