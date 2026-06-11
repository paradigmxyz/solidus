import EvmCompiler.Compiler.Artifact
import EvmCompiler.Locals.Allocation
import EvmCompiler.TypedCfg.Certificate

namespace EvmCompiler
namespace Compiler
namespace AllocatedTypedCfg

structure ScopeLayout where
  scope : Locals.Allocation.ScopeId
  stackShape : TypedCfg.Shape
  scratchBindings : List (Locals.Name × Nat)
  deriving DecidableEq, Repr

namespace ScopeLayout

def ofScopePlan (scopePlan : Locals.Allocation.ScopePlan) : ScopeLayout where
  scope := scopePlan.scope
  stackShape :=
    TypedCfg.Shape.closed
      (scopePlan.allocation.stackOrder.map TypedCfg.Slot.local)
  scratchBindings :=
    scopePlan.allocation.bindings.filterMap fun binding =>
      match binding.2 with
      | .stack _ => none
      | .scratch slot => some (binding.1, slot)

end ScopeLayout

def scopeLayoutsOf (plan : Locals.Allocation.ProgramPlan) : List ScopeLayout :=
  plan.scopes.map ScopeLayout.ofScopePlan

structure Program where
  allocation : Locals.Allocation.ProgramPlan
  cfg : TypedCfg.Program
  scopeLayouts : List ScopeLayout := scopeLayoutsOf allocation
  deriving DecidableEq, Repr

structure Certificate where
  scopeLayouts : List ScopeLayout
  cfg : TypedCfg.ProgramCert
  deriving DecidableEq, Repr

namespace Certificate

def ValidFor (certificate : Certificate) (program : Program) : Prop :=
  program.allocation.WellFormed ∧
    program.scopeLayouts = scopeLayoutsOf program.allocation ∧
    certificate.scopeLayouts = program.scopeLayouts ∧
    TypedCfg.Program.ProgramCert.ValidFor certificate.cfg program.cfg

end Certificate

abbrev CertifiedArtifact :=
  Compiler.Artifact Assembly.Program Certificate

namespace Program

def ofAllocation (allocation : Locals.Allocation.ProgramPlan)
    (cfg : TypedCfg.Program) : Program :=
  { allocation := allocation
    cfg := cfg
    scopeLayouts := scopeLayoutsOf allocation }

def compileCertified? (program : Program) : Option CertifiedArtifact := do
  if program.allocation.wellFormed? then pure () else none
  if program.scopeLayouts = scopeLayoutsOf program.allocation then
    pure ()
  else
    none
  let compiled ← program.cfg.compileCertified?
  some
    { target := compiled.target
      metadata :=
        { scopeLayouts := program.scopeLayouts
          cfg := compiled.metadata } }

def compilePass :
    Compiler.Pass Program Assembly.Program Certificate where
  compile? := compileCertified?

def compileContract :
    Compiler.PassContract Program Assembly.Program Certificate where
  pass := compilePass
  Accepted := fun program =>
    program.allocation.WellFormed ∧
      program.scopeLayouts = scopeLayoutsOf program.allocation ∧
      program.cfg.WellTyped
  MetaValid := fun program artifact =>
    artifact.metadata.ValidFor program

theorem compileCertified?_allocationWellFormed
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.allocation.WellFormed := by
  unfold compileCertified? at hCompile
  by_cases hAllocation : program.allocation.wellFormed? = true
  · exact
      Locals.Allocation.ProgramPlan.wellFormed_of_check hAllocation
  · simp [hAllocation] at hCompile

theorem compileCertified?_scopeLayouts
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.scopeLayouts = scopeLayoutsOf program.allocation ∧
      artifact.metadata.scopeLayouts = program.scopeLayouts := by
  unfold compileCertified? at hCompile
  by_cases hAllocation : program.allocation.wellFormed? = true
  · simp [hAllocation] at hCompile
    by_cases hLayouts :
        program.scopeLayouts = scopeLayoutsOf program.allocation
    · simp [hLayouts] at hCompile
      cases hCfg : program.cfg.compileCertified? with
      | none =>
          simp [hCfg] at hCompile
      | some compiled =>
          simp [hCfg] at hCompile
          cases hCompile
          exact ⟨hLayouts, hLayouts.symm⟩
    · simp [hLayouts] at hCompile
  · simp [hAllocation] at hCompile

theorem compileCertified?_cfg
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.cfg.compileCertified? =
      some
        { target := artifact.target
          metadata := artifact.metadata.cfg } := by
  have hAllocation :=
    Locals.Allocation.ProgramPlan.check_of_wellFormed
      (compileCertified?_allocationWellFormed hCompile)
  have hLayouts := (compileCertified?_scopeLayouts hCompile).1
  cases hCfg : program.cfg.compileCertified? with
  | none =>
      simp [compileCertified?, hAllocation, hLayouts, hCfg] at hCompile
  | some compiled =>
      have hArtifact :
          ({ target := compiled.target
             metadata :=
               { scopeLayouts := program.scopeLayouts
                 cfg := compiled.metadata } } :
            CertifiedArtifact) = artifact := by
        simpa [compileCertified?, hAllocation, hLayouts, hCfg] using hCompile
      rw [← hArtifact]

theorem compileCertified?_certificateValid
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    artifact.metadata.ValidFor program := by
  refine
    ⟨compileCertified?_allocationWellFormed hCompile,
      (compileCertified?_scopeLayouts hCompile).1,
      (compileCertified?_scopeLayouts hCompile).2, ?_⟩
  have hCfg := compileCertified?_cfg hCompile
  exact
    ⟨TypedCfg.Program.compileCertified?_wellTyped hCfg,
      TypedCfg.Program.compileCertified?_certificate hCfg⟩

theorem compileCertified?_checked
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    Compiler.PassContract.Checked compileContract program artifact := by
  have hValid := compileCertified?_certificateValid hCompile
  exact
    { accepted := ⟨hValid.1, hValid.2.1, hValid.2.2.2.1⟩
      compiles := hCompile
      metadataValid := hValid }

theorem compileCertified?_labelPc_exists
    {program : Program} {artifact : CertifiedArtifact}
    {label : Assembly.Label} {block : TypedCfg.Block}
    (hCompile : program.compileCertified? = some artifact)
    (hFind : program.cfg.findBlock? label = some block) :
    ∃ entryPc, artifact.target.labelPc label = some entryPc := by
  exact
    TypedCfg.Program.compileCertified?_labelPc_exists
      (compileCertified?_cfg hCompile) hFind

theorem compileCertified?_step_eventually
    {program : Program} {artifact : CertifiedArtifact}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {state : Assembly.EVMState} {entryPc : Nat}
    (hCompile : program.compileCertified? = some artifact)
    (hFind : program.cfg.findBlock? label = some block)
    (hLabelPc :
      artifact.target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Assembly.Source.Eventually artifact.target state
      (TypedCfg.Preservation.Block.RunSimulates artifact.target
        (program.cfg.step label state.incrPC)) := by
  exact
    TypedCfg.Program.compileCertified?_step_eventually
      (compileCertified?_cfg hCompile)
      hFind hLabelPc hPc

end Program

namespace Examples

def entry : Assembly.Label :=
  .named "allocated-typedcfg:entry"

def cfg : TypedCfg.Program :=
  let shape := TypedCfg.Shape.closed
  { entry := entry
    blocks :=
      [{ label := entry
         input := shape
         body := []
         output := shape
         term := .invalid }] }

def localAllocation : Locals.Allocation.Plan :=
  { sourceScope := []
    stackOrder := []
    bindings := []
    scratchRegion? := none }

def allocation : Locals.Allocation.ProgramPlan :=
  Locals.Allocation.ProgramPlan.main localAllocation

def duplicateScopeAllocation : Locals.Allocation.ProgramPlan :=
  { scopes :=
      [{ scope := .main
         allocation := localAllocation },
       { scope := .main
         allocation := localAllocation }] }

def program : Program :=
  Program.ofAllocation allocation cfg

def staleLayoutProgram : Program :=
  { allocation := allocation
    cfg := cfg
    scopeLayouts :=
      [{ scope := .main
         stackShape := TypedCfg.Shape.closed [.local "stale"]
         scratchBindings := [] }] }

example : program.compileCertified?.isSome = true := by
  native_decide

example : staleLayoutProgram.compileCertified? = none := by
  native_decide

example : duplicateScopeAllocation.wellFormed? = false := by
  native_decide

end Examples

end AllocatedTypedCfg
end Compiler
end EvmCompiler
