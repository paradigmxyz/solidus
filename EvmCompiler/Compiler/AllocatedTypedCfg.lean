import EvmCompiler.Compiler.Artifact
import EvmCompiler.Locals.Allocation
import EvmCompiler.TypedCfg.Certificate

namespace EvmCompiler
namespace Compiler
namespace AllocatedTypedCfg

structure Program where
  allocation : Locals.Allocation.ProgramPlan
  cfg : TypedCfg.Program
  deriving DecidableEq, Repr

structure Certificate where
  cfg : TypedCfg.ProgramCert
  deriving DecidableEq, Repr

namespace Certificate

def ValidFor (certificate : Certificate) (program : Program) : Prop :=
  program.allocation.WellFormed ∧
    TypedCfg.Program.ProgramCert.ValidFor certificate.cfg program.cfg

end Certificate

abbrev CertifiedArtifact :=
  Compiler.Artifact Assembly.Program Certificate

namespace Program

def compileCertified? (program : Program) : Option CertifiedArtifact := do
  if program.allocation.wellFormed? then pure () else none
  let compiled ← program.cfg.compileCertified?
  some
    { target := compiled.target
      metadata := { cfg := compiled.metadata } }

def compilePass :
    Compiler.Pass Program Assembly.Program Certificate where
  compile? := compileCertified?

def compileContract :
    Compiler.PassContract Program Assembly.Program Certificate where
  pass := compilePass
  Accepted := fun program =>
    program.allocation.WellFormed ∧ program.cfg.WellTyped
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

theorem compileCertified?_cfg
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.cfg.compileCertified? =
      some
        { target := artifact.target
          metadata := artifact.metadata.cfg } := by
  unfold compileCertified? at hCompile
  by_cases hAllocation : program.allocation.wellFormed? = true
  · simp [hAllocation] at hCompile
    cases hCfg : program.cfg.compileCertified? with
    | none =>
        simp [hCfg] at hCompile
    | some compiled =>
        simp [hCfg] at hCompile
        cases hCompile
        simpa using hCfg
  · simp [hAllocation] at hCompile

theorem compileCertified?_certificateValid
    {program : Program} {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    artifact.metadata.ValidFor program := by
  refine
    ⟨compileCertified?_allocationWellFormed hCompile, ?_⟩
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
    { accepted := ⟨hValid.1, hValid.2.1⟩
      compiles := hCompile
      metadataValid := hValid }

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
  { allocation := allocation, cfg := cfg }

example : program.compileCertified?.isSome = true := by
  native_decide

example : duplicateScopeAllocation.wellFormed? = false := by
  native_decide

end Examples

end AllocatedTypedCfg
end Compiler
end EvmCompiler
