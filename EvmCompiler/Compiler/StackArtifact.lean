import EvmCompiler.Functions.StackLowering
import EvmCompiler.Functions.StackPressureNormalizationProgram
import EvmCompiler.Functions.Compiler
import EvmCompiler.Functions.OpenSupportCheck
import EvmCompiler.Locals.Compiler
import EvmCompiler.Structured.SourceAcceptedCheck
import EvmCompiler.Structured.Semantics
import EvmCompiler.Structured.TypedCfgCompiler
import EvmCompiler.TypedCfg.Certificate
import EvmCompiler.TypedCfg.PeepholeSpine
import EvmCompiler.TypedCfg.PeepholeNoopSwapProgram
import EvmCompiler.TypedCfg.PeepholeSeamCancel
import EvmCompiler.TypedCfg.PeepholeSeamCancelEff
import EvmCompiler.TypedCfg.ShuffleCanonChain
import EvmCompiler.TypedCfg.BlockReorderCanon
import EvmCompiler.TypedCfg.ConstTrueBranch
import EvmCompiler.TypedCfg.VirtualStackCanon
import EvmCompiler.Assembly.Bytecode

namespace EvmCompiler
namespace Compiler
namespace StackArtifact

/-!
Compiler-owned artifact for the checked stack-allocation path.

The record retains the actual output of each adjacent compiler pass and the
existing TypedCfg certificate. It contains no memory-allocation policy, spill
plan, or source memory-safety evidence.
-/

structure Artifact where
  normalized : Functions.Program
  locals : Locals.Program
  expressions : Expressions.Program
  entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes
  cfg : TypedCfg.Program
  certified : TypedCfg.Program.CertifiedArtifact
  target : Assembly.TargetProgram

abbrev reorderedProgram (cfg : TypedCfg.Program) : TypedCfg.Program :=
  TypedCfg.ConstTrueBranch.optimizedProgram
    (TypedCfg.ShuffleCanon.chainCanonProgram
      (TypedCfg.Peephole.seamCancelProgramEff
        (TypedCfg.Peephole.peepholeProgram
          (TypedCfg.Peephole.normalizeProgram cfg))))

abbrev virtualProgram (cfg : TypedCfg.Program) : TypedCfg.Program :=
  TypedCfg.VirtualStack.canonProgram (reorderedProgram cfg)

/--
Fail-open gate for the virtual-stack layer.  The candidate must independently
type-check and lower, remain program-counter independent, and not increase the
whole-program execution fuel budget.
-/
def virtualCertified? (cfg : TypedCfg.Program) :
    Option TypedCfg.Program.CertifiedArtifact := do
  let candidate ← (virtualProgram cfg).compileCertified?
  if (virtualProgram cfg).programCounterIndependent? then
    pure ()
  else
    none
  if decide
      (TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
          (virtualProgram cfg) ≤
        TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
          (reorderedProgram cfg)) then
    some candidate
  else
    none

theorem virtualCertified?_parts
    {cfg : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    (hChoice : virtualCertified? cfg = some artifact) :
    (virtualProgram cfg).compileCertified? = some artifact ∧
      (virtualProgram cfg).ProgramCounterIndependent ∧
      TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
          (virtualProgram cfg) ≤
        TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
          (reorderedProgram cfg) := by
  unfold virtualCertified? at hChoice
  cases hCompile :
      (virtualProgram cfg).compileCertified? with
  | none =>
      simp [hCompile] at hChoice
  | some candidate =>
      simp only [hCompile, Option.bind_some] at hChoice
      by_cases hIndependent :
          (virtualProgram cfg).programCounterIndependent? = true
      · simp only [hIndependent, if_true, pure_bind] at hChoice
        by_cases hFuel :
            decide
                (TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    (virtualProgram cfg) ≤
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    (reorderedProgram cfg)) =
              true
        · simp only [hFuel, if_true, Option.some.injEq] at hChoice
          simp at hChoice
          subst artifact
          exact
            ⟨rfl,
              TypedCfg.Program.programCounterIndependent_of_check
                hIndependent,
              of_decide_eq_true hFuel⟩
        · have hFuelFalse :
              decide
                  (TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                      (virtualProgram cfg) ≤
                    TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                      (reorderedProgram cfg)) =
                false :=
            Bool.eq_false_of_not_eq_true hFuel
          simp [hFuelFalse] at hChoice
      · have hIndependentFalse :
            (virtualProgram cfg).programCounterIndependent? = false :=
          Bool.eq_false_of_not_eq_true hIndependent
        simp [hIndependentFalse] at hChoice

/-- The certified artifact chosen for a generated CFG under the chain-canon +
block-reorder splice (design (ii), fail-open on savings): the seam-cancelled
corrected program `Q` always lowers (its certificate `qc` is retained); the
chain-canonicalised `chainCanonProgram Q` is taken whenever it *also* lowers
(certificate `cc`); and `optimizedProgram (chainCanonProgram Q)` (constant-true
branch elimination followed by block reorder)
is taken on top of `cc` whenever *it* lowers, falling back to `cc` (then to `qc`)
otherwise.  Each layer can only be entered when the layer beneath it lowered, so
the chosen certificate can never regress below the shipped seam path. -/
def CertifiedChoice (cfg : TypedCfg.Program)
    (certified : TypedCfg.Program.CertifiedArtifact) : Prop :=
  ∃ qc,
    (TypedCfg.Peephole.seamCancelProgramEff
        (TypedCfg.Peephole.peepholeProgram
          (TypedCfg.Peephole.normalizeProgram cfg))).compileCertified? = some qc ∧
      certified =
        ((TypedCfg.ShuffleCanon.chainCanonProgram
          (TypedCfg.Peephole.seamCancelProgramEff
              (TypedCfg.Peephole.peepholeProgram
                (TypedCfg.Peephole.normalizeProgram cfg)))).compileCertified?).elim qc
          (fun cc =>
            ((reorderedProgram cfg).compileCertified?).elim cc
              (fun rc => (virtualCertified? cfg).getD rc))

def compile? (source : Functions.Program) : Option Artifact := do
  if Functions.SourceAcceptedCheck.Program.sourceAccepted? source then
    pure ()
  else
    none
  let normalized := Functions.StackPressureNormalization.Program.normalize source
  if Functions.SourceAcceptedCheck.Program.sourceAccepted? normalized then
    pure ()
  else
    none
  let locals ← Functions.StackLowering.lowerProgram? normalized
  let expressions ← Locals.Program.toExpressions? locals
  if Structured.SourceAcceptedCheck.Program.wf?
      expressions.toStructured then
    pure ()
  else
    none
  let entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes := []
  let generated ←
    Structured.TypedCfgCompiler.artifactWithProcEntryShapes?
      expressions.toStructured entryShapes
  let cfg := generated.cfg
  if cfg.programCounterIndependent? then
    pure ()
  else
    none
  let qcertified ←
    (TypedCfg.Peephole.seamCancelProgramEff
      (TypedCfg.Peephole.peepholeProgram
        (TypedCfg.Peephole.normalizeProgram cfg))).compileCertified?
  let certified :=
    ((TypedCfg.ShuffleCanon.chainCanonProgram
      (TypedCfg.Peephole.seamCancelProgramEff
          (TypedCfg.Peephole.peepholeProgram
            (TypedCfg.Peephole.normalizeProgram cfg)))).compileCertified?).elim qcertified
      (fun cc =>
        ((reorderedProgram cfg).compileCertified?).elim cc
          (fun rc => (virtualCertified? cfg).getD rc))
  let target ← Assembly.compileExecutable? certified.target
  if Assembly.Bytecode.targetFitsDecodeWindow? target then
    if Functions.OpenSupportCheck.Program.openSupported? source then
      if Functions.OpenSupportCheck.Program.openSupported? normalized then
        some { normalized, locals, expressions, entryShapes, cfg, certified, target }
      else
        none
    else
      none
  else
    none

theorem compile?_parts
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    artifact.normalized =
        Functions.StackPressureNormalization.Program.normalize source ∧
      Functions.InteractionSemantics.Program.OpenSupported source ∧
      Functions.InteractionSemantics.Program.OpenSupported
        artifact.normalized ∧
      Functions.StackLowering.lowerProgram? artifact.normalized =
        some artifact.locals ∧
      Locals.Program.toExpressions? artifact.locals =
        some artifact.expressions ∧
      artifact.expressions.toStructured.WF ∧
      artifact.entryShapes = [] ∧
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          artifact.expressions.toStructured artifact.entryShapes =
        some artifact.cfg ∧
      artifact.cfg.WellTyped ∧
      artifact.cfg.ProgramCounterIndependent ∧
      CertifiedChoice artifact.cfg artifact.certified ∧
      Assembly.compileExecutable? artifact.certified.target =
        some artifact.target ∧
      Assembly.Bytecode.TargetFitsDecodeWindow artifact.target ∧
      artifact.normalized.SourceAccepted ∧
      source.SourceAccepted := by
  have hSourceAcceptedCheck :
      Functions.SourceAcceptedCheck.Program.sourceAccepted? source = true := by
    by_contra hNot
    have hFalse :
        Functions.SourceAcceptedCheck.Program.sourceAccepted? source = false :=
      Bool.eq_false_of_not_eq_true hNot
    simp [compile?, hFalse] at hCompile
  have hSourceAccepted : source.SourceAccepted :=
    Functions.SourceAcceptedCheck.Program.sourceAccepted_of_check
      hSourceAcceptedCheck
  have hNormalizedAcceptedCheck :
      Functions.SourceAcceptedCheck.Program.sourceAccepted?
          (Functions.StackPressureNormalization.Program.normalize source) =
        true := by
    by_contra hNot
    have hFalse :
        Functions.SourceAcceptedCheck.Program.sourceAccepted?
            (Functions.StackPressureNormalization.Program.normalize source) =
          false := Bool.eq_false_of_not_eq_true hNot
    simp [compile?, hSourceAcceptedCheck, hFalse] at hCompile
  have hNormalizedAccepted :
      (Functions.StackPressureNormalization.Program.normalize source).SourceAccepted :=
    Functions.SourceAcceptedCheck.Program.sourceAccepted_of_check
      hNormalizedAcceptedCheck
  unfold compile? at hCompile
  simp only [hSourceAcceptedCheck, hNormalizedAcceptedCheck, if_true,
    pure_bind] at hCompile
  cases hLocals : Functions.StackLowering.lowerProgram?
      (Functions.StackPressureNormalization.Program.normalize source) with
  | none => simp [hLocals] at hCompile
  | some locals =>
      cases hExpressions : Locals.Program.toExpressions? locals with
      | none => simp [hLocals, hExpressions] at hCompile
      | some expressions =>
          by_cases hWF :
              Structured.SourceAcceptedCheck.Program.wf?
                  expressions.toStructured = true
          · simp [hLocals, hExpressions, hWF] at hCompile
            cases hGenerated :
                Structured.TypedCfgCompiler.artifactWithProcEntryShapes?
                  expressions.toStructured [] with
            | none => simp [hGenerated] at hCompile
            | some generated =>
                simp [hGenerated] at hCompile
                by_cases hIndependent :
                    generated.cfg.programCounterIndependent? = true
                · simp [hIndependent] at hCompile
                  cases hQCert :
                      (TypedCfg.Peephole.seamCancelProgramEff
                        (TypedCfg.Peephole.peepholeProgram
                          (TypedCfg.Peephole.normalizeProgram
                            generated.cfg))).compileCertified? with
                  | none => simp [hQCert] at hCompile
                  | some qc =>
                      simp [hQCert] at hCompile
                      set certified :=
                        ((TypedCfg.ShuffleCanon.chainCanonProgram
                          (TypedCfg.Peephole.seamCancelProgramEff
                            (TypedCfg.Peephole.peepholeProgram
                              (TypedCfg.Peephole.normalizeProgram
                                generated.cfg)))).compileCertified?).elim qc
                          (fun cc =>
                            ((reorderedProgram generated.cfg).compileCertified?).elim cc
                              (fun rc =>
                                (virtualCertified? generated.cfg).getD rc))
                          with hCertifiedDef
                      cases hTarget :
                          Assembly.compileExecutable? certified.target with
                      | none => simp [hTarget] at hCompile
                      | some target =>
                          simp [hTarget] at hCompile
                          by_cases hWindow :
                              Assembly.Bytecode.targetFitsDecodeWindow?
                                  target = true
                          · by_cases hSupported :
                                Functions.OpenSupportCheck.Program.openSupported?
                                    source = true
                            · by_cases hNormalizedSupported :
                                  Functions.OpenSupportCheck.Program.openSupported?
                                    (Functions.StackPressureNormalization.Program.normalize
                                      source) = true
                              · simp [hWindow, hSupported, hNormalizedSupported]
                                  at hCompile
                                cases hCompile
                                refine
                                  ⟨rfl,
                                    Functions.OpenSupportCheck.Program.openSupported_of_check
                                      hSupported,
                                    Functions.OpenSupportCheck.Program.openSupported_of_check
                                      hNormalizedSupported,
                                    by simpa using hLocals,
                                    by simpa using hExpressions,
                                    Structured.SourceAcceptedCheck.Program.wf_of_check
                                      hWF,
                                    rfl, ?_, ?_, ?_, ⟨qc, hQCert, hCertifiedDef⟩,
                                    hTarget, ?_⟩
                                · exact
                                    Structured.TypedCfgCompiler.artifactWithProcEntryShapes?_generate
                                      hGenerated
                                · exact generated.wellTyped
                                · exact
                                    TypedCfg.Program.programCounterIndependent_of_check
                                      hIndependent
                                · exact
                                    ⟨Assembly.Bytecode.targetFitsDecodeWindow_of_check
                                        hWindow,
                                      hNormalizedAccepted, hSourceAccepted⟩
                              · simp [hWindow, hSupported, hNormalizedSupported]
                                  at hCompile
                            · simp [hWindow, hSupported] at hCompile
                          · simp [hWindow] at hCompile
                · simp [hIndependent] at hCompile
          · simp [hLocals, hExpressions, hWF] at hCompile

theorem compile?_sourceWF
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    artifact.expressions.toStructured.WF := by
  obtain ⟨_hNormalized, _hSupported, _hNormalizedSupported, _hLower,
      _hExpressions, hSourceWF, _hShapes, _hGenerate, _hWellTyped,
      _hIndependent, _hCertified, _hTarget, _hWindow,
      _hNormalizedAccepted, _hSourceAccepted⟩ :=
    compile?_parts hCompile
  exact hSourceWF

theorem compile?_openSupported
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    Functions.InteractionSemantics.Program.OpenSupported source :=
  (compile?_parts hCompile).2.1

theorem compile?_normalizedOpenSupported
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    Functions.InteractionSemantics.Program.OpenSupported artifact.normalized :=
  (compile?_parts hCompile).2.2.1

theorem compile?_frameSafe
    {source : Functions.Program} {artifact : Artifact}
    (_hCompile : compile? source = some artifact) :
    artifact.expressions.toStructured.FrameSafe :=
  Structured.Program.frameSafe artifact.expressions.toStructured

theorem compile?_assembly
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    Assembly.compile? artifact.certified.target = some artifact.target := by
  obtain ⟨_hNormalized, _hSupported, _hNormalizedSupported, _hLower,
      _hExpressions, _hSourceWF, _hShapes, _hGenerate, _hWellTyped,
      _hIndependent, _hCertified, hTarget, _hWindow,
      _hNormalizedAccepted, _hSourceAccepted⟩ :=
    compile?_parts hCompile
  rw [← Assembly.compileExecutable?_eq_compile?]
  exact hTarget

theorem compile?_decodingCorrect
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    Assembly.Bytecode.DecodingCorrect artifact.target
      (Assembly.Bytecode.encodeTarget artifact.target) := by
  have hAssembly := compile?_assembly hCompile
  obtain ⟨_hNormalized, _hSupported, _hNormalizedSupported, _hLower,
      _hExpressions, _hSourceWF, _hShapes, _hGenerate, _hWellTyped,
      _hIndependent, _hCertified, _hTarget, hWindow,
      _hNormalizedAccepted, _hSourceAccepted⟩ :=
    compile?_parts hCompile
  exact
    { decodes :=
        Assembly.Bytecode.compile_decode_correct hAssembly
          (Assembly.Bytecode.compile_decodeSafety hAssembly hWindow) }

theorem compile?_sourceAccepted
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    source.SourceAccepted := by
  obtain ⟨_hNormalized, _hSupported, _hNormalizedSupported, _hLower,
      _hExpressions, _hSourceWF, _hShapes, _hGenerate, _hWellTyped,
      _hIndependent, _hCertified, _hTarget, _hWindow,
      _hNormalizedAccepted, hSourceAccepted⟩ := compile?_parts hCompile
  exact hSourceAccepted

theorem compile?_normalizedSourceAccepted
    {source : Functions.Program} {artifact : Artifact}
    (hCompile : compile? source = some artifact) :
    artifact.normalized.SourceAccepted := by
  obtain ⟨_hNormalized, _hSupported, _hNormalizedSupported, _hLower,
      _hExpressions, _hSourceWF, _hShapes, _hGenerate, _hWellTyped,
      _hIndependent, _hCertified, _hTarget, _hWindow,
      hNormalizedAccepted, _hSourceAccepted⟩ := compile?_parts hCompile
  exact hNormalizedAccepted

end StackArtifact
end Compiler
end EvmCompiler
