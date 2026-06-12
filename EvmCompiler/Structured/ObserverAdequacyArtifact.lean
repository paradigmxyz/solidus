import EvmCompiler.Structured.ObserverPreservation
import EvmCompiler.Structured.TypedCfgCompilerFacts

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy

abbrev Trace := Assembly.ResourceTrace

namespace OutcomeSimulation

/--
Pass-owned stack evidence for every Structured control outcome.

Regular execution records the compiler result's checked fallthrough shape.
Abrupt control records the corresponding typed destination carried by the
compiler context. Halts do not continue into another typed Structured fragment.
-/
def OutcomeArtifact {transcript : Trace}
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (outcome : ObserverSemantics.Outcome
      (transcript := transcript)) : Prop :=
  match outcome.mode with
  | .regular =>
      ∃ output,
        result.fallthrough? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .brk =>
      ∃ output,
        ctx.breakShape? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .cont =>
      ∃ output,
        ctx.continueShape? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .leave =>
      ∃ output,
        ctx.leaveShape? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .halt _ => True

/--
Pass-owned control evidence at a checked regular join. Unlike
`OutcomeArtifact`, this interface does not retain a particular compiler result;
it is the stable artifact transported through recursive switch and loop rules.
-/
def JoinArtifact {transcript : Trace}
    (ctx : TypedCfgCompiler.Context)
    (regularShape : TypedCfg.Shape)
    (outcome : ObserverSemantics.Outcome
      (transcript := transcript)) : Prop :=
  match outcome.mode with
  | .regular =>
      TypedCfgCompiler.Shape.SourceFrameFits regularShape
        outcome.state.source.evm.stack.length
  | .brk =>
      ∃ output,
        ctx.breakShape? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .cont =>
      ∃ output,
        ctx.continueShape? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .leave =>
      ∃ output,
        ctx.leaveShape? = some output ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            outcome.state.source.evm.stack.length
  | .halt _ => True

namespace OutcomeArtifact

theorem regular
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    (hArtifact : OutcomeArtifact result ctx outcome)
    (hMode : outcome.mode = .regular) :
    ∃ output,
      result.fallthrough? = some output ∧
        TypedCfgCompiler.Shape.SourceFrameFits output
          outcome.state.source.evm.stack.length := by
  simpa [OutcomeArtifact, hMode] using hArtifact

theorem replaceRegular
    {transcript : Trace}
    {oldResult newResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    (hArtifact : OutcomeArtifact oldResult ctx outcome)
    (hRegular :
      outcome.mode = .regular →
        ∃ output,
          newResult.fallthrough? = some output ∧
            TypedCfgCompiler.Shape.SourceFrameFits output
              outcome.state.source.evm.stack.length) :
    OutcomeArtifact newResult ctx outcome := by
  rcases outcome with ⟨state, mode⟩
  cases mode with
  | regular => exact hRegular rfl
  | brk => exact hArtifact
  | cont => exact hArtifact
  | leave => exact hArtifact
  | halt kind => trivial

theorem toJoin
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regularShape : TypedCfg.Shape}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    (hFallthrough : result.fallthrough? = some regularShape)
    (hArtifact : OutcomeArtifact result ctx outcome) :
    JoinArtifact ctx regularShape outcome := by
  rcases outcome with ⟨state, mode⟩
  cases mode with
  | regular =>
      obtain ⟨output, hOutput, hBound⟩ := hArtifact
      have hEq : output = regularShape :=
        Option.some.inj (hOutput.symm.trans hFallthrough)
      simpa [hEq] using hBound
  | brk => exact hArtifact
  | cont => exact hArtifact
  | leave => exact hArtifact
  | halt kind => trivial

theorem toJoin_of_requireFallthrough
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regularShape : TypedCfg.Shape}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    (hRequire :
      result.requireFallthrough? regularShape = some ())
    (hArtifact : OutcomeArtifact result ctx outcome) :
    JoinArtifact ctx regularShape outcome := by
  rcases outcome with ⟨state, mode⟩
  cases mode with
  | regular =>
      obtain ⟨output, hOutput, hBound⟩ := hArtifact
      rcases
          TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
            hRequire with
        hNoFallthrough | hMatchingFallthrough
      · rw [hNoFallthrough] at hOutput
        cases hOutput
      · have hEq : output = regularShape :=
          Option.some.inj (hOutput.symm.trans hMatchingFallthrough)
        simpa [hEq] using hBound
  | brk => exact hArtifact
  | cont => exact hArtifact
  | leave => exact hArtifact
  | halt kind => trivial

theorem ofJoin
    {transcript : Trace}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regularShape : TypedCfg.Shape}
    {outcome : ObserverSemantics.Outcome (transcript := transcript)}
    (hFallthrough : result.fallthrough? = some regularShape)
    (hArtifact : JoinArtifact ctx regularShape outcome) :
    OutcomeArtifact result ctx outcome := by
  rcases outcome with ⟨state, mode⟩
  cases mode with
  | regular => exact ⟨regularShape, hFallthrough, hArtifact⟩
  | brk => exact hArtifact
  | cont => exact hArtifact
  | leave => exact hArtifact
  | halt kind => trivial

end OutcomeArtifact

end OutcomeSimulation
end ObserverAdequacy
end Structured
end EvmCompiler
