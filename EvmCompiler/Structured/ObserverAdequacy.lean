import EvmCompiler.Structured.ObserverPreservation

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy

/-!
Backward adequacy for the adjacent Structured-to-TypedCfg pass.

This module consumes only the existing Structured compiler, its TypedCfg
typing facts, the shared observer semantics, and the pass-owned state relation.
It does not reason about Assembly or bytecode execution.
-/

abbrev Trace := Assembly.ResourceTrace

namespace Stmt

/--
A well-typed TypedCfg halt cannot obtain missing operands from compiler-owned
return data. The shape-indexed relation therefore reconstructs the
corresponding observer-aware Structured terminal evaluation.
-/
theorem terminal_of_wellTyped_halt
    {transcript : Trace} {program : Structured.Program}
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {kind : Assembly.HaltKind}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {fuel : Nat}
    (hTyped : block.WellTyped cfg)
    (hTerm : block.term = .halt kind)
    (hRel :
      ObserverPreservation.StateRel.At
        block.output source tokens target trace) :
    ∃ finalEVM,
      Structured.Terminal.step kind source.source.evm =
          .ok finalEVM ∧
        ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM finalEVM))) := by
  have hArityShape :
      kind.argCount ≤ block.output.length :=
    TypedCfg.Block.halt_argCount_le_of_wellTyped hTyped hTerm
  have hAritySource :
      kind.argCount ≤ source.source.evm.stack.length :=
    Nat.le_trans hArityShape hRel.sourceStack
  obtain ⟨finalEVM, hStep⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind source.source.evm hAritySource
  exact
    ⟨finalEVM, hStep,
      Structured.EffectSemantics.Stmt.Eval.terminal hStep⟩

end Stmt

end ObserverAdequacy
end Structured
end EvmCompiler
