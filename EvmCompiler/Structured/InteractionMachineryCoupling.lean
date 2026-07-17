import EvmCompiler.Structured.InteractionConstructCoupling

/-!
# Machinery-block successor suppliers (route-2 `hInv` machinery arms)

Session 33 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-32).

Sessions 27–31 banked the per-construct successor suppliers for the blocks that
ARE `compileStmtFuel?` heads (`realizedWitness_of_{if,call,code}_compile`,
`realizedWitness_of_dispatch_jump`).  The assembled provenance capstone additionally
has to classify the **non-head machinery/join blocks** that the `for`/`switch`
lowerings emit as reachable jump targets but which are NOT `compileStmtFuel?` heads:
the for-loop-condition block, the switch test / case-entry blocks, the default `pop`
block, and the nil-join block.  This module banks their successor suppliers — the
inputs the machinery disjuncts of the capstone's classification predicate feed the
`hInv` case split.

## `realizedWitness_of_condBlock_jump` — the condition-block machinery supplier

The **for-loop-condition** block (label `LabelSupply.label supply 0`) has exactly the
same shape as an `if`-condition head — `{ body := Code.toCfg cond, term := .jumpi
trueLabel falseLabel }` — differing only in that it is generated inside a `.for_`
lowering rather than being a `compileStmtFuel?` head.  Its successor story is
therefore identical to the `if` head's: its `openStep` is source-coupled to the
condition run by `Condition.DoneRel`, and `realizedWitness_of_branch_jump`
(session 27) reads the child `StateRel`/`SourceFrameFits` off the concrete first
jump.

This lemma packages that story generically, keyed on the block's `findBlock?` fact
(the exact fact the eventual `hInv` proof has in hand: `realizedWitness` carries
`cfg.findBlock? e = some block`, and the capstone identifies `block` as the
condition block) plus the condition's type/source facts (which the enclosing
`for` compile fact exposes via `Loop.components_of_compileStmtFuel?_for`).  It is a
direct composition of `openRunCondition_jumpi_toCfg` (the general condition-block
`DoneRel` producer, reused from the `if` path) with `realizedWitness_of_branch_jump`,
and subsumes the `if`-head condition case as well.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionMachineryCoupling

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**Condition-block (`.jumpi` over `Code.toCfg cond`) successor supplier.**

For any ambient CFG block at `entry` of the condition shape
`{ input, body := Code.toCfg cond, output, term := .jumpi trueLabel falseLabel }`
(the shape of both an `if`-condition head and a `for`-loop-condition machinery
block), whose condition types (`hType`) and requires one source word of output
(`hSource`), given the `realizedWitness` ingredients carried at the entry
(`SourceFrameFits input …` + `StateRel source tokens target`), any concrete first
jump to `(next, state')` lands a child `realizedWitness cfg next state'`, provided
the ambient CFG block at `next` expects the branch's residual shape
(`{ output with slots := output.slots.tail }`).

Proof: rewriting `openStep` through `findBlock?` (`hFind`) reduces it to the block's
`openRun`, which `openRunCondition_jumpi_toCfg` couples to the condition run by
`Condition.DoneRel`; `realizedWitness_of_branch_jump` reads off the child
`StateRel`/`SourceFrameFits` at `state'` and packages it with the target
`LabelShape`.
-/
theorem realizedWitness_of_condBlock_jump
    {cfg : TypedCfg.Program}
    {cond : Structured.Code} {input output : TypedCfg.Shape}
    {entry trueLabel falseLabel next : Assembly.Label}
    {source : RunState} {tokens : List Word}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := TypedCfgCompiler.Code.toCfg cond
            output := output
            term := .jumpi trueLabel falseLabel })
    (hType : TypedCfgCompiler.Code.type? cond input = some output)
    (hSource : TypedCfgCompiler.Shape.requireSourceWords? 1 output = some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape :
      TypedCfgPreservation.LabelShape cfg next
        { output with slots := output.slots.tail }) :
    realizedWitness cfg next state' := by
  have hDoneRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel trueLabel falseLabel tokens
          { output with slots := output.slots.tail })
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa using
      InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := entry) (trueLabel := trueLabel) (falseLabel := falseLabel)
        hType hSource hFits hRel
  exact
    InteractionRealizedWitnessSuccessor.realizedWitness_of_branch_jump
      hDoneRel hExec hLabelShape

end InteractionMachineryCoupling
end Structured
end EvmCompiler
