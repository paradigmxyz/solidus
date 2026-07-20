import EvmCompiler.Structured.InteractionMachineryCoupling
import EvmCompiler.Structured.InteractionCodeConstructCoupling

/-!
# Per-disjunct `hInv` dispatch — the machinery-block legs (session 40)

Session 40 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-39 frontier item 2).

The `hInv` `openStep`-jump invariant for `realized := realizedWitness cfg` is assembled
by case-splitting the entry block's `BlockGenShapeReg` classification and, per disjunct,
feeding the matching successor supplier the entry-side `realizedWitness` ingredients plus
the disjunct's enriched exact-target `LabelShape` field.  This module banks the two
machinery disjuncts whose successor shape coincides with the entry `input` — so the
`realizedWitness` frame-fit transports with NO extra hypothesis:

* `realizedWitness_of_nilJoin_dispatch` — the `nilJoin` disjunct (`{ body := [], output :=
  input, term := .jump exitLabel }`).  The join is a pure identity fallthrough; its child
  fits/`StateRel` are exactly the entry's, so the entry `realizedWitness` (unified to the
  join block by `findBlock?` uniqueness) feeds `realizedWitness_of_join_jump` directly with
  the disjunct's `hExit : LabelShape cfg exitLabel input`.

* `realizedWitness_of_terminalHalt_dispatch` — the `terminalHalt` disjunct.  A halt block
  never `Executes`-produces a jump, so the obligation is vacuous
  (`halt_openStep_no_jump`); no entry witness is even needed.

The remaining machinery disjuncts (`caseEntryPop` pop, `procAdapter` relabel) shift the
runtime stack / static shape, so their child fits is NOT the entry fits — those legs take
the transported fits as a hypothesis at the eventual capstone assembly and are deferred.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionHInvDispatch

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness realizedWitness_of_stateRel)

/--
**`nilJoin` disjunct `hInv` leg.**  From the entry `realizedWitness` (which, unified to the
join block by `findBlock?` uniqueness, supplies the entry `StateRel` + `SourceFrameFits
input`), the join block's `findBlock?` fact, the enriched exit `LabelShape`, and any
concrete first jump, land the child `realizedWitness cfg next state'` via
`realizedWitness_of_join_jump`. -/
theorem realizedWitness_of_nilJoin_dispatch
    {cfg : TypedCfg.Program}
    {entry exitLabel next : Assembly.Label} {input : TypedCfg.Shape}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitness cfg entry target)
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .jump exitLabel })
    (hExit : TypedCfgPreservation.LabelShape cfg exitLabel input)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitness cfg next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := input
          body := []
          output := input
          term := .jump exitLabel } :=
    Option.some.inj (hFindReal.symm.trans hFind)
  subst hBlockEq
  exact
    InteractionMachineryCoupling.realizedWitness_of_join_jump
      hFind hFits hStateRel hExec hExit

/--
**`terminalHalt` disjunct `hInv` leg.**  A halt block never `Executes`-produces a jump, so
the obligation is vacuous — `halt_openStep_no_jump` refutes `hExec`.  No entry witness is
required. -/
theorem realizedWitness_of_terminalHalt_dispatch
    {cfg : TypedCfg.Program}
    {entry next : Assembly.Label} {input : TypedCfg.Shape}
    {kind : Assembly.HaltKind}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .halt kind })
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitness cfg next state' :=
  (InteractionMachineryCoupling.halt_openStep_no_jump hFind hExec).elim

/--
**`codeHead` disjunct `hInv` leg.**  For a straight-line `.code` head block, the only
first jump falls through to `regular` (`next = regular`, exposed by
`jump_state_rel_of_outcome`).  This leg mirrors `realizedWitness_of_code_compile` but,
instead of consuming a `LabelShape cfg next expected` supplied at the CONCRETE jumped-to
`next`, it consumes the enriched `codeHead` field `hReg` (the threaded
`HRegular result cfg regular` form) and feeds it at the fallthrough shape once
`next = regular` is exposed — the fallthrough shape existing by
`fallthrough_code_of_compileStmtFuel?`. -/
theorem realizedWitness_of_codeHead_dispatch
    {cfg : TypedCfg.Program} {sourceProgram : Structured.Program}
    {compilerFuel sourceFuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular next : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.code code) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hReg :
      ∀ out, result.fallthrough? = some out →
        TypedCfgPreservation.LabelShape cfg regular out)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitness cfg next state' := by
  obtain ⟨expected, hFall⟩ :=
    TypedCfgCompilerFacts.Stmt.fallthrough_code_of_compileStmtFuel? hCompile
  have hRequire : result.requireFallthrough? expected = some () :=
    TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr (Or.inr hFall)
  have hProd :=
    InteractionControlPreservation.Stmt.openStep_code_of_compileStmtFuel?
      (sourceProgram := sourceProgram) (sourceFuel := sourceFuel)
      hCompile hBlocks hFits hRel
  obtain ⟨srcState, hNext, hStateRel, hFits'⟩ :=
    InteractionControlPreservation.OpenOutcome.jump_state_rel_of_outcome
      hRequire hProd hExec
      (fun _t _o hExec' =>
        InteractionConstructCoupling.stmt_openRun_code_only_regular hExec')
  subst hNext
  exact realizedWitness_of_stateRel (hReg expected hFall) hStateRel hFits'

/--
**`ifHead` disjunct `hInv` leg.**  An `if` head block is the condition block
`{ body := Code.toCfg cond, term := .jumpi bodyLabel regular }` (`bodyLabel =
LabelSupply.label supply 0`), so the first jump lands `next = if cond then bodyLabel else
regular` (exposed by `jump_state_rel_of_rel`).  Both targets expect the residual shape
`{ output with slots := output.slots.tail }` (the `if`'s fallthrough): the `regular` case
is the enriched `hReg` field; the `bodyLabel` case is the body entry, whose `LabelShape`
is derived from the body compile fact carried inside the `.if_` compile
(`components_of_compileStmtFuel?_if` → `of_compileBlockFuel?`).  The condition-block
`DoneRel` is built directly by `openRunCondition_jumpi_toCfg`, exactly as in
`realizedWitness_of_condBlock_jump`. -/
theorem realizedWitness_of_ifHead_dispatch
    {cfg : TypedCfg.Program}
    {compilerFuel : Nat} {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular next : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {source : RunState} {tokens : List Word} {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.if_ cond body) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hReg :
      ∀ out, result.fallthrough? = some out →
        TypedCfgPreservation.LabelShape cfg regular out)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitness cfg next state' := by
  obtain ⟨output, condition, bodyResult, hType, hSource, hHead,
      hBodyCompile, hBodyRequire, hResultEq⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
  have hCondMem :
      ({ label := entry
         input := input
         body := TypedCfgCompiler.Code.toCfg cond
         output := output
         term := .jumpi (LabelSupply.label supply 0) regular } :
        TypedCfg.Block) ∈ result.blocks := by
    rw [hResultEq]; simp
  have hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := TypedCfgCompiler.Code.toCfg cond
            output := output
            term := .jumpi (LabelSupply.label supply 0) regular } :=
    hBlocks _ hCondMem
  have hBodyBlocks : TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro blk hMem
    apply hBlocks
    rw [hResultEq]
    simp only [List.mem_cons]
    exact Or.inr hMem
  have hBodyLS :
      TypedCfgPreservation.LabelShape cfg (LabelSupply.label supply 0)
        { output with slots := output.slots.tail } :=
    TypedCfgPreservation.LabelShape.of_compileBlockFuel? hBodyCompile hBodyBlocks
  have hDoneRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens
          { output with slots := output.slots.tail })
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa using
      InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := entry) (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular) hType hSource hFits hRel
  obtain ⟨srcState, cnd, hNext, hStateRel, hFits'⟩ :=
    InteractionBranchPreservation.Condition.jump_state_rel_of_rel hDoneRel hExec
  have hLS :
      TypedCfgPreservation.LabelShape cfg next
        { output with slots := output.slots.tail } := by
    rw [hNext]
    cases cnd with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact hReg _ (by rw [hResultEq])
    | true =>
        simp only [if_true]
        exact hBodyLS
  exact realizedWitness_of_stateRel hLS hStateRel hFits'

/--
**`procAdapter` disjunct `hInv` leg.**  The proc-entry adapter block
`{ body := [.relabel relabelTarget], term := .jump bodyLabel }` is an unconditional jump,
so the enriched `hBodyShape : LabelShape cfg bodyLabel output` field is exactly the target
`LabelShape` `realizedWitness_of_adapter_jump` consumes; the entry `realizedWitness`
supplies the `StateRel` and (after unifying the block by `findBlock?` uniqueness) the entry
fits at `blockInput`.  The relabel shifts the STATIC shape (`blockInput → output`) so the
child fits at `output` is NOT the entry fits at `blockInput`; the concrete
`SourceFrameFits`-transport across the (runtime-no-op) relabel is taken here as the
source-quantified hypothesis `hTransport` and discharged at the capstone assembly, where
the proc's `procEntry`/body shapes are pinned. -/
theorem realizedWitness_of_procAdapter_dispatch
    {cfg : TypedCfg.Program}
    {entry bodyLabel next : Assembly.Label}
    {blockInput relabelTarget output : TypedCfg.Shape}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitness cfg entry target)
    (hType :
      TypedCfg.Instr.type? (.relabel relabelTarget) blockInput = some output)
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := blockInput
            body := [.relabel relabelTarget]
            output := output
            term := .jump bodyLabel })
    (hBodyShape : TypedCfgPreservation.LabelShape cfg bodyLabel output)
    (hTransport :
      ∀ n, TypedCfgCompiler.Shape.SourceFrameFits blockInput n →
        TypedCfgCompiler.Shape.SourceFrameFits output n)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitness cfg next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := blockInput
          body := [.relabel relabelTarget]
          output := output
          term := .jump bodyLabel } :=
    Option.some.inj (hFindReal.symm.trans hFind)
  subst hBlockEq
  exact
    InteractionMachineryCoupling.realizedWitness_of_adapter_jump
      hFind hType (hTransport _ hFits) hStateRel hExec hBodyShape

/--
**`caseEntryPop` disjunct `hInv` leg.**  The switch case-entry `pop` block
`{ body := [.pop], term := .jump label }` is an unconditional jump, so once the source
scrutinee pop is available the first jump lands `(label, targetFinal)` with the popped
`StateRel` (`openStep_pop_jump`); the enriched `hExit : LabelShape cfg label output` field
is exactly the target shape.  The source pop and the child fits at the shifted (popped)
shape `output` are taken here as the source-quantified hypothesis `hPopTransport` — the
pop existence follows from the switch's `requireSourceWords? 1` fact and the popped fits
from `sourceFrameFits_tail`, both pinned at the capstone assembly. -/
theorem realizedWitness_of_caseEntryPop_dispatch
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {entry label next : Assembly.Label} {input output : TypedCfg.Shape}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitness cfg entry target)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump label } ∈ result.blocks)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hExit : TypedCfgPreservation.LabelShape cfg label output)
    (hPopTransport :
      ∀ source : RunState,
        TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length →
        ∃ (stack : EvmYul.Stack Word) (value : Word),
          source.evm.stack.pop = some (stack, value) ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            (source.withEVM { source.evm with stack := stack }).evm.stack.length)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitness cfg next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits⟩ := hReal
  have hFindPop := hBlocks _ hMem
  have hBlockEq :
      block =
        { label := entry
          input := input
          body := [.pop]
          output := output
          term := .jump label } :=
    Option.some.inj (hFindReal.symm.trans hFindPop)
  subst hBlockEq
  obtain ⟨stack, value, hPop, hPopFits⟩ := hPopTransport source hFits
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    InteractionSwitchPreservation.Switch.openStep_pop_jump
      hBlocks hMem hType hStateRel hPop
  rw [hStep] at hExec
  cases hExec
  exact realizedWitness_of_stateRel hExit hFinalRel hPopFits

end InteractionHInvDispatch
end Structured
end EvmCompiler
