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

end InteractionHInvDispatch
end Structured
end EvmCompiler
