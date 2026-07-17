import EvmCompiler.Structured.InteractionBlockProvenance
import EvmCompiler.Structured.InteractionBranchPreservation
import EvmCompiler.Structured.InteractionCallPreservation

/-!
# Per-construct coupling suppliers (route-2 `hInv` arms at the OIC splice)

Session 30 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-29).

The route-B master lever `AllEntriesRealized.of_openStep_invariant`
(`TypedCfg/InteractionEntryRealized.lean:271`) reduces the whole peephole endgame
to one global `openStep`-jump invariant

    hInv : realizedWitness cfg e t →
           Executes (openStep cfg e t) transcript (.ok (.jump n s)) →
           realizedWitness cfg n s.

Sessions 27/28 banked the three per-terminator **successor legs**
(`realizedWitness_of_{branch,pure,dispatch}_jump`,
`InteractionRealizedWitnessSuccessor.lean`), each of which discharges the
conclusion GIVEN the *source coupling* at `e` (the branch `Rel (DoneRel …)`, the
call `openStep = pure …` equation, or the dispatch frame-boundary facts).  Session
29's `block_category` (`InteractionBlockProvenance.lean:79`) performs the outer
per-entry case split (main body / proc body / dispatch / programEnd) and discharges
the programEnd arm unconditionally.  The remaining frontier is obligation (1):
supply, at a reached compiled-construct entry, the source coupling the successor leg
consumes — which requires the source construct's *compile fact* at `e`
(route 2: recovered from the in-scope source run threaded at the OIC splice).

This module banks the **per-construct coupling suppliers**: for each compiled-body
construct, a single lemma that takes the construct's compile fact
(`compileStmtFuel? … = some result`) together with the `realizedWitness`
ingredients carried at the entry (`StateRel` + `SourceFrameFits`) and the reached
first jump, and produces the child `realizedWitness cfg next state'` directly.  Each
collapses the producer (`openStep_*_of_compileStmtFuel?`) → extraction
(`jump_state_rel_*`) → packager (`realizedWitness_of_stateRel`) chain into the exact
single form the eventual `hInv` proof invokes once provenance hands it the compile
fact for the block at `e`:

* `realizedWitness_of_if_compile` — the `if`/branch main-body/proc-body arm
  (producer `openStep_if_of_compileStmtFuel?` ∘ `realizedWitness_of_branch_jump`).
* `realizedWitness_of_call_compile` — the `call`/pure arm
  (producer `openStep_entry_of_compileStmtFuel?` ∘ `realizedWitness_of_pure_jump`).

The dispatch arm's supplier is already banked at the compile-fact-adjacent level:
`realizedWitness_of_dispatch_jump` (`InteractionRealizedWitnessSuccessor.lean:149`)
takes the `openStep_dispatch` frame-boundary facts directly.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionConstructCoupling

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**`if`/branch coupling supplier** (the compiled-`if` main-body/proc-body arm of the
`hInv` invariant).

Given the source `if`'s compile fact at a reached entry (`hCompile`), the ambient
`BlocksInProgram` fact, and the `realizedWitness` ingredients carried at the entry
(`SourceFrameFits input …` + `StateRel source tokens target`), any concrete first
jump out of the entry block lands a child `realizedWitness cfg next state'`,
provided the ambient CFG block at `next` expects the branch's residual body shape
(`result.fallthrough?`, i.e. the `restShape` the branch coupling carries).

Proof: `openStep_if_of_compileStmtFuel?` produces the branch coupling
`Rel (Condition.DoneRel (label supply 0) regular tokens bodyInput) …` and pins
`result.fallthrough? = some bodyInput`; `realizedWitness_of_branch_jump` (session 27)
reads off the child `StateRel`/`SourceFrameFits` at `state'` and packages it with the
target `LabelShape`. -/
theorem realizedWitness_of_if_compile
    {compilerFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape :
      ∀ restShape, result.fallthrough? = some restShape →
        TypedCfgPreservation.LabelShape cfg next restShape) :
    realizedWitness cfg next state' := by
  obtain
      ⟨output, bodyInput, bodyResult, _hBodyInputEq, _hBodyCompile,
        _hRequire, hFallthrough, hDoneRel⟩ :=
    InteractionBranchPreservation.Condition.openStep_if_of_compileStmtFuel?
      hCompile hBlocks hFits hRel
  exact
    InteractionRealizedWitnessSuccessor.realizedWitness_of_branch_jump
      hDoneRel hExec (hLabelShape bodyInput hFallthrough)

/--
**`call`/pure coupling supplier** (the compiled-`call` main-body/proc-body arm of
the `hInv` invariant).

Given the source `call`'s compile fact (`hCompile`) + the callee lookup (`hLookup`)
+ the `realizedWitness` entry `StateRel` (`hRel`) + the argument split (`hSplit`) +
`proc.WF`, any concrete first jump out of the call-site block lands the callee entry
`(ProcLabel.entry name, state')` with a child `realizedWitness cfg next state'`,
provided the ambient CFG block at the callee entry expects `childInput`
(`LabelShape`) and the pushed child frame fits (`SourceFrameFits`).

Proof: `openStep_entry_of_compileStmtFuel?` reduces the call-site `openStep` to the
silent `pure (.jump (ProcLabel.entry name) targetFinal)` and yields the child
`StateRel`; `realizedWitness_of_pure_jump` (session 27) forces `next = ProcLabel.entry
name`, transports the child `StateRel` to `state'`, and packages it with the target
`LabelShape`. -/
theorem realizedWitness_of_call_compile
    {compilerFuel : Nat} {name : Structured.Name} {proc : Structured.Proc}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {args callerStack : EvmYul.Stack Word}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {childInput : TypedCfg.Shape} {state' : EVMState}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hProcWF : proc.WF)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape :
      TypedCfgPreservation.LabelShape cfg (ProcLabel.entry name) childInput)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits childInput
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack proc.retc).evm.stack.length) :
    realizedWitness cfg next state' := by
  obtain ⟨targetFinal, hStep, hChildRel⟩ :=
    InteractionCallPreservation.Call.openStep_entry_of_compileStmtFuel?
      hLookup hCompile hBlocks hRel hSplit hProcWF
  exact
    InteractionRealizedWitnessSuccessor.realizedWitness_of_pure_jump
      hStep hChildRel hExec hLabelShape hFits

end InteractionConstructCoupling
end Structured
end EvmCompiler
