import EvmCompiler.Solidus.Bridge
import EvmCompiler.Solidus.Defs
import EvmCompiler.Solidus.SourceRun

/-!
# C6 triangulation containment (Solidus Arena freeze cone)

`Assembly.Compact.InteractionSemantics.openRunNResult` — the gas-free open
bytecode interpreter — appears directly in the public correctness statements
(`EvmCompiler.Solidus.compile_correct` and friends), yet its file
(`EvmCompiler/Assembly/Compact.lean`) cannot be hash-frozen: its `Instr` type
and instruction dispatch are shared with the mutable *compaction pass* that
contestants optimize. That leaves a statement-level symbol adversary-editable.

The audit's containment argument (FREEZE_DECISION.md, Part 5) claimed that an
adversary who redefines `openRunNResult` gains nothing, because the two frozen
conjuncts of the statement — the source-side `ForwardRel`/`ObservableDoneRel`
refinement and the gasful-side `RunRefinesOpenTotal` over the pinned
`EvmYul.EVM.X` — *triangulate* onto the interpreter's result and pin its
observable behavior regardless of its definition. This module converts that
prose into checked theorems.

## Why the symbol's definition is irrelevant

Every theorem here is **quantified over an arbitrary `openRun`** (of exactly
the type `openRunNResult` returns: `Simulation.Interaction EVMException
StepResult`). None mentions `openRunNResult`, `Assembly.Compact`, or any other
mutable symbol — only frozen freeze-cone vocabulary and pinned `EvmYul`. Since
the results hold for *all* `openRun`, they hold in particular for whatever an
adversary redefines `openRunNResult` to be: the corollary
"`openRunNResult := <anything>` still forces the observable outcome" is just
instantiation. That is precisely what makes leaving `openRunNResult` in a
mutable file sound.

## What is pinned

* `openRun_ok_agrees` / `openRun_success_pinned` / `openRun_revert_pinned`:
  if the pinned `EVM.X` result `gasful` is *not* a fault (`.ok _`), then
  `RunRefinesOpenTotal` forces `openRun` to actually **execute** its transcript
  to a terminal leaf that is `DoneRel`-related to `gasful` — i.e. the produced
  output bytes and the code-erased world (`OpenSameData`) match `EVM.X`
  exactly, and a revert is reported as a revert. The `outOfGas` /
  `exceptionalFrame` escape arms are unavailable there, because both *demand*
  `gasful = .error _`, and the adversary does not control `EVM.X`.
* `openRun_no_running_leaf`: consequently, when `EVM.X` does not fault the
  adversary cannot dodge by returning a still-`running` (non-halted) leaf; the
  interpreter must genuinely halt with `EVM.X`'s observable data.
* `doneRel_not_running` / `observableDoneRel_not_running`: neither frozen
  relation ever accepts a `.running` target leaf — the structural fact both
  sides of the triangulation rest on.
* `source_terminates_forces_open`: the source-side pin. If the source run
  genuinely terminates (its leaf is not a `Truncated` fuel-exhaustion), the
  `ForwardRel.truncated` arm is unavailable, so `openRun` must execute to an
  `ObservableDoneRel`-related leaf — pinning `openRun` against the *source* as
  well as against `EVM.X`.
* `runRefinesOpenTotal_inversion`: the full case analysis, exposing that the
  only two non-agreeing arms both require a genuine `EVM.X` fault.

Nothing here weakens to a vacuous claim: `DoneRel`/`ObservableDoneRel` are the
codebase's own observable-agreement relations, and the conclusions carry real
`Executes` witnesses tying `openRun`'s transcript behavior to `EVM.X`.
-/

namespace EvmCompiler
namespace Solidus
namespace OpenRunContainment

open Simulation
open Simulation.Interaction
open Assembly
open Assembly.GasfulBridge

/-- The type of the value in `openRunNResult`'s result position: an open
interaction over EVM exceptions producing an assembly step result. The
containment theorems quantify over this type; they never name the interpreter
that inhabits it. -/
abbrev OpenRun := Simulation.Interaction Assembly.EVMException Assembly.StepResult

/-- The pinned `EVM.X` result position: an `Except`-wrapped `EvmYul` execution
result over the assembly EVM state. -/
abbrev GasfulResult :=
  Except Assembly.EVMException (EvmYul.EVM.ExecutionResult Assembly.EVMState)

/-! ### The `.running` rejections both relations rest on -/

/-- The frozen gasful/open terminal relation never relates any charged result
to a *still-running* open leaf: every constructor of `DoneRel` produces a
`.halted` (or `.error`) target. This is the structural fact that stops an
adversary from satisfying the gasful conjunct with a bogus non-halting value. -/
theorem doneRel_not_running
    {gasful : GasfulResult} {state : Assembly.EVMState}
    (h : DoneRel gasful (.ok (.running state))) : False := by
  cases h

/-- The frozen source/open observable relation likewise never relates a
finished source value to a *still-running* open leaf: `regular`/`halt`/`revert`
all produce `.ok (.halted _)` and `error` produces `.error _`. This is the
source-side counterpart of `doneRel_not_running`. -/
theorem observableDoneRel_not_running
    {source :
      Except Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {state : Assembly.EVMState}
    (h : ObservableDoneRel source (.ok (.running state))) : False := by
  cases h

/-! ### Executes is deterministic along a fixed transcript -/

/-- Along one fixed concrete transcript, an interaction reaches a unique
terminal outcome: the transcript selects the answer at every suspension and a
`.done` leaf forces the empty transcript. Used to turn "there exists a
`DoneRel`-related leaf" into "the adversary's leaf *is* that value". -/
theorem executes_unique
    {Error : Type} {Result : Type}
    {interaction : Simulation.Interaction Error Result}
    {transcript : Simulation.Interaction.Transcript}
    {outcome₁ outcome₂ : Except Error Result}
    (h₁ : Executes interaction transcript outcome₁)
    (h₂ : Executes interaction transcript outcome₂) :
    outcome₁ = outcome₂ := by
  induction h₁ generalizing outcome₂ with
  | done outcome =>
      cases h₂ with
      | done => rfl
  | request answer tail ih =>
      cases h₂ with
      | request answer tail₂ => exact ih tail₂

/-! ### The gasful-side pin (conjunct B against `EVM.X`) -/

/--
Full inversion of the frozen gasful/open refinement: for an arbitrary
`openRun`, `RunRefinesOpenTotal gasful openRun transcript` lands in exactly one
of three shapes, and the only two that are *not* an observable agreement with
`gasful` both require `gasful = .error _` (a genuine `EVM.X` fault):

* **agreement** — `openRun` executes its transcript to a leaf `DoneRel`-related
  to `gasful`;
* **exceptional frame** — `gasful` is a non-structural fault and `openRun`
  executes to an error leaf;
* **out of gas** — `gasful` is the committal out-of-gas fault and `openRun`'s
  transcript is a genuine prefix.
-/
theorem runRefinesOpenTotal_inversion
    {gasful : GasfulResult} {openRun : OpenRun}
    {transcript : Simulation.Interaction.Transcript}
    (hTotal : RunRefinesOpenTotal gasful openRun transcript) :
    (∃ openDone,
        Executes openRun transcript openDone ∧ DoneRel gasful openDone) ∨
      (∃ gasErr openErr,
        gasful = .error gasErr ∧
          gasErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel ∧
          gasErr ≠ EvmYul.EVM.ExecutionException.StackOverflow ∧
          gasErr ≠ EvmYul.EVM.ExecutionException.BadJumpDestination ∧
          openErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel ∧
          Executes openRun transcript (.error openErr)) ∨
      (OutOfGasFrameSemantics gasful ∧ Follows openRun transcript) := by
  cases hTotal with
  | completed hExec hDone => exact .inl ⟨_, hExec, hDone⟩
  | exceptionalFrame hne1 hne2 hne3 hne4 hEq hExec =>
      exact .inr (.inl ⟨_, _, hEq, hne1, hne2, hne3, hne4, hExec⟩)
  | outOfGas hOOG hFollows => exact .inr (.inr ⟨hOOG, hFollows⟩)

/--
When the pinned `EVM.X` result is *not* a fault (`gasful = .ok _`),
`RunRefinesOpenTotal` forces the **agreement** arm: `openRun` actually executes
its transcript to a terminal leaf `DoneRel`-related to `gasful`. The two escape
arms are eliminated because each demands `gasful = .error _`. This is the core
containment step: the adversary cannot route a successful/reverting `EVM.X` run
through an escape hatch. -/
theorem openRun_ok_agrees
    {gasful : GasfulResult} {openRun : OpenRun}
    {transcript : Simulation.Interaction.Transcript}
    {result : EvmYul.EVM.ExecutionResult Assembly.EVMState}
    (hTotal : RunRefinesOpenTotal gasful openRun transcript)
    (hOk : gasful = .ok result) :
    ∃ openDone,
      Executes openRun transcript openDone ∧ DoneRel gasful openDone := by
  cases hTotal with
  | completed hExec hDone => exact ⟨_, hExec, hDone⟩
  | exceptionalFrame _ _ _ _ hEq _ =>
      rw [hOk] at hEq; simp at hEq
  | outOfGas hOOG _ =>
      have hHalt := hOOG.halted
      rw [hOk] at hHalt; simp at hHalt

/--
Observable success pin. If `EVM.X` succeeds (`gasful = .ok (.success g out)`)
then `openRun` executes its transcript to a `.halted` leaf whose **output
bytes equal `out`** and whose state is **`OpenSameData`-equal to `EVM.X`'s
success state `g`** (equal code-erased world: nonces, balances, storage,
transient storage, code — plus the protected frame-local data). The halt
*kind* is deliberately free — the codebase pins output, not the
stop/return/selfdestruct label. No adversarial `openRun` can satisfy the frozen
conjunct while producing different output or a different world. -/
theorem openRun_success_pinned
    {gasful : GasfulResult} {openRun : OpenRun}
    {transcript : Simulation.Interaction.Transcript}
    {g : Assembly.EVMState} {out : ByteArray}
    (hTotal : RunRefinesOpenTotal gasful openRun transcript)
    (hOk : gasful = .ok (.success g out)) :
    ∃ (halt : Assembly.Halt),
      Executes openRun transcript (.ok (.halted halt)) ∧
        halt.output = out ∧ OpenSameData g halt.state := by
  obtain ⟨openDone, hExec, hDone⟩ := openRun_ok_agrees hTotal hOk
  rw [hOk] at hDone
  cases hDone with
  | success hsame => exact ⟨_, hExec, rfl, hsame⟩

/--
Observable revert pin. If `EVM.X` reverts (`gasful = .ok (.revert gas out)`)
then `openRun` executes its transcript to a `.halted` leaf whose **kind is
`revert`** and whose **output bytes equal `out`**. -/
theorem openRun_revert_pinned
    {gasful : GasfulResult} {openRun : OpenRun}
    {transcript : Simulation.Interaction.Transcript}
    {gas : EvmYul.UInt256} {out : ByteArray}
    (hTotal : RunRefinesOpenTotal gasful openRun transcript)
    (hOk : gasful = .ok (.revert gas out)) :
    ∃ (halt : Assembly.Halt),
      Executes openRun transcript (.ok (.halted halt)) ∧
        halt.kind = .revert ∧ halt.output = out := by
  obtain ⟨openDone, hExec, hDone⟩ := openRun_ok_agrees hTotal hOk
  rw [hOk] at hDone
  cases hDone with
  | revert => exact ⟨_, hExec, rfl, rfl⟩

/--
No-dodge corollary. When `EVM.X` does not fault, `openRun` cannot terminate its
transcript in a still-`running` (non-halted) leaf: it is forced to halt with
`EVM.X`'s observable data. Combines the gasful pin (`openRun_ok_agrees`),
transcript determinism (`executes_unique`), and the `.running` rejection
(`doneRel_not_running`). This is the crisp statement that trivializing
`openRunNResult` (e.g. `fun .. => .done (.ok (.running default))`) makes the
frozen conjunct **unprovable** rather than vacuously true, for any funded valid
run. -/
theorem openRun_no_running_leaf
    {gasful : GasfulResult} {openRun : OpenRun}
    {transcript : Simulation.Interaction.Transcript}
    {result : EvmYul.EVM.ExecutionResult Assembly.EVMState}
    {state : Assembly.EVMState}
    (hTotal : RunRefinesOpenTotal gasful openRun transcript)
    (hOk : gasful = .ok result)
    (hRun : Executes openRun transcript (.ok (.running state))) : False := by
  obtain ⟨openDone, hExec, hDone⟩ := openRun_ok_agrees hTotal hOk
  have hEq : openDone = .ok (.running state) := executes_unique hExec hRun
  rw [hEq] at hDone
  exact doneRel_not_running hDone

/-! ### The source-side pin (conjunct A against the decoded source) -/

/--
Source-side triangulation. If the source run genuinely **terminates** — it
executes some transcript to a leaf `sourceDone` that is *not* a `Truncated`
fuel-exhaustion — then the `ForwardRel.truncated` escape arm is unavailable, so
`openRun` must execute the same transcript to a leaf `ObservableDoneRel`-related
to `sourceDone`. Thus for a terminating source, `openRun`'s observable outcome
is pinned against the decoded source (and, by `observableDoneRel_not_running`,
cannot be a still-running leaf) — the other leg of the triangulation. -/
theorem source_terminates_forces_open
    {source :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {openRun : OpenRun}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone :
      Except Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    (hForward :
      ForwardRel Yul.FunctionsInteractionPrimitive.Truncated
        ObservableDoneRel source openRun)
    (hExecSource : Executes source transcript sourceDone)
    (hNotTrunc :
      ∀ failure, sourceDone = .error failure →
        ¬ Yul.FunctionsInteractionPrimitive.Truncated failure) :
    ∃ openDone,
      Executes openRun transcript openDone ∧
        ObservableDoneRel sourceDone openDone := by
  rcases ForwardRel.executes_or_follows hForward hExecSource with
    ⟨failure, hEq, hTrunc, _⟩ | ⟨openDone, hExec, hRel⟩
  · exact absurd hTrunc (hNotTrunc failure hEq)
  · exact ⟨openDone, hExec, hRel⟩

/-! ### Capstone: both conjuncts together -/

/--
The full triangulation containment, stated over both frozen conjuncts at once
for an arbitrary `openRun`. Given

* **(A)** `ForwardRel Truncated ObservableDoneRel source openRun` and
* **(B)** `RunRefinesOpenTotal gasful openRun transcript`,

if the pinned `EVM.X` result is not a fault (`gasful = .ok result`), then
`openRun` executes its transcript to a single terminal leaf that is
**simultaneously** `DoneRel`-related to `gasful` (agreement with `EVM.X`:
output + code-erased world) *and* — whenever the source terminates at this same
transcript to a non-truncated leaf — `ObservableDoneRel`-related to that source
leaf. So any `openRun` satisfying both frozen conjuncts is pinned on both
sides; its definition cannot influence the observable outcome the theorem
asserts. Instantiating `openRun := openRunNResult ..` recovers the concrete C6
containment as a corollary. -/
theorem openRun_triangulated
    {source :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {openRun : OpenRun}
    {gasful : GasfulResult}
    {transcript : Simulation.Interaction.Transcript}
    {result : EvmYul.EVM.ExecutionResult Assembly.EVMState}
    (hForward :
      ForwardRel Yul.FunctionsInteractionPrimitive.Truncated
        ObservableDoneRel source openRun)
    (hTotal : RunRefinesOpenTotal gasful openRun transcript)
    (hOk : gasful = .ok result) :
    ∃ openDone,
      Executes openRun transcript openDone ∧
        DoneRel gasful openDone ∧
          (∀ sourceDone,
            Executes source transcript sourceDone →
              (∀ failure, sourceDone = .error failure →
                ¬ Yul.FunctionsInteractionPrimitive.Truncated failure) →
              ObservableDoneRel sourceDone openDone) := by
  obtain ⟨openDone, hExec, hDone⟩ := openRun_ok_agrees hTotal hOk
  refine ⟨openDone, hExec, hDone, ?_⟩
  intro sourceDone hExecSource hNotTrunc
  obtain ⟨openDone', hExec', hRel⟩ :=
    source_terminates_forces_open hForward hExecSource hNotTrunc
  have hEq : openDone' = openDone := executes_unique hExec' hExec
  rw [hEq] at hRel
  exact hRel

end OpenRunContainment
end Solidus
end EvmCompiler
