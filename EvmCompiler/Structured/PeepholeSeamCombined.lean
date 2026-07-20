import EvmCompiler.Structured.PeepholeNoopSwapCombined
import EvmCompiler.TypedCfg.PeepholeSeamCancel

/-!
# The seam-cancelled combined transform `seamCancelProgram (peepholeProgram (normalizeProgram cfg))`
(session-66)

The splice route (PEEPHOLE_PROGRESS §Session-65 frontier).  We compose the
already-banked source-threaded combined congruence
(`openStep_combined_congr_of_source`, relating `cfg` to
`P := peepholeProgram (normalizeProgram cfg)`) with the banked whole-program
one-step seam-cancel congruence (`openStep_seamCancel_congr`, relating `P` to
`seamCancelProgram P`) via `Rel.trans`.

The seam leg's per-entry `StackRealizes (seamBlock P b0).input s_c` guard is
DERIVABLE, not axiomatic: `stackRealizes_of_realizedWitnessFC_total` on `cfg`,
transported through `findBlock?_{peephole,normalize}Program` +
`{peephole,normalize}Block_input`, then along `SameRuntimeData` stack equality
and the pending-swap / `remapShape` stack-**length** preservation carried by
`SeamStepRel`.

These lemmas have the argument shape of the combined `*_of_source` family, so the
OIC consumption sites swap `combined` → `seamCombined` names and supply the seam
guards.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-! ## Stack-length preservation support lemmas -/

/-- `remapShape` (the `0 ↔ d+1` transposition) preserves shape length. -/
@[simp] theorem remapShape_length (d : Nat) (s : Shape) :
    (remapShape d s).length = s.length := by
  simp [remapShape, Shape.length]

/-- `EvmYul.swap n` (when it succeeds) preserves the runtime stack length. -/
theorem swap_ok_stack_length {n : Nat} {s next : EVMState} (hn : 1 ≤ n)
    (h : EvmYul.swap n s = .ok next) : next.stack.length = s.stack.length := by
  have hlen : n + 1 ≤ s.stack.length := by
    unfold EvmYul.swap at h
    by_cases hc : (List.take (n + 1) s.stack).length = n + 1
    · rw [List.length_take] at hc; omega
    · rw [if_neg hc] at h; simp at h
  obtain ⟨top, last, front, suffix, hStack, hfront⟩ :=
    exists_swap_decomp s.stack n hn hlen
  have h1 : EvmYul.swap n s =
      .ok (s.replaceStackAndIncrPC (last :: front ++ [top] ++ suffix)) := by
    have hsn := Assembly.StackShuffle.swap_snoc
      (state := s) (front := front) (suffix := suffix) (top := top) (last := last)
    rw [hfront] at hsn
    rw [← hStack] at hsn
    exact hsn
  rw [h1] at h
  injection h with h
  subst h
  have hstack :
      (s.replaceStackAndIncrPC (last :: front ++ [top] ++ suffix)).stack =
        last :: front ++ [top] ++ suffix := by
    simp [EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  rw [hstack, hStack]
  simp [List.length_append, Nat.add_comm, Nat.add_left_comm]

/-- A `PendingSwap` relates two states of equal runtime stack length. -/
theorem pendingSwap_stack_length {d : Nat} {s_c s_o : EVMState}
    (h : PendingSwap d s_c s_o) :
    s_o.stack.length = s_c.stack.length := by
  obtain ⟨next, hswap, hsync⟩ := h
  have h1 := swap_ok_stack_length (n := d + 1) (by omega) hswap
  have h2 := SameRuntimeData.stack_eq hsync
  rw [← h1, h2]

/-! ## The carried 3-tuple invariant + disjunctive combined outcome relation -/

/-- The 3-tuple invariant carried at each reached block entry across the combined
seam-cancel bisimulation: the ORIGINAL `cfg` state `s1` realizes the source
witness, is `SameRuntimeData` to an intermediate `P`-state `s2`, and that `P`-state
stands in the `SeamStepRel` (SRD unless the block tails a fired seam) to the
seam-cancelled state `s_c`. -/
def SeamCombinedStepRel {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite)
    (label : Label) (s1 s_c : EVMState) : Prop :=
  ∃ s2, realizedWitnessFC source cfg calls label s1 ∧
    SameRuntimeData s1 s2 ∧
    SeamStepRel (peepholeProgram (normalizeProgram cfg)) label s2 s_c

/-- The disjunctive one-step combined outcome relation.  Either both outcomes are
a `.jump` to the same successor carrying `SeamCombinedStepRel` there, or they are
plain `RuntimeOutcomeRel` (halts / fallthroughs / errors — always from re-synced,
witness-carrying states). -/
def SeamCombinedOutcomeRel {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun a b =>
    (∃ (next : Label) (s1 s_c : EVMState),
      a = .ok (.jump next s1) ∧ b = .ok (.jump next s_c) ∧
        SeamCombinedStepRel (source := source) (cfg := cfg) calls next s1 s_c)
    ∨ (InteractionCongruence.Block.RuntimeOutcomeRel a b ∧
        ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s))

/-! ## Source-threaded one-step seam-combined congruence -/

/-- **Source-threaded one-step seam-combined congruence.**  `Rel.trans` of the
combined step (source-threaded, LEFT tree `cfg`, carrying the successor witness)
and the seam-cancel step (`program := peepholeProgram (normalizeProgram cfg)`).
The seam leg's per-entry `StackRealizes` guard is derived from the source witness
transported through the pass block-input equalities and `SeamStepRel`'s
stack-length preservation. -/
theorem openStep_seamCombined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Label} {state1 s_c : EVMState}
    (hStep : SeamCombinedStepRel (source := source) (cfg := cfg)
      context.calls label state1 s_c) :
    Simulation.Interaction.Rel
      (SeamCombinedOutcomeRel (source := source) (cfg := cfg) context.calls)
      (InteractionSemantics.Program.openStep cfg label state1)
      (InteractionSemantics.Program.openStep
        (seamCancelProgram (peepholeProgram (normalizeProgram cfg))) label s_c) := by
  obtain ⟨state2, hReal, hRel, hStepP⟩ := hStep
  set P := peepholeProgram (normalizeProgram cfg) with hP
  have hTypedP : P.WellTyped :=
    peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped)
  have hIndepP : P.ProgramCounterIndependent :=
    combined_programCounterIndependent hIndependent
  have hCombined :=
    openStep_combined_congr_of_source context hSourceWF hTyped hIndependent hReal hRel
  -- Derive the seam leg's per-entry `StackRealizes` guard.
  have hReal_cP : ∀ b0, P.findBlock? label = some b0 →
      StackRealizes (seamBlock P b0).input s_c := by
    intro b0 hFindP
    have hFindP' := hFindP
    rw [hP, findBlock?_peepholeProgram, findBlock?_normalizeProgram] at hFindP'
    cases hf0 : cfg.findBlock? label with
    | none => rw [hf0] at hFindP'; simp at hFindP'
    | some bcfg =>
        rw [hf0] at hFindP'
        simp only [Option.map_some, Option.some.injEq] at hFindP'
        have hInputEq : b0.input = bcfg.input := by rw [← hFindP']; simp
        have hRcfg : bcfg.input.length ≤ state1.stack.length :=
          Structured.TokenBottomThread.stackRealizes_of_realizedWitnessFC_total
            context hSourceWF hReal hf0
        have hLen12 : state1.stack.length = state2.stack.length :=
          congrArg List.length (SameRuntimeData.stack_eq hRel)
        rw [seamBlock_input]
        unfold StackRealizes
        cases htf : targetFire? P b0 with
        | none =>
            simp only [htf, hInputEq]
            simp only [SeamStepRel, hFindP, htf] at hStepP
            have h3 : state2.stack.length = s_c.stack.length :=
              congrArg List.length (SameRuntimeData.stack_eq hStepP)
            omega
        | some d =>
            simp only [htf, remapShape_length, hInputEq]
            simp only [SeamStepRel, hFindP, htf] at hStepP
            have h3 : state2.stack.length = s_c.stack.length :=
              pendingSwap_stack_length hStepP
            omega
  have hSeam :=
    openStep_seamCancel_congr (program := P) hTypedP.1 hTypedP hIndepP hReal_cP hStepP
  refine Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hCombined hSeam) ?_
  rintro x z ⟨y, hxy, hyz⟩
  cases hxy with
  | error he =>
      rcases hyz with hjump | hrr
      · obtain ⟨next, so, sc, hy, _, _⟩ := hjump
        exact absurd hy (by simp)
      · obtain ⟨hrrr, _⟩ := hrr
        cases hrrr with
        | error he2 => exact Or.inr ⟨.error (he.trans he2), by simp⟩
  | ok hok =>
      obtain ⟨hrr, hwit⟩ := hok
      rcases hyz with hjump | hrr2
      · obtain ⟨next, so, sc, hy, hz, hstepP⟩ := hjump
        rw [Except.ok.injEq] at hy
        subst hy
        cases hrr with
        | jump lbl hSt =>
            refine Or.inl ⟨next, _, sc, rfl, hz, ?_⟩
            exact ⟨so, hwit next _ rfl, hSt, hstepP⟩
      · obtain ⟨hrrz0, hnj⟩ := hrr2
        cases hrrz0 with
        | ok hrrz =>
            refine Or.inr ⟨.ok (Outcome.RuntimeRel.trans hrr hrrz), ?_⟩
            rintro n s hEq
            rw [Except.ok.injEq] at hEq
            subst hEq
            cases hrr with
            | jump lbl hSt => exact hnj _ _ rfl

/-! ## Source-threaded fuel + prefix seam-combined congruences -/

/-- **Source-threaded fuel-bounded seam-combined congruence.**  Threads the
`SeamCombinedStepRel` 3-tuple invariant across the fuel recursion.  The outcome
relation is `SeamCombinedOutcomeRel` (NOT clean: residual jumps carry the pending
invariant); the PREFIX lemma below collapses it to clean `RuntimeOutcomeRel`. -/
theorem openRunN_seamCombined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent) :
    ∀ (fuel : Nat) (label : Label) (state1 s_c : EVMState),
      SeamCombinedStepRel (source := source) (cfg := cfg) context.calls label state1 s_c →
      Simulation.Interaction.Rel
        (SeamCombinedOutcomeRel (source := source) (cfg := cfg) context.calls)
        (InteractionSemantics.Program.openRunN cfg fuel label state1)
        (InteractionSemantics.Program.openRunN
          (seamCancelProgram (peepholeProgram (normalizeProgram cfg))) fuel label s_c)
  | 0, label, state1, s_c, hStep => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (Or.inl ⟨label, state1, s_c, rfl, rfl, hStep⟩)
  | fuel + 1, label, state1, s_c, hStep => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStepOne :=
        openStep_seamCombined_congr_of_source context hSourceWF hTyped hIndependent hStep
      apply Simulation.Interaction.Rel.bind_custom hStepOne
      intro leftDone rightDone hOut
      rcases hOut with hjump | hterm
      · obtain ⟨next, s1', sc', h1, h2, hstep'⟩ := hjump
        subst h1; subst h2
        exact openRunN_seamCombined_congr_of_source context hSourceWF hTyped hIndependent
          fuel next s1' sc' hstep'
      · obtain ⟨hrr, hnj⟩ := hterm
        cases hrr with
        | error he => exact .done (Or.inr ⟨.error he, by simp⟩)
        | ok hrrr =>
            cases hrrr with
            | jump lbl hSt => exact absurd rfl (hnj _ _)
            | fallthrough hSt => exact .done (Or.inr ⟨.ok (.fallthrough hSt), by simp⟩)
            | returnDispatch hSt => exact .done (Or.inr ⟨.ok (.returnDispatch hSt), by simp⟩)
            | halt kind hSt => exact .done (Or.inr ⟨.ok (.halt kind hSt), by simp⟩)
            | invalid hSt => exact .done (Or.inr ⟨.ok (.invalid hSt), by simp⟩)

/-- **Source-threaded prefix seam-combined congruence.**  Collapses the
`SeamCombinedOutcomeRel` N-level relation to clean `Block.RuntimeOutcomeRel`: every
residual jump (the only place a pending-swap state surfaces) maps to `OutOfFuel` on
BOTH sides, and halts arise only from the re-synced `RuntimeOutcomeRel` disjunct.
This is exactly the OIC-consumable prefix shape. -/
theorem openRunNPrefix_seamCombined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    (fuel : Nat) (label : Label) (state1 s_c : EVMState)
    (hStep : SeamCombinedStepRel (source := source) (cfg := cfg)
      context.calls label state1 s_c) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix cfg fuel label state1)
      (InteractionSemantics.Program.openRunNPrefix
        (seamCancelProgram (peepholeProgram (normalizeProgram cfg))) fuel label s_c) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_seamCombined_congr_of_source context hSourceWF hTyped hIndependent
      fuel label state1 s_c hStep
  apply Simulation.Interaction.Rel.bind_custom hRun
  intro leftDone rightDone hOut
  rcases hOut with hjump | hterm
  · obtain ⟨next, s1', sc', h1, h2, _⟩ := hjump
    subst h1; subst h2
    exact .done (.error rfl)
  · obtain ⟨hrr, hnj⟩ := hterm
    cases hrr with
    | error he => exact .done (.error he)
    | ok hrrr =>
        cases hrrr with
        | jump lbl hSt => exact absurd rfl (hnj _ _)
        | fallthrough hSt => exact .done (.error rfl)
        | returnDispatch hSt => exact .done (.error rfl)
        | halt kind hSt => exact .done (.ok (Outcome.RuntimeRel.halt kind hSt))
        | invalid hSt => exact .done (.error rfl)

/-! ## Item 3: the seam-cancel fuel bound

`fuelBudget (seamCancelProgram P) ≤ fuelBudget P`.  Reduces (via
`seamCancelProgram_blocks` + `CompiledProgram.fuelBudget = (blocks.map
CompiledBlock.fuelBudget).sum`) to the per-block bound
`CompiledBlock.fuelBudget (seamBlock P b) ≤ CompiledBlock.fuelBudget b`.  In every
firing case the edited body is a `dropLast` / `tail` sub-list whose lowering has no
more bytes than the original (the dropped `swap` fragments are appended back on the
original side), and the terminator code length is unchanged (a source-firing block
has `term = .fallthrough B`, which lowers shape-independently to `[.jump B]`; a
target-only-firing block keeps its output). -/

/-- General append decomposition of `lowerBodyFrom?`. -/
theorem lowerBodyFrom?_append (A B : List Instr) (input : Shape) :
    Block.lowerBodyFrom? (A ++ B) input =
      (Block.lowerBodyFrom? A input).bind (fun p =>
        (Block.lowerBodyFrom? B p.2).bind (fun q => some (p.1 ++ q.1, q.2))) := by
  induction A generalizing input with
  | nil =>
      show Block.lowerBodyFrom? B input
          = (Block.lowerBodyFrom? B input).bind (fun q => some (q.1, q.2))
      cases Block.lowerBodyFrom? B input with
      | none => rfl
      | some q => rfl
  | cons a as ih =>
      rw [List.cons_append, lowerBodyFrom?_cons, lowerBodyFrom?_cons]
      cases Instr.lowerAt? a input with
      | none => rfl
      | some p =>
          simp only [Option.bind_some]
          rw [ih]
          cases Block.lowerBodyFrom? as p.2 with
          | none => rfl
          | some r =>
              simp only [Option.bind_some]
              cases Block.lowerBodyFrom? B r.2 with
              | none => rfl
              | some s => simp [List.append_assoc]

/-- The output shape of a successful lowering equals the `bodyType?` output. -/
theorem bodyType?_of_lowerBodyFrom? :
    ∀ (body : List Instr) {input : Shape} {code : Assembly.Program} {out : Shape},
      Block.lowerBodyFrom? body input = some (code, out) →
      Block.bodyType? body input = some out
  | [], input, code, out, h => by
      simp only [Block.lowerBodyFrom?, Option.some.injEq, Prod.mk.injEq] at h
      simp only [Block.bodyType?, h.2]
  | i :: rest, input, code, out, h => by
      rw [lowerBodyFrom?_cons, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, h2⟩ := h
      rw [Option.bind_eq_some_iff] at h2
      obtain ⟨q, hq, h3⟩ := h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h3
      rw [bodyType?_cons, Preservation.Instr.type?_eq_some_of_lowerAt? hp,
        Option.bind_some, bodyType?_of_lowerBodyFrom? rest hq, h3.2]

/-- `lowerBodyFrom?` of a single well-typed `swap` from its typed input. -/
theorem lowerBodyFrom?_singleton_swap {e : Nat} {input output : Shape}
    (hType : Instr.type? (.swap e) input = some output) :
    ∃ sc, Block.lowerBodyFrom? [Instr.swap e] input = some (sc, output) := by
  obtain ⟨sc, hsc⟩ := lowerAt?_swap_of_type? hType
  refine ⟨sc, ?_⟩
  rw [lowerBodyFrom?_cons, hsc]
  simp [Block.lowerBodyFrom?, Option.bind]

/-- **Per-block seam fuel bound.**  The seam-edited block lowers to no more bytes
than the original.  Four firing cases; the dropped head/tail swap fragments only
add bytes on the original side, and the fallthrough terminator (source-fire) lowers
shape-independently. -/
theorem compiledBlock_fuelBudget_seamBlock_le {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped)
    (hmem : b0 ∈ program.blocks) :
    InteractionSemantics.CompiledBlock.fuelBudget (seamBlock program b0) ≤
      InteractionSemantics.CompiledBlock.fuelBudget b0 := by
  have hTyped := blockWellTyped_of_mem hAll hmem
  have hBodyEq := seamBlock_body program b0
  have hInEq := seamBlock_input program b0
  have hOutEq := seamBlock_output program b0
  have hTermEq := seamBlock_term program b0
  cases hs : sourceFire? program b0 with
  | none =>
      cases ht : targetFire? program b0 with
      | none =>
          -- identity: seamBlock is `b0`.
          have : seamBlock program b0 = b0 := by
            unfold seamBlock; rw [hs, ht]
          rw [this]
      | some d =>
          -- target only: drop the head swap, re-type the input.
          obtain ⟨hdecomp, htype, hrest, hd16⟩ :=
            targetFire_body_facts hUnique hmem hTyped ht
          unfold InteractionSemantics.CompiledBlock.fuelBudget
          simp only [hBodyEq, hInEq, hOutEq, hTermEq, hs, ht]
          -- edited body = b0.body.tail, edited input = remapShape d b0.input,
          -- edited output = b0.output.
          cases hLowEdit : Block.lowerBodyFrom? b0.body.tail (remapShape d b0.input) with
          | none => simp
          | some pair =>
              obtain ⟨bc, o⟩ := pair
              have hoEq : o = b0.output := by
                have := bodyType?_of_lowerBodyFrom? b0.body.tail hLowEdit
                rw [hrest] at this; exact (Option.some.inj this).symm
              subst hoEq
              -- original: b0.body = swap d :: tail, lowers with the extra head fragment
              obtain ⟨hc, hhc⟩ := lowerAt?_swap_of_type? htype
              have hLowOrig : Block.lowerBodyFrom? b0.body b0.input
                  = some (hc ++ bc, b0.output) := by
                conv_lhs => rw [hdecomp]
                rw [lowerBodyFrom?_cons, hhc]
                simp [Option.bind, hLowEdit]
              simp only [hLowOrig, ↓reduceIte]
              cases hTerm : b0.term.lowerAt? b0.output with
              | none => simp
              | some tc => simp only [List.length_append]; omega
  | some e =>
      obtain ⟨hpreDrop, hswapType, hsplit⟩ := sourceFire_body_facts hTyped hs
      obtain ⟨bLabel, B, hterm, href, hfind, hla, hhd, hal, hbl⟩ := sourceFire?_spec hs
      have hTermJump : ∀ s : Shape, b0.term.lowerAt? s = some [Assembly.Instr.jump bLabel] := by
        intro s; rw [hterm]; rfl
      cases ht : targetFire? program b0 with
      | none =>
          -- source only: drop the trailing swap, re-type the output.
          unfold InteractionSemantics.CompiledBlock.fuelBudget
          simp only [hBodyEq, hInEq, hOutEq, hTermEq, hs, ht]
          cases hLowEdit : Block.lowerBodyFrom? b0.body.dropLast b0.input with
          | none => simp
          | some pair =>
              obtain ⟨bc, o⟩ := pair
              have hoEq : o = remapShape e b0.output := by
                have := bodyType?_of_lowerBodyFrom? b0.body.dropLast hLowEdit
                rw [hpreDrop] at this; exact (Option.some.inj this).symm
              subst hoEq
              obtain ⟨sc, hsc⟩ := lowerBodyFrom?_singleton_swap hswapType
              have hLowOrig : Block.lowerBodyFrom? b0.body b0.input
                  = some (bc ++ sc, b0.output) := by
                conv_lhs => rw [← hsplit]
                rw [lowerBodyFrom?_append, hLowEdit]
                simp [Option.bind, hsc]
              simp only [hLowOrig, ↓reduceIte, hTermJump, List.length_append]
              omega
      | some d =>
          -- both: drop head and tail swap.
          obtain ⟨hdecompH, htypeH, hrestH, hd16⟩ :=
            targetFire_body_facts hUnique hmem hTyped ht
          have hlen : 2 ≤ b0.body.length := hal
          have hhdSwap : b0.body.head? = some (Instr.swap d) :=
            head_swap_of_targetFire hUnique hmem ht
          have hd2 : b0.body.dropLast = Instr.swap d :: b0.body.dropLast.tail :=
            dropLast_head_tail hhdSwap hlen
          have hbeq : b0.body =
              Instr.swap d :: (b0.body.dropLast.tail ++ [Instr.swap e]) := by
            conv_lhs => rw [← hsplit, hd2]; rw [List.cons_append]
          have hpreP : Block.bodyType? b0.body.dropLast.tail (remapShape d b0.input)
              = some (remapShape e b0.output) := by
            have hh := hpreDrop; rw [hd2] at hh; exact bodyType?_dropHead_swap hh
          unfold InteractionSemantics.CompiledBlock.fuelBudget
          simp only [hBodyEq, hInEq, hOutEq, hTermEq, hs, ht]
          cases hLowEdit : Block.lowerBodyFrom? b0.body.dropLast.tail
              (remapShape d b0.input) with
          | none => simp
          | some pair =>
              obtain ⟨bc, o⟩ := pair
              have hoEq : o = remapShape e b0.output := by
                have := bodyType?_of_lowerBodyFrom? b0.body.dropLast.tail hLowEdit
                rw [hpreP] at this; exact (Option.some.inj this).symm
              subst hoEq
              obtain ⟨hc, hhc⟩ := lowerAt?_swap_of_type? htypeH
              obtain ⟨sc, hsc⟩ := lowerBodyFrom?_singleton_swap hswapType
              have hLowOrig : Block.lowerBodyFrom? b0.body b0.input
                  = some (hc ++ (bc ++ sc), b0.output) := by
                conv_lhs => rw [hbeq]
                rw [lowerBodyFrom?_cons, hhc]
                simp only [Option.bind, lowerBodyFrom?_append, hLowEdit, hsc]
              simp only [hLowOrig, ↓reduceIte, hTermJump, List.length_append]
              omega

/-- Whole-block-list seam fuel-budget monotonicity. -/
theorem fuelBudget_seamBlocks_le {program : Program}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped) :
    ∀ (blocks : List Block), (∀ b ∈ blocks, b ∈ program.blocks) →
      (blocks.map fun b =>
          InteractionSemantics.CompiledBlock.fuelBudget (seamBlock program b)).sum ≤
        (blocks.map InteractionSemantics.CompiledBlock.fuelBudget).sum
  | [], _ => by simp
  | b :: bs, hAllMem => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledBlock_fuelBudget_seamBlock_le hUnique hAll
          (hAllMem b (List.mem_cons_self ..)))
        (fuelBudget_seamBlocks_le hUnique hAll bs
          (fun b' hb' => hAllMem b' (List.mem_cons_of_mem _ hb')))

/-- **The seam cancellation does not increase the whole-program fuel budget.** -/
theorem fuelBudget_seamCancelProgram_le {program : Program}
    (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget (seamCancelProgram program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  rw [seamCancelProgram_blocks, List.map_map]
  obtain ⟨hUnique, hAll, _, _⟩ := hWT
  exact fuelBudget_seamBlocks_le hUnique hAll program.blocks (fun b hb => hb)

/-- **Combined seam fuel bound.**  `seamCancelProgram (peepholeProgram
(normalizeProgram cfg))` lowers to at most `cfg`'s whole-program fuel budget. -/
theorem fuelBudget_seamCombined_le (program : Program) (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget
        (seamCancelProgram (peepholeProgram (normalizeProgram program))) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program :=
  le_trans
    (fuelBudget_seamCancelProgram_le
      (peepholeProgram_wellTyped (normalizeProgram_wellTyped hWT)))
    (fuelBudget_combined_le program hWT)

end Peephole
end TypedCfg
end EvmCompiler
