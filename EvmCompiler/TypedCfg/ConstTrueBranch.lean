import EvmCompiler.TypedCfg.BlockReorderCanon
import EvmCompiler.TypedCfg.PeepholeOpen
import EvmCompiler.TypedCfg.PeepholeNoopSwapConj
import EvmCompiler.TypedCfg.PeepholeFuel

/-!
# Constant-true branch elimination

Generated loop headers contain blocks of the form

```
  prefix; push 1; jumpi target fallthrough
```

The condition is statically true.  This pass removes the trailing push and
replaces the conditional terminator with `jump target`.  It deliberately
recognises only the exact literal `1`, keeping the transform and its proof
surface narrow.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ConstTrueBranch

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

private def one : Word := EvmYul.UInt256.ofNat 1

/-- Eliminate an exact trailing `push 1; jumpi`. -/
def constTrueBlock (block : Block) : Block :=
  match block.body.getLast?, block.term with
  | some (.push value), .jumpi target _ =>
      if value = one then
        { block with
          body := block.body.dropLast
          output := block.output.pop 1
          term := .jump target }
      else
        block
  | _, _ => block

/-- Apply constant-true branch elimination independently to every block. -/
def constTrueProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map constTrueBlock }

/-- The final layout candidate used by the compiler. -/
def optimizedProgram (program : Program) : Program :=
  BlockReorder.reorderProgram (constTrueProgram program)

@[simp] theorem constTrueBlock_label (block : Block) :
    (constTrueBlock block).label = block.label := by
  cases hLast : block.body.getLast? with
  | none => simp [constTrueBlock, hLast]
  | some instr =>
      cases instr <;> cases hTerm : block.term <;>
        simp [constTrueBlock, hLast, hTerm] <;>
        split <;> rfl

@[simp] theorem constTrueBlock_input (block : Block) :
    (constTrueBlock block).input = block.input := by
  cases hLast : block.body.getLast? with
  | none => simp [constTrueBlock, hLast]
  | some instr =>
      cases instr <;> cases hTerm : block.term <;>
        simp [constTrueBlock, hLast, hTerm] <;>
        split <;> rfl

@[simp] theorem constTrueProgram_entry (program : Program) :
    (constTrueProgram program).entry = program.entry := rfl

@[simp] theorem constTrueProgram_blocks (program : Program) :
    (constTrueProgram program).blocks =
      program.blocks.map constTrueBlock := rfl

theorem findBlock?_constTrueProgram (program : Program) (label : Label) :
    (constTrueProgram program).findBlock? label =
      (program.findBlock? label).map constTrueBlock := by
  simp only [constTrueProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons block blocks ih =>
      simp only [List.map_cons, List.find?_cons, constTrueBlock_label]
      by_cases h : (block.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]
        exact ih

theorem labelShape?_constTrueProgram (program : Program) (label : Label) :
    (constTrueProgram program).labelShape? label =
      program.labelShape? label := by
  unfold Program.labelShape?
  rw [findBlock?_constTrueProgram]
  cases program.findBlock? label <;> simp

theorem labelsUnique_constTrueProgram {program : Program}
    (h : program.LabelsUnique) :
    (constTrueProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [constTrueProgram_blocks, List.pairwise_map]
  exact h.imp (fun hne => by simpa using hne)

theorem entry_findBlock?_constTrueProgram {program : Program}
    (h : program.findBlock? program.entry ≠ none) :
    (constTrueProgram program).findBlock?
        (constTrueProgram program).entry ≠ none := by
  rw [constTrueProgram_entry, findBlock?_constTrueProgram]
  cases hFind : program.findBlock? program.entry with
  | none => exact absurd hFind h
  | some block => simp

theorem constTrueBlock_definedLabels (block : Block) :
    (constTrueBlock block).term.definedLabels =
      block.term.definedLabels := by
  unfold constTrueBlock
  split
  next value target fallthrough hLast hTerm =>
    split <;> simp_all [Terminator.definedLabels]
  next => rfl

theorem emittedLabels_constTrueProgram (program : Program) :
    (constTrueProgram program).EmittedLabels =
      program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [constTrueProgram_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro block _
  simp [constTrueBlock_definedLabels]

theorem emittedLabelsUnique_constTrueProgram {program : Program}
    (h : program.EmittedLabelsUnique) :
    (constTrueProgram program).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique
  rw [emittedLabels_constTrueProgram]
  exact h

private theorem bodyType?_dropLast_push_one
    {body : List Instr} {input output : Shape}
    (hLast : body.getLast? = some (.push one))
    (hType : Block.bodyType? body input = some output) :
    Block.bodyType? body.dropLast input = some (output.pop 1) := by
  have hSplit : body.dropLast ++ [Instr.push one] = body :=
    List.dropLast_append_getLast? _ (Option.mem_def.mpr hLast)
  rw [← hSplit, Peephole.bodyType?_append,
    Option.bind_eq_some_iff] at hType
  obtain ⟨middle, hPrefix, hPush⟩ := hType
  simp only [Block.bodyType?, Instr.type?, Option.bind_eq_some_iff] at hPush
  obtain ⟨after, hAfter, hNil⟩ := hPush
  cases middle
  simpa [Shape.pop] using hPrefix

private theorem termType_constTrueProgram_eq
    (program : Program) (shape : Shape) (term : Terminator) :
    term.type? (constTrueProgram program) shape =
      term.type? program shape := by
  unfold Terminator.type?
  rw [show (constTrueProgram program).labelShape? =
      program.labelShape? from funext (labelShape?_constTrueProgram program)]

private theorem constTrueBlock_wellTyped
    {program : Program} {block : Block}
    (hTyped : block.WellTyped program) :
    (constTrueBlock block).WellTyped (constTrueProgram program) := by
  unfold constTrueBlock
  split
  next value target fallthrough hLast hTerm =>
    split
    next hValue =>
      subst value
      constructor
      · exact bodyType?_dropLast_push_one hLast hTyped.1
      · have hTermType := hTyped.2
        rw [hTerm] at hTermType
        rw [termType_constTrueProgram_eq]
        simp only [Terminator.type?, Terminator.typeWith?] at hTermType ⊢
        cases hOutput : block.output.slots with
        | nil => simp [hOutput] at hTermType
        | cons condition rest =>
            simp only [hOutput] at hTermType
            cases hTarget : program.labelShape? target with
            | none => simp [hTarget] at hTermType
            | some targetShape =>
                cases hFall : program.labelShape? fallthrough with
                | none => simp [hTarget, hFall] at hTermType
                | some fallShape =>
                    simp [hTarget, hFall] at hTermType
                    simp [Shape.pop, hOutput, hTarget, hTermType.1]
    next _ =>
      constructor
      · exact hTyped.1
      · rw [termType_constTrueProgram_eq]
        exact hTyped.2
  next =>
    constructor
    · exact hTyped.1
    · rw [termType_constTrueProgram_eq]
      exact hTyped.2

theorem wellTyped_constTrueProgram {program : Program}
    (hTyped : program.WellTyped) :
    (constTrueProgram program).WellTyped := by
  obtain ⟨hUnique, hBlocks, hEntry, hEmitted⟩ := hTyped
  refine ⟨labelsUnique_constTrueProgram hUnique, ?_,
    entry_findBlock?_constTrueProgram hEntry,
    emittedLabelsUnique_constTrueProgram hEmitted⟩
  unfold Program.AllBlocksTyped at hBlocks ⊢
  change (program.blocks.map constTrueBlock).Forall
    (fun block => block.WellTyped (constTrueProgram program))
  rw [List.forall_iff_forall_mem] at hBlocks ⊢
  intro block hMem
  obtain ⟨original, hOriginalMem, rfl⟩ := List.mem_map.mp hMem
  exact constTrueBlock_wellTyped (hBlocks original hOriginalMem)

private theorem forall_dropLast {p : Instr → Prop} {body : List Instr}
    (h : body.Forall p) : body.dropLast.Forall p := by
  rw [List.forall_iff_forall_mem] at h ⊢
  exact fun instr hMem => h instr (List.mem_of_mem_dropLast hMem)

theorem programCounterIndependent_constTrueProgram {program : Program}
    (h : program.ProgramCounterIndependent) :
    (constTrueProgram program).ProgramCounterIndependent := by
  unfold Program.ProgramCounterIndependent at h ⊢
  change (program.blocks.map constTrueBlock).Forall
    Block.ProgramCounterIndependent
  rw [List.forall_iff_forall_mem] at h ⊢
  intro block hMem
  obtain ⟨original, hOriginalMem, rfl⟩ := List.mem_map.mp hMem
  have hOriginal := h original hOriginalMem
  unfold Block.ProgramCounterIndependent at hOriginal ⊢
  cases hLast : original.body.getLast? with
  | none => simpa [constTrueBlock, hLast] using hOriginal
  | some instr =>
      cases instr <;> cases hTerm : original.term <;>
        try { simpa [constTrueBlock, hLast, hTerm] using hOriginal }
      by_cases hValue : ‹Word› = one
      · simpa [constTrueBlock, hLast, hTerm, hValue] using
          forall_dropLast hOriginal
      · simpa [constTrueBlock, hLast, hTerm, hValue] using hOriginal

private theorem push_one_pop_output
    {body : List Instr} {input output : Shape}
    (hLast : body.getLast? = some (.push one))
    (hType : Block.bodyType? body input = some output) :
    { output.pop 1 with
      slots := .literal one :: (output.pop 1).slots } = output := by
  have hSplit : body.dropLast ++ [Instr.push one] = body :=
    List.dropLast_append_getLast? _ (Option.mem_def.mpr hLast)
  rw [← hSplit, Peephole.bodyType?_append,
    Option.bind_eq_some_iff] at hType
  obtain ⟨middle, hPrefix, hPush⟩ := hType
  simp only [Block.bodyType?, Instr.type?] at hPush
  cases middle
  cases output
  rcases hPush with ⟨rfl, rfl⟩
  rfl

private theorem sameRuntimeData_push_pop
    {left right : EVMState} (hRel : SameRuntimeData left right) :
    SameRuntimeData
      { left.replaceStackAndIncrPC
          (left.stack.push one) (Assembly.pushPcDelta one) with
        stack := left.stack }
      right := by
  cases left
  cases right
  simp [SameRuntimeData, Assembly.eraseRuntimeControl] at hRel ⊢
  exact hRel

private theorem push_one_jumpi_runtimeRel
    {shape : Shape} {target fallthrough : Label}
    {left right : EVMState}
    (hRel : SameRuntimeData left right) :
    InteractionCongruence.Block.RuntimeOutcomeRel
      (Block.runTermChecked
        { shape with slots := .literal one :: shape.slots }
        (.jumpi target fallthrough)
        (left.replaceStackAndIncrPC
          (left.stack.push one) (Assembly.pushPcDelta one)))
      (Block.runTermChecked shape (.jump target) right) := by
  simp only [Block.runTermChecked, Block.runTerm]
  have hOne : one ≠ EvmYul.UInt256.ofNat 0 := by decide
  simp only [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]
  simp only [EvmYul.Stack.push, EvmYul.Stack.pop]
  rw [if_neg hOne]
  exact .ok (.jump target (by
    simpa [Assembly.SameRuntimeData, Assembly.eraseRuntimeControl, one]
      using hRel))

/-- Per-block open-semantics congruence for the constant-true edit. -/
theorem openRun_constTrueBlock_congr
    {program : Program} (block : Block) {left right : EVMState}
    (hTyped : block.WellTyped program)
    (hIndependent : block.ProgramCounterIndependent)
    (hRel : SameRuntimeData left right) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Block.openRun block left)
      (InteractionSemantics.Block.openRun (constTrueBlock block) right) := by
  unfold constTrueBlock
  split
  next value target fallthrough hLast hTerm =>
    split
    next hValue =>
      subst value
      have hSplit : block.body.dropLast ++ [Instr.push one] = block.body :=
        List.dropLast_append_getLast? _ (Option.mem_def.mpr hLast)
      have hPrefixType :=
        bodyType?_dropLast_push_one hLast hTyped.1
      have hPrefixRel :=
        InteractionCongruence.Block.openRunBody_runtimeRel
          hPrefixType (forall_dropLast hIndependent) hRel
      have hOutput := push_one_pop_output hLast hTyped.1
      unfold InteractionSemantics.Block.openRun Control.Block.run
      change Simulation.Interaction.Rel
        InteractionCongruence.Block.RuntimeOutcomeRel
        (do
          let (state', output) ←
            InteractionSemantics.Block.openRunBody
              block.body block.input left
          if output = block.output then
            match Block.runTermChecked block.output block.term state' with
            | .ok outcome => pure outcome
            | .error err => throw err
          else throw .InvalidInstruction)
        (do
          let (state', output) ←
            InteractionSemantics.Block.openRunBody
              block.body.dropLast block.input right
          if output = block.output.pop 1 then
            match Block.runTermChecked (block.output.pop 1)
                (.jump target) state' with
            | .ok outcome => pure outcome
            | .error err => throw err
          else throw .InvalidInstruction)
      conv =>
        lhs
        rw [← hSplit, Peephole.openRunBody_append]
      change Simulation.Interaction.Rel
        InteractionCongruence.Block.RuntimeOutcomeRel
        (Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (InteractionSemantics.Block.openRunBody
              block.body.dropLast block.input left)
            (fun result =>
              InteractionSemantics.Block.openRunBody
                [Instr.push one] result.2 result.1))
          (fun result =>
            if result.2 = block.output then
              match Block.runTermChecked block.output block.term result.1 with
              | .ok outcome => pure outcome
              | .error err => throw err
            else throw .InvalidInstruction))
        (Simulation.Interaction.bind
          (InteractionSemantics.Block.openRunBody
            block.body.dropLast block.input right)
          (fun result =>
            if result.2 = block.output.pop 1 then
              match Block.runTermChecked (block.output.pop 1)
                  (.jump target) result.1 with
              | .ok outcome => pure outcome
              | .error err => throw err
            else throw .InvalidInstruction))
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.Rel.bind hPrefixRel
      intro leftPair rightPair hPair
      rcases leftPair with ⟨leftAfter, leftShape⟩
      rcases rightPair with ⟨rightAfter, rightShape⟩
      rcases hPair with ⟨hAfter, hLeftShape, hRightShape⟩
      change SameRuntimeData leftAfter rightAfter at hAfter
      change leftShape = block.output.pop 1 at hLeftShape
      change rightShape = block.output.pop 1 at hRightShape
      subst leftShape
      subst rightShape
      rw [Peephole.openRunBody_push_cons]
      simp only [InteractionSemantics.Block.openRunBody,
        Control.Block.runBody, Simulation.Interaction.bind_done_ok]
      rw [hOutput]
      simp only [↓reduceIte, hTerm]
      have hLeaf :
          InteractionCongruence.Block.RuntimeOutcomeRel
            (Block.runTermChecked block.output
              (.jumpi target fallthrough)
              (leftAfter.replaceStackAndIncrPC
                (leftAfter.stack.push one) (Assembly.pushPcDelta one)))
            (Block.runTermChecked (block.output.pop 1)
              (.jump target) rightAfter) := by
        simpa only [hOutput] using
          (push_one_jumpi_runtimeRel
            (shape := block.output.pop 1)
            (target := target) (fallthrough := fallthrough) hAfter)
      simp only [Block.runTermChecked_jumpi,
        Block.runTermChecked_jump] at hLeaf ⊢
      simp only [Simulation.Interaction.instMonad,
        Simulation.Interaction.pure]
      rw [Simulation.Interaction.bind_done_ok]
      simp only [↓reduceIte]
      exact .done hLeaf
    next _ =>
      simpa using InteractionCongruence.Block.openRun_runtimeRel
        hTyped hIndependent hRel
  next =>
    simpa using InteractionCongruence.Block.openRun_runtimeRel
      hTyped hIndependent hRel

/-- One-step whole-program congruence. -/
theorem openStep_constTrueProgram_congr
    {program : Program} {label : Label} {left right : EVMState}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hRel : SameRuntimeData left right) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openStep program label left)
      (InteractionSemantics.Program.openStep
        (constTrueProgram program) label right) := by
  unfold InteractionSemantics.Program.openStep Control.Program.step
  rw [findBlock?_constTrueProgram]
  cases hFind : program.findBlock? label with
  | none =>
      simp only [hFind, Option.map_none]
      exact .done (.ok (Outcome.RuntimeRel.invalid hRel))
  | some block =>
      simp only [hFind, Option.map_some]
      have hMem : block ∈ program.blocks :=
        List.mem_of_find?_eq_some hFind
      have hBlockTyped : block.WellTyped program :=
        (List.forall_iff_forall_mem.mp hTyped.2.1) block hMem
      have hBlockIndependent : block.ProgramCounterIndependent :=
        (List.forall_iff_forall_mem.mp hIndependent) block hMem
      have h1 :=
        InteractionCongruence.Block.openRun_runtimeRel
          hBlockTyped hBlockIndependent hRel
      have h2 :=
        openRun_constTrueBlock_congr block
          hBlockTyped hBlockIndependent (SameRuntimeData.refl right)
      refine Simulation.Interaction.Rel.mono
        (Simulation.Interaction.Rel.trans h1 h2) ?_
      rintro l r ⟨middle, hl, hr⟩
      exact Peephole.runtimeOutcomeRel_trans hl hr

/-- Fuel-bounded whole-program congruence. -/
theorem openRunN_constTrueProgram_congr
    {program : Program}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent) :
    ∀ (fuel : Nat) (label : Label) (left right : EVMState),
      SameRuntimeData left right →
      Simulation.Interaction.Rel
        InteractionCongruence.Block.RuntimeOutcomeRel
        (InteractionSemantics.Program.openRunN program fuel label left)
        (InteractionSemantics.Program.openRunN
          (constTrueProgram program) fuel label right)
  | 0, label, left, right, hRel => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (.ok (Outcome.RuntimeRel.jump label hRel))
  | fuel + 1, label, left, right, hRel => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStep := openStep_constTrueProgram_congr
        hTyped hIndependent hRel (label := label)
      apply Simulation.Interaction.Rel.bind hStep
      intro leftOutcome rightOutcome hOutcome
      cases hOutcome with
      | jump next hState =>
          exact openRunN_constTrueProgram_congr hTyped hIndependent
            fuel next _ _ hState
      | fallthrough hState =>
          exact .done (.ok (Outcome.RuntimeRel.fallthrough hState))
      | returnDispatch hState =>
          exact .done (.ok (Outcome.RuntimeRel.returnDispatch hState))
      | halt kind hState =>
          exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
      | invalid hState =>
          exact .done (.ok (Outcome.RuntimeRel.invalid hState))

/-- Canonical finite-prefix congruence. -/
theorem openRunNPrefix_constTrueProgram_congr
    {program : Program}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (fuel : Nat) (label : Label) (left right : EVMState)
    (hRel : SameRuntimeData left right) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix
        program fuel label left)
      (InteractionSemantics.Program.openRunNPrefix
        (constTrueProgram program) fuel label right) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun := openRunN_constTrueProgram_congr
    hTyped hIndependent fuel label left right hRel
  apply Simulation.Interaction.Rel.bind hRun
  intro leftOutcome rightOutcome hOutcome
  cases hOutcome with
  | halt kind hState =>
      exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
  | jump next hState =>
      exact .done (.error rfl)
  | fallthrough hState =>
      exact .done (.error rfl)
  | returnDispatch hState =>
      exact .done (.error rfl)
  | invalid hState =>
      exact .done (.error rfl)

private theorem lowerBodyFrom?_append
    (first second : List Instr) (input : Shape) :
    Block.lowerBodyFrom? (first ++ second) input =
      (Block.lowerBodyFrom? first input).bind (fun firstResult =>
        (Block.lowerBodyFrom? second firstResult.2).bind
          (fun secondResult =>
            some (firstResult.1 ++ secondResult.1, secondResult.2))) := by
  induction first generalizing input with
  | nil =>
      simp [Block.lowerBodyFrom?]
  | cons instr rest ih =>
      rw [List.cons_append, Peephole.lowerBodyFrom?_cons,
        Peephole.lowerBodyFrom?_cons]
      cases Instr.lowerAt? instr input with
      | none => rfl
      | some head =>
          simp only [Option.bind_some]
          rw [ih]
          cases Block.lowerBodyFrom? rest head.2 with
          | none => rfl
          | some middle =>
              simp only [Option.bind_some]
              cases Block.lowerBodyFrom? second middle.2 with
              | none => rfl
              | some tail => simp [List.append_assoc]

private theorem bodyType?_of_lowerBodyFrom? :
    ∀ (body : List Instr) {input : Shape}
      {code : Assembly.Program} {output : Shape},
      Block.lowerBodyFrom? body input = some (code, output) →
      Block.bodyType? body input = some output
  | [], input, code, output, h => by
      simp only [Block.lowerBodyFrom?, Option.some.injEq,
        Prod.mk.injEq] at h
      simp only [Block.bodyType?, h.2]
  | instr :: rest, input, code, output, h => by
      rw [Peephole.lowerBodyFrom?_cons,
        Option.bind_eq_some_iff] at h
      obtain ⟨head, hHead, hRest⟩ := h
      rw [Option.bind_eq_some_iff] at hRest
      obtain ⟨tail, hTail, hResult⟩ := hRest
      simp only [Option.some.injEq, Prod.mk.injEq] at hResult
      rw [Peephole.bodyType?_cons,
        Preservation.Instr.type?_eq_some_of_lowerAt? hHead,
        Option.bind_some,
        bodyType?_of_lowerBodyFrom? rest hTail, hResult.2]

private theorem compiledBlock_fuelBudget_constTrueBlock_le
    (block : Block)
    (hType : Block.bodyType? block.body block.input =
      some block.output) :
    InteractionSemantics.CompiledBlock.fuelBudget
        (constTrueBlock block) ≤
      InteractionSemantics.CompiledBlock.fuelBudget block := by
  unfold constTrueBlock
  split
  next value target fallthrough hLast hTerm =>
    split
    next hValue =>
      subst value
      have hSplit : block.body.dropLast ++ [Instr.push one] =
          block.body :=
        List.dropLast_append_getLast? _ (Option.mem_def.mpr hLast)
      have hPrefixType :=
        bodyType?_dropLast_push_one hLast hType
      have hOutput := push_one_pop_output hLast hType
      unfold InteractionSemantics.CompiledBlock.fuelBudget
      simp only
      cases hLowPrefix :
          Block.lowerBodyFrom? block.body.dropLast block.input with
      | none => simp [hLowPrefix]
      | some prefixResult =>
          obtain ⟨prefixCode, prefixOutput⟩ := prefixResult
          have hPrefixOutput : prefixOutput = block.output.pop 1 := by
            have hLowerType :=
              bodyType?_of_lowerBodyFrom? block.body.dropLast hLowPrefix
            rw [hPrefixType] at hLowerType
            exact (Option.some.inj hLowerType).symm
          subst prefixOutput
          have hLowPush :
              Block.lowerBodyFrom? [Instr.push one]
                  (block.output.pop 1) =
                some (Assembly.pushCode one, block.output) := by
            simp [Block.lowerBodyFrom?, Instr.lowerAt?,
              Instr.type?, Instr.lower?, hOutput]
          have hLowOriginal :
              Block.lowerBodyFrom? block.body block.input =
                some (prefixCode ++ Assembly.pushCode one,
                  block.output) := by
            conv_lhs => rw [← hSplit]
            rw [lowerBodyFrom?_append, hLowPrefix]
            simp [Option.bind, hLowPush]
          simp only [hLowPrefix, hLowOriginal, ↓reduceIte,
            hTerm, Terminator.lowerAt?, List.length_append,
            List.length_singleton]
          have hPushLength : 1 ≤ (Assembly.pushCode one).length := by
            unfold Assembly.pushCode
            split <;> simp [List.length_append]
          omega
    next _ => exact le_rfl
  next => exact le_rfl

private theorem fuelBudget_blocks_le {program : Program} :
    ∀ (blocks : List Block),
      (∀ block ∈ blocks, block.WellTyped program) →
      (blocks.map (fun block =>
        InteractionSemantics.CompiledBlock.fuelBudget
          (constTrueBlock block))).sum ≤
      (blocks.map
        InteractionSemantics.CompiledBlock.fuelBudget).sum
  | [], _ => by simp
  | block :: rest, hAll => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledBlock_fuelBudget_constTrueBlock_le block
          (hAll block (List.mem_cons_self ..)).1)
        (fuelBudget_blocks_le rest
          (fun candidate hMem =>
            hAll candidate (List.mem_cons_of_mem block hMem)))

/-- Constant-true elimination does not increase the compiled fuel budget. -/
theorem fuelBudget_constTrueProgram_le
    (program : Program) (hTyped : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget
        (constTrueProgram program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  rw [constTrueProgram_blocks, List.map_map]
  obtain ⟨_, hBlocks, _, _⟩ := hTyped
  unfold Program.AllBlocksTyped at hBlocks
  rw [List.forall_iff_forall_mem] at hBlocks
  exact fuelBudget_blocks_le program.blocks hBlocks

/-- The final optimized candidate preserves typing. -/
theorem wellTyped_optimizedProgram {program : Program}
    (hTyped : program.WellTyped) :
    (optimizedProgram program).WellTyped := by
  unfold optimizedProgram
  exact BlockReorder.wellTyped_reorderProgram _
    (wellTyped_constTrueProgram hTyped)

/-- The final optimized candidate preserves PC independence. -/
theorem programCounterIndependent_optimizedProgram {program : Program}
    (hIndependent : program.ProgramCounterIndependent) :
    (optimizedProgram program).ProgramCounterIndependent := by
  unfold optimizedProgram
  exact BlockReorder.programCounterIndependent_reorderProgram _
    (programCounterIndependent_constTrueProgram hIndependent)

/-- Open runs of the final optimized candidate refine the input program. -/
theorem openRunN_optimizedProgram_congr
    {program : Program}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (fuel : Nat) (label : Label) (left right : EVMState)
    (hRel : SameRuntimeData left right) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunN
        program fuel label left)
      (InteractionSemantics.Program.openRunN
        (optimizedProgram program) fuel label right) := by
  unfold optimizedProgram
  rw [BlockReorder.openRunN_reorderProgram
    (constTrueProgram program) (wellTyped_constTrueProgram hTyped).1]
  exact openRunN_constTrueProgram_congr
    hTyped hIndependent fuel label left right hRel

/-- Prefix runs of the final optimized candidate refine the input program. -/
theorem openRunNPrefix_optimizedProgram_congr
    {program : Program}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (fuel : Nat) (label : Label) (left right : EVMState)
    (hRel : SameRuntimeData left right) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix
        program fuel label left)
      (InteractionSemantics.Program.openRunNPrefix
        (optimizedProgram program) fuel label right) := by
  unfold optimizedProgram
  rw [BlockReorder.openRunNPrefix_reorderProgram
    (constTrueProgram program) (wellTyped_constTrueProgram hTyped).1]
  exact openRunNPrefix_constTrueProgram_congr
    hTyped hIndependent fuel label left right hRel

/-- The final optimized candidate does not increase the fuel budget. -/
theorem fuelBudget_optimizedProgram_le
    (program : Program) (hTyped : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget
        (optimizedProgram program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold optimizedProgram
  rw [BlockReorder.fuelBudget_reorderProgram_eq
    (constTrueProgram program) (wellTyped_constTrueProgram hTyped).1]
  exact fuelBudget_constTrueProgram_le program hTyped

end ConstTrueBranch
end TypedCfg
end EvmCompiler
