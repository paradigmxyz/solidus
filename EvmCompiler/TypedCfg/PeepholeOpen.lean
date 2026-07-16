import EvmCompiler.TypedCfg.PeepholeSemantics
import EvmCompiler.TypedCfg.InteractionCongruence

/-!
# Peephole preservation at the OPEN interaction level

Milestone (d): lift the `push v ; pop → ε` cancellation from the closed
block level (`PeepholeBlock.Block.run_peephole_runtimeRel`) to the OPEN
interaction semantics `InteractionSemantics.Block.openRun`, which is the
semantics the public compile spine actually routes every block through
(call-bearing blocks included).

The single genuinely-new lemma is `openRunBody_peephole_congr`: the peepholed
body, run from a state `state1`, is `Simulation.Interaction.Rel`-related (up to
`SameRuntimeData`, i.e. runtime data equal, pc/execLength erased) to the original
body run from any `SameRuntimeData`-equivalent `state2`.  Unlike the closed
proof, this needs only `ProgramCounterIndependent` (no call/create exclusion):
CALL/CREATE ride the existing open congruence `Instr.openRunAt_runtimeRel`, and
the cancelled `push`/`pop` are non-primitive, so their open steps are embedded
closed `.done` steps that reuse `PeepholeKernel.pop_after_push_sameRuntimeData`
directly.

Everything composes through the pre-existing `InteractionCongruence` RuntimeRel
tower (`openRunBody_runtimeRel`, `runTermChecked_runtimeRel`).
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-- The peephole preserves a straight-line body's shape transition: cancelling
`push v ; pop` pairs is stack-shape-neutral, so `bodyType?` is unchanged. -/
theorem peepholeBody_bodyType? :
    ∀ (body : List Instr) (input : Shape),
      Block.bodyType? (peepholeBody body) input =
        Block.bodyType? body input
  | [], _ => rfl
  | instr :: rest, input => by
      have ih : ∀ s, Block.bodyType? (peepholeBody rest) s =
          Block.bodyType? rest s := fun s => peepholeBody_bodyType? rest s
      rw [peepholeBody_cons]
      split
      · -- cancel arm: instr = .push v, peepholeBody rest = .pop :: rest'
        rename_i v rest' hPeep
        have hkey := ih { input with slots := .literal v :: input.slots }
        rw [hPeep] at hkey
        have hPopType :
            Instr.type? .pop { input with slots := .literal v :: input.slots } =
              some input := by simp [Instr.type?]
        simp only [Block.bodyType?, hPopType, Option.bind] at hkey
        -- goal: bodyType? rest' input = bodyType? (.push v :: rest) input
        simp only [Block.bodyType?, Instr.type?, Option.bind]
        exact hkey
      · -- keep arm
        simp only [Block.bodyType?, ih]

open InteractionSemantics

/-- Non-primitive instruction step in the open body evaluator embeds the closed
`runAt`. -/
theorem openRunBody_nonprim_cons
    {instr : Instr} {rest : List Instr} {shape : Shape} {state : EVMState}
    (hNonPrim : ∀ op, instr ≠ .prim op) :
    Block.openRunBody (instr :: rest) shape state =
      (match TypedCfg.Instr.runAt instr shape state with
        | .error e => .done (.error e)
        | .ok r => Block.openRunBody rest r.2 r.1) := by
  unfold Block.openRunBody
  change
    Simulation.Interaction.bind (Instr.openRunAt instr shape state)
      (fun result => Block.openRunBody rest result.2 result.1) = _
  rw [Instr.openRunAt_eq_done_of_not_prim hNonPrim]
  cases TypedCfg.Instr.runAt instr shape state <;> rfl

/-- One `push v` step in the open body evaluator. -/
theorem openRunBody_push_cons
    (v : Word) (rest : List Instr) (input : Shape) (state : EVMState) :
    Block.openRunBody (.push v :: rest) input state =
      Block.openRunBody rest
        { input with slots := .literal v :: input.slots }
        (state.replaceStackAndIncrPC (state.stack.push v) 33) := by
  rw [openRunBody_nonprim_cons (by intro op; simp)]
  simp [TypedCfg.Instr.runAt, Instr.type?, Instr.runState, Option.elim]

open InteractionCongruence

/-- `Instr.RuntimeAtRel` is transitive on the closed result carrier. -/
theorem runtimeAtRel_trans {output : Shape}
    {l m r : Except EVMException (EVMState × Shape)}
    (h1 : Instr.RuntimeAtRel output l m)
    (h2 : Instr.RuntimeAtRel output m r) :
    Instr.RuntimeAtRel output l r := by
  cases h1 with
  | error he1 =>
      cases h2 with
      | error he2 => exact .error (he1.trans he2)
  | ok ho1 =>
      cases h2 with
      | ok ho2 =>
          exact .ok ⟨ho1.1.trans ho2.1, ho1.2.1, ho2.2.2⟩

/-- Membership monotonicity of `ProgramCounterIndependent` through the peephole. -/
theorem forall_pcIndependent_peephole {body : List Instr}
    (h : body.Forall Instr.ProgramCounterIndependent) :
    (peepholeBody body).Forall Instr.ProgramCounterIndependent := by
  rw [List.forall_iff_forall_mem] at h ⊢
  exact fun i hi => h i (mem_peepholeBody hi)

theorem forall_pcIndependent_tail_of_cons {i : Instr} {rest : List Instr}
    (h : (i :: rest).Forall Instr.ProgramCounterIndependent) :
    rest.Forall Instr.ProgramCounterIndependent :=
  ((List.forall_cons _ i rest).mp h).2

theorem pcIndependent_head_of_cons {i : Instr} {rest : List Instr}
    (h : (i :: rest).Forall Instr.ProgramCounterIndependent) :
    i.ProgramCounterIndependent :=
  ((List.forall_cons _ i rest).mp h).1

/-- **Open peephole body congruence (the one genuinely-new lemma).**
The peepholed body run from `state1` is `Rel`-related to the original body run
from any `SameRuntimeData`-equivalent `state2`, up to runtime data. -/
theorem openRunBody_peephole_congr :
    ∀ (body : List Instr) (input output : Shape) (state1 state2 : EVMState),
      Block.bodyType? body input = some output →
      body.Forall Instr.ProgramCounterIndependent →
      SameRuntimeData state1 state2 →
      Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
        (Block.openRunBody (peepholeBody body) input state1)
        (Block.openRunBody body input state2)
  | [], input, output, state1, state2, hType, _, hRel => by
      simp only [Block.bodyType?, Option.some.injEq] at hType
      subst hType
      simp only [peepholeBody_nil]
      exact .done (.ok ⟨hRel, rfl, rfl⟩)
  | instr :: rest, input, output, state1, state2, hType, hPC, hRel => by
      cases hHeadType : instr.type? input with
      | none => simp [Block.bodyType?, hHeadType] at hType
      | some middle =>
          have hTailType : Block.bodyType? rest middle = some output := by
            simpa [Block.bodyType?, hHeadType] using hType
          have hHeadPC := pcIndependent_head_of_cons hPC
          have hTailPC := forall_pcIndependent_tail_of_cons hPC
          rw [peepholeBody_cons]
          split
          · -- cancel arm: instr = .push v, peepholeBody rest = .pop :: rest'
            rename_i v rest' hPeep
            -- instr has been refined to `.push v`; recover the pushed shape.
            have hMiddle : middle =
                { input with slots := .literal v :: input.slots } := by
              simpa [Instr.type?] using hHeadType.symm
            subst hMiddle
            have hPushRel :
                SameRuntimeData
                  (state1.replaceStackAndIncrPC (state1.stack.push v) 33)
                  (state2.replaceStackAndIncrPC (state2.stack.push v) 33) :=
              SameRuntimeData.replaceStackAndIncrPC (pcΔ := 33) hRel
                (congrArg (fun st => st.push v) (SameRuntimeData.stack_eq hRel))
            obtain ⟨popState1, hPopStep, hPopRel⟩ :=
              pop_after_push_sameRuntimeData state1 v 33
            have hPopType :
                Instr.type? .pop
                    { input with slots := .literal v :: input.slots } =
                  some input := by simp [Instr.type?]
            have hRestBodyType : Block.bodyType? rest' input = some output := by
              have ihPush := peepholeBody_bodyType? rest
                { input with slots := .literal v :: input.slots }
              rw [hPeep] at ihPush
              simp only [Block.bodyType?, hPopType, Option.bind] at ihPush
              exact ihPush.trans hTailType
            have hRest'PC : rest'.Forall Instr.ProgramCounterIndependent := by
              have hp := forall_pcIndependent_peephole hTailPC
              rw [hPeep] at hp
              exact forall_pcIndependent_tail_of_cons hp
            have hRHS :
                Block.openRunBody (Instr.push v :: rest) input state2 =
                  Block.openRunBody rest
                    { input with slots := .literal v :: input.slots }
                    (state2.replaceStackAndIncrPC (state2.stack.push v) 33) :=
              openRunBody_push_cons v rest input state2
            have ihRest :=
              openRunBody_peephole_congr rest
                { input with slots := .literal v :: input.slots } output
                (state1.replaceStackAndIncrPC (state1.stack.push v) 33)
                (state2.replaceStackAndIncrPC (state2.stack.push v) 33)
                hTailType hTailPC hPushRel
            rw [hPeep] at ihRest
            have hPopReduce :
                Block.openRunBody (.pop :: rest')
                    { input with slots := .literal v :: input.slots }
                    (state1.replaceStackAndIncrPC (state1.stack.push v) 33) =
                  Block.openRunBody rest' input popState1 := by
              rw [openRunBody_nonprim_cons (by intro op; simp)]
              simp [TypedCfg.Instr.runAt, hPopType, Instr.runState,
                Option.elim, hPopStep]
            rw [hPopReduce] at ihRest
            have hCong :=
              InteractionCongruence.Block.openRunBody_runtimeRel
                hRestBodyType hRest'PC hPopRel.symm
            rw [hRHS]
            refine Simulation.Interaction.Rel.mono
              (Simulation.Interaction.Rel.trans hCong ihRest) ?_
            rintro l r ⟨m, ha, hb⟩
            exact runtimeAtRel_trans ha hb
          · -- keep arm: peepholeBody (instr :: rest) = instr :: peepholeBody rest
            have hHead :=
              InteractionCongruence.Instr.openRunAt_runtimeRel
                hHeadType hHeadPC hRel
            unfold InteractionSemantics.Block.openRunBody
              Control.Block.runBody
            apply Simulation.Interaction.Rel.bind hHead
            intro leftPair rightPair hPair
            rcases leftPair with ⟨leftAfter, leftShape⟩
            rcases rightPair with ⟨rightAfter, rightShape⟩
            rcases hPair with ⟨hAfter, hLeftShape, hRightShape⟩
            change SameRuntimeData leftAfter rightAfter at hAfter
            change leftShape = middle at hLeftShape
            change rightShape = middle at hRightShape
            subst leftShape; subst rightShape
            exact
              openRunBody_peephole_congr rest middle output
                leftAfter rightAfter hTailType hTailPC hAfter

/-- The peepholed block: same label/input/output/terminator, cancelled body. -/
def peepholeBlock (block : Block) : Block :=
  { block with body := peepholeBody block.body }

@[simp] theorem peepholeBlock_body (block : Block) :
    (peepholeBlock block).body = peepholeBody block.body := rfl
@[simp] theorem peepholeBlock_input (block : Block) :
    (peepholeBlock block).input = block.input := rfl
@[simp] theorem peepholeBlock_output (block : Block) :
    (peepholeBlock block).output = block.output := rfl
@[simp] theorem peepholeBlock_term (block : Block) :
    (peepholeBlock block).term = block.term := rfl
@[simp] theorem peepholeBlock_label (block : Block) :
    (peepholeBlock block).label = block.label := rfl

/-- **Open peephole block congruence.** Peepholing a `ProgramCounterIndependent`
block preserves the OPEN `Block.openRun` up to the pass-agnostic
`RuntimeOutcomeRel` (equal control label, equal halt kind, `SameRuntimeData`
carried state), from the same input state. -/
theorem Block.openRun_peephole_runtimeRel
    {program : Program} (block : Block) (state : EVMState)
    (hTyped : block.WellTyped program)
    (hIndependent : block.ProgramCounterIndependent) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Block.openRun (peepholeBlock block) state)
      (InteractionSemantics.Block.openRun block state) := by
  have hBody :=
    openRunBody_peephole_congr block.body block.input block.output
      state state hTyped.1 hIndependent (SameRuntimeData.refl state)
  unfold InteractionSemantics.Block.openRun Control.Block.run
  simp only [peepholeBlock_body, peepholeBlock_input, peepholeBlock_output,
    peepholeBlock_term]
  apply Simulation.Interaction.Rel.bind hBody
  intro leftPair rightPair hPair
  rcases leftPair with ⟨leftAfter, leftShape⟩
  rcases rightPair with ⟨rightAfter, rightShape⟩
  rcases hPair with ⟨hAfter, hLeftShape, hRightShape⟩
  change SameRuntimeData leftAfter rightAfter at hAfter
  change leftShape = block.output at hLeftShape
  change rightShape = block.output at hRightShape
  subst leftShape; subst rightShape
  simp only [↓reduceIte]
  have hChecked :=
    InteractionCongruence.Block.runTermChecked_runtimeRel
      (shape := block.output) (term := block.term) hAfter
  cases hLeft : TypedCfg.Block.runTermChecked block.output block.term leftAfter <;>
    cases hRight : TypedCfg.Block.runTermChecked block.output block.term rightAfter <;>
    simp [hLeft, hRight] at hChecked ⊢
  all_goals exact .done hChecked

end Peephole
end TypedCfg
end EvmCompiler
