import EvmCompiler.TypedCfg.PeepholeSemantics
import EvmCompiler.TypedCfg.InteractionCongruence
import EvmCompiler.TypedCfg.PeepholeOpenStackRealizes
import EvmCompiler.TypedCfg.PeepholeSwapKernel

/-!
# Peephole preservation at the OPEN interaction level

Milestone (d): the `push v ; pop → ε` (and `swap d ; swap d → ε`) cancellation
at the OPEN interaction semantics `InteractionSemantics.Block.openRun`, which is
the semantics the public compile spine actually routes every block through
(call-bearing blocks included).  This OPEN level (not a closed `runBody`
variant) is the sole crown path; the swap arm's runtime depth guard
(`StackRealizes`) only exists here.

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

/-- The peephole preserves a straight-line body's shape transition in the
DIRECTIONAL sense: if the ORIGINAL body types `input` to `output`, so does the
peepholed body.  (The reverse implication FAILS once the `swap d ; swap d` arm is
added — a shallow `input` can make the original untypeable while the cancelled
tail still types — so the invariant is stated one-way; every consumer supplies
the `= some output` typing of the original body, which is exactly what the
peephole-into-spine splice already carries.) -/
theorem peepholeBody_bodyType? :
    ∀ (body : List Instr) (input output : Shape),
      Block.bodyType? body input = some output →
      Block.bodyType? (peepholeBody body) input = some output
  | [], _, _, h => by simpa [peepholeBody_nil] using h
  | instr :: rest, input, output, h => by
      cases hHeadType : instr.type? input with
      | none => simp [Block.bodyType?, hHeadType] at h
      | some middle =>
          have hTailType : Block.bodyType? rest middle = some output := by
            simpa [Block.bodyType?, hHeadType] using h
          rw [peepholeBody_cons]
          split
          · -- cancel arm: instr = .push v, peepholeBody rest = .pop :: rest'
            rename_i v rest' hPeep
            have hMiddle : middle =
                { input with slots := .literal v :: input.slots } := by
              simpa [Instr.type?] using hHeadType.symm
            subst hMiddle
            have ih := peepholeBody_bodyType? rest
              { input with slots := .literal v :: input.slots } output hTailType
            rw [hPeep] at ih
            have hPopType :
                Instr.type? .pop { input with slots := .literal v :: input.slots } =
                  some input := by simp [Instr.type?]
            -- goal: bodyType? rest' input = some output
            simpa [Block.bodyType?, hPopType] using ih
          · -- swap;swap arm: instr = .swap d, peepholeBody rest = .swap d' :: rest'
            rename_i d d' rest' hEq
            have ihB := peepholeBody_bodyType? rest middle output hTailType
            rw [hEq] at ihB
            -- ihB : bodyType? (.swap d' :: rest') middle = some output
            split
            · -- d = d': cancels to rest'
              rename_i hdd
              subst hdd
              have hInv : Instr.type? (.swap d) middle = some input :=
                Instr.swap_type_involution hHeadType
              simpa [Block.bodyType?, hInv] using ihB
            · -- d ≠ d': keeps both swaps (= .swap d :: peepholeBody rest)
              rw [← hEq]
              simpa [Block.bodyType?, hHeadType] using
                peepholeBody_bodyType? rest middle output hTailType
          · -- keep arm
            simpa [Block.bodyType?, hHeadType] using
              peepholeBody_bodyType? rest middle output hTailType

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

/-- `Instr.swap depth` dispatches to `EvmYul.swap (depth + 1)` at the runtime
transformer level (the trivial 16-way dispatch, uniform via `interval_cases`).
Moved here from `PeepholeSwapOpen` (retired) so the swap arm of
`openRunBody_peephole_congr` can use it without the import cycle. -/
theorem runState_swap_eq {depth : Nat} (hDepth : depth < 16)
    (shape : Shape) (state : EVMState) :
    Instr.runState (.swap depth) shape state = EvmYul.swap (depth + 1) state := by
  interval_cases depth <;> rfl

/-- One `swap depth` step in the open body evaluator, when the swap succeeds.
Moved here from `PeepholeSwapOpen` (retired). -/
theorem openRunBody_swap_cons_ok
    {depth : Nat} {rest : List Instr} {input middle : Shape}
    {state next : EVMState}
    (hType : Instr.type? (.swap depth) input = some middle)
    (hRun : Instr.runState (.swap depth) input state = .ok next) :
    Block.openRunBody (.swap depth :: rest) input state =
      Block.openRunBody rest middle next := by
  rw [openRunBody_nonprim_cons (by intro op; simp)]
  simp [TypedCfg.Instr.runAt, hType, hRun, Option.elim]

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
      StackRealizes input state2 →
      SameRuntimeData state1 state2 →
      Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
        (Block.openRunBody (peepholeBody body) input state1)
        (Block.openRunBody body input state2)
  | [], input, output, state1, state2, hType, _, _hReal2, hRel => by
      simp only [Block.bodyType?, Option.some.injEq] at hType
      subst hType
      simp only [peepholeBody_nil]
      exact .done (.ok ⟨hRel, rfl, rfl⟩)
  | instr :: rest, input, output, state1, state2, hType, hPC, hReal2, hRel => by
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
                { input with slots := .literal v :: input.slots } output hTailType
              rw [hPeep] at ihPush
              simpa [Block.bodyType?, hPopType] using ihPush
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
            have hPushReal2 :
                StackRealizes { input with slots := .literal v :: input.slots }
                  (state2.replaceStackAndIncrPC (state2.stack.push v) 33) := by
              unfold StackRealizes at hReal2 ⊢
              simp only [Shape.length, List.length_cons,
                EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
                EvmYul.Stack.push, List.length_cons] at *
              omega
            have ihRest :=
              openRunBody_peephole_congr rest
                { input with slots := .literal v :: input.slots } output
                (state1.replaceStackAndIncrPC (state1.stack.push v) 33)
                (state2.replaceStackAndIncrPC (state2.stack.push v) 33)
                hTailType hTailPC hPushReal2 hPushRel
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
          · -- swap;swap arm: instr = .swap d, peepholeBody rest = .swap d' :: rest'
            rename_i d d' rest' hEq
            split
            · -- d = d': REAL cancellation.  The original `.swap d :: rest`
              -- peepholes to `rest'` because `peepholeBody rest = .swap d :: rest'`.
              -- Mirror of the push;pop cancel arm: fire the RHS head swap on
              -- state2, recurse on `rest`, fire the LHS second swap on state1's
              -- first swap, then collapse `state1`-swapped-twice back via the
              -- depth-guarded kernel.
              rename_i hdd
              subst hdd
              obtain ⟨hDepthLt, hShapeDepth, _hOutLen⟩ :=
                Instr.length_of_type?_swap hHeadType
              have hReal1 : StackRealizes input state1 := by
                have hStk := SameRuntimeData.stack_eq hRel
                unfold StackRealizes; rw [hStk]; exact hReal2
              have hDepth1 : d + 1 + 1 ≤ state1.stack.length := by
                have hl : input.length ≤ state1.stack.length := hReal1
                omega
              have hDepth2 : d + 1 + 1 ≤ state2.stack.length := by
                have hl : input.length ≤ state2.stack.length := hReal2
                omega
              obtain ⟨s1a, s1b, hE1a, hE1b, hSame1⟩ :=
                swap_swap_sameRuntimeData state1 (d + 1) (by omega) hDepth1
              obtain ⟨s2a, _s2b, hE2a, _hE2b, _hSame2⟩ :=
                swap_swap_sameRuntimeData state2 (d + 1) (by omega) hDepth2
              have hHeadType2 : Instr.type? (.swap d) middle = some input :=
                Instr.swap_type_involution hHeadType
              have hRun1a : Instr.runState (.swap d) input state1 = .ok s1a := by
                rw [runState_swap_eq hDepthLt]; exact hE1a
              have hRun1b : Instr.runState (.swap d) middle s1a = .ok s1b := by
                rw [runState_swap_eq hDepthLt]; exact hE1b
              have hRun2a : Instr.runState (.swap d) input state2 = .ok s2a := by
                rw [runState_swap_eq hDepthLt]; exact hE2a
              have hSame1a2a : SameRuntimeData s1a s2a := by
                have hc := runState_map_erase (.swap d) input (by rfl) hRel
                rw [hRun1a, hRun2a] at hc
                simp only [Except.map, Except.ok.injEq] at hc
                exact hc
              have hReal_middle_s2a : StackRealizes middle s2a :=
                runState_stackRealizes hHeadType hRun2a hReal2
              have hRHS : Block.openRunBody (.swap d :: rest) input state2 =
                  Block.openRunBody rest middle s2a :=
                openRunBody_swap_cons_ok hHeadType hRun2a
              have ihRest := openRunBody_peephole_congr rest middle output
                s1a s2a hTailType hTailPC hReal_middle_s2a hSame1a2a
              rw [hEq] at ihRest
              have hLHSreduce :
                  Block.openRunBody (.swap d :: rest') middle s1a =
                    Block.openRunBody rest' input s1b :=
                openRunBody_swap_cons_ok hHeadType2 hRun1b
              rw [hLHSreduce] at ihRest
              have hRest'PC : rest'.Forall Instr.ProgramCounterIndependent := by
                have hp := forall_pcIndependent_peephole hTailPC
                rw [hEq] at hp
                exact forall_pcIndependent_tail_of_cons hp
              have hRestBodyType' : Block.bodyType? rest' input = some output := by
                have ihB := peepholeBody_bodyType? rest middle output hTailType
                rw [hEq] at ihB
                simpa [Block.bodyType?, hHeadType2] using ihB
              have hCong :=
                InteractionCongruence.Block.openRunBody_runtimeRel
                  hRestBodyType' hRest'PC (SameRuntimeData.symm hSame1)
              rw [hRHS]
              refine Simulation.Interaction.Rel.mono
                (Simulation.Interaction.Rel.trans hCong ihRest) ?_
              rintro l r ⟨m, ha, hb⟩
              exact runtimeAtRel_trans ha hb
            · -- d ≠ d': no cancellation — behaves exactly as the keep arm.
              rw [← hEq]
              have hHead :=
                InteractionCongruence.Instr.openRunAt_runtimeRel
                  hHeadType hHeadPC hRel
              have hGuard := openRunAt_stackRealizes hHeadType hReal2
              have hStrong' :
                  Simulation.Interaction.Rel
                    (Simulation.Interaction.ExceptRel
                      (fun a b : EVMException => a = b)
                      (fun lp rp : EVMState × Shape =>
                        SameRuntimeData lp.1 rp.1 ∧ lp.2 = middle ∧ rp.2 = middle ∧
                          StackRealizes middle rp.1))
                    _ _ :=
                Simulation.Interaction.Rel.mono
                  (Simulation.Interaction.Rel.strengthen_right hHead hGuard) (by
                    rintro l r ⟨hER, hSR⟩
                    cases hER with
                    | error he => exact .error he
                    | ok hSS => exact .ok ⟨hSS.1, hSS.2.1, hSS.2.2, hSR⟩)
              unfold InteractionSemantics.Block.openRunBody
                Control.Block.runBody
              apply Simulation.Interaction.Rel.bind hStrong'
              intro leftPair rightPair hPair
              rcases leftPair with ⟨leftAfter, leftShape⟩
              rcases rightPair with ⟨rightAfter, rightShape⟩
              obtain ⟨hAfter, hLeftShape, hRightShape, hRightReal⟩ := hPair
              change SameRuntimeData leftAfter rightAfter at hAfter
              change leftShape = middle at hLeftShape
              change rightShape = middle at hRightShape
              subst leftShape; subst rightShape
              exact
                openRunBody_peephole_congr rest middle output
                  leftAfter rightAfter hTailType hTailPC hRightReal hAfter
          · -- keep arm: peepholeBody (instr :: rest) = instr :: peepholeBody rest
            have hHead :=
              InteractionCongruence.Instr.openRunAt_runtimeRel
                hHeadType hHeadPC hRel
            -- The gating lemma supplies the RIGHT-tree depth guard at every leaf;
            -- `strengthen_right` folds it into the value relation so the guard
            -- rides alongside `RuntimeAtRel` into the bind continuation and
            -- re-seeds the recursion (the bind-quantification obstacle, resolved
            -- on the RIGHT tree — mirror of Step B's left-tree resolution).
            have hGuard := openRunAt_stackRealizes hHeadType hReal2
            have hStrong' :
                Simulation.Interaction.Rel
                  (Simulation.Interaction.ExceptRel
                    (fun a b : EVMException => a = b)
                    (fun lp rp : EVMState × Shape =>
                      SameRuntimeData lp.1 rp.1 ∧ lp.2 = middle ∧ rp.2 = middle ∧
                        StackRealizes middle rp.1))
                  _ _ :=
              Simulation.Interaction.Rel.mono
                (Simulation.Interaction.Rel.strengthen_right hHead hGuard) (by
                  rintro l r ⟨hER, hSR⟩
                  cases hER with
                  | error he => exact .error he
                  | ok hSS => exact .ok ⟨hSS.1, hSS.2.1, hSS.2.2, hSR⟩)
            unfold InteractionSemantics.Block.openRunBody
              Control.Block.runBody
            apply Simulation.Interaction.Rel.bind hStrong'
            intro leftPair rightPair hPair
            rcases leftPair with ⟨leftAfter, leftShape⟩
            rcases rightPair with ⟨rightAfter, rightShape⟩
            obtain ⟨hAfter, hLeftShape, hRightShape, hRightReal⟩ := hPair
            change SameRuntimeData leftAfter rightAfter at hAfter
            change leftShape = middle at hLeftShape
            change rightShape = middle at hRightShape
            subst leftShape; subst rightShape
            exact
              openRunBody_peephole_congr rest middle output
                leftAfter rightAfter hTailType hTailPC hRightReal hAfter

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
    (hIndependent : block.ProgramCounterIndependent)
    (hReal : StackRealizes block.input state) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Block.openRun (peepholeBlock block) state)
      (InteractionSemantics.Block.openRun block state) := by
  have hBody :=
    openRunBody_peephole_congr block.body block.input block.output
      state state hTyped.1 hIndependent hReal (SameRuntimeData.refl state)
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
