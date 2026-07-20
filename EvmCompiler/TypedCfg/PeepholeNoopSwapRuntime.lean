import EvmCompiler.TypedCfg.PeepholeNoopSwapConj
import EvmCompiler.TypedCfg.PeepholeOpen

/-!
# Runtime (open) congruence for `normalizeBody` (session-58, step-3 runtime half)

The type half (`PeepholeNoopSwapConj.normalizeBody_bodyType?`) shows the Route-3
`swap d ; z* ; swap d → (remapZeroWidth d)*` transform preserves the *shape*
transition.  This module supplies the runtime half at the OPEN interaction level:
running the normalized body is `Simulation.Interaction.Rel`-related (up to
`SameRuntimeData`) to running the original body from any `SameRuntimeData`
state — the exact analogue of `openRunBody_peephole_congr` for the window
transform.

The runtime content is small once the type half is in hand: every intervening
zero-width instruction (and its `remapZeroWidth` residue) runs as `.ok state`
(state-identity, `runState_zeroWidth`), so an interior run advances only the shape
(`openRunBody_zeroWidth_run`); the two enclosing `swap d` cancel via the depth-
guarded involution kernel (`swap_swap_sameRuntimeData`).  The keep arms reuse the
`openRunBody_peephole_congr` keep-arm skeleton verbatim (head fired on both trees,
recurse) via `openRunBody_normalize_keep`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-! ## Zero-width run runtime reduction -/

/-- A zero-width instruction runs as pure state-identity. -/
theorem runState_zeroWidth {z : Instr} (h : isZeroWidth z = true)
    (shape : Shape) (state : EVMState) :
    Instr.runState z shape state = .ok state := by
  cases z <;> simp_all [isZeroWidth, Instr.runState]

/-- Zero-width instructions are never primitives. -/
theorem zeroWidth_not_prim {z : Instr} (h : isZeroWidth z = true) :
    ∀ op, z ≠ .prim op := by
  cases z <;> simp_all [isZeroWidth]

/-- A zero-width instruction's `type?` preserves the slot count. -/
theorem type?_zeroWidth_length {z : Instr} (h : isZeroWidth z = true)
    {s s' : Shape} (ht : Instr.type? z s = some s') :
    s'.slots.length = s.slots.length := by
  cases z with
  | bindLocals offset names =>
      have := Instr.length_of_type?_bindLocals ht; simpa [Shape.length] using this
  | bindScratch baseDepth name slot =>
      have := Instr.length_of_type?_bindScratch ht; simpa [Shape.length] using this
  | relabel target =>
      have := Instr.length_of_type?_relabel ht; simpa [Shape.length] using this
  | _ => simp [isZeroWidth] at h

theorem bodyType?_zeroWidth_length (zrun : List Instr) :
    ∀ (s s' : Shape), (∀ z ∈ zrun, isZeroWidth z = true) →
      Block.bodyType? zrun s = some s' → s'.slots.length = s.slots.length := by
  induction zrun with
  | nil => intro s s' _ h; simp only [Block.bodyType?, Option.some.injEq] at h; rw [h]
  | cons z rest ih =>
      intro s s' hAll h
      rw [bodyType?_cons, Option.bind_eq_some_iff] at h
      obtain ⟨s1, hz, h⟩ := h
      have hz1 := ih s1 s' (fun z' hz' => hAll z' (List.mem_cons_of_mem z hz')) h
      rw [hz1, type?_zeroWidth_length (hAll z (List.mem_cons_self ..)) hz]

/-- **Zero-width run reduction.** Running a zero-width run through the open body
evaluator leaves the runtime state untouched and merely advances the shape. -/
theorem openRunBody_zeroWidth_run (zrun : List Instr) :
    ∀ (tail : List Instr) (shape shape' : Shape) (state : EVMState),
      (∀ z ∈ zrun, isZeroWidth z = true) →
      Block.bodyType? zrun shape = some shape' →
      Block.openRunBody (zrun ++ tail) shape state
        = Block.openRunBody tail shape' state := by
  induction zrun with
  | nil =>
      intro tail shape shape' state _ hType
      simp only [Block.bodyType?, Option.some.injEq] at hType; subst hType; rfl
  | cons z rest ih =>
      intro tail shape shape' state hAll hType
      have hz : isZeroWidth z = true := hAll z (List.mem_cons_self ..)
      rw [bodyType?_cons] at hType
      cases hzt : Instr.type? z shape with
      | none => rw [hzt] at hType; simp at hType
      | some z1 =>
          rw [hzt, Option.bind_some] at hType
          have hrunAt : Instr.runAt z shape state = .ok (state, z1) := by
            simp [Instr.runAt, hzt, runState_zeroWidth hz, Option.elim]
          rw [List.cons_append, openRunBody_nonprim_cons (zeroWidth_not_prim hz),
            hrunAt]
          exact ih tail z1 shape' state
            (fun z' hz' => hAll z' (List.mem_cons_of_mem z hz')) hType

/-! ## The keep-arm skeleton (shared by the three non-firing cases) -/

/-- The `openRunBody_peephole_congr` keep-arm skeleton, abstracted over the tail
congruence: an identical head fired on both trees, then recurse. -/
theorem openRunBody_normalize_keep (head : Instr) (rest ltail : List Instr)
    {input output middle : Shape} {state1 state2 : EVMState}
    (hHeadType : head.type? input = some middle)
    (hHeadPC : head.ProgramCounterIndependent)
    (hReal2 : StackRealizes input state2)
    (hRel : SameRuntimeData state1 state2)
    (hTail : ∀ st1 st2, StackRealizes middle st2 → SameRuntimeData st1 st2 →
      Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
        (Block.openRunBody ltail middle st1) (Block.openRunBody rest middle st2)) :
    Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
      (Block.openRunBody (head :: ltail) input state1)
      (Block.openRunBody (head :: rest) input state2) := by
  have hHead :=
    InteractionCongruence.Instr.openRunAt_runtimeRel hHeadType hHeadPC hRel
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
  unfold InteractionSemantics.Block.openRunBody Control.Block.runBody
  apply Simulation.Interaction.Rel.bind hStrong'
  intro leftPair rightPair hPair
  rcases leftPair with ⟨leftAfter, leftShape⟩
  rcases rightPair with ⟨rightAfter, rightShape⟩
  obtain ⟨hAfter, hLeftShape, hRightShape, hRightReal⟩ := hPair
  change SameRuntimeData leftAfter rightAfter at hAfter
  change leftShape = middle at hLeftShape
  change rightShape = middle at hRightShape
  subst leftShape; subst rightShape
  exact hTail leftAfter rightAfter hRightReal hAfter

/-! ## The open normalize congruence -/

/-- **Open normalize body congruence.** The normalized body run from `state1` is
`Rel`-related to the original body run from any `SameRuntimeData`-equivalent
`state2`, up to runtime data.  The analogue of `openRunBody_peephole_congr` for the
Route-3 `swap d ; z* ; swap d → (remapZeroWidth d)*` transform. -/
theorem openRunBody_normalize_congr (body : List Instr) :
    ∀ (input output : Shape) (state1 state2 : EVMState),
      Block.bodyType? body input = some output →
      body.Forall Instr.ProgramCounterIndependent →
      StackRealizes input state2 →
      SameRuntimeData state1 state2 →
      Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
        (Block.openRunBody (normalizeBody body) input state1)
        (Block.openRunBody body input state2) := by
  induction body using normalizeBody.induct with
  | case1 =>
      intro input output state1 state2 hType _ _ hRel
      simp only [normalizeBody]
      simp only [Block.bodyType?, Option.some.injEq] at hType; subst hType
      exact .done (.ok ⟨hRel, rfl, rfl⟩)
  | case2 d rest d' rest' hTail hGuard ih =>
      intro input output state1 state2 hType hPC hReal2 hRel
      obtain ⟨hdd, hSafe⟩ := hGuard
      subst hdd
      have happ : (leadingZeroWidth rest).1 ++ Instr.swap d :: rest' = rest := by
        conv_rhs => rw [← leadingZeroWidth_append rest]
        rw [hTail]
      have hAllSafe : ∀ z ∈ (leadingZeroWidth rest).1, RemapSafe z = true :=
        fun z hz => List.all_eq_true.mp hSafe z hz
      have hAllZW : ∀ z ∈ (leadingZeroWidth rest).1, isZeroWidth z = true :=
        fun z hz => remapSafe_isZeroWidth (hAllSafe z hz)
      -- PC facts
      have hRestPC : rest.Forall Instr.ProgramCounterIndependent :=
        forall_pcIndependent_tail_of_cons hPC
      have hrest'PC : rest'.Forall Instr.ProgramCounterIndependent := by
        rw [List.forall_iff_forall_mem] at hRestPC ⊢
        intro x hx; apply hRestPC x
        rw [← happ]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
      -- decompose the original typing: swap ; zrun ; swap ; rest'
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨s1, h1, hTypeRest⟩ := hType
      obtain ⟨hDepthLt, hShapeDepth, _⟩ := Instr.length_of_type?_swap h1
      obtain ⟨hi0, hid1⟩ := swap_bounds h1
      obtain ⟨hs1slots, hs1tail⟩ := type?_swap_eq h1
      have hs1len : s1.slots.length = input.slots.length := by
        rw [hs1slots, swapPos_length]
      have hs1eq : s1 = remapShape d input := by
        rcases s1 with ⟨sl1, tl1⟩
        simp only at hs1slots hs1tail
        subst hs1slots; subst hs1tail; rfl
      rw [← happ, bodyType?_append, Option.bind_eq_some_iff] at hTypeRest
      obtain ⟨sInner, hzt, hTypeRest⟩ := hTypeRest
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hTypeRest
      obtain ⟨s3, h3, hTypeRest'⟩ := hTypeRest
      obtain ⟨hs3slots, hs3tail⟩ := type?_swap_eq h3
      -- depth guards
      have hReal1 : StackRealizes input state1 := by
        unfold StackRealizes; rw [SameRuntimeData.stack_eq hRel]; exact hReal2
      have hInLen : d + 2 ≤ input.slots.length := hShapeDepth
      have hDepth1 : d + 1 + 1 ≤ state1.stack.length := by
        have := hReal1; unfold StackRealizes Shape.length at this; omega
      have hDepth2 : d + 1 + 1 ≤ state2.stack.length := by
        have := hReal2; unfold StackRealizes Shape.length at this; omega
      obtain ⟨s2a, s2b, hE2a, hE2b, hSame2⟩ :=
        swap_swap_sameRuntimeData state2 (d + 1) (by omega) hDepth2
      have hRun2a : Instr.runState (.swap d) input state2 = .ok s2a := by
        rw [runState_swap_eq hDepthLt]; exact hE2a
      have hRun2b : Instr.runState (.swap d) sInner s2a = .ok s2b := by
        rw [runState_swap_eq hDepthLt]; exact hE2b
      -- RHS reduction chain: swap ; zrun ; swap  ↦  openRunBody rest' s3 s2b
      have hRHS1 : Block.openRunBody (Instr.swap d :: rest) input state2
          = Block.openRunBody rest s1 s2a :=
        openRunBody_swap_cons_ok h1 hRun2a
      have hRHS2 : Block.openRunBody rest s1 s2a
          = Block.openRunBody (Instr.swap d :: rest') sInner s2a := by
        conv_lhs => rw [← happ]
        exact openRunBody_zeroWidth_run (leadingZeroWidth rest).1
          (Instr.swap d :: rest') s1 sInner s2a hAllZW hzt
      have hRHS3 : Block.openRunBody (Instr.swap d :: rest') sInner s2a
          = Block.openRunBody rest' s3 s2b :=
        openRunBody_swap_cons_ok h3 hRun2b
      -- StackRealizes chain on the RHS
      have hRealS1 : StackRealizes s1 s2a := runState_stackRealizes h1 hRun2a hReal2
      have hRealInner : StackRealizes sInner s2a := by
        have hlen := bodyType?_zeroWidth_length (leadingZeroWidth rest).1 s1 sInner hAllZW hzt
        unfold StackRealizes Shape.length at hRealS1 ⊢; omega
      have hRealS3 : StackRealizes s3 s2b := runState_stackRealizes h3 hRun2b hRealInner
      -- LHS reduction: the mapped run advances to s3, state1 untouched
      have hfoldLHS : Block.bodyType?
          ((leadingZeroWidth rest).1.map (remapZeroWidth d)) input = some s3 := by
        have hinput_eq : input = remapShape d s1 := by
          rw [hs1eq, remapShape_involutive d input hi0 hid1]
        rw [hinput_eq, bodyType?_map_remap_conj d (leadingZeroWidth rest).1 s1 hAllSafe
          (by rw [hs1len]; exact hi0) (by rw [hs1len]; exact hid1), hzt, Option.map_some]
        refine congrArg some ?_
        rcases s3 with ⟨sl3, tl3⟩
        simp only at hs3slots hs3tail
        simp only [remapShape, Shape.mk.injEq]; exact ⟨hs3slots.symm, hs3tail.symm⟩
      have hLHS : Block.openRunBody
          ((leadingZeroWidth rest).1.map (remapZeroWidth d) ++ normalizeBody rest')
          input state1
          = Block.openRunBody (normalizeBody rest') s3 state1 :=
        openRunBody_zeroWidth_run ((leadingZeroWidth rest).1.map (remapZeroWidth d))
          (normalizeBody rest') input s3 state1
          (fun z hz => by
            obtain ⟨z0, hz0mem, hz0eq⟩ := List.mem_map.mp hz
            subst hz0eq; rw [isZeroWidth_remapZeroWidth]
            exact hAllZW z0 hz0mem)
          hfoldLHS
      -- assemble
      have hRel_1_2b : SameRuntimeData state1 s2b :=
        SameRuntimeData.trans hRel (SameRuntimeData.symm hSame2)
      rw [normalizeBody_fire d rest rest' hTail hSafe, hLHS, hRHS1, hRHS2, hRHS3]
      exact ih s3 output state1 s2b hTypeRest' hrest'PC hRealS3 hRel_1_2b
  | case3 d rest d' rest' hTail hGuard ih =>
      intro input output state1 state2 hType hPC hReal2 hRel
      have hunfold : normalizeBody (Instr.swap d :: rest)
          = Instr.swap d :: normalizeBody rest := by
        by_cases hdd : d = d'
        · have hUnsafe : (leadingZeroWidth rest).1.all RemapSafe = false := by
            by_contra hne; simp only [Bool.not_eq_false] at hne
            exact hGuard ⟨hdd, hne⟩
          exact normalizeBody_keep_unsafe d d' rest rest' hTail hUnsafe
        · exact normalizeBody_keep_swap d d' rest rest' hTail hdd
      rw [hunfold, bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨middle, hHeadType, hTailType⟩ := hType
      exact openRunBody_normalize_keep (Instr.swap d) rest (normalizeBody rest)
        hHeadType (pcIndependent_head_of_cons hPC) hReal2 hRel
        (fun st1 st2 hR hS => ih middle output st1 st2 hTailType
          (forall_pcIndependent_tail_of_cons hPC) hR hS)
  | case4 d rest hNoTail ih =>
      intro input output state1 state2 hType hPC hReal2 hRel
      rw [normalizeBody_keep_noTail d rest (fun d' rest' h => hNoTail d' rest' h),
        bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨middle, hHeadType, hTailType⟩ := hType
      exact openRunBody_normalize_keep (Instr.swap d) rest (normalizeBody rest)
        hHeadType (pcIndependent_head_of_cons hPC) hReal2 hRel
        (fun st1 st2 hR hS => ih middle output st1 st2 hTailType
          (forall_pcIndependent_tail_of_cons hPC) hR hS)
  | case5 instr rest hNotSwap ih =>
      intro input output state1 state2 hType hPC hReal2 hRel
      rw [normalizeBody_cons_generic instr rest (fun d h => hNotSwap d h),
        bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨middle, hHeadType, hTailType⟩ := hType
      exact openRunBody_normalize_keep instr rest (normalizeBody rest)
        hHeadType (pcIndependent_head_of_cons hPC) hReal2 hRel
        (fun st1 st2 hR hS => ih middle output st1 st2 hTailType
          (forall_pcIndependent_tail_of_cons hPC) hR hS)

end Peephole
end TypedCfg
end EvmCompiler
