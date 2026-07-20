import EvmCompiler.TypedCfg.PeepholeSeamCancelEff

/-!
# Runtime pending-swap bisimulation for the corrected (clean-seam) canceller (session-72)

Ports the §62-67 runtime tower of `PeepholeSeamCancel` to the corrected
conjugating, clean-seam transform `seamCancelProgramEff` (PEEPHOLE_PROGRESS
§Session-70/71).  Structurally mechanical over the shipped tower with
`sourceFire? → cleanSrc?`, `targetFire? → cleanTgt?`; the one genuinely-new kernel
is the SOURCE-side birth: the removable swap is the block's HEAD (not the shipped
trailing swap), followed by a runtime-identity `bindLocals`.  The bind is an
EVMState identity for *any* names (`Semantics.lean:78-83`), so the birth is the
plain swap-involution born by the head swap, transparent to the trailing bind.

Because `cleanSrc?` and `cleanTgt?` are disjoint (`cleanSrc?_cleanTgt?_disjoint`),
the body kernel has only THREE reachable cases (the shipped some/some chain case is
vacuous here).

This leaf is imported by **nobody** in the spine and hence cannot affect the
`compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-! ## Source-side birth kernel (head swap + runtime-identity conjugated bind) -/

/-- **Eff source-side birth kernel.**  Running the original source body
`[swap d, bindLocals 0 names]` from `s_o` is `Rel`-related to running the edited
body `[bindLocals 0 names']` from a `SameRuntimeData` state `s_c`, with the results
in `PendingSwap d` (the original result is one `swap (d+1)` ahead of
`SameRuntimeData` to the edited one).  The head swap births the pending desync;
both `bindLocals` are EVMState identities. -/
theorem openRunBody_headSwap_bind_pending
    {d : Nat} {names names' : List String} {input mid output outputC : Shape}
    {s_o s_c : EVMState}
    (hswapType : Instr.type? (.swap d) input = some mid)
    (hbindO : Instr.type? (.bindLocals 0 names) mid = some output)
    (hbindC : Instr.type? (.bindLocals 0 names') input = some outputC)
    (hRel : SameRuntimeData s_o s_c)
    (hReal_c : StackRealizes input s_c) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          PendingSwap d rp.1 lp.1 ∧ lp.2 = output ∧ rp.2 = outputC))
      (InteractionSemantics.Block.openRunBody
        [Instr.swap d, Instr.bindLocals 0 names] input s_o)
      (InteractionSemantics.Block.openRunBody
        [Instr.bindLocals 0 names'] input s_c) := by
  obtain ⟨hd16, hdepth, _⟩ := Instr.length_of_type?_swap hswapType
  -- Runtime depth for the head swap on `s_o` (stacks equal via SRD).
  have hStackEq : s_o.stack = s_c.stack := SameRuntimeData.stack_eq hRel
  have hDepth : (d + 1) + 1 ≤ s_o.stack.length := by
    have h1 : input.length ≤ s_c.stack.length := hReal_c
    have h2 : d + 2 ≤ input.length := hdepth
    rw [hStackEq]; omega
  obtain ⟨s1, s2, hE1, hE2, hSame2⟩ :=
    swap_swap_sameRuntimeData s_o (d + 1) (by omega) hDepth
  have hRun : Instr.runState (.swap d) input s_o = .ok s1 := by
    rw [runState_swap_eq hd16]; exact hE1
  -- Reduce the LHS: head swap then bind-identity.
  rw [openRunBody_swap_cons_ok hswapType hRun]
  have hRunAtO : TypedCfg.Instr.runAt (Instr.bindLocals 0 names) mid s1
      = .ok (s1, output) := by
    simp [TypedCfg.Instr.runAt, hbindO, Instr.runState]
  have hlhs : InteractionSemantics.Block.openRunBody
      [Instr.bindLocals 0 names] mid s1
      = Simulation.Interaction.done (.ok (s1, output)) := by
    rw [openRunBody_nonprim_cons (by intro op; simp), hRunAtO]; rfl
  -- Reduce the RHS: bind-identity only.
  have hRunAtC : TypedCfg.Instr.runAt (Instr.bindLocals 0 names') input s_c
      = .ok (s_c, outputC) := by
    simp [TypedCfg.Instr.runAt, hbindC, Instr.runState]
  have hrhs : InteractionSemantics.Block.openRunBody
      [Instr.bindLocals 0 names'] input s_c
      = Simulation.Interaction.done (.ok (s_c, outputC)) := by
    rw [openRunBody_nonprim_cons (by intro op; simp), hRunAtC]; rfl
  rw [hlhs, hrhs]
  refine Simulation.Interaction.Rel.done (.ok ⟨⟨s2, ?_, ?_⟩, rfl, rfl⟩)
  · exact hE2
  · exact SameRuntimeData.trans hSame2 hRel

/-! ## Body facts for the two firing cases -/

/-- Typing facts for a clean source block: body is `[swap d, bindLocals 0 names]`,
the swap types `input` to `remapShape d input`, the bind types that to `output`, and
the conjugated bind types `input` to `remapShape d output`. -/
theorem cleanSrc_body_facts {program : Program} {b0 : Block} {d : Nat}
    (hTyped : b0.WellTyped program) (hs : cleanSrc? program b0 = some d) :
    ∃ names, b0.body = [Instr.swap d, Instr.bindLocals 0 names] ∧
      Instr.type? (.swap d) b0.input = some (remapShape d b0.input) ∧
      Instr.type? (.bindLocals 0 names) (remapShape d b0.input) = some b0.output ∧
      Instr.type? (.bindLocals 0 (swapPos 0 (d + 1) names)) b0.input
        = some (remapShape d b0.output) := by
  obtain ⟨hsr, _, _⟩ := cleanSrc?_spec hs
  obtain ⟨bLabel, b, names, hterm, _, _, _, hbody, hln, _, _⟩ := srcRaw?_spec hsr
  have hbodyT := hTyped.1
  rw [hbody, bodyType?_cons, Option.bind_eq_some_iff] at hbodyT
  obtain ⟨m, hswap, hrest⟩ := hbodyT
  rw [bodyType?_cons, Option.bind_eq_some_iff] at hrest
  obtain ⟨o, hbind, hnil⟩ := hrest
  simp only [Block.bodyType?, Option.some.injEq] at hnil
  subst hnil
  have hm : m = remapShape d b0.input := type?_swap_eq_remapShape hswap
  subst hm
  have hswap' : Instr.type? (.swap d) b0.input = some (remapShape d b0.input) := hswap
  -- Conjugated bind typing via bodyType?_conj.
  have hconj : Block.bodyType? [Instr.bindLocals 0 (swapPos 0 (d + 1) names)] b0.input
      = some (remapShape d b0.output) := by
    apply bodyType?_conj hln
    have hbt := hTyped.1
    rw [hbody] at hbt
    exact hbt
  rw [bodyType?_cons, Option.bind_eq_some_iff] at hconj
  obtain ⟨oc, hbindC, hnilC⟩ := hconj
  simp only [Block.bodyType?, Option.some.injEq] at hnilC
  subst hnilC
  exact ⟨names, hbody, hswap', hbind, hbindC⟩

/-! ## The unified Eff seam-cancel body kernel (three reachable cases) -/

/-- **Unified corrected seam-cancel body kernel.**  Running the original block body
from `s_o` is `Rel`-related to running the edited body from `s_c`, ENTRY relation
discriminated by `cleanTgt?` (SRD if `none`, `PendingSwap d` if `some d`) and RESULT
by `cleanSrc?` (SRD if `none`, `PendingSwap e` if `some e`).  By disjointness only
three cases are reachable. -/
theorem seamBlockEff_body_rel {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hmem : b0 ∈ program.blocks)
    (hTyped : b0.WellTyped program) (hIndep : b0.ProgramCounterIndependent)
    {s_o s_c : EVMState}
    (hRin : match cleanTgt? program b0 with
            | none => SameRuntimeData s_o s_c
            | some d => PendingSwap d s_c s_o)
    (hReal_c : StackRealizes (seamBlockEff program b0).input s_c) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          (match cleanSrc? program b0 with
           | none => SameRuntimeData lp.1 rp.1
           | some e => PendingSwap e rp.1 lp.1)
          ∧ lp.2 = b0.output ∧ rp.2 = (seamBlockEff program b0).output))
      (InteractionSemantics.Block.openRunBody b0.body b0.input s_o)
      (InteractionSemantics.Block.openRunBody (seamBlockEff program b0).body
        (seamBlockEff program b0).input s_c) := by
  have hBodyEq := seamBlockEff_body program b0
  have hInEq := seamBlockEff_input program b0
  have hOutEq := seamBlockEff_output program b0
  have hIndBody : b0.body.Forall Instr.ProgramCounterIndependent := hIndep
  cases hs : cleanSrc? program b0 with
  | some d =>
      -- Source fires ⟹ cleanTgt? = none (disjoint) ⟹ entry SRD; result PendingSwap.
      have hct : cleanTgt? program b0 = none := by
        rcases cleanSrc?_cleanTgt?_disjoint program b0 with h | h
        · rw [h] at hs; exact absurd hs (by simp)
        · exact h
      simp only [hBodyEq, hInEq, hOutEq, hs, hct] at hRin hReal_c ⊢
      obtain ⟨names, hbody, hswapT, hbindO, hbindC⟩ := cleanSrc_body_facts hTyped hs
      rw [hbody]
      simp only [List.tail_cons, List.map_cons, List.map_nil, conjBind]
      exact openRunBody_headSwap_bind_pending hswapT hbindO hbindC hRin hReal_c
  | none =>
      cases ht : cleanTgt? program b0 with
      | none =>
          -- Identity block: plain runtime congruence.
          simp only [hBodyEq, hInEq, hOutEq, hs, ht] at hRin ⊢
          exact InteractionCongruence.Block.openRunBody_runtimeRel hTyped.1 hIndBody hRin
      | some d =>
          -- Target only: resync the dropped head swap.
          simp only [hBodyEq, hInEq, hOutEq, hs, ht] at hRin hReal_c ⊢
          have hhd := cleanTgt_head_swap hUnique hmem ht
          have hdecomp : b0.body = Instr.swap d :: b0.body.tail := head_tail_decomp hhd
          have hbodyT := hTyped.1
          rw [hdecomp, bodyType?_cons, Option.bind_eq_some_iff] at hbodyT
          obtain ⟨m, htype, hrest⟩ := hbodyT
          have hmid : m = remapShape d b0.input := type?_swap_eq_remapShape htype
          subst hmid
          obtain ⟨hd16, _, _⟩ := Instr.length_of_type?_swap htype
          obtain ⟨next, hswapNext, hsyncNext⟩ := hRin
          have hRun : Instr.runState (.swap d) b0.input s_o = .ok next := by
            rw [runState_swap_eq hd16]; exact hswapNext
          have hIndTail : b0.body.tail.Forall Instr.ProgramCounterIndependent :=
            forall_sub (List.tail_subset b0.body) hIndBody
          have hcore :=
            openRunBody_swap_cons_resync (input := b0.input)
              (middle := remapShape d b0.input) htype hRun hrest hIndTail hsyncNext
          conv_lhs => rw [hdecomp]
          exact hcore

/-! ## The carried invariant + disjunctive outcome relation -/

/-- The inter-block state invariant carried across a fired clean seam.  SRD unless
the block is a clean target, in which case one `swap (d+1)` apart. -/
def SeamStepRelEff (program : Program) (label : Label) (s_o s_c : EVMState) : Prop :=
  match program.findBlock? label with
  | none => SameRuntimeData s_o s_c
  | some b =>
      match cleanTgt? program b with
      | none => SameRuntimeData s_o s_c
      | some d => PendingSwap d s_c s_o

/-- The disjunctive one-step outcome relation for the corrected canceller. -/
def SeamOutcomeRelEff (program : Program) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun a b =>
    (∃ (next : Label) (so sc : EVMState),
      a = .ok (.jump next so) ∧ b = .ok (.jump next sc) ∧
        SeamStepRelEff program next so sc)
    ∨ (InteractionCongruence.Block.RuntimeOutcomeRel a b ∧
        ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s))

/-- **Block-level corrected seam-cancel congruence.** -/
theorem openRun_seamCancelEff_congr {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hTyped : program.WellTyped)
    (hmem : b0 ∈ program.blocks) (hIndep : b0.ProgramCounterIndependent)
    {s_o s_c : EVMState}
    (hRin : match cleanTgt? program b0 with
            | none => SameRuntimeData s_o s_c
            | some d => PendingSwap d s_c s_o)
    (hReal_c : StackRealizes (seamBlockEff program b0).input s_c) :
    Simulation.Interaction.Rel (SeamOutcomeRelEff program)
      (InteractionSemantics.Block.openRun b0 s_o)
      (InteractionSemantics.Block.openRun (seamBlockEff program b0) s_c) := by
  have hb0Typed : b0.WellTyped program := blockWellTyped_of_mem hTyped.2.1 hmem
  have hbody := seamBlockEff_body_rel hUnique hmem hb0Typed hIndep hRin hReal_c
  unfold InteractionSemantics.Block.openRun Control.Block.run
  simp only [seamBlockEff_term]
  refine Simulation.Interaction.Rel.bind_custom hbody ?_
  intro leftDone rightDone hDone
  cases hDone with
  | error he => exact Simulation.Interaction.Rel.done (Or.inr ⟨.error he, by simp⟩)
  | ok hpair =>
      rename_i lpair rpair
      obtain ⟨hrel, hlp2, hrp2⟩ := hpair
      simp only [hlp2, hrp2, ↓reduceIte]
      cases hsrc : cleanSrc? program b0 with
      | none =>
          simp only [hsrc] at hrel
          have hsoeq : (seamBlockEff program b0).output = b0.output := by
            rw [seamBlockEff_output, hsrc]
          rw [hsoeq]
          have hChecked := InteractionCongruence.Block.runTermChecked_runtimeRel
            (shape := b0.output) (term := b0.term) hrel
          cases hL : TypedCfg.Block.runTermChecked b0.output b0.term lpair.1 with
          | error eL =>
              cases hR : TypedCfg.Block.runTermChecked b0.output b0.term rpair.1 with
              | error eR =>
                  simp only [hL, hR] at hChecked
                  cases hChecked with
                  | error he =>
                      exact Simulation.Interaction.Rel.done (Or.inr ⟨.error he, by simp⟩)
              | ok oR => simp only [hL, hR] at hChecked; cases hChecked
          | ok oL =>
              cases hR : TypedCfg.Block.runTermChecked b0.output b0.term rpair.1 with
              | error eR => simp only [hL, hR] at hChecked; cases hChecked
              | ok oR =>
                  simp only [hL, hR] at hChecked
                  refine Simulation.Interaction.Rel.done ?_
                  cases hChecked with
                  | ok hrr =>
                      cases hrr with
                      | jump lbl hSt =>
                          have hmemT : lbl ∈ b0.term.targets :=
                            runTerm_jump_mem_targets
                              (TypedCfg.Block.runTerm_eq_of_runTermChecked_eq_ok hL)
                          refine Or.inl ⟨lbl, _, _, rfl, rfl, ?_⟩
                          unfold SeamStepRelEff
                          cases hfindL : program.findBlock? lbl with
                          | none => exact hSt
                          | some bL =>
                              simp only [cleanTgt?_none_of_cleanSrc?_none hmem hmemT hsrc hfindL]
                              exact hSt
                      | fallthrough hSt => exact Or.inr ⟨.ok (.fallthrough hSt), by simp⟩
                      | returnDispatch hSt => exact Or.inr ⟨.ok (.returnDispatch hSt), by simp⟩
                      | halt kind hSt => exact Or.inr ⟨.ok (.halt kind hSt), by simp⟩
                      | invalid hSt => exact Or.inr ⟨.ok (.invalid hSt), by simp⟩
      | some e =>
          obtain ⟨hsr, _, bLabel, B, hterm, hfind, hsrcB⟩ := cleanSrc?_spec hsrc
          simp only [hsrc] at hrel
          rw [hterm]
          simp only [TypedCfg.Block.runTermChecked_jump, TypedCfg.Block.runTerm]
          refine Simulation.Interaction.Rel.done ?_
          refine Or.inl ⟨bLabel, lpair.1, rpair.1, rfl, rfl, ?_⟩
          have htf : cleanTgt? program B = some e :=
            cleanTgt?_of_cleanSrc? hmem hterm hfind hsrc
          unfold SeamStepRelEff
          simp only [hfind, htf]
          exact hrel

/-- **Whole-program one-step corrected seam-cancel congruence.** -/
theorem openStep_seamCancelEff_congr {program : Program} {label : Label}
    {s_o s_c : EVMState}
    (hUnique : program.LabelsUnique) (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hReal_c : ∀ b0, program.findBlock? label = some b0 →
      StackRealizes (seamBlockEff program b0).input s_c)
    (hStep : SeamStepRelEff program label s_o s_c) :
    Simulation.Interaction.Rel (SeamOutcomeRelEff program)
      (InteractionSemantics.Program.openStep program label s_o)
      (InteractionSemantics.Program.openStep (seamCancelProgramEff program) label s_c) := by
  unfold InteractionSemantics.Program.openStep Control.Program.step
  rw [findBlock?_seamCancelProgramEff]
  cases hFind : program.findBlock? label with
  | none =>
      simp only [hFind, Option.map_none]
      simp only [SeamStepRelEff, hFind] at hStep
      exact Simulation.Interaction.Rel.done (Or.inr ⟨.ok (Outcome.RuntimeRel.invalid hStep), by simp⟩)
  | some b0 =>
      simp only [hFind, Option.map_some]
      have hMem : b0 ∈ program.blocks := by
        unfold TypedCfg.Program.findBlock? at hFind
        exact List.mem_of_find?_eq_some hFind
      have hb0Indep : b0.ProgramCounterIndependent :=
        (List.forall_iff_forall_mem.mp hIndependent) b0 hMem
      simp only [SeamStepRelEff, hFind] at hStep
      exact openRun_seamCancelEff_congr hUnique hTyped hMem hb0Indep hStep (hReal_c b0 hFind)

/-! ## Structural preservation for the splice (PCI) -/

/-- `conjBind` preserves per-instruction `ProgramCounterIndependent` (it only
permutes a `bindLocals` name list, which is PC-independent for any names). -/
theorem conjBind_programCounterIndependent {d : Nat} {instr : Instr}
    (h : instr.ProgramCounterIndependent) :
    (conjBind d instr).ProgramCounterIndependent := by
  cases instr <;> exact h

/-- The corrected seam edit preserves per-block `ProgramCounterIndependent`. -/
theorem seamBlockEff_programCounterIndependent {program : Program} {block : Block}
    (h : block.ProgramCounterIndependent) :
    (seamBlockEff program block).ProgramCounterIndependent := by
  have hBody : block.body.Forall Instr.ProgramCounterIndependent := h
  unfold Block.ProgramCounterIndependent
  rw [seamBlockEff_body]
  cases cleanSrc? program block with
  | some d =>
      rw [List.forall_iff_forall_mem]
      intro i hi
      rw [List.mem_map] at hi
      obtain ⟨i0, hi0mem, rfl⟩ := hi
      exact conjBind_programCounterIndependent
        ((List.forall_iff_forall_mem.mp (forall_sub (List.tail_subset _) hBody)) i0 hi0mem)
  | none =>
      cases cleanTgt? program block with
      | some d => exact forall_sub (List.tail_subset _) hBody
      | none => exact hBody

/-- **Whole-program `ProgramCounterIndependent` preservation** under the corrected
seam cancellation. -/
theorem seamCancelProgramEff_programCounterIndependent {program : Program}
    (h : program.ProgramCounterIndependent) :
    (seamCancelProgramEff program).ProgramCounterIndependent := by
  unfold Program.ProgramCounterIndependent at h ⊢
  rw [List.forall_iff_forall_mem] at h
  rw [seamCancelProgramEff_blocks, List.forall_iff_forall_mem]
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨b0, hb0mem, rfl⟩ := hb
  exact seamBlockEff_programCounterIndependent (h b0 hb0mem)

/-! ## Entry seed: the entry block never clean-target-fires -/

/-- The entry block never clean-target-fires: `cleanTgt?` unfolds through `tgtRaw?`'s
`b.label ≠ program.entry` guard. -/
theorem cleanTgt?_entry_eq_none {program : Program} {b : Block}
    (hlabel : b.label = program.entry) :
    cleanTgt? program b = none := by
  unfold cleanTgt?
  have htg : tgtRaw? program b = none := by
    unfold tgtRaw?
    rw [if_neg]
    rintro ⟨hne, _⟩
    exact hne hlabel
  rw [htg]

/-- **Entry seed (`SeamStepRelEff`).**  At the program entry, equal states satisfy
`SeamStepRelEff` via its `SameRuntimeData` branch. -/
theorem seamStepRelEff_entry (program : Program) (s : EVMState) :
    SeamStepRelEff program program.entry s s := by
  unfold SeamStepRelEff
  cases hf : program.findBlock? program.entry with
  | none => exact SameRuntimeData.refl s
  | some b =>
      have hlabel : b.label = program.entry := by
        unfold Program.findBlock? at hf
        have := List.find?_some hf; simpa using this
      simp only [cleanTgt?_entry_eq_none hlabel]
      exact SameRuntimeData.refl s

end Peephole
end TypedCfg
end EvmCompiler
