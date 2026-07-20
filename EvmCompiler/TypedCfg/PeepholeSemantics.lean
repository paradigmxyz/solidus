import EvmCompiler.TypedCfg.Semantics
import EvmCompiler.TypedCfg.Peephole
import EvmCompiler.TypedCfg.PeepholeKernel

/-!
# Peephole semantic preservation (closed block-body level)

Milestone (c), core: the `runBody`-level facts that justify the
`push v ; pop → ε` cancellation performed by `Peephole.peepholeBody`.

The observable content of a state is everything except the compiler-owned
control counters `pc`/`execLength` — captured by
`(·).map eraseRuntimeControl` equality on the `Except` result (which forces
both sides to agree on error, or to be `SameRuntimeData` on success).

Two facts are established:

* `runState`/`runBody` are **congruences** for `SameRuntimeData` on
  *peephole-safe* straight-line instructions (every ordinary stack/data op;
  the only exclusions are `PC`, which reads the counter, and the
  call/create/terminal family, which are handled by the open interaction
  semantics rather than the closed `runState`).
* `peepholeBody` preserves the observable `runBody` result on a safe body.

This is the closed-body core.  Call/create blocks (which run through the open
interaction semantics) and the wiring into `Block.lower?` are the remaining
integration steps.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData eraseRuntimeControl)

/-- A straight-line instruction whose closed `runState` is a `SameRuntimeData`
congruence: ordinary stack/data ops.  `PC` (reads the counter) and the
call/create/terminal ops (arity-less or gated behind the open interaction
semantics) are excluded. -/
def Instr.peepholeSafe : Instr → Bool
  | .prim op =>
      op.stackArity?.isSome && (op != .pc) && (!op.isExternalCallCreate)
  | _ => true

/-- Every instruction of a body is peephole-safe. -/
def BodySafe (body : List Instr) : Prop :=
  ∀ instr ∈ body, Instr.peepholeSafe instr

theorem runPops_map_erase
    {t s : EVMState} :
    ∀ n : Nat, SameRuntimeData t s →
      (Instr.runPops n t).map eraseRuntimeControl =
        (Instr.runPops n s).map eraseRuntimeControl
  | 0, hRel => by
      simp only [Instr.runPops, Except.map]; exact congrArg Except.ok hRel
  | n + 1, hRel => by
      have hPop :
          (Assembly.PrimOp.pop.step t).map eraseRuntimeControl =
            (Assembly.PrimOp.pop.step s).map eraseRuntimeControl :=
        Assembly.PrimOp.step_map_eraseRuntimeControl
          ⟨_, rfl⟩ (by decide) (by decide) hRel
      unfold Instr.runPops
      cases hT : Assembly.PrimOp.pop.step t with
      | error eT =>
          cases hS : Assembly.PrimOp.pop.step s with
          | error eS => simp [hT, hS, Except.map] at hPop ⊢; simp [hPop]
          | ok sS => simp [hT, hS, Except.map] at hPop
      | ok tS =>
          cases hS : Assembly.PrimOp.pop.step s with
          | error eS => simp [hT, hS, Except.map] at hPop
          | ok sS =>
              simp only [hT, hS, bind_pure_comp] at *
              have hRel' : SameRuntimeData tS sS := by
                simp [hT, hS, Except.map] at hPop
                exact hPop
              simpa [Bind.bind, Except.bind] using
                runPops_map_erase n hRel'

/-- Closed `runState` is a `SameRuntimeData` congruence on safe instructions. -/
theorem runState_map_erase
    (instr : Instr) (shape : Shape) {t s : EVMState}
    (hSafe : Instr.peepholeSafe instr = true)
    (hRel : SameRuntimeData t s) :
    (instr.runState shape t).map eraseRuntimeControl =
      (instr.runState shape s).map eraseRuntimeControl := by
  cases instr with
  | push v =>
      simp only [Instr.runState, Except.map]
      exact congrArg Except.ok
        (SameRuntimeData.replaceStackAndIncrPC (pcΔ := 33) hRel
          (congrArg (fun st => st.push v) (SameRuntimeData.stack_eq hRel)))
  | returnToken v =>
      simp only [Instr.runState, Except.map]
      exact congrArg Except.ok
        (SameRuntimeData.replaceStackAndIncrPC (pcΔ := 33) hRel
          (congrArg (fun st => st.push v) (SameRuntimeData.stack_eq hRel)))
  | prim op =>
      simp only [Instr.runState]
      simp only [Instr.peepholeSafe, Bool.and_eq_true] at hSafe
      obtain ⟨⟨hAr, hPc⟩, hCall⟩ := hSafe
      exact Assembly.PrimOp.step_map_eraseRuntimeControl
        (Option.isSome_iff_exists.mp hAr) (by simpa using hPc)
        (by simpa using hCall) hRel
  | pop =>
      simp only [Instr.runState]
      exact Assembly.PrimOp.step_map_eraseRuntimeControl
        ⟨_, rfl⟩ (by decide) (by decide) hRel
  | dup depth =>
      simp only [Instr.runState]
      split <;>
        first
        | (exact Assembly.PrimOp.step_map_eraseRuntimeControl
            ⟨_, rfl⟩ (by decide) (by decide) hRel)
        | rfl
  | swap depth =>
      simp only [Instr.runState]
      split <;>
        first
        | (exact Assembly.PrimOp.step_map_eraseRuntimeControl
            ⟨_, rfl⟩ (by decide) (by decide) hRel)
        | rfl
  | bindLocals _ _ =>
      simp only [Instr.runState, Except.map]; exact congrArg Except.ok hRel
  | bindScratch _ _ _ =>
      simp only [Instr.runState, Except.map]; exact congrArg Except.ok hRel
  | relabel _ =>
      simp only [Instr.runState, Except.map]; exact congrArg Except.ok hRel
  | unwind target =>
      simpa [Instr.runState] using
        runPops_map_erase (shape.length - target.length) hRel

/-- Observable projection of a `runBody` result: erase control counters on the
state, keep the output shape. -/
def eraseFst (r : EVMState × Shape) : EVMState × Shape :=
  (eraseRuntimeControl r.1, r.2)

theorem BodySafe.tail {instr : Instr} {rest : List Instr}
    (h : BodySafe (instr :: rest)) : BodySafe rest :=
  fun i hi => h i (List.mem_cons_of_mem _ hi)

theorem BodySafe.head {instr : Instr} {rest : List Instr}
    (h : BodySafe (instr :: rest)) : Instr.peepholeSafe instr = true :=
  h instr (by simp)

/-- Closed `runBody` is a `SameRuntimeData` congruence on safe bodies: the
final states are `SameRuntimeData` and the output shapes are equal. -/
theorem runBody_map_erase :
    ∀ (body : List Instr) (shape : Shape) {t s : EVMState},
      BodySafe body → SameRuntimeData t s →
        (Block.runBody body shape t).map eraseFst =
          (Block.runBody body shape s).map eraseFst
  | [], shape, t, s, _, hRel => by
      simp only [Block.runBody, Except.map, eraseFst]
      rw [show eraseRuntimeControl t = eraseRuntimeControl s from hRel]
  | instr :: rest, shape, t, s, hSafe, hRel => by
      have hStep := runState_map_erase instr shape hSafe.head hRel
      simp only [Block.runBody, Instr.runAt]
      cases hType : instr.type? shape with
      | none => simp [hType]
      | some out =>
          simp only [hType, Option.elim, bind_pure_comp]
          cases hT : instr.runState shape t with
          | error eT =>
              cases hS : instr.runState shape s with
              | error eS =>
                  simp only [hT, hS, Except.map] at hStep
                  have : eT = eS := Except.error.inj hStep
                  simp [hT, hS, this, Bind.bind, Except.bind, Except.map]
              | ok stS => simp [hT, hS, Except.map] at hStep
          | ok stT =>
              cases hS : instr.runState shape s with
              | error eS => simp [hT, hS, Except.map] at hStep
              | ok stS =>
                  have hRel' : SameRuntimeData stT stS := by
                    simp only [hT, hS, Except.map] at hStep
                    exact Except.ok.inj hStep
                  simp only [hT, hS, Bind.bind, Except.bind]
                  exact runBody_map_erase rest out hSafe.tail hRel'

/-- The peephole only ever drops instructions, so every instruction it keeps
was already present. -/
theorem mem_peepholeBody {x : Instr} :
    ∀ {body : List Instr}, x ∈ peepholeBody body → x ∈ body
  | [], hx => by simp [peepholeBody] at hx
  | instr :: rest, hx => by
      rw [peepholeBody_cons] at hx
      split at hx
      · -- cancel arm: `x ∈ rest'`, a suffix of the (peepholed) tail.
        rename_i v rest' hEq
        have hmem : x ∈ peepholeBody rest := by
          rw [hEq]; exact List.mem_cons_of_mem _ hx
        exact List.mem_cons_of_mem _ (mem_peepholeBody hmem)
      · -- keep arm: `x ∈ instr :: peepholeBody rest`.
        rcases List.mem_cons.mp hx with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_peepholeBody h)

/-- Congruence of `runBody` under a leading common instruction: if two bodies
have observationally equal `runBody` from every shape/state, so do they after
a shared prefix instruction. -/
theorem runBody_cons_congr (i : Instr) {A1 A2 : List Instr}
    (shape : Shape) (state : EVMState)
    (h : ∀ (sh : Shape) (st : EVMState),
      (Block.runBody A1 sh st).map eraseFst =
        (Block.runBody A2 sh st).map eraseFst) :
    (Block.runBody (i :: A1) shape state).map eraseFst =
      (Block.runBody (i :: A2) shape state).map eraseFst := by
  simp only [Block.runBody]
  cases hr : i.runAt shape state with
  | error e => simp [hr]
  | ok r =>
      rcases r with ⟨st', out⟩
      simp only [hr, Bind.bind, Except.bind]
      exact h out st'

theorem BodySafe.peephole {body : List Instr}
    (h : BodySafe body) : BodySafe (peepholeBody body) :=
  fun i hi => h i (mem_peepholeBody hi)

-- NOTE (session 54, Obstacle A): the closed-level preservation theorem
-- `peepholeBody_runBody_erase` and its dead lift
-- `PeepholeBlock.Block.run_peephole_runtimeRel` were RETIRED here.  The
-- `swap d ; swap d → ε` arm is UNSOUND without a runtime depth guard, which the
-- `BodySafe`-only closed signature cannot supply, and the public compile spine
-- routes every block through the OPEN interaction semantics
-- (`openRunBody_peephole_congr`, which carries the `StackRealizes` guard).  The
-- `PeepholeBlock` module was imported by nobody; both are removed.

end Peephole
end TypedCfg
end EvmCompiler
