import EvmCompiler.TypedCfg.Control

namespace EvmCompiler
namespace TypedCfg
namespace EffectSemantics

/-!
Compatibility API for post-instruction effects.

The recursive control flow lives in `TypedCfg.Control`. This module only turns
the historical `afterInstr` handler into a `StateT` instruction step. Observer
replay therefore remains source-compatible without owning another interpreter.
-/

structure Handler (ε : Type) where
  afterInstr :
    TypedCfg.Instr → EVMState → ε →
      Except EVMException (EVMState × ε)

abbrev EffectM (ε : Type) :=
  StateT ε (Except EVMException)

namespace Instr

def runState {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (effect : ε) :
    Except EVMException (EVMState × ε) := do
  let final ← TypedCfg.Instr.runState instr shape state
  handler.afterInstr instr final effect

def runStateM {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) : EffectM ε EVMState :=
  fun effect => runState handler instr shape state effect

def runAt {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (effect : ε) :
    Except EVMException ((EVMState × Shape) × ε) := do
  let output ←
    (instr.type? shape).elim (.error .InvalidInstruction) .ok
  let (state', effect') ← runState handler instr shape state effect
  .ok ((state', output), effect')

theorem control_runAt_eq {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (effect : ε) :
    Control.Instr.runAt
        (runStateM handler) instr shape state effect =
      runAt handler instr shape state effect := by
  unfold Control.Instr.runAt runStateM runAt
  simp only [StateT.instMonad, StateT.bind,
    StateT.instMonadExceptOf]
  cases hType : instr.type? shape with
  | none =>
      simp [hType]
      rfl
  | some output =>
      simp [hType, StateT.pure]

end Instr

namespace Block

def runBody {ε : Type} (handler : Handler ε)
    (body : List TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (effect : ε) :
    Except EVMException ((EVMState × Shape) × ε) :=
  (Control.Block.runBody
    (Instr.runStateM handler) body shape state).run effect

@[simp] theorem runBody_cons {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (rest : List TypedCfg.Instr)
    (shape : Shape) (state : EVMState) (effect : ε) :
    runBody handler (instr :: rest) shape state effect =
      (do
        let ((state', shape'), effect') ←
          Instr.runAt handler instr shape state effect
        runBody handler rest shape' state' effect') := by
  change
    Control.Block.runBody
        (Instr.runStateM handler) (instr :: rest)
        shape state effect =
      (do
        let ((state', shape'), effect') ←
          Instr.runAt handler instr shape state effect
        Control.Block.runBody
          (Instr.runStateM handler) rest shape' state' effect')
  rw [Control.Block.runBody]
  simp only [StateT.instMonad, StateT.bind]
  rw [Instr.control_runAt_eq]

def run {ε : Type} (handler : Handler ε)
    (block : TypedCfg.Block) (state : EVMState) (effect : ε) :
    Except EVMException (TypedCfg.Outcome × ε) :=
  (Control.Block.run
    (Instr.runStateM handler) block state).run effect

end Block

namespace Program

def step {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (effect : ε) :
    Except EVMException (TypedCfg.Outcome × ε) :=
  (Control.Program.step
    (Instr.runStateM handler) program label state).run effect

def runN {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (fuel : Nat) (label : Label)
    (state : EVMState) (effect : ε) :
    Except EVMException (TypedCfg.Outcome × ε) :=
  (Control.Program.runN
    (Instr.runStateM handler) program fuel label state).run effect

@[simp] theorem runN_zero {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (effect : ε) :
    runN handler program 0 label state effect =
      .ok (.jump label state, effect) := rfl

theorem runN_succ {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (fuel : Nat) (label : Label)
    (state : EVMState) (effect : ε) :
    runN handler program (fuel + 1) label state effect =
      match step handler program label state effect with
      | .error err => .error err
      | .ok (outcome, effect') =>
          match outcome with
          | .jump next state' =>
              runN handler program fuel next state' effect'
          | .fallthrough state' =>
              .ok (.fallthrough state', effect')
          | .returnDispatch state' =>
              .ok (.returnDispatch state', effect')
          | .halt kind state' =>
              .ok (.halt kind state', effect')
          | .invalid state' =>
              .ok (.invalid state', effect') := by
  unfold runN step
  rw [Control.Program.runN_succ]
  cases hStep :
      (Control.Program.step
        (Instr.runStateM handler) program label state).run effect with
  | error err =>
      simp [hStep]
  | ok result =>
      rcases result with ⟨outcome, effect'⟩
      cases outcome <;> simp [hStep, runN]

/--
Successful finite execution from an effectful CFG entry.

Residual jumps are intentional: adjacent compiler fragments compose by
reaching one another's entry labels while threading the same effect state.
-/
def Eventually {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (effect : ε)
    (outcome : TypedCfg.Outcome) (effect' : ε) : Prop :=
  ∃ fuel,
    runN handler program fuel label state effect =
      .ok (outcome, effect')

namespace Eventually

theorem residual {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (effect : ε) :
    Eventually handler program label state effect
      (.jump label state) effect :=
  ⟨0, rfl⟩

theorem of_runN {ε : Type} {handler : Handler ε}
    {program : TypedCfg.Program} {fuel : Nat} {label : Label}
    {state : EVMState} {effect effect' : ε}
    {outcome : TypedCfg.Outcome}
    (hRun :
      runN handler program fuel label state effect =
        .ok (outcome, effect')) :
    Eventually handler program label state effect outcome effect' :=
  ⟨fuel, hRun⟩

theorem bind_jump {ε : Type} {handler : Handler ε}
    {program : TypedCfg.Program} {entry next : Label}
    {initial middle : EVMState}
    {initialEffect middleEffect finalEffect : ε}
    {outcome : TypedCfg.Outcome}
    (hFirst :
      Eventually handler program entry initial initialEffect
        (.jump next middle) middleEffect)
    (hNext :
      Eventually handler program next middle middleEffect
        outcome finalEffect) :
    Eventually handler program entry initial initialEffect
      outcome finalEffect := by
  rcases hFirst with ⟨firstFuel, hFirst⟩
  rcases hNext with ⟨nextFuel, hNext⟩
  refine ⟨firstFuel + nextFuel, ?_⟩
  induction firstFuel generalizing entry initial initialEffect with
  | zero =>
      simp only [runN_zero] at hFirst
      cases hFirst
      simpa using hNext
  | succ firstFuel ih =>
      rw [Nat.succ_add, runN_succ]
      rw [runN_succ] at hFirst
      cases hStep :
          step handler program entry initial initialEffect with
      | error err =>
          simp [hStep] at hFirst
      | ok result =>
          rcases result with ⟨stepOutcome, stepEffect⟩
          rw [hStep] at hFirst
          cases stepOutcome with
          | jump target stepped =>
              exact ih hFirst
          | fallthrough stepped
          | returnDispatch stepped
          | halt kind stepped
          | invalid stepped =>
              cases hFirst

end Eventually

end Program

end EffectSemantics
end TypedCfg
end EvmCompiler
