import EvmCompiler.TypedCfg.Semantics

namespace EvmCompiler
namespace TypedCfg
namespace Control

/-!
The canonical monadic control kernel for TypedCfg.

The instruction step is the only semantic parameter. Ordinary execution,
resource observation, and open-world execution specialize this recursion
instead of defining their own block and program interpreters.
-/

namespace Instr

def runAt {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) : M (EVMState × Shape) := do
  let output ←
    (instr.type? shape).elim (throw .InvalidInstruction) pure
  let state' ← runState instr shape state
  pure (state', output)

end Instr

namespace Block

def runBody {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState) :
    List TypedCfg.Instr → Shape → EVMState → M (EVMState × Shape)
  | [], shape, state => pure (state, shape)
  | instr :: rest, shape, state => do
      let (state', shape') ← Instr.runAt runState instr shape state
      runBody runState rest shape' state'

def run {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (block : TypedCfg.Block) (state : EVMState) : M TypedCfg.Outcome := do
  let (state', output) ←
    runBody runState block.body block.input state
  if output = block.output then
    pure (TypedCfg.Block.runTerm block.output block.term state')
  else
    throw .InvalidInstruction

end Block

namespace Program

def step {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) : M TypedCfg.Outcome :=
  match program.findBlock? label with
  | none => pure (.invalid state)
  | some block => Block.run runState block state

inductive RunResult where
  | exhausted (label : Label) (state : EVMState)
  | stopped (outcome : TypedCfg.Outcome)

def runNWithStopAs {M : Type → Type} {Result : Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (exhausted : Label → EVMState → Result)
    (stopped : TypedCfg.Outcome → Result)
    (program : TypedCfg.Program) :
    Nat → Label → EVMState → M Result
  | 0, label, state => pure (exhausted label state)
  | fuel + 1, label, state => do
      let outcome ← step runState program label state
      match outcome with
      | .jump next state' =>
          if stopJump next then
            pure (stopped (.jump next state'))
          else
            runNWithStopAs runState stopJump exhausted stopped
              program fuel next state'
      | .fallthrough state' =>
          pure (stopped (.fallthrough state'))
      | .returnDispatch state' =>
          pure (stopped (.returnDispatch state'))
      | .halt kind state' =>
          pure (stopped (.halt kind state'))
      | .invalid state' =>
          pure (stopped (.invalid state'))

abbrev runNWithStop {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (program : TypedCfg.Program) :
    Nat → Label → EVMState → M TypedCfg.Outcome :=
  runNWithStopAs runState stopJump
    (fun label state => .jump label state) id program

abbrev runNResultWithStop {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (program : TypedCfg.Program) :
    Nat → Label → EVMState → M RunResult :=
  runNWithStopAs runState stopJump
    RunResult.exhausted RunResult.stopped program

abbrev runN {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (program : TypedCfg.Program) :
    Nat → Label → EVMState → M TypedCfg.Outcome :=
  runNWithStop runState (fun _ => false) program

@[simp] theorem runNResultWithStop_zero {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) :
    runNResultWithStop runState stopJump program 0 label state =
      pure (.exhausted label state) := rfl

theorem runNResultWithStop_succ {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (program : TypedCfg.Program) (fuel : Nat) (label : Label)
    (state : EVMState) :
    runNResultWithStop runState stopJump
        program (fuel + 1) label state =
      (do
        let outcome ← step runState program label state
        match outcome with
        | .jump next state' =>
            if stopJump next then
              pure (.stopped (.jump next state'))
            else
              runNResultWithStop runState stopJump
                program fuel next state'
        | .fallthrough state' =>
            pure (.stopped (.fallthrough state'))
        | .returnDispatch state' =>
            pure (.stopped (.returnDispatch state'))
        | .halt kind state' =>
            pure (.stopped (.halt kind state'))
        | .invalid state' =>
            pure (.stopped (.invalid state'))) := rfl

@[simp] theorem runNWithStop_zero {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) :
    runNWithStop runState stopJump program 0 label state =
      pure (.jump label state) := rfl

theorem runNWithStop_succ {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → Bool)
    (program : TypedCfg.Program) (fuel : Nat) (label : Label)
    (state : EVMState) :
    runNWithStop runState stopJump program (fuel + 1) label state =
      (do
        let outcome ← step runState program label state
        match outcome with
        | .jump next state' =>
            if stopJump next then
              pure (.jump next state')
            else
              runNWithStop runState stopJump program fuel next state'
        | .fallthrough state' => pure (.fallthrough state')
        | .returnDispatch state' => pure (.returnDispatch state')
        | .halt kind state' => pure (.halt kind state')
        | .invalid state' => pure (.invalid state')) := rfl

@[simp] theorem runN_zero {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) :
    runN runState program 0 label state =
      pure (.jump label state) := rfl

theorem runN_succ {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (program : TypedCfg.Program) (fuel : Nat) (label : Label)
    (state : EVMState) :
    runN runState program (fuel + 1) label state =
      (do
        let outcome ← step runState program label state
        match outcome with
        | .jump next state' =>
            runN runState program fuel next state'
        | .fallthrough state' => pure (.fallthrough state')
        | .returnDispatch state' => pure (.returnDispatch state')
        | .halt kind state' => pure (.halt kind state')
        | .invalid state' => pure (.invalid state')) := rfl

end Program

end Control
end TypedCfg
end EvmCompiler
