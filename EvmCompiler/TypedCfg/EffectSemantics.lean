import EvmCompiler.TypedCfg.Semantics

namespace EvmCompiler
namespace TypedCfg
namespace EffectSemantics

/-!
One parameterized TypedCfg control interpreter.

The ordinary TypedCfg instruction and terminator semantics remain authoritative.
An effect handler runs only after a successful instruction. Observer replay is
therefore a specialization of this control recursion, not a second interpreter.
-/

structure Handler (ε : Type) where
  afterInstr :
    TypedCfg.Instr → EVMState → ε →
      Except EVMException (EVMState × ε)

namespace Instr

def runState {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (effect : ε) :
    Except EVMException (EVMState × ε) := do
  let final ← TypedCfg.Instr.runState instr shape state
  handler.afterInstr instr final effect

def runAt {ε : Type} (handler : Handler ε)
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (effect : ε) :
    Except EVMException ((EVMState × Shape) × ε) := do
  let output ←
    (instr.type? shape).elim (.error .InvalidInstruction) .ok
  let (state', effect') ← runState handler instr shape state effect
  .ok ((state', output), effect')

end Instr

namespace Block

def runBody {ε : Type} (handler : Handler ε) :
    List TypedCfg.Instr → Shape → EVMState → ε →
      Except EVMException ((EVMState × Shape) × ε)
  | [], shape, state, effect => .ok ((state, shape), effect)
  | instr :: rest, shape, state, effect => do
      let ((state', shape'), effect') ←
        Instr.runAt handler instr shape state effect
      runBody handler rest shape' state' effect'

def run {ε : Type} (handler : Handler ε)
    (block : TypedCfg.Block) (state : EVMState) (effect : ε) :
    Except EVMException (TypedCfg.Outcome × ε) := do
  let ((state', output), effect') ←
    runBody handler block.body block.input state effect
  if output = block.output then
    .ok (TypedCfg.Block.runTerm block.output block.term state', effect')
  else
    .error .InvalidInstruction

end Block

namespace Program

def step {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (effect : ε) :
    Except EVMException (TypedCfg.Outcome × ε) :=
  match program.findBlock? label with
  | none => .ok (.invalid state, effect)
  | some block => Block.run handler block state effect

def runN {ε : Type} (handler : Handler ε)
    (program : TypedCfg.Program) :
    Nat → Label → EVMState → ε →
      Except EVMException (TypedCfg.Outcome × ε)
  | 0, label, state, effect => .ok (.jump label state, effect)
  | fuel + 1, label, state, effect =>
      match step handler program label state effect with
      | .error err => .error err
      | .ok (outcome, effect') =>
          match outcome with
          | .jump next state' =>
              runN handler program fuel next state' effect'
          | .fallthrough state' => .ok (.fallthrough state', effect')
          | .returnDispatch state' =>
              .ok (.returnDispatch state', effect')
          | .halt kind state' => .ok (.halt kind state', effect')
          | .invalid state' => .ok (.invalid state', effect')

end Program

end EffectSemantics
end TypedCfg
end EvmCompiler
