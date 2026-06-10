import EvmCompiler.TypedCfg.Typing
import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace TypedCfg

abbrev EVMState := Assembly.EVMState
abbrev EVMException := Assembly.EVMException

inductive Outcome where
  | fallthrough (state : EVMState)
  | jump (target : Label) (state : EVMState)
  | returnDispatch (state : EVMState)
  | halt (kind : Assembly.HaltKind) (state : EVMState)
  | invalid (state : EVMState)

namespace Instr

def runAt (instr : Instr) (shape : Shape) (state : EVMState) :
    Except EVMException (EVMState × Shape) := do
  let output ←
    (instr.type? shape).elim (.error .InvalidInstruction) .ok
  let state' ←
    match instr with
    | .push value =>
        .ok
          (state.replaceStackAndIncrPC
            (state.stack.push value) (pcΔ := 33))
    | .returnToken value =>
        .ok
          (state.replaceStackAndIncrPC
            (state.stack.push value) (pcΔ := 33))
    | .prim op =>
        op.step state
    | .pop =>
        Assembly.PrimOp.pop.step state
    | .dup depth =>
        match depth with
        | 0 => Assembly.PrimOp.dup1.step state
        | 1 => Assembly.PrimOp.dup2.step state
        | 2 => Assembly.PrimOp.dup3.step state
        | 3 => Assembly.PrimOp.dup4.step state
        | 4 => Assembly.PrimOp.dup5.step state
        | 5 => Assembly.PrimOp.dup6.step state
        | 6 => Assembly.PrimOp.dup7.step state
        | 7 => Assembly.PrimOp.dup8.step state
        | 8 => Assembly.PrimOp.dup9.step state
        | 9 => Assembly.PrimOp.dup10.step state
        | 10 => Assembly.PrimOp.dup11.step state
        | 11 => Assembly.PrimOp.dup12.step state
        | 12 => Assembly.PrimOp.dup13.step state
        | 13 => Assembly.PrimOp.dup14.step state
        | 14 => Assembly.PrimOp.dup15.step state
        | 15 => Assembly.PrimOp.dup16.step state
        | _ => .error .InvalidInstruction
    | .swap depth =>
        match depth with
        | 0 => Assembly.PrimOp.swap1.step state
        | 1 => Assembly.PrimOp.swap2.step state
        | 2 => Assembly.PrimOp.swap3.step state
        | 3 => Assembly.PrimOp.swap4.step state
        | 4 => Assembly.PrimOp.swap5.step state
        | 5 => Assembly.PrimOp.swap6.step state
        | 6 => Assembly.PrimOp.swap7.step state
        | 7 => Assembly.PrimOp.swap8.step state
        | 8 => Assembly.PrimOp.swap9.step state
        | 9 => Assembly.PrimOp.swap10.step state
        | 10 => Assembly.PrimOp.swap11.step state
        | 11 => Assembly.PrimOp.swap12.step state
        | 12 => Assembly.PrimOp.swap13.step state
        | 13 => Assembly.PrimOp.swap14.step state
        | 14 => Assembly.PrimOp.swap15.step state
        | 15 => Assembly.PrimOp.swap16.step state
        | _ => .error .InvalidInstruction
    | .unwind target =>
        let popCount := shape.length - target.length
        .ok
          (state.replaceStackAndIncrPC
            (state.stack.drop popCount) (pcΔ := popCount))
  .ok (state', output)

end Instr

namespace Block

def runBody : List Instr → Shape → EVMState →
    Except EVMException (EVMState × Shape)
  | [], shape, state => .ok (state, shape)
  | instr :: rest, shape, state => do
      let (state', shape') ← instr.runAt shape state
      runBody rest shape' state'

def ReturnSite.findTarget? (token : Word) :
    List ReturnSite → Option Label
  | [] => none
  | site :: rest =>
      if site.token = token then some site.target
      else findTarget? token rest

def runTerm (shape : Shape) (term : Terminator) (state : EVMState) : Outcome :=
  match term with
  | .fallthrough next => .jump next state
  | .jump target => .jump target state
  | .jumpi target fallthrough =>
      match state.stack.pop with
      | none => .invalid state
      | some (stack, cond) =>
          let state' := { state with stack := stack }
          if cond = EvmYul.UInt256.ofNat 0 then
            .jump fallthrough state'
          else
            .jump target state'
  | .returnDispatch returnCount sites =>
      match shape.returnTokenDepth? with
      | none => .invalid state
      | some depth =>
          if depth ≠ returnCount then
            .invalid state
          else match state.stack[depth]? with
          | none => .invalid state
          | some token =>
              match ReturnSite.findTarget? token sites with
              | none => .invalid state
              | some target =>
                  .jump target { state with stack := state.stack.eraseIdx depth }
  | .halt kind => .halt kind state
  | .invalid => .invalid state

def run (block : Block) (state : EVMState) :
    Except EVMException Outcome := do
  let (state', output) ← runBody block.body block.input state
  if output = block.output then
    .ok (runTerm block.output block.term state')
  else
    .error .InvalidInstruction

end Block

namespace Program

def step (program : Program) (label : Label) (state : EVMState) :
    Except EVMException Outcome :=
  match program.findBlock? label with
  | none => .ok (.invalid state)
  | some block => block.run state

end Program

end TypedCfg
end EvmCompiler
