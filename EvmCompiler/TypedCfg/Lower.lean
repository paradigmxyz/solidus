import EvmCompiler.TypedCfg.Semantics

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def lower? : Instr → Option Assembly.Program
  | .push value => some [.push value]
  | .returnToken value => some [.push value]
  | .prim op => some [.prim op]
  | .pop => some [.prim .pop]
  | .dup depth =>
      match depth with
      | 0 => some [.prim .dup1]
      | 1 => some [.prim .dup2]
      | 2 => some [.prim .dup3]
      | 3 => some [.prim .dup4]
      | 4 => some [.prim .dup5]
      | 5 => some [.prim .dup6]
      | 6 => some [.prim .dup7]
      | 7 => some [.prim .dup8]
      | 8 => some [.prim .dup9]
      | 9 => some [.prim .dup10]
      | 10 => some [.prim .dup11]
      | 11 => some [.prim .dup12]
      | 12 => some [.prim .dup13]
      | 13 => some [.prim .dup14]
      | 14 => some [.prim .dup15]
      | 15 => some [.prim .dup16]
      | _ => none
  | .swap depth =>
      match depth with
      | 0 => some [.prim .swap1]
      | 1 => some [.prim .swap2]
      | 2 => some [.prim .swap3]
      | 3 => some [.prim .swap4]
      | 4 => some [.prim .swap5]
      | 5 => some [.prim .swap6]
      | 6 => some [.prim .swap7]
      | 7 => some [.prim .swap8]
      | 8 => some [.prim .swap9]
      | 9 => some [.prim .swap10]
      | 10 => some [.prim .swap11]
      | 11 => some [.prim .swap12]
      | 12 => some [.prim .swap13]
      | 13 => some [.prim .swap14]
      | 14 => some [.prim .swap15]
      | 15 => some [.prim .swap16]
      | _ => none
  | .unwind _target => none

def lowerAt? (instr : Instr) (shape : Shape) :
    Option (Assembly.Program × Shape) := do
  let output ← instr.type? shape
  match instr with
  | .unwind target =>
      some
        (List.replicate (shape.length - target.length) (.prim .pop),
          output)
  | _ =>
      let code ← instr.lower?
      some (code, output)

end Instr

namespace Terminator

def swapAt? (depth : Nat) : Option Assembly.Instr :=
  (Instr.lower? (.swap (depth - 1))).bind List.head?

def liftBuriedToTop? : Nat → Option Assembly.Program
  | 0 => some []
  | depth + 1 => do
      let lifted ← liftBuriedToTop? depth
      let swap ← swapAt? (depth + 1)
      some (lifted ++ [swap])

def removeBuriedUnder? (depth : Nat) : Option Assembly.Program := do
  let lifted ← liftBuriedToTop? depth
  some (lifted ++ [.prim .pop])

def returnDispatchTests? (depth : Nat) :
    List ReturnSite → Option Assembly.Program
  | [] => some [.prim .invalid]
  | site :: rest => do
      let duplicate ← Instr.lower? (.dup depth)
      let tail ← returnDispatchTests? depth rest
      some
        (duplicate ++
          [.push site.token, .prim .eq,
            .jumpi site.caseLabel] ++ tail)

def returnDispatchCases? (depth : Nat) :
    List ReturnSite → Option Assembly.Program
  | [] => some []
  | site :: rest => do
      let cleanup ← removeBuriedUnder? depth
      let tail ← returnDispatchCases? depth rest
      some
        (.label site.caseLabel ::
          cleanup ++ [.jump site.target] ++ tail)

def returnDispatchCode? (depth : Nat) (sites : List ReturnSite) :
    Option Assembly.Program := do
  let tests ← returnDispatchTests? depth sites
  let cases ← returnDispatchCases? depth sites
  some (tests ++ cases)

def lowerAt? (shape : Shape) : Terminator → Option Assembly.Program
  | .fallthrough next => some [.jump next]
  | .jump target => some [.jump target]
  | .jumpi target next => some [.jumpi target, .jump next]
  | .returnDispatch returnCount sites => do
      let depth ← shape.returnTokenDepth?
      if sites.isEmpty ∨ depth ≠ returnCount then none
      else returnDispatchCode? depth sites
  | .halt kind =>
      match kind with
      | .stop => some [.prim .stop]
      | .return => some [.prim .return]
      | .revert => some [.prim .revert]
      | .selfdestruct => some [.prim .selfdestruct]
  | .invalid => some [.prim .invalid]

end Terminator

namespace Block

def lowerBodyFrom? : List Instr → Shape →
    Option (Assembly.Program × Shape)
  | [], shape => some ([], shape)
  | instr :: rest, shape => do
      let (head, shape') ← instr.lowerAt? shape
      let (tail, output) ← lowerBodyFrom? rest shape'
      some (head ++ tail, output)

def lower? (block : Block) : Option Assembly.Program := do
  let (body, output) ← lowerBodyFrom? block.body block.input
  if output = block.output then
    let term ← block.term.lowerAt? output
    some (.label block.label :: body ++ term)
  else
    none

end Block

namespace Program

def lowerBlocks? : List Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← block.lower?
      let tail ← lowerBlocks? rest
      some (head ++ tail)

def lower? (program : Program) : Option Assembly.Program :=
  program.blocksInLoweringOrder? >>= lowerBlocks?

def Lowerable (program : Program) : Prop :=
  ∃ asm, program.lower? = some asm

end Program

end TypedCfg
end EvmCompiler
