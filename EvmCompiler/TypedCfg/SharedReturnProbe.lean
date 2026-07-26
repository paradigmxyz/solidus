import EvmCompiler.Compiler.StackArtifact
import EvmCompiler.TypedCfg.ReturnAddressProbe
import EvmCompiler.Assembly.Compact

namespace EvmCompiler
namespace TypedCfg
namespace SharedReturnProbe

/-!
Executable projection for a program-wide logical return dispatcher.

Each ordinary return-dispatch block validates and lifts its buried token, then
jumps to one shared table appended to the program.  The table performs the
token tests and removes the token exactly once before transferring to the
continuation.  This path uses only ordinary static Assembly control flow, so
it can be measured with the production compact encoder.
-/

def dispatcherLabel : Assembly.Label :=
  .named "typedcfg:shared-return-dispatch"

namespace Terminator

def lowerAt? (shape : Shape) : TypedCfg.Terminator →
    Option Assembly.Program
  | .returnDispatch returnCount sites => do
      let depth ← shape.returnTokenDepth?
      if sites.isEmpty ∨ depth ≠ returnCount then
        none
      else if depth < 16 then
        some
          (Assembly.StackShuffle.guardedLiftBuriedToTop depth ++
            [.jump dispatcherLabel])
      else
        none
  | term => term.lowerAt? shape

end Terminator

namespace Block

def lower? (block : TypedCfg.Block) : Option Assembly.Program := do
  let (body, output) ←
    TypedCfg.Block.lowerBodyFrom? block.body block.input
  if output = block.output then
    let term ← Terminator.lowerAt? output block.term
    some (.label block.label :: body ++ term)
  else
    none

end Block

namespace Program

def returnSites (program : TypedCfg.Program) : List ReturnSite :=
  ReturnAddressLower.Program.returnSites program

def dispatcherCode (sites : List ReturnSite) : Assembly.Program :=
  .label dispatcherLabel ::
    TypedCfg.Terminator.returnDispatchCode 0 sites

def lowerBlocks? : List TypedCfg.Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← Block.lower? block
      let tail ← lowerBlocks? rest
      some (head ++ tail)

def lower? (program : TypedCfg.Program) : Option Assembly.Program := do
  let blocks ← program.blocksInLoweringOrder?
  let body ← lowerBlocks? blocks
  let sites := returnSites program
  if sites.isEmpty then
    some body
  else
    some (body ++ dispatcherCode sites)

end Program

structure Artifact where
  cfg : TypedCfg.Program
  assembly : Assembly.Program
  compact : Assembly.Compact.Artifact

def compileCfg? (cfg : TypedCfg.Program) : Option Artifact := do
  let optimized ← ReturnAddressProbe.optimizedCfg? cfg
  let assembly ← Program.lower? optimized
  if assembly.accepted then
    let compact ← Assembly.Compact.compile? assembly
    some { cfg := optimized, assembly, compact }
  else
    none

def compileFunctions? (source : Functions.Program) : Option Artifact := do
  let stack ← Compiler.StackArtifact.compile? source
  compileCfg? stack.cfg

end SharedReturnProbe
end TypedCfg
end EvmCompiler
