import EvmCompiler.Functions.AllocationLayoutLowering
import EvmCompiler.Functions.StackLowering
import EvmCompiler.Locals.Compiler

/-!
Adjacent executable bridge from stack-scheduled Functions lowering to the
ordinary Locals compiler.  Semantic preservation remains owned by the
Functions-to-Locals proof boundary; this module contains no observer semantics
and does not bypass the existing Locals compiler.
-/

namespace EvmCompiler
namespace Functions
namespace StackLoweringCompilation

namespace Examples

def deadProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ← StackLowering.lowerProgram? StackLowering.Examples.deadProgram
  Locals.Program.compile? lower

theorem deadProgram_compiles : deadProgramCompiles?.isSome = true := by
  native_decide

def dormantCallProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ←
    StackLowering.lowerProgram?
      StackLowering.Examples.dormantCallProgram
  Locals.Program.compile? lower

theorem dormantCallProgram_compiles :
    dormantCallProgramCompiles?.isSome = true := by
  native_decide

def controlProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ←
    StackLowering.lowerProgram? StackLowering.Examples.controlProgram
  Locals.Program.compile? lower

theorem controlProgram_compiles :
    controlProgramCompiles?.isSome = true := by
  native_decide

end Examples

end StackLoweringCompilation
end Functions
end EvmCompiler
