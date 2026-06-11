import EvmCompiler.Assembly.Syntax

open EvmCompiler

namespace EvmCompiler.ProofArtifacts.AssemblyLargeProgram

def largeProgram : Assembly.Program :=
  List.replicate 20000 (.prim .add)

#guard largeProgram.byteLength = 20000

#guard decide (Assembly.Program.PCFitsFrom [] largeProgram)

end EvmCompiler.ProofArtifacts.AssemblyLargeProgram
