import EvmCompiler.Objects.Compiler

open EvmCompiler

namespace EvmCompiler.ProofArtifacts.InlineAllocationPlanner

def sourceProgram : Functions.Program :=
  Functions.MixedAllocation.Examples.nestedProgram

def objectProgram : Objects.Program :=
  { root := .mk "InlineAllocationPlannerSmoke" sourceProgram [] [] }

def sourceDerivedLexicalPlanRecorded : Bool :=
  match Objects.Program.planInlineStack? objectProgram with
  | none => false
  | some planned =>
      match planned.loweringResult? with
      | none => false
      | some lowered =>
          decide
            (planned.allocation.find? (.lexical .main 0) =
              some Functions.MixedAllocation.Examples.nestedStackAllocationExpected) &&
            decide (lowered.backend = .inlineStack)

example : sourceDerivedLexicalPlanRecorded = true := by
  native_decide

example :
    (Objects.Program.Backend.compileArtifact? {}
      objectProgram .inlineStack).isSome = true := by
  native_decide

def wideStatements : List Functions.Stmt :=
  (List.range 17).map fun idx =>
    .let_ ("wide_" ++ toString idx)
      (.lit (Functions.AllocationSupport.word idx))

def wideSourceProgram : Functions.Program :=
  { functions := []
    body := { stmts := wideStatements } }

def wideObjectProgram : Objects.Program :=
  { root := .mk "ScratchFrameFallbackSmoke" wideSourceProgram [] [] }

example : Objects.Program.planInlineStack? wideObjectProgram = none := by
  native_decide

def wideFallbackUsesScratchFrame : Bool :=
  match Objects.Program.compileArtifact? wideObjectProgram with
  | none => false
  | some artifact =>
      decide (artifact.metadata.backend = .scratchFrameSpill)

example : wideFallbackUsesScratchFrame = true := by
  native_decide

end EvmCompiler.ProofArtifacts.InlineAllocationPlanner
