import EvmCompiler.Objects.Compiler

open EvmCompiler

namespace EvmCompiler.ProofArtifacts.InlineAllocationPlanner

def sourceProgram : Functions.Program :=
  Functions.ScratchFrameSpill.AllocationExamples.nestedProgram

def objectProgram : Objects.Program :=
  { root := .mk "InlineAllocationPlannerSmoke" sourceProgram [] [] }

def sourceDerivedLexicalPlanRecorded : Bool :=
  match Objects.Program.planInlineStack? objectProgram with
  | none => false
  | some planned =>
      decide
        (planned.backend = .inlineStack ∧
          planned.allocation.find? (.lexical .main 0) =
            some Functions.ScratchFrameSpill.AllocationExamples.nestedStackAllocationExpected)

example : sourceDerivedLexicalPlanRecorded = true := by
  native_decide

example :
    (Objects.Program.Backend.compileArtifact? {}
      objectProgram .inlineStack).isSome = true := by
  native_decide

def wideStatements : List Functions.Stmt :=
  (List.range 17).map fun idx =>
    .let_ ("wide_" ++ toString idx)
      (.lit (Functions.ScratchFrameSpill.word idx))

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
