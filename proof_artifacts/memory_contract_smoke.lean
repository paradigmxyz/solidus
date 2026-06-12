import EvmCompiler.Solidity.Frontend
import EvmCompiler.Functions.AllocationLowering

namespace EvmCompiler.ProofArtifacts.MemoryContractSmoke

open Solidity.Frontend

def guardSize : EvmYul.UInt256 :=
  EvmYul.UInt256.ofNat 128

def guardObject : Solidity.Frontend.Object :=
  { name := "Guarded"
    dispatcher :=
      [ .letDecl ["ptr"]
          (some
            (.call .objectBuiltin "memoryguard"
              [.lit guardSize])) ]
    functions := []
    data := []
    objects := []
    items := [] }

def guardContract : MemoryContract.Contract :=
  { scratch? :=
      some
        { base := 128
          words := MemoryContract.defaultReservedWords } }

example :
    Solidity.Frontend.MemoryGuard.Object.inferredContract? guardObject =
      some guardContract := by
  native_decide

def emptyLayout : Solidity.Frontend.ObjectLayout :=
  { entries := [] }

def resolvedPointer? : Option EvmYul.UInt256 := do
  let resolved ← guardObject.resolveObjectBuiltins? emptyLayout
  match resolved.dispatcher with
  | [.letDecl _ (some (.lit value))] =>
      some value
  | _ =>
      none

example :
    resolvedPointer? =
      MemoryContract.returnedPointer? guardContract := by
  native_decide

def guardedWideProgram : Functions.Program :=
  { Functions.MixedAllocation.Examples.wideProgram with
    memoryContract := guardContract }

def guardedWidePlan : Option Locals.Allocation.ProgramPlan :=
  Functions.MixedAllocation.planAllocation?
    8192 [] guardedWideProgram

example :
    (guardedWidePlan.map fun plan =>
      decide (plan.MemoryAuthorized guardedWideProgram.memoryContract)) =
        some true := by
  native_decide

example :
    (do
      let allocation ← guardedWidePlan
      Functions.AllocationLowering.lowerExpressionsFromAllocation?
        allocation guardedWideProgram).isSome = true := by
  native_decide

end EvmCompiler.ProofArtifacts.MemoryContractSmoke
