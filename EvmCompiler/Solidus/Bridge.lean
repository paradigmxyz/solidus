import EvmCompiler.Assembly.StateRelation
import EvmCompiler.Assembly.Semantics
import EvmCompiler.Simulation.Interaction
import EvmCompiler.Simulation.OpenWorld
import EvmYul.EVM.Semantics

/-!
# Frozen bridge relations (Solidus Arena freeze cone)

This module holds the statement-level relations that pin the meaning of the
gasful/open refinement conjunct of `EvmCompiler.Solidus.compile_correct`.
They were relocated here out of the mutable, proof-machinery-dominated
`EvmCompiler/Assembly/GasfulBridge.lean` (378 lemmas) and
`EvmCompiler/Yul/GasfulCrown.lean` so that an adversary who is free to rewrite
the compiler and its proofs cannot redefine these relations (e.g.
`DoneRel := fun _ _ => True`) while leaving the frozen file hashes unchanged.

Everything here is pure specification: it references only the frozen state
vocabulary (`Assembly.StateRelation`, `Assembly.Semantics`), the semantic
framework (`Simulation.Interaction`, `Simulation.OpenWorld`), and the pinned
`EvmYul` interpreter (`EVM.X`/`Ξ`/`Θ`/`D_J`). The definitions keep their
original fully-qualified names and `EvmCompiler.Assembly.GasfulBridge`
namespace, so all downstream references remain valid; the original files gain
an `import` of this module.
-/

namespace EvmCompiler
namespace Assembly
namespace GasfulBridge

open Simulation

/-- Erase the mutable open world as well as gas/control, retaining only the
frame-local data that emitted bytecode can compare across an external
request/response boundary. -/
def eraseOpenWorldData (state : EVMState) : EVMState :=
  { eraseControl state with
    accountMap := ∅
    substate := default
    createdAccounts := ∅ }

/-- Honest gas-erased relation at an external boundary. Mutable accounts,
substate, and created-account tracking are compared through the code-erased
`OpenWorld` projection; protected frame-local data is compared directly after
erasing gas and interpreter control. -/
structure OpenSameData (left right : EVMState) : Prop where
  world :
    OpenWorld.ofEVMShared left.toSharedState =
      OpenWorld.ofEVMShared right.toSharedState
  frame : eraseOpenWorldData left = eraseOpenWorldData right

/-- Recursive gasful/open state invariant. The mutable world is compared
through its normalized open projection, frame-local data ignores gas/control,
and the current PC remains exact so both runners decode the same instruction. -/
structure OpenStateRel (gasful openState : EVMState) : Prop where
  openData : OpenSameData gasful openState
  pc_eq : gasful.pc = openState.pc

/-- Canonical charged-frame entry state used to relate `EVM.X` at a code
boundary to the frame-collapsing `Ξ`/`Θ` message-call semantics. -/
def xiEntryState
    (createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare)
    (genesisBlockHeader : EvmYul.BlockHeader)
    (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (chainContext : EvmYul.EVM.ChildFrameChainContext)
    (g : EvmYul.UInt256)
    (A : EvmYul.Substate)
    (I : EvmYul.ExecutionEnv .EVM) : EVMState :=
  let defState : EvmYul.EVM.State := default
  { defState with
      accountMap := σ
      σ₀ := σ₀
      totalGasUsedInBlock := chainContext.totalGasUsedInBlock
      transactionReceipts := chainContext.transactionReceipts
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
  }

/-- Terminal-leaf relation between a charged `EVM.X` result and an open
bytecode done-value: a success pins output and the code-erased world
(`OpenSameData`), a revert pins output, and errors are forwarded. -/
inductive DoneRel :
    Except EVMException (EvmYul.EVM.ExecutionResult EVMState) →
    Except EVMException StepResult → Prop where
  | success {gasful openState output haltKind} :
      OpenSameData gasful openState →
      DoneRel
        (.ok (.success gasful output))
        (.ok (.halted
          { kind := haltKind, state := openState, output := output }))
  | revert {gas output openState} :
      DoneRel
        (.ok (.revert gas output))
        (.ok (.halted
          { kind := .revert, state := openState, output := output }))
  | sameError {err} :
      DoneRel (.error err) (.error err)

/-- Committal out-of-gas outcome. Beyond naming the exceptional label of the
charged run, this pins what the EVM's frame semantics does with it: the run is
exactly `.error .OutOfGass`, a code-execution boundary `Ξ` entered at this run
reports the same exceptional halt, and a message-call boundary `Θ` built on it
commits to the canonical exceptional-halt collapse — the caller's world and
substate are restored to the checkpoint, zero gas is returned, the failure
flag is set, and the output data is empty. -/
structure OutOfGasFrameSemantics
    (gasful :
      Except EVMException (EvmYul.EVM.ExecutionResult EVMState)) : Prop where
  halted : gasful = .error EvmYul.EVM.ExecutionException.OutOfGass
  xiExceptional :
    ∀ {f : Nat}
      {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
      {genesisBlockHeader : EvmYul.BlockHeader}
      {blocks : EvmYul.ProcessedBlocks}
      {σ σ₀ : EvmYul.AccountMap .EVM}
      {chainContext : EvmYul.EVM.ChildFrameChainContext}
      {g : EvmYul.UInt256}
      {A : EvmYul.Substate}
      {I : EvmYul.ExecutionEnv .EVM},
      EvmYul.EVM.X f (EvmYul.EVM.D_J I.code ⟨0⟩)
        (xiEntryState createdAccounts genesisBlockHeader blocks σ σ₀
          chainContext g A I) = gasful →
      EvmYul.EVM.Ξ (f + 1) createdAccounts genesisBlockHeader blocks σ σ₀
        chainContext g A I =
        .error EvmYul.EVM.ExecutionException.OutOfGass
  thetaRollback :
    ∀ {f : Nat}
      {blobVersionedHashes : List ByteArray}
      {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
      {genesisBlockHeader : EvmYul.BlockHeader}
      {blocks : EvmYul.ProcessedBlocks}
      {σ σ₀ : EvmYul.AccountMap .EVM}
      {chainContext : EvmYul.EVM.ChildFrameChainContext}
      {A : EvmYul.Substate}
      {s o r : EvmYul.AccountAddress}
      {code : ByteArray}
      {g p v v' : EvmYul.UInt256}
      {d : ByteArray}
      {e : Nat}
      {H : EvmYul.BlockHeader}
      {w : Bool},
      EvmYul.EVM.X f
        (EvmYul.EVM.D_J
          (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes s o r
            (EvmYul.ToExecute.Code code) p v' d e H w).code ⟨0⟩)
        (xiEntryState createdAccounts genesisBlockHeader blocks
          (EvmYul.EVM.thetaCallTransfer σ s r v) σ₀ chainContext g A
          (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes s o r
            (EvmYul.ToExecute.Code code) p v' d e H w)) = gasful →
      EvmYul.EVM.Θ (f + 2) blobVersionedHashes createdAccounts
        genesisBlockHeader blocks σ σ₀ chainContext A s o r
        (EvmYul.ToExecute.Code code) g p v v' d e H w =
        .ok (createdAccounts, σ, ⟨0⟩, A, false, ByteArray.empty)

/-- Bridge outcomes with every escape constructor removed. The charged run
either reaches a related terminal leaf, collapses an exceptional frame
together with the open run (and the charged label is provably none of
`OutOfFuel`, `StackOverflow`, `BadJumpDestination`), or halts out-of-gas with
the committal frame-boundary semantics (`Ξ` exceptional halt, `Θ` checkpoint
rollback with zero returned gas, failure flag, empty output). -/
inductive RunRefinesOpenTotal
    (gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (openRun : Simulation.Interaction EVMException StepResult) :
    Simulation.Interaction.Transcript → Prop where
  | completed {transcript openDone} :
      Simulation.Interaction.Executes openRun transcript openDone →
      DoneRel gasful openDone →
      RunRefinesOpenTotal gasful openRun transcript
  | exceptionalFrame {transcript gasErr openErr} :
      gasErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasErr ≠ EvmYul.EVM.ExecutionException.StackOverflow →
      gasErr ≠ EvmYul.EVM.ExecutionException.BadJumpDestination →
      openErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasful = .error gasErr →
      Simulation.Interaction.Executes openRun transcript (.error openErr) →
      RunRefinesOpenTotal gasful openRun transcript
  | outOfGas {transcript} :
      OutOfGasFrameSemantics gasful →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenTotal gasful openRun transcript

end GasfulBridge
end Assembly
end EvmCompiler
