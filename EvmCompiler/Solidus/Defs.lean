import EvmCompiler.Assembly.Semantics
import EvmCompiler.Simulation.OpenWorld
import EvmCompiler.Yul.InteractionSemantics
import EvmCompiler.Yul.Installation
import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.StackHeadroomEndToEnd

/-!
# Solidus spec vocabulary

Frozen definitions for the public correctness statement. Everything the top
theorem (`Solidus.compile_correct` in `EvmCompiler/Correctness.lean`) says is
said in terms of the definitions in this file plus the pinned `EvmYul`
interpreter and the repository's semantic framework (`Simulation.OpenWorld`,
`Simulation.Interaction`, the Yul interaction semantics, and the open
assembly interpreter). No compiler pass structure appears here.

Two definitions reference the mutable compiler by name (`compile?` wraps the
raw-solc entry point and the fail-closed stack-headroom check). That is the
point of the freeze: the *signature and wrapper* are pinned while the
implementation behind them is free to change.

## The observable outcome relation

`ObservableDoneRel` relates a finished source-side Yul run to a finished
open-bytecode run. One honesty note: the imported Yul semantics represents
`stop`, `return`, and `selfdestruct` with a single exception constructor
(`.YulHalt`), so a finished source value pins the halt kind only up to that
three-element set. What distinguishes those kinds observably — the returned
bytes: empty for `stop`/`selfdestruct`, the return buffer for `return` — is
pinned exactly by the `output` field.
-/

namespace EvmCompiler
namespace Solidus

/-- The public compilation entry point. Fail-closed: compilation succeeds
only if the raw-solc pipeline produces an artifact AND the stack-headroom
certificate for its code image checks. The result is the deployed byte
image; nothing else about the compiler's internals is exposed. -/
def compile? (rawJson : String) (selection : Solidity.RawAst.Selection) :
    Option (List UInt8) := do
  let artifact ← Solidity.RawAst.compileArtifactFromRawSolcIr? rawJson selection
  let _ ← artifact.stackHeadroomCert?
  pure artifact.image.bytes

/-- Exception agreement for forwarded errors. On the EVM every non-revert
exception is observationally identical — an exceptional frame halt — so the
spec does not claim the exception's identity survives compilation (reverts
are a separate `ObservableDoneRel` constructor and ARE pinned). The one
semantically meaningful guarantee is directional: a structural out-of-fuel
error on the compiled side can only arise from source fuel exhaustion —
the compiler cannot manufacture fuel failures. The charged-run theorem
(`RunRefinesOpenTotal`) independently excludes out-of-fuel there. -/
def ExceptionRel (source : EvmYul.Yul.Exception)
    (target : Assembly.EVMException) : Prop :=
  target = .OutOfFuel → source = .OutOfFuel

/-- Observable agreement between a finished source shared state and a final
EVM state: the code-erased open world (nonces, balances, storage, transient
storage, code images) coincides, and the machine data a caller or later
frame could observe — remaining gas, active memory words, memory contents,
and the return buffer — coincides. The return-data scratch register is
deliberately absent: EVM `STOP` clears it, the imported Yul semantics does
not, and nothing can observe it after the frame ends. -/
structure FinalStateObs (source : EvmYul.SharedState .Yul)
    (target : Assembly.EVMState) : Prop where
  world :
    Simulation.OpenWorld.ofYulShared source =
      Simulation.OpenWorld.ofEVMShared target.toSharedState
  gasAvailable : source.gasAvailable = target.gasAvailable
  activeWords :
    source.toMachineState.activeWords = target.toMachineState.activeWords
  memory : source.toMachineState.memory = target.toMachineState.memory
  returnBuffer :
    source.toMachineState.H_return = target.toMachineState.H_return

/-- Frozen observable done relation between a finished source-side Yul run
and a finished open-bytecode run. Every constructor pins the open world, the
observable machine data, and the produced output. A source run that
completes normally is observable as an on-chain `stop` — empty output, and
the return buffer is cleared by the STOP, so the final-state comparison is
taken with the source's stale pre-STOP buffer scratch cleared (its content
is unobservable; this mirrors the existing returnData-scratch exclusion
rationale in `FinalStateObs`'s docstring). Explicit halts pin the halt kind
(up to the source semantics' `.YulHalt` conflation of
`stop`/`return`/`selfdestruct` — see the module docstring), reverts pin
`revert` exactly, and forwarded errors are mapped by `ExceptionRel`. -/
inductive ObservableDoneRel :
    Except Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State →
      Assembly.Source.ExecutionOutcome → Prop where
  | regular {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
      {halt : Assembly.Halt} :
      halt.kind = .stop →
      FinalStateObs { shared with H_return := ByteArray.empty } halt.state →
      halt.output = halt.kind.output halt.state →
      ObservableDoneRel (.ok (.Ok shared vars)) (.ok (.halted halt))
  | halt {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
      {value : EvmYul.UInt256}
      {failState : Yul.InteractionSemantics.State}
      {halt : Assembly.Halt} :
      (halt.kind = .stop ∨ halt.kind = .return ∨ halt.kind = .selfdestruct) →
      FinalStateObs shared halt.state →
      halt.output = halt.kind.output halt.state →
      ObservableDoneRel
        (.error { exception := .YulHalt (.Ok shared vars) value
                  state := failState })
        (.ok (.halted halt))
  | revert {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
      {failState : Yul.InteractionSemantics.State}
      {halt : Assembly.Halt} :
      halt.kind = .revert →
      FinalStateObs shared halt.state →
      halt.output = halt.kind.output halt.state →
      ObservableDoneRel
        (.error { exception := .Revert (.Ok shared vars)
                  state := failState })
        (.ok (.halted halt))
  | error {failure : Yul.InteractionSemantics.Failure}
      {exception : Assembly.EVMException} :
      ExceptionRel failure.exception exception →
      ObservableDoneRel (.error failure) (.error exception)

/-- The source-side initial state: `base` with the compiled image installed
as the executing contract's code at the frame owner's account, entered with
an empty variable store. The installed AST slot is existential: the imported
Yul semantics stores a contract AST alongside the code image (re-entrant
self-calls dispatch through it), and the compiler installs its own
elaboration of the source there. Every observable field — the code image,
the open world, the machine state, and the execution frame — is pinned by
`installContractWithCodeImage` regardless of the AST choice. -/
def InstalledSource (bytes : List UInt8) (base : EvmYul.SharedState .Yul)
    (state : Yul.InteractionSemantics.State) : Prop :=
  ∃ contract : Yul.AstContract,
    state = .Ok
      (Yul.Source.Installation.installContractWithCodeImage contract
        (Assembly.Bytecode.ofList bytes) base)
      default

/-- The EVM execution environment of the installed frame: the source frame's
fields with the compiled image as the active code. -/
def installedExecutionEnv (image : ByteArray)
    (env : EvmYul.ExecutionEnv .Yul) : EvmYul.ExecutionEnv .EVM where
  codeOwner := env.codeOwner
  sender := env.sender
  source := env.source
  weiValue := env.weiValue
  calldata := env.calldata
  code := image
  gasPrice := env.gasPrice
  header := env.header
  depth := env.depth
  perm := env.perm
  blobVersionedHashes := env.blobVersionedHashes
  codeBytes := image

/-- The open world of `base` with the compiled image installed as the frame
owner's account code. -/
def installedWorld (image : ByteArray) (base : EvmYul.SharedState .Yul) :
    Simulation.OpenWorld :=
  let world := Simulation.OpenWorld.ofYulShared base
  let owner := base.executionEnv.codeOwner
  let account := (base.accountMap.find? owner).getD default
  { world with
    accounts :=
      world.accounts.insert owner
        { Simulation.OpenAccount.ofYul account with codeBytes := image } }

/-- The canonical target start state for a deployed image `bytes` over the
source world `base`: the installed open world, the installed execution
environment, `base`'s machine state and transaction-level fields, program
counter `0`, and an empty operand stack. The gas-charged initial state of
the public theorem is related to this state by
`Assembly.GasfulBridge.OpenStateRel`, which pins every field except the
available gas. -/
def installedTarget (bytes : List UInt8) (base : EvmYul.SharedState .Yul) :
    Assembly.EVMState :=
  let image := Assembly.Bytecode.ofList bytes
  { toSharedState :=
      Simulation.OpenWorld.installEVMShared
        { toState :=
            { accountMap := default
              σ₀ := base.σ₀
              totalGasUsedInBlock := base.totalGasUsedInBlock
              transactionReceipts := base.transactionReceipts
              substate := base.substate
              executionEnv := installedExecutionEnv image base.executionEnv
              blocks := base.blocks
              genesisBlockHeader := base.genesisBlockHeader
              createdAccounts := base.createdAccounts }
          toMachineState := base.toMachineState }
        (installedWorld image base)
    pc := EvmYul.UInt256.ofNat 0
    stack := []
    execLength := 0 }

end Solidus
end EvmCompiler
