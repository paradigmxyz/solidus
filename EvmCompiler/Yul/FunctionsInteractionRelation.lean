import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Yul.InteractionSemantics

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRelation

abbrev SourceState := Yul.InteractionSemantics.State
abbrev TargetState := Functions.InteractionSemantics.State

/-- Protected active-frame data. External account implementation code is
intentionally absent; only the active byte image remains observable. -/
structure ExecutionEnvRel
    (source : EvmYul.ExecutionEnv .Yul)
    (target : EvmYul.ExecutionEnv .EVM) : Prop where
  codeOwner : source.codeOwner = target.codeOwner
  sender : source.sender = target.sender
  sourceAddress : source.source = target.source
  weiValue : source.weiValue = target.weiValue
  calldata : source.calldata = target.calldata
  gasPrice : source.gasPrice = target.gasPrice
  header : source.header = target.header
  depth : source.depth = target.depth
  permission : source.perm = target.perm
  blobVersionedHashes :
    source.blobVersionedHashes = target.blobVersionedHashes
  codeImage : source.codeBytes = target.code
  codeBytes : source.codeBytes = target.codeBytes

/-- Code-erased shared-state relation for the adjacent Yul-to-Functions pass. -/
structure SharedRel
    (source : EvmYul.SharedState .Yul)
    (target : EvmYul.SharedState .EVM) : Prop where
  openWorld :
    Simulation.OpenWorld.ofYulShared source =
      Simulation.OpenWorld.ofEVMShared target
  machine : source.toMachineState = target.toMachineState
  initialAccounts : source.σ₀ = target.σ₀
  totalGasUsedInBlock :
    source.totalGasUsedInBlock = target.totalGasUsedInBlock
  transactionReceipts :
    source.transactionReceipts = target.transactionReceipts
  executionEnv : ExecutionEnvRel source.executionEnv target.executionEnv
  blocks : source.blocks = target.blocks
  genesisBlockHeader :
    source.genesisBlockHeader = target.genesisBlockHeader

def VarsRel (source : EvmYul.Yul.VarStore)
    (target : Locals.Source.Store) : Prop :=
  ∀ name value, source.lookup name = some value →
    target name = some value

/-- Regular Yul states correspond to the stack-free Functions source state.
Compiler-private target locals may extend the source-visible store. -/
def StateRel (source : SourceState) (target : TargetState) : Prop :=
  ∃ sourceShared sourceVars,
    source = .Ok sourceShared sourceVars ∧
      SharedRel sourceShared target.shared ∧
      VarsRel sourceVars target.vars

namespace ExecutionEnvRel

theorem externalFrame_eq
    {source : EvmYul.ExecutionEnv .Yul}
    {target : EvmYul.ExecutionEnv .EVM}
    (hRel : ExecutionEnvRel source target)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    Simulation.ExternalFrame.mk sourceMachine source.codeOwner source.source
        source.weiValue source.perm =
      Simulation.ExternalFrame.mk targetMachine target.codeOwner target.source
        target.weiValue target.perm := by
  rcases hRel with
    ⟨hOwner, _hSender, hSource, hValue, _hCalldata, _hGasPrice,
      _hHeader, _hDepth, hPermission, _hBlobHashes, _hCodeImage,
      _hCodeBytes⟩
  simp [hMachine, hOwner, hSource, hValue, hPermission]

end ExecutionEnvRel

namespace SharedRel

theorem externalFrame_eq
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target) :
    Simulation.ExternalFrame.ofShared source =
      Simulation.ExternalFrame.ofShared target := by
  exact hRel.executionEnv.externalFrame_eq _ _ hRel.machine

/-- Installing one exact arbitrary response world and one related local
machine transition preserves the adjacent relation. -/
theorem withWorldAndMachine
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : SharedRel source target)
    (world : Simulation.OpenWorld)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    SharedRel
      { Simulation.OpenWorld.installYulShared source world with
        toMachineState := sourceMachine }
      { Simulation.OpenWorld.installEVMShared target world with
        toMachineState := targetMachine } := by
  refine
    { openWorld := by
        change
          Simulation.OpenWorld.ofYulShared
              (Simulation.OpenWorld.installYulShared source world) =
            Simulation.OpenWorld.ofEVMShared
              (Simulation.OpenWorld.installEVMShared target world)
        simp
      machine := hMachine
      initialAccounts := hRel.initialAccounts
      totalGasUsedInBlock := hRel.totalGasUsedInBlock
      transactionReceipts := hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := hRel.blocks
      genesisBlockHeader := hRel.genesisBlockHeader }

end SharedRel

namespace VarsRel

theorem empty :
    VarsRel (default : EvmYul.Yul.VarStore)
      Locals.Source.Store.empty := by
  intro name value hLookup
  change (none : Option Word) = some value at hLookup
  contradiction

end VarsRel

namespace StateRel

theorem lookup
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    {name : EvmYul.Identifier} {value : Word}
    (hLookup : source.lookup? name = some value) :
    target.vars name = some value := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  rw [hSource] at hLookup
  exact hVars name value (by simpa [EvmYul.Yul.State.lookup?] using hLookup)

theorem shared
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    SharedRel source.sharedState target.shared := by
  rcases hRel with ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  simpa [hSource] using hShared

theorem externalFrame_eq
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    Simulation.ExternalFrame.ofShared source.sharedState =
      Simulation.ExternalFrame.ofShared target.shared :=
  (shared hRel).externalFrame_eq

theorem openWorld_eq
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    Simulation.OpenWorld.ofYulShared source.sharedState =
      Simulation.OpenWorld.ofEVMShared target.shared :=
  (shared hRel).openWorld

/-- Arbitrary external post-worlds preserve source-visible locals and the
protected frame while installing exactly the same world on both sides. -/
theorem withWorldAndMachine
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target)
    (world : Simulation.OpenWorld)
    (sourceMachine targetMachine : EvmYul.MachineState)
    (hMachine : sourceMachine = targetMachine) :
    StateRel
      (Yul.InteractionSemantics.State.withWorldAndMachine
        source world sourceMachine)
      (target.withShared
        { Simulation.OpenWorld.installEVMShared target.shared world with
          toMachineState := targetMachine }) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  refine ⟨_, sourceVars, rfl, ?_, hVars⟩
  exact hShared.withWorldAndMachine world sourceMachine targetMachine hMachine

end StateRel

def VarsDomainWithin (layout : List Functions.Name)
    (source : EvmYul.Yul.VarStore) : Prop :=
  ∀ name value, source.lookup name = some value → name ∈ layout

/-- Regular adjacent relation plus the source-only lexical-domain fact needed
when Functions control exits restrict compiler-private target locals. -/
structure ScopedStateRel (layout : List Functions.Name)
    (source : SourceState) (target : TargetState) : Prop where
  state : StateRel source target
  domain :
    ∀ sourceShared sourceVars,
      source = .Ok sourceShared sourceVars →
        VarsDomainWithin layout sourceVars

namespace ScopedStateRel

theorem restrictTarget
    {layout scope : List Functions.Name}
    {source : SourceState} {target : TargetState}
    (hRel : ScopedStateRel layout source target)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope) :
    StateRel source (target.restrictTo scope) := by
  rcases hRel.state with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  refine ⟨sourceShared, sourceVars, hSource, by simpa, ?_⟩
  intro name value hLookup
  have hLayout : name ∈ layout :=
    hRel.domain sourceShared sourceVars hSource name value hLookup
  have hScope : name ∈ scope := hSubset name hLayout
  simpa [Locals.Source.State.restrictTo,
    Locals.Source.Store.restrictTo, hScope] using
    hVars name value hLookup

end ScopedStateRel

/-- Agreement between imported Yul checkpoints and canonical Functions
control outcomes. Yul's historical `OutOfFuel` state is not a terminal
control outcome and therefore relates to no Functions mode. -/
def ModeRel (source : SourceState)
    (target : Functions.InteractionSemantics.Outcome) : Prop :=
  match source, target.mode with
  | .Ok _ _, .regular => True
  | .Checkpoint (.Break _ _), .brk => True
  | .Checkpoint (.Continue _ _), .cont => True
  | .Checkpoint (.Leave _ _), .leave => True
  | _, _ => False

/-- Outcome-indexed adjacent state relation. Checkpoint payloads are revived
only for relating their shared state and visible locals; `ModeRel` retains
the exact control destination. -/
structure OutcomeRel (source : SourceState)
    (target : Functions.InteractionSemantics.Outcome) : Prop where
  mode : ModeRel source target
  state : StateRel source.reviveJump target.state

namespace OutcomeRel

theorem regular
    {source : SourceState} {target : TargetState}
    (hRel : StateRel source target) :
    OutcomeRel source
      (Functions.Source.Effectful.Outcome.regular target) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  exact ⟨trivial, ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩⟩

theorem brk
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : StateRel (.Ok sourceShared sourceVars) target) :
    OutcomeRel (.Checkpoint (.Break sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.brk target) :=
  ⟨trivial, hRel⟩

theorem cont
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : StateRel (.Ok sourceShared sourceVars) target) :
    OutcomeRel (.Checkpoint (.Continue sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.cont target) :=
  ⟨trivial, hRel⟩

theorem leave
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore} {target : TargetState}
    (hRel : StateRel (.Ok sourceShared sourceVars) target) :
    OutcomeRel (.Checkpoint (.Leave sourceShared sourceVars))
      (Functions.Source.Effectful.Outcome.leave target) :=
  ⟨trivial, hRel⟩

end OutcomeRel

end FunctionsInteractionRelation
end Yul
end EvmCompiler
