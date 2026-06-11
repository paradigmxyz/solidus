import EvmCompiler.Locals.SourceSemantics
import EvmCompiler.Simulation.ResourceReplay
import EvmYul.Yul.StateOps

namespace EvmCompiler
namespace Yul
namespace StateRelation

abbrev CodeRel :=
  EvmYul.Yul.Ast.YulContract → ByteArray → Prop

def OptionRel {α β : Type} (rel : α → β → Prop) :
    Option α → Option β → Prop
  | none, none => True
  | some left, some right => rel left right
  | _, _ => False

namespace ExecutionEnv

structure Rel (codeRel : CodeRel)
    (source : EvmYul.ExecutionEnv .Yul)
    (target : EvmYul.ExecutionEnv .EVM) : Prop where
  codeOwner : source.codeOwner = target.codeOwner
  sender : source.sender = target.sender
  sourceAddress : source.source = target.source
  weiValue : source.weiValue = target.weiValue
  calldata : source.calldata = target.calldata
  code : codeRel source.code target.code
  gasPrice : source.gasPrice = target.gasPrice
  header : source.header = target.header
  depth : source.depth = target.depth
  permission : source.perm = target.perm
  blobVersionedHashes :
    source.blobVersionedHashes = target.blobVersionedHashes
  codeBytes : source.codeBytes = target.codeBytes

end ExecutionEnv

namespace Account

structure Rel (codeRel : CodeRel)
    (source : EvmYul.Account .Yul)
    (target : EvmYul.Account .EVM) : Prop where
  nonce : source.nonce = target.nonce
  balance : source.balance = target.balance
  storage : source.storage = target.storage
  code : codeRel source.code target.code
  codeBytes : source.codeBytes = target.codeBytes
  transientStorage : source.tstorage = target.tstorage

end Account

namespace AccountMap

def Rel (codeRel : CodeRel)
    (source : EvmYul.AccountMap .Yul)
    (target : EvmYul.AccountMap .EVM) : Prop :=
  ∀ address,
    OptionRel (Account.Rel codeRel)
      (source.find? address) (target.find? address)

end AccountMap

namespace World

structure Rel (codeRel : CodeRel)
    (source : EvmYul.State .Yul)
    (target : EvmYul.State .EVM) : Prop where
  accounts : AccountMap.Rel codeRel source.accountMap target.accountMap
  initialAccounts : source.σ₀ = target.σ₀
  totalGasUsedInBlock :
    source.totalGasUsedInBlock = target.totalGasUsedInBlock
  transactionReceipts :
    source.transactionReceipts = target.transactionReceipts
  substate : source.substate = target.substate
  executionEnv :
    ExecutionEnv.Rel codeRel source.executionEnv target.executionEnv
  blocks : source.blocks = target.blocks
  genesisBlockHeader :
    source.genesisBlockHeader = target.genesisBlockHeader
  createdAccounts : source.createdAccounts = target.createdAccounts

end World

namespace Shared

structure Rel (codeRel : CodeRel)
    (source : EvmYul.SharedState .Yul)
    (target : EvmYul.SharedState .EVM) : Prop where
  world : World.Rel codeRel source.toState target.toState
  machine : source.toMachineState = target.toMachineState

end Shared

namespace Vars

def Rel (source : EvmYul.Yul.VarStore)
    (target : Locals.Source.Store) : Prop :=
  ∀ name, source.lookup name = target name

theorem empty :
    Rel (default : EvmYul.Yul.VarStore) Locals.Source.Store.empty := by
  intro name
  rfl

theorem insert
    {source : EvmYul.Yul.VarStore} {target : Locals.Source.Store}
    (hRel : Rel source target) (name : EvmYul.Identifier)
    (value : Assembly.Word) :
    Rel (source.insert name value)
      (Locals.Source.Store.insert target name value) := by
  intro key
  by_cases hKey : key = name
  · subst key
    simp [Locals.Source.Store.insert]
  · simpa [hKey, Locals.Source.Store.insert] using hRel key

end Vars

namespace Regular

def Rel (codeRel : CodeRel)
    (source : EvmYul.Yul.State)
    (target : Locals.Source.State) : Prop :=
  ∃ sourceShared : EvmYul.SharedState .Yul,
    ∃ sourceVars : EvmYul.Yul.VarStore,
      source = .Ok sourceShared sourceVars ∧
        Shared.Rel codeRel sourceShared target.shared ∧
        Vars.Rel sourceVars target.vars

theorem multifill_single
    {codeRel : CodeRel} {source : EvmYul.Yul.State}
    {target : Locals.Source.State}
    (hRel : Rel codeRel source target)
    (name : EvmYul.Identifier) (value : Assembly.Word) :
    Rel codeRel (source.multifill [name] [value])
      (target.insert name value) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  refine
    ⟨sourceShared, sourceVars.insert name value, ?_, hShared,
      Vars.insert hVars name value⟩
  simp [EvmYul.Yul.State.multifill, EvmYul.Yul.State.insert]

end Regular

namespace Replay

def Rel {transcript : Assembly.ResourceTrace} (codeRel : CodeRel)
    (source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript)
    (target :
      Simulation.ResourceReplay.State Locals.Source.State transcript) : Prop :=
  source.cursor = target.cursor ∧
    Regular.Rel codeRel source.source target.source

theorem consumedExactly_iff
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.ConsumedExactly ↔ target.ConsumedExactly := by
  change source.cursor = transcript.length ↔
    target.cursor = transcript.length
  rw [hRel.1]

theorem observed_eq
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.observed = target.observed := by
  simp only [Simulation.ResourceReplay.State.observed]
  rw [hRel.1]

theorem remaining_eq
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target) :
    source.remaining = target.remaining := by
  simp only [Simulation.ResourceReplay.State.remaining]
  rw [hRel.1]

theorem multifill_single
    {transcript : Assembly.ResourceTrace} {codeRel : CodeRel}
    {source :
      Simulation.ResourceReplay.State EvmYul.Yul.State transcript}
    {target :
      Simulation.ResourceReplay.State Locals.Source.State transcript}
    (hRel : Rel codeRel source target)
    (name : EvmYul.Identifier) (value : Assembly.Word) :
    Rel codeRel
      (source.withSource (source.source.multifill [name] [value]))
      (target.withSource (target.source.insert name value)) := by
  exact
    ⟨hRel.1, Regular.multifill_single hRel.2 name value⟩

end Replay

end StateRelation
end Yul
end EvmCompiler
