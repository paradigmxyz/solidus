import EvmCompiler.Compiler.StackArtifact
import EvmCompiler.TypedCfg.ReturnAddressProbe

namespace EvmCompiler
namespace TypedCfg
namespace LateReturnProbe

/-!
Projection for late return-address materialisation.

Logical return tokens remain ordinary words throughout calls and procedure
bodies.  A return dispatcher validates the token while accumulating the
selected physical destination, removes the logical token, and performs one
dynamic jump.  Physical label values therefore exist only inside the
dispatcher rather than across arbitrary procedure execution.
-/

namespace Terminator

def standardReturnSiteLimit : Nat := 3

def firstSelection (site : ReturnSite) : Assembly.Program :=
  [ Assembly.StackShuffle.dupInstr 1
  , .push site.token
  , .prim .eq
  , .pushLabel site.target
  , .prim .mul
  ]

def nextSelection (site : ReturnSite) : Assembly.Program :=
  [ Assembly.StackShuffle.dupInstr 2
  , .push site.token
  , .prim .eq
  , .pushLabel site.target
  , .prim .mul
  , .prim .add
  ]

def selectionCode : List ReturnSite → Assembly.Program
  | [] => []
  | first :: rest =>
      firstSelection first ++ rest.flatMap nextSelection

def dynamicReturnCode (depth : Nat) : List ReturnSite → Assembly.Program
  | [] => []
  | first :: rest =>
      Assembly.StackShuffle.guardedLiftBuriedToTop depth ++
        selectionCode (first :: rest) ++
          Assembly.StackShuffle.removeBuriedUnder 1 ++
            [ Assembly.StackShuffle.dupInstr 1
            , .jumpi first.caseLabel
            , .prim .invalid
            , .label first.caseLabel
            , .jumpDynamic
            ]

def lowerAt? (shape : Shape) : TypedCfg.Terminator →
    Option Assembly.Program
  | term@(.returnDispatch returnCount sites) =>
      if sites.length ≤ standardReturnSiteLimit then
        term.lowerAt? shape
      else do
        let depth ← shape.returnTokenDepth?
        if sites.isEmpty ∨ depth ≠ returnCount then
          none
        else if depth < 16 then
          some (dynamicReturnCode depth sites)
        else
          none
  | term => term.lowerAt? shape

theorem standard_lowerAt?_of_lowerAt?_direct
    {shape : Shape} {term : TypedCfg.Terminator}
    {code : Assembly.Program}
    (hDirect : TypedCfg.Preservation.Terminator.Direct term)
    (hLower : lowerAt? shape term = some code) :
    TypedCfg.Terminator.lowerAt? shape term = some code := by
  cases term with
  | fallthrough next => exact hLower
  | jump target => exact hLower
  | jumpi target next => exact hLower
  | returnDispatch returnCount sites =>
      simp [TypedCfg.Preservation.Terminator.Direct] at hDirect
  | halt kind => exact hLower
  | invalid => exact hLower

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

theorem lower?_starts_with_label
    {block : TypedCfg.Block} {code : Assembly.Program}
    (hLower : lower? block = some code) :
    ∃ tail, code = Assembly.Instr.label block.label :: tail := by
  unfold lower? at hLower
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm :
            Terminator.lowerAt? block.output block.term with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            exact ⟨body ++ term, rfl⟩
      · simp [hBody, hOutput] at hLower

theorem target_instr_mem_of_lower?_of_direct
    {block : TypedCfg.Block} {code : Assembly.Program}
    {target : Label}
    (hLower : lower? block = some code)
    (hDirect :
      TypedCfg.Preservation.Terminator.Direct block.term)
    (hTarget : target ∈ block.term.targets) :
    ∃ instr,
      instr ∈ code ∧ target ∈ instr.targets := by
  unfold lower? at hLower
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm :
            Terminator.lowerAt? block.output block.term with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            have hStandard :=
              Terminator.standard_lowerAt?_of_lowerAt?_direct
                hDirect hTerm
            rcases
                TypedCfg.Terminator.target_instr_mem_of_lowerAt?
                  hStandard hTarget with
              ⟨instr, hInstr, hInstrTarget⟩
            exact
              ⟨instr,
                by
                  simp only [List.mem_cons]
                  exact Or.inr
                    (List.mem_append_right body hInstr),
                hInstrTarget⟩
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

def lowerBlocks? : List TypedCfg.Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← Block.lower? block
      let tail ← lowerBlocks? rest
      some (head ++ tail)

def lower? (program : TypedCfg.Program) : Option Assembly.Program := do
  let blocks ← program.blocksInLoweringOrder?
  lowerBlocks? blocks

theorem lowerBlocks?_starts_with_label
    {block : TypedCfg.Block} {rest : List TypedCfg.Block}
    {target : Assembly.Program}
    (hLower : lowerBlocks? (block :: rest) = some target) :
    ∃ tail, target = .label block.label :: tail := by
  unfold lowerBlocks? at hLower
  cases hHead : Block.lower? block with
  | none =>
      simp [hHead] at hLower
  | some head =>
      cases hTail : lowerBlocks? rest with
      | none =>
          simp [hHead, hTail] at hLower
      | some tail =>
          simp [hHead, hTail] at hLower
          subst target
          rcases Block.lower?_starts_with_label hHead with
            ⟨headTail, rfl⟩
          exact ⟨headTail ++ tail, by simp⟩

theorem lower?_starts_with_entry_label
    {program : TypedCfg.Program} {target : Assembly.Program}
    (hLower : lower? program = some target) :
    ∃ tail, target = .label program.entry :: tail := by
  unfold lower? at hLower
  cases hOrder : program.blocksInLoweringOrder? with
  | none =>
      simp [hOrder] at hLower
  | some blocks =>
      simp [hOrder] at hLower
      unfold TypedCfg.Program.blocksInLoweringOrder? at hOrder
      cases hExtract :
          TypedCfg.Program.extractBlock? program.blocks program.entry with
      | none =>
          simp [hExtract] at hOrder
      | some result =>
          rcases result with ⟨entry, remaining⟩
          simp [hExtract] at hOrder
          subst blocks
          have hEntry : entry.label = program.entry :=
            TypedCfg.Program.extractBlock?_label hExtract
          rcases lowerBlocks?_starts_with_label hLower with
            ⟨tail, hTarget⟩
          rw [hEntry] at hTarget
          exact ⟨tail, hTarget⟩

theorem lower?_entry_labelPc_zero
    {program : TypedCfg.Program} {target : Assembly.Program}
    (hLower : lower? program = some target) :
    target.labelPc program.entry = some 0 := by
  rcases lower?_starts_with_entry_label hLower with ⟨tail, rfl⟩
  simp [Assembly.Program.labelPc, Assembly.Program.labelPcFrom]

structure BlockFragment
    (target : Assembly.Program) (block : TypedCfg.Block) where
  pre : Assembly.Program
  code : Assembly.Program
  post : Assembly.Program
  lower : Block.lower? block = some code
  target_eq : target = pre ++ code ++ post

theorem lowerBlocks?_fragment_of_mem
    {blocks : List TypedCfg.Block} {target : Assembly.Program}
    {block : TypedCfg.Block}
    (hLower : lowerBlocks? blocks = some target)
    (hMem : block ∈ blocks) :
    Nonempty (BlockFragment target block) := by
  induction blocks generalizing target with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold lowerBlocks? at hLower
      cases hHead : Block.lower? head with
      | none =>
          simp [hHead] at hLower
      | some headCode =>
          cases hTail : lowerBlocks? rest with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailCode =>
              simp [hHead, hTail] at hLower
              subst target
              simp only [List.mem_cons] at hMem
              cases hMem with
              | inl hEq =>
                  subst block
                  exact
                    ⟨{ pre := []
                       code := headCode
                       post := tailCode
                       lower := hHead
                       target_eq := by simp }⟩
              | inr hRest =>
                  rcases ih hTail hRest with ⟨fragment⟩
                  exact
                    ⟨{ pre := headCode ++ fragment.pre
                       code := fragment.code
                       post := fragment.post
                       lower := fragment.lower
                       target_eq := by
                         calc
                           headCode ++ tailCode =
                               headCode ++
                                 (fragment.pre ++ fragment.code ++
                                   fragment.post) :=
                             congrArg (headCode ++ ·)
                               fragment.target_eq
                           _ =
                               (headCode ++ fragment.pre) ++
                                 fragment.code ++ fragment.post := by
                             simp [List.append_assoc] }⟩

theorem lower?_fragment_of_findBlock?
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    (hLower : lower? program = some target)
    (hFind : program.findBlock? label = some block) :
    Nonempty (BlockFragment target block) := by
  unfold lower? at hLower
  cases hOrder : program.blocksInLoweringOrder? with
  | none =>
      simp [hOrder] at hLower
  | some blocks =>
      simp [hOrder] at hLower
      have hMemSource : block ∈ program.blocks :=
        List.mem_of_find?_eq_some hFind
      have hPerm :=
        TypedCfg.Program.blocksInLoweringOrder?_perm hOrder
      have hMemOrdered : block ∈ blocks :=
        hPerm.mem_iff.mp hMemSource
      exact lowerBlocks?_fragment_of_mem hLower hMemOrdered

/--
Executable fail-closed gate for the zero sentinel used by the late dispatcher.
All logical return targets must resolve, and their encoded words must be
nonzero.
-/
def returnTargetsResolveNonzero?
    (program : TypedCfg.Program) (assembly : Assembly.Program) : Bool :=
  (ReturnAddressLower.Program.returnSites program).all fun site =>
    match assembly.labelPc site.target with
    | none => false
    | some dest =>
        decide
          (EvmYul.UInt256.ofNat dest ≠ EvmYul.UInt256.ofNat 0)

/-- Each return dispatcher must map tokens injectively within its own cases. -/
def localReturnTokensUnique? (program : TypedCfg.Program) : Bool :=
  program.blocks.all fun block =>
    ReturnAddressRelation.tokensUnique?
      (ReturnAddressLower.Terminator.sites block.term)

end Program

namespace CompiledBlock

/-- Instruction budget for one block under late return materialisation. -/
def fuelBudget (block : TypedCfg.Block) : Nat :=
  match TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none => 0
  | some (bodyCode, output) =>
      if output = block.output then
        match Terminator.lowerAt? output block.term with
        | none => 0
        | some termCode => 1 + bodyCode.length + termCode.length
      else
        0

/--
Execute one late-lowered block through the same Assembly-owned runners used by
the standard lowering adapter.
-/
def openRun (block : TypedCfg.Block)
    (program : Assembly.Program) (state : Assembly.EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      .done (.error .InvalidInstruction)
  | some (bodyCode, output) =>
      if output = block.output then
        match Terminator.lowerAt? output block.term with
        | none =>
            .done (.error .InvalidInstruction)
        | some termCode => do
            let labelResult ←
              Assembly.InteractionSemantics.Source.openRunNResult
                program 1 state
            match labelResult with
            | .halted halt =>
                pure (.halted halt)
            | .running entry =>
                let bodyResult ←
                  Assembly.InteractionSemantics.Source.openRunNResult
                    program bodyCode.length entry
                match bodyResult with
                | .halted halt =>
                    pure (.halted halt)
                | .running mid =>
                    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                        block.term)
                      program termCode.length mid
      else
        .done (.error .InvalidInstruction)

end CompiledBlock

namespace CompiledProgram

def fuelBudget (source : TypedCfg.Program) : Nat :=
  (source.blocks.map CompiledBlock.fuelBudget).sum

def openStep (source : TypedCfg.Program)
    (target : Assembly.Program) (state : Assembly.EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match target.instrAtPc state.pc.toNat with
  | some (_, .label label) =>
      match source.findBlock? label with
      | some block =>
          CompiledBlock.openRun block target state
      | none =>
          .done (.error .InvalidInstruction)
  | _ =>
      .done (.error .InvalidInstruction)

def openRunN (source : TypedCfg.Program)
    (target : Assembly.Program) (fuel : Nat)
    (state : Assembly.EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  Assembly.Control.runNResultWith
    (openStep source target) fuel state

@[simp] theorem openRunN_zero
    (source : TypedCfg.Program) (target : Assembly.Program)
    (state : Assembly.EVMState) :
    openRunN source target 0 state =
      .done (.ok (.running state)) := rfl

theorem openRunN_succ
    (source : TypedCfg.Program) (target : Assembly.Program)
    (fuel : Nat) (state : Assembly.EVMState) :
    openRunN source target (fuel + 1) state =
      (do
        let result ← openStep source target state
        match result with
        | .running state' =>
            openRunN source target fuel state'
        | .halted halt =>
            pure (.halted halt)) := rfl

end CompiledProgram

structure Artifact where
  cfg : TypedCfg.Program
  assembly : Assembly.Program
  compact : ReturnAddressProbe.Compact.Artifact

def compileCfg? (cfg : TypedCfg.Program) : Option Artifact := do
  let optimized ← ReturnAddressProbe.optimizedCfg? cfg
  if ReturnAddressLower.Program.tokensUnique? optimized &&
      Program.localReturnTokensUnique? optimized then
    let assembly ← Program.lower? optimized
    if assembly.acceptedWithDynamic then
      if Program.returnTargetsResolveNonzero? optimized assembly then
        let compact ← ReturnAddressProbe.Compact.compile? assembly
        some { cfg := optimized, assembly, compact }
      else
        none
    else
      none
  else
    none

def compileFunctions? (source : Functions.Program) : Option Artifact := do
  let stack ← Compiler.StackArtifact.compile? source
  compileCfg? stack.cfg

end LateReturnProbe
end TypedCfg
end EvmCompiler
