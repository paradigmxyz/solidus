import EvmCompiler.TypedCfg.ReturnAddressRelation
import EvmCompiler.TypedCfg.Lower
import EvmCompiler.Assembly.Accepted

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressLower

namespace Terminator

def sites : TypedCfg.Terminator -> List ReturnSite
  | .returnDispatch _ sites => sites
  | _ => []

end Terminator

namespace Program

def returnSites (program : TypedCfg.Program) : List ReturnSite :=
  program.blocks.flatMap fun block => Terminator.sites block.term

def siteForToken? (program : TypedCfg.Program) (token : Word) :
    Option ReturnSite :=
  (returnSites program).find? fun site => decide (site.token = token)

def tokensUnique? (program : TypedCfg.Program) : Bool :=
  ReturnAddressRelation.tokensUnique? (returnSites program)

def targetsUnique? (program : TypedCfg.Program) : Bool :=
  ReturnAddressRelation.targetsUnique? (returnSites program)

end Program

namespace Instr

def Safe (instr : TypedCfg.Instr) (input output : Shape) : Prop :=
  match instr with
  | .prim op =>
      match op.stackArity? with
      | none => False
      | some (inputArity, _) =>
          op ≠ .pc ∧
            ReturnAddressRelation.PlainSlots
              (input.slots.take inputArity)
  | .bindLocals _ _
  | .bindScratch _ _ _
  | .relabel _ =>
      ReturnAddressRelation.SlotsClassRel input.slots output.slots
  | _ => True

def safe? (instr : TypedCfg.Instr) (input output : Shape) : Bool :=
  match instr with
  | .prim op =>
      match op.stackArity? with
      | none => false
      | some (inputArity, _) =>
          decide (op ≠ .pc) &&
            ReturnAddressRelation.plainSlots?
              (input.slots.take inputArity)
  | .bindLocals _ _
  | .bindScratch _ _ _
  | .relabel _ =>
      ReturnAddressRelation.slotsClassRel?
        input.slots output.slots
  | _ => true

theorem safe_of_check
    {instr : TypedCfg.Instr} {input output : Shape}
    (hSafe : safe? instr input output = true) :
    Safe instr input output := by
  cases instr with
  | prim op =>
      cases hArity : op.stackArity? with
      | none => simp [safe?, Safe, hArity] at hSafe
      | some arity =>
          rcases arity with ⟨inputArity, outputArity⟩
          simp only [safe?, Safe, hArity, Bool.and_eq_true,
            decide_eq_true_eq] at hSafe ⊢
          exact
            ⟨hSafe.1,
              ReturnAddressRelation.plainSlots_of_check hSafe.2⟩
  | bindLocals offset names
  | bindScratch offset names slot
  | relabel names =>
      exact
        ReturnAddressRelation.slotsClassRel_of_check
          (by simpa [safe?] using hSafe)
  | push value
  | returnToken value
  | pop
  | dup value
  | swap value
  | unwind value =>
      trivial

def lower? (program : TypedCfg.Program) : TypedCfg.Instr ->
    Option Assembly.Program
  | .returnToken token => do
      let site <- Program.siteForToken? program token
      some [.pushLabel site.target]
  | instr => instr.lower?

def lowerAt? (program : TypedCfg.Program) (instr : TypedCfg.Instr)
    (shape : Shape) : Option (Assembly.Program × Shape) := do
  let output <- instr.type? shape
  if safe? instr shape output then
    match instr with
    | .unwind target =>
        some
          (List.replicate (shape.length - target.length) (.prim .pop), output)
    | _ =>
        let code <- lower? program instr
        some (code, output)
  else
    none

end Instr

namespace Terminator

def dynamicReturnFirstTest (site : ReturnSite) : Assembly.Program :=
  [ Assembly.StackShuffle.dupInstr 1
  , .pushLabel site.target
  , .prim .eq
  ]

def dynamicReturnNextTest (site : ReturnSite) : Assembly.Program :=
  [ Assembly.StackShuffle.dupInstr 2
  , .pushLabel site.target
  , .prim .eq
  , .prim .or
  ]

def dynamicReturnMatch
    (resolve : ReturnAddressRelation.Resolver) (token : Word)
    (site : ReturnSite) : Word :=
  match resolve site.target with
  | some dest =>
      EvmYul.UInt256.eq (EvmYul.UInt256.ofNat dest) token
  | none => EvmYul.UInt256.ofNat 0

def dynamicReturnAccumulator
    (resolve : ReturnAddressRelation.Resolver) (token : Word) :
    List ReturnSite → Word
  | [] => EvmYul.UInt256.ofNat 0
  | first :: rest =>
      rest.foldl
        (fun accumulator site =>
          EvmYul.UInt256.lor
            (dynamicReturnMatch resolve token site)
            accumulator)
        (dynamicReturnMatch resolve token first)

def dynamicReturnTests : List ReturnSite -> Assembly.Program
  | [] => []
  | first :: rest =>
      dynamicReturnFirstTest first ++
        rest.flatMap dynamicReturnNextTest

def dynamicReturnTransferCode (depth : Nat) : Assembly.Program :=
  Assembly.StackShuffle.liftBuriedToTop depth ++ [.jumpDynamic]

def dynamicReturnCode (depth : Nat) (sites : List ReturnSite) :
    Assembly.Program :=
  match sites with
  | [] => []
  | first :: _ =>
      Assembly.StackShuffle.liftBuriedToTop depth ++
        dynamicReturnTests sites ++
          [ .jumpi first.caseLabel
          , .prim .invalid
          , .label first.caseLabel
          , .jumpDynamic
          ]

def Safe (shape : Shape) : TypedCfg.Terminator → Prop
  | .jumpi _ _ =>
      ReturnAddressRelation.PlainSlots (shape.slots.take 1)
  | .halt kind =>
      ReturnAddressRelation.PlainSlots
        (shape.slots.take kind.argCount)
  | _ => True

def safe? (shape : Shape) : TypedCfg.Terminator → Bool
  | .jumpi _ _ =>
      ReturnAddressRelation.plainSlots? (shape.slots.take 1)
  | .halt kind =>
      ReturnAddressRelation.plainSlots?
        (shape.slots.take kind.argCount)
  | _ => true

/-- Stack shape after the control operand, if any, has been consumed. -/
def outputShape (shape : Shape) : TypedCfg.Terminator → Shape
  | .jumpi _ _ => Shape.pop 1 shape
  | .returnDispatch _ _ =>
      match shape.returnTokenDepth? with
      | some depth => shape.erase depth
      | none => shape
  | _ => shape

theorem safe_of_check
    {shape : Shape} {term : TypedCfg.Terminator}
    (hSafe : safe? shape term = true) :
    Safe shape term := by
  cases term with
  | jumpi target next =>
      exact ReturnAddressRelation.plainSlots_of_check hSafe
  | halt kind =>
      exact ReturnAddressRelation.plainSlots_of_check hSafe
  | fallthrough next
  | jump target
  | returnDispatch returnCount sites
  | invalid =>
      trivial

def lowerUncheckedAt? (shape : Shape) :
    TypedCfg.Terminator → Option Assembly.Program
  | .returnDispatch returnCount sites => do
      let depth <- shape.returnTokenDepth?
      if sites.isEmpty ∨ depth ≠ returnCount then none
      else if depth < 16 then some (dynamicReturnCode depth sites)
      else none
  | term => term.lowerAt? shape

def lowerAt? (shape : Shape) (term : TypedCfg.Terminator) :
    Option Assembly.Program :=
  if safe? shape term then lowerUncheckedAt? shape term else none

end Terminator

theorem Terminator.safe_of_lowerAt?
    {shape : Shape} {term : TypedCfg.Terminator}
    {code : Assembly.Program}
    (hLower : Terminator.lowerAt? shape term = some code) :
    Terminator.Safe shape term := by
  unfold Terminator.lowerAt? at hLower
  by_cases hSafe : Terminator.safe? shape term = true
  · exact Terminator.safe_of_check hSafe
  · have hFalse : Terminator.safe? shape term = false :=
      Bool.eq_false_of_not_eq_true hSafe
    simp [hFalse] at hLower

theorem Terminator.standard_lowerAt?_of_lowerAt?_not_returnDispatch
    {shape : Shape} {term : TypedCfg.Terminator}
    {code : Assembly.Program}
    (hNotReturnDispatch :
      ∀ returnCount sites,
        term ≠ .returnDispatch returnCount sites)
    (hLower : Terminator.lowerAt? shape term = some code) :
    TypedCfg.Terminator.lowerAt? shape term = some code := by
  unfold Terminator.lowerAt? at hLower
  by_cases hSafe : Terminator.safe? shape term = true
  · simp only [hSafe, if_true] at hLower
    cases term <;>
      simp [Terminator.lowerUncheckedAt?] at hLower ⊢
    case pos.returnDispatch returnCount sites =>
      exact False.elim
        (hNotReturnDispatch returnCount sites rfl)
    all_goals exact hLower
  · have hFalse : Terminator.safe? shape term = false :=
      Bool.eq_false_of_not_eq_true hSafe
    simp [hFalse] at hLower

theorem Terminator.lowerAt?_returnDispatch_parts
    {shape : Shape} {returnCount : Nat} {sites : List ReturnSite}
    {code : Assembly.Program}
    (hLower :
      Terminator.lowerAt? shape (.returnDispatch returnCount sites) =
        some code) :
    ∃ depth,
      shape.returnTokenDepth? = some depth ∧
        sites ≠ [] ∧ depth = returnCount ∧ depth < 16 ∧
          code = Terminator.dynamicReturnCode depth sites := by
  cases hDepth : shape.returnTokenDepth? with
  | none =>
      simp [Terminator.lowerAt?, Terminator.safe?,
        Terminator.lowerUncheckedAt?, hDepth] at hLower
  | some depth =>
      by_cases hSites : sites = []
      · simp [Terminator.lowerAt?, Terminator.safe?,
          Terminator.lowerUncheckedAt?, hDepth, hSites] at hLower
      · by_cases hCount : depth = returnCount
        · have hFacts :
              depth < 16 ∧
                Terminator.dynamicReturnCode depth sites = code := by
            simpa [Terminator.lowerAt?, Terminator.safe?,
              Terminator.lowerUncheckedAt?, hDepth, hSites,
              hCount] using hLower
          exact
            ⟨depth, rfl, hSites, hCount, hFacts.1,
              hFacts.2.symm⟩
        · simp [Terminator.lowerAt?, Terminator.safe?,
            Terminator.lowerUncheckedAt?, hDepth, hSites,
            hCount] at hLower

namespace Block

def lowerBodyFrom? (program : TypedCfg.Program) :
    List TypedCfg.Instr → Shape →
      Option (Assembly.Program × Shape)
  | [], shape => some ([], shape)
  | instr :: rest, shape => do
      let (head, shape') ← Instr.lowerAt? program instr shape
      let (tail, output) ← lowerBodyFrom? program rest shape'
      some (head ++ tail, output)

def lower? (program : TypedCfg.Program) (block : TypedCfg.Block) :
    Option Assembly.Program := do
  let (body, output) ← lowerBodyFrom? program block.body block.input
  if output = block.output then
    let term ← Terminator.lowerAt? output block.term
    some (.label block.label :: body ++ term)
  else
    none

theorem lower?_starts_with_label
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {target : Assembly.Program}
    (hLower : lower? program block = some target) :
    ∃ tail, target = .label block.label :: tail := by
  unfold lower? at hLower
  cases hBody : lowerBodyFrom? program block.body block.input with
  | none => simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm :
            Terminator.lowerAt? block.output block.term with
        | none => simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst target
            exact ⟨body ++ term, rfl⟩
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

def lowerBlocks? (program : TypedCfg.Program) :
    List TypedCfg.Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← Block.lower? program block
      let tail ← lowerBlocks? program rest
      some (head ++ tail)

def lower? (program : TypedCfg.Program) : Option Assembly.Program := do
  let blocks ← program.blocksInLoweringOrder?
  lowerBlocks? program blocks

/--
Every control edge preserves the physical-return/ordinary-word partition of
the visible stack.  The ordinary row-compatibility checker is intentionally
more permissive than this; the physical-return path therefore carries this
additional fail-open gate.
-/
def EdgeClassSafe (program : TypedCfg.Program) : Prop :=
  ∀ block ∈ program.blocks,
    ∀ target ∈ block.term.targets,
      ∃ targetBlock,
        program.findBlock? target = some targetBlock ∧
          ReturnAddressRelation.SlotsClassRel
            (Terminator.outputShape block.output block.term).slots
            targetBlock.input.slots ∧
          targetBlock.input.tail =
            (Terminator.outputShape block.output block.term).tail

def edgeClassSafe? (program : TypedCfg.Program) : Bool :=
  program.blocks.all fun block =>
    block.term.targets.all fun target =>
      match program.findBlock? target with
      | none => false
      | some targetBlock =>
          ReturnAddressRelation.slotsClassRel?
              (Terminator.outputShape block.output block.term).slots
              targetBlock.input.slots &&
            decide
              (targetBlock.input.tail =
                (Terminator.outputShape block.output block.term).tail)

theorem edgeClassSafe_of_check
    {program : TypedCfg.Program}
    (hCheck : edgeClassSafe? program = true) :
    EdgeClassSafe program := by
  intro block hBlock target hTarget
  have hBlockCheck :=
    (List.all_eq_true.mp hCheck) block hBlock
  have hTargetCheck :=
    (List.all_eq_true.mp hBlockCheck) target hTarget
  cases hFind : program.findBlock? target with
  | none =>
      simp [edgeClassSafe?, hFind] at hTargetCheck
  | some targetBlock =>
      simp only [hFind, Bool.and_eq_true, decide_eq_true_eq]
        at hTargetCheck
      exact
        ⟨targetBlock, rfl,
          ReturnAddressRelation.slotsClassRel_of_check
            hTargetCheck.1,
          hTargetCheck.2⟩

/-- Every operand consumed by a terminal instruction is an ordinary word,
never a compiler-owned logical/physical return address. This narrow fail-open
gate transfers terminal safety across the representation relation. -/
def TerminalArgsPlain (program : TypedCfg.Program) : Prop :=
  ∀ block ∈ program.blocks, ∀ kind,
    block.term = .halt kind →
      kind.argCount ≤ block.output.length ∧
        ReturnAddressRelation.PlainSlots
          (block.output.slots.take kind.argCount)

def terminalArgsPlain? (program : TypedCfg.Program) : Bool :=
  program.blocks.all fun block =>
    match block.term with
    | .halt kind =>
        decide (kind.argCount ≤ block.output.length) &&
          ReturnAddressRelation.plainSlots?
            (block.output.slots.take kind.argCount)
    | _ => true

theorem terminalArgsPlain_of_check
    {program : TypedCfg.Program}
    (hCheck : terminalArgsPlain? program = true) :
    TerminalArgsPlain program := by
  intro block hBlock kind hTerm
  have hBlockCheck :=
    (List.all_eq_true.mp hCheck) block hBlock
  rw [hTerm] at hBlockCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hBlockCheck
  exact
    ⟨hBlockCheck.1,
      ReturnAddressRelation.plainSlots_of_check hBlockCheck.2⟩

theorem lowerBlocks?_starts_with_label
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {rest : List TypedCfg.Block} {target : Assembly.Program}
    (hLower : lowerBlocks? program (block :: rest) = some target) :
    ∃ tail, target = .label block.label :: tail := by
  unfold lowerBlocks? at hLower
  cases hHead : Block.lower? program block with
  | none => simp [hHead] at hLower
  | some head =>
      cases hTail : lowerBlocks? program rest with
      | none => simp [hHead, hTail] at hLower
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
  | none => simp [hOrder] at hLower
  | some blocks =>
      simp [hOrder] at hLower
      unfold TypedCfg.Program.blocksInLoweringOrder? at hOrder
      cases hExtract :
          TypedCfg.Program.extractBlock? program.blocks program.entry with
      | none => simp [hExtract] at hOrder
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

structure BlockFragment (program : TypedCfg.Program)
    (target : Assembly.Program) (block : TypedCfg.Block) where
  pre : Assembly.Program
  code : Assembly.Program
  post : Assembly.Program
  lower : Block.lower? program block = some code
  target_eq : target = pre ++ code ++ post

theorem lowerBlocks?_fragment_of_mem
    {program : TypedCfg.Program} {blocks : List TypedCfg.Block}
    {target : Assembly.Program} {block : TypedCfg.Block}
    (hLower : lowerBlocks? program blocks = some target)
    (hMem : block ∈ blocks) :
    Nonempty (BlockFragment program target block) := by
  induction blocks generalizing target with
  | nil => simp at hMem
  | cons head rest ih =>
      unfold lowerBlocks? at hLower
      cases hHead : Block.lower? program head with
      | none => simp [hHead] at hLower
      | some headCode =>
          cases hTail : lowerBlocks? program rest with
          | none => simp [hHead, hTail] at hLower
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
    {label : Assembly.Label} {block : TypedCfg.Block}
    (hLower : lower? program = some target)
    (hFind : program.findBlock? label = some block) :
    Nonempty (BlockFragment program target block) := by
  unfold lower? at hLower
  cases hOrder : program.blocksInLoweringOrder? with
  | none => simp [hOrder] at hLower
  | some blocks =>
      simp [hOrder] at hLower
      have hMemSource : block ∈ program.blocks :=
        List.mem_of_find?_eq_some hFind
      have hPerm := TypedCfg.Program.blocksInLoweringOrder?_perm hOrder
      have hMemOrdered : block ∈ blocks :=
        hPerm.mem_iff.mp hMemSource
      exact lowerBlocks?_fragment_of_mem hLower hMemOrdered

theorem blockLabel_instr_mem_of_lower?
    {program : TypedCfg.Program} {target : Assembly.Program}
    {block : TypedCfg.Block}
    (hLower : lower? program = some target)
    (hUnique : program.LabelsUnique)
    (hBlock : block ∈ program.blocks) :
    Assembly.Instr.label block.label ∈ target := by
  have hFind :
      program.findBlock? block.label = some block :=
    TypedCfg.Program.findBlock?_eq_some_of_mem hUnique hBlock
  rcases lower?_fragment_of_findBlock? hLower hFind with
    ⟨fragment⟩
  rcases Block.lower?_starts_with_label fragment.lower with
    ⟨tail, hCode⟩
  rw [fragment.target_eq, hCode]
  simp

theorem blockLabel_labelPc_exists_of_lower?
    {program : TypedCfg.Program} {target : Assembly.Program}
    {block : TypedCfg.Block}
    (hLower : lower? program = some target)
    (hUnique : program.LabelsUnique)
    (hBlock : block ∈ program.blocks) :
    ∃ pc, target.labelPc block.label = some pc := by
  have hInstr :=
    blockLabel_instr_mem_of_lower? hLower hUnique hBlock
  exact
    Assembly.Program.labelPc_exists_of_mem_labels target
      (Assembly.Program.mem_labels_of_label_mem hInstr)

end Program

theorem siteForToken?_mem
    {program : TypedCfg.Program} {token : Word} {site : ReturnSite}
    (hFind : Program.siteForToken? program token = some site) :
    site ∈ Program.returnSites program ∧ site.token = token := by
  unfold Program.siteForToken? at hFind
  exact
    ⟨List.mem_of_find?_eq_some hFind,
      by simpa only [decide_eq_true_eq] using List.find?_some hFind⟩

theorem tokensUnique_of_check
    {program : TypedCfg.Program} (hCheck : Program.tokensUnique? program = true) :
    ReturnAddressRelation.TokensUnique (Program.returnSites program) := by
  exact
    (ReturnAddressRelation.tokensUnique?_eq_true_iff
      (Program.returnSites program)).mp hCheck

theorem targetsUnique_of_check
    {program : TypedCfg.Program} (hCheck : Program.targetsUnique? program = true) :
    ReturnAddressRelation.TargetsUnique (Program.returnSites program) := by
  exact
    (ReturnAddressRelation.targetsUnique?_eq_true_iff
      (Program.returnSites program)).mp hCheck

theorem term_site_mem_returnSites
    {program : TypedCfg.Program} {block : Block} {site : ReturnSite}
    (hBlock : block ∈ program.blocks)
    (hSite : site ∈ Terminator.sites block.term) :
    site ∈ Program.returnSites program := by
  exact List.mem_flatMap.mpr ⟨block, hBlock, hSite⟩

theorem lower?_returnToken
    {program : TypedCfg.Program} {token : Word} {site : ReturnSite}
    (hFind : Program.siteForToken? program token = some site) :
    Instr.lower? program (.returnToken token) =
      some [.pushLabel site.target] := by
  simp [Instr.lower?, hFind]

theorem Instr.type?_eq_some_of_lowerAt?
    {program : TypedCfg.Program} {instr : TypedCfg.Instr}
    {input output : Shape} {code : Assembly.Program}
    (hLower : Instr.lowerAt? program instr input = some (code, output)) :
    instr.type? input = some output := by
  unfold Instr.lowerAt? at hLower
  cases hType : instr.type? input with
  | none => simp [hType] at hLower
  | some typedOutput =>
      simp only [hType, Option.bind_eq_bind, Option.bind_some] at hLower
      by_cases hSafe : Instr.safe? instr input typedOutput = true
      · simp [hSafe] at hLower
        cases instr <;>
          simp [Instr.lower?] at hLower
        case pos.returnToken value =>
          cases hFind : Program.siteForToken? program value with
          | none => simp [Instr.lower?, hFind] at hLower
          | some site =>
              have hPair :
                  [Assembly.Instr.pushLabel site.target] = code ∧
                    typedOutput = output := by
                simpa [Instr.lower?, hFind] using hLower
              exact congrArg some hPair.2
        all_goals
          repeat' split at hLower
          all_goals try simp_all [Option.bind_eq_some_iff]
      · have hFalse : Instr.safe? instr input typedOutput = false :=
          Bool.eq_false_of_not_eq_true hSafe
        simp [hFalse] at hLower

theorem Instr.safe_of_lowerAt?
    {program : TypedCfg.Program} {instr : TypedCfg.Instr}
    {input output : Shape} {code : Assembly.Program}
    (hLower : Instr.lowerAt? program instr input = some (code, output)) :
    Instr.Safe instr input output := by
  unfold Instr.lowerAt? at hLower
  cases hType : instr.type? input with
  | none => simp [hType] at hLower
  | some typedOutput =>
      simp only [hType, Option.bind_eq_bind, Option.bind_some] at hLower
      by_cases hSafe : Instr.safe? instr input typedOutput = true
      · have hSafeProp := Instr.safe_of_check hSafe
        simp [hSafe] at hLower
        cases instr <;>
          simp [Instr.lower?] at hLower
        case pos.returnToken value =>
          cases hFind : Program.siteForToken? program value with
          | none => simp [Instr.lower?, hFind] at hLower
          | some site =>
              have hPair :
                  [Assembly.Instr.pushLabel site.target] = code ∧
                    typedOutput = output := by
                simpa [Instr.lower?, hFind] using hLower
              have hOutput := hPair.2
              subst output
              exact hSafeProp
        all_goals
          repeat' split at hLower
          all_goals try simp_all [Option.bind_eq_some_iff]
      · have hFalse : Instr.safe? instr input typedOutput = false :=
          Bool.eq_false_of_not_eq_true hSafe
        simp [hFalse] at hLower

theorem Instr.standard_lowerAt?_of_lowerAt?_not_returnToken
    {program : TypedCfg.Program} {instr : TypedCfg.Instr}
    {input output : Shape} {code : Assembly.Program}
    (hNotReturnToken : ∀ token, instr ≠ .returnToken token)
    (hLower : Instr.lowerAt? program instr input = some (code, output)) :
    TypedCfg.Instr.lowerAt? instr input = some (code, output) := by
  cases hType : instr.type? input with
  | none =>
      simp [Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      cases instr <;>
        simp [Instr.lowerAt?, Instr.lower?, TypedCfg.Instr.lowerAt?,
          TypedCfg.Instr.lower?, hType] at hLower ⊢
      case returnToken token =>
        exact False.elim (hNotReturnToken token rfl)
      all_goals simp_all

theorem Instr.lowerAt?_returnToken_parts
    {program : TypedCfg.Program} {token : Word}
    {input output : Shape} {code : Assembly.Program}
    (hLower :
      Instr.lowerAt? program (.returnToken token) input =
        some (code, output)) :
    ∃ site,
      Program.siteForToken? program token = some site ∧
        code = [.pushLabel site.target] ∧
          output =
            { input with
              slots := .returnPC token.toNat :: input.slots } := by
  cases hFind : Program.siteForToken? program token with
  | none =>
      simp [Instr.lowerAt?, Instr.lower?, hFind] at hLower
  | some site =>
      refine ⟨site, rfl, ?_⟩
      have hPair :
          [Assembly.Instr.pushLabel site.target] = code ∧
            { input with
                slots := .returnPC token.toNat :: input.slots } =
              output := by
        simpa [Instr.lowerAt?, Instr.lower?, Instr.safe?,
          TypedCfg.Instr.type?, hFind] using hLower
      exact ⟨hPair.1.symm, hPair.2.symm⟩

theorem type?_returnToken (token : Word) (shape : Shape) :
    TypedCfg.Instr.type? (.returnToken token) shape =
      some { shape with slots := .returnPC token.toNat :: shape.slots } := rfl

end ReturnAddressLower
end TypedCfg
end EvmCompiler
