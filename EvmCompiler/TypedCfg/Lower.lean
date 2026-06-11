import EvmCompiler.TypedCfg.Semantics
import EvmCompiler.Assembly.StackShuffle

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def lower? : Instr → Option Assembly.Program
  | .push value => some [.push value]
  | .returnToken value => some [.push value]
  | .prim op => some [.prim op]
  | .pop => some [.prim .pop]
  | .dup depth =>
      match depth with
      | 0 => some [.prim .dup1]
      | 1 => some [.prim .dup2]
      | 2 => some [.prim .dup3]
      | 3 => some [.prim .dup4]
      | 4 => some [.prim .dup5]
      | 5 => some [.prim .dup6]
      | 6 => some [.prim .dup7]
      | 7 => some [.prim .dup8]
      | 8 => some [.prim .dup9]
      | 9 => some [.prim .dup10]
      | 10 => some [.prim .dup11]
      | 11 => some [.prim .dup12]
      | 12 => some [.prim .dup13]
      | 13 => some [.prim .dup14]
      | 14 => some [.prim .dup15]
      | 15 => some [.prim .dup16]
      | _ => none
  | .swap depth =>
      match depth with
      | 0 => some [.prim .swap1]
      | 1 => some [.prim .swap2]
      | 2 => some [.prim .swap3]
      | 3 => some [.prim .swap4]
      | 4 => some [.prim .swap5]
      | 5 => some [.prim .swap6]
      | 6 => some [.prim .swap7]
      | 7 => some [.prim .swap8]
      | 8 => some [.prim .swap9]
      | 9 => some [.prim .swap10]
      | 10 => some [.prim .swap11]
      | 11 => some [.prim .swap12]
      | 12 => some [.prim .swap13]
      | 13 => some [.prim .swap14]
      | 14 => some [.prim .swap15]
      | 15 => some [.prim .swap16]
      | _ => none
  | .unwind _target => none

def lowerAt? (instr : Instr) (shape : Shape) :
    Option (Assembly.Program × Shape) := do
  let output ← instr.type? shape
  match instr with
  | .unwind target =>
      some
        (List.replicate (shape.length - target.length) (.prim .pop),
          output)
  | _ =>
      let code ← instr.lower?
      some (code, output)

end Instr

namespace Terminator

def returnDispatchTest (depth : Nat) (site : ReturnSite) : Assembly.Program :=
  [ Assembly.StackShuffle.dupInstr (depth + 1)
  , .push site.token
  , .prim .eq
  , .jumpi site.caseLabel
  ]

def returnDispatchTestCases (depth : Nat) (sites : List ReturnSite) :
    Assembly.Program :=
  sites.flatMap (returnDispatchTest depth)

def returnDispatchTests (depth : Nat) (sites : List ReturnSite) :
    Assembly.Program :=
  returnDispatchTestCases depth sites ++ [.prim .invalid]

def returnDispatchCase (depth : Nat) (site : ReturnSite) : Assembly.Program :=
  .label site.caseLabel ::
    Assembly.StackShuffle.removeBuriedUnder depth ++ [.jump site.target]

def returnDispatchCases (depth : Nat) (sites : List ReturnSite) :
    Assembly.Program :=
  sites.flatMap (returnDispatchCase depth)

def returnDispatchCode (depth : Nat) (sites : List ReturnSite) :
    Assembly.Program :=
  returnDispatchTests depth sites ++ returnDispatchCases depth sites

def returnDispatchCode? (depth : Nat) (sites : List ReturnSite) :
    Option Assembly.Program :=
  if depth < 16 then some (returnDispatchCode depth sites) else none

def lowerAt? (shape : Shape) : Terminator → Option Assembly.Program
  | .fallthrough next => some [.jump next]
  | .jump target => some [.jump target]
  | .jumpi target next => some [.jumpi target, .jump next]
  | .returnDispatch returnCount sites => do
      let depth ← shape.returnTokenDepth?
      if sites.isEmpty ∨ depth ≠ returnCount then none
      else returnDispatchCode? depth sites
  | .halt kind =>
      match kind with
      | .stop => some [.prim .stop]
      | .return => some [.prim .return]
      | .revert => some [.prim .revert]
      | .selfdestruct => some [.prim .selfdestruct]
  | .invalid => some [.prim .invalid]

theorem definedLabel_instr_mem_of_lowerAt?
    {shape : Shape} {term : Terminator}
    {code : Assembly.Program} {label : Label}
    (hLower : term.lowerAt? shape = some code)
    (hLabel : label ∈ term.definedLabels) :
    Assembly.Instr.label label ∈ code := by
  cases term with
  | fallthrough next =>
      simp [definedLabels] at hLabel
  | jump target =>
      simp [definedLabels] at hLabel
  | jumpi target next =>
      simp [definedLabels] at hLabel
  | halt kind =>
      simp [definedLabels] at hLabel
  | invalid =>
      simp [definedLabels] at hLabel
  | returnDispatch returnCount sites =>
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simp [lowerAt?, hDepth] at hLower
      | some depth =>
          by_cases hSites : sites = []
          · simp [lowerAt?, hDepth, hSites] at hLower
          · by_cases hCount : depth = returnCount
            · by_cases hBound : depth < 16
              · simp [lowerAt?, hDepth, hSites, hCount,
                  returnDispatchCode?, hBound] at hLower
                rcases hLower with ⟨_, hCode⟩
                rw [← hCode]
                simp only [definedLabels, List.mem_map] at hLabel
                rcases hLabel with ⟨site, hSite, rfl⟩
                have hCase :
                    Assembly.Instr.label site.caseLabel ∈
                      returnDispatchCases depth sites :=
                  List.mem_flatMap.mpr
                    ⟨site, hSite, by simp [returnDispatchCase]⟩
                have hCase' :
                    Assembly.Instr.label site.caseLabel ∈
                      returnDispatchCases returnCount sites := by
                  simpa [hCount] using hCase
                simp only [returnDispatchCode, List.mem_append]
                exact Or.inr hCase'
              · simp [lowerAt?, hDepth, hSites, hCount,
                  returnDispatchCode?, hBound] at hLower
                exact False.elim (hBound (hCount ▸ hLower.1))
            · simp [lowerAt?, hDepth, hSites, hCount] at hLower

theorem target_instr_mem_of_lowerAt?
    {shape : Shape} {term : Terminator}
    {code : Assembly.Program} {target : Label}
    (hLower : term.lowerAt? shape = some code)
    (hTarget : target ∈ term.targets) :
    ∃ instr,
      instr ∈ code ∧ target ∈ instr.targets := by
  cases term with
  | fallthrough next =>
      simp [lowerAt?, targets] at hLower hTarget
      subst code
      subst next
      exact ⟨.jump target, by simp [Assembly.Instr.targets]⟩
  | jump jumpTarget =>
      simp [lowerAt?, targets] at hLower hTarget
      subst code
      subst jumpTarget
      exact ⟨.jump target, by simp [Assembly.Instr.targets]⟩
  | jumpi jumpTarget next =>
      simp [lowerAt?, targets] at hLower
      subst code
      simp only [targets, List.mem_cons, List.mem_singleton] at hTarget
      cases hTarget with
      | inl hEq =>
          subst jumpTarget
          exact ⟨.jumpi target, by simp [Assembly.Instr.targets]⟩
      | inr hEq =>
          simp at hEq
          subst next
          exact ⟨.jump target, by simp [Assembly.Instr.targets]⟩
  | halt kind =>
      simp [targets] at hTarget
  | invalid =>
      simp [targets] at hTarget
  | returnDispatch returnCount sites =>
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simp [lowerAt?, hDepth] at hLower
      | some depth =>
          by_cases hSites : sites = []
          · simp [lowerAt?, hDepth, hSites] at hLower
          · by_cases hCount : depth = returnCount
            · by_cases hBound : depth < 16
              · simp [lowerAt?, hDepth, hSites, hCount,
                  returnDispatchCode?, hBound] at hLower
                rcases hLower with ⟨_, hCode⟩
                rw [← hCode]
                simp only [targets, List.mem_map] at hTarget
                rcases hTarget with ⟨site, hSite, rfl⟩
                have hJump :
                    Assembly.Instr.jump site.target ∈
                      returnDispatchCases depth sites :=
                  List.mem_flatMap.mpr
                    ⟨site, hSite, by
                      simp [returnDispatchCase]⟩
                have hJump' :
                    Assembly.Instr.jump site.target ∈
                      returnDispatchCases returnCount sites := by
                  simpa [hCount] using hJump
                exact
                  ⟨.jump site.target,
                    by
                      simp only [returnDispatchCode, List.mem_append]
                      exact Or.inr hJump',
                    by simp [Assembly.Instr.targets]⟩
              · simp [lowerAt?, hDepth, hSites, hCount,
                  returnDispatchCode?, hBound] at hLower
                exact False.elim (hBound (hCount ▸ hLower.1))
            · simp [lowerAt?, hDepth, hSites, hCount] at hLower

end Terminator

namespace Block

def lowerBodyFrom? : List Instr → Shape →
    Option (Assembly.Program × Shape)
  | [], shape => some ([], shape)
  | instr :: rest, shape => do
      let (head, shape') ← instr.lowerAt? shape
      let (tail, output) ← lowerBodyFrom? rest shape'
      some (head ++ tail, output)

def lower? (block : Block) : Option Assembly.Program := do
  let (body, output) ← lowerBodyFrom? block.body block.input
  if output = block.output then
    let term ← block.term.lowerAt? output
    some (.label block.label :: body ++ term)
  else
    none

theorem lower?_starts_with_label
    {block : Block} {code : Assembly.Program}
    (hLower : block.lower? = some code) :
    ∃ tail, code = Assembly.Instr.label block.label :: tail := by
  unfold lower? at hLower
  cases hBody : lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            exact ⟨body ++ term, rfl⟩
      · simp [hBody, hOutput] at hLower

theorem definedLabel_instr_mem_of_lower?
    {block : Block} {code : Assembly.Program} {label : Label}
    (hLower : block.lower? = some code)
    (hLabel : label ∈ block.term.definedLabels) :
    Assembly.Instr.label label ∈ code := by
  unfold lower? at hLower
  cases hBody : lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            exact
              (by
                simp only [List.mem_cons]
                exact Or.inr
                  (List.mem_append_right body
                    (Terminator.definedLabel_instr_mem_of_lowerAt?
                      hTerm hLabel)))
      · simp [hBody, hOutput] at hLower

theorem target_instr_mem_of_lower?
    {block : Block} {code : Assembly.Program} {target : Label}
    (hLower : block.lower? = some code)
    (hTarget : target ∈ block.term.targets) :
    ∃ instr,
      instr ∈ code ∧ target ∈ instr.targets := by
  unfold lower? at hLower
  cases hBody : lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            rcases
                Terminator.target_instr_mem_of_lowerAt?
                  hTerm hTarget with
              ⟨instr, hInstr, hInstrTarget⟩
            exact
              ⟨instr,
                by
                  simp only [List.mem_cons]
                  exact Or.inr (List.mem_append_right body hInstr),
                hInstrTarget⟩
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

def lowerBlocks? : List Block → Option Assembly.Program
  | [] => some []
  | block :: rest => do
      let head ← block.lower?
      let tail ← lowerBlocks? rest
      some (head ++ tail)

def lower? (program : Program) : Option Assembly.Program :=
  program.blocksInLoweringOrder? >>= lowerBlocks?

def Lowerable (program : Program) : Prop :=
  ∃ asm, program.lower? = some asm

structure BlockFragment
    (target : Assembly.Program) (block : Block) where
  pre : Assembly.Program
  code : Assembly.Program
  post : Assembly.Program
  lower : block.lower? = some code
  target_eq : target = pre ++ code ++ post

theorem extractBlock?_perm
    {blocks : List Block} {label : Label}
    {block : Block} {remaining : List Block}
    (hExtract :
      extractBlock? blocks label = some (block, remaining)) :
    blocks.Perm (block :: remaining) := by
  induction blocks generalizing block remaining with
  | nil =>
      simp [extractBlock?] at hExtract
  | cons head rest ih =>
      by_cases hHead : head.label = label
      · simp [extractBlock?, hHead] at hExtract
        rcases hExtract with ⟨rfl, rfl⟩
        exact List.Perm.refl _
      · simp [extractBlock?, hHead] at hExtract
        cases hTail : extractBlock? rest label with
        | none =>
            simp [hTail] at hExtract
        | some result =>
            rcases result with ⟨entry, tail⟩
            simp [hTail] at hExtract
            rcases hExtract with ⟨rfl, rfl⟩
            exact
              (List.Perm.cons head (ih hTail)).trans
                (List.Perm.swap head entry tail).symm

theorem blocksInLoweringOrder?_perm
    {program : Program} {blocks : List Block}
    (hOrder : program.blocksInLoweringOrder? = some blocks) :
    program.blocks.Perm blocks := by
  unfold blocksInLoweringOrder? at hOrder
  cases hExtract :
      extractBlock? program.blocks program.entry with
  | none =>
      simp [hExtract] at hOrder
  | some result =>
      rcases result with ⟨entry, remaining⟩
      simp [hExtract] at hOrder
      subst blocks
      exact extractBlock?_perm hExtract

theorem lowerBlocks?_fragment_of_mem
    {blocks : List Block} {target : Assembly.Program}
    {block : Block}
    (hLower : lowerBlocks? blocks = some target)
    (hMem : block ∈ blocks) :
    Nonempty (BlockFragment target block) := by
  induction blocks generalizing target with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold lowerBlocks? at hLower
      cases hHead : head.lower? with
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
    {program : Program} {target : Assembly.Program}
    {label : Label} {block : Block}
    (hLower : program.lower? = some target)
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
      have hPerm := blocksInLoweringOrder?_perm hOrder
      have hMemOrdered : block ∈ blocks :=
        hPerm.mem_iff.mp hMemSource
      exact lowerBlocks?_fragment_of_mem hLower hMemOrdered

end Program

end TypedCfg
end EvmCompiler
