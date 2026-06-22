import EvmCompiler.TypedCfg.ReturnAddressRelation
import EvmCompiler.TypedCfg.Lower

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

end Program

namespace Instr

def lower? (program : TypedCfg.Program) : TypedCfg.Instr ->
    Option Assembly.Program
  | .returnToken token => do
      let site <- Program.siteForToken? program token
      some [.pushLabel site.target]
  | instr => instr.lower?

def lowerAt? (program : TypedCfg.Program) (instr : TypedCfg.Instr)
    (shape : Shape) : Option (Assembly.Program × Shape) := do
  let output <- instr.type? shape
  match instr with
  | .unwind target =>
      some
        (List.replicate (shape.length - target.length) (.prim .pop), output)
  | _ =>
      let code <- lower? program instr
      some (code, output)

end Instr

namespace Terminator

def dynamicReturnCode (depth : Nat) : Assembly.Program :=
  Assembly.StackShuffle.liftBuriedToTop depth ++ [.jumpDynamic]

def lowerAt? (shape : Shape) : TypedCfg.Terminator -> Option Assembly.Program
  | .returnDispatch returnCount sites => do
      let depth <- shape.returnTokenDepth?
      if sites.isEmpty ∨ depth ≠ returnCount then none
      else if depth < 16 then some (dynamicReturnCode depth)
      else none
  | term => term.lowerAt? shape

end Terminator

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

theorem type?_returnToken (token : Word) (shape : Shape) :
    TypedCfg.Instr.type? (.returnToken token) shape =
      some { shape with slots := .returnPC token.toNat :: shape.slots } := rfl

end ReturnAddressLower
end TypedCfg
end EvmCompiler
