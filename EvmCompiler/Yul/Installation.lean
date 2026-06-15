import EvmCompiler.Yul.Syntax
import EvmYul.SharedState

namespace EvmCompiler
namespace Yul
namespace Source
namespace Installation

def installContract (contract : AstContract)
    (shared : EvmYul.SharedState .Yul) : EvmYul.SharedState .Yul :=
  let owner := shared.executionEnv.codeOwner
  let account := (shared.accountMap.find? owner).getD default
  { shared with
    accountMap :=
      shared.accountMap.insert owner { account with code := contract }
    executionEnv := { shared.executionEnv with code := contract } }

def installContractWithCodeImage (contract : AstContract)
    (codeImage : ByteArray) (shared : EvmYul.SharedState .Yul) :
    EvmYul.SharedState .Yul :=
  let owner := shared.executionEnv.codeOwner
  let account := (shared.accountMap.find? owner).getD default
  { shared with
    accountMap :=
      shared.accountMap.insert owner
        { account with code := contract, codeBytes := codeImage }
    executionEnv :=
      { shared.executionEnv with
        code := contract
        codeBytes := codeImage } }

@[simp] theorem installContract_code
    (contract : AstContract) (shared : EvmYul.SharedState .Yul) :
    (installContract contract shared).executionEnv.code = contract := rfl

@[simp] theorem installContract_codeOwner
    (contract : AstContract) (shared : EvmYul.SharedState .Yul) :
    (installContract contract shared).executionEnv.codeOwner =
      shared.executionEnv.codeOwner := rfl

theorem installContract_find_owner
    (contract : AstContract) (shared : EvmYul.SharedState .Yul) :
    (installContract contract shared).accountMap.find?
        (installContract contract shared).executionEnv.codeOwner =
      some
        { ((shared.accountMap.find?
              shared.executionEnv.codeOwner).getD default) with
          code := contract } := by
  simp [installContract, Batteries.RBMap.find?_insert]

@[simp] theorem installContractWithCodeImage_code
    (contract : AstContract) (codeImage : ByteArray)
    (shared : EvmYul.SharedState .Yul) :
    (installContractWithCodeImage contract codeImage shared).executionEnv.code =
      contract := rfl

@[simp] theorem installContractWithCodeImage_codeBytes
    (contract : AstContract) (codeImage : ByteArray)
    (shared : EvmYul.SharedState .Yul) :
    (installContractWithCodeImage contract codeImage shared).executionEnv.codeBytes =
      codeImage := rfl

theorem installContractWithCodeImage_find_owner
    (contract : AstContract) (codeImage : ByteArray)
    (shared : EvmYul.SharedState .Yul) :
    (installContractWithCodeImage contract codeImage shared).accountMap.find?
        (installContractWithCodeImage contract codeImage shared).executionEnv.codeOwner =
      some
        { ((shared.accountMap.find?
              shared.executionEnv.codeOwner).getD default) with
          code := contract
          codeBytes := codeImage } := by
  simp [installContractWithCodeImage, Batteries.RBMap.find?_insert]

end Installation
end Source
end Yul
end EvmCompiler
