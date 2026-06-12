import Lake
open Lake DSL

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "3918e920f79f912b90ffd776838fa2397ece877f"

package «evm-compiler» {
  moreLeanArgs := #[
    "-DautoImplicit=false",
    "-Dlinter.all=false",
    "-Dlinter.constructorNameAsVariable=false",
    "-Dlinter.deprecated=false",
    "-Dlinter.unnecessarySeqFocus=false",
    "-Dlinter.unnecessarySimpa=false",
    "-Dlinter.unreachableTactic=false",
    "-Dlinter.unusedSimpArgs=false",
    "-Dlinter.unusedTactic=false",
    "-Dlinter.unusedVariables=false"
  ]
  moreServerOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, false⟩,
    ⟨`linter.constructorNameAsVariable, false⟩,
    ⟨`linter.deprecated, false⟩,
    ⟨`linter.unnecessarySeqFocus, false⟩,
    ⟨`linter.unnecessarySimpa, false⟩,
    ⟨`linter.unreachableTactic, false⟩,
    ⟨`linter.unusedSimpArgs, false⟩,
    ⟨`linter.unusedTactic, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]
}

@[default_target]
lean_lib «EvmCompiler»
