import Lake
open Lake DSL

require «evm-interaction» from git
  "https://github.com/danrobinson/evm-interaction.git" @ "c939817c55f966dab97e1ba8df05ceca1fdfbdb2"

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "b08573c65e33feb5331abe2b7c1d76be89bb8eff"

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

lean_exe «evm-compiler-backend» where
  root := `EvmCompiler.BackendCli
