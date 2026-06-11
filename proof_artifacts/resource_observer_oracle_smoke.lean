import EvmCompiler.Yul.ObserverOracle

#check EvmCompiler.Yul.Source.Effectful.StateModel
#check EvmCompiler.Yul.Source.Effectful.PrimitiveSemantics
#check EvmCompiler.Yul.ObserverOracle.SourceReplay.Program.run
#check EvmCompiler.Yul.ObserverOracle.SourceReplay.evalValues_gas_cons
#check EvmCompiler.Yul.ObserverOracle.SourceReplay.evalValues_msize_cons
#check EvmCompiler.Yul.ObserverOracle.typedCfgEffects_gas
#check EvmCompiler.Yul.ObserverOracle.typedCfgEffects_msize
#check EvmCompiler.Yul.ObserverOracle.PublicArtifact.ObserverReplay
#check EvmCompiler.Yul.ObserverOracle.compileResourceArtifactWithPolicy?_verifiedObserverRun

#print axioms EvmCompiler.Yul.ObserverOracle.SourceReplay.evalValues_gas_cons
#print axioms EvmCompiler.Yul.ObserverOracle.SourceReplay.evalValues_msize_cons
#print axioms EvmCompiler.Yul.ObserverOracle.compileResourceArtifactWithPolicy?_verifiedObserverRun
