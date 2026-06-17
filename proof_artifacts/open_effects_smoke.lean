import EvmCompiler.Assembly.InteractionBytecode

#check EvmCompiler.Simulation.OpenWorld
#check EvmCompiler.Simulation.OpenWorld.installYulShared
#check EvmCompiler.Simulation.OpenWorld.installEVMShared
#check EvmCompiler.Simulation.Interaction.bind
#check EvmCompiler.Simulation.Interaction.Rel.refl
#check EvmCompiler.Simulation.Interaction.Rel.symm
#check EvmCompiler.Simulation.Interaction.Rel.trans
#check EvmCompiler.Simulation.Interaction.Rel.bind
#check EvmCompiler.Simulation.Interaction.Rel.request_left
#check EvmCompiler.Simulation.Interaction.Rel.interpret
#check EvmCompiler.Simulation.Interaction.Rel.executes
#check EvmCompiler.Assembly.InteractionSemantics.PrimOp.openStep
#check EvmCompiler.Assembly.InteractionSemantics.Source.prim_openStep_rel
#check EvmCompiler.Assembly.InteractionSemantics.Target.openRunNResult
#check EvmCompiler.Assembly.InteractionPreservation.stepAt_emit_open_rel
#check EvmCompiler.Assembly.InteractionPreservation.stepAt_emit_open_result_rel
#check EvmCompiler.Assembly.InteractionPreservation.source_openRunNResult_rel_compiled
#check EvmCompiler.Assembly.InteractionPreservation.compile_openRunNResult_block_rel
#check EvmCompiler.Assembly.InteractionPreservation.compile_openRunNResult_target_executes
#check EvmCompiler.Assembly.TargetInstr.ofDecoded?_op_arg
#check EvmCompiler.Assembly.Bytecode.InteractionSemantics.openRunNResult
#check EvmCompiler.Assembly.Bytecode.target_openRunNResult_executes
#check EvmCompiler.Assembly.Bytecode.compile_openRunNResult_executes

#print axioms EvmCompiler.Simulation.OpenAccount.ofYul_toYul
#print axioms EvmCompiler.Simulation.OpenAccount.ofEVM_toEVM
#print axioms EvmCompiler.Simulation.ExternalKind.classifies_call
#print axioms EvmCompiler.Simulation.ExternalKind.classifies_callcode
#print axioms EvmCompiler.Simulation.ExternalKind.classifies_delegatecall
#print axioms EvmCompiler.Simulation.ExternalKind.classifies_staticcall
#print axioms EvmCompiler.Simulation.ExternalKind.classifies_create
#print axioms EvmCompiler.Simulation.ExternalKind.classifies_create2
#print axioms EvmCompiler.Simulation.Interaction.Rel.bind
#print axioms EvmCompiler.Simulation.Interaction.Rel.trans
#print axioms EvmCompiler.Simulation.Interaction.Rel.interpret
#print axioms EvmCompiler.Simulation.Interaction.Rel.executes
#print axioms EvmCompiler.Assembly.InteractionSemantics.Source.prim_openStep_rel
#print axioms EvmCompiler.Assembly.InteractionPreservation.stepAt_emit_open_result_rel
#print axioms EvmCompiler.Assembly.InteractionPreservation.compile_openRunNResult_block_rel
#print axioms EvmCompiler.Assembly.InteractionPreservation.compile_openRunNResult_target_executes
#print axioms EvmCompiler.Assembly.Bytecode.target_openRunNResult_executes
#print axioms EvmCompiler.Assembly.Bytecode.compile_openRunNResult_executes
