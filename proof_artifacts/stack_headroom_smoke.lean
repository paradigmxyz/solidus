import EvmCompiler.Solidity.StackHeadroomEndToEnd

/-!
Stack-headroom certificate smoke: pins the checker, its soundness spine, the
gasful crown theorems, and the escape-free refinement view, with axiom
audits.
-/

#check EvmCompiler.Assembly.StackHeadroom.check?
#check EvmCompiler.Assembly.StackHeadroom.mkCert?
#check EvmCompiler.Assembly.StackHeadroom.mkCert?_check
#check EvmCompiler.Assembly.StackHeadroom.HeightPoint
#check EvmCompiler.Assembly.StackHeadroom.reach_heightPoint
#check EvmCompiler.Assembly.StackHeadroom.reach_noOverflow
#check EvmCompiler.Assembly.StackHeadroom.step_error_ne_stackOverflow_at
#check EvmCompiler.Assembly.StackHeadroom.x_ne_stackOverflow_of_invariants
#check EvmCompiler.Assembly.StackHeadroom.x_ne_stackOverflow_of_cert
#check EvmCompiler.Assembly.StackHeadroom.RunRefinesOpenNoStackOverflow
#check EvmCompiler.Assembly.StackHeadroom.runRefinesOpenNoStackOverflow_of_ne
#check EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.stackHeadroomCert?
#check EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow
#check EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix
#check EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow
#check EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow_withCodeSuffix

#print axioms EvmCompiler.Assembly.StackHeadroom.reach_noOverflow
#print axioms EvmCompiler.Assembly.StackHeadroom.x_ne_stackOverflow_of_cert
#print axioms EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.x_ne_stackOverflow
#print axioms EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow_withCodeSuffix
