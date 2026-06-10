import EvmCompiler.TypedCfg

open EvmCompiler

namespace TypedCfgLoweringInvariantsSmoke

def firstLabel : Assembly.Label :=
  .named "typedcfg:lowering:first"

def entryLabel : Assembly.Label :=
  .named "typedcfg:lowering:entry"

def reorderedProgram : TypedCfg.Program :=
  let shape := TypedCfg.Shape.closed
  { entry := entryLabel
    blocks :=
      [{ label := firstLabel
         input := shape
         body := []
         output := shape
         term := .invalid },
       { label := entryLabel
         input := shape
         body := []
         output := shape
         term := .invalid }] }

example :
    reorderedProgram.lower? =
      some
        [.label entryLabel, .prim .invalid,
          .label firstLabel, .prim .invalid] := by
  native_decide

example : reorderedProgram.compileCertified?.isSome = true := by
  native_decide

example {artifact : TypedCfg.Program.CertifiedArtifact}
    (hCompile :
      reorderedProgram.compileCertified? = some artifact) :
    artifact.target.accepted = true ∧ artifact.target.PCFits := by
  exact
    ⟨TypedCfg.Program.compileCertified?_targetAccepted hCompile,
      TypedCfg.Program.compileCertified?_pcFits hCompile⟩

def dispatchLabel : Assembly.Label :=
  .named "typedcfg:dispatch"

def returnTarget : Assembly.Label :=
  .named "typedcfg:return-target"

def caseLabel : Assembly.Label :=
  .generated 7 10000

def validDispatchProgram : TypedCfg.Program :=
  let dispatchShape := TypedCfg.Shape.closed [.returnToken]
  let targetShape := TypedCfg.Shape.closed
  { entry := dispatchLabel
    blocks :=
      [{ label := dispatchLabel
         input := dispatchShape
         body := []
         output := dispatchShape
         term :=
           .returnDispatch 0
             [{ token := EvmYul.UInt256.ofNat 7
                target := returnTarget
                caseLabel := caseLabel }] },
       { label := returnTarget
         input := targetShape
         body := []
         output := targetShape
         term := .invalid }] }

example : validDispatchProgram.compileCertified?.isSome = true := by
  native_decide

def collidingDispatchProgram : TypedCfg.Program :=
  let dispatchShape := TypedCfg.Shape.closed [.returnToken]
  let targetShape := TypedCfg.Shape.closed
  { entry := dispatchLabel
    blocks :=
      [{ label := dispatchLabel
         input := dispatchShape
         body := []
         output := dispatchShape
         term :=
           .returnDispatch 0
             [{ token := EvmYul.UInt256.ofNat 7
                target := returnTarget
                caseLabel := returnTarget }] },
       { label := returnTarget
         input := targetShape
         body := []
         output := targetShape
         term := .invalid }] }

example : collidingDispatchProgram.wellTyped? = false := by
  native_decide

example : collidingDispatchProgram.compileCertified? = none := by
  native_decide

end TypedCfgLoweringInvariantsSmoke
