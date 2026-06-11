import EvmCompiler.TypedCfg
import EvmCompiler.Compiler.AllocatedTypedCfg
import EvmCompiler.Objects.Compiler

open EvmCompiler

namespace TypedCfgLoweringInvariantsSmoke

#check TypedCfg.Preservation.Program.lower?_step_eventually
#check TypedCfg.Preservation.Instr.lowerAt_source_runNResult
#check TypedCfg.Program.compileCertified?_step_eventually
#check Compiler.AllocatedTypedCfg.Program.compileCertified?_scopeLayouts
#check Compiler.AllocatedTypedCfg.Program.compileCertified?_step_eventually

def genericEntryShape : TypedCfg.Shape :=
  { slots := [.word, .returnToken]
    tail := .caller }

def namedEntryShape : TypedCfg.Shape :=
  { slots := [.local "value", .returnToken]
    tail := .caller }

example :
    TypedCfg.Instr.type? (.relabel namedEntryShape) genericEntryShape =
      some namedEntryShape := by
  native_decide

example :
    TypedCfg.Instr.lowerAt? (.relabel namedEntryShape) genericEntryShape =
      some ([], namedEntryShape) := by
  native_decide

example :
    TypedCfg.Instr.type?
        (.relabel (TypedCfg.Shape.caller [.local "value"]))
        genericEntryShape =
      none := by
  native_decide

def allocationDrivenProcShapeRecorded : Bool :=
  let source :=
    Functions.ScratchFrameSpill.AllocationExamples.program
  match
      Functions.ScratchFrameSpill.stackAllocationPlanner.plan? source with
  | none => false
  | some allocation =>
      let planned : Objects.Program.PlannedProgram :=
        { source := source
          backend := .inlineStack
          allocation := allocation }
      match planned.lowerWithAllocation? with
      | none => false
      | some expressions =>
          match planned.lowerTypedCfg? expressions with
          | none => false
          | some cfg =>
              decide
                (cfg.labelShape? (Structured.ProcLabel.body "f") =
                  some
                    { slots := [.local "p", .returnToken]
                      tail := .caller })

example : allocationDrivenProcShapeRecorded = true := by
  native_decide

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
