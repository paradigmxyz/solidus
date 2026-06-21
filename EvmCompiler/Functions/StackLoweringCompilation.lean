import EvmCompiler.Functions.AllocationLayoutLowering
import EvmCompiler.Functions.StackLowering
import EvmCompiler.Locals.Compiler

/-!
Adjacent executable bridge from stack-scheduled Functions lowering to the
ordinary Locals compiler.  Semantic preservation remains owned by the
Functions-to-Locals proof boundary; this module contains no observer semantics
and does not bypass the existing Locals compiler.
-/

namespace EvmCompiler
namespace Functions
namespace StackLoweringCompilation

open AllocationLiveness

structure BlockArtifact
    (sourceCtx : StackLowering.Ctx) (demand : Demand)
    (pinned : LiveSet) (initial : Locals.Ctx) (source : Block) where
  facts : AllocationLivenessFacts.Region
  schedule : StackSchedule.Region
  locals : Locals.Block
  code : List Expressions.Stmt
  finalCtx : Locals.Ctx
  factsEq :
    AllocationLivenessFacts.annotateBlock? demand source = some facts
  scheduleEq :
    StackSchedule.scheduleBlock? pinned initial.layout source facts =
      some schedule
  lowerEq :
    StackLowering.lowerScheduledBlock? sourceCtx source schedule =
      some locals
  compileEq :
    Locals.Block.compileOpen initial locals = some (code, finalCtx)
  finalLayout : finalCtx.layout = schedule.finalLayout

def compileBlock?
    (sourceCtx : StackLowering.Ctx) (demand : Demand)
    (pinned : LiveSet) (initial : Locals.Ctx) (source : Block) :
    Option (BlockArtifact sourceCtx demand pinned initial source) :=
  match hFacts : AllocationLivenessFacts.annotateBlock? demand source with
  | none => none
  | some facts =>
      match hSchedule :
          StackSchedule.scheduleBlock? pinned initial.layout source facts with
      | none => none
      | some schedule =>
          match hLower :
              StackLowering.lowerScheduledBlock? sourceCtx source schedule with
          | none => none
          | some locals =>
              match hCompile : Locals.Block.compileOpen initial locals with
              | none => none
              | some (code, finalCtx) =>
                  if hFinal : finalCtx.layout = schedule.finalLayout then
                    some
                      { facts
                        schedule
                        locals
                        code
                        finalCtx
                        factsEq := hFacts
                        scheduleEq := hSchedule
                        lowerEq := hLower
                        compileEq := hCompile
                        finalLayout := hFinal }
                  else
                    none

theorem compileBlock?_sound
    {sourceCtx : StackLowering.Ctx} {demand : Demand}
    {pinned : LiveSet} {initial : Locals.Ctx} {source : Block}
    {artifact : BlockArtifact sourceCtx demand pinned initial source}
    (hCompile :
      compileBlock? sourceCtx demand pinned initial source = some artifact) :
    Locals.Block.compileOpen initial artifact.locals =
        some (artifact.code, artifact.finalCtx) ∧
      artifact.finalCtx.layout = artifact.schedule.finalLayout := by
  exact ⟨artifact.compileEq, artifact.finalLayout⟩

namespace Examples

def deadProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ← StackLowering.lowerProgram? StackLowering.Examples.deadProgram
  Locals.Program.compile? lower

theorem deadProgram_compiles : deadProgramCompiles?.isSome = true := by
  native_decide

def dormantCallProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ←
    StackLowering.lowerProgram?
      StackLowering.Examples.dormantCallProgram
  Locals.Program.compile? lower

theorem dormantCallProgram_compiles :
    dormantCallProgramCompiles?.isSome = true := by
  native_decide

def controlProgramCompiles? : Option Assembly.TargetProgram := do
  let lower ←
    StackLowering.lowerProgram? StackLowering.Examples.controlProgram
  Locals.Program.compile? lower

theorem controlProgram_compiles :
    controlProgramCompiles?.isSome = true := by
  native_decide

def controlMainBlockArtifact? :=
  compileBlock?
    { functions := [], returns := [] }
    { normal := ∅ } ∅ Locals.Ctx.initial
    StackLowering.Examples.controlProgram.body

theorem controlMainBlock_layout_checked :
    controlMainBlockArtifact?.isSome = true := by
  native_decide

end Examples

end StackLoweringCompilation
end Functions
end EvmCompiler
