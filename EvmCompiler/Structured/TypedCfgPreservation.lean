import EvmCompiler.Structured.TypedCfgCompiler

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

namespace BasicInstr

theorem runAt_toCfg
    {instr : Structured.BasicInstr} {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType :
      TypedCfg.Instr.type?
        (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output) :
    TypedCfg.Instr.runAt
        (TypedCfgCompiler.BasicInstr.toCfg instr) input state =
      (instr.step state).map fun final => (final, output) := by
  unfold TypedCfg.Instr.runAt
  rw [hType]
  cases instr <;>
    rfl

end BasicInstr

namespace Code

/--
Straight-line Structured code and the generated TypedCfg body have identical
runtime behavior. The TypedCfg side additionally returns the symbolic output
shape already computed by the checked body typer.
-/
theorem runBody_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.Block.runBody (TypedCfgCompiler.Code.toCfg code) input state =
      (Structured.Code.run code state).map fun final => (final, output) := by
  induction code generalizing input output state with
  | nil =>
      simp [TypedCfgCompiler.Code.type?, TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?, TypedCfg.Block.runBody,
        Structured.Code.run] at hType ⊢
      cases hType
      rfl
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      simp only [TypedCfgCompiler.Code.toCfg, List.map_cons,
        TypedCfg.Block.bodyType?] at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
          simp [hHeadType] at hType
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [TypedCfgCompiler.Code.type?,
              TypedCfgCompiler.Code.toCfg] using hType
          simp only [TypedCfgCompiler.Code.toCfg, List.map_cons]
          unfold TypedCfg.Block.runBody
          rw [BasicInstr.runAt_toCfg hHeadType]
          cases hStep : instr.step state with
          | error err =>
              simp only [hStep, Except.map, Bind.bind, Except.bind,
                Structured.Code.run]
          | ok state' =>
              simp only [hStep, Except.map, Bind.bind, Except.bind,
                Structured.Code.run]
              exact ih hTailType

theorem runState_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state : RunState}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.Block.runBody (TypedCfgCompiler.Code.toCfg code) input
        state.evm =
      (Structured.Code.runState code state).map fun final =>
        (final.evm, output) := by
  rw [runBody_toCfg hType]
  unfold Structured.Code.runState
  cases hRun : Structured.Code.run code state.evm with
  | error err =>
      simp only [Bind.bind, Except.bind, Except.map]
  | ok final =>
      simp only [Bind.bind, Except.bind, Except.map]
      rfl

end Code

/--
View a compiled fragment as an independently executable CFG. The continuation
label need not occur in `blocks`: `TypedCfg.Program.runN` can expose reaching it
as a residual jump.
-/
def resultProgram (result : TypedCfgCompiler.Result)
    (entry : Assembly.Label) : TypedCfg.Program where
  entry := entry
  blocks := result.blocks

namespace Stmt

/--
The straight-line statement compiler preserves the independent Structured
semantics and reaches its supplied regular continuation in one CFG block.
-/
theorem runN_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hRun : Structured.Code.runState code state = .ok final) :
    (resultProgram result entry).runN 1 entry state.evm =
      Except.ok (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      simp [TypedCfg.Program.runN, TypedCfg.Program.step,
        resultProgram, TypedCfg.Program.findBlock?, TypedCfg.Block.run,
        Code.runState_toCfg hType, hRun, Except.map, Bind.bind, Except.bind,
        TypedCfg.Block.runTerm]

end Stmt

namespace Block

/--
An empty compiled statement list reaches its supplied regular continuation
without changing the source EVM state.
-/
theorem runN_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result) :
    (resultProgram result entry).runN 1 entry state.evm =
      Except.ok (TypedCfg.Outcome.jump regular state.evm) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  simp [TypedCfg.Program.runN, TypedCfg.Program.step,
    resultProgram, TypedCfg.Program.findBlock?, TypedCfg.Block.run,
    TypedCfg.Block.runBody, TypedCfg.Block.runTerm, Bind.bind, Except.bind]

end Block

end TypedCfgPreservation
end Structured
end EvmCompiler
