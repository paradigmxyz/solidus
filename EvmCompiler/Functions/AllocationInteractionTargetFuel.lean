import EvmCompiler.Functions.AllocationInteractionCursor
import EvmCompiler.Expressions.TargetFuel

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionTargetFuel

abbrev stmtSize := Expressions.TargetFuel.stmtSize
abbrev blockSize := Expressions.TargetFuel.blockSize
abbrev stmtListSize := Expressions.TargetFuel.stmtListSize
abbrev caseListSize := Expressions.TargetFuel.caseListSize
abbrev defaultSize := Expressions.TargetFuel.defaultSize
abbrev stmtNestedSize := Expressions.TargetFuel.stmtNestedSize
abbrev stmtListNestedSize := Expressions.TargetFuel.stmtListNestedSize
abbrev structuredStmtSize := Expressions.TargetFuel.structuredStmtSize
abbrev structuredBlockSize := Expressions.TargetFuel.structuredBlockSize
abbrev structuredStmtListSize := Expressions.TargetFuel.structuredStmtListSize
abbrev structuredCaseListSize := Expressions.TargetFuel.structuredCaseListSize
abbrev structuredDefaultSize := Expressions.TargetFuel.structuredDefaultSize

theorem blockSize_toStructured (block : Expressions.Block) :
    structuredBlockSize block.toStructured = blockSize block :=
  Expressions.TargetFuel.blockSize_toStructured block

theorem stmtListSize_toStructured (stmts : List Expressions.Stmt) :
    structuredStmtListSize (Expressions.StmtList.toStructured stmts) =
      stmtListSize stmts :=
  Expressions.TargetFuel.stmtListSize_toStructured stmts

theorem structured_block_size_le_program
    {name : Structured.Name} {proc : Structured.Proc}
    {program : Structured.Program}
    (hLookup : Structured.ProcList.lookup? name program.procs = some proc) :
    structuredBlockSize proc.body ≤
      (program.procs.map fun candidate =>
        structuredBlockSize candidate.body).sum :=
  Expressions.TargetFuel.structured_block_size_le_program hLookup

@[simp] theorem stmtListSize_append
    (left right : List Expressions.Stmt) :
    stmtListSize (left ++ right) = stmtListSize left + stmtListSize right :=
  Expressions.TargetFuel.stmtListSize_append left right

@[simp] theorem stmtListNestedSize_append
    (left right : List Expressions.Stmt) :
    stmtListNestedSize (left ++ right) =
      stmtListNestedSize left + stmtListNestedSize right :=
  Expressions.TargetFuel.stmtListNestedSize_append left right

theorem stmtSize_eq (stmt : Expressions.Stmt) :
    stmtSize stmt = 1 + stmtNestedSize stmt :=
  Expressions.TargetFuel.stmtSize_eq stmt

theorem stmtListSize_eq (stmts : List Expressions.Stmt) :
    stmtListSize stmts = stmts.length + stmtListNestedSize stmts :=
  Expressions.TargetFuel.stmtListSize_eq stmts

theorem nestedSize_le_size (stmts : List Expressions.Stmt) :
    stmtListNestedSize stmts ≤ stmtListSize stmts :=
  Expressions.TargetFuel.nestedSize_le_size stmts

theorem stmtSize_pos (stmt : Expressions.Stmt) : 0 < stmtSize stmt :=
  Expressions.TargetFuel.stmtSize_pos stmt

theorem length_le_stmtListSize (stmts : List Expressions.Stmt) :
    stmts.length ≤ stmtListSize stmts :=
  Expressions.TargetFuel.length_le_stmtListSize stmts

theorem stmtListSize_suffix
    {whole pre suffix : List Expressions.Stmt}
    (hCode : whole = pre ++ suffix) :
    stmtListSize suffix ≤ stmtListSize whole :=
  Expressions.TargetFuel.stmtListSize_suffix hCode

theorem selected_block_size_le
    {value : Expressions.Word}
    {cases : List (Expressions.Word × Expressions.Block)}
    {defaultBody : Option Expressions.Block}
    {selected : Expressions.Block}
    (hSelect :
      Expressions.EffectSemantics.Switch.select value cases defaultBody =
        some selected) :
    blockSize selected ≤ caseListSize cases + defaultSize defaultBody :=
  Expressions.TargetFuel.selected_block_size_le hSelect

/-- Additional compiler-owned reserve carried by the recursive fixed point. -/
def Reserve
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationInteractionCursor.Compilation allocation program expressions}
    {root : AllocationInteractionCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      AllocationInteractionCursor.CoreCursor root scope live sourceBlock
        lowerState localsCtx)
    (targetExtra : Nat) : Prop :=
  stmtListNestedSize cursor.compiled ≤ targetExtra

namespace Reserve

/-- Exact statement tails inherit every nested-code reserve, with arbitrary
additional target slack. -/
theorem tail
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationInteractionCursor.Compilation allocation program expressions}
    {root : AllocationInteractionCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {targetExtra slack : Nat}
    {cursor :
      AllocationInteractionCursor.CoreCursor root scope live
        { stmts := stmt :: rest } beforeState beforeLocals}
    {tail :
      AllocationInteractionCursor.CoreCursor root scope
        (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals}
    (hReserve : Reserve cursor targetExtra)
    (hExact : AllocationInteractionCursor.ExactTail cursor tail) :
    Reserve tail (targetExtra + slack) := by
  rcases hExact.compiled with ⟨headCode, hCompiled⟩
  have hSuffix :
      stmtListNestedSize tail.compiled ≤
        stmtListNestedSize cursor.compiled := by
    rw [hCompiled, stmtListNestedSize_append]
    omega
  unfold Reserve at hReserve ⊢
  omega

end Reserve

end AllocationInteractionTargetFuel
end Functions
end EvmCompiler
