import EvmCompiler.Structured.TypedCfgPreservation.Core

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompilerFacts

/--
A compiler result contains the requested fragment entry with its checked input
shape.
-/
def HasEntry (result : TypedCfgCompiler.Result)
    (entry : Assembly.Label) (input : TypedCfg.Shape) : Prop :=
  ∃ block,
    block ∈ result.blocks ∧
      block.label = entry ∧
      block.input = input

theorem mkBlock?_label_input
    {label : Assembly.Label} {input : TypedCfg.Shape}
    {body : List TypedCfg.Instr} {term : TypedCfg.Terminator}
    {block : TypedCfg.Block}
    (hCompile :
      TypedCfgCompiler.mkBlock? label input body term = some block) :
    block.label = label ∧ block.input = input := by
  unfold TypedCfgCompiler.mkBlock? at hCompile
  cases hType : TypedCfg.Block.bodyType? body input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      simp [hType] at hCompile
      cases hCompile
      exact ⟨rfl, rfl⟩

mutual

theorem block_hasEntry
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result) :
    HasEntry result entry input := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ compilerFuel =>
      unfold TypedCfgCompiler.compileBlockFuel? at hCompile
      change
        TypedCfgCompiler.compileStmtListFuel? compilerFuel block.stmts ctx
            supply entry input regular = some result
        at hCompile
      exact stmtList_hasEntry hCompile

theorem stmtList_hasEntry
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result) :
    HasEntry result entry input := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
  | succ compilerFuel =>
      cases stmts with
      | nil =>
          simp [TypedCfgCompiler.compileStmtListFuel?,
            TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?] at hCompile
          cases hCompile
          exact
            ⟨{ label := entry
               input := input
               body := []
               output := input
               term := .jump regular },
              by simp, rfl, rfl⟩
      | cons stmt rest =>
          rcases
              TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
                hCompile with
            ⟨headResult, hHead, hNoTail | hTail⟩
          · rcases hNoTail with ⟨_hFallthrough, rfl⟩
            exact stmt_hasEntry hHead
          · rcases hTail with
              ⟨tailInput, tailResult,
                _hFallthrough, _hTailCompile, rfl⟩
            rcases stmt_hasEntry hHead with
              ⟨block, hMem, hLabel, hInput⟩
            exact
              ⟨block, by
                simp [TypedCfgCompiler.Result.append, hMem],
                hLabel, hInput⟩

theorem stmt_hasEntry
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result) :
    HasEntry result entry input := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases stmt with
      | code code =>
          obtain ⟨output, _hType, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_code hCompile
          exact
            ⟨{ label := entry
               input := input
               body := TypedCfgCompiler.Code.toCfg code
               output := output
               term := .jump regular },
              by simp, rfl, rfl⟩
      | if_ cond body =>
          obtain
              ⟨output, condition, bodyResult,
                _hType, _hSource, _hHead, _hBody, _hRequire, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_if hCompile
          exact
            ⟨{ label := entry
               input := input
               body := TypedCfgCompiler.Code.toCfg cond
               output := output
               term := .jumpi (LabelSupply.label supply 0) regular },
              by simp, rfl, rfl⟩
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, valueSlot, caseResult, defaultResult,
                _hType, _hSource, _hHead, _hCases, _hDefault, rfl⟩ :=
            Switch.components_of_compileStmtFuel?_switch hCompile
          exact
            ⟨{ label := entry
               input := input
               body := TypedCfgCompiler.Code.toCfg scrutinee
               output := valueShape
               term :=
                 .jump
                   (Switch.casesEntryLabel supply 0 cases) },
              by simp, rfl, rfl⟩
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, condition,
                bodyResult, postResult, hInit, _hInitFallthrough,
                _hType, _hSource, _hHead, _hBody, _hBodyRequire,
                _hPost, _hPostRequire, rfl⟩ :=
            Loop.components_of_compileStmtFuel?_for hCompile
          rcases block_hasEntry hInit with
            ⟨block, hMem, hLabel, hInput⟩
          exact
            ⟨block, by simp [hMem], hLabel, hInput⟩
      | brk =>
          unfold TypedCfgCompiler.compileStmtFuel? at hCompile
          cases hLabel : ctx.breakLabel? with
          | none =>
              simp [TypedCfgCompiler.checkedJumpOrInvalid, hLabel] at hCompile
          | some label =>
              cases hShape : ctx.breakShape? with
              | none =>
                  simp [TypedCfgCompiler.checkedJumpOrInvalid,
                    hLabel, hShape] at hCompile
              | some expected =>
                  by_cases hInput : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    exact
                      ⟨{ label := entry
                         input := input
                         body := []
                         output := input
                         term := .jump label },
                        by simp, rfl, rfl⟩
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | cont =>
          unfold TypedCfgCompiler.compileStmtFuel? at hCompile
          cases hLabel : ctx.continueLabel? with
          | none =>
              simp [TypedCfgCompiler.checkedJumpOrInvalid, hLabel] at hCompile
          | some label =>
              cases hShape : ctx.continueShape? with
              | none =>
                  simp [TypedCfgCompiler.checkedJumpOrInvalid,
                    hLabel, hShape] at hCompile
              | some expected =>
                  by_cases hInput : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    exact
                      ⟨{ label := entry
                         input := input
                         body := []
                         output := input
                         term := .jump label },
                        by simp, rfl, rfl⟩
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | leave =>
          unfold TypedCfgCompiler.compileStmtFuel? at hCompile
          cases hLabel : ctx.leaveLabel? with
          | none =>
              simp [TypedCfgCompiler.checkedJumpOrInvalid, hLabel] at hCompile
          | some label =>
              cases hShape : ctx.leaveShape? with
              | none =>
                  simp [TypedCfgCompiler.checkedJumpOrInvalid,
                    hLabel, hShape] at hCompile
              | some expected =>
                  by_cases hInput : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    exact
                      ⟨{ label := entry
                         input := input
                         body := []
                         output := input
                         term := .jump label },
                        by simp, rfl, rfl⟩
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | call name =>
          obtain ⟨proc, hLookup⟩ :=
            Call.exists_lookup_of_compileStmtFuel?_call hCompile
          obtain ⟨returnShape, output, _hSource, _hAfter,
              _hType, rfl⟩ :=
            Call.components_of_compileStmtFuel?_call hLookup hCompile
          exact
            ⟨{ label := entry
               input := input
               body :=
                 .returnToken (Structured.Stmt.callToken supply) ::
                   TypedCfgCompiler.sinkTopUnder proc.argc
               output := output
               term := .jump (ProcLabel.entry name) },
              by simp, rfl, rfl⟩
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_terminal hCompile
          exact
            ⟨{ label := entry
               input := input
               body := []
               output := input
               term := .halt kind },
              by simp, rfl, rfl⟩

end

end TypedCfgCompilerFacts
end Structured
end EvmCompiler
