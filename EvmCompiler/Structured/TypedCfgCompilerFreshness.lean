import EvmCompiler.Structured.TypedCfgCompilerFacts

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompilerFacts
namespace Supply

mutual

theorem block_next_ge
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result) :
    supply ≤ result.next := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ fuel =>
      unfold TypedCfgCompiler.compileBlockFuel? at hCompile
      exact stmtList_next_ge hCompile

theorem stmtList_next_ge
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result) :
    supply ≤ result.next := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
  | succ fuel =>
      cases stmts with
      | nil =>
          simp [TypedCfgCompiler.compileStmtListFuel?,
            TypedCfgCompiler.mkBlock?] at hCompile
          cases hCompile
          exact Nat.le_refl supply
      | cons stmt rest =>
          unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
          cases hHead :
              TypedCfgCompiler.compileStmtFuel? fuel stmt ctx supply
                entry input (TypedCfgCompiler.restLabel supply) with
          | none =>
              simp [hHead] at hCompile
          | some headResult =>
              cases hFallthrough : headResult.fallthrough? with
              | none =>
                  simp [hHead, hFallthrough] at hCompile
                  cases hCompile
                  exact stmt_next_ge hHead
              | some tailInput =>
                  cases hTail :
                      TypedCfgCompiler.compileStmtListFuel? fuel rest ctx
                        headResult.next
                        (TypedCfgCompiler.restLabel supply)
                        tailInput regular with
                  | none =>
                      simp [hHead, hFallthrough, hTail] at hCompile
                  | some tailResult =>
                      simp [hHead, hFallthrough, hTail,
                        TypedCfgCompiler.Result.append] at hCompile
                      cases hCompile
                      exact
                        Nat.le_trans (stmt_next_ge hHead)
                          (stmtList_next_ge (result := tailResult) hTail)

theorem stmt_next_ge
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result) :
    supply ≤ result.next := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases stmt with
      | code code =>
          obtain ⟨output, _hType, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_code hCompile
          exact Nat.le_succ supply
      | if_ cond body =>
          obtain
              ⟨output, condition, bodyResult,
                _hType, _hSource, _hHead, hBody, _hRequire, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_if hCompile
          have hBodyNext := block_next_ge hBody
          exact Nat.le_trans (Nat.le_succ supply) hBodyNext
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, valueSlot, caseResult, defaultResult,
                _hType, _hSource, hHead, hCases, hDefault, rfl⟩ :=
            Switch.components_of_compileStmtFuel?_switch hCompile
          have hPop :
              TypedCfg.Instr.type? .pop valueShape =
                some { valueShape with slots := valueShape.slots.tail } := by
            rcases valueShape with ⟨slots, tail⟩
            cases slots with
            | nil =>
                simp at hHead
            | cons slot rest =>
                simp [TypedCfg.Instr.type?]
          have hCasesNext :=
            cases_next_ge hHead hPop hCases
          have hDefaultNext :=
            default_next_ge hPop hDefault
          exact
            Nat.le_trans (Nat.le_succ supply)
              (Nat.le_trans hCasesNext hDefaultNext)
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, condition,
                bodyResult, postResult, hInit, _hInitFallthrough,
                _hType, _hSource, _hHead, hBody, _hBodyRequire,
                hPost, _hPostRequire, rfl⟩ :=
            Loop.components_of_compileStmtFuel?_for hCompile
          have hInitNext := block_next_ge hInit
          have hBodyNext := block_next_ge hBody
          have hPostNext := block_next_ge hPost
          exact
            Nat.le_trans (Nat.le_succ supply)
              (Nat.le_trans hInitNext
                (Nat.le_trans hBodyNext hPostNext))
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
                    exact Nat.le_succ supply
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
                    exact Nat.le_succ supply
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
                    exact Nat.le_succ supply
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | call name =>
          obtain ⟨proc, hLookup⟩ :=
            Call.exists_lookup_of_compileStmtFuel?_call hCompile
          obtain ⟨returnShape, output, _hSource, _hAfter,
              _hType, rfl⟩ :=
            Call.components_of_compileStmtFuel?_call hLookup hCompile
          exact Nat.le_succ supply
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_terminal hCompile
          exact Nat.le_succ supply

theorem cases_next_ge
    {fuel : Nat} {cases : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result}
    (hHead : valueShape.slots.head? = some slot)
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? fuel cases ctx
          base supply idx valueShape bodyShape regular = some result) :
    supply ≤ result.next := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
  | succ compilerFuel =>
      cases cases with
      | nil =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          exact Nat.le_refl supply
      | cons head rest =>
          rcases head with ⟨caseValue, body⟩
          obtain ⟨bodyResult, tail, hBody, _hRequire, hTail, rfl⟩ :=
            Switch.components_of_compileCasesFuel?_cons
              hHead hPop hCompile
          exact
            Nat.le_trans (block_next_ge hBody)
              (cases_next_ge (result := tail) hHead hPop hTail)

theorem default_next_ge
    {fuel : Nat} {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? fuel defaultBody ctx
          supply entry valueShape bodyShape regular = some result) :
    supply ≤ result.next := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileDefaultFuel?] at hCompile
  | succ compilerFuel =>
      cases defaultBody with
      | none =>
          rw [
            Switch.components_of_compileDefaultFuel?_none
              hPop hCompile]
          exact Nat.le_succ supply
      | some body =>
          obtain ⟨bodyResult, hBody, _hRequire, rfl⟩ :=
            Switch.components_of_compileDefaultFuel?_some
              hPop hCompile
          have hBodyNext := block_next_ge hBody
          exact Nat.le_trans (Nat.le_succ supply) hBodyNext

end

theorem stmt_next_ge_succ
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result) :
    supply + 1 ≤ result.next := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases stmt with
      | code code =>
          obtain ⟨output, _hType, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_code hCompile
          exact Nat.le_refl (supply + 1)
      | if_ cond body =>
          obtain
              ⟨output, condition, bodyResult,
                _hType, _hSource, _hHead, hBody, _hRequire, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_if hCompile
          exact block_next_ge (result := bodyResult) hBody
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, valueSlot, caseResult, defaultResult,
                _hType, _hSource, hHead, hCases, hDefault, rfl⟩ :=
            Switch.components_of_compileStmtFuel?_switch hCompile
          have hPop :
              TypedCfg.Instr.type? .pop valueShape =
                some { valueShape with slots := valueShape.slots.tail } := by
            rcases valueShape with ⟨slots, tail⟩
            cases slots with
            | nil =>
                simp at hHead
            | cons slot rest =>
                simp [TypedCfg.Instr.type?]
          exact
            Nat.le_trans
              (cases_next_ge hHead hPop hCases)
              (default_next_ge (result := defaultResult) hPop hDefault)
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, condition,
                bodyResult, postResult, hInit, _hInitFallthrough,
                _hType, _hSource, _hHead, _hBody, _hBodyRequire,
                _hPost, _hPostRequire, rfl⟩ :=
            Loop.components_of_compileStmtFuel?_for hCompile
          exact block_next_ge (result := initResult) hInit
            |>.trans (block_next_ge (result := bodyResult) _hBody)
            |>.trans (block_next_ge (result := postResult) _hPost)
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
                    exact Nat.le_refl (supply + 1)
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
                    exact Nat.le_refl (supply + 1)
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
                    exact Nat.le_refl (supply + 1)
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | call name =>
          obtain ⟨proc, hLookup⟩ :=
            Call.exists_lookup_of_compileStmtFuel?_call hCompile
          obtain ⟨returnShape, output, _hSource, _hAfter,
              _hType, rfl⟩ :=
            Call.components_of_compileStmtFuel?_call hLookup hCompile
          exact Nat.le_refl (supply + 1)
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_terminal hCompile
          exact Nat.le_refl (supply + 1)

end Supply
end TypedCfgCompilerFacts
end Structured
end EvmCompiler
