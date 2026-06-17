import EvmCompiler.Structured.TypedCfgCompilerFacts

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompilerFacts

/--
The label was allocated before `supply`, or is a stable named label.

This is a compiler-allocation fact, independent of any observer or execution
semantics.
-/
def LabelBeforeSupply
    (label : Assembly.Label) (supply : LabelSupply) : Prop :=
  match label with
  | .named _ => True
  | .generated scope _ => scope < supply

namespace LabelBeforeSupply

theorem mono
    {label : Assembly.Label} {supply next : LabelSupply}
    (hBefore : LabelBeforeSupply label supply)
    (hSupply : supply ≤ next) :
    LabelBeforeSupply label next := by
  cases label with
  | named name =>
      trivial
  | generated scope tag =>
      simp only [LabelBeforeSupply] at hBefore ⊢
      exact Nat.lt_of_lt_of_le hBefore hSupply

theorem generated_ne
    {label : Assembly.Label} {supply scope tag : Nat}
    (hBefore : LabelBeforeSupply label supply)
    (hScope : supply ≤ scope) :
    .generated scope tag ≠ label := by
  cases label with
  | named name =>
      simp
  | generated prior priorTag =>
      simp only [LabelBeforeSupply] at hBefore
      intro hEq
      cases hEq
      omega

theorem restLabel_ne
    {label : Assembly.Label} {supply : LabelSupply}
    (hBefore : LabelBeforeSupply label supply) :
    TypedCfgCompiler.restLabel supply ≠ label := by
  simpa [TypedCfgCompiler.restLabel] using
    hBefore.generated_ne (Nat.le_refl supply)

end LabelBeforeSupply

/--
At a statement boundary the regular continuation is either inherited from an
older compiler generation or is the current statement-list tail label.
-/
def RegularAtSupply
    (regular : Assembly.Label) (supply : LabelSupply) : Prop :=
  LabelBeforeSupply regular supply ∨
    regular = TypedCfgCompiler.restLabel supply

namespace RegularAtSupply

theorem before_succ
    {regular : Assembly.Label} {supply : LabelSupply}
    (hRegular : RegularAtSupply regular supply) :
    LabelBeforeSupply regular (supply + 1) := by
  rcases hRegular with hBefore | rfl
  · cases regular with
    | named name =>
        trivial
    | generated scope tag =>
        simp only [LabelBeforeSupply] at hBefore ⊢
        omega
  · simp [LabelBeforeSupply, TypedCfgCompiler.restLabel]

theorem current_generated_ne
    {regular : Assembly.Label} {supply tag : Nat}
    (hRegular : RegularAtSupply regular supply)
    (hTag : tag ≠ 100) :
    .generated supply tag ≠ regular := by
  rcases hRegular with hBefore | rfl
  · exact hBefore.generated_ne (Nat.le_refl supply)
  · simpa [TypedCfgCompiler.restLabel] using hTag

theorem advance
    {regular : Assembly.Label} {supply next : LabelSupply}
    (hRegular : RegularAtSupply regular supply)
    (hNext : supply + 1 ≤ next) :
    RegularAtSupply regular next :=
  Or.inl (hRegular.before_succ.mono hNext)

end RegularAtSupply

/--
Every externally visible continuation predates the labels allocated by the
current compiler fragment.
-/
structure ContinuationLabelsBeforeSupply
    (ctx : TypedCfgCompiler.Context)
    (regular : Assembly.Label) (supply : LabelSupply) : Prop where
  regular : LabelBeforeSupply regular supply
  breakLabel :
    ∀ label, ctx.breakLabel? = some label →
      LabelBeforeSupply label supply
  continueLabel :
    ∀ label, ctx.continueLabel? = some label →
      LabelBeforeSupply label supply
  leaveLabel :
    ∀ label, ctx.leaveLabel? = some label →
      LabelBeforeSupply label supply

structure NonregularLabelsBeforeSupply
    (ctx : TypedCfgCompiler.Context) (supply : LabelSupply) : Prop where
  breakLabel :
    ∀ label, ctx.breakLabel? = some label →
      LabelBeforeSupply label supply
  continueLabel :
    ∀ label, ctx.continueLabel? = some label →
      LabelBeforeSupply label supply
  leaveLabel :
    ∀ label, ctx.leaveLabel? = some label →
      LabelBeforeSupply label supply

namespace NonregularLabelsBeforeSupply

theorem mono
    {ctx : TypedCfgCompiler.Context} {supply next : LabelSupply}
    (hBefore : NonregularLabelsBeforeSupply ctx supply)
    (hSupply : supply ≤ next) :
    NonregularLabelsBeforeSupply ctx next where
  breakLabel label hLabel :=
    (hBefore.breakLabel label hLabel).mono hSupply
  continueLabel label hLabel :=
    (hBefore.continueLabel label hLabel).mono hSupply
  leaveLabel label hLabel :=
    (hBefore.leaveLabel label hLabel).mono hSupply

theorem with_regular
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (hBefore : NonregularLabelsBeforeSupply ctx supply)
    (hRegular : LabelBeforeSupply regular supply) :
    ContinuationLabelsBeforeSupply ctx regular supply where
  regular := hRegular
  breakLabel := hBefore.breakLabel
  continueLabel := hBefore.continueLabel
  leaveLabel := hBefore.leaveLabel

end NonregularLabelsBeforeSupply

namespace ContinuationLabelsBeforeSupply

theorem nonregular
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (hBefore :
      ContinuationLabelsBeforeSupply ctx regular supply) :
    NonregularLabelsBeforeSupply ctx supply where
  breakLabel := hBefore.breakLabel
  continueLabel := hBefore.continueLabel
  leaveLabel := hBefore.leaveLabel

theorem mono
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply next : LabelSupply}
    (hBefore :
      ContinuationLabelsBeforeSupply ctx regular supply)
    (hSupply : supply ≤ next) :
    ContinuationLabelsBeforeSupply ctx regular next where
  regular := hBefore.regular.mono hSupply
  breakLabel label hLabel :=
    (hBefore.breakLabel label hLabel).mono hSupply
  continueLabel label hLabel :=
    (hBefore.continueLabel label hLabel).mono hSupply
  leaveLabel label hLabel :=
    (hBefore.leaveLabel label hLabel).mono hSupply

theorem rest_succ
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {supply : LabelSupply}
    (hBefore :
      ContinuationLabelsBeforeSupply ctx regular supply) :
    ContinuationLabelsBeforeSupply
      ctx (TypedCfgCompiler.restLabel supply) (supply + 1) where
  regular := by
    simp [
      LabelBeforeSupply,
      TypedCfgCompiler.restLabel]
  breakLabel label hLabel :=
    (hBefore.breakLabel label hLabel).mono (by simp)
  continueLabel label hLabel :=
    (hBefore.continueLabel label hLabel).mono (by simp)
  leaveLabel label hLabel :=
    (hBefore.leaveLabel label hLabel).mono (by simp)

end ContinuationLabelsBeforeSupply

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
