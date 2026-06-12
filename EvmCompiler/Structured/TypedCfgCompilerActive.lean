import EvmCompiler.Structured.TypedCfgPreservation.Core

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompilerFacts

/--
A TypedCfg shape belongs to an active procedure activation when it contains the
compiler-owned return token.
-/
def ReturnTokenActive (shape : TypedCfg.Shape) : Prop :=
  ∃ depth, shape.returnTokenDepth? = some depth

/--
Every entry emitted by one Structured compiler result remains in the active
procedure frame, and any regular fallthrough does as well.
-/
structure ActiveResult (result : TypedCfgCompiler.Result) : Prop where
  blocks :
    ∀ block, block ∈ result.blocks → ReturnTokenActive block.input
  fallthrough :
    ∀ output, result.fallthrough? = some output →
      ReturnTokenActive output

namespace ReturnTokenActive

theorem tail
    {shape : TypedCfg.Shape}
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (hActive : ReturnTokenActive shape) :
    ReturnTokenActive
      { shape with slots := shape.slots.tail } := by
  rcases hActive with ⟨depth, hDepth⟩
  exact Shape.returnTokenDepth?_tail_some_of_some hSource hDepth

theorem code
    {code : Structured.Code} {input output : TypedCfg.Shape}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hActive : ReturnTokenActive input) :
    ReturnTokenActive output := by
  rcases hActive with ⟨depth, hDepth⟩
  exact
    TypedCfgPreservation.BasicInstr.Code.output_returnTokenDepth?_eq_some_of_input
      hType hDepth

theorem afterCall
    {input output : TypedCfg.Shape} {argc retc : Nat}
    (hSource : argc ≤ TypedCfgCompiler.Shape.sourceLength input)
    (hAfter :
      TypedCfgCompiler.Shape.afterCall input argc retc = some output)
    (hActive : ReturnTokenActive input) :
    ReturnTokenActive output := by
  rcases hActive with ⟨depth, hDepth⟩
  exact
    Shape.returnTokenDepth?_afterCall_some_of_some
      hSource hDepth hAfter

end ReturnTokenActive

namespace ActiveResult

theorem append
    {left right : TypedCfgCompiler.Result}
    (hLeft : ActiveResult left)
    (hRight : ActiveResult right) :
    ActiveResult (left.append right) := by
  constructor
  · intro block hMem
    rcases List.mem_append.mp hMem with hLeftMem | hRightMem
    · exact hLeft.blocks block hLeftMem
    · exact hRight.blocks block hRightMem
  · intro output hFallthrough
    exact hRight.fallthrough output hFallthrough

end ActiveResult

mutual

theorem activeResult_of_compileBlockFuel?
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActive : ReturnTokenActive input)
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result) :
    ActiveResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ compilerFuel =>
      unfold TypedCfgCompiler.compileBlockFuel? at hCompile
      exact
        activeResult_of_compileStmtListFuel?
          hActive hCompile

theorem activeResult_of_compileStmtListFuel?
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActive : ReturnTokenActive input)
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result) :
    ActiveResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
  | succ compilerFuel =>
      cases stmts with
      | nil =>
          simp [TypedCfgCompiler.compileStmtListFuel?,
            TypedCfgCompiler.mkBlock?] at hCompile
          cases hCompile
          exact
            { blocks := by
                intro block hMem
                simp at hMem
                subst block
                exact hActive
              fallthrough := by
                intro output hFallthrough
                simp at hFallthrough
                subst output
                exact hActive }
      | cons stmt rest =>
          rcases
              TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
                hCompile with
            ⟨headResult, hHead, hNoTail | hTail⟩
          · rcases hNoTail with ⟨_hFallthrough, rfl⟩
            exact activeResult_of_compileStmtFuel? hActive hHead
          · rcases hTail with
              ⟨tailInput, tailResult,
                hFallthrough, hTailCompile, rfl⟩
            have hHeadActive :=
              activeResult_of_compileStmtFuel? hActive hHead
            have hTailInput :=
              hHeadActive.fallthrough tailInput hFallthrough
            exact
              hHeadActive.append
                (activeResult_of_compileStmtListFuel?
                  hTailInput hTailCompile)

theorem activeResult_of_compileStmtFuel?
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActive : ReturnTokenActive input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result) :
    ActiveResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases stmt with
      | code code =>
          obtain ⟨output, hType, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_code hCompile
          have hOutput := hActive.code hType
          exact
            { blocks := by
                intro block hMem
                simp at hMem
                subst block
                exact hActive
              fallthrough := by
                intro final hFallthrough
                simp at hFallthrough
                subst final
                exact hOutput }
      | if_ cond body =>
          obtain
              ⟨output, _condition, bodyResult,
                hType, hSource, _hHead, hBody, _hRequire, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_if hCompile
          have hOutput := hActive.code hType
          have hSourceBound :
              1 ≤ TypedCfgCompiler.Shape.sourceLength output :=
            Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hBranch := hOutput.tail hSourceBound
          have hBodyActive :=
            activeResult_of_compileBlockFuel? hBranch hBody
          exact
            { blocks := by
                intro block hMem
                simp only [List.mem_cons] at hMem
                rcases hMem with rfl | hBodyMem
                · exact hActive
                · exact hBodyActive.blocks block hBodyMem
              fallthrough := by
                intro final hFallthrough
                simp at hFallthrough
                subst final
                exact hBranch }
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, valueSlot, caseResult, defaultResult,
                hType, hSource, hHead, hCases, hDefault, rfl⟩ :=
            Switch.components_of_compileStmtFuel?_switch hCompile
          have hValue := hActive.code hType
          have hSourceBound :
              1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
            Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hBody := hValue.tail hSourceBound
          have hPop :
              TypedCfg.Instr.type? .pop valueShape =
                some { valueShape with slots := valueShape.slots.tail } := by
            rcases valueShape with ⟨slots, tail⟩
            cases slots with
            | nil =>
                simp at hHead
            | cons slot rest =>
                simp [TypedCfg.Instr.type?]
          have hCasesActive :=
            activeResult_of_compileCasesFuel?
              hHead hPop hValue hBody hCases
          have hDefaultActive :=
            activeResult_of_compileDefaultFuel?
              hPop hValue hBody hDefault
          exact
            { blocks := by
                intro block hMem
                simp only [List.mem_cons, List.mem_append] at hMem
                rcases hMem with (rfl | hCaseMem) | hDefaultMem
                · exact hActive
                · exact hCasesActive.blocks block hCaseMem
                · exact hDefaultActive.blocks block hDefaultMem
              fallthrough := by
                intro final hFallthrough
                simp at hFallthrough
                subst final
                exact hBody }
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, _condition,
                bodyResult, postResult, hInit, hInitFallthrough,
                hType, hSource, _hHead, hBody, _hBodyRequire,
                hPost, _hPostRequire, rfl⟩ :=
            Loop.components_of_compileStmtFuel?_for hCompile
          have hInitActive :=
            activeResult_of_compileBlockFuel? hActive hInit
          have hLoop :=
            hInitActive.fallthrough loopInput hInitFallthrough
          have hCond := hLoop.code hType
          have hSourceBound :
              1 ≤ TypedCfgCompiler.Shape.sourceLength condOutput :=
            Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hBranch := hCond.tail hSourceBound
          have hBodyActive :=
            activeResult_of_compileBlockFuel? hBranch hBody
          have hPostActive :=
            activeResult_of_compileBlockFuel? hBranch hPost
          exact
            { blocks := by
                intro block hMem
                rcases List.mem_append.mp hMem with
                  hBeforePost | hPostMem
                rcases List.mem_append.mp hBeforePost with
                  hBeforeBody | hBodyMem
                rcases List.mem_append.mp hBeforeBody with
                  hInitMem | hLoopMem
                · exact hInitActive.blocks block hInitMem
                · have hBlock :
                      block =
                        { label := LabelSupply.label supply 0
                          input := loopInput
                          body := TypedCfgCompiler.Code.toCfg cond
                          output := condOutput
                          term :=
                            .jumpi (LabelSupply.label supply 1) regular } := by
                    simpa using hLoopMem
                  subst block
                  exact hLoop
                · exact hBodyActive.blocks block hBodyMem
                · exact hPostActive.blocks block hPostMem
              fallthrough := by
                intro final hFallthrough
                simp at hFallthrough
                subst final
                exact hBranch }
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
                      { blocks := by
                          intro block hMem
                          simp at hMem
                          subst block
                          exact hActive
                        fallthrough := by simp }
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
                      { blocks := by
                          intro block hMem
                          simp at hMem
                          subst block
                          exact hActive
                        fallthrough := by simp }
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
                      { blocks := by
                          intro block hMem
                          simp at hMem
                          subst block
                          exact hActive
                        fallthrough := by simp }
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | call name =>
          obtain ⟨proc, hLookup⟩ :=
            Call.exists_lookup_of_compileStmtFuel?_call hCompile
          obtain
              ⟨returnShape, _output, hSource, hAfter, _hType, rfl⟩ :=
            Call.components_of_compileStmtFuel?_call hLookup hCompile
          have hSourceBound :
              proc.argc ≤ TypedCfgCompiler.Shape.sourceLength input :=
            Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hReturn :=
            hActive.afterCall hSourceBound hAfter
          exact
            { blocks := by
                intro block hMem
                simp at hMem
                subst block
                exact hActive
              fallthrough := by
                intro final hFallthrough
                simp at hFallthrough
                subst final
                exact hReturn }
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            Stmt.components_of_compileStmtFuel?_terminal hCompile
          exact
            { blocks := by
                intro block hMem
                simp at hMem
                subst block
                exact hActive
              fallthrough := by simp }

theorem activeResult_of_compileCasesFuel?
    {fuel : Nat} {cases : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result}
    (hHead : valueShape.slots.head? = some slot)
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hValue : ReturnTokenActive valueShape)
    (hBody : ReturnTokenActive bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? fuel cases ctx
          base supply idx valueShape bodyShape regular = some result) :
    ActiveResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
  | succ compilerFuel =>
      cases cases with
      | nil =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          exact
            { blocks := by simp
              fallthrough := by
                intro output hFallthrough
                simp at hFallthrough
                subst output
                exact hBody }
      | cons head rest =>
          rcases head with ⟨caseValue, body⟩
          obtain
              ⟨bodyResult, tail, hBodyCompile, _hRequire,
                hTailCompile, rfl⟩ :=
            Switch.components_of_compileCasesFuel?_cons
              hHead hPop hCompile
          have hBodyResultActive :=
            activeResult_of_compileBlockFuel?
              hBody hBodyCompile
          have hTailActive :=
            activeResult_of_compileCasesFuel?
              hHead hPop hValue hBody hTailCompile
          exact
            { blocks := by
                intro block hMem
                rcases List.mem_append.mp hMem with
                  hPrefix | hTailMem
                · simp only [List.mem_cons] at hPrefix
                  rcases hPrefix with rfl | rfl | hBodyMem
                  · exact hValue
                  · exact hValue
                  · exact
                      hBodyResultActive.blocks block hBodyMem
                · exact hTailActive.blocks block hTailMem
              fallthrough := by
                intro output hFallthrough
                simp at hFallthrough
                subst output
                exact hBody }

theorem activeResult_of_compileDefaultFuel?
    {fuel : Nat} {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hValue : ReturnTokenActive valueShape)
    (hBody : ReturnTokenActive bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? fuel defaultBody ctx
          supply entry valueShape bodyShape regular = some result) :
    ActiveResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileDefaultFuel?] at hCompile
  | succ compilerFuel =>
      cases defaultBody with
      | none =>
          rw [
            Switch.components_of_compileDefaultFuel?_none
              hPop hCompile]
          exact
            { blocks := by
                intro block hMem
                simp at hMem
                subst block
                exact hValue
              fallthrough := by
                intro output hFallthrough
                simp at hFallthrough
                subst output
                exact hBody }
      | some body =>
          obtain ⟨bodyResult, hBodyCompile, _hRequire, rfl⟩ :=
            Switch.components_of_compileDefaultFuel?_some
              hPop hCompile
          have hBodyActive :=
            activeResult_of_compileBlockFuel?
              hBody hBodyCompile
          exact
            { blocks := by
                intro block hMem
                simp only [List.mem_cons] at hMem
                rcases hMem with rfl | hBodyMem
                · exact hValue
                · exact hBodyActive.blocks block hBodyMem
              fallthrough := by
                intro output hFallthrough
                simp at hFallthrough
                subst output
                exact hBody }

end

/--
The public block compiler inherits the active-result invariant from its
fuel-indexed implementation.
-/
theorem activeResult_of_compileBlock?
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActive : ReturnTokenActive input)
    (hCompile :
      TypedCfgCompiler.compileBlock? block ctx
          supply entry input regular = some result) :
    ActiveResult result := by
  apply activeResult_of_compileBlockFuel? hActive
  simpa [TypedCfgCompiler.compileBlock?] using hCompile

namespace ActiveResult

/--
The checked input selected for a lowered procedure body contains its
compiler-owned return token at the source argument depth.
-/
theorem procFragment_input
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs : List Structured.Proc} {proc : Structured.Proc}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes allProcs proc procBlocks procCalls) :
    fragment.input.returnTokenDepth? = some proc.argc := by
  rcases fragment.route with hDirect | hAdapter
  · rcases hDirect with ⟨_hEntry, hInput⟩
    simpa [hInput] using
      Call.returnTokenDepth?_procEntry proc
  · rcases hAdapter with
      ⟨_adapter, _hEntry, _hInput, hFrame,
        _hCompile, _hMem⟩
    exact
      Shape.requireReturnTokenDepth?_eq_some_iff.mp hFrame

/--
Every block emitted for a checked procedure fragment remains in the active
procedure frame, and so does any regular body fallthrough.
-/
theorem of_procFragment
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs : List Structured.Proc} {proc : Structured.Proc}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes allProcs proc procBlocks procCalls) :
    ActiveResult fragment.result :=
  activeResult_of_compileBlock?
    ⟨proc.argc, procFragment_input fragment⟩
    fragment.compile

end ActiveResult

end TypedCfgCompilerFacts
end Structured
end EvmCompiler
