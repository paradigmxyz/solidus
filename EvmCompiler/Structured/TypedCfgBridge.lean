import EvmCompiler.Structured.TypedContinuations
import EvmCompiler.TypedCfg

namespace EvmCompiler
namespace Structured
namespace TypedContinuations

/-!
Bridge from the older structured-control typed-continuation facade to the real
`TypedCfg` IR.

The old facade named symbolic shapes but still paired them with directly emitted
labeled assembly.  This module gives those public continuation contracts a
concrete `TypedCfg.Shape` projection so the refactor can migrate one compiler
constructor at a time: continuation proofs should target `TypedCfg` shapes,
while backend-specific call/return-token materialization remains in the later
lowering proof.
-/

namespace Shape

def toCfg : Shape → TypedCfg.Shape
  | .any => .caller
  | .unreachable => .caller
  | .named name => .caller [.local name]
  | .join scope tag => .caller [.temp scope tag]
  | .loop scope tag => .caller [.temp scope tag]
  | .afterCode input _code =>
      { input.toCfg with slots := .word :: input.toCfg.slots }
  | .afterCondition input _cond =>
      { input.toCfg with slots := .word :: input.toCfg.slots }
  | .afterSwitchPop input _scrutinee => input.toCfg
  | .procEntry name argc =>
      .caller
        ((List.range argc).map
          (fun idx => .local ("arg:" ++ name ++ ":" ++ toString idx)))
  | .procExit name retc =>
      .caller
        ((List.range retc).map (fun idx => .returnValue name idx))
  | .callReturn name token =>
      .caller [.returnPC token.toNat, .local ("call:" ++ name)]
  | .programEnd => .caller

@[simp] theorem toCfg_mainEntry :
    Shape.mainEntry.toCfg =
      TypedCfg.Shape.caller [.local "structured:main:entry"] := rfl

@[simp] theorem toCfg_switchValue (input : Shape) (scrutinee : Code) :
    (Shape.switchValue input scrutinee).toCfg =
      { input.toCfg with slots := .word :: input.toCfg.slots } := rfl

end Shape

namespace Kont

def toCfgTarget (kont : Kont) : Option TypedCfg.Label :=
  kont.label?

def toCfgShape (kont : Kont) : TypedCfg.Shape :=
  kont.shape.toCfg

end Kont

namespace LabelDecl

def toCfgBlock (decl : LabelDecl) : TypedCfg.Block where
  label := decl.label
  input := decl.shape.toCfg
  body := []
  output := decl.shape.toCfg
  term := .invalid

@[simp] theorem toCfgBlock_label (decl : LabelDecl) :
    decl.toCfgBlock.label = decl.label := rfl

@[simp] theorem toCfgBlock_input (decl : LabelDecl) :
    decl.toCfgBlock.input = decl.shape.toCfg := rfl

end LabelDecl

namespace LabelMap

def toCfgBlocks (labels : LabelMap) : List TypedCfg.Block :=
  labels.map LabelDecl.toCfgBlock

end LabelMap

namespace Result

def labelShapeProgram (result : Result) (entryLabel : TypedCfg.Label) :
    TypedCfg.Program where
  entry := entryLabel
  blocks := result.labels.toCfgBlocks

end Result

end TypedContinuations
end Structured
end EvmCompiler
