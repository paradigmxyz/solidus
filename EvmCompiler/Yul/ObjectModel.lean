import EvmCompiler.Yul.Compiler
import EvmCompiler.Yul.Semantics
import EvmCompiler.Objects.Layout

namespace EvmCompiler
namespace Yul

/-
Yul object-source support.

The imported Nethermind Yul AST is the executable core: it has numeric
literals, variables, primitive calls, and user calls, but not string-named
object/data sections.  This module adds a source-facing object layer whose only
extra code constructs are the object-layout builtins:

* `datasize(name)`, lowered to a checked layout size constant;
* `dataoffset(name)`, lowered to a checked layout offset constant;
* `datacopy(dst, offset, size)`, lowered to EVM-Yul `codecopy`.

The code image/layout computation stays at the object boundary.  The public
helpers below expose a checked elaboration to the existing core Yul/source
interpreter with `ExecutionEnv.codeBytes` installed to the serialized object
image.
-/
namespace ObjectModel

abbrev PrimOp := EvmYul.Operation .Yul
abbrev AstFunctionName := EvmYul.Yul.Ast.YulFunctionName
abbrev DataSection := Objects.DataSection
abbrev ObjectLayout := Objects.ObjectLayout.Layout
abbrev ObjectLayoutEntry := Objects.ObjectLayout.Entry

structure ImmutableReference where
  start : Nat
  length : Nat
  deriving Inhabited, Repr

namespace ImmutableReference

def patchLength : Nat :=
  32

def isPatchable (reference : ImmutableReference) : Bool :=
  reference.length == patchLength

end ImmutableReference

def findNamed? {α : Type} (entries : List (Name × α)) (name : Name) :
    Option α := do
  let entry ← entries.find? fun entry => entry.fst == name
  some entry.snd

def collectNamedLists {α : Type}
    (entries : List (Name × List α)) (name : Name) : List α :=
  entries.foldr
    (fun entry acc =>
      if entry.fst == name then
        entry.snd ++ acc
      else
        acc)
    []

inductive LayoutMode where
  | placeholder
  | checked (layout : ObjectLayout)
  | placeholderWith
      (linkerSymbols immutableValues : List (Name × Word))
      (immutableReferences : List (Name × List ImmutableReference))
  | checkedWith
      (layout : ObjectLayout)
      (linkerSymbols immutableValues : List (Name × Word))
      (immutableReferences : List (Name × List ImmutableReference))
  deriving Inhabited, Repr

namespace LayoutMode

def offset? : LayoutMode → Name → Option Word
  | .placeholder, _name => some (EvmYul.UInt256.ofNat 0)
  | .checked layout, name => Objects.ObjectLayout.offset? layout name
  | .placeholderWith .., _name => some (EvmYul.UInt256.ofNat 0)
  | .checkedWith layout .., name => Objects.ObjectLayout.offset? layout name

def size? : LayoutMode → Name → Option Word
  | .placeholder, _name => some (EvmYul.UInt256.ofNat 0)
  | .checked layout, name => Objects.ObjectLayout.size? layout name
  | .placeholderWith .., _name => some (EvmYul.UInt256.ofNat 0)
  | .checkedWith layout .., name => Objects.ObjectLayout.size? layout name

def linkerSymbol? : LayoutMode → Name → Option Word
  | .placeholder, _name => some (EvmYul.UInt256.ofNat 0)
  | .checked _layout, _name => none
  | .placeholderWith linkerSymbols _immutableValues _immutableReferences, name =>
      findNamed? linkerSymbols name
  | .checkedWith _layout linkerSymbols _immutableValues _immutableReferences,
      name =>
      findNamed? linkerSymbols name

def immutableValue? : LayoutMode → Name → Option Word
  | .placeholder, _name => some (EvmYul.UInt256.ofNat 0)
  | .checked _layout, _name => none
  | .placeholderWith _linkerSymbols immutableValues _immutableReferences,
      name =>
      findNamed? immutableValues name
  | .checkedWith _layout _linkerSymbols immutableValues _immutableReferences,
      name =>
      findNamed? immutableValues name

def immutableReferences? : LayoutMode → Name → Option (List ImmutableReference)
  | .placeholder, _name => none
  | .checked _layout, _name => none
  | .placeholderWith _linkerSymbols _immutableValues immutableReferences,
      name =>
      match collectNamedLists immutableReferences name with
      | [] => none
      | head :: tail => some (head :: tail)
  | .checkedWith _layout _linkerSymbols _immutableValues immutableReferences,
      name =>
      match collectNamedLists immutableReferences name with
      | [] => none
      | head :: tail => some (head :: tail)

end LayoutMode

mutual
  inductive Expr where
    | call (functionName : PrimOp ⊕ AstFunctionName) (args : List Expr)
    | var (name : Name)
    | lit (value : Word)
    | datasize (name : Name)
    | dataoffset (name : Name)
    | datacopy (dst offset size : Expr)
    | linkersymbol (name : Name)
    | loadimmutable (name : Name)
    | memoryguard (size : Word)
    deriving Inhabited, Repr

  inductive Stmt where
    | block (body : List Stmt)
    | let_ (names : List Name) (value? : Option Expr)
    | assign (names : List Name) (value : Expr)
    | exprStmtCall (value : Expr)
    | switch (scrutinee : Expr) (cases : List (Word × List Stmt))
        (defaultBody : List Stmt)
    | for_ (cond : Expr) (post body : List Stmt)
    | if_ (cond : Expr) (body : List Stmt)
    | setimmutable (offset : Expr) (name : Name) (value : Expr)
    | continue
    | break
    | leave
    deriving Inhabited, Repr
end

structure FunctionDefinition where
  params : List Name
  returns : List Name
  body : List Stmt
  deriving Inhabited, Repr

structure Contract where
  dispatcher : Stmt
  functions : List (AstFunctionName × FunctionDefinition)
  deriving Inhabited, Repr

mutual
  inductive Object where
    | mk (name : Name) (code : Contract)
        (data : List DataSection) (objects : List Object)
    deriving Inhabited
end

structure Program where
  root : Object
  linkerSymbols : List (Name × Word) := []
  immutableValues : List (Name × Word) := []
  immutableReferences : List (Name × List ImmutableReference) := []
  deriving Inhabited

namespace Layout

def entrySame? (left right : ObjectLayoutEntry) : Bool :=
  left.name == right.name && (left.offset == right.offset && left.size == right.size)

def entriesSame? : List ObjectLayoutEntry → List ObjectLayoutEntry → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      entrySame? left right && entriesSame? lefts rights
  | _, _ => false

def same? (left right : ObjectLayout) : Bool :=
  entriesSame? left.entries right.entries

theorem word_beq_eq_true_iff_eq (left right : Word) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftVal =>
      cases right with
      | mk rightVal =>
          constructor
          · intro hEq
            have hVal : leftVal = rightVal := eq_of_beq hEq
            cases hVal
            rfl
          · intro hEq
            cases hEq
            change (leftVal == leftVal) = true
            exact BEq.rfl

theorem entrySame?_eq_true {left right : ObjectLayoutEntry}
    (hSame : entrySame? left right = true) :
    left = right := by
  unfold entrySame? at hSame
  simp only [Bool.and_eq_true] at hSame
  have hName : left.name = right.name := beq_iff_eq.mp hSame.1
  have hOffset : left.offset = right.offset :=
    (word_beq_eq_true_iff_eq left.offset right.offset).1 hSame.2.1
  have hSize : left.size = right.size :=
    (word_beq_eq_true_iff_eq left.size right.size).1 hSame.2.2
  cases left
  cases right
  simp_all

theorem entriesSame?_eq_true {left right : List ObjectLayoutEntry}
    (hSame : entriesSame? left right = true) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [entriesSame?] at hSame ⊢
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [entriesSame?] at hSame
      | cons rightHead rightTail =>
          simp only [entriesSame?, Bool.and_eq_true] at hSame
          have hHead : head = rightHead := entrySame?_eq_true hSame.1
          have hTail : tail = rightTail := ih hSame.2
          simp [hHead, hTail]

theorem same?_eq_true {left right : ObjectLayout}
    (hSame : same? left right = true) :
    left = right := by
  cases left with
  | mk leftEntries =>
      cases right with
      | mk rightEntries =>
          change entriesSame? leftEntries rightEntries = true at hSame
          have hEntries : leftEntries = rightEntries :=
            entriesSame?_eq_true hSame
          simp [hEntries]

end Layout

namespace Expr

mutual
  noncomputable def toAst? (mode : LayoutMode) :
      Expr → Option AstExpr
    | .call functionName args => do
        let args ← List.toAst? mode args
        some (.Call functionName args)
    | .var name => some (.Var name)
    | .lit value => some (.Lit value)
    | .datasize name => do
        let value ← mode.size? name
        some (.Lit value)
    | .dataoffset name => do
        let value ← mode.offset? name
        some (.Lit value)
    | .datacopy dst offset size => do
        let dst ← toAst? mode dst
        let offset ← toAst? mode offset
        let size ← toAst? mode size
        some
          (.Call (.inl ((.Env .CODECOPY : EvmYul.Operation .Yul)))
            [dst, offset, size])
    | .linkersymbol name => do
        let value ← mode.linkerSymbol? name
        some (.Lit value)
    | .loadimmutable name => do
        let value ← mode.immutableValue? name
        some (.Lit value)
    | .memoryguard size => some (.Lit size)

  noncomputable def List.toAst? (mode : LayoutMode) :
      List Expr → Option (List AstExpr)
    | [] => some []
    | head :: tail => do
        let head ← toAst? mode head
        let tail ← List.toAst? mode tail
        some (head :: tail)
end

theorem toAst?_datasize_checked {layout : ObjectLayout}
    {name : Name} {value : Word}
    (hLookup : Objects.ObjectLayout.size? layout name = some value) :
    toAst? (.checked layout) (.datasize name) = some (.Lit value) := by
  simp [toAst?, LayoutMode.size?, hLookup]

theorem toAst?_dataoffset_checked {layout : ObjectLayout}
    {name : Name} {value : Word}
    (hLookup : Objects.ObjectLayout.offset? layout name = some value) :
    toAst? (.checked layout) (.dataoffset name) = some (.Lit value) := by
  simp [toAst?, LayoutMode.offset?, hLookup]

theorem toAst?_datacopy_checked {mode : LayoutMode}
    {dst offset size : Expr} {dstAst offsetAst sizeAst : AstExpr}
    (hDst : toAst? mode dst = some dstAst)
    (hOffset : toAst? mode offset = some offsetAst)
    (hSize : toAst? mode size = some sizeAst) :
    toAst? mode (.datacopy dst offset size) =
      some
        (.Call (.inl ((.Env .CODECOPY : EvmYul.Operation .Yul)))
          [dstAst, offsetAst, sizeAst]) := by
  simp [toAst?, hDst, hOffset, hSize]

end Expr

namespace ImmutableReference

def patchAstStmt? (reference : ImmutableReference)
    (base value : AstExpr) : Option AstStmt :=
  if reference.isPatchable then
    some
      (.ExprStmtCall
        (.Call (.inl ((.StackMemFlow .MSTORE : EvmYul.Operation .Yul)))
          [ .Call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
              [base, .Lit (EvmYul.UInt256.ofNat reference.start)]
          , value ]))
  else
    none

namespace List

def patchAstStmts? : List ImmutableReference → AstExpr → AstExpr →
    Option (List AstStmt)
  | [], _base, _value => some []
  | reference :: rest, base, value => do
      let head ← reference.patchAstStmt? base value
      let tail ← patchAstStmts? rest base value
      some (head :: tail)

end List
end ImmutableReference

namespace Stmt

mutual
  noncomputable def toAst? (mode : LayoutMode) :
      Stmt → Option AstStmt
    | .block body => do
        let body ← List.toAst? mode body
        some (.Block body)
    | .let_ names none => some (.Let names none)
    | .let_ names (some value) => do
        let value ← Expr.toAst? mode value
        some (.Let names (some value))
    | .assign names value => do
        let value ← Expr.toAst? mode value
        some (.Assign names value)
    | .exprStmtCall value => do
        let value ← Expr.toAst? mode value
        some (.ExprStmtCall value)
    | .switch scrutinee cases defaultBody => do
        let scrutinee ← Expr.toAst? mode scrutinee
        let cases ← Cases.toAst? mode cases
        let defaultBody ← List.toAst? mode defaultBody
        some (.Switch scrutinee cases defaultBody)
    | .for_ cond post body => do
        let cond ← Expr.toAst? mode cond
        let post ← List.toAst? mode post
        let body ← List.toAst? mode body
        some (.For cond post body)
    | .if_ cond body => do
        let cond ← Expr.toAst? mode cond
        let body ← List.toAst? mode body
        some (.If cond body)
    | .setimmutable offset name value => do
        let offset ← Expr.toAst? mode offset
        let value ← Expr.toAst? mode value
        let references ← mode.immutableReferences? name
        let patchStmts ←
          ImmutableReference.List.patchAstStmts? references offset value
        some (.Block patchStmts)
    | .continue => some .Continue
    | .break => some .Break
    | .leave => some .Leave

  noncomputable def List.toAst? (mode : LayoutMode) :
      List Stmt → Option (List AstStmt)
    | [] => some []
    | head :: tail => do
        let head ← toAst? mode head
        let tail ← List.toAst? mode tail
        some (head :: tail)

  noncomputable def Cases.toAst? (mode : LayoutMode) :
      List (Word × List Stmt) → Option (List (Word × List AstStmt))
    | [] => some []
    | (value, body) :: tail => do
        let body ← List.toAst? mode body
        let tail ← Cases.toAst? mode tail
        some ((value, body) :: tail)
end

end Stmt

namespace FunctionDefinition

noncomputable def toAst? (mode : LayoutMode)
    (fn : FunctionDefinition) : Option AstFunctionDefinition := do
  let body ← Stmt.List.toAst? mode fn.body
  some (.Def fn.params fn.returns body)

end FunctionDefinition

namespace Contract

def functionNames (contract : Contract) : List AstFunctionName :=
  contract.functions.map Prod.fst

noncomputable def functionMapUnchecked? (mode : LayoutMode) :
    List (AstFunctionName × FunctionDefinition) →
      Option (Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition))
  | [] => some ∅
  | (name, fn) :: rest => do
      let fn ← fn.toAst? mode
      let rest ← functionMapUnchecked? mode rest
      some (rest.insert name fn)

noncomputable def functionMap? (mode : LayoutMode)
    (entries : List (AstFunctionName × FunctionDefinition)) :
    Option (Finmap (fun (_ : AstFunctionName) => AstFunctionDefinition)) :=
  if decide ((entries.map Prod.fst).Nodup) then
    functionMapUnchecked? mode entries
  else
    none

noncomputable def toAst? (mode : LayoutMode)
    (contract : Contract) : Option AstContract := do
  let dispatcher ← Stmt.toAst? mode contract.dispatcher
  let functions ← functionMap? mode contract.functions
  some { dispatcher := dispatcher, functions := functions }

noncomputable def toCoreProgram? (mode : LayoutMode)
    (contract : Contract) : Option Yul.Program := do
  let contract ← toAst? mode contract
  some { contract := contract }

noncomputable def toFunctionProgram? (mode : LayoutMode)
    (contract : Contract) : Option Functions.Program := do
  let core ← toCoreProgram? mode contract
  let lower ← core.toObjects?
  some lower.root.code

end Contract

namespace Object

def name : Object → Name
  | .mk name _code _data _objects => name

def code : Object → Contract
  | .mk _name code _data _objects => code

def data : Object → List DataSection
  | .mk _name _code data _objects => data

def objects : Object → List Object
  | .mk _name _code _data objects => objects

mutual
  noncomputable def toObjectsPlaceholderWith? (mode : LayoutMode) :
      Object → Option Objects.Object
    | .mk name code data objects => do
        let code ← code.toFunctionProgram? mode
        let objects ← ObjectList.toObjectsPlaceholderWith? mode objects
        some (.mk name code data objects)

  noncomputable def ObjectList.toObjectsPlaceholderWith? (mode : LayoutMode) :
      List Object → Option (List Objects.Object)
    | [] => some []
    | object :: rest => do
        let object ← toObjectsPlaceholderWith? mode object
        let rest ← ObjectList.toObjectsPlaceholderWith? mode rest
        some (object :: rest)
end

mutual
  noncomputable def toObjectsPlaceholder? :
      Object → Option Objects.Object
    | object => toObjectsPlaceholderWith? .placeholder object

  noncomputable def ObjectList.toObjectsPlaceholder? :
      List Object → Option (List Objects.Object)
    | objects => ObjectList.toObjectsPlaceholderWith? .placeholder objects
end

mutual
  noncomputable def toObjectsWithPrelayoutWith?
      (modeOfLayout : ObjectLayout → LayoutMode) :
      Object → Objects.Object → Option Objects.Object
    | .mk name code data objects, prelim => do
        let layout ← Objects.Object.payloadLayout? prelim
        let code ← code.toFunctionProgram? (modeOfLayout layout)
        let objects ←
          ObjectList.toObjectsWithPrelayoutWith? modeOfLayout objects
            prelim.objects
        some (.mk name code data objects)

  noncomputable def ObjectList.toObjectsWithPrelayoutWith?
      (modeOfLayout : ObjectLayout → LayoutMode) :
      List Object → List Objects.Object → Option (List Objects.Object)
    | [], [] => some []
    | object :: rest, prelim :: prelimRest => do
        let object ←
          toObjectsWithPrelayoutWith? modeOfLayout object prelim
        let rest ←
          ObjectList.toObjectsWithPrelayoutWith? modeOfLayout rest prelimRest
        some (object :: rest)
    | _, _ => none
end

mutual
  noncomputable def toObjectsWithPrelayout? :
      Object → Objects.Object → Option Objects.Object
    | object, prelim =>
        toObjectsWithPrelayoutWith? (fun layout => .checked layout) object
          prelim

  noncomputable def ObjectList.toObjectsWithPrelayout? :
      List Object → List Objects.Object → Option (List Objects.Object)
    | objects, prelims =>
        ObjectList.toObjectsWithPrelayoutWith? (fun layout => .checked layout)
          objects prelims
end

mutual
  noncomputable def layoutStableFuel? :
      Nat → Objects.Object → Objects.Object → Bool
    | 0, _prelim, _final => false
    | fuel + 1, prelim, final =>
        match Objects.Object.payloadLayout? prelim,
            Objects.Object.payloadLayout? final with
        | some prelimLayout, some finalLayout =>
            Layout.same? prelimLayout finalLayout &&
              ObjectList.layoutStableFuel? fuel prelim.objects final.objects
        | _, _ => false

  noncomputable def ObjectList.layoutStableFuel? :
      Nat → List Objects.Object → List Objects.Object → Bool
    | 0, _prelim, _final => false
    | _fuel + 1, [], [] => true
    | fuel + 1, prelim :: prelimRest, final :: finalRest =>
        layoutStableFuel? fuel prelim final &&
          ObjectList.layoutStableFuel? fuel prelimRest finalRest
    | _fuel + 1, _, _ => false
end

noncomputable def layoutStable? (prelim final : Objects.Object) : Bool :=
  layoutStableFuel? (sizeOf prelim + sizeOf final + 1) prelim final

theorem layoutStableFuel?_payloadLayout_eq {fuel : Nat}
    {prelim final : Objects.Object} {prelimLayout finalLayout : ObjectLayout}
    (hStable : layoutStableFuel? fuel prelim final = true)
    (hPrelim : Objects.Object.payloadLayout? prelim = some prelimLayout)
    (hFinal : Objects.Object.payloadLayout? final = some finalLayout) :
    prelimLayout = finalLayout := by
  cases fuel with
  | zero =>
      simp [layoutStableFuel?] at hStable
  | succ fuel =>
      simp [layoutStableFuel?, hPrelim, hFinal, Bool.and_eq_true] at hStable
      exact Layout.same?_eq_true hStable.1

theorem layoutStable?_payloadLayout_eq {prelim final : Objects.Object}
    {prelimLayout finalLayout : ObjectLayout}
    (hStable : layoutStable? prelim final = true)
    (hPrelim : Objects.Object.payloadLayout? prelim = some prelimLayout)
    (hFinal : Objects.Object.payloadLayout? final = some finalLayout) :
    prelimLayout = finalLayout := by
  exact
    layoutStableFuel?_payloadLayout_eq
      (fuel := sizeOf prelim + sizeOf final + 1)
      hStable hPrelim hFinal

end Object

namespace Program

def placeholderMode (program : Program) : LayoutMode :=
  .placeholderWith program.linkerSymbols program.immutableValues
    program.immutableReferences

def checkedMode (program : Program) (layout : ObjectLayout) : LayoutMode :=
  .checkedWith layout program.linkerSymbols program.immutableValues
    program.immutableReferences

noncomputable def toObjects? (program : Program) : Option Objects.Program := do
  let prelim ←
    program.root.toObjectsPlaceholderWith? (placeholderMode program)
  let final ←
    program.root.toObjectsWithPrelayoutWith? (checkedMode program) prelim
  if Object.layoutStable? prelim final then
    some { root := final }
  else
    none

noncomputable def toRootCoreProgram? (program : Program) :
    Option Yul.Program := do
  let prelim ←
    program.root.toObjectsPlaceholderWith? (placeholderMode program)
  let layout ← Objects.Object.payloadLayout? prelim
  let core ← program.root.code.toCoreProgram? (checkedMode program layout)
  let final ←
    program.root.toObjectsWithPrelayoutWith? (checkedMode program) prelim
  if Object.layoutStable? prelim final then
    some core
  else
    none

noncomputable def bytecodeImage? (program : Program) : Option ByteArray := do
  let lower ← toObjects? program
  Objects.Program.bytecodeImage? lower

def Accepted (program : Program) : Prop :=
  ∃ lower : Objects.Program,
    toObjects? program = some lower ∧ Objects.Program.Accepted lower

def SourceAccepted (program : Program) : Prop :=
  ∃ lower : Objects.Program,
    toObjects? program = some lower ∧ Objects.Program.SourceAccepted lower

theorem sourceAccepted_of_accepted {program : Program}
    (hAccepted : Accepted program) :
    SourceAccepted program := by
  rcases hAccepted with ⟨lower, hLower, hAcceptedLower⟩
  exact
    ⟨lower, hLower,
      Objects.Program.sourceAccepted_of_accepted hAcceptedLower⟩

noncomputable def sourceRunChecked? (fuel : Nat) (program : Program)
    (state : ReferenceState) :
    Option (Except ReferenceException ReferenceResult) := do
  let core ← toRootCoreProgram? program
  let image ← bytecodeImage? program
  some (Yul.Program.runWithCodeImage fuel core image state)

noncomputable def compileArtifact?
    (program : Program) : Option Objects.Program.CompileArtifact := do
  let lower ← toObjects? program
  Objects.Program.compileArtifact? lower

noncomputable def compile?
    (program : Program) : Option Assembly.TargetProgram :=
  Compiler.Artifact.target? (compileArtifact? program)

theorem compileArtifact?_valid
    {program : Program} {artifact : Objects.Program.CompileArtifact}
    (hCompile : compileArtifact? program = some artifact) :
    ∃ lower : Objects.Program,
      toObjects? program = some lower ∧
        artifact.Valid Objects.Program.defaultBackendPolicy lower := by
  unfold compileArtifact? at hCompile
  cases hLower : toObjects? program with
  | none =>
      simp [hLower] at hCompile
  | some lower =>
      simp [hLower] at hCompile
      exact
        ⟨lower, rfl,
          Objects.Program.compileArtifactWithPolicy?_valid hCompile⟩

def CheckedLowering (program : Program) (lower : Objects.Program) : Prop :=
  ∃ prelim : Objects.Object,
    program.root.toObjectsPlaceholderWith? (placeholderMode program) =
      some prelim ∧
      program.root.toObjectsWithPrelayoutWith? (checkedMode program) prelim =
        some lower.root ∧
        Object.layoutStable? prelim lower.root = true

theorem toObjects?_checked {program : Program} {lower : Objects.Program}
    (hLower : toObjects? program = some lower) :
    CheckedLowering program lower := by
  unfold toObjects? at hLower
  cases hPrelim :
      program.root.toObjectsPlaceholderWith? (placeholderMode program) with
  | none =>
      simp [hPrelim] at hLower
  | some prelim =>
      cases hFinal :
          program.root.toObjectsWithPrelayoutWith? (checkedMode program)
            prelim with
      | none =>
          simp [hPrelim, hFinal] at hLower
      | some final =>
          cases hStable : Object.layoutStable? prelim final <;>
          simp [hPrelim, hFinal, hStable] at hLower
          subst hLower
          exact ⟨prelim, hPrelim, hFinal, hStable⟩

theorem bytecodeImage?_checked {program : Program} {image : ByteArray}
    (hImage : bytecodeImage? program = some image) :
    ∃ lower : Objects.Program,
      toObjects? program = some lower ∧
        Objects.Program.bytecodeImage? lower = some image := by
  unfold bytecodeImage? at hImage
  cases hLower : toObjects? program with
  | none =>
      simp [hLower] at hImage
  | some lower =>
      have hImageLower :
          Objects.Program.bytecodeImage? lower = some image := by
        simpa [bytecodeImage?, hLower] using hImage
      exact ⟨lower, rfl, hImageLower⟩

theorem toRootCoreProgram?_checked {program : Program} {core : Yul.Program}
    (hCore : toRootCoreProgram? program = some core) :
    ∃ prelim final : Objects.Object, ∃ layout : ObjectLayout,
      program.root.toObjectsPlaceholderWith? (placeholderMode program) =
        some prelim ∧
        Objects.Object.payloadLayout? prelim = some layout ∧
          program.root.code.toCoreProgram? (checkedMode program layout) =
            some core ∧
            program.root.toObjectsWithPrelayoutWith? (checkedMode program)
              prelim = some final ∧
              Object.layoutStable? prelim final = true := by
  unfold toRootCoreProgram? at hCore
  cases hPrelim :
      program.root.toObjectsPlaceholderWith? (placeholderMode program) with
  | none =>
      simp [hPrelim] at hCore
  | some prelim =>
      cases hLayout : Objects.Object.payloadLayout? prelim with
      | none =>
          simp [hPrelim, hLayout] at hCore
      | some layout =>
          cases hCoreLower :
              program.root.code.toCoreProgram? (checkedMode program layout) with
          | none =>
              simp [hPrelim, hLayout, hCoreLower] at hCore
          | some coreLower =>
              cases hFinal :
                  program.root.toObjectsWithPrelayoutWith?
                    (checkedMode program) prelim with
              | none =>
                  simp [hPrelim, hLayout, hFinal] at hCore
              | some final =>
                  cases hStable : Object.layoutStable? prelim final <;>
                    simp [hPrelim, hLayout, hCoreLower, hFinal, hStable]
                      at hCore
                  subst hCore
                  exact
                    ⟨prelim, final, layout, rfl, hLayout, hCoreLower, hFinal,
                      hStable⟩

theorem sourceRunChecked?_checked {fuel : Nat} {program : Program}
    {state : ReferenceState}
    {result : Except ReferenceException ReferenceResult}
    (hRun : sourceRunChecked? fuel program state = some result) :
    ∃ core : Yul.Program, ∃ image : ByteArray,
      toRootCoreProgram? program = some core ∧
        bytecodeImage? program = some image ∧
          Yul.Program.runWithCodeImage fuel core image state = result := by
  unfold sourceRunChecked? at hRun
  cases hCore : toRootCoreProgram? program with
  | none =>
      simp [hCore] at hRun
  | some core =>
      cases hImage : bytecodeImage? program with
      | none =>
          simp [hCore, hImage] at hRun
      | some image =>
          have hRunCore :
              Yul.Program.runWithCodeImage fuel core image state = result := by
            simpa [sourceRunChecked?, hCore, hImage] using hRun
          exact ⟨core, image, rfl, rfl, hRunCore⟩

end Program

end ObjectModel
end Yul
end EvmCompiler
