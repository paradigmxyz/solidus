import EvmCompiler.TypedCfg.Syntax
import EvmCompiler.Assembly.PrimSemantics
import Std.Data.HashMap.Lemmas

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def type? (instr : Instr) (shape : Shape) : Option Shape :=
  match instr with
  | .push value =>
      some { shape with slots := .literal value :: shape.slots }
  | .returnToken value =>
      some { shape with slots := .returnPC value.toNat :: shape.slots }
  | .prim op =>
      match op.stackArity? with
      | none => none
      | some (inputArity, outputArity) =>
          if inputArity ≤ shape.length then
            some
              (Shape.pushWords outputArity
                (Shape.pop inputArity shape))
          else
            none
  | .pop =>
      match shape.slots with
      | [] => none
      | _ :: rest => some { shape with slots := rest }
  | .dup depth =>
      if depth < 16 then
        match shape.get? depth with
        | some slot => some { shape with slots := slot :: shape.slots }
        | none => none
      else
        none
  | .swap depth =>
      if depth < 16 then
        match shape.slots, shape.get? (depth + 1) with
        | top :: rest, some slot =>
            some { shape with slots := slot :: rest.set depth top }
        | _, none => none
        | [], _ => none
      else
        none
  | .bindLocals offset names =>
      shape.bindLocals? offset names
  | .bindScratch baseDepth _name _slot =>
      shape.bindScratch? baseDepth
  | .relabel target =>
      if shape.relabelCompatible target then some target else none
  | .unwind target =>
      Shape.unwindTo target shape

theorem length_of_type?_prim
    {op : Assembly.PrimOp} {input output : Shape}
    {inputArity outputArity : Nat}
    (hArity : op.stackArity? = some (inputArity, outputArity))
    (hType : Instr.type? (.prim op) input = some output) :
    inputArity ≤ input.length ∧
      output.length =
        input.length - inputArity + outputArity := by
  simp only [Instr.type?] at hType
  rw [hArity] at hType
  by_cases hBound : inputArity ≤ input.length
  · simp [hBound] at hType
    cases hType
    change inputArity ≤ input.slots.length at hBound
    constructor
    · exact hBound
    · change
        (Shape.pushWords outputArity
            (Shape.pop inputArity input)).slots.length =
          input.slots.length - inputArity + outputArity
      simp [Shape.pushWords, Shape.pop, List.length_drop]
      omega
  · simp [hBound] at hType

theorem length_of_type?_pop
    {input output : Shape}
    (hType : Instr.type? .pop input = some output) :
    1 ≤ input.length ∧
      output.length = input.length - 1 := by
  cases input with
  | mk slots tail =>
      cases slots with
      | nil =>
          simp [Instr.type?] at hType
      | cons slot rest =>
          simp [Instr.type?] at hType
          cases hType
          simp [Shape.length]

theorem length_of_type?_dup
    {depth : Nat} {input output : Shape}
    (hType : Instr.type? (.dup depth) input = some output) :
    depth < 16 ∧
      depth + 1 ≤ input.length ∧
      output.length = input.length + 1 := by
  unfold Instr.type? at hType
  by_cases hDepth : depth < 16
  · simp [hDepth] at hType
    cases hGet : input.get? depth with
    | none =>
        simp [hGet] at hType
    | some slot =>
        simp [hGet] at hType
        cases hType
        have hIndex : depth < input.slots.length :=
          List.getElem?_eq_some_iff.mp hGet |>.1
        simp [Shape.length]
        omega
  · simp [hDepth] at hType

theorem length_of_type?_swap
    {depth : Nat} {input output : Shape}
    (hType : Instr.type? (.swap depth) input = some output) :
    depth < 16 ∧
      depth + 2 ≤ input.length ∧
      output.length = input.length := by
  unfold Instr.type? at hType
  by_cases hDepth : depth < 16
  · simp [hDepth] at hType
    cases hSlots : input.slots with
    | nil =>
        simp [Shape.get?, hSlots] at hType
    | cons top rest =>
        cases hGet : input.get? (depth + 1) with
        | none =>
            simp [hSlots, hGet] at hType
        | some slot =>
            simp [hSlots, hGet] at hType
            cases hType
            have hIndex : depth + 1 < input.slots.length :=
              List.getElem?_eq_some_iff.mp hGet |>.1
            simp [hSlots] at hIndex
            simp [Shape.length, hSlots, List.length_set]
            omega
  · simp [hDepth] at hType

theorem length_of_type?_bindLocals
    {offset : Nat} {names : List String}
    {input output : Shape}
    (hType :
      Instr.type? (.bindLocals offset names) input = some output) :
    output.length = input.length := by
  unfold Instr.type? Shape.bindLocals? at hType
  by_cases hBound : offset + names.length ≤ input.length
  · simp [hBound] at hType
    cases hType
    change offset + names.length ≤ input.slots.length at hBound
    have hOffset : offset ≤ input.slots.length := by omega
    simp [Shape.length, List.length_take, List.length_drop, hOffset]
    omega
  · simp [hBound] at hType

theorem length_of_type?_bindScratch
    {baseDepth : Nat} {name : String} {slot : Nat}
    {input output : Shape}
    (hType :
      Instr.type? (.bindScratch baseDepth name slot) input =
        some output) :
    output.length = input.length := by
  unfold Instr.type? Shape.bindScratch? at hType
  cases hGet : input.slots[baseDepth]? with
  | none =>
      simp [hGet] at hType
  | some existing =>
      simp [hGet] at hType
      cases hType
      simp [Shape.length]

end Instr

namespace Block

def bodyType? : List Instr → Shape → Option Shape
  | [], shape => some shape
  | instr :: rest, shape => do
      let shape' ← instr.type? shape
      bodyType? rest shape'

end Block

namespace Shape

def returnTokenDepthList? : List Slot → Option Nat
  | [] => none
  | .returnToken :: _ => some 0
  | .returnPC _ :: _ => some 0
  | _ :: rest => returnTokenDepthList? rest |>.map (· + 1)

def returnTokenDepth? (shape : Shape) : Option Nat :=
  returnTokenDepthList? shape.slots

end Shape

namespace Program

abbrev LabelShapeIndex := Std.HashMap Label Shape

def buildLabelShapeIndexFrom : List Block → LabelShapeIndex → LabelShapeIndex
  | [], index => index
  | block :: rest, index =>
      buildLabelShapeIndexFrom rest
        (index.insertIfNew block.label block.input)

def buildLabelShapeIndex (program : Program) : LabelShapeIndex :=
  buildLabelShapeIndexFrom program.blocks {}

theorem buildLabelShapeIndexFrom_get?
    (blocks : List Block) (index : LabelShapeIndex) (target : Label) :
    (buildLabelShapeIndexFrom blocks index).get? target =
      match index.get? target with
      | some existing => some existing
      | none =>
          (blocks.find? fun block => block.label == target).map Block.input := by
  induction blocks generalizing index with
  | nil =>
      cases hExisting : index.get? target <;>
        simp only [buildLabelShapeIndexFrom, List.find?_nil, Option.map_none,
          hExisting]
  | cons block rest ih =>
      rw [buildLabelShapeIndexFrom, ih]
      by_cases hLabel : block.label = target
      · subst target
        cases hExisting : index.get? block.label with
        | none =>
            have hExisting' : index[block.label]? = none := by
              simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
            have hNotMem : block.label ∉ index := by
              intro hMem
              have hSome :=
                (Std.HashMap.mem_iff_isSome_getElem?).mp hMem
              rw [hExisting'] at hSome
              simp at hSome
            simp only [Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insertIfNew]
            simp [hExisting', hNotMem]
        | some existing =>
            have hExisting' : index[block.label]? = some existing := by
              simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
            obtain ⟨hMem, _hGet⟩ :=
              Std.HashMap.getElem?_eq_some_iff.mp hExisting'
            simp only [Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insertIfNew]
            simp only [beq_self_eq_true, true_and, hMem,
              not_true_eq_false, if_false, hExisting']
      · have hBeq : (block.label == target) = false := by
          simpa using hLabel
        simp only [Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insertIfNew]
        simp [hBeq, hLabel]

theorem buildLabelShapeIndex_get? (program : Program) (target : Label) :
    (buildLabelShapeIndex program).get? target = program.labelShape? target := by
  simpa [buildLabelShapeIndex, Program.labelShape?, Program.findBlock?] using
    buildLabelShapeIndexFrom_get? program.blocks
      ({} : LabelShapeIndex) target

end Program

namespace Terminator

def targets : Terminator → List Label
  | .fallthrough next => [next]
  | .jump target => [target]
  | .jumpi target next => [target, next]
  | .returnDispatch _returnCount sites => sites.map ReturnSite.target
  | .halt _ => []
  | .invalid => []

def definedLabels : Terminator → List Label
  | .returnDispatch _returnCount sites => sites.map ReturnSite.caseLabel
  | _ => []

def targetsHaveShapeWith?
    (labelShape? : Label → Option Shape) (shape : Shape) :
    List ReturnSite → Bool
  | [] => true
  | site :: rest =>
      match labelShape? site.target with
      | none => false
      | some targetShape =>
          shape.compatible targetShape &&
            targetsHaveShapeWith? labelShape? shape rest

def targetsHaveShape? (program : Program) (shape : Shape) :
    List ReturnSite → Bool :=
  targetsHaveShapeWith? program.labelShape? shape

def typeWith? (labelShape? : Label → Option Shape)
    (shape : Shape) : Terminator → Option Unit
  | .fallthrough next => do
      let targetShape ← labelShape? next
      if shape.compatible targetShape then some () else none
  | .jump target => do
      let targetShape ← labelShape? target
      if shape.compatible targetShape then some () else none
  | .jumpi target next => do
      let targetShape ← labelShape? target
      let fallthroughShape ← labelShape? next
      match shape.slots with
      | _condition :: rest =>
          let restShape := { shape with slots := rest }
          if restShape.compatible targetShape &&
              restShape.compatible fallthroughShape then
            some ()
          else
            none
      | _ => none
  | .returnDispatch returnCount sites => do
      let depth ← shape.returnTokenDepth?
      if sites.isEmpty then
        none
      else if depth = returnCount &&
          targetsHaveShapeWith? labelShape? (shape.erase depth) sites then
        some ()
      else
        none
  | .halt kind =>
      if kind.argCount ≤ shape.length then some () else none
  | .invalid => some ()

attribute [simp] targetsHaveShapeWith? typeWith?

def type? (program : Program) (shape : Shape) : Terminator → Option Unit :=
  typeWith? program.labelShape? shape

def targetsHaveShapeIndexed? (index : Program.LabelShapeIndex)
    (shape : Shape) : List ReturnSite → Bool :=
  targetsHaveShapeWith? index.get? shape

def typeIndexed? (index : Program.LabelShapeIndex)
    (shape : Shape) : Terminator → Option Unit :=
  typeWith? index.get? shape

theorem targetsHaveShapeIndexed_eq (program : Program) (shape : Shape)
    (sites : List ReturnSite) :
    targetsHaveShapeIndexed? program.buildLabelShapeIndex shape sites =
      targetsHaveShape? program shape sites := by
  induction sites with
  | nil => rfl
  | cons site rest ih =>
      have hRest :
          targetsHaveShapeWith? program.buildLabelShapeIndex.get? shape rest =
            targetsHaveShapeWith? program.labelShape? shape rest := by
        simpa [targetsHaveShapeIndexed?, targetsHaveShape?] using ih
      simp only [targetsHaveShapeIndexed?, targetsHaveShape?,
        targetsHaveShapeWith?]
      rw [Program.buildLabelShapeIndex_get?, hRest]

@[simp] theorem targetsHaveShapeWith_index_eq (program : Program)
    (shape : Shape) (sites : List ReturnSite) :
    targetsHaveShapeWith? program.buildLabelShapeIndex.get? shape sites =
      targetsHaveShapeWith? program.labelShape? shape sites := by
  simpa [targetsHaveShapeIndexed?, targetsHaveShape?] using
    targetsHaveShapeIndexed_eq program shape sites

theorem typeIndexed_eq (program : Program) (shape : Shape)
    (term : Terminator) :
    typeIndexed? program.buildLabelShapeIndex shape term =
      type? program shape term := by
  cases term <;>
    simp only [typeIndexed?, type?, typeWith?,
      Program.buildLabelShapeIndex_get?, targetsHaveShapeWith_index_eq]

@[simp] theorem type?_halt_eq_some_iff
    {program : Program} {shape : Shape} {kind : Assembly.HaltKind} :
    type? program shape (.halt kind) = some () ↔
      kind.argCount ≤ shape.length := by
  simp [type?, typeWith?]

@[simp] theorem type?_halt_eq_none_iff
    {program : Program} {shape : Shape} {kind : Assembly.HaltKind} :
    type? program shape (.halt kind) = none ↔
      shape.length < kind.argCount := by
  simp [type?, typeWith?, Nat.not_le]

@[simp] theorem type?_halt_stop_empty
    {program : Program} :
    type? program (Shape.closed []) (.halt .stop) = some () := by
  simp [type?, typeWith?, Assembly.HaltKind.argCount, Shape.length,
    Shape.closed]

@[simp] theorem type?_halt_return_empty
    {program : Program} :
    type? program (Shape.closed []) (.halt .return) = none := by
  simp [type?, typeWith?, Assembly.HaltKind.argCount, Shape.length,
    Shape.closed]

@[simp] theorem type?_halt_revert_empty
    {program : Program} :
    type? program (Shape.closed []) (.halt .revert) = none := by
  simp [type?, typeWith?, Assembly.HaltKind.argCount, Shape.length,
    Shape.closed]

@[simp] theorem type?_halt_selfdestruct_empty
    {program : Program} :
    type? program (Shape.closed []) (.halt .selfdestruct) = none := by
  simp [type?, typeWith?, Assembly.HaltKind.argCount, Shape.length,
    Shape.closed]

end Terminator

namespace Block

def WellTyped (program : Program) (block : Block) : Prop :=
  bodyType? block.body block.input = some block.output ∧
    block.term.type? program block.output = some ()

def wellTypedIndexed? (index : Program.LabelShapeIndex)
    (block : Block) : Bool :=
  decide (bodyType? block.body block.input = some block.output) &&
    decide (block.term.typeIndexed? index block.output = some ())

@[simp] theorem wellTypedIndexed?_eq_true_iff
    (program : Program) (block : Block) :
    wellTypedIndexed? program.buildLabelShapeIndex block = true ↔
      block.WellTyped program := by
  simp [wellTypedIndexed?, WellTyped, Terminator.typeIndexed_eq]

theorem halt_argCount_le_of_wellTyped
    {program : Program} {block : Block} {kind : Assembly.HaltKind}
    (hTyped : block.WellTyped program)
    (hTerm : block.term = .halt kind) :
    kind.argCount ≤ block.output.length := by
  have hTermType := hTyped.2
  rw [hTerm] at hTermType
  exact Terminator.type?_halt_eq_some_iff.mp hTermType

end Block

namespace Program

def LabelsUnique (program : Program) : Prop :=
  program.blocks.Pairwise (fun left right => left.label ≠ right.label)

theorem findBlock?_eq_some_of_mem
    {program : Program} {block : Block}
    (hUnique : program.LabelsUnique)
    (hMem : block ∈ program.blocks) :
    program.findBlock? block.label = some block := by
  unfold findBlock?
  unfold LabelsUnique at hUnique
  have aux :
      ∀ blocks : List Block,
        blocks.Pairwise (fun left right => left.label ≠ right.label) →
        ∀ candidate : Block, candidate ∈ blocks →
          blocks.find? (fun current => current.label == candidate.label) =
            some candidate := by
    intro blocks hPairwise candidate hMember
    induction blocks with
    | nil =>
        simp at hMember
    | cons head tail ih =>
        rw [List.pairwise_cons] at hPairwise
        simp only [List.mem_cons] at hMember
        cases hMember with
        | inl hHead =>
            subst head
            simp
        | inr hTail =>
            have hNe : head.label ≠ candidate.label :=
              hPairwise.1 candidate hTail
            rw [List.find?_cons, beq_false_of_ne hNe]
            exact ih hPairwise.2 hTail
  exact aux program.blocks hUnique block hMem

def EmittedLabels (program : Program) : List Label :=
  program.blocks.flatMap fun block =>
    block.label :: block.term.definedLabels

def EmittedLabelsUnique (program : Program) : Prop :=
  program.EmittedLabels.Nodup

def AllBlocksTyped (program : Program) : Prop :=
  program.blocks.Forall (fun block => block.WellTyped program)

def WellTyped (program : Program) : Prop :=
  program.LabelsUnique ∧ program.AllBlocksTyped ∧
    program.findBlock? program.entry ≠ none ∧ program.EmittedLabelsUnique

instance labelsUniqueDecidable (program : Program) :
    Decidable program.LabelsUnique := by
  unfold LabelsUnique
  infer_instance

instance blockWellTypedDecidable (program : Program) (block : Block) :
    Decidable (block.WellTyped program) := by
  unfold Block.WellTyped
  infer_instance

instance allBlocksTypedDecidable (program : Program) :
    Decidable program.AllBlocksTyped := by
  unfold AllBlocksTyped
  infer_instance

instance emittedLabelsUniqueDecidable (program : Program) :
    Decidable program.EmittedLabelsUnique := by
  unfold EmittedLabelsUnique
  infer_instance

instance wellTypedDecidable (program : Program) :
    Decidable program.WellTyped := by
  unfold WellTyped
  infer_instance

def allBlocksTypedIndexed? (program : Program)
    (index : LabelShapeIndex) : Bool :=
  program.blocks.all (Block.wellTypedIndexed? index)

@[simp] theorem allBlocksTypedIndexed?_eq_true_iff (program : Program) :
    allBlocksTypedIndexed? program program.buildLabelShapeIndex = true ↔
      program.AllBlocksTyped := by
  simp [allBlocksTypedIndexed?, AllBlocksTyped,
    List.forall_iff_forall_mem]

@[simp] theorem blockLabels_nodup_iff (program : Program) :
    (program.blocks.map Block.label).Nodup ↔ program.LabelsUnique := by
  unfold List.Nodup LabelsUnique
  rw [List.pairwise_map]

def wellTypedIndexed? (program : Program) : Bool :=
  let index := program.buildLabelShapeIndex
  Assembly.LabelList.unique? (program.blocks.map Block.label) &&
    allBlocksTypedIndexed? program index &&
    decide (program.findBlock? program.entry ≠ none) &&
    Assembly.LabelList.unique? program.EmittedLabels

@[simp] theorem wellTypedIndexed?_eq_true_iff (program : Program) :
    program.wellTypedIndexed? = true ↔ program.WellTyped := by
  simp [wellTypedIndexed?, WellTyped]
  aesop

theorem wellTyped_of_indexed_check {program : Program}
    (hCheck : program.wellTypedIndexed? = true) :
    program.WellTyped :=
  (wellTypedIndexed?_eq_true_iff program).mp hCheck

def wellTyped? (program : Program) : Bool :=
  decide program.WellTyped

theorem wellTyped_of_check {program : Program}
    (hCheck : program.wellTyped? = true) :
    program.WellTyped := by
  simpa [wellTyped?] using hCheck

theorem wellTyped_allBlocksTyped {program : Program}
    (h : program.WellTyped) :
    program.AllBlocksTyped :=
  h.2.1

theorem wellTyped_emittedLabelsUnique {program : Program}
    (h : program.WellTyped) :
    program.EmittedLabelsUnique :=
  h.2.2.2

end Program

end TypedCfg
end EvmCompiler
