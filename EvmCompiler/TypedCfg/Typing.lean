import EvmCompiler.TypedCfg.Syntax
import EvmCompiler.Assembly.PrimSemantics

namespace EvmCompiler
namespace TypedCfg

namespace Instr

def type? (instr : Instr) (shape : Shape) : Option Shape :=
  match instr with
  | .push value =>
      some { shape with slots := .literal value :: shape.slots }
  | .returnToken _value =>
      some { shape with slots := .returnToken :: shape.slots }
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
  | .relabel target =>
      if shape.relabelCompatible target then some target else none
  | .unwind target =>
      Shape.unwindTo target shape

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
  | _ :: rest => returnTokenDepthList? rest |>.map (· + 1)

def returnTokenDepth? (shape : Shape) : Option Nat :=
  returnTokenDepthList? shape.slots

end Shape

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

def targetsHaveShape? (program : Program) (shape : Shape) :
    List ReturnSite → Bool
  | [] => true
  | site :: rest =>
      match program.labelShape? site.target with
      | none => false
      | some targetShape =>
          shape.compatible targetShape &&
            targetsHaveShape? program shape rest

def type? (program : Program) (shape : Shape) : Terminator → Option Unit
  | .fallthrough next => do
      let targetShape ← program.labelShape? next
      if shape.compatible targetShape then some () else none
  | .jump target => do
      let targetShape ← program.labelShape? target
      if shape.compatible targetShape then some () else none
  | .jumpi target next => do
      let targetShape ← program.labelShape? target
      let fallthroughShape ← program.labelShape? next
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
          targetsHaveShape? program (shape.erase depth) sites then
        some ()
      else
        none
  | .halt _ => some ()
  | .invalid => some ()

end Terminator

namespace Block

def WellTyped (program : Program) (block : Block) : Prop :=
  bodyType? block.body block.input = some block.output ∧
    block.term.type? program block.output = some ()

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
