import EvmCompiler.TypedCfg.Typing
import EvmCompiler.Assembly.Assembler

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressRelation

abbrev Resolver := Label -> Option Nat

def TokensUnique : List ReturnSite -> Prop
  | [] => True
  | site :: rest =>
      (forall other, other ∈ rest -> site.token ≠ other.token) ∧
        TokensUnique rest

def TargetsUnique : List ReturnSite -> Prop
  | [] => True
  | site :: rest =>
      (forall other, other ∈ rest -> site.target ≠ other.target) ∧
        TargetsUnique rest

def tokensUnique? : List ReturnSite -> Bool
  | [] => true
  | site :: rest =>
      rest.all (fun other => decide (site.token ≠ other.token)) &&
        tokensUnique? rest

def targetsUnique? : List ReturnSite -> Bool
  | [] => true
  | site :: rest =>
      rest.all (fun other => decide (site.target ≠ other.target)) &&
        targetsUnique? rest

theorem tokensUnique?_eq_true_iff (sites : List ReturnSite) :
    tokensUnique? sites = true ↔ TokensUnique sites := by
  induction sites with
  | nil => simp [tokensUnique?, TokensUnique]
  | cons site rest ih =>
      simp [tokensUnique?, TokensUnique, ih, List.all_eq_true]

theorem targetsUnique?_eq_true_iff (sites : List ReturnSite) :
    targetsUnique? sites = true ↔ TargetsUnique sites := by
  induction sites with
  | nil => simp [targetsUnique?, TargetsUnique]
  | cons site rest ih =>
      simp [targetsUnique?, TargetsUnique, ih, List.all_eq_true]

theorem TokensUnique.eq_of_mem
    {sites : List ReturnSite} (hUnique : TokensUnique sites)
    {left right : ReturnSite}
    (hLeft : left ∈ sites) (hRight : right ∈ sites)
    (hToken : left.token = right.token) : left = right := by
  induction sites with
  | nil => simp at hLeft
  | cons head rest ih =>
      simp only [List.mem_cons] at hLeft hRight
      rcases hUnique with ⟨hFresh, hRest⟩
      rcases hLeft with rfl | hLeft <;> rcases hRight with rfl | hRight
      · rfl
      · exact False.elim ((hFresh right hRight) hToken)
      · exact False.elim ((hFresh left hLeft) hToken.symm)
      · exact ih hRest hLeft hRight

theorem TargetsUnique.eq_of_mem
    {sites : List ReturnSite} (hUnique : TargetsUnique sites)
    {left right : ReturnSite}
    (hLeft : left ∈ sites) (hRight : right ∈ sites)
    (hTarget : left.target = right.target) : left = right := by
  induction sites with
  | nil => simp at hLeft
  | cons head rest ih =>
      simp only [List.mem_cons] at hLeft hRight
      rcases hUnique with ⟨hFresh, hRest⟩
      rcases hLeft with rfl | hLeft <;> rcases hRight with rfl | hRight
      · rfl
      · exact False.elim ((hFresh right hRight) hTarget)
      · exact False.elim ((hFresh left hLeft) hTarget.symm)
      · exact ih hRest hLeft hRight

def AddressRel (resolve : Resolver) (sites : List ReturnSite)
    (target source : Word) : Prop :=
  exists site, site ∈ sites ∧
    source = site.token ∧
    exists pc, resolve site.target = some pc ∧
      target = EvmYul.UInt256.ofNat pc

def SlotWordRel (resolve : Resolver) (sites : List ReturnSite) :
    Slot -> Word -> Word -> Prop
  | .returnToken, target, source =>
      AddressRel resolve sites target source
  | .returnPC _, target, source =>
      AddressRel resolve sites target source
  | _, target, source => target = source

def ClosedStackRel (resolve : Resolver) (sites : List ReturnSite) :
    List Slot -> List Word -> List Word -> Prop
  | [], target, source => target = [] ∧ source = []
  | slot :: slots, targetValue :: targetRest,
      sourceValue :: sourceRest =>
      SlotWordRel resolve sites slot targetValue sourceValue ∧
        ClosedStackRel resolve sites slots targetRest sourceRest
  | _ :: _, _, _ => False

def TailRel (resolve : Resolver) (sites : List ReturnSite) :
    FrameTail -> List Word -> List Word -> Prop
  | .closed, target, source => target = [] ∧ source = []
  | .caller, target, source =>
      exists hiddenSlots, ClosedStackRel resolve sites hiddenSlots target source

def StackRel (resolve : Resolver) (sites : List ReturnSite) :
    List Slot -> FrameTail -> List Word -> List Word -> Prop
  | [], .closed, target, source => target = [] ∧ source = []
  | [], .caller, target, source =>
      exists hiddenSlots, ClosedStackRel resolve sites hiddenSlots target source
  | slot :: slots, tail, targetValue :: targetRest,
      sourceValue :: sourceRest =>
      SlotWordRel resolve sites slot targetValue sourceValue ∧
        StackRel resolve sites slots tail targetRest sourceRest
  | _ :: _, _, _, _ => False

def ShapeStackRel (resolve : Resolver) (sites : List ReturnSite)
    (shape : Shape) (target source : List Word) : Prop :=
  StackRel resolve sites shape.slots shape.tail target source

def RuntimeRel (resolve : Resolver) (sites : List ReturnSite)
    (shape : Shape) (target source : Assembly.EVMState) : Prop :=
  target.toSharedState = source.toSharedState ∧
    ShapeStackRel resolve sites shape target.stack source.stack

theorem runtimeRel_left_of_sameRuntimeData
    {resolve : Resolver} {sites : List ReturnSite} {shape : Shape}
    {left middle source : Assembly.EVMState}
    (hSame : Assembly.SameRuntimeData left middle)
    (hRel : RuntimeRel resolve sites shape middle source) :
    RuntimeRel resolve sites shape left source := by
  constructor
  · exact
      (Assembly.SameRuntimeData.shared_eq hSame).trans hRel.1
  · rw [Assembly.SameRuntimeData.stack_eq hSame]
    exact hRel.2

theorem runtimeRel_incrPC_left
    {resolve : Resolver} {sites : List ReturnSite} {shape : Shape}
    {target source : Assembly.EVMState}
    (hRel : RuntimeRel resolve sites shape target source) :
    RuntimeRel resolve sites shape target.incrPC source := by
  exact ⟨by simpa using hRel.1, by simpa using hRel.2⟩

def PlainSlot : Slot -> Prop
  | .returnToken | .returnPC _ => False
  | _ => True

def ReturnSlot : Slot -> Prop
  | .returnToken | .returnPC _ => True
  | _ => False

def SameSlotClass (input output : Slot) : Prop :=
  (ReturnSlot input ∧ ReturnSlot output) ∨
    (PlainSlot input ∧ PlainSlot output)

def SlotsClassRel : List Slot → List Slot → Prop
  | [], [] => True
  | input :: inputs, output :: outputs =>
      SameSlotClass input output ∧ SlotsClassRel inputs outputs
  | _, _ => False

def plainSlot? : Slot → Bool
  | .returnToken | .returnPC _ => false
  | _ => true

def returnSlot? : Slot → Bool
  | .returnToken | .returnPC _ => true
  | _ => false

def plainSlots? (slots : List Slot) : Bool :=
  slots.all plainSlot?

def slotsClassRel? : List Slot → List Slot → Bool
  | [], [] => true
  | input :: inputs, output :: outputs =>
      (returnSlot? input == returnSlot? output) &&
        slotsClassRel? inputs outputs
  | _, _ => false

theorem plainSlot_of_check
    {slot : Slot} (hCheck : plainSlot? slot = true) :
    PlainSlot slot := by
  cases slot <;> simp [plainSlot?, PlainSlot] at hCheck ⊢

theorem returnSlot_of_check
    {slot : Slot} (hCheck : returnSlot? slot = true) :
    ReturnSlot slot := by
  cases slot <;> simp [returnSlot?, ReturnSlot] at hCheck ⊢

theorem plainSlot_of_returnSlot_check_false
    {slot : Slot} (hCheck : returnSlot? slot = false) :
    PlainSlot slot := by
  cases slot <;> simp [returnSlot?, PlainSlot] at hCheck ⊢

theorem slotsClassRel_of_check
    {input output : List Slot}
    (hCheck : slotsClassRel? input output = true) :
    SlotsClassRel input output := by
  induction input generalizing output with
  | nil =>
      cases output <;> simp [slotsClassRel?, SlotsClassRel] at hCheck ⊢
  | cons input inputs ih =>
      cases output with
      | nil => simp [slotsClassRel?] at hCheck
      | cons output outputs =>
          simp only [slotsClassRel?, Bool.and_eq_true] at hCheck
          constructor
          · have hClass := hCheck.1
            cases hInput : returnSlot? input <;>
              cases hOutput : returnSlot? output <;>
              simp [hInput, hOutput] at hClass
            · exact Or.inr
                ⟨plainSlot_of_returnSlot_check_false hInput,
                  plainSlot_of_returnSlot_check_false hOutput⟩
            · exact Or.inl
                ⟨returnSlot_of_check hInput,
                  returnSlot_of_check hOutput⟩
          · exact ih hCheck.2

theorem returnSlot_get_of_returnTokenDepthList?_eq_some
    {slots : List Slot} {depth : Nat}
    (hDepth : Shape.returnTokenDepthList? slots = some depth) :
    ∃ slot, slots[depth]? = some slot ∧ ReturnSlot slot := by
  induction slots generalizing depth with
  | nil =>
      simp [Shape.returnTokenDepthList?] at hDepth
  | cons head rest ih =>
      cases head <;>
        simp only [Shape.returnTokenDepthList?] at hDepth
      case returnToken =>
        simp at hDepth
        subst depth
        exact ⟨.returnToken, by simp [ReturnSlot]⟩
      case returnPC site =>
        simp at hDepth
        subst depth
        exact ⟨.returnPC site, by simp [ReturnSlot]⟩
      all_goals
        cases hRest : Shape.returnTokenDepthList? rest with
        | none =>
            simp [hRest] at hDepth
        | some restDepth =>
          simp [hRest] at hDepth
          subst depth
          obtain ⟨slot, hGet, hReturn⟩ := ih hRest
          exact ⟨slot, by simpa using hGet, hReturn⟩

theorem returnSlot_get_of_returnTokenDepth?_eq_some
    {shape : Shape} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    ∃ slot, shape.slots[depth]? = some slot ∧ ReturnSlot slot :=
  returnSlot_get_of_returnTokenDepthList?_eq_some hDepth

def PlainSlots (slots : List Slot) : Prop :=
  forall slot, slot ∈ slots -> PlainSlot slot

theorem plainSlots_of_check
    {slots : List Slot} (hCheck : plainSlots? slots = true) :
    PlainSlots slots := by
  intro slot hMem
  apply plainSlot_of_check
  exact (List.all_eq_true.mp hCheck) slot hMem

theorem plainSlots_take_of_returnTokenDepthList?_eq_some
    {slots : List Slot} {depth : Nat}
    (hDepth : Shape.returnTokenDepthList? slots = some depth) :
    PlainSlots (slots.take depth) := by
  induction slots generalizing depth with
  | nil =>
      simp [Shape.returnTokenDepthList?] at hDepth
  | cons head rest ih =>
      cases head <;>
        simp only [Shape.returnTokenDepthList?] at hDepth
      case returnToken =>
        simp at hDepth
        subst depth
        simp [PlainSlots]
      case returnPC =>
        simp at hDepth
        subst depth
        simp [PlainSlots]
      all_goals
        cases hRest : Shape.returnTokenDepthList? rest with
        | none =>
            simp [hRest] at hDepth
        | some restDepth =>
          simp [hRest] at hDepth
          subst depth
          intro slot hMem
          simp at hMem
          rcases hMem with rfl | hMem
          · trivial
          · exact ih hRest slot hMem

theorem plainSlots_take_of_returnTokenDepth?_eq_some
    {shape : Shape} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    PlainSlots (shape.slots.take depth) := by
  exact plainSlots_take_of_returnTokenDepthList?_eq_some hDepth

theorem plainSlots_drop
    {slots : List Slot} (hPlain : PlainSlots slots) (count : Nat) :
    PlainSlots (slots.drop count) := by
  intro slot hMem
  exact hPlain slot (List.mem_of_mem_drop hMem)

theorem plainSlots_replicate_word_append
    {slots : List Slot} (hPlain : PlainSlots slots) (count : Nat) :
    PlainSlots (List.replicate count .word ++ slots) := by
  intro slot hMem
  rcases List.mem_append.mp hMem with hWord | hRest
  · have hSlot : slot = .word := by
      simpa using List.eq_of_mem_replicate hWord
    subst slot
    trivial
  · exact hPlain slot hRest

theorem plainSlots_pushWords
    {shape : Shape} (hPlain : PlainSlots shape.slots) (count : Nat) :
    PlainSlots (Shape.pushWords count shape).slots := by
  exact plainSlots_replicate_word_append hPlain count

theorem plainSlots_pop
    {shape : Shape} (hPlain : PlainSlots shape.slots) (count : Nat) :
    PlainSlots (Shape.pop count shape).slots := by
  exact plainSlots_drop hPlain count

theorem slotWordRel_eq_of_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {slot : Slot} {target source : Word}
    (hPlain : PlainSlot slot)
    (hRel : SlotWordRel resolve sites slot target source) :
    target = source := by
  cases slot <;>
    simp [PlainSlot, SlotWordRel] at hPlain hRel ⊢ <;>
    assumption

theorem slotWordRel_retype_return
    {resolve : Resolver} {sites : List ReturnSite}
    {input output : Slot} {target source : Word}
    (hInput : ReturnSlot input)
    (hOutput : ReturnSlot output)
    (hRel : SlotWordRel resolve sites input target source) :
    SlotWordRel resolve sites output target source := by
  cases input <;> cases output <;>
    simp [ReturnSlot, SlotWordRel] at hInput hOutput hRel ⊢ <;>
    assumption

theorem slotWordRel_retype_class
    {resolve : Resolver} {sites : List ReturnSite}
    {input output : Slot} {target source : Word}
    (hClass : SameSlotClass input output)
    (hRel : SlotWordRel resolve sites input target source) :
    SlotWordRel resolve sites output target source := by
  rcases hClass with ⟨hInput, hOutput⟩ | ⟨hInput, hOutput⟩
  · exact slotWordRel_retype_return hInput hOutput hRel
  · have hEq := slotWordRel_eq_of_plain hInput hRel
    cases output <;>
      simp [PlainSlot, SlotWordRel] at hOutput ⊢ <;>
      exact hEq

theorem closedStackRel_lengths
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {target source : List Word}
    (hRel : ClosedStackRel resolve sites slots target source) :
    target.length = slots.length ∧ source.length = slots.length := by
  induction slots generalizing target source with
  | nil =>
      rcases hRel with ⟨rfl, rfl⟩
      simp
  | cons slot rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              rcases ih hRel.2 with ⟨hTarget, hSource⟩
              simp [hTarget, hSource]

theorem closedStackRel_eq_of_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {target source : List Word}
    (hPlain : PlainSlots slots)
    (hRel : ClosedStackRel resolve sites slots target source) :
    target = source := by
  induction slots generalizing target source with
  | nil => exact hRel.1.trans hRel.2.symm
  | cons slot rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              have hHeadPlain : PlainSlot slot := hPlain slot (by simp)
              have hRestPlain : PlainSlots rest := by
                intro candidate hMem
                exact hPlain candidate (by simp [hMem])
              rw [slotWordRel_eq_of_plain hHeadPlain hRel.1]
              rw [ih hRestPlain hRel.2]

theorem closedStackRel_refl_of_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {values : List Word}
    (hPlain : PlainSlots slots)
    (hLength : values.length = slots.length) :
    ClosedStackRel resolve sites slots values values := by
  induction slots generalizing values with
  | nil =>
      have hValues : values = [] := List.eq_nil_of_length_eq_zero hLength
      subst values
      simp [ClosedStackRel]
  | cons slot rest ih =>
      cases values with
      | nil => simp at hLength
      | cons value values =>
          have hHeadPlain : PlainSlot slot := hPlain slot (by simp)
          have hRestPlain : PlainSlots rest := by
            intro candidate hMem
            exact hPlain candidate (by simp [hMem])
          have hRestLength : values.length = rest.length := by
            simpa using hLength
          constructor
          · cases slot <;>
              simp [PlainSlot, SlotWordRel] at hHeadPlain ⊢
          · exact ih hRestPlain hRestLength

theorem closedStackRel_refl_words
    (resolve : Resolver) (sites : List ReturnSite)
    (values : List Word) :
    ClosedStackRel resolve sites
      (List.replicate values.length .word) values values := by
  apply closedStackRel_refl_of_plain
  · intro slot hSlot
    have hWord : slot = .word := by
      simpa using
        (List.eq_of_mem_replicate hSlot)
    subst slot
    trivial
  · simp

theorem stackRel_caller_nil_refl
    (resolve : Resolver) (sites : List ReturnSite)
    (values : List Word) :
    StackRel resolve sites [] .caller values values :=
  ⟨List.replicate values.length .word,
    closedStackRel_refl_words resolve sites values⟩

theorem stackRel_lengths
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {target source : List Word}
    (hRel : StackRel resolve sites slots tail target source) :
    slots.length ≤ target.length ∧ slots.length ≤ source.length := by
  induction slots generalizing target source with
  | nil =>
      simp
  | cons slot rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              have hRest := ih hRel.2
              simpa using
                And.intro (Nat.succ_le_succ hRest.1)
                  (Nat.succ_le_succ hRest.2)

theorem stackRel_take_eq_of_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {target source : List Word} {count : Nat}
    (hBound : count ≤ slots.length)
    (hPlain : PlainSlots (slots.take count))
    (hRel : StackRel resolve sites slots tail target source) :
    target.take count = source.take count := by
  induction count generalizing slots target source with
  | zero =>
      simp
  | succ count ih =>
      cases slots with
      | nil => simp at hBound
      | cons slot rest =>
          cases target with
          | nil => cases hRel
          | cons targetHead targetRest =>
              cases source with
              | nil => cases hRel
              | cons sourceHead sourceRest =>
                  have hHeadPlain : PlainSlot slot :=
                    hPlain slot (by simp)
                  have hRestPlain : PlainSlots (rest.take count) := by
                    intro candidate hCandidate
                    exact hPlain candidate (by simp [hCandidate])
                  have hRestBound : count ≤ rest.length := by
                    simpa using hBound
                  have hHeadEq :=
                    slotWordRel_eq_of_plain hHeadPlain hRel.1
                  simp only [List.take_succ_cons]
                  rw [hHeadEq]
                  exact congrArg (sourceHead :: ·)
                    (ih hRestBound hRestPlain hRel.2)

theorem runtimeRel_stack_lengths
    {resolve : Resolver} {sites : List ReturnSite}
    {shape : Shape} {target source : Assembly.EVMState}
    (hRel : RuntimeRel resolve sites shape target source) :
    shape.length ≤ target.stack.length ∧
      shape.length ≤ source.stack.length := by
  simpa [Shape.length] using stackRel_lengths hRel.2

theorem runtimeRel_caller_nil_of_sameRuntimeData
    {resolve : Resolver} {sites : List ReturnSite}
    {target source : Assembly.EVMState}
    (hSame : Assembly.SameRuntimeData target source) :
    RuntimeRel resolve sites (Shape.caller []) target source := by
  constructor
  · exact Assembly.SameRuntimeData.shared_eq hSame
  · have hStack := Assembly.SameRuntimeData.stack_eq hSame
    rw [hStack]
    exact stackRel_caller_nil_refl resolve sites source.stack

theorem stackRel_split
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {target source : List Word}
    (hRel : StackRel resolve sites slots tail target source) :
    exists targetVisible targetHidden sourceVisible sourceHidden,
      target = targetVisible ++ targetHidden ∧
      source = sourceVisible ++ sourceHidden ∧
      ClosedStackRel resolve sites slots targetVisible sourceVisible ∧
      TailRel resolve sites tail targetHidden sourceHidden := by
  induction slots generalizing target source with
  | nil =>
      cases tail with
      | closed =>
          rcases hRel with ⟨rfl, rfl⟩
          exact ⟨[], [], [], [], by simp [ClosedStackRel, TailRel]⟩
      | caller =>
          exact
            ⟨[], target, [], source, by simp,
              by simp, by simp [ClosedStackRel], hRel⟩
  | cons slot rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              obtain
                ⟨targetVisible, targetHidden, sourceVisible, sourceHidden,
                  hTarget, hSource, hVisible, hTail⟩ := ih hRel.2
              exact
                ⟨targetHead :: targetVisible, targetHidden,
                  sourceHead :: sourceVisible, sourceHidden,
                  by simp [hTarget], by simp [hSource],
                  ⟨hRel.1, hVisible⟩, hTail⟩

theorem stackRel_split_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {target source : List Word}
    (hPlain : PlainSlots slots)
    (hRel : StackRel resolve sites slots tail target source) :
    exists visible targetHidden sourceHidden,
      target = visible ++ targetHidden ∧
      source = visible ++ sourceHidden ∧
      visible.length = slots.length ∧
      TailRel resolve sites tail targetHidden sourceHidden := by
  obtain
    ⟨targetVisible, targetHidden, sourceVisible, sourceHidden,
      hTarget, hSource, hVisible, hTail⟩ := stackRel_split hRel
  have hVisibleEq := closedStackRel_eq_of_plain hPlain hVisible
  subst sourceVisible
  have hLength := (closedStackRel_lengths hVisible).1
  exact ⟨targetVisible, targetHidden, sourceHidden,
    hTarget, hSource, hLength, hTail⟩

theorem stackRel_split_prefix_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {target source : List Word} {count : Nat}
    (hBound : count ≤ slots.length)
    (hPlain : PlainSlots (slots.take count))
    (hRel : StackRel resolve sites slots tail target source) :
    exists visible targetSuffix sourceSuffix,
      target = visible ++ targetSuffix ∧
      source = visible ++ sourceSuffix ∧
      visible.length = count ∧
      StackRel resolve sites (slots.drop count) tail
        targetSuffix sourceSuffix := by
  induction count generalizing slots target source with
  | zero =>
      exact ⟨[], target, source, by simp, by simp, rfl, by simpa using hRel⟩
  | succ count ih =>
      cases slots with
      | nil => simp at hBound
      | cons slot rest =>
          cases target with
          | nil => cases hRel
          | cons targetHead targetRest =>
              cases source with
              | nil => cases hRel
              | cons sourceHead sourceRest =>
                  have hHeadPlain : PlainSlot slot :=
                    hPlain slot (by simp)
                  have hRestPlain : PlainSlots (rest.take count) := by
                    intro candidate hMem
                    exact hPlain candidate (by simp [hMem])
                  have hHeadEq : targetHead = sourceHead :=
                    slotWordRel_eq_of_plain hHeadPlain hRel.1
                  obtain
                    ⟨visible, targetSuffix, sourceSuffix,
                      hTarget, hSource, hLength, hSuffix⟩ :=
                    ih (by simpa using hBound) hRestPlain hRel.2
                  subst sourceHead
                  exact
                    ⟨targetHead :: visible, targetSuffix, sourceSuffix,
                      by simp [hTarget], by simp [hSource],
                      by simp [hLength], by simpa using hSuffix⟩

theorem stackRel_of_closed_prefix_suffix
    {resolve : Resolver} {sites : List ReturnSite}
    {prefixSlots slots : List Slot} {tail : FrameTail}
    {targetPrefix targetSuffix sourcePrefix sourceSuffix : List Word}
    (hPrefix :
      ClosedStackRel resolve sites prefixSlots targetPrefix sourcePrefix)
    (hSuffix :
      StackRel resolve sites slots tail targetSuffix sourceSuffix) :
    StackRel resolve sites (prefixSlots ++ slots) tail
      (targetPrefix ++ targetSuffix) (sourcePrefix ++ sourceSuffix) := by
  induction prefixSlots generalizing targetPrefix sourcePrefix with
  | nil =>
      rcases hPrefix with ⟨rfl, rfl⟩
      simpa using hSuffix
  | cons slot rest ih =>
      cases targetPrefix with
      | nil => cases hPrefix
      | cons targetHead targetRest =>
          cases sourcePrefix with
          | nil => cases hPrefix
          | cons sourceHead sourceRest =>
              exact ⟨hPrefix.1, ih hPrefix.2⟩

theorem drop_eq_singleton_returnSlot_of_depth_bottom
    {slots : List Slot} {depth : Nat}
    (hDepth : Shape.returnTokenDepthList? slots = some depth)
    (hBottom : depth + 1 = slots.length) :
    ∃ slot, slots.drop depth = [slot] ∧ ReturnSlot slot := by
  induction slots generalizing depth with
  | nil =>
      simp [Shape.returnTokenDepthList?] at hDepth
  | cons head rest ih =>
      cases head <;>
        simp only [Shape.returnTokenDepthList?] at hDepth
      case returnToken =>
        simp at hDepth
        subst depth
        have hRestLength : rest.length = 0 := by
          simpa using hBottom
        have hRest : rest = [] :=
          List.eq_nil_of_length_eq_zero hRestLength
        subst rest
        exact ⟨.returnToken, by simp [ReturnSlot]⟩
      case returnPC site =>
        simp at hDepth
        subst depth
        have hRestLength : rest.length = 0 := by
          simpa using hBottom
        have hRest : rest = [] :=
          List.eq_nil_of_length_eq_zero hRestLength
        subst rest
        exact ⟨.returnPC site, by simp [ReturnSlot]⟩
      all_goals
        cases hRest : Shape.returnTokenDepthList? rest with
        | none =>
            simp [hRest] at hDepth
        | some restDepth =>
          simp [hRest] at hDepth
          subst depth
          have hRestBottom : restDepth + 1 = rest.length := by
            simpa [Nat.add_assoc] using hBottom
          simpa using ih hRest hRestBottom

theorem stackRel_retype_return_bottom
    {resolve : Resolver} {sites : List ReturnSite}
    {inputSlots outputSlots : List Slot} {tail : FrameTail}
    {target source : List Word} {depth : Nat}
    (hInputDepth :
      Shape.returnTokenDepthList? inputSlots = some depth)
    (hOutputDepth :
      Shape.returnTokenDepthList? outputSlots = some depth)
    (hInputBottom : depth + 1 = inputSlots.length)
    (hOutputBottom : depth + 1 = outputSlots.length)
    (hRel :
      StackRel resolve sites inputSlots tail target source) :
    StackRel resolve sites outputSlots tail target source := by
  have hInputPlain : PlainSlots (inputSlots.take depth) :=
    plainSlots_take_of_returnTokenDepthList?_eq_some hInputDepth
  have hOutputPlain : PlainSlots (outputSlots.take depth) :=
    plainSlots_take_of_returnTokenDepthList?_eq_some hOutputDepth
  have hBound : depth ≤ inputSlots.length := by omega
  obtain ⟨visible, targetSuffix, sourceSuffix,
      hTarget, hSource, hVisibleLength, hSuffix⟩ :=
    stackRel_split_prefix_plain hBound hInputPlain hRel
  obtain ⟨inputReturn, hInputDrop, hInputReturn⟩ :=
    drop_eq_singleton_returnSlot_of_depth_bottom
      hInputDepth hInputBottom
  obtain ⟨outputReturn, hOutputDrop, hOutputReturn⟩ :=
    drop_eq_singleton_returnSlot_of_depth_bottom
      hOutputDepth hOutputBottom
  rw [hInputDrop] at hSuffix
  cases targetSuffix with
  | nil => cases hSuffix
  | cons targetReturn targetTail =>
      cases sourceSuffix with
      | nil => cases hSuffix
      | cons sourceReturn sourceTail =>
          have hReturnRel :
              SlotWordRel resolve sites outputReturn
                targetReturn sourceReturn :=
            slotWordRel_retype_return
              hInputReturn hOutputReturn hSuffix.1
          have hOutputPrefixLength :
              visible.length = (outputSlots.take depth).length := by
            rw [hVisibleLength]
            simp [List.length_take]
            omega
          have hOutputPrefix :
              ClosedStackRel resolve sites (outputSlots.take depth)
                visible visible :=
            closedStackRel_refl_of_plain
              hOutputPlain hOutputPrefixLength
          have hOutputSuffix :
              StackRel resolve sites [outputReturn] tail
                (targetReturn :: targetTail)
                (sourceReturn :: sourceTail) :=
            ⟨hReturnRel, hSuffix.2⟩
          have hRebuilt :=
            stackRel_of_closed_prefix_suffix
              hOutputPrefix hOutputSuffix
          rw [hTarget, hSource]
          have hOutputSlots :
              outputSlots =
                outputSlots.take depth ++ [outputReturn] := by
            rw [← hOutputDrop]
            exact (List.take_append_drop depth outputSlots).symm
          rw [hOutputSlots]
          exact hRebuilt

theorem stackRel_retype_classes
    {resolve : Resolver} {sites : List ReturnSite}
    {inputSlots outputSlots : List Slot}
    {inputTail outputTail : FrameTail}
    {target source : List Word}
    (hClasses : SlotsClassRel inputSlots outputSlots)
    (hTail : outputTail = inputTail)
    (hRel :
      StackRel resolve sites inputSlots inputTail target source) :
    StackRel resolve sites outputSlots outputTail target source := by
  induction inputSlots generalizing
      outputSlots inputTail outputTail target source with
  | nil =>
      cases outputSlots with
      | nil => simpa [hTail] using hRel
      | cons output rest => cases hClasses
  | cons input inputs ih =>
      cases outputSlots with
      | nil => cases hClasses
      | cons output outputs =>
          cases target with
          | nil => cases hRel
          | cons targetHead targetRest =>
              cases source with
              | nil => cases hRel
              | cons sourceHead sourceRest =>
                  exact
                    ⟨slotWordRel_retype_class hClasses.1 hRel.1,
                      ih hClasses.2 hTail hRel.2⟩

theorem runtimeRel_retype_classes
    {resolve : Resolver} {sites : List ReturnSite}
    {input output : Shape}
    {target source : Assembly.EVMState}
    (hClasses : SlotsClassRel input.slots output.slots)
    (hTail : output.tail = input.tail)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  exact
    ⟨hRel.1,
      stackRel_retype_classes hClasses hTail hRel.2⟩

theorem runtimeRel_retype_return_bottom
    {resolve : Resolver} {sites : List ReturnSite}
    {input output : Shape} {target source : Assembly.EVMState}
    {depth : Nat}
    (hInputDepth : input.returnTokenDepth? = some depth)
    (hOutputDepth : output.returnTokenDepth? = some depth)
    (hInputBottom : depth + 1 = input.length)
    (hOutputBottom : depth + 1 = output.length)
    (hTail : output.tail = input.tail)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  constructor
  · exact hRel.1
  · change StackRel resolve sites output.slots output.tail
      target.stack source.stack
    rw [hTail]
    exact
      stackRel_retype_return_bottom
        hInputDepth hOutputDepth
        (by simpa [Shape.length] using hInputBottom)
        (by simpa [Shape.length] using hOutputBottom)
        hRel.2

theorem runtimeRel_retype_active_bottom
    {resolve : Resolver} {sites : List ReturnSite}
    {input output : Shape} {target source : Assembly.EVMState}
    {inputDepth outputDepth : Nat}
    (hInputDepth : input.returnTokenDepth? = some inputDepth)
    (hOutputDepth : output.returnTokenDepth? = some outputDepth)
    (hInputBottom : inputDepth + 1 = input.length)
    (hOutputBottom : outputDepth + 1 = output.length)
    (hLength : output.length = input.length)
    (hTail : output.tail = input.tail)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  have hDepth : outputDepth = inputDepth := by omega
  subst outputDepth
  exact
    runtimeRel_retype_return_bottom
      hInputDepth hOutputDepth hInputBottom hOutputBottom hTail hRel

theorem stackRel_of_closed_prefix_tail
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {targetVisible targetHidden sourceVisible sourceHidden : List Word}
    (hVisible :
      ClosedStackRel resolve sites slots targetVisible sourceVisible)
    (hTail : TailRel resolve sites tail targetHidden sourceHidden) :
    StackRel resolve sites slots tail
      (targetVisible ++ targetHidden) (sourceVisible ++ sourceHidden) := by
  induction slots generalizing targetVisible sourceVisible with
  | nil =>
      rcases hVisible with ⟨rfl, rfl⟩
      cases tail <;> simpa [TailRel, StackRel] using hTail
  | cons slot rest ih =>
      cases targetVisible with
      | nil => cases hVisible
      | cons targetHead targetRest =>
          cases sourceVisible with
          | nil => cases hVisible
          | cons sourceHead sourceRest =>
              exact ⟨hVisible.1, ih hVisible.2⟩

theorem stackRel_retype_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {inputSlots outputSlots : List Slot} {inputTail outputTail : FrameTail}
    {target source : List Word}
    (hInputPlain : PlainSlots inputSlots)
    (hOutputPlain : PlainSlots outputSlots)
    (hLength : outputSlots.length = inputSlots.length)
    (hTailEq : outputTail = inputTail)
    (hRel : StackRel resolve sites inputSlots inputTail target source) :
    StackRel resolve sites outputSlots outputTail target source := by
  obtain ⟨visible, targetHidden, sourceHidden,
      hTarget, hSource, hVisibleLength, hTail⟩ :=
    stackRel_split_plain hInputPlain hRel
  have hOutputLength : visible.length = outputSlots.length := by
    omega
  have hVisible :
      ClosedStackRel resolve sites outputSlots visible visible :=
    closedStackRel_refl_of_plain hOutputPlain hOutputLength
  have hRebuilt := stackRel_of_closed_prefix_tail hVisible hTail
  rw [← hTarget, ← hSource] at hRebuilt
  simpa [hTailEq] using hRebuilt

theorem runtimeRel_retype_plain
    {resolve : Resolver} {sites : List ReturnSite}
    {input output : Shape} {target source : Assembly.EVMState}
    (hInputPlain : PlainSlots input.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hLength : output.length = input.length)
    (hTailEq : output.tail = input.tail)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  constructor
  · exact hRel.1
  · apply stackRel_retype_plain hInputPlain hOutputPlain
    · simpa [Shape.length] using hLength
    · exact hTailEq
    · exact hRel.2

theorem runtimeRel_replaceStackAndIncrPC
    {resolve : Resolver} {sites : List ReturnSite}
    {inputShape outputShape : Shape}
    {target source : Assembly.EVMState} {targetStack sourceStack : List Word}
    {targetDelta sourceDelta : Nat}
    (hRel : RuntimeRel resolve sites inputShape target source)
    (hStack : ShapeStackRel resolve sites outputShape targetStack sourceStack) :
    RuntimeRel resolve sites outputShape
      (target.replaceStackAndIncrPC targetStack (pcΔ := targetDelta))
      (source.replaceStackAndIncrPC sourceStack (pcΔ := sourceDelta)) := by
  constructor
  · simpa [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.1
  · exact hStack

theorem address_of_site
    {resolve : Resolver} {sites : List ReturnSite} {site : ReturnSite}
    {pc : Nat}
    (hSite : site ∈ sites) (hResolve : resolve site.target = some pc) :
    AddressRel resolve sites (EvmYul.UInt256.ofNat pc) site.token := by
  exact ⟨site, hSite, rfl, pc, hResolve, rfl⟩

theorem address_of_site_filter
    {resolve : Resolver} {sites : List ReturnSite} {site : ReturnSite}
    {pc : Nat}
    (hSite : site ∈ sites) (hResolve : resolve site.target = some pc) :
    AddressRel resolve
        (sites.filter fun candidate => candidate.token.toNat = site.token.toNat)
        (EvmYul.UInt256.ofNat pc) site.token := by
  apply address_of_site
  · simp [hSite]
  · exact hResolve

theorem address_target_of_unique
    {resolve : Resolver} {sites : List ReturnSite}
    {selected : ReturnSite} {target source : Word}
    (hUnique : TokensUnique sites)
    (hSelected : selected ∈ sites)
    (hSelectedToken : selected.token = source)
    (hAddress : AddressRel resolve sites target source) :
    exists pc, resolve selected.target = some pc ∧
      target = EvmYul.UInt256.ofNat pc := by
  rcases hAddress with
    ⟨actual, hActual, hSource, pc, hResolve, hTarget⟩
  have hToken : actual.token = selected.token := by
    rw [← hSource, ← hSelectedToken]
  have hSiteEq := hUnique.eq_of_mem hActual hSelected hToken
  subst actual
  exact ⟨pc, hResolve, hTarget⟩

theorem shapeStackRel_push_returnPC
    {resolve : Resolver} {sites : List ReturnSite} {site : ReturnSite}
    {pc : Nat} {shape : Shape} {target source : List Word}
    (hSite : site ∈ sites)
    (hResolve : resolve site.target = some pc)
    (hRel : ShapeStackRel resolve sites shape target source) :
    ShapeStackRel resolve sites
      { shape with slots := .returnPC site.token.toNat :: shape.slots }
      (EvmYul.UInt256.ofNat pc :: target) (site.token :: source) := by
  exact ⟨address_of_site hSite hResolve, hRel⟩

theorem runtimeRel_push_returnPC
    {resolve : Resolver} {sites : List ReturnSite} {site : ReturnSite}
    {pc : Nat} {shape : Shape} {target source : Assembly.EVMState}
    (hSite : site ∈ sites)
    (hResolve : resolve site.target = some pc)
    (hRel : RuntimeRel resolve sites shape target source) :
    RuntimeRel resolve sites
      { shape with slots := .returnPC site.token.toNat :: shape.slots }
      { target with stack := EvmYul.UInt256.ofNat pc :: target.stack }
      { source with stack := site.token :: source.stack } := by
  exact
    ⟨hRel.1,
      shapeStackRel_push_returnPC hSite hResolve hRel.2⟩

theorem shapeStackRel_pop
    {resolve : Resolver} {sites : List ReturnSite}
    {slot : Slot} {slots : List Slot} {tail : FrameTail}
    {targetValue sourceValue : Word} {target source : List Word}
    (hRel : StackRel resolve sites (slot :: slots) tail
      (targetValue :: target) (sourceValue :: source)) :
    StackRel resolve sites slots tail target source :=
  hRel.2

theorem stackRel_drop
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail}
    {target source : List Word} (count : Nat)
    (hBound : count ≤ slots.length)
    (hRel : StackRel resolve sites slots tail target source) :
    StackRel resolve sites (slots.drop count) tail
      (target.drop count) (source.drop count) := by
  induction count generalizing slots target source with
  | zero => simpa using hRel
  | succ count ih =>
      cases slots with
      | nil => simp at hBound
      | cons slot rest =>
          cases target with
          | nil => cases hRel
          | cons targetHead targetRest =>
              cases source with
              | nil => cases hRel
              | cons sourceHead sourceRest =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    ih (by simpa using hBound) hRel.2

theorem stackRel_get
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot : Slot} {targetValue sourceValue : Word}
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot)
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceValue) :
    SlotWordRel resolve sites slot targetValue sourceValue := by
  induction slots generalizing depth target source with
  | nil => simp at hSlot
  | cons head rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              cases depth with
              | zero =>
                  simp at hSlot hTarget hSource
                  subst slot
                  subst targetValue
                  subst sourceValue
                  exact hRel.1
              | succ depth =>
                  simp at hSlot hTarget hSource
                  exact ih hRel.2 hSlot hTarget hSource

theorem stackRel_get_exists
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot : Slot}
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot) :
    ∃ targetValue sourceValue,
      target[depth]? = some targetValue ∧
        source[depth]? = some sourceValue ∧
          SlotWordRel resolve sites slot targetValue sourceValue := by
  induction slots generalizing depth target source with
  | nil => simp at hSlot
  | cons head rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              cases depth with
              | zero =>
                  simp at hSlot
                  subst slot
                  exact
                    ⟨targetHead, sourceHead, by simp, by simp, hRel.1⟩
              | succ depth =>
                  simp at hSlot
                  obtain
                    ⟨targetValue, sourceValue,
                      hTarget, hSource, hValue⟩ :=
                    ih hRel.2 hSlot
                  exact
                    ⟨targetValue, sourceValue,
                      by simpa using hTarget,
                      by simpa using hSource, hValue⟩

theorem stackRel_set
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot newSlot : Slot}
    {targetValue sourceValue newTarget newSource : Word}
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot)
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceValue)
    (hNew : SlotWordRel resolve sites newSlot newTarget newSource) :
    StackRel resolve sites (slots.set depth newSlot) tail
      (target.set depth newTarget) (source.set depth newSource) := by
  induction slots generalizing depth target source with
  | nil => simp at hSlot
  | cons head rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              cases depth with
              | zero =>
                  simp
                  exact ⟨hNew, hRel.2⟩
              | succ depth =>
                  simp at hSlot hTarget hSource ⊢
                  exact
                    ⟨hRel.1,
                      ih hRel.2 hSlot hTarget hSource⟩

theorem stackRel_eraseIdx
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot : Slot}
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot) :
    StackRel resolve sites (slots.eraseIdx depth) tail
      (target.eraseIdx depth) (source.eraseIdx depth) := by
  induction slots generalizing depth target source with
  | nil => simp at hSlot
  | cons head rest ih =>
      cases target with
      | nil => cases hRel
      | cons targetHead targetRest =>
          cases source with
          | nil => cases hRel
          | cons sourceHead sourceRest =>
              cases depth with
              | zero =>
                  simp at hSlot
                  simp [List.eraseIdx]
                  exact hRel.2
              | succ depth =>
                  simp at hSlot
                  simp [List.eraseIdx]
                  exact ⟨hRel.1, ih hRel.2 hSlot⟩

theorem stackRel_dup
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot : Slot} {targetValue sourceValue : Word}
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot)
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceValue) :
    StackRel resolve sites (slot :: slots) tail
      (targetValue :: target) (sourceValue :: source) :=
  ⟨stackRel_get hRel hSlot hTarget hSource, hRel⟩

theorem stackRel_lift
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot : Slot} {targetValue sourceValue : Word}
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot)
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceValue) :
    StackRel resolve sites (slot :: slots.eraseIdx depth) tail
      (targetValue :: target.eraseIdx depth)
      (sourceValue :: source.eraseIdx depth) :=
  ⟨stackRel_get hRel hSlot hTarget hSource,
    stackRel_eraseIdx hRel hSlot⟩

theorem list_eq_take_get_drop
    {α : Type} {items : List α} {depth : Nat} {value : α}
    (hGet : items[depth]? = some value) :
    items = items.take depth ++ value :: items.drop (depth + 1) := by
  induction items generalizing depth with
  | nil => simp at hGet
  | cons head rest ih =>
      cases depth with
      | zero =>
          simp at hGet
          subst value
          simp
      | succ depth =>
          simp at hGet
          simpa [Nat.add_assoc] using congrArg (List.cons head) (ih hGet)

theorem eraseIdx_eq_take_drop_of_get?
    {α : Type} {items : List α} {depth : Nat} {value : α}
    (hGet : items[depth]? = some value) :
    items.eraseIdx depth = items.take depth ++ items.drop (depth + 1) := by
  induction items generalizing depth with
  | nil => simp at hGet
  | cons head rest ih =>
      cases depth with
      | zero => simp [List.eraseIdx]
      | succ depth =>
          simp at hGet
          simp [List.eraseIdx, ih hGet, Nat.add_assoc]

theorem returnToken_target_of_unique
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {targetValue sourceToken : Word}
    {selected : ReturnSite}
    (hUnique : TokensUnique sites)
    (hSelected : selected ∈ sites)
    (hSelectedToken : selected.token = sourceToken)
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some .returnToken)
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceToken) :
    exists pc, resolve selected.target = some pc ∧
      targetValue = EvmYul.UInt256.ofNat pc ∧
      StackRel resolve sites (slots.eraseIdx depth) tail
        (target.eraseIdx depth) (source.eraseIdx depth) := by
  have hAddress : AddressRel resolve sites targetValue sourceToken :=
    stackRel_get hRel hSlot hTarget hSource
  obtain ⟨pc, hResolve, hValue⟩ :=
    address_target_of_unique hUnique hSelected hSelectedToken hAddress
  exact ⟨pc, hResolve, hValue, stackRel_eraseIdx hRel hSlot⟩

theorem returnPC_target_of_unique
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {targetValue sourceToken : Word}
    {selected : ReturnSite}
    (hUnique : TokensUnique sites)
    (hSelected : selected ∈ sites)
    (hSelectedToken : selected.token = sourceToken)
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some (.returnPC sourceToken.toNat))
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceToken) :
    exists pc, resolve selected.target = some pc ∧
      targetValue = EvmYul.UInt256.ofNat pc ∧
      StackRel resolve sites (slots.eraseIdx depth) tail
        (target.eraseIdx depth) (source.eraseIdx depth) := by
  have hAddress : AddressRel resolve sites targetValue sourceToken :=
    stackRel_get hRel hSlot hTarget hSource
  obtain ⟨pc, hResolve, hValue⟩ :=
    address_target_of_unique hUnique hSelected hSelectedToken hAddress
  exact ⟨pc, hResolve, hValue, stackRel_eraseIdx hRel hSlot⟩

theorem returnSlot_target_of_unique
    {resolve : Resolver} {sites : List ReturnSite}
    {slots : List Slot} {tail : FrameTail} {target source : List Word}
    {depth : Nat} {slot : Slot} {targetValue sourceToken : Word}
    {selected : ReturnSite}
    (hUnique : TokensUnique sites)
    (hSelected : selected ∈ sites)
    (hSelectedToken : selected.token = sourceToken)
    (hRel : StackRel resolve sites slots tail target source)
    (hSlot : slots[depth]? = some slot)
    (hReturn : ReturnSlot slot)
    (hTarget : target[depth]? = some targetValue)
    (hSource : source[depth]? = some sourceToken) :
    exists pc, resolve selected.target = some pc ∧
      targetValue = EvmYul.UInt256.ofNat pc ∧
      StackRel resolve sites (slots.eraseIdx depth) tail
        (target.eraseIdx depth) (source.eraseIdx depth) := by
  have hAddress : AddressRel resolve sites targetValue sourceToken := by
    have hWord := stackRel_get hRel hSlot hTarget hSource
    cases slot <;>
      simp [ReturnSlot, SlotWordRel] at hReturn hWord ⊢
    all_goals exact hWord
  obtain ⟨pc, hResolve, hValue⟩ :=
    address_target_of_unique hUnique hSelected hSelectedToken hAddress
  exact
    ⟨pc, hResolve, hValue,
      stackRel_eraseIdx hRel hSlot⟩

theorem stackRel_swapTop
    {resolve : Resolver} {sites : List ReturnSite}
    {topSlot deepSlot : Slot} {slots : List Slot} {tail : FrameTail}
    {topTarget deepTarget topSource deepSource : Word}
    {target source : List Word} {depth : Nat}
    (hRel : StackRel resolve sites (topSlot :: slots) tail
      (topTarget :: target) (topSource :: source))
    (hSlot : slots[depth]? = some deepSlot)
    (hTarget : target[depth]? = some deepTarget)
    (hSource : source[depth]? = some deepSource) :
    StackRel resolve sites (deepSlot :: slots.set depth topSlot) tail
      (deepTarget :: target.set depth topTarget)
      (deepSource :: source.set depth topSource) := by
  exact
    ⟨stackRel_get hRel.2 hSlot hTarget hSource,
      stackRel_set hRel.2 hSlot hTarget hSource hRel.1⟩

theorem shapeStackRel_relabel
    {resolve : Resolver} {sites : List ReturnSite}
    {left right : Shape} {target source : List Word}
    (hSlots : left.slots = right.slots) (hTail : left.tail = right.tail)
    (hRel : ShapeStackRel resolve sites left target source) :
    ShapeStackRel resolve sites right target source := by
  cases left
  cases right
  simp only [ShapeStackRel] at hRel ⊢
  subst hSlots
  subst hTail
  exact hRel

end ReturnAddressRelation
end TypedCfg
end EvmCompiler
