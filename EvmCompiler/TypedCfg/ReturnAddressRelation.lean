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

def tokensUnique? : List ReturnSite -> Bool
  | [] => true
  | site :: rest =>
      rest.all (fun other => decide (site.token ≠ other.token)) &&
        tokensUnique? rest

theorem tokensUnique?_eq_true_iff (sites : List ReturnSite) :
    tokensUnique? sites = true ↔ TokensUnique sites := by
  induction sites with
  | nil => simp [tokensUnique?, TokensUnique]
  | cons site rest ih =>
      simp [tokensUnique?, TokensUnique, ih, List.all_eq_true]

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
  | .returnPC siteId, target, source =>
      AddressRel resolve
        (sites.filter fun site => site.token.toNat = siteId) target source
  | _, target, source => target = source

def ClosedStackRel (resolve : Resolver) (sites : List ReturnSite) :
    List Slot -> List Word -> List Word -> Prop
  | [], target, source => target = [] ∧ source = []
  | slot :: slots, targetValue :: targetRest,
      sourceValue :: sourceRest =>
      SlotWordRel resolve sites slot targetValue sourceValue ∧
        ClosedStackRel resolve sites slots targetRest sourceRest
  | _ :: _, _, _ => False

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
  exact ⟨address_of_site_filter hSite hResolve, hRel⟩

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
  have hFiltered : AddressRel resolve
      (sites.filter fun site => site.token.toNat = sourceToken.toNat)
      targetValue sourceToken :=
    stackRel_get hRel hSlot hTarget hSource
  rcases hFiltered with
    ⟨actual, hActualFiltered, hSourceToken, pc, hResolve, hTargetValue⟩
  have hActual : actual ∈ sites := (List.mem_filter.mp hActualFiltered).1
  have hToken : actual.token = selected.token := by
    rw [← hSourceToken, ← hSelectedToken]
  have hSiteEq := hUnique.eq_of_mem hActual hSelected hToken
  subst actual
  exact
    ⟨pc, hResolve, hTargetValue,
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
