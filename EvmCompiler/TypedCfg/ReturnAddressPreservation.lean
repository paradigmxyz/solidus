import EvmCompiler.TypedCfg.ReturnAddressLower
import EvmCompiler.TypedCfg.InteractionPreservation
import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.Assembly.StackShufflePreservation

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressPreservation

open ReturnAddressRelation

def BooleanWord (value : Word) : Prop :=
  value = EvmYul.UInt256.ofNat 0 ∨
    value = EvmYul.UInt256.ofNat 1

theorem booleanWord_zero :
    BooleanWord (EvmYul.UInt256.ofNat 0) :=
  Or.inl rfl

theorem booleanWord_one :
    BooleanWord (EvmYul.UInt256.ofNat 1) :=
  Or.inr rfl

theorem dynamicReturnMatch_boolean
    (resolve : ReturnAddressRelation.Resolver)
    (token : Word) (site : ReturnSite) :
    BooleanWord
      (ReturnAddressLower.Terminator.dynamicReturnMatch
        resolve token site) := by
  unfold ReturnAddressLower.Terminator.dynamicReturnMatch
  split
  · rename_i dest hDest
    by_cases hEq : EvmYul.UInt256.ofNat dest = token
    · exact Or.inr (by simp [EvmYul.UInt256.eq, hEq])
    · exact Or.inl (by simp [EvmYul.UInt256.eq, hEq])
  · exact booleanWord_zero

theorem lor_boolean
    {left right : Word}
    (hLeft : BooleanWord left) (hRight : BooleanWord right) :
    BooleanWord (EvmYul.UInt256.lor left right) := by
  rcases hLeft with rfl | rfl <;>
    rcases hRight with rfl | rfl <;>
    unfold BooleanWord <;> decide

theorem lor_eq_zero_iff_of_boolean
    {left right : Word}
    (hLeft : BooleanWord left) (hRight : BooleanWord right) :
    EvmYul.UInt256.lor left right = EvmYul.UInt256.ofNat 0 ↔
      left = EvmYul.UInt256.ofNat 0 ∧
        right = EvmYul.UInt256.ofNat 0 := by
  rcases hLeft with rfl | rfl <;>
    rcases hRight with rfl | rfl <;>
    decide

theorem foldl_lor_match_eq_zero_iff
    (resolve : ReturnAddressRelation.Resolver) (token : Word) :
    ∀ (sites : List ReturnSite) (accumulator : Word),
      BooleanWord accumulator →
        (sites.foldl
            (fun value site =>
              EvmYul.UInt256.lor
                (ReturnAddressLower.Terminator.dynamicReturnMatch
                  resolve token site)
                value)
            accumulator =
            EvmYul.UInt256.ofNat 0 ↔
          accumulator = EvmYul.UInt256.ofNat 0 ∧
            ∀ site ∈ sites,
              ReturnAddressLower.Terminator.dynamicReturnMatch
                  resolve token site =
                EvmYul.UInt256.ofNat 0) := by
  intro sites accumulator hAccumulator
  induction sites generalizing accumulator with
  | nil =>
      simp
  | cons head rest ih =>
      let next :=
        EvmYul.UInt256.lor
          (ReturnAddressLower.Terminator.dynamicReturnMatch
            resolve token head)
          accumulator
      have hHead :=
        dynamicReturnMatch_boolean resolve token head
      have hNext : BooleanWord next :=
        lor_boolean hHead hAccumulator
      rw [show
        (head :: rest).foldl
            (fun value site =>
              EvmYul.UInt256.lor
                (ReturnAddressLower.Terminator.dynamicReturnMatch
                  resolve token site)
                value)
            accumulator =
          rest.foldl
            (fun value site =>
              EvmYul.UInt256.lor
                (ReturnAddressLower.Terminator.dynamicReturnMatch
                  resolve token site)
                value)
            next by rfl]
      rw [ih next hNext]
      rw [lor_eq_zero_iff_of_boolean hHead hAccumulator]
      constructor
      · rintro ⟨⟨hHeadZero, hAccumulatorZero⟩, hRest⟩
        exact
          ⟨hAccumulatorZero, by
            intro site hSite
            simp only [List.mem_cons] at hSite
            rcases hSite with rfl | hSite
            · exact hHeadZero
            · exact hRest site hSite⟩
      · rintro ⟨hAccumulatorZero, hAll⟩
        exact
          ⟨⟨hAll head (by simp), hAccumulatorZero⟩,
            fun site hSite => hAll site (by simp [hSite])⟩

theorem dynamicReturnAccumulator_eq_zero_iff
    (resolve : ReturnAddressRelation.Resolver)
    (token : Word) (first : ReturnSite) (rest : List ReturnSite) :
    ReturnAddressLower.Terminator.dynamicReturnAccumulator
          resolve token (first :: rest) =
        EvmYul.UInt256.ofNat 0 ↔
      ∀ site ∈ first :: rest,
        ReturnAddressLower.Terminator.dynamicReturnMatch
            resolve token site =
          EvmYul.UInt256.ofNat 0 := by
  unfold ReturnAddressLower.Terminator.dynamicReturnAccumulator
  rw [foldl_lor_match_eq_zero_iff resolve token rest
    (ReturnAddressLower.Terminator.dynamicReturnMatch
      resolve token first)
    (dynamicReturnMatch_boolean resolve token first)]
  constructor
  · rintro ⟨hFirst, hRest⟩ site hSite
    simp only [List.mem_cons] at hSite
    rcases hSite with rfl | hSite
    · exact hFirst
    · exact hRest site hSite
  · intro hAll
    exact
      ⟨hAll first (by simp),
        fun site hSite => hAll site (by simp [hSite])⟩

theorem label_eq_of_labelPc_eq_some
    {program : Assembly.Program}
    {left right : Label} {pc : Nat}
    (hLeft : program.labelPc left = some pc)
    (hRight : program.labelPc right = some pc) :
    left = right := by
  have hLeftAt := Assembly.Program.instrAtPc_of_labelPc hLeft
  have hRightAt := Assembly.Program.instrAtPc_of_labelPc hRight
  rw [hLeftAt] at hRightAt
  have hInstr :
      Assembly.Instr.label left = Assembly.Instr.label right := by
    exact congrArg Prod.snd (Option.some.inj hRightAt)
  exact Assembly.Instr.label.inj hInstr

theorem returnSlot_address
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {shape : Shape} {depth : Nat} {slot : Slot}
    {targetValue sourceToken : Word}
    {target source : Assembly.EVMState}
    (hSlot : shape.slots[depth]? = some slot)
    (hReturn : ReturnSlot slot)
    (hTarget : target.stack[depth]? = some targetValue)
    (hSource : source.stack[depth]? = some sourceToken)
    (hRel : RuntimeRel resolve sites shape target source) :
    AddressRel resolve sites targetValue sourceToken := by
  have hWord :=
    stackRel_get hRel.2 hSlot hTarget hSource
  cases slot <;>
    simp [ReturnSlot, SlotWordRel] at hReturn hWord ⊢
  all_goals exact hWord

abbrev OpenResultRel (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) :
    Except Assembly.EVMException Assembly.EVMState ->
      Except Assembly.EVMException Assembly.EVMState -> Prop :=
  Simulation.Interaction.ExceptRel
    (fun _targetError _sourceError => True)
    (RuntimeRel resolve sites output)

abbrev OpenPairRel (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) :
    Except Assembly.EVMException (Assembly.EVMState × Shape) ->
      Except Assembly.EVMException (Assembly.EVMState × Shape) -> Prop :=
  Simulation.Interaction.ExceptRel
    (fun _targetError _sourceError => True)
    (fun target source =>
      target.2 = output ∧ source.2 = output ∧
        RuntimeRel resolve sites output target.1 source.1)

theorem openRunAt_runtimeRel_of_openRunState
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {instr : TypedCfg.Instr} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType : instr.type? input = some output)
    (hOpen :
      Simulation.Interaction.Rel (OpenResultRel resolve sites output)
        (TypedCfg.InteractionSemantics.Instr.openRunState
          instr input target)
        (TypedCfg.InteractionSemantics.Instr.openRunState
          instr input source)) :
    Simulation.Interaction.Rel (OpenPairRel resolve sites output)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr input target)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr input source) := by
  unfold TypedCfg.InteractionSemantics.Instr.openRunAt
    TypedCfg.Control.Instr.runAt
  simp only [hType, Option.elim_some,
    Simulation.Interaction.pure, Simulation.Interaction.bind_done_ok]
  apply Simulation.Interaction.Rel.bind hOpen
  intro targetAfter sourceAfter hAfter
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok
      ⟨rfl, rfl, hAfter⟩)

theorem prim_openStep_runtimeRel
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {op : Assembly.PrimOp} {inputArity outputArity : Nat}
    {input output : Shape}
    {target source : Assembly.EVMState}
    (hArity : op.stackArity? = some (inputArity, outputArity))
    (hType : TypedCfg.Instr.type? (.prim op) input = some output)
    (hNoPc : op ≠ .pc)
    (hInputPlain : PlainSlots input.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    Simulation.Interaction.Rel (OpenResultRel resolve sites output)
      (Assembly.InteractionSemantics.PrimOp.openStep op target)
      (Assembly.InteractionSemantics.PrimOp.openStep op source) := by
  obtain ⟨visible, targetHidden, sourceHidden,
      hTargetStack, hSourceStack, hVisibleLength, hTail⟩ :=
    stackRel_split_plain hInputPlain hRel.2
  let targetActive : Assembly.EVMState := { target with stack := visible }
  let sourceActive : Assembly.EVMState := { source with stack := visible }
  have hActiveRel : Assembly.SameRuntimeData targetActive sourceActive := by
    cases target
    cases source
    simp [targetActive, sourceActive, Assembly.SameRuntimeData,
      Assembly.eraseRuntimeControl] at hRel ⊢
    exact hRel.1
  have hTypedLengths :=
    TypedCfg.Instr.length_of_type?_prim hArity hType
  have hTailEq : output.tail = input.tail := by
    simp only [TypedCfg.Instr.type?] at hType
    rw [hArity] at hType
    by_cases hFits : inputArity ≤ input.length
    · simp [hFits] at hType
      cases hType
      rfl
    · simp [hFits] at hType
  have hBound : inputArity ≤ visible.length := by
    rw [hVisibleLength]
    simpa [TypedCfg.Shape.length] using hTypedLengths.1
  have hTargetSuffix :=
    Assembly.InteractionPreservation.PrimOp.openStep_append_stack_rel_of_stackArity_le
      targetActive targetHidden hArity hBound
  have hTargetSuffix' :
      Simulation.Interaction.Rel
        (Assembly.InteractionPreservation.PrimOp.StackSuffixRuntimeRel
          targetHidden)
        (Assembly.InteractionSemantics.PrimOp.openStep op targetActive)
        (Assembly.InteractionSemantics.PrimOp.openStep op target) := by
    have hTargetState :
        { targetActive with stack := targetActive.stack ++ targetHidden } =
          target := by
      cases target
      simp [targetActive] at hTargetStack ⊢
      exact hTargetStack.symm
    rw [hTargetState] at hTargetSuffix
    exact hTargetSuffix
  have hSourceSuffix :=
    Assembly.InteractionPreservation.PrimOp.openStep_append_stack_rel_of_stackArity_le
      sourceActive sourceHidden hArity hBound
  have hSourceSuffix' :
      Simulation.Interaction.Rel
        (Assembly.InteractionPreservation.PrimOp.StackSuffixRuntimeRel
          sourceHidden)
        (Assembly.InteractionSemantics.PrimOp.openStep op sourceActive)
        (Assembly.InteractionSemantics.PrimOp.openStep op source) := by
    have hSourceState :
        { sourceActive with stack := sourceActive.stack ++ sourceHidden } =
          source := by
      cases source
      simp [sourceActive] at hSourceStack ⊢
      exact hSourceStack.symm
    rw [hSourceState] at hSourceSuffix
    exact hSourceSuffix
  have hActive :=
    Assembly.InteractionPreservation.PrimOp.openStep_runtimeRel
      (op := op) ⟨(inputArity, outputArity), hArity⟩ hNoPc hActiveRel
  have hRealizes :=
    Assembly.InteractionPreservation.PrimOp.openStep_realizesStackArity
      (state := targetActive) hArity
  have hTargetToActive :=
    Simulation.Interaction.Rel.strengthen_right hTargetSuffix'.symm hRealizes
  have hTargetToSourceActive :=
    Simulation.Interaction.Rel.trans hTargetToActive hActive
  have hAll :=
    Simulation.Interaction.Rel.trans hTargetToSourceActive hSourceSuffix'
  apply Simulation.Interaction.Rel.mono hAll
  intro targetDone sourceDone hDone
  rcases hDone with
    ⟨sourceActiveDone,
      ⟨targetActiveDone, ⟨hTargetSuffixDone, hTargetLength⟩,
        hActiveDone⟩,
      hSourceSuffixDone⟩
  cases hTargetSuffixDone with
  | @error targetActiveError targetError hTargetError =>
      cases hActiveDone with
      | @error _ sourceActiveError hActiveError =>
          cases hSourceSuffixDone with
          | @error _ sourceError hSourceError =>
              exact Simulation.Interaction.ExceptRel.error
                True.intro
  | @ok targetActiveFinal targetFinal hTargetSuffixState =>
      cases hActiveDone with
      | @ok _ sourceActiveFinal hActiveState =>
          cases hSourceSuffixDone with
          | @ok _ sourceFinal hSourceSuffixState =>
              apply Simulation.Interaction.ExceptRel.ok
              constructor
              · exact
                  (Assembly.SameRuntimeData.shared_eq hTargetSuffixState).trans
                    ((Assembly.SameRuntimeData.shared_eq hActiveState).trans
                      (Assembly.SameRuntimeData.shared_eq
                        hSourceSuffixState).symm)
              · have hPrefixLength :
                    targetActiveFinal.stack.length = output.slots.length := by
                  simp only [
                    Assembly.InteractionPreservation.PrimOp.RealizesStackArity]
                    at hTargetLength
                  rw [hTargetLength, show targetActive.stack.length = visible.length by
                    simp [targetActive], hVisibleLength]
                  simpa [TypedCfg.Shape.length] using hTypedLengths.2.symm
                have hVisibleRel :
                    ClosedStackRel resolve sites output.slots
                      targetActiveFinal.stack targetActiveFinal.stack :=
                  closedStackRel_refl_of_plain hOutputPlain hPrefixLength
                have hActiveStack :
                    targetActiveFinal.stack = sourceActiveFinal.stack :=
                  Assembly.SameRuntimeData.stack_eq hActiveState
                have hVisibleRel' :
                    ClosedStackRel resolve sites output.slots
                      targetActiveFinal.stack sourceActiveFinal.stack := by
                  simpa [hActiveStack] using hVisibleRel
                have hStackRel :=
                  stackRel_of_closed_prefix_tail hVisibleRel' hTail
                have hTargetFinalStack :=
                  Assembly.SameRuntimeData.stack_eq hTargetSuffixState
                have hSourceFinalStack :=
                  Assembly.SameRuntimeData.stack_eq hSourceSuffixState
                have hTargetFinalStack' :
                    targetFinal.stack =
                      targetActiveFinal.stack ++ targetHidden := by
                  simpa using hTargetFinalStack
                have hSourceFinalStack' :
                    sourceFinal.stack =
                      sourceActiveFinal.stack ++ sourceHidden := by
                  simpa using hSourceFinalStack
                change StackRel resolve sites output.slots output.tail
                  targetFinal.stack sourceFinal.stack
                rw [hTailEq]
                rw [hTargetFinalStack', hSourceFinalStack']
                exact hStackRel

theorem prim_openStep_runtimeRel_prefix
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {op : Assembly.PrimOp} {inputArity outputArity : Nat}
    {input output : Shape}
    {target source : Assembly.EVMState}
    (hArity : op.stackArity? = some (inputArity, outputArity))
    (hType : TypedCfg.Instr.type? (.prim op) input = some output)
    (hNoPc : op ≠ .pc)
    (hInputPlain : PlainSlots (input.slots.take inputArity))
    (hRel : RuntimeRel resolve sites input target source) :
    Simulation.Interaction.Rel (OpenResultRel resolve sites output)
      (Assembly.InteractionSemantics.PrimOp.openStep op target)
      (Assembly.InteractionSemantics.PrimOp.openStep op source) := by
  have hTypedLengths :=
    TypedCfg.Instr.length_of_type?_prim hArity hType
  have hInputBound : inputArity ≤ input.slots.length := by
    simpa [TypedCfg.Shape.length] using hTypedLengths.1
  obtain ⟨visible, targetSuffix, sourceSuffix,
      hTargetStack, hSourceStack, hVisibleLength, hSuffixRel⟩ :=
    stackRel_split_prefix_plain hInputBound hInputPlain hRel.2
  let targetActive : Assembly.EVMState := { target with stack := visible }
  let sourceActive : Assembly.EVMState := { source with stack := visible }
  have hActiveRel : Assembly.SameRuntimeData targetActive sourceActive := by
    cases target
    cases source
    simp [targetActive, sourceActive, Assembly.SameRuntimeData,
      Assembly.eraseRuntimeControl] at hRel ⊢
    exact hRel.1
  have hOutputEq :
      output = Shape.pushWords outputArity (Shape.pop inputArity input) := by
    simp only [TypedCfg.Instr.type?] at hType
    rw [hArity] at hType
    by_cases hFits : inputArity ≤ input.length
    · simp [hFits] at hType
      exact hType.symm
    · simp [hFits] at hType
  have hBound : inputArity ≤ visible.length := by
    omega
  have hTargetSuffix :=
    Assembly.InteractionPreservation.PrimOp.openStep_append_stack_rel_of_stackArity_le
      targetActive targetSuffix hArity hBound
  have hTargetSuffix' :
      Simulation.Interaction.Rel
        (Assembly.InteractionPreservation.PrimOp.StackSuffixRuntimeRel
          targetSuffix)
        (Assembly.InteractionSemantics.PrimOp.openStep op targetActive)
        (Assembly.InteractionSemantics.PrimOp.openStep op target) := by
    have hTargetState :
        { targetActive with stack := targetActive.stack ++ targetSuffix } =
          target := by
      cases target
      simp [targetActive] at hTargetStack ⊢
      exact hTargetStack.symm
    rw [hTargetState] at hTargetSuffix
    exact hTargetSuffix
  have hSourceSuffix :=
    Assembly.InteractionPreservation.PrimOp.openStep_append_stack_rel_of_stackArity_le
      sourceActive sourceSuffix hArity hBound
  have hSourceSuffix' :
      Simulation.Interaction.Rel
        (Assembly.InteractionPreservation.PrimOp.StackSuffixRuntimeRel
          sourceSuffix)
        (Assembly.InteractionSemantics.PrimOp.openStep op sourceActive)
        (Assembly.InteractionSemantics.PrimOp.openStep op source) := by
    have hSourceState :
        { sourceActive with stack := sourceActive.stack ++ sourceSuffix } =
          source := by
      cases source
      simp [sourceActive] at hSourceStack ⊢
      exact hSourceStack.symm
    rw [hSourceState] at hSourceSuffix
    exact hSourceSuffix
  have hActive :=
    Assembly.InteractionPreservation.PrimOp.openStep_runtimeRel
      (op := op) ⟨(inputArity, outputArity), hArity⟩ hNoPc hActiveRel
  have hRealizes :=
    Assembly.InteractionPreservation.PrimOp.openStep_realizesStackArity
      (state := targetActive) hArity
  have hTargetToActive :=
    Simulation.Interaction.Rel.strengthen_right hTargetSuffix'.symm hRealizes
  have hTargetToSourceActive :=
    Simulation.Interaction.Rel.trans hTargetToActive hActive
  have hAll :=
    Simulation.Interaction.Rel.trans hTargetToSourceActive hSourceSuffix'
  apply Simulation.Interaction.Rel.mono hAll
  intro targetDone sourceDone hDone
  rcases hDone with
    ⟨sourceActiveDone,
      ⟨targetActiveDone, ⟨hTargetSuffixDone, hTargetLength⟩,
        hActiveDone⟩,
      hSourceSuffixDone⟩
  cases hTargetSuffixDone with
  | @error targetActiveError targetError hTargetError =>
      cases hActiveDone with
      | @error _ sourceActiveError hActiveError =>
          cases hSourceSuffixDone with
          | @error _ sourceError hSourceError =>
              exact Simulation.Interaction.ExceptRel.error
                True.intro
  | @ok targetActiveFinal targetFinal hTargetSuffixState =>
      cases hActiveDone with
      | @ok _ sourceActiveFinal hActiveState =>
          cases hSourceSuffixDone with
          | @ok _ sourceFinal hSourceSuffixState =>
              apply Simulation.Interaction.ExceptRel.ok
              constructor
              · exact
                  (Assembly.SameRuntimeData.shared_eq hTargetSuffixState).trans
                    ((Assembly.SameRuntimeData.shared_eq hActiveState).trans
                      (Assembly.SameRuntimeData.shared_eq
                        hSourceSuffixState).symm)
              · have hPrefixLength :
                    targetActiveFinal.stack.length =
                      (List.replicate outputArity Slot.word).length := by
                  simp only [
                    Assembly.InteractionPreservation.PrimOp.RealizesStackArity]
                    at hTargetLength
                  rw [hTargetLength,
                    show targetActive.stack.length = visible.length by
                      simp [targetActive],
                    hVisibleLength]
                  simp
                have hPrefixPlain :
                    PlainSlots (List.replicate outputArity Slot.word) := by
                  intro slot hMem
                  have hSlot : slot = .word := by
                    simpa using List.eq_of_mem_replicate hMem
                  subst slot
                  trivial
                have hPrefixRel :
                    ClosedStackRel resolve sites
                      (List.replicate outputArity Slot.word)
                      targetActiveFinal.stack targetActiveFinal.stack :=
                  closedStackRel_refl_of_plain hPrefixPlain hPrefixLength
                have hActiveStack :
                    targetActiveFinal.stack = sourceActiveFinal.stack :=
                  Assembly.SameRuntimeData.stack_eq hActiveState
                have hPrefixRel' :
                    ClosedStackRel resolve sites
                      (List.replicate outputArity Slot.word)
                      targetActiveFinal.stack sourceActiveFinal.stack := by
                  simpa [hActiveStack] using hPrefixRel
                have hStackRel :=
                  stackRel_of_closed_prefix_suffix hPrefixRel' hSuffixRel
                have hTargetFinalStack :=
                  Assembly.SameRuntimeData.stack_eq hTargetSuffixState
                have hSourceFinalStack :=
                  Assembly.SameRuntimeData.stack_eq hSourceSuffixState
                have hTargetFinalStack' :
                    targetFinal.stack =
                      targetActiveFinal.stack ++ targetSuffix := by
                  simpa using hTargetFinalStack
                have hSourceFinalStack' :
                    sourceFinal.stack =
                      sourceActiveFinal.stack ++ sourceSuffix := by
                  simpa using hSourceFinalStack
                change StackRel resolve sites output.slots output.tail
                  targetFinal.stack sourceFinal.stack
                rw [hTargetFinalStack', hSourceFinalStack']
                simpa [hOutputEq, Shape.pushWords, Shape.pop] using hStackRel

theorem prim_openStep_runtimeRel_retype
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {op : Assembly.PrimOp} {inputArity outputArity : Nat}
    {input primitiveOutput output : Shape}
    {target source : Assembly.EVMState}
    (hArity : op.stackArity? = some (inputArity, outputArity))
    (hPrimitiveType :
      TypedCfg.Instr.type? (.prim op) input = some primitiveOutput)
    (hNoPc : op ≠ .pc)
    (hInputPlain : PlainSlots input.slots)
    (hPrimitivePlain : PlainSlots primitiveOutput.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hLength : output.length = primitiveOutput.length)
    (hTail : output.tail = primitiveOutput.tail)
    (hRel : RuntimeRel resolve sites input target source) :
    Simulation.Interaction.Rel (OpenResultRel resolve sites output)
      (Assembly.InteractionSemantics.PrimOp.openStep op target)
      (Assembly.InteractionSemantics.PrimOp.openStep op source) := by
  have hPrimitive := prim_openStep_runtimeRel hArity hPrimitiveType hNoPc
    hInputPlain hPrimitivePlain hRel
  apply Simulation.Interaction.Rel.mono hPrimitive
  intro targetDone sourceDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hState =>
      apply Simulation.Interaction.ExceptRel.ok
      exact runtimeRel_retype_plain hPrimitivePlain hOutputPlain
        hLength hTail hState

theorem bindLocals_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {offset : Nat} {names : List String} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.bindLocals offset names) input = some output)
    (hInputPlain : PlainSlots input.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  exact runtimeRel_retype_plain hInputPlain hOutputPlain
    (TypedCfg.Instr.length_of_type?_bindLocals hType)
    (TypedCfg.Instr.tail_of_type? hType) hRel

theorem bindLocals_runtimeRel_classes
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {offset : Nat} {names : List String} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.bindLocals offset names) input = some output)
    (hClasses : SlotsClassRel input.slots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source :=
  runtimeRel_retype_classes hClasses
    (TypedCfg.Instr.tail_of_type? hType) hRel

theorem bindScratch_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {baseDepth slot : Nat} {name : String} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType :
      TypedCfg.Instr.type? (.bindScratch baseDepth name slot) input = some output)
    (hInputPlain : PlainSlots input.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  exact runtimeRel_retype_plain hInputPlain hOutputPlain
    (TypedCfg.Instr.length_of_type?_bindScratch hType)
    (TypedCfg.Instr.tail_of_type? hType) hRel

theorem bindScratch_runtimeRel_classes
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {baseDepth slot : Nat} {name : String} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType :
      TypedCfg.Instr.type? (.bindScratch baseDepth name slot) input = some output)
    (hClasses : SlotsClassRel input.slots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source :=
  runtimeRel_retype_classes hClasses
    (TypedCfg.Instr.tail_of_type? hType) hRel

theorem relabel_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {newShape input output : Shape} {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.relabel newShape) input = some output)
    (hInputPlain : PlainSlots input.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source := by
  exact runtimeRel_retype_plain hInputPlain hOutputPlain
    (TypedCfg.Instr.length_of_type?_relabel hType)
    (TypedCfg.Instr.tail_of_type? hType) hRel

theorem relabel_runtimeRel_classes
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {newShape input output : Shape} {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.relabel newShape) input = some output)
    (hClasses : SlotsClassRel input.slots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    RuntimeRel resolve sites output target source :=
  runtimeRel_retype_classes hClasses
    (TypedCfg.Instr.tail_of_type? hType) hRel

theorem push_runState_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {value : Word} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.push value) input = some output)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites output
      (TypedCfg.Instr.runState (.push value) input target)
      (TypedCfg.Instr.runState (.push value) input source) := by
  simp [TypedCfg.Instr.type?] at hType
  subst output
  apply Simulation.Interaction.ExceptRel.ok
  apply runtimeRel_replaceStackAndIncrPC hRel
  exact ⟨rfl, hRel.2⟩

theorem dup_runState_eq_evmDup
    {depth : Nat} (hDepth : depth < 16)
    (shape : Shape) (state : Assembly.EVMState) :
    TypedCfg.Instr.runState (.dup depth) shape state =
      EvmYul.dup (depth + 1) state := by
  interval_cases depth <;> rfl

theorem swap_runState_eq_evmSwap
    {depth : Nat} (hDepth : depth < 16)
    (shape : Shape) (state : Assembly.EVMState) :
    TypedCfg.Instr.runState (.swap depth) shape state =
      EvmYul.swap (depth + 1) state := by
  interval_cases depth <;> rfl

theorem dup_runState_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {depth : Nat} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.dup depth) input = some output)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites output
      (TypedCfg.Instr.runState (.dup depth) input target)
      (TypedCfg.Instr.runState (.dup depth) input source) := by
  have hDepth : depth < 16 := by
    by_contra hNot
    simp [TypedCfg.Instr.type?, hNot] at hType
  cases hSlot : input.get? depth with
  | none =>
      simp [TypedCfg.Instr.type?, hDepth, hSlot] at hType
  | some slot =>
      simp [TypedCfg.Instr.type?, hDepth, hSlot] at hType
      subst output
      obtain ⟨targetValue, sourceValue,
          hTargetGet, hSourceGet, _hValueRel⟩ :=
        stackRel_get_exists hRel.2 hSlot
      let targetAfter :=
        target.replaceStackAndIncrPC (targetValue :: target.stack)
      let sourceAfter :=
        source.replaceStackAndIncrPC (sourceValue :: source.stack)
      have hTargetStack :
          target.stack =
            target.stack.take depth ++
              targetValue :: target.stack.drop (depth + 1) :=
        list_eq_take_get_drop hTargetGet
      have hSourceStack :
          source.stack =
            source.stack.take depth ++
              sourceValue :: source.stack.drop (depth + 1) :=
        list_eq_take_get_drop hSourceGet
      have hTargetRun :
          TypedCfg.Instr.runState (.dup depth) input target =
            .ok targetAfter := by
        rw [dup_runState_eq_evmDup hDepth]
        have hFrontLength :
            (target.stack.take depth).length = depth := by
          have hLt := (List.getElem?_eq_some_iff.mp hTargetGet).choose
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hLt)]
        have hTargetStack' :
            target.stack =
              target.stack.take depth ++ [targetValue] ++
                target.stack.drop (depth + 1) := by
          simpa [List.append_assoc] using hTargetStack
        have hTargetRecord :
            { target with
              stack :=
                target.stack.take depth ++ [targetValue] ++
                  target.stack.drop (depth + 1) } = target := by
          cases target
          simpa using hTargetStack'.symm
        have hRun :=
          Assembly.StackShuffle.dup_append_token
            (state := target)
            (front := target.stack.take depth)
            (suffix := target.stack.drop (depth + 1))
            (token := targetValue)
        rw [hFrontLength, hTargetRecord] at hRun
        have hNewStack :
            targetValue ::
                target.stack.take depth ++ [targetValue] ++
                  target.stack.drop (depth + 1) =
              targetValue :: target.stack :=
          congrArg (List.cons targetValue) hTargetStack'.symm
        rw [hNewStack] at hRun
        simpa [targetAfter] using hRun
      have hSourceRun :
          TypedCfg.Instr.runState (.dup depth) input source =
            .ok sourceAfter := by
        rw [dup_runState_eq_evmDup hDepth]
        have hFrontLength :
            (source.stack.take depth).length = depth := by
          have hLt := (List.getElem?_eq_some_iff.mp hSourceGet).choose
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hLt)]
        have hSourceStack' :
            source.stack =
              source.stack.take depth ++ [sourceValue] ++
                source.stack.drop (depth + 1) := by
          simpa [List.append_assoc] using hSourceStack
        have hSourceRecord :
            { source with
              stack :=
                source.stack.take depth ++ [sourceValue] ++
                  source.stack.drop (depth + 1) } = source := by
          cases source
          simpa using hSourceStack'.symm
        have hRun :=
          Assembly.StackShuffle.dup_append_token
            (state := source)
            (front := source.stack.take depth)
            (suffix := source.stack.drop (depth + 1))
            (token := sourceValue)
        rw [hFrontLength, hSourceRecord] at hRun
        have hNewStack :
            sourceValue ::
                source.stack.take depth ++ [sourceValue] ++
                  source.stack.drop (depth + 1) =
              sourceValue :: source.stack :=
          congrArg (List.cons sourceValue) hSourceStack'.symm
        rw [hNewStack] at hRun
        simpa [sourceAfter] using hRun
      rw [hTargetRun, hSourceRun]
      apply Simulation.Interaction.ExceptRel.ok
      apply runtimeRel_replaceStackAndIncrPC hRel
      exact stackRel_dup hRel.2 hSlot hTargetGet hSourceGet

theorem swap_runState_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {depth : Nat} {input output : Shape}
    {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? (.swap depth) input = some output)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites output
      (TypedCfg.Instr.runState (.swap depth) input target)
      (TypedCfg.Instr.runState (.swap depth) input source) := by
  have hDepth : depth < 16 := by
    by_contra hNot
    simp [TypedCfg.Instr.type?, hNot] at hType
  cases hInputSlots : input.slots with
  | nil =>
      simp [TypedCfg.Instr.type?, Shape.get?, hDepth, hInputSlots] at hType
  | cons topSlot restSlots =>
      cases hDeep : input.get? (depth + 1) with
      | none =>
          have hDeepRest : restSlots[depth]? = none := by
            simpa [Shape.get?, hInputSlots] using hDeep
          simp [TypedCfg.Instr.type?, hDepth,
            hInputSlots, hDeep, hDeepRest] at hType
      | some deepSlot =>
          simp [TypedCfg.Instr.type?, hDepth, hInputSlots, hDeep] at hType
          subst output
          have hDeepRest : restSlots[depth]? = some deepSlot := by
            simpa [Shape.get?, hInputSlots] using hDeep
          cases hTargetStack : target.stack with
          | nil =>
              have hFalse := hRel.2
              simp [ShapeStackRel, hInputSlots, hTargetStack] at hFalse
              exact False.elim hFalse
          | cons topTarget targetRest =>
              cases hSourceStack : source.stack with
              | nil =>
                  have hFalse := hRel.2
                  simp [ShapeStackRel, hInputSlots,
                    hTargetStack, hSourceStack] at hFalse
                  exact False.elim hFalse
              | cons topSource sourceRest =>
                  have hStackRel :
                      StackRel resolve sites (topSlot :: restSlots)
                        input.tail (topTarget :: targetRest)
                        (topSource :: sourceRest) := by
                    simpa [ShapeStackRel, hInputSlots,
                      hTargetStack, hSourceStack] using hRel.2
                  obtain ⟨deepTarget, deepSource,
                      hTargetGet, hSourceGet, _hDeepRel⟩ :=
                    stackRel_get_exists hStackRel.2 hDeepRest
                  let targetAfter :=
                    target.replaceStackAndIncrPC
                      (deepTarget :: targetRest.set depth topTarget)
                  let sourceAfter :=
                    source.replaceStackAndIncrPC
                      (deepSource :: sourceRest.set depth topSource)
                  have hTargetRest :
                      targetRest =
                        targetRest.take depth ++
                          deepTarget :: targetRest.drop (depth + 1) :=
                    list_eq_take_get_drop hTargetGet
                  have hSourceRest :
                      sourceRest =
                        sourceRest.take depth ++
                          deepSource :: sourceRest.drop (depth + 1) :=
                    list_eq_take_get_drop hSourceGet
                  have hTargetSet :
                      targetRest.set depth topTarget =
                        targetRest.take depth ++
                          topTarget :: targetRest.drop (depth + 1) := by
                    exact
                      List.set_eq_take_cons_drop topTarget
                        (List.getElem?_eq_some_iff.mp hTargetGet).choose
                  have hSourceSet :
                      sourceRest.set depth topSource =
                        sourceRest.take depth ++
                          topSource :: sourceRest.drop (depth + 1) := by
                    exact
                      List.set_eq_take_cons_drop topSource
                        (List.getElem?_eq_some_iff.mp hSourceGet).choose
                  have hTargetRun :
                      TypedCfg.Instr.runState (.swap depth) input target =
                        .ok targetAfter := by
                    rw [swap_runState_eq_evmSwap hDepth]
                    have hTargetRecord :
                        { target with
                          stack :=
                            topTarget :: targetRest.take depth ++
                              [deepTarget] ++
                                targetRest.drop (depth + 1) } = target := by
                      have hFullStack :
                          target.stack =
                            topTarget :: targetRest.take depth ++
                              [deepTarget] ++
                                targetRest.drop (depth + 1) := by
                        calc
                          target.stack = topTarget :: targetRest :=
                            hTargetStack
                          _ =
                              topTarget :: targetRest.take depth ++
                                [deepTarget] ++
                                  targetRest.drop (depth + 1) :=
                            congrArg (List.cons topTarget)
                              (by
                                simpa [List.append_assoc] using hTargetRest)
                      cases target
                      simpa using hFullStack.symm
                    have hRun :=
                      Assembly.StackShuffle.swap_snoc
                        (state := target)
                        (front := targetRest.take depth)
                        (suffix := targetRest.drop (depth + 1))
                        (top := topTarget) (last := deepTarget)
                    have hFrontLength :
                        (targetRest.take depth).length = depth := by
                      have hLt :=
                        (List.getElem?_eq_some_iff.mp hTargetGet).choose
                      simp [List.length_take,
                        Nat.min_eq_left (Nat.le_of_lt hLt)]
                    rw [hFrontLength, hTargetRecord] at hRun
                    have hNewStack :
                        deepTarget :: targetRest.take depth ++
                            [topTarget] ++ targetRest.drop (depth + 1) =
                          deepTarget :: targetRest.set depth topTarget :=
                      congrArg (List.cons deepTarget)
                        (by
                          simpa [List.append_assoc] using hTargetSet.symm)
                    rw [hNewStack] at hRun
                    simpa [targetAfter] using hRun
                  have hSourceRun :
                      TypedCfg.Instr.runState (.swap depth) input source =
                        .ok sourceAfter := by
                    rw [swap_runState_eq_evmSwap hDepth]
                    have hSourceRecord :
                        { source with
                          stack :=
                            topSource :: sourceRest.take depth ++
                              [deepSource] ++
                                sourceRest.drop (depth + 1) } = source := by
                      have hFullStack :
                          source.stack =
                            topSource :: sourceRest.take depth ++
                              [deepSource] ++
                                sourceRest.drop (depth + 1) := by
                        calc
                          source.stack = topSource :: sourceRest :=
                            hSourceStack
                          _ =
                              topSource :: sourceRest.take depth ++
                                [deepSource] ++
                                  sourceRest.drop (depth + 1) :=
                            congrArg (List.cons topSource)
                              (by
                                simpa [List.append_assoc] using hSourceRest)
                      cases source
                      simpa using hFullStack.symm
                    have hRun :=
                      Assembly.StackShuffle.swap_snoc
                        (state := source)
                        (front := sourceRest.take depth)
                        (suffix := sourceRest.drop (depth + 1))
                        (top := topSource) (last := deepSource)
                    have hFrontLength :
                        (sourceRest.take depth).length = depth := by
                      have hLt :=
                        (List.getElem?_eq_some_iff.mp hSourceGet).choose
                      simp [List.length_take,
                        Nat.min_eq_left (Nat.le_of_lt hLt)]
                    rw [hFrontLength, hSourceRecord] at hRun
                    have hNewStack :
                        deepSource :: sourceRest.take depth ++
                            [topSource] ++ sourceRest.drop (depth + 1) =
                          deepSource :: sourceRest.set depth topSource :=
                      congrArg (List.cons deepSource)
                        (by
                          simpa [List.append_assoc] using hSourceSet.symm)
                    rw [hNewStack] at hRun
                    simpa [sourceAfter] using hRun
                  rw [hTargetRun, hSourceRun]
                  apply Simulation.Interaction.ExceptRel.ok
                  apply runtimeRel_replaceStackAndIncrPC hRel
                  simpa [ShapeStackRel, hInputSlots,
                    hTargetStack, hSourceStack] using
                      (stackRel_swapTop hStackRel hDeepRest
                        hTargetGet hSourceGet)

theorem pop_runState_runtimeRel_any
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {input output : Shape} {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites output
      (TypedCfg.Instr.runState .pop input target)
      (TypedCfg.Instr.runState .pop input source) := by
  cases hInputSlots : input.slots with
  | nil =>
      simp [TypedCfg.Instr.type?, hInputSlots] at hType
  | cons slot restSlots =>
      simp [TypedCfg.Instr.type?, hInputSlots] at hType
      subst output
      cases hTargetStack : target.stack with
      | nil =>
          have hFalse := hRel.2
          simp [ShapeStackRel, hInputSlots, hTargetStack] at hFalse
          exact False.elim hFalse
      | cons targetValue targetRest =>
          cases hSourceStack : source.stack with
          | nil =>
              have hFalse := hRel.2
              simp [ShapeStackRel, hInputSlots,
                hTargetStack, hSourceStack] at hFalse
              exact False.elim hFalse
          | cons sourceValue sourceRest =>
              let targetAfter :=
                target.replaceStackAndIncrPC targetRest
              let sourceAfter :=
                source.replaceStackAndIncrPC sourceRest
              have hTargetRun :
                  TypedCfg.Instr.runState .pop input target =
                    .ok targetAfter := by
                simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
                  Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
                  EvmYul.Stack.pop, hTargetStack, targetAfter]
              have hSourceRun :
                  TypedCfg.Instr.runState .pop input source =
                    .ok sourceAfter := by
                simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
                  Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
                  EvmYul.Stack.pop, hSourceStack, sourceAfter]
              rw [hTargetRun, hSourceRun]
              apply Simulation.Interaction.ExceptRel.ok
              apply runtimeRel_replaceStackAndIncrPC hRel
              have hStackRel :
                  StackRel resolve sites (slot :: restSlots) input.tail
                    (targetValue :: targetRest)
                    (sourceValue :: sourceRest) := by
                simpa [ShapeStackRel, hInputSlots,
                  hTargetStack, hSourceStack] using hRel.2
              exact hStackRel.2

theorem runPops_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {input : Shape} {target source : Assembly.EVMState}
    (count : Nat) (hBound : count ≤ input.length)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites (Shape.pop count input)
      (TypedCfg.Instr.runPops count target)
      (TypedCfg.Instr.runPops count source) := by
  induction count generalizing input target source with
  | zero =>
      exact Simulation.Interaction.ExceptRel.ok (by simpa using hRel)
  | succ count ih =>
      cases hInputSlots : input.slots with
      | nil =>
          simp [Shape.length, hInputSlots] at hBound
      | cons slot restSlots =>
          cases hTargetStack : target.stack with
          | nil =>
              have hFalse := hRel.2
              simp [ShapeStackRel, hInputSlots, hTargetStack] at hFalse
              exact False.elim hFalse
          | cons targetValue targetRest =>
              cases hSourceStack : source.stack with
              | nil =>
                  have hFalse := hRel.2
                  simp [ShapeStackRel, hInputSlots,
                    hTargetStack, hSourceStack] at hFalse
                  exact False.elim hFalse
              | cons sourceValue sourceRest =>
                  let targetAfter :=
                    target.replaceStackAndIncrPC targetRest
                  let sourceAfter :=
                    source.replaceStackAndIncrPC sourceRest
                  have hTargetPop :
                      Assembly.PrimOp.pop.step target =
                        .ok targetAfter := by
                    simp [Assembly.PrimOp.step,
                      Assembly.PrimOp.continuingStep?,
                      Assembly.PrimStep.run, EvmYul.Stack.pop,
                      hTargetStack, targetAfter]
                  have hSourcePop :
                      Assembly.PrimOp.pop.step source =
                        .ok sourceAfter := by
                    simp [Assembly.PrimOp.step,
                      Assembly.PrimOp.continuingStep?,
                      Assembly.PrimStep.run, EvmYul.Stack.pop,
                      hSourceStack, sourceAfter]
                  have hStackRel :
                      StackRel resolve sites (slot :: restSlots) input.tail
                        (targetValue :: targetRest)
                        (sourceValue :: sourceRest) := by
                    simpa [ShapeStackRel, hInputSlots,
                      hTargetStack, hSourceStack] using hRel.2
                  have hAfterRel :
                      RuntimeRel resolve sites
                        { input with slots := restSlots }
                        targetAfter sourceAfter := by
                    apply runtimeRel_replaceStackAndIncrPC hRel
                    exact hStackRel.2
                  have hRestBound :
                      count ≤ ({ input with slots := restSlots } : Shape).length := by
                    simp [Shape.length]
                    simpa [Shape.length, hInputSlots] using hBound
                  have hRest :=
                    ih hRestBound hAfterRel
                  simp only [TypedCfg.Instr.runPops, hTargetPop,
                    hSourcePop, Bind.bind, Except.bind]
                  simpa [Shape.pop, hInputSlots] using hRest

theorem unwind_runState_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {targetShape input output : Shape}
    {target source : Assembly.EVMState}
    (hType :
      TypedCfg.Instr.type? (.unwind targetShape) input = some output)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites output
      (TypedCfg.Instr.runState (.unwind targetShape) input target)
      (TypedCfg.Instr.runState (.unwind targetShape) input source) := by
  simp only [TypedCfg.Instr.type?] at hType
  unfold Shape.unwindTo at hType
  by_cases hCheck :
      targetShape.tail = input.tail ∧
        targetShape.length ≤ input.length ∧
          input.slots.drop (input.length - targetShape.length) =
            targetShape.slots
  · simp [hCheck] at hType
    subst output
    have hBound :
        input.length - targetShape.length ≤ input.length := by omega
    have hPops :=
      runPops_runtimeRel
        (input.length - targetShape.length) hBound hRel
    have hShape :
        Shape.pop (input.length - targetShape.length) input =
          targetShape := by
      cases input
      cases targetShape
      simp [Shape.pop, Shape.length] at hCheck ⊢
      exact ⟨hCheck.2.2, hCheck.1.symm⟩
    simpa [TypedCfg.Instr.runState, hShape] using hPops
  · simp [hCheck] at hType

theorem pop_runState_runtimeRel
    {resolve : ReturnAddressRelation.Resolver} {sites : List ReturnSite}
    {input output : Shape} {target source : Assembly.EVMState}
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hInputPlain : PlainSlots input.slots)
    (hOutputPlain : PlainSlots output.slots)
    (hRel : RuntimeRel resolve sites input target source) :
    OpenResultRel resolve sites output
      (TypedCfg.Instr.runState .pop input target)
      (TypedCfg.Instr.runState .pop input source) := by
  have hPrimType :
      TypedCfg.Instr.type? (.prim .pop) input = some output := by
    rcases input with ⟨slots, tail⟩
    cases slots with
    | nil => simp [TypedCfg.Instr.type?] at hType
    | cons slot rest =>
        simp [TypedCfg.Instr.type?, TypedCfg.Shape.length,
          TypedCfg.Shape.pop, TypedCfg.Shape.pushWords,
          Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
          EvmYul.EVM.δ, EvmYul.EVM.α] at hType ⊢
        exact hType
  have hOpen := prim_openStep_runtimeRel
    (resolve := resolve) (sites := sites)
    (op := Assembly.PrimOp.pop) (inputArity := 1) (outputArity := 0)
    (input := input) (output := output)
    (target := target) (source := source)
    (by rfl) hPrimType (by decide) hInputPlain hOutputPlain hRel
  change Simulation.Interaction.Rel (OpenResultRel resolve sites output)
    (.done (TypedCfg.Instr.runState .pop input target))
    (.done (TypedCfg.Instr.runState .pop input source)) at hOpen
  cases hOpen with
  | done hDone => exact hDone

theorem openRunState_runtimeRel_of_not_returnToken
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {instr : TypedCfg.Instr} {input output : Shape}
    {target source : Assembly.EVMState}
    (hNotReturnToken : ∀ token, instr ≠ .returnToken token)
    (hType : instr.type? input = some output)
    (hSafe : ReturnAddressLower.Instr.Safe instr input output)
    (hRel : RuntimeRel resolve sites input target source) :
    Simulation.Interaction.Rel (OpenResultRel resolve sites output)
      (TypedCfg.InteractionSemantics.Instr.openRunState
        instr input target)
      (TypedCfg.InteractionSemantics.Instr.openRunState
        instr input source) := by
  cases instr with
  | prim op =>
      cases hArity : op.stackArity? with
      | none =>
          simp [ReturnAddressLower.Instr.Safe, hArity] at hSafe
      | some arity =>
          rcases arity with ⟨inputArity, outputArity⟩
          simp only [ReturnAddressLower.Instr.Safe, hArity] at hSafe
          exact
            prim_openStep_runtimeRel_prefix hArity hType
              hSafe.1 hSafe.2 hRel
  | push value =>
      exact Simulation.Interaction.Rel.done
        (push_runState_runtimeRel hType hRel)
  | returnToken token =>
      exact False.elim (hNotReturnToken token rfl)
  | pop =>
      exact Simulation.Interaction.Rel.done
        (pop_runState_runtimeRel_any hType hRel)
  | dup depth =>
      exact Simulation.Interaction.Rel.done
        (dup_runState_runtimeRel hType hRel)
  | swap depth =>
      exact Simulation.Interaction.Rel.done
        (swap_runState_runtimeRel hType hRel)
  | bindLocals offset names =>
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.ok
          (bindLocals_runtimeRel_classes hType hSafe hRel))
  | bindScratch baseDepth name slot =>
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.ok
          (bindScratch_runtimeRel_classes hType hSafe hRel))
  | relabel newShape =>
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.ok
          (relabel_runtimeRel_classes hType hSafe hRel))
  | unwind targetShape =>
      exact Simulation.Interaction.Rel.done
        (unwind_runState_runtimeRel hType hRel)

theorem openRunAt_runtimeRel_of_not_returnToken
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {instr : TypedCfg.Instr} {input output : Shape}
    {target source : Assembly.EVMState}
    (hNotReturnToken : ∀ token, instr ≠ .returnToken token)
    (hType : instr.type? input = some output)
    (hSafe : ReturnAddressLower.Instr.Safe instr input output)
    (hRel : RuntimeRel resolve sites input target source) :
    Simulation.Interaction.Rel (OpenPairRel resolve sites output)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr input target)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr input source) :=
  openRunAt_runtimeRel_of_openRunState hType
    (openRunState_runtimeRel_of_not_returnToken
      hNotReturnToken hType hSafe hRel)

abbrev LoweredInstrResultRel
    (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) (endPc : Word) :
    Except Assembly.EVMException Assembly.StepResult ->
      Except Assembly.EVMException (Assembly.EVMState × Shape) -> Prop :=
  Simulation.Interaction.ExceptRel
    (fun _targetError _sourceError => True)
    (fun target source =>
      match target with
      | .halted _ => False
      | .running targetState =>
          targetState.pc = endPc ∧ source.2 = output ∧
            RuntimeRel resolve sites output targetState source.1)

theorem map_running_left
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {output : Shape} {endPc : Word}
    {target :
      Simulation.Interaction Assembly.EVMException
        (Assembly.EVMState × Shape)}
    {source :
      Simulation.Interaction Assembly.EVMException
        (Assembly.EVMState × Shape)}
    (hRel :
      Simulation.Interaction.Rel (OpenPairRel resolve sites output)
        target source)
    (hAtEnd :
      Simulation.Interaction.AllDone
        (fun result =>
          match result with
          | .error _ => True
          | .ok targetResult => targetResult.1.pc = endPc)
        target) :
    Simulation.Interaction.Rel
      (LoweredInstrResultRel resolve sites output endPc)
      (Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1) target)
      source := by
  induction hRel with
  | done hDone =>
      cases hAtEnd with
      | done hEnd =>
        cases hDone with
        | error hError =>
            exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error True.intro)
        | ok hPair =>
            exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.ok
                ⟨hEnd, hPair.2.1, hPair.2.2⟩)
  | request hResume ih =>
      cases hAtEnd with
      | request hAtResume =>
          exact Simulation.Interaction.Rel.request fun answer =>
            ih answer (hAtResume answer)

theorem lowerAt_openRunNResult_runtimeRel_of_not_returnToken
    {cfg : TypedCfg.Program}
    {instr : TypedCfg.Instr} {input output : Shape}
    {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hNotReturnToken : ∀ token, instr ≠ .returnToken token)
    (hLower :
      ReturnAddressLower.Instr.lowerAt? cfg instr input =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        input target source) :
    Simulation.Interaction.Rel
      (LoweredInstrResultRel
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg) output
        (pre ++ code).pcAfter)
      (Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length target)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr input source) := by
  have hType :=
    ReturnAddressLower.Instr.type?_eq_some_of_lowerAt? hLower
  have hSafe :=
    ReturnAddressLower.Instr.safe_of_lowerAt? hLower
  have hStandard :=
    ReturnAddressLower.Instr.standard_lowerAt?_of_lowerAt?_not_returnToken
      hNotReturnToken hLower
  have hExact :=
    TypedCfg.InteractionPreservation.Instr.lowerAt_openRunNResult_eq
      (post := post) hStandard hFits hPc
  rw [hExact]
  apply map_running_left
  · exact openRunAt_runtimeRel_of_not_returnToken
      hNotReturnToken hType hSafe hRel
  · apply Simulation.Interaction.AllDone.mono
      (TypedCfg.InteractionPreservation.Instr.openRunAt_atLoweredEnd
        (state := target) hStandard)
    intro result hEnd
    cases result with
    | error err => trivial
    | ok value =>
        rcases value with ⟨final, actualOutput⟩
        exact
          calc
            final.pc =
                target.pc +
                  EvmYul.UInt256.ofNat code.byteLength :=
              hEnd.1
            _ =
                pre.pcAfter +
                  EvmYul.UInt256.ofNat code.byteLength := by
              rw [hPc]
            _ = (pre ++ code).pcAfter :=
              (Assembly.Program.pcAfter_append pre code).symm

theorem returnToken_stepAt
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {token : Word} {site : ReturnSite} {targetPc currentPc : Nat}
    {shape : Shape} {target source : Assembly.EVMState}
    (hFind : ReturnAddressLower.Program.siteForToken? cfg token = some site)
    (hResolve : assembly.labelPc site.target = some targetPc)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    exists targetAfter sourceAfter,
      Assembly.Source.stepAt assembly currentPc (.pushLabel site.target) target =
          .ok targetAfter ∧
      TypedCfg.Instr.runState (.returnToken token) shape source =
          .ok sourceAfter ∧
        RuntimeRel assembly.labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          { shape with slots := .returnPC token.toNat :: shape.slots }
          targetAfter sourceAfter ∧
        targetAfter.pc =
          target.pc + EvmYul.UInt256.ofNat 33 := by
  have hSite := ReturnAddressLower.siteForToken?_mem hFind
  have hToken : site.token = token := hSite.2
  subst token
  let targetAfter :=
    target.replaceStackAndIncrPC
      (target.stack.push (EvmYul.UInt256.ofNat targetPc)) (pcΔ := 33)
  let sourceAfter :=
    source.replaceStackAndIncrPC (source.stack.push site.token) (pcΔ := 33)
  refine ⟨targetAfter, sourceAfter, ?_, ?_, ?_, ?_⟩
  · simp [Assembly.Source.stepAt, hResolve, targetAfter,
      Assembly.Target.stepInstr, Assembly.Target.stepInstrWith,
      Assembly.Target.stepPushWith]
  · rfl
  · apply runtimeRel_replaceStackAndIncrPC hRel
    exact shapeStackRel_push_returnPC hSite.1 hResolve hRel.2
  · simp [targetAfter, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

theorem returnToken_openStepAt
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {token : Word} {site : ReturnSite} {targetPc currentPc : Nat}
    {shape : Shape} {target source : Assembly.EVMState}
    (hFind : ReturnAddressLower.Program.siteForToken? cfg token = some site)
    (hResolve : assembly.labelPc site.target = some targetPc)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    exists targetAfter sourceAfter,
      Assembly.InteractionSemantics.Source.openStepAt assembly currentPc
          (.pushLabel site.target) target =
          Simulation.Interaction.pure targetAfter ∧
      TypedCfg.Instr.runState (.returnToken token) shape source =
          .ok sourceAfter ∧
        RuntimeRel assembly.labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          { shape with slots := .returnPC token.toNat :: shape.slots }
          targetAfter sourceAfter ∧
        targetAfter.pc =
          target.pc + EvmYul.UInt256.ofNat 33 := by
  obtain ⟨targetAfter, sourceAfter, hTarget, hSource, hRelAfter,
      hTargetPc⟩ :=
    returnToken_stepAt (currentPc := currentPc) hFind hResolve hRel
  exact
    ⟨targetAfter, sourceAfter,
      by
        simp [Assembly.InteractionSemantics.Source.openStepAt, hTarget]
        rfl,
      hSource, hRelAfter, hTargetPc⟩

theorem lowerAt_returnToken_openRunNResult_runtimeRel
    {cfg : TypedCfg.Program} {token : Word}
    {input output : Shape}
    {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hLower :
      ReturnAddressLower.Instr.lowerAt? cfg (.returnToken token) input =
        some (code, output))
    (hTargets :
      ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
        ∃ pc, (pre ++ code ++ post).labelPc site.target = some pc)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        input target source) :
    Simulation.Interaction.Rel
      (LoweredInstrResultRel
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg) output
        (pre ++ code).pcAfter)
      (Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length target)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        (.returnToken token) input source) := by
  obtain ⟨site, hFind, hCode, hOutput⟩ :=
    ReturnAddressLower.Instr.lowerAt?_returnToken_parts hLower
  have hSite := ReturnAddressLower.siteForToken?_mem hFind
  obtain ⟨targetPc, hResolve⟩ := hTargets site hSite.1
  subst code
  subst output
  obtain ⟨targetAfter, sourceAfter, hTarget, hSource, hAfter,
      hTargetPc⟩ :=
    returnToken_openStepAt
      (assembly := pre ++ [.pushLabel site.target] ++ post)
      (currentPc := pre.byteLength) hFind hResolve hRel
  rw [show
      pre ++ [Assembly.Instr.pushLabel site.target] ++ post =
        pre ++ Assembly.Instr.pushLabel site.target :: post by
      simp [List.append_assoc]]
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  rw [Assembly.InteractionPreservation.source_openRunNResult_one_at_boundary
    (Assembly.Program.PCFitsFrom.start hFits) hPc]
  unfold Assembly.InteractionSemantics.Source.openStepAtResult
  have hTarget' :
      Assembly.InteractionSemantics.Source.openStepAt
          (pre ++ Assembly.Instr.pushLabel site.target :: post)
          pre.byteLength (.pushLabel site.target) target =
        Simulation.Interaction.pure targetAfter := by
    simpa using hTarget
  rw [hTarget']
  rw [TypedCfg.InteractionSemantics.Instr.openRunAt_eq_done_of_not_prim
    (by intro op hEq; cases hEq)]
  simp only [TypedCfg.Instr.runAt, ReturnAddressLower.type?_returnToken,
    Option.elim_some, hSource, Bind.bind, Except.bind]
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok
      ⟨by
          calc
            targetAfter.pc =
                target.pc + EvmYul.UInt256.ofNat 33 :=
              hTargetPc
            _ =
                pre.pcAfter + EvmYul.UInt256.ofNat 33 := by
              rw [hPc]
            _ =
                (pre ++
                  [Assembly.Instr.pushLabel site.target]).pcAfter :=
              by
                simpa [Assembly.Program.byteLength,
                  Assembly.Instr.byteSize] using
                  (Assembly.Program.pcAfter_append pre
                    [.pushLabel site.target]).symm,
        rfl, by simpa using hAfter⟩)

theorem lowerAt_openRunNResult_runtimeRel
    {cfg : TypedCfg.Program}
    {instr : TypedCfg.Instr} {input output : Shape}
    {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hLower :
      ReturnAddressLower.Instr.lowerAt? cfg instr input =
        some (code, output))
    (hTargets :
      ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
        ∃ pc, (pre ++ code ++ post).labelPc site.target = some pc)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        input target source) :
    Simulation.Interaction.Rel
      (LoweredInstrResultRel
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg) output
        (pre ++ code).pcAfter)
      (Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length target)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr input source) := by
  by_cases hReturn : ∃ token, instr = .returnToken token
  · obtain ⟨token, rfl⟩ := hReturn
    exact lowerAt_returnToken_openRunNResult_runtimeRel
      hLower hTargets hFits hPc hRel
  · have hNotReturnToken : ∀ token, instr ≠ .returnToken token := by
      intro token hEq
      exact hReturn ⟨token, hEq⟩
    exact lowerAt_openRunNResult_runtimeRel_of_not_returnToken
      hNotReturnToken hLower hFits hPc hRel

theorem lowerBodyFrom?_openRunNResult_runtimeRel
    {cfg : TypedCfg.Program}
    {body : List TypedCfg.Instr} {input output : Shape}
    {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hLower :
      ReturnAddressLower.Block.lowerBodyFrom? cfg body input =
        some (code, output))
    (hTargets :
      ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
        ∃ pc, (pre ++ code ++ post).labelPc site.target = some pc)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        input target source) :
    Simulation.Interaction.Rel
      (LoweredInstrResultRel
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg) output
        (pre ++ code).pcAfter)
      (Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length target)
      (TypedCfg.InteractionSemantics.Block.openRunBody
        body input source) := by
  induction body generalizing input output code pre post target source with
  | nil =>
      simp [ReturnAddressLower.Block.lowerBodyFrom?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.ok
          ⟨by simpa using hPc, rfl, by simpa using hRel⟩)
  | cons instr rest ih =>
      unfold ReturnAddressLower.Block.lowerBodyFrom? at hLower
      cases hHead :
          ReturnAddressLower.Instr.lowerAt? cfg instr input with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              ReturnAddressLower.Block.lowerBodyFrom?
                cfg rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hHeadFits :
                  Assembly.Program.PCFitsFrom pre head :=
                Assembly.Program.PCFitsFrom.left hFits
              have hTailFits :
                  Assembly.Program.PCFitsFrom (pre ++ head) tail :=
                Assembly.Program.PCFitsFrom.right hFits
              have hHeadTargets :
                  ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
                    ∃ pc,
                      (pre ++ head ++ (tail ++ post)).labelPc
                          site.target =
                        some pc := by
                simpa [List.append_assoc] using hTargets
              have hHeadRel :
                  RuntimeRel
                    (pre ++ head ++ (tail ++ post)).labelPc
                    (ReturnAddressLower.Program.returnSites cfg)
                    input target source := by
                simpa [List.append_assoc] using hRel
              have hHeadRun :=
                lowerAt_openRunNResult_runtimeRel
                  (post := tail ++ post) hHead hHeadTargets
                  hHeadFits hPc hHeadRel
              have hCombined :
                  Simulation.Interaction.Rel
                    (LoweredInstrResultRel
                      (pre ++ (head ++ tail) ++ post).labelPc
                      (ReturnAddressLower.Program.returnSites cfg)
                      tailOutput (pre ++ (head ++ tail)).pcAfter)
                    (Simulation.Interaction.bind
                      (Assembly.InteractionSemantics.Source.openRunNResult
                        (pre ++ (head ++ tail) ++ post)
                        head.length target)
                      (fun targetResult =>
                        match targetResult with
                        | .running targetAfter =>
                            Assembly.InteractionSemantics.Source.openRunNResult
                              (pre ++ (head ++ tail) ++ post)
                              tail.length targetAfter
                        | .halted halt =>
                            Simulation.Interaction.pure (.halted halt)))
                    (Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr input source)
                      (fun sourceResult =>
                        TypedCfg.InteractionSemantics.Block.openRunBody
                          rest sourceResult.2 sourceResult.1)) := by
                apply Simulation.Interaction.Rel.bind
                  (by simpa [List.append_assoc] using hHeadRun)
                intro targetResult sourceResult hResult
                rcases sourceResult with ⟨sourceAfter, actualOutput⟩
                cases targetResult with
                | halted halt =>
                    exact False.elim hResult
                | running targetAfter =>
                    have hOutput : actualOutput = headOutput :=
                      hResult.2.1
                    subst actualOutput
                    have hTailTargets :
                        ∀ site ∈
                            ReturnAddressLower.Program.returnSites cfg,
                          ∃ pc,
                            ((pre ++ head) ++ tail ++ post).labelPc
                                site.target =
                              some pc := by
                      simpa [List.append_assoc] using hTargets
                    have hTailRel :
                        RuntimeRel
                          ((pre ++ head) ++ tail ++ post).labelPc
                          (ReturnAddressLower.Program.returnSites cfg)
                          headOutput targetAfter sourceAfter := by
                      simpa [List.append_assoc] using hResult.2.2
                    simpa [List.append_assoc] using
                      (ih hTail hTailTargets hTailFits hResult.1 hTailRel)
              rw [List.length_append,
                Assembly.InteractionSemantics.Source.openRunNResult_add]
              simpa [TypedCfg.InteractionSemantics.Block.openRunBody,
                TypedCfg.Control.Block.runBody, List.append_assoc] using
                hCombined

def OutcomeRuntimeRel
    (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) :
    TypedCfg.Outcome → TypedCfg.Outcome → Prop
  | .fallthrough target, .fallthrough source =>
      RuntimeRel resolve sites output target source
  | .jump targetLabel target, .jump sourceLabel source =>
      targetLabel = sourceLabel ∧
        RuntimeRel resolve sites output target source
  | .returnDispatch target, .returnDispatch source =>
      RuntimeRel resolve sites output target source
  | .halt targetKind target, .halt sourceKind source =>
      targetKind = sourceKind ∧
        RuntimeRel resolve sites output target source
  | .invalid _, .invalid _ => True
  | _, _ => False

abbrev TypedOutcomeRuntimeRel
    (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) :
    Except Assembly.EVMException TypedCfg.Outcome →
      Except Assembly.EVMException TypedCfg.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun targetError sourceError => targetError = sourceError)
    (OutcomeRuntimeRel resolve sites output)

def LoweredTerminatorResultRel
    (program : Assembly.Program)
    (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) :
    Assembly.Source.ExecutionOutcome →
      Except Assembly.EVMException TypedCfg.Outcome → Prop :=
  fun target source =>
    ∃ middle,
      TypedCfg.Preservation.Block.RunSimulates
          program middle target ∧
        TypedOutcomeRuntimeRel resolve sites output middle source

/--
Whole-block result relation for the physical-return lowering.

The adjacent stack-suffix lemmas intentionally forget the identity of runtime
errors.  Successful outcomes retain the stronger terminator relation; error
outcomes are refined to the public structural-error relation later, using the
Assembly owner's `NotOutOfFuel` theorem.
-/
def LoweredBlockResultRel
    (program : Assembly.Program)
    (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) (output : Shape) :
    Assembly.Source.ExecutionOutcome →
      Except Assembly.EVMException TypedCfg.Outcome → Prop
  | .error _, .error _ => True
  | target, .ok source =>
      LoweredTerminatorResultRel program resolve sites output
        target (.ok source)
  | .ok _, .error _ => False

theorem LoweredTerminatorResultRel.toBlock
    {program : Assembly.Program}
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {output : Shape}
    {target : Assembly.Source.ExecutionOutcome}
    {source : Except Assembly.EVMException TypedCfg.Outcome}
    (hRel :
      LoweredTerminatorResultRel program resolve sites output
        target source) :
    LoweredBlockResultRel program resolve sites output target source := by
  cases source with
  | ok source =>
      simpa [LoweredBlockResultRel] using hRel
  | error sourceError =>
      cases target with
      | error targetError =>
          trivial
      | ok targetResult =>
          rcases hRel with ⟨middle, hTarget, hSource⟩
          cases middle with
          | error middleError =>
              cases hTarget
          | ok middleOutcome =>
              cases hSource

namespace CompiledBlock

/--
Execute one physical-return-lowered block through the canonical Assembly
runners.  This is the ordinary compiled-block adapter with only the lowering
functions changed.
-/
def openRun (cfg : TypedCfg.Program) (block : TypedCfg.Block)
    (program : Assembly.Program) (state : Assembly.EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match ReturnAddressLower.Block.lowerBodyFrom?
      cfg block.body block.input with
  | none =>
      .done (.error .InvalidInstruction)
  | some (bodyCode, output) =>
      if output = block.output then
        match ReturnAddressLower.Terminator.lowerAt?
            output block.term with
        | none =>
            .done (.error .InvalidInstruction)
        | some termCode => do
            let labelResult ←
              Assembly.InteractionSemantics.Source.openRunNResult
                program 1 state
            match labelResult with
            | .halted halt =>
                pure (.halted halt)
            | .running entry =>
                let bodyResult ←
                  Assembly.InteractionSemantics.Source.openRunNResult
                    program bodyCode.length entry
                match bodyResult with
                | .halted halt =>
                    pure (.halted halt)
                | .running mid =>
                    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                        block.term)
                      program termCode.length mid
      else
        .done (.error .InvalidInstruction)

end CompiledBlock

namespace CompiledProgram

/-- Select a physical-return-lowered block from the concrete label at `pc`. -/
def openStep (source : TypedCfg.Program)
    (target : Assembly.Program) (state : Assembly.EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match target.instrAtPc state.pc.toNat with
  | some (_, .label label) =>
      match source.findBlock? label with
      | some block =>
          CompiledBlock.openRun source block target state
      | none =>
          .done (.error .InvalidInstruction)
  | _ =>
      .done (.error .InvalidInstruction)

def openRunN (source : TypedCfg.Program)
    (target : Assembly.Program) (fuel : Nat)
    (state : Assembly.EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  Assembly.Control.runNResultWith
    (openStep source target) fuel state

@[simp] theorem openRunN_zero
    (source : TypedCfg.Program) (target : Assembly.Program)
    (state : Assembly.EVMState) :
    openRunN source target 0 state =
      .done (.ok (.running state)) := rfl

theorem openRunN_succ
    (source : TypedCfg.Program) (target : Assembly.Program)
    (fuel : Nat) (state : Assembly.EVMState) :
    openRunN source target (fuel + 1) state =
      (do
        let result ← openStep source target state
        match result with
        | .running state' =>
            openRunN source target fuel state'
        | .halted halt =>
            pure (.halted halt)) := rfl

end CompiledProgram

def terminatorOutputShape (shape : Shape) :
    TypedCfg.Terminator → Shape
  | .jumpi _ _ => Shape.pop 1 shape
  | .returnDispatch _ _ =>
      match shape.returnTokenDepth? with
      | some depth => shape.erase depth
      | none => shape
  | _ => shape

/--
Whole-program invariant.  Residual jumps carry a re-seeded entry-shape
relation; completed non-jump outcomes retain the block result witness.
-/
def ProgramRunResultRel
    (cfg : TypedCfg.Program) (assembly : Assembly.Program)
    (resolve : ReturnAddressRelation.Resolver)
    (sites : List ReturnSite) :
    Assembly.Source.ExecutionOutcome →
      Except Assembly.EVMException TypedCfg.Outcome → Prop
  | .error _, .error _ => True
  | .error _, .ok (.jump _ _) => False
  | _, .ok (.fallthrough _) => False
  | _, .ok (.returnDispatch _) => False
  | .ok target, .ok (.jump label source) =>
      match target with
      | .halted _ => False
      | .running targetState =>
          ∃ block dest,
            cfg.findBlock? label = some block ∧
              assembly.labelPc label = some dest ∧
              targetState.pc = EvmYul.UInt256.ofNat dest ∧
              RuntimeRel resolve sites block.input
                targetState.incrPC source
  | target, .ok (.halt kind source) =>
      ∃ output,
        kind.argCount ≤ output.length ∧
          ReturnAddressRelation.PlainSlots
              (output.slots.take kind.argCount) ∧
            LoweredBlockResultRel assembly resolve sites output
              target (.ok (.halt kind source))
  | target, .ok source =>
      ∃ output,
        LoweredBlockResultRel assembly resolve sites output
          target (.ok source)
  | .ok _, .error _ => False

def BlockJumpTarget (term : TypedCfg.Terminator) :
    Except Assembly.EVMException TypedCfg.Outcome → Prop
  | .ok (.jump target _) => target ∈ term.targets
  | .ok (.fallthrough _) => False
  | .ok (.returnDispatch _) => False
  | .ok (.halt kind _) => term = .halt kind
  | _ => True

theorem runTerm_jump_mem_targets
    {shape : Shape} {term : TypedCfg.Terminator}
    {state final : Assembly.EVMState} {next : Label}
    (hRun :
      TypedCfg.Block.runTerm shape term state =
        .jump next final) :
    next ∈ term.targets := by
  cases term with
  | fallthrough target =>
      rw [TypedCfg.Block.runTerm] at hRun
      simp only [TypedCfg.Outcome.jump.injEq] at hRun
      simp [TypedCfg.Terminator.targets, hRun.1]
  | jump target =>
      rw [TypedCfg.Block.runTerm] at hRun
      simp only [TypedCfg.Outcome.jump.injEq] at hRun
      simp [TypedCfg.Terminator.targets, hRun.1]
  | jumpi target fallthrough =>
      rw [TypedCfg.Block.runTerm] at hRun
      split at hRun
      · simp at hRun
      · split at hRun <;>
          (simp only [TypedCfg.Outcome.jump.injEq] at hRun
           simp [TypedCfg.Terminator.targets, hRun.1])
  | returnDispatch returnCount sites =>
      rw [TypedCfg.Block.runTerm] at hRun
      split at hRun
      · simp at hRun
      · split at hRun
        · simp at hRun
        · split at hRun
          · simp at hRun
          · split at hRun
            · simp at hRun
            · rename_i hFind
              simp only [TypedCfg.Outcome.jump.injEq] at hRun
              obtain ⟨site, hSite, hTarget⟩ :=
                TypedCfg.Block.ReturnSite.mem_of_findTarget?_eq_some
                  hFind
              exact
                List.mem_map.mpr
                  ⟨site, hSite, hTarget.trans hRun.1⟩
  | halt kind =>
      rw [TypedCfg.Block.runTerm] at hRun
      simp at hRun
  | invalid =>
      rw [TypedCfg.Block.runTerm] at hRun
      simp at hRun

theorem runTerm_halt_eq
    {shape : Shape} {term : TypedCfg.Terminator}
    {state final : Assembly.EVMState} {kind : Assembly.HaltKind}
    (hRun :
      TypedCfg.Block.runTerm shape term state =
        .halt kind final) :
    term = .halt kind := by
  cases term with
  | fallthrough target
  | jump target =>
      simp [TypedCfg.Block.runTerm] at hRun
  | jumpi target fallthrough
  | returnDispatch returnCount sites =>
      simp only [TypedCfg.Block.runTerm] at hRun
      repeat' split at hRun
      all_goals simp at hRun
  | halt actual =>
      simp only [TypedCfg.Block.runTerm,
        TypedCfg.Outcome.halt.injEq] at hRun
      exact congrArg TypedCfg.Terminator.halt hRun.1
  | invalid =>
      simp [TypedCfg.Block.runTerm] at hRun

theorem block_openRun_jumpTarget
    (block : TypedCfg.Block) (state : Assembly.EVMState) :
    Simulation.Interaction.AllDone
      (BlockJumpTarget block.term)
      (TypedCfg.InteractionSemantics.Block.openRun block state) := by
  unfold TypedCfg.InteractionSemantics.Block.openRun
    TypedCfg.Control.Block.run
  apply
    Simulation.Interaction.AllDone.bind
      (Simulation.Interaction.AllDone.trivial
        (TypedCfg.InteractionSemantics.Block.openRunBody
          block.body block.input state))
  · intro error _
    trivial
  · intro result _
    rcases result with ⟨final, output⟩
    by_cases hOutput : output = block.output
    · subst output
      simp only [if_pos rfl]
      cases hChecked :
          TypedCfg.Block.runTermChecked
            block.output block.term final with
      | error error =>
          exact Simulation.Interaction.AllDone.done trivial
      | ok outcome =>
          apply Simulation.Interaction.AllDone.done
          have hRun :
              TypedCfg.Block.runTerm
                  block.output block.term final =
                outcome :=
            TypedCfg.Block.runTerm_eq_of_runTermChecked_eq_ok
              hChecked
          cases hOutcome : outcome with
          | jump next jumpState =>
              exact
                runTerm_jump_mem_targets
                  (hRun.trans hOutcome)
          | fallthrough fallthroughState =>
              exact
                (TypedCfg.Block.runTerm_ne_fallthrough
                  block.output block.term final
                  fallthroughState
                  (hRun.trans hOutcome)).elim
          | returnDispatch dispatchState =>
              exact
                (TypedCfg.Block.runTerm_ne_returnDispatch
                  block.output block.term final
                  dispatchState
                  (hRun.trans hOutcome)).elim
          | halt kind haltState =>
              exact
                runTerm_halt_eq
                  (hRun.trans hOutcome)
          | invalid invalidState =>
              trivial
    · simp only [if_neg hOutput]
      exact Simulation.Interaction.AllDone.done trivial

theorem pop_runtimeRel_of_plain_top
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {shape : Shape}
    {target source : Assembly.EVMState}
    (hNonempty : shape.slots ≠ [])
    (hPlain : PlainSlots (shape.slots.take 1))
    (hRel : RuntimeRel resolve sites shape target source) :
    ∃ condition targetRest sourceRest,
      target.stack.pop = some (targetRest, condition) ∧
        source.stack.pop = some (sourceRest, condition) ∧
          RuntimeRel resolve sites (Shape.pop 1 shape)
            { target with stack := targetRest }
            { source with stack := sourceRest } := by
  rcases shape with ⟨slots, tail⟩
  cases slots with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons slot rest =>
      have hTopPlain : PlainSlot slot :=
        hPlain slot (by simp)
      cases hTargetStack : target.stack with
      | nil =>
          have hFalse := hRel.2
          exact False.elim
            (by
              simpa [ShapeStackRel, StackRel,
                hTargetStack] using hFalse)
      | cons targetTop targetRest =>
          cases hSourceStack : source.stack with
          | nil =>
              have hFalse := hRel.2
              exact False.elim
                (by
                  simpa [ShapeStackRel, StackRel,
                    hTargetStack, hSourceStack] using hFalse)
          | cons sourceTop sourceRest =>
              have hStack :
                  SlotWordRel resolve sites slot targetTop sourceTop ∧
                    StackRel resolve sites rest tail
                      targetRest sourceRest := by
                simpa [ShapeStackRel, hTargetStack,
                  hSourceStack] using hRel.2
              have hTop : targetTop = sourceTop := by
                cases slot <;>
                  simp [PlainSlot, SlotWordRel] at hTopPlain hStack ⊢
                all_goals exact hStack.1
              subst sourceTop
              refine ⟨targetTop, targetRest, sourceRest, ?_, ?_, ?_⟩
              · simp [EvmYul.Stack.pop, hTargetStack]
              · simp [EvmYul.Stack.pop, hSourceStack]
              · constructor
                · simpa using hRel.1
                · simpa [ShapeStackRel, Shape.pop] using hStack.2

theorem runTermChecked_runtimeRel_of_not_returnDispatch
    {cfg : TypedCfg.Program}
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite}
    {shape : Shape} {term : TypedCfg.Terminator}
    {target source : Assembly.EVMState}
    (hNotReturnDispatch :
      ∀ returnCount returnSites,
        term ≠ .returnDispatch returnCount returnSites)
    (hType : term.type? cfg shape = some ())
    (hSafe : ReturnAddressLower.Terminator.Safe shape term)
    (hRel : RuntimeRel resolve sites shape target source) :
    TypedOutcomeRuntimeRel resolve sites
      (terminatorOutputShape shape term)
      (TypedCfg.Block.runTermChecked shape term target)
      (TypedCfg.Block.runTermChecked shape term source) := by
  cases term with
  | fallthrough next =>
      exact Simulation.Interaction.ExceptRel.ok
        (by simpa [terminatorOutputShape, OutcomeRuntimeRel,
          TypedCfg.Block.runTerm] using hRel)
  | jump next =>
      exact Simulation.Interaction.ExceptRel.ok
        (by simpa [terminatorOutputShape, OutcomeRuntimeRel,
          TypedCfg.Block.runTerm] using hRel)
  | jumpi targetLabel nextLabel =>
      have hPlain :
          PlainSlots (shape.slots.take 1) := hSafe
      have hNonempty : shape.slots ≠ [] := by
        intro hEmpty
        simp [TypedCfg.Terminator.type?,
          TypedCfg.Terminator.typeWith?, hEmpty] at hType
      obtain ⟨condition, targetRest, sourceRest,
          hTargetPop, hSourcePop, hAfter⟩ :=
        pop_runtimeRel_of_plain_top hNonempty hPlain hRel
      by_cases hZero : condition = EvmYul.UInt256.ofNat 0
      · subst condition
        exact Simulation.Interaction.ExceptRel.ok
          (by
            simpa [terminatorOutputShape, OutcomeRuntimeRel,
              TypedCfg.Block.runTerm, hTargetPop, hSourcePop] using
              hAfter)
      · exact Simulation.Interaction.ExceptRel.ok
          (by
            simpa [terminatorOutputShape, OutcomeRuntimeRel,
              TypedCfg.Block.runTerm, hTargetPop, hSourcePop,
              hZero] using hAfter)
  | returnDispatch returnCount returnSites =>
      exact False.elim
        (hNotReturnDispatch returnCount returnSites rfl)
  | halt kind =>
      have hPermission :
          target.executionEnv.perm = source.executionEnv.perm := by
        simpa using congrArg
          (fun shared => shared.executionEnv.perm) hRel.1
      cases kind with
      | stop | «return» | revert =>
          exact Simulation.Interaction.ExceptRel.ok
            (by simpa [terminatorOutputShape, OutcomeRuntimeRel,
              TypedCfg.Block.runTerm] using hRel)
      | selfdestruct =>
          cases hTargetPermission : target.executionEnv.perm with
          | false =>
              have hSourcePermission :
                  source.executionEnv.perm = false := by
                rw [← hPermission]
                exact hTargetPermission
              have hDone :
                  TypedOutcomeRuntimeRel resolve sites shape
                    (.error .StaticModeViolation)
                    (.error .StaticModeViolation) :=
                Simulation.Interaction.ExceptRel.error rfl
              simpa [TypedCfg.Block.runTermChecked,
                hTargetPermission, hSourcePermission,
                terminatorOutputShape] using hDone
          | true =>
              have hSourcePermission :
                  source.executionEnv.perm = true := by
                rw [← hPermission]
                exact hTargetPermission
              have hOutcome :
                  OutcomeRuntimeRel resolve sites shape
                    (.halt .selfdestruct target)
                    (.halt .selfdestruct source) := by
                simpa [OutcomeRuntimeRel] using hRel
              have hDone :
                  TypedOutcomeRuntimeRel resolve sites shape
                    (.ok (.halt .selfdestruct target))
                    (.ok (.halt .selfdestruct source)) :=
                Simulation.Interaction.ExceptRel.ok hOutcome
              simpa [TypedCfg.Block.runTermChecked,
                hTargetPermission, hSourcePermission,
                terminatorOutputShape, TypedCfg.Block.runTerm] using hDone
  | invalid =>
      exact Simulation.Interaction.ExceptRel.ok
        (by simp [terminatorOutputShape, OutcomeRuntimeRel,
          TypedCfg.Block.runTerm])

theorem lowerAt_openRunUntilTransfer_runtimeRel_of_not_returnDispatch
    {cfg : TypedCfg.Program}
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hNotReturnDispatch :
      ∀ returnCount returnSites,
        term ≠ .returnDispatch returnCount returnSites)
    (hType : term.type? cfg shape = some ())
    (hLower :
      ReturnAddressLower.Terminator.lowerAt? shape term = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        shape target source) :
    Simulation.Interaction.Rel
      (LoweredTerminatorResultRel
        (pre ++ code ++ post)
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (terminatorOutputShape shape term))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy term)
        (pre ++ code ++ post) code.length target)
      (.done (TypedCfg.Block.runTermChecked shape term source)) := by
  have hStandard :=
    ReturnAddressLower.Terminator.standard_lowerAt?_of_lowerAt?_not_returnDispatch
      hNotReturnDispatch hLower
  have hSafe :=
    ReturnAddressLower.Terminator.safe_of_lowerAt? hLower
  have hTyped :=
    runTermChecked_runtimeRel_of_not_returnDispatch
      hNotReturnDispatch hType hSafe hRel
  have hStandardRun :=
    TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel
      hStandard hFits hPc hResolved hLabels
  have hTypedRun :
      Simulation.Interaction.Rel
        (TypedOutcomeRuntimeRel
          (pre ++ code ++ post).labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          (terminatorOutputShape shape term))
        (.done (TypedCfg.Block.runTermChecked shape term target))
        (.done (TypedCfg.Block.runTermChecked shape term source)) :=
    Simulation.Interaction.Rel.done hTyped
  have hTrans :=
    Simulation.Interaction.Rel.trans hStandardRun.symm hTypedRun
  apply Simulation.Interaction.Rel.mono hTrans
  intro targetDone sourceDone hDone
  exact hDone

theorem jumpDynamic_eventually
    {pre post : Assembly.Program} {state : Assembly.EVMState}
    {destination : Word} {stack : List Word}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hStack : state.stack = destination :: stack) :
    Assembly.Source.Eventually
      (pre ++ [.jumpDynamic] ++ post) state
      (fun outcome =>
        outcome = .ok (.running { state with pc := destination, stack := stack })) := by
  refine ⟨1, .ok (.running { state with pc := destination, stack := stack }), ?_, rfl⟩
  rw [show pre ++ [.jumpDynamic] ++ post =
      pre ++ .jumpDynamic :: post by simp [List.append_assoc]]
  rw [Assembly.InteractionPreservation.source_runNResult_one_at_boundary
    hFits hPc]
  simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
    Assembly.Target.stepInstr, Assembly.Target.stepInstrWith, hStack,
    EvmYul.Stack.pop, Assembly.Instr.haltKind?]

def ReturnGuardInstr : Assembly.Instr → Prop
  | .push _ => True
  | .pushLabel _ => True
  | .prim .dup1
  | .prim .dup2
  | .prim .eq
  | .prim .or
  | .prim .mul
  | .prim .add => True
  | _ => False

theorem returnGuardInstr_openStepAt
    {program : Assembly.Program} {pc : Nat}
    {instr : Assembly.Instr} {state : Assembly.EVMState}
    (hGuard : ReturnGuardInstr instr) :
    Assembly.InteractionSemantics.Source.openStepAt
        program pc instr state =
      .done (Assembly.Source.stepAt program pc instr state) := by
  cases instr with
  | push value => rfl
  | pushLabel label => rfl
  | prim op =>
      cases op <;> simp [ReturnGuardInstr] at hGuard
      all_goals
        exact
          Assembly.InteractionPreservation.source_openStepAt_prim_closed
            (by decide) (by decide) (by decide)
  | label label | jump label | jumpi label
  | jumpDynamic =>
      cases hGuard

theorem returnGuardInstr_flow_next
    (continueTransfer : Assembly.Instr → Bool)
    {instr : Assembly.Instr} {state final : Assembly.EVMState}
    (hGuard : ReturnGuardInstr instr) :
    instr.classifyFlowWith continueTransfer state (.running final) =
      .next final := by
  cases instr with
  | push value => rfl
  | pushLabel label => rfl
  | prim op =>
      cases op <;> simp [ReturnGuardInstr] at hGuard
      all_goals rfl
  | label label | jump label | jumpi label
  | jumpDynamic =>
      cases hGuard

theorem returnGuardInstr_step_pc
    {program : Assembly.Program} {pc : Nat}
    {instr : Assembly.Instr} {state final : Assembly.EVMState}
    (hGuard : ReturnGuardInstr instr)
    (hStep :
      Assembly.Source.stepAtResult program pc instr state =
        .ok (.running final)) :
    final.pc =
      state.pc + EvmYul.UInt256.ofNat instr.byteSize := by
  cases instr with
  | push value =>
      unfold Assembly.Source.stepAtResult Assembly.Source.stepAt at hStep
      simp [Assembly.Instr.haltKind?, Assembly.Target.stepInstr,
        EvmYul.Stack.push] at hStep
      subst final
      simp [Assembly.Instr.byteSize,
        Assembly.Instr.push32Size,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | pushLabel label =>
      unfold Assembly.Source.stepAtResult Assembly.Source.stepAt at hStep
      cases hDest : program.labelPc label with
      | none =>
          simp [hDest, Assembly.Source.invalid] at hStep
      | some dest =>
          simp [hDest, Assembly.Instr.haltKind?,
            Assembly.Target.stepInstr,
            EvmYul.Stack.push] at hStep
          subst final
          simp [Assembly.Instr.byteSize,
            Assembly.Instr.push32Size,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | prim op =>
      have hNoHalt :
          (Assembly.Instr.prim op).haltKind? = none := by
        cases op <;> simp [ReturnGuardInstr] at hGuard
        all_goals rfl
      have hRun : op.step state = .ok final := by
        simp only [Assembly.Source.stepAtResult,
          Assembly.Source.stepAt, hNoHalt,
          Assembly.Target.stepInstrWith_prim] at hStep
        cases hOp : op.step state with
        | error err =>
            simp [hOp] at hStep
        | ok opFinal =>
            simp [hOp] at hStep
            subst opFinal
            rfl
      cases op <;> simp [ReturnGuardInstr] at hGuard
      all_goals
        have hPc :=
          Assembly.PrimOp.step_pc_of_stackArity
            (state := state) (final := final) (by rfl) hRun
        simpa [Assembly.Instr.byteSize] using hPc
  | label label | jump label | jumpi label
  | jumpDynamic =>
      cases hGuard

theorem returnGuardCode_openRunUntilTransferWithPolicy
    (continueTransfer : Assembly.Instr → Bool)
    {code pre post : Assembly.Program}
    {state final : Assembly.EVMState}
    (fuel : Nat)
    (hGuard : ∀ instr ∈ code, ReturnGuardInstr instr)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hRun :
      Assembly.Source.runNResult
          (pre ++ code ++ post) code.length state =
        .ok (.running final)) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ code ++ post)
        (fuel + code.length) state =
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ code ++ post) fuel final := by
  induction code generalizing pre state with
  | nil =>
      simp [Assembly.Source.runNResult,
        Assembly.Control.runNResultWith] at hRun
      subst final
      simp
  | cons instr rest ih =>
      have hInstrGuard : ReturnGuardInstr instr :=
        hGuard instr (by simp)
      have hRestGuard :
          ∀ candidate ∈ rest, ReturnGuardInstr candidate := by
        intro candidate hCandidate
        exact hGuard candidate (by simp [hCandidate])
      have hHeadFits : pre.PCFits := hFits.1
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ [instr]) rest := by
        simpa [List.append_assoc] using hFits.2
      cases hStep :
          Assembly.Source.stepResult
            (pre ++ instr :: rest ++ post) state with
      | error err =>
          have hImpossible := hRun
          have hStep' :
              Assembly.Source.stepResult
                  (pre ++ instr :: (rest ++ post)) state =
                .error err := by
            simpa [List.append_assoc] using hStep
          simp [Assembly.Source.runNResult,
            Assembly.Control.runNResultWith, hStep'] at hImpossible
      | ok result =>
          cases result with
          | halted halt =>
              have hImpossible := hRun
              have hStep' :
                  Assembly.Source.stepResult
                      (pre ++ instr :: (rest ++ post)) state =
                    .ok (.halted halt) := by
                simpa [List.append_assoc] using hStep
              simp [Assembly.Source.runNResult,
                Assembly.Control.runNResultWith, hStep'] at hImpossible
          | running mid =>
              have hStep' :
                  Assembly.Source.stepResult
                      (pre ++ instr :: (rest ++ post)) state =
                    .ok (.running mid) := by
                simpa [List.append_assoc] using hStep
              have hStepAt :
                  Assembly.Source.stepAtResult
                      (pre ++ instr :: rest ++ post)
                      pre.byteLength instr state =
                    .ok (.running mid) := by
                have hStepAt' :
                    Assembly.Source.stepAtResult
                        (pre ++ instr :: (rest ++ post))
                        pre.byteLength instr state =
                      .ok (.running mid) := by
                  rw [←
                    Assembly.InteractionPreservation.source_stepResult_at_boundary
                      (pre := pre) (post := rest ++ post)
                      (instr := instr) (state := state)
                      hHeadFits hPc]
                  exact hStep'
                simpa [List.append_assoc] using hStepAt'
              have hOpenAt :
                  Assembly.InteractionSemantics.Source.openStepAtResult
                      (pre ++ instr :: rest ++ post)
                      pre.byteLength instr state =
                    .done (.ok (.running mid)) := by
                rw [
                  Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
                    (returnGuardInstr_openStepAt hInstrGuard)]
                exact congrArg Simulation.Interaction.done hStepAt
              have hMidPc :
                  mid.pc = (pre ++ [instr]).pcAfter := by
                calc
                  mid.pc =
                      state.pc +
                        EvmYul.UInt256.ofNat instr.byteSize :=
                    returnGuardInstr_step_pc hInstrGuard hStepAt
                  _ =
                      pre.pcAfter +
                        EvmYul.UInt256.ofNat instr.byteSize := by
                    rw [hPc]
                  _ = (pre ++ [instr]).pcAfter :=
                    (Assembly.Program.pcAfter_snoc pre instr).symm
              have hTailRun :
                  Assembly.Source.runNResult
                      ((pre ++ [instr]) ++ rest ++ post)
                      rest.length mid =
                    .ok (.running final) := by
                have hRun' := hRun
                simp only [List.length_cons] at hRun'
                unfold Assembly.Source.runNResult
                  Assembly.Control.runNResultWith at hRun'
                rw [hStep] at hRun'
                simp only [Bind.bind, Except.bind] at hRun'
                simpa [List.append_assoc] using hRun'
              have hHeadOpen :=
                Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_running
                  continueTransfer
                  (pre := pre) (post := rest ++ post)
                  (instr := instr) (state := state) (final := mid)
                  (fuel := fuel + rest.length)
                  hHeadFits hPc
                  (by simpa [List.append_assoc] using hOpenAt)
                  (returnGuardInstr_flow_next
                    continueTransfer hInstrGuard)
              have hTailOpen :=
                ih
                  (pre := pre ++ [instr]) (state := mid)
                  hRestGuard hTailFits hMidPc hTailRun
              rw [show
                fuel + (instr :: rest).length =
                  (fuel + rest.length) + 1 by
                simp
                omega]
              have hHeadOpen' :
                  Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      continueTransfer
                      (pre ++ instr :: rest ++ post)
                      ((fuel + rest.length) + 1) state =
                    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      continueTransfer
                      (pre ++ instr :: rest ++ post)
                      (fuel + rest.length) mid := by
                simpa [List.append_assoc] using hHeadOpen
              rw [hHeadOpen']
              simpa [List.append_assoc] using hTailOpen

theorem dynamicReturnTests_returnGuard
    (sites : List ReturnSite) :
    ∀ instr ∈
        ReturnAddressLower.Terminator.dynamicReturnTests sites,
      ReturnGuardInstr instr := by
  intro instr hInstr
  cases sites with
  | nil =>
      simp [ReturnAddressLower.Terminator.dynamicReturnTests] at hInstr
  | cons first rest =>
      simp only [
        ReturnAddressLower.Terminator.dynamicReturnTests,
        ReturnAddressLower.Terminator.dynamicReturnFirstTest,
        ReturnAddressLower.Terminator.dynamicReturnNextTest,
        Assembly.StackShuffle.dupInstr,
        List.mem_append, List.mem_cons, List.mem_singleton,
        List.mem_flatMap] at hInstr
      rcases hInstr with
        hInstr | ⟨site, _hSite, hInstr⟩
      · rcases hInstr with rfl | rfl | rfl | hImpossible
        all_goals simp_all [ReturnGuardInstr]
      · rcases hInstr with rfl | rfl | rfl | rfl | hImpossible
        all_goals simp_all [ReturnGuardInstr]

theorem dynamicReturnTail_openRunUntilTransferWithPolicy
    {caseLabel : Label} {accumulator token : Word}
    {suffix : List Word} {pre post : Assembly.Program}
    {state : Assembly.EVMState}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [ .jumpi caseLabel
        , .prim .invalid
        , .label caseLabel
        , .jumpDynamic
        ])
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hLabels :
      ((pre ++
          [ Assembly.Instr.jumpi caseLabel
          , Assembly.Instr.prim .invalid
          , Assembly.Instr.label caseLabel
          , Assembly.Instr.jumpDynamic
          ] ++ post).labels).Nodup) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++
          [ .jumpi caseLabel
          , .prim .invalid
          , .label caseLabel
          , .jumpDynamic
          ] ++ post)
        4
        { state with stack := accumulator :: token :: suffix } =
      if accumulator = EvmYul.UInt256.ofNat 0 then
        .done (.error .InvalidInstruction)
      else
        .done
          (.ok
            (.running
              { state with stack := suffix, pc := token })) := by
  let tail : Assembly.Program :=
    [ .jumpi caseLabel
    , .prim .invalid
    , .label caseLabel
    , .jumpDynamic
    ]
  let start : Assembly.EVMState :=
    { state with stack := accumulator :: token :: suffix }
  have hStatePc : state.pc = pre.pcAfter := by
    simpa using hPc
  let casePre : Assembly.Program :=
    pre ++ [.jumpi caseLabel, .prim .invalid]
  have hProgramAtLabel :
      pre ++ tail ++ post =
        casePre ++
          Assembly.Instr.label caseLabel ::
            (Assembly.Instr.jumpDynamic :: post) := by
    simp [tail, casePre, List.append_assoc]
  have hLabelPc :
      (pre ++ tail ++ post).labelPc caseLabel =
        some casePre.byteLength := by
    rw [hProgramAtLabel]
    exact
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        casePre (Assembly.Instr.jumpDynamic :: post)
        (by
          rw [← hProgramAtLabel]
          simpa [tail] using hLabels)
  have hLabelPcAssoc :
      (pre ++ (tail ++ post)).labelPc caseLabel =
        some casePre.byteLength := by
    simpa [List.append_assoc] using hLabelPc
  have hJumpiFits : pre.PCFits :=
    Assembly.Program.PCFitsFrom.start hFits
  have hAfterJumpiFits :
      Assembly.Program.PCFitsFrom
        (pre ++ [.jumpi caseLabel])
        [ .prim .invalid
        , .label caseLabel
        , .jumpDynamic
        ] := by
    simpa [List.append_assoc] using hFits.2
  have hAfterInvalidFits :
      Assembly.Program.PCFitsFrom casePre
        [.label caseLabel, .jumpDynamic] := by
    simpa [casePre, List.append_assoc] using hAfterJumpiFits.2
  have hAfterLabelFits :
      Assembly.Program.PCFitsFrom
        (casePre ++ [.label caseLabel])
        [.jumpDynamic] := by
    simpa [List.append_assoc] using hAfterInvalidFits.2
  by_cases hZero :
      accumulator = EvmYul.UInt256.ofNat 0
  · let afterJumpi : Assembly.EVMState :=
      { state with
        stack := token :: suffix
        pc :=
          (pre ++ [Assembly.Instr.jumpi caseLabel]).pcAfter }
    have hJumpiOpen :
        Assembly.InteractionSemantics.Source.openStepAtResult
            (pre ++ tail ++ post)
            pre.byteLength (.jumpi caseLabel) start =
          .done (.ok (.running afterJumpi)) := by
      rw [
        Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
          (by rfl)]
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Instr.haltKind?, hLabelPcAssoc,
        start, afterJumpi, hStatePc,
        hZero, Assembly.Source.jumpiFallthroughPc,
        Assembly.Program.pcAfter_snoc,
        Assembly.Instr.byteSize, Assembly.Instr.jumpSize,
        Assembly.Instr.push32Size, Assembly.UInt256_ofNat_add,
        Assembly.UInt256_add_assoc, Nat.add_assoc,
        EvmYul.Stack.pop,
        TypedCfg.Preservation.uint256_bne_zero_self]
    have hJumpiFlow :
        (Assembly.Instr.jumpi caseLabel).classifyFlowWith
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            start (.running afterJumpi) =
          .next afterJumpi := by
      simp [Assembly.Instr.classifyFlowWith,
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy,
        start, hZero, EvmYul.Stack.pop]
    have hJumpiRun :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 4 start =
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 3 afterJumpi := by
      have hRun :=
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_running
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre := pre)
          (post :=
            [.prim .invalid, .label caseLabel, .jumpDynamic] ++ post)
          (instr := .jumpi caseLabel) (state := start)
          (final := afterJumpi) 3 hJumpiFits
          (by simpa [start] using hPc)
          (by simpa [tail, List.append_assoc] using hJumpiOpen)
          hJumpiFlow
      simpa [tail, List.append_assoc] using hRun
    have hInvalidOpen :
        Assembly.InteractionSemantics.Source.openStepAtResult
            ((pre ++ [Assembly.Instr.jumpi caseLabel]) ++
              Assembly.Instr.prim .invalid ::
                (Assembly.Instr.label caseLabel ::
                  Assembly.Instr.jumpDynamic :: post))
            (pre ++
              [Assembly.Instr.jumpi caseLabel]).byteLength
            (.prim .invalid) afterJumpi =
          .done (.error .InvalidInstruction) := by
      rw [
        Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
          (Assembly.InteractionPreservation.source_openStepAt_prim_closed
            (by rfl) (by decide) (by decide))]
      rfl
    have hInvalidRun :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 3 afterJumpi =
          .done (.error .InvalidInstruction) := by
      have hRun :=
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_error
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre := pre ++ [Assembly.Instr.jumpi caseLabel])
          (post :=
            [.label caseLabel, .jumpDynamic] ++ post)
          (instr := .prim .invalid) (state := afterJumpi)
          (err := .InvalidInstruction) 2
          (Assembly.Program.PCFitsFrom.start hAfterJumpiFits)
          (by simp [afterJumpi])
          (by simpa [List.append_assoc] using hInvalidOpen)
      simpa [tail, List.append_assoc] using hRun
    simpa [hZero, start, tail] using
      hJumpiRun.trans hInvalidRun
  · let afterJumpi : Assembly.EVMState :=
      { state with
        stack := token :: suffix
        pc := EvmYul.UInt256.ofNat casePre.byteLength }
    let afterLabel : Assembly.EVMState := afterJumpi.incrPC
    let final : Assembly.EVMState :=
      { state with stack := suffix, pc := token }
    have hNonzero :
        (accumulator != EvmYul.UInt256.ofNat 0) = true :=
      TypedCfg.Preservation.uint256_bne_zero_of_ne
        accumulator hZero
    have hJumpiOpen :
        Assembly.InteractionSemantics.Source.openStepAtResult
            (pre ++ tail ++ post)
            pre.byteLength (.jumpi caseLabel) start =
          .done (.ok (.running afterJumpi)) := by
      rw [
        Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
          (by rfl)]
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Instr.haltKind?, hLabelPcAssoc,
        start, afterJumpi, hNonzero, EvmYul.Stack.pop]
    have hJumpiFlow :
        (Assembly.Instr.jumpi caseLabel).classifyFlowWith
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            start (.running afterJumpi) =
          .next afterJumpi := by
      simp [Assembly.Instr.classifyFlowWith,
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy,
        start, hZero, EvmYul.Stack.pop]
    have hJumpiRun :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 4 start =
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 3 afterJumpi := by
      have hRun :=
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_running
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre := pre)
          (post :=
            [.prim .invalid, .label caseLabel, .jumpDynamic] ++ post)
          (instr := .jumpi caseLabel) (state := start)
          (final := afterJumpi) 3 hJumpiFits
          (by simpa [start] using hPc)
          (by simpa [tail, List.append_assoc] using hJumpiOpen)
          hJumpiFlow
      simpa [tail, List.append_assoc] using hRun
    have hAfterJumpiPc :
        afterJumpi.pc = casePre.pcAfter := by
      simp [afterJumpi, casePre, Assembly.Program.pcAfter]
    have hLabelOpen :
        Assembly.InteractionSemantics.Source.openStepAtResult
            (casePre ++
              Assembly.Instr.label caseLabel ::
                (Assembly.Instr.jumpDynamic :: post))
            casePre.byteLength (.label caseLabel) afterJumpi =
          .done (.ok (.running afterLabel)) := by
      rw [
        Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
          (by rfl)]
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Instr.haltKind?, Assembly.Target.stepInstr,
        afterLabel]
    have hLabelFlow :
        (Assembly.Instr.label caseLabel).classifyFlowWith
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            afterJumpi (.running afterLabel) =
          .next afterLabel := by
      rfl
    have hLabelRun :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 3 afterJumpi =
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 2 afterLabel := by
      have hRun :=
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_running
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre := casePre) (post := [.jumpDynamic] ++ post)
          (instr := .label caseLabel) (state := afterJumpi)
          (final := afterLabel) 2
          (Assembly.Program.PCFitsFrom.start hAfterInvalidFits)
          hAfterJumpiPc hLabelOpen hLabelFlow
      simpa [hProgramAtLabel, List.append_assoc] using hRun
    have hAfterLabelPc :
        afterLabel.pc =
          (casePre ++
            [Assembly.Instr.label caseLabel]).pcAfter := by
      calc
        afterLabel.pc =
            afterJumpi.pc + EvmYul.UInt256.ofNat 1 := by
          simp [afterLabel, EvmYul.EVM.State.incrPC]
        _ =
            casePre.pcAfter + EvmYul.UInt256.ofNat 1 := by
          rw [hAfterJumpiPc]
        _ =
            (casePre ++
              [Assembly.Instr.label caseLabel]).pcAfter := by
          simpa [Assembly.Instr.byteSize] using
            (Assembly.Program.pcAfter_snoc
              casePre
              (Assembly.Instr.label caseLabel)).symm
    have hJumpOpen :
        Assembly.InteractionSemantics.Source.openStepAtResult
            ((casePre ++
                [Assembly.Instr.label caseLabel]) ++
              Assembly.Instr.jumpDynamic :: post)
            (casePre ++
              [Assembly.Instr.label caseLabel]).byteLength
            .jumpDynamic afterLabel =
          .done (.ok (.running final)) := by
      rw [
        Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
          (by rfl)]
      simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
        Assembly.Instr.haltKind?, Assembly.Target.stepInstr,
        Assembly.Target.stepInstrWith, EvmYul.Stack.pop,
        EvmYul.EVM.State.incrPC, afterLabel, afterJumpi, final]
    have hJumpFlow :
        Assembly.Instr.jumpDynamic.classifyFlowWith
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            afterLabel (.running final) =
          .exit (.running final) := by
      rfl
    have hJumpRun :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ tail ++ post) 2 afterLabel =
          .done (.ok (.running final)) := by
      have hRun :=
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_exit
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre :=
            casePre ++ [Assembly.Instr.label caseLabel])
          (post := post) (instr := .jumpDynamic)
          (state := afterLabel) (result := .running final) 1
          (Assembly.Program.PCFitsFrom.start hAfterLabelFits)
          hAfterLabelPc hJumpOpen hJumpFlow
      simpa [hProgramAtLabel, List.append_assoc] using hRun
    simpa [hZero, start, tail, final] using
      hJumpiRun.trans (hLabelRun.trans hJumpRun)

theorem dispatchLabelCondition_source_run
    {state : Assembly.EVMState}
    {front suffix : List Word} {token : Word}
    {label : Label} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [ Assembly.StackShuffle.dupInstr (front.length + 1)
        , .pushLabel label
        , .prim .eq
        ])
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length < 16)
    (hLabel :
      (pre ++
          [ Assembly.StackShuffle.dupInstr (front.length + 1)
          , .pushLabel label
          , .prim .eq
          ] ++ post).labelPc label = some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            [ Assembly.StackShuffle.dupInstr (front.length + 1)
            , .pushLabel label
            , .prim .eq
            ] ++ post)
          3 { state with stack := front ++ token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          EvmYul.UInt256.eq (EvmYul.UInt256.ofNat dest) token ::
            front ++ token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              EvmYul.UInt256.eq
                  (EvmYul.UInt256.ofNat dest) token ::
                front ++ token :: suffix } ∧
      final.pc =
        (pre ++
          [ Assembly.StackShuffle.dupInstr (front.length + 1)
          , .pushLabel label
          , .prim .eq
          ]).pcAfter := by
  let duplicate := Assembly.StackShuffle.dupInstr (front.length + 1)
  let start : Assembly.EVMState :=
    { state with stack := front ++ token :: suffix }
  let afterDup : Assembly.EVMState :=
    start.replaceStackAndIncrPC (token :: front ++ token :: suffix)
  let afterPush : Assembly.EVMState :=
    afterDup.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat dest :: token :: front ++ token :: suffix)
      (pcΔ := Assembly.Instr.push32Size)
  let finalState : Assembly.EVMState :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq (EvmYul.UInt256.ofNat dest) token ::
        front ++ token :: suffix)
  have hDupStep :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr duplicate) start =
        .ok afterDup := by
    rw [show duplicate =
      Assembly.StackShuffle.dupInstr (front.length + 1) from rfl]
    rw [Assembly.StackShuffle.dupInstr_step_eq_dup (by omega) (by omega)]
    simpa [afterDup, start, List.append_assoc] using
      (Assembly.StackShuffle.dup_append_token
        (state := state) (front := front)
        (suffix := suffix) (token := token))
  have hEqStep :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr (.prim .eq)) afterPush =
        .ok finalState := by
    simp [Assembly.StackShuffle.targetInstr, finalState, afterPush, afterDup,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.push, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hDupByte : duplicate.byteSize = 1 :=
    Assembly.StackShuffle.dupInstr_byteSize (by omega) (by omega)
  have hAfterDupPc :
      afterDup.pc = (pre ++ [duplicate]).pcAfter := by
    have hPcState : state.pc = pre.pcAfter := by
      simpa [start] using hPc
    calc
      afterDup.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterDup, start, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by rw [hPcState]
      _ = EvmYul.UInt256.ofNat (pre.byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = (pre ++ [duplicate]).pcAfter := by
        simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, hDupByte]
  have hAfterPushPc :
      afterPush.pc =
        (pre ++ [duplicate, .pushLabel label]).pcAfter := by
    calc
      afterPush.pc =
          afterDup.pc +
            EvmYul.UInt256.ofNat Assembly.Instr.push32Size := by
        simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ =
          (pre ++ [duplicate]).pcAfter +
            EvmYul.UInt256.ofNat Assembly.Instr.push32Size := by
        rw [hAfterDupPc]
      _ =
          EvmYul.UInt256.ofNat
            ((pre ++ [duplicate]).byteLength +
              Assembly.Instr.push32Size) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = (pre ++ [duplicate, .pushLabel label]).pcAfter := by
        simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize,
          Assembly.Instr.push32Size, Nat.add_assoc]
  have hDupSource :
      Assembly.Source.stepResult
          (pre ++ [duplicate] ++
            ([Assembly.Instr.pushLabel label, .prim .eq] ++ post))
          start =
        .ok (.running afterDup) := by
    exact Assembly.StackShuffle.source_stepResult_local
      (instr := duplicate) (pre := pre)
      (post := [Assembly.Instr.pushLabel label, .prim .eq] ++ post)
      (state := start) (final := afterDup)
      (Assembly.StackShuffle.dupInstr_sourceLocal (by omega) (by omega))
      (Assembly.StackShuffle.dupInstr_haltKind?_none (by omega) (by omega))
      hFits.1 (by simpa [start] using hPc) hDupStep
  have hPushSource :
      Assembly.Source.stepResult
          (pre ++ [duplicate] ++
            ([Assembly.Instr.pushLabel label, .prim .eq] ++ post))
          afterDup =
        .ok (.running afterPush) := by
    have hStep :=
      Assembly.InteractionPreservation.source_stepResult_at_boundary
        (pre := pre ++ [duplicate])
        (post := [Assembly.Instr.prim .eq] ++ post)
        (instr := Assembly.Instr.pushLabel label)
        (state := afterDup)
        (by simpa [List.append_assoc] using hFits.2.1)
        hAfterDupPc
    rw [show
      pre ++ [duplicate] ++
          ([Assembly.Instr.pushLabel label, .prim .eq] ++ post) =
        (pre ++ [duplicate]) ++
          Assembly.Instr.pushLabel label ::
            ([Assembly.Instr.prim .eq] ++ post) by
      simp [List.append_assoc]]
    rw [hStep]
    have hLabel' :
        ((pre ++ [duplicate]) ++
          Assembly.Instr.pushLabel label ::
            ([Assembly.Instr.prim .eq] ++ post)).labelPc label =
          some dest := by
      simpa [duplicate, List.append_assoc] using hLabel
    have hLabel'' :
        (pre ++ duplicate ::
          Assembly.Instr.pushLabel label ::
            Assembly.Instr.prim .eq :: post).labelPc label =
          some dest := by
      simpa [List.append_assoc] using hLabel'
    rw [show
      pre ++ [duplicate] ++
          Assembly.Instr.pushLabel label ::
            ([Assembly.Instr.prim .eq] ++ post) =
        pre ++ duplicate ::
          Assembly.Instr.pushLabel label ::
            Assembly.Instr.prim .eq :: post by
      simp [List.append_assoc]]
    simp only [Assembly.Source.stepAtResult, Assembly.Source.stepAt]
    rw [hLabel'']
    simp [afterPush, Assembly.Target.stepInstr,
      Assembly.Target.stepInstrWith, EvmYul.Stack.push,
      Assembly.Instr.push32Size, afterDup, start, List.append_assoc,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Assembly.Instr.haltKind?]
  have hEqSource :
      Assembly.Source.stepResult
          (pre ++ [duplicate] ++
            ([Assembly.Instr.pushLabel label, .prim .eq] ++ post))
          afterPush =
        .ok (.running finalState) := by
    simpa [List.append_assoc] using
      (Assembly.StackShuffle.source_stepResult_local
        (instr := Assembly.Instr.prim .eq)
        (pre := pre ++ [duplicate, Assembly.Instr.pushLabel label])
        (post := post) (state := afterPush) (final := finalState)
        (by simp [Assembly.StackShuffle.SourceLocalInstr]) rfl
        (by simpa [duplicate, List.append_assoc] using hFits.2.2.1)
        hAfterPushPc hEqStep)
  refine ⟨finalState, ?_, ?_, ?_, ?_⟩
  · unfold Assembly.Source.runNResult Assembly.Control.runNResultWith
    rw [show
      pre ++
          [ Assembly.StackShuffle.dupInstr (front.length + 1)
          , .pushLabel label
          , .prim .eq
          ] ++ post =
        pre ++ [duplicate] ++
          ([.pushLabel label, .prim .eq] ++ post) by
      simp [duplicate, List.append_assoc]]
    change
      (do
        let result ←
          Assembly.Source.stepResult
            (pre ++ [duplicate] ++
              ([Assembly.Instr.pushLabel label, .prim .eq] ++ post))
            start
        match result with
        | .running state' =>
            Assembly.Source.runNResult
              (pre ++ [duplicate] ++
                ([Assembly.Instr.pushLabel label, .prim .eq] ++ post))
              2 state'
        | .halted halt => .ok (.halted halt)) =
        .ok (.running finalState)
    rw [hDupSource]
    simp only [Bind.bind, Except.bind]
    unfold Assembly.Control.runNResultWith
    rw [hPushSource]
    simp only [Bind.bind, Except.bind]
    unfold Assembly.Control.runNResultWith
    rw [hEqSource]
    rfl
  · simp [finalState, afterPush, afterDup,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [finalState, afterPush, afterDup, start,
      Assembly.eraseRuntimeControl,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · calc
        finalState.pc =
            afterPush.pc + EvmYul.UInt256.ofNat 1 := by
          simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        _ =
            (pre ++ [duplicate, .pushLabel label]).pcAfter +
              EvmYul.UInt256.ofNat 1 := by rw [hAfterPushPc]
        _ =
            EvmYul.UInt256.ofNat
              ((pre ++ [duplicate, .pushLabel label]).byteLength + 1) := by
          rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
        _ =
            (pre ++
              [duplicate, .pushLabel label, .prim .eq]).pcAfter := by
          simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
            Assembly.Program.byteLength, Assembly.Instr.byteSize,
            Assembly.Instr.push32Size, Nat.add_assoc]
        _ =
            (pre ++
              [ Assembly.StackShuffle.dupInstr (front.length + 1)
              , .pushLabel label
              , .prim .eq
              ]).pcAfter := by
          rfl

theorem dispatchLabelCondition_source_exists
    {state : Assembly.EVMState}
    {front suffix : List Word} {token : Word}
    {label : Label} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [ Assembly.StackShuffle.dupInstr (front.length + 1)
        , .pushLabel label
        , .prim .eq
        ])
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length < 16)
    (hLabel :
      (pre ++
          [ Assembly.StackShuffle.dupInstr (front.length + 1)
          , .pushLabel label
          , .prim .eq
          ] ++ post).labelPc label = some dest) :
    Assembly.Source.Eventually
      (pre ++
        [ Assembly.StackShuffle.dupInstr (front.length + 1)
        , .pushLabel label
        , .prim .eq
        ] ++ post)
      { state with stack := front ++ token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                EvmYul.UInt256.eq (EvmYul.UInt256.ofNat dest) token ::
                  front ++ token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      EvmYul.UInt256.eq
                          (EvmYul.UInt256.ofNat dest) token ::
                        front ++ token :: suffix } ∧
              final.pc =
                (pre ++
                  [ Assembly.StackShuffle.dupInstr (front.length + 1)
                  , .pushLabel label
                  , .prim .eq
                  ]).pcAfter
        | _ => False) := by
  obtain ⟨final, hRun, hStack, hRuntime, hFinalPc⟩ :=
    dispatchLabelCondition_source_run
      (state := state) (front := front) (suffix := suffix)
      (token := token) (label := label) (dest := dest)
      (pre := pre) (post := post)
      hFits hPc hBound hLabel
  exact
    ⟨3, .ok (.running final), hRun,
      hStack, hRuntime, hFinalPc⟩

theorem dispatchLabelAccumulate_source_exists
    {state : Assembly.EVMState}
    {suffix : List Word} {token accumulator : Word}
    {label : Label} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [ Assembly.StackShuffle.dupInstr 2
        , .pushLabel label
        , .prim .eq
        , .prim .or
        ])
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hLabel :
      (pre ++
          [ Assembly.StackShuffle.dupInstr 2
          , .pushLabel label
          , .prim .eq
          , .prim .or
          ] ++ post).labelPc label = some dest) :
    Assembly.Source.Eventually
      (pre ++
        [ Assembly.StackShuffle.dupInstr 2
        , .pushLabel label
        , .prim .eq
        , .prim .or
        ] ++ post)
      { state with stack := accumulator :: token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                EvmYul.UInt256.lor
                    (EvmYul.UInt256.eq
                      (EvmYul.UInt256.ofNat dest) token)
                    accumulator ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      EvmYul.UInt256.lor
                          (EvmYul.UInt256.eq
                            (EvmYul.UInt256.ofNat dest) token)
                          accumulator ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  [ Assembly.StackShuffle.dupInstr 2
                  , .pushLabel label
                  , .prim .eq
                  , .prim .or
                  ]).pcAfter
        | _ => False) := by
  let conditionCode : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 2
    , .pushLabel label
    , .prim .eq
    ]
  let condition :=
    EvmYul.UInt256.eq (EvmYul.UInt256.ofNat dest) token
  have hConditionFits :
      Assembly.Program.PCFitsFrom pre conditionCode := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [conditionCode] using hFits
  have hOrFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode)
        [.prim .or] := by
    have hAppend :
        Assembly.Program.PCFitsFrom pre
          (conditionCode ++ [.prim .or]) := by
      simpa [conditionCode, List.append_assoc] using hFits
    exact Assembly.Program.PCFitsFrom.right hAppend
  have hCondition :=
    dispatchLabelCondition_source_exists
      (state := state) (front := [accumulator]) (suffix := suffix)
      (token := token) (label := label) (dest := dest)
      (pre := pre) (post := [.prim .or] ++ post)
      (by simpa [conditionCode] using hConditionFits)
      (by simpa using hPc)
      (by simp)
      (by simpa [conditionCode, List.append_assoc] using hLabel)
  have hCondition' :
      Assembly.Source.Eventually
        (pre ++ conditionCode ++ [.prim .or] ++ post)
        { state with stack := accumulator :: token :: suffix }
        (fun outcome =>
          match outcome with
          | .ok (.running mid) =>
              mid.stack = condition :: accumulator :: token :: suffix ∧
                Assembly.eraseRuntimeControl mid =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack := condition :: accumulator :: token :: suffix } ∧
                mid.pc = (pre ++ conditionCode).pcAfter
          | _ => False) := by
    simpa [conditionCode, condition, List.append_assoc] using hCondition
  rw [show
    pre ++
        [ Assembly.StackShuffle.dupInstr 2
        , .pushLabel label
        , .prim .eq
        , .prim .or
        ] ++ post =
      pre ++ conditionCode ++ [.prim .or] ++ post by
    simp [conditionCode, List.append_assoc]]
  apply Assembly.Source.Eventually.bind_running hCondition'
  intro mid hMid
  let final : Assembly.EVMState :=
    mid.replaceStackAndIncrPC
      (EvmYul.UInt256.lor condition accumulator :: token :: suffix)
  have hOrStep :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr (.prim .or)) mid =
        .ok final := by
    simp [Assembly.StackShuffle.targetInstr, final,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.push, EvmYul.Stack.pop2,
      hMid.1, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hOrSource :
      Assembly.Source.stepResult
          ((pre ++ conditionCode) ++ [.prim .or] ++ post) mid =
        .ok (.running final) := by
    exact Assembly.StackShuffle.source_stepResult_local
      (instr := Assembly.Instr.prim .or)
      (pre := pre ++ conditionCode) (post := post)
      (state := mid) (final := final)
      (by simp [Assembly.StackShuffle.SourceLocalInstr]) rfl
      (Assembly.Program.PCFitsFrom.start hOrFits) hMid.2.2 hOrStep
  refine ⟨1, .ok (.running final), ?_, ?_⟩
  · unfold Assembly.Source.runNResult Assembly.Control.runNResultWith
    rw [show
      pre ++ conditionCode ++ [.prim .or] ++ post =
        (pre ++ conditionCode) ++ [.prim .or] ++ post by rfl]
    rw [hOrSource]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp [final, condition, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
    · calc
        Assembly.eraseRuntimeControl final =
            Assembly.eraseRuntimeControl
              { mid with
                stack :=
                  EvmYul.UInt256.lor condition accumulator ::
                    token :: suffix } := by
          simp [final, Assembly.eraseRuntimeControl,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        _ =
            Assembly.eraseRuntimeControl
              { state with
                stack :=
                  EvmYul.UInt256.lor condition accumulator ::
                    token :: suffix } := by
          exact
            Assembly.eraseRuntimeControl_with_stack_congr
              (left := mid)
              (right :=
                { state with
                  stack := condition :: accumulator :: token :: suffix })
              (stack :=
                EvmYul.UInt256.lor condition accumulator ::
                  token :: suffix)
              hMid.2.1
    · calc
        final.pc = mid.pc + EvmYul.UInt256.ofNat 1 := by
          simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        _ = (pre ++ conditionCode).pcAfter +
              EvmYul.UInt256.ofNat 1 := by rw [hMid.2.2]
        _ =
            EvmYul.UInt256.ofNat
              ((pre ++ conditionCode).byteLength + 1) := by
          rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
        _ =
            (pre ++ conditionCode ++ [Assembly.Instr.prim .or]).pcAfter := by
          simp [Assembly.Program.pcAfter,
            Assembly.Program.byteLength_append,
            Assembly.Program.byteLength, Assembly.Instr.byteSize,
            Nat.add_assoc]
        _ =
            (pre ++
              [ Assembly.StackShuffle.dupInstr 2
              , .pushLabel label
              , .prim .eq
              , .prim .or
              ]).pcAfter := by
          simp [conditionCode, List.append_assoc]

set_option maxHeartbeats 800000 in
theorem dispatchLabelAccumulate_source_run
    {state : Assembly.EVMState}
    {suffix : List Word} {token accumulator : Word}
    {label : Label} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [ Assembly.StackShuffle.dupInstr 2
        , .pushLabel label
        , .prim .eq
        , .prim .or
        ])
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hLabel :
      (pre ++
          [ Assembly.StackShuffle.dupInstr 2
          , .pushLabel label
          , .prim .eq
          , .prim .or
          ] ++ post).labelPc label = some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            [ Assembly.StackShuffle.dupInstr 2
            , .pushLabel label
            , .prim .eq
            , .prim .or
            ] ++ post)
          4 { state with stack := accumulator :: token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          EvmYul.UInt256.lor
              (EvmYul.UInt256.eq
                (EvmYul.UInt256.ofNat dest) token)
              accumulator ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              EvmYul.UInt256.lor
                  (EvmYul.UInt256.eq
                    (EvmYul.UInt256.ofNat dest) token)
                  accumulator ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          [ Assembly.StackShuffle.dupInstr 2
          , .pushLabel label
          , .prim .eq
          , .prim .or
          ]).pcAfter := by
  let conditionCode : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 2
    , .pushLabel label
    , .prim .eq
    ]
  let condition :=
    EvmYul.UInt256.eq (EvmYul.UInt256.ofNat dest) token
  have hConditionFits :
      Assembly.Program.PCFitsFrom pre conditionCode := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [conditionCode] using hFits
  have hOrFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode)
        [.prim .or] := by
    have hAppend :
        Assembly.Program.PCFitsFrom pre
          (conditionCode ++ [.prim .or]) := by
      simpa [conditionCode, List.append_assoc] using hFits
    exact Assembly.Program.PCFitsFrom.right hAppend
  obtain ⟨mid, hConditionRun, hMidStack, hMidRuntime, hMidPc⟩ :=
    dispatchLabelCondition_source_run
      (state := state) (front := [accumulator]) (suffix := suffix)
      (token := token) (label := label) (dest := dest)
      (pre := pre) (post := [.prim .or] ++ post)
      (by simpa [conditionCode] using hConditionFits)
      (by simpa using hPc)
      (by simp)
      (by simpa [conditionCode, List.append_assoc] using hLabel)
  have hConditionRun' :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ [.prim .or] ++ post)
          3 { state with stack := accumulator :: token :: suffix } =
        .ok (.running mid) := by
    simpa [conditionCode, List.append_assoc] using hConditionRun
  have hMidStack' :
      mid.stack = condition :: accumulator :: token :: suffix := by
    simpa [condition] using hMidStack
  have hMidPc' :
      mid.pc = (pre ++ conditionCode).pcAfter := by
    simpa [conditionCode] using hMidPc
  let final : Assembly.EVMState :=
    mid.replaceStackAndIncrPC
      (EvmYul.UInt256.lor condition accumulator :: token :: suffix)
  have hOrStep :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr (.prim .or)) mid =
        .ok final := by
    simp [Assembly.StackShuffle.targetInstr, final,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.push, EvmYul.Stack.pop2,
      hMidStack', EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hOrSource :
      Assembly.Source.stepResult
          ((pre ++ conditionCode) ++ [.prim .or] ++ post) mid =
        .ok (.running final) := by
    exact Assembly.StackShuffle.source_stepResult_local
      (instr := Assembly.Instr.prim .or)
      (pre := pre ++ conditionCode) (post := post)
      (state := mid) (final := final)
      (by simp [Assembly.StackShuffle.SourceLocalInstr]) rfl
      (Assembly.Program.PCFitsFrom.start hOrFits) hMidPc hOrStep
  have hFullRun :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++
            [Assembly.Instr.prim .or] ++ post)
          4 { state with stack := accumulator :: token :: suffix } =
        .ok (.running final) := by
    calc
      Assembly.Source.runNResult
          (pre ++ conditionCode ++
            [Assembly.Instr.prim .or] ++ post)
          4 { state with stack := accumulator :: token :: suffix } =
        Assembly.Source.runNResult
          (pre ++ conditionCode ++
            [Assembly.Instr.prim .or] ++ post)
          1 mid := by
            rw [show 4 = 3 + 1 by omega]
            exact
              Assembly.Source.runNResult_add_of_running
                (pre ++ conditionCode ++
                  [Assembly.Instr.prim .or] ++ post)
                3 1 hConditionRun'
      _ = .ok (.running final) := by
        unfold Assembly.Source.runNResult
          Assembly.Control.runNResultWith
        rw [show
          pre ++ conditionCode ++ [Assembly.Instr.prim .or] ++ post =
            (pre ++ conditionCode) ++
              [Assembly.Instr.prim .or] ++ post by rfl]
        rw [hOrSource]
        rfl
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa [conditionCode, List.append_assoc] using hFullRun
  · simp [final, condition, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { mid with
              stack :=
                EvmYul.UInt256.lor condition accumulator ::
                  token :: suffix } := by
        simp [final, Assembly.eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                EvmYul.UInt256.lor condition accumulator ::
                  token :: suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := mid)
            (right :=
              { state with
                stack := condition :: accumulator :: token :: suffix })
            (stack :=
              EvmYul.UInt256.lor condition accumulator ::
                token :: suffix)
            (by simpa [condition] using hMidRuntime)
  · calc
      final.pc = mid.pc + EvmYul.UInt256.ofNat 1 := by
        simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ = (pre ++ conditionCode).pcAfter +
            EvmYul.UInt256.ofNat 1 := by rw [hMidPc']
      _ =
          EvmYul.UInt256.ofNat
            ((pre ++ conditionCode).byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
          (pre ++ conditionCode ++ [Assembly.Instr.prim .or]).pcAfter := by
        simp [Assembly.Program.pcAfter,
          Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize,
          Nat.add_assoc]
      _ =
          (pre ++
            [ Assembly.StackShuffle.dupInstr 2
            , .pushLabel label
            , .prim .eq
            , .prim .or
            ]).pcAfter := by
        simp [conditionCode, List.append_assoc]

theorem dynamicReturnNextTests_source_exists
    {state : Assembly.EVMState}
    {suffix : List Word} {token accumulator : Word}
    {sites : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (sites.flatMap
          ReturnAddressLower.Terminator.dynamicReturnNextTest))
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      ∀ site ∈ sites,
        ∃ dest,
          (pre ++
              sites.flatMap
                ReturnAddressLower.Terminator.dynamicReturnNextTest ++
              post).labelPc site.target =
            some dest) :
    Assembly.Source.Eventually
      (pre ++
        sites.flatMap
          ReturnAddressLower.Terminator.dynamicReturnNextTest ++
        post)
      { state with stack := accumulator :: token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                sites.foldl
                    (fun value site =>
                      EvmYul.UInt256.lor
                        (ReturnAddressLower.Terminator.dynamicReturnMatch
                          (pre ++
                            sites.flatMap
                              ReturnAddressLower.Terminator.dynamicReturnNextTest ++
                            post).labelPc
                          token site)
                        value)
                    accumulator ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      sites.foldl
                          (fun value site =>
                            EvmYul.UInt256.lor
                              (ReturnAddressLower.Terminator.dynamicReturnMatch
                                (pre ++
                                  sites.flatMap
                                    ReturnAddressLower.Terminator.dynamicReturnNextTest ++
                                  post).labelPc
                                token site)
                              value)
                          accumulator ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  sites.flatMap
                    ReturnAddressLower.Terminator.dynamicReturnNextTest).pcAfter
        | _ => False) := by
  induction sites generalizing pre state accumulator with
  | nil =>
      apply Assembly.Source.Eventually.pure
      have hPc' : state.pc = pre.pcAfter := by
        simpa using hPc
      simp [Assembly.eraseRuntimeControl, hPc']
  | cons site rest ih =>
      let headCode :=
        ReturnAddressLower.Terminator.dynamicReturnNextTest site
      let tailCode :=
        rest.flatMap
          ReturnAddressLower.Terminator.dynamicReturnNextTest
      have hProgramEq :
          pre ++ headCode ++ tailCode ++ post =
            pre ++
              (site :: rest).flatMap
                ReturnAddressLower.Terminator.dynamicReturnNextTest ++
              post := by
        simp [headCode, tailCode, List.append_assoc]
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode := by
        apply Assembly.Program.PCFitsFrom.left
        simpa [headCode, tailCode, List.append_assoc] using hFits
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode := by
        have hRight := Assembly.Program.PCFitsFrom.right hFits
        simpa [headCode, tailCode, List.append_assoc] using hRight
      obtain ⟨dest, hDest⟩ := hResolved site (by simp)
      have hDest' :
          (pre ++ headCode ++ tailCode ++ post).labelPc site.target =
            some dest := by
        simpa [headCode, tailCode, List.append_assoc] using hDest
      have hDestAssoc :
          (pre ++ (headCode ++ (tailCode ++ post))).labelPc site.target =
            some dest := by
        simpa [List.append_assoc] using hDest'
      have hHead :=
        dispatchLabelAccumulate_source_exists
          (state := state) (suffix := suffix)
          (token := token) (accumulator := accumulator)
          (label := site.target) (dest := dest)
          (pre := pre) (post := tailCode ++ post)
          (by simpa [headCode] using hHeadFits)
          hPc
          (by
            simpa [headCode, List.append_assoc] using hDest')
      have hHead' :
          Assembly.Source.Eventually
            (pre ++ headCode ++ tailCode ++ post)
            { state with stack := accumulator :: token :: suffix }
            (fun outcome =>
              match outcome with
              | .ok (.running mid) =>
                  mid.stack =
                      EvmYul.UInt256.lor
                          (ReturnAddressLower.Terminator.dynamicReturnMatch
                            (pre ++ headCode ++ tailCode ++ post).labelPc
                            token site)
                          accumulator ::
                        token :: suffix ∧
                    Assembly.eraseRuntimeControl mid =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            EvmYul.UInt256.lor
                                (ReturnAddressLower.Terminator.dynamicReturnMatch
                                  (pre ++ headCode ++ tailCode ++ post).labelPc
                                  token site)
                                accumulator ::
                              token :: suffix } ∧
                    mid.pc = (pre ++ headCode).pcAfter
              | _ => False) := by
        have hHeadRaw :
            Assembly.Source.Eventually
              (pre ++ headCode ++ tailCode ++ post)
              { state with stack := accumulator :: token :: suffix }
              (fun outcome =>
                match outcome with
                | .ok (.running mid) =>
                    mid.stack =
                        EvmYul.UInt256.lor
                            (EvmYul.UInt256.eq
                              (EvmYul.UInt256.ofNat dest) token)
                            accumulator ::
                          token :: suffix ∧
                      Assembly.eraseRuntimeControl mid =
                        Assembly.eraseRuntimeControl
                          { state with
                            stack :=
                              EvmYul.UInt256.lor
                                  (EvmYul.UInt256.eq
                                    (EvmYul.UInt256.ofNat dest) token)
                                  accumulator ::
                                token :: suffix } ∧
                      mid.pc = (pre ++ headCode).pcAfter
                | _ => False) := by
          simpa [headCode, List.append_assoc] using hHead
        apply Assembly.Source.Eventually.mono hHeadRaw
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok result =>
            cases result with
            | halted halt => cases hOutcome
            | running mid =>
                simpa [ReturnAddressLower.Terminator.dynamicReturnMatch,
                  hDestAssoc] using hOutcome
      rw [show
        pre ++
            (site :: rest).flatMap
              ReturnAddressLower.Terminator.dynamicReturnNextTest ++
            post =
          pre ++ headCode ++ tailCode ++ post by
        simp [headCode, tailCode, List.append_assoc]]
      apply Assembly.Source.Eventually.bind_running hHead'
      intro mid hMid
      let nextAccumulator :=
        EvmYul.UInt256.lor
          (ReturnAddressLower.Terminator.dynamicReturnMatch
            (pre ++ headCode ++ tailCode ++ post).labelPc
            token site)
          accumulator
      have hTailResolved :
          ∀ candidate ∈ rest,
            ∃ candidateDest,
              ((pre ++ headCode) ++ tailCode ++ post).labelPc
                  candidate.target =
                some candidateDest := by
        intro candidate hCandidate
        obtain ⟨candidateDest, hCandidateDest⟩ :=
          hResolved candidate (by simp [hCandidate])
        exact
          ⟨candidateDest,
            by
              simpa [headCode, tailCode, List.append_assoc] using
                hCandidateDest⟩
      have hTail :=
        ih
          (pre := pre ++ headCode) (state := mid)
          (accumulator := nextAccumulator)
          hTailFits
          (by
            simpa [nextAccumulator, hMid.1] using hMid.2.2)
          hTailResolved
      have hMidRecord :
          { mid with stack := nextAccumulator :: token :: suffix } = mid := by
        cases mid
        simpa [nextAccumulator] using hMid.1.symm
      have hTail' := hTail
      rw [hMidRecord] at hTail'
      apply Assembly.Source.Eventually.mono
        (by simpa [tailCode] using hTail')
      intro outcome hOutcome
      cases outcome with
      | error err => cases hOutcome
      | ok result =>
          cases result with
          | halted halt => cases hOutcome
          | running final =>
              rcases hOutcome with
                ⟨hFinalStack, hFinalRuntime, hFinalPc⟩
              refine ⟨?_, ?_, ?_⟩
              · simpa [nextAccumulator, headCode, tailCode,
                  List.append_assoc] using hFinalStack
              · calc
                  Assembly.eraseRuntimeControl final =
                      Assembly.eraseRuntimeControl
                        { mid with
                          stack :=
                            rest.foldl
                                (fun value candidate =>
                                  EvmYul.UInt256.lor
                                    (ReturnAddressLower.Terminator.dynamicReturnMatch
                                      (pre ++ headCode ++ tailCode ++ post).labelPc
                                      token candidate)
                                    value)
                                nextAccumulator ::
                              token :: suffix } := by
                    simpa [headCode, tailCode, List.append_assoc] using
                      hFinalRuntime
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            rest.foldl
                                (fun value candidate =>
                                  EvmYul.UInt256.lor
                                    (ReturnAddressLower.Terminator.dynamicReturnMatch
                                      (pre ++ headCode ++ tailCode ++ post).labelPc
                                      token candidate)
                                    value)
                                nextAccumulator ::
                              token :: suffix } := by
                    exact
                      Assembly.eraseRuntimeControl_with_stack_congr
                        (left := mid)
                        (right :=
                          { state with
                            stack := nextAccumulator :: token :: suffix })
                        hMid.2.1
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            (site :: rest).foldl
                                (fun value candidate =>
                                  EvmYul.UInt256.lor
                                    (ReturnAddressLower.Terminator.dynamicReturnMatch
                                      (pre ++ headCode ++ tailCode ++ post).labelPc
                                      token candidate)
                                    value)
                                accumulator ::
                              token :: suffix } := by
                    simp [nextAccumulator]
              · simpa [headCode, tailCode, List.append_assoc] using hFinalPc

set_option maxHeartbeats 800000 in
theorem dynamicReturnNextTests_source_run
    {state : Assembly.EVMState}
    {suffix : List Word} {token accumulator : Word}
    {sites : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (sites.flatMap
          ReturnAddressLower.Terminator.dynamicReturnNextTest))
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      ∀ site ∈ sites,
        ∃ dest,
          (pre ++
              sites.flatMap
                ReturnAddressLower.Terminator.dynamicReturnNextTest ++
              post).labelPc site.target =
            some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            sites.flatMap
              ReturnAddressLower.Terminator.dynamicReturnNextTest ++
            post)
          (sites.flatMap
            ReturnAddressLower.Terminator.dynamicReturnNextTest).length
          { state with stack := accumulator :: token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          sites.foldl
              (fun value site =>
                EvmYul.UInt256.lor
                  (ReturnAddressLower.Terminator.dynamicReturnMatch
                    (pre ++
                      sites.flatMap
                        ReturnAddressLower.Terminator.dynamicReturnNextTest ++
                      post).labelPc
                    token site)
                  value)
              accumulator ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              sites.foldl
                  (fun value site =>
                    EvmYul.UInt256.lor
                      (ReturnAddressLower.Terminator.dynamicReturnMatch
                        (pre ++
                          sites.flatMap
                            ReturnAddressLower.Terminator.dynamicReturnNextTest ++
                          post).labelPc
                        token site)
                      value)
                  accumulator ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          sites.flatMap
            ReturnAddressLower.Terminator.dynamicReturnNextTest).pcAfter := by
  induction sites generalizing pre state accumulator with
  | nil =>
      let final : Assembly.EVMState :=
        { state with stack := accumulator :: token :: suffix }
      refine ⟨final, ?_, ?_, ?_, ?_⟩
      · simp [Assembly.Source.runNResult,
          Assembly.Control.runNResultWith, final]
      · rfl
      · rfl
      · simpa [final] using hPc
  | cons site rest ih =>
      let headCode :=
        ReturnAddressLower.Terminator.dynamicReturnNextTest site
      let tailCode :=
        rest.flatMap
          ReturnAddressLower.Terminator.dynamicReturnNextTest
      have hProgramEq :
          pre ++ headCode ++ tailCode ++ post =
            pre ++
              (site :: rest).flatMap
                ReturnAddressLower.Terminator.dynamicReturnNextTest ++
              post := by
        simp [headCode, tailCode, List.append_assoc]
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode := by
        apply Assembly.Program.PCFitsFrom.left
        simpa [headCode, tailCode, List.append_assoc] using hFits
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode := by
        have hRight := Assembly.Program.PCFitsFrom.right hFits
        simpa [headCode, tailCode, List.append_assoc] using hRight
      obtain ⟨dest, hDest⟩ := hResolved site (by simp)
      have hDest' :
          (pre ++ headCode ++ tailCode ++ post).labelPc site.target =
            some dest := by
        simpa [headCode, tailCode, List.append_assoc] using hDest
      obtain ⟨mid, hHeadRun, hMidStackRaw,
          hMidRuntimeRaw, hMidPc⟩ :=
        dispatchLabelAccumulate_source_run
          (state := state) (suffix := suffix)
          (token := token) (accumulator := accumulator)
          (label := site.target) (dest := dest)
          (pre := pre) (post := tailCode ++ post)
          (by simpa [headCode] using hHeadFits)
          hPc
          (by simpa [headCode, List.append_assoc] using hDest')
      let nextAccumulator :=
        EvmYul.UInt256.lor
          (ReturnAddressLower.Terminator.dynamicReturnMatch
            (pre ++ headCode ++ tailCode ++ post).labelPc
            token site)
          accumulator
      have hDestAssoc :
          (pre ++ (headCode ++ (tailCode ++ post))).labelPc site.target =
            some dest := by
        simpa [List.append_assoc] using hDest'
      have hMidStack :
          mid.stack = nextAccumulator :: token :: suffix := by
        simpa [nextAccumulator,
          ReturnAddressLower.Terminator.dynamicReturnMatch,
          hDestAssoc] using hMidStackRaw
      have hMidRuntime :
          Assembly.eraseRuntimeControl mid =
            Assembly.eraseRuntimeControl
              { state with
                stack := nextAccumulator :: token :: suffix } := by
        simpa [nextAccumulator,
          ReturnAddressLower.Terminator.dynamicReturnMatch,
          hDestAssoc] using hMidRuntimeRaw
      have hHeadRun' :
          Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              headCode.length
              { state with stack := accumulator :: token :: suffix } =
            .ok (.running mid) := by
        simpa [headCode, List.append_assoc] using hHeadRun
      have hTailResolved :
          ∀ candidate ∈ rest,
            ∃ candidateDest,
              ((pre ++ headCode) ++ tailCode ++ post).labelPc
                  candidate.target =
                some candidateDest := by
        intro candidate hCandidate
        obtain ⟨candidateDest, hCandidateDest⟩ :=
          hResolved candidate (by simp [hCandidate])
        exact
          ⟨candidateDest,
            by
              simpa [headCode, tailCode, List.append_assoc] using
                hCandidateDest⟩
      obtain ⟨final, hTailRunRaw, hFinalStack,
          hFinalRuntime, hFinalPc⟩ :=
        ih
          (pre := pre ++ headCode) (state := mid)
          (accumulator := nextAccumulator)
          hTailFits
          (by simpa [hMidStack] using hMidPc)
          hTailResolved
      have hMidRecord :
          { mid with stack := nextAccumulator :: token :: suffix } = mid := by
        cases mid
        simpa using hMidStack.symm
      have hTailRun :
          Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              tailCode.length mid =
            .ok (.running final) := by
        have hTailRun' := hTailRunRaw
        rw [hMidRecord] at hTailRun'
        simpa [tailCode, List.append_assoc] using hTailRun'
      have hFullRun :
          Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              (headCode.length + tailCode.length)
              { state with stack := accumulator :: token :: suffix } =
            .ok (.running final) := by
        calc
          Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              (headCode.length + tailCode.length)
              { state with stack := accumulator :: token :: suffix } =
            Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              tailCode.length mid :=
                Assembly.Source.runNResult_add_of_running
                  (pre ++ headCode ++ tailCode ++ post)
                  headCode.length tailCode.length hHeadRun'
          _ = .ok (.running final) := hTailRun
      refine ⟨final, ?_, ?_, ?_, ?_⟩
      · simpa [headCode, tailCode, List.append_assoc] using hFullRun
      · simpa [nextAccumulator, headCode, tailCode,
          List.append_assoc] using hFinalStack
      · calc
          Assembly.eraseRuntimeControl final =
              Assembly.eraseRuntimeControl
                { mid with
                  stack :=
                    rest.foldl
                        (fun value candidate =>
                          EvmYul.UInt256.lor
                            (ReturnAddressLower.Terminator.dynamicReturnMatch
                              (pre ++ headCode ++ tailCode ++ post).labelPc
                              token candidate)
                            value)
                        nextAccumulator ::
                      token :: suffix } := by
            simpa [headCode, tailCode, List.append_assoc] using
              hFinalRuntime
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack :=
                    rest.foldl
                        (fun value candidate =>
                          EvmYul.UInt256.lor
                            (ReturnAddressLower.Terminator.dynamicReturnMatch
                              (pre ++ headCode ++ tailCode ++ post).labelPc
                              token candidate)
                            value)
                        nextAccumulator ::
                      token :: suffix } := by
            exact
              Assembly.eraseRuntimeControl_with_stack_congr
                (left := mid)
                (right :=
                  { state with
                    stack := nextAccumulator :: token :: suffix })
                hMidRuntime
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack :=
                    (site :: rest).foldl
                        (fun value candidate =>
                          EvmYul.UInt256.lor
                            (ReturnAddressLower.Terminator.dynamicReturnMatch
                              (pre ++
                                (site :: rest).flatMap
                                  ReturnAddressLower.Terminator.dynamicReturnNextTest ++
                                post).labelPc
                              token candidate)
                            value)
                        accumulator ::
                      token :: suffix } := by
            simp only [List.foldl_cons, nextAccumulator]
            rw [hProgramEq]
      · simpa [headCode, tailCode, List.append_assoc] using hFinalPc

theorem dynamicReturnTests_source_exists
    {state : Assembly.EVMState}
    {suffix : List Word} {token : Word}
    {first : ReturnSite} {rest : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (ReturnAddressLower.Terminator.dynamicReturnTests
          (first :: rest)))
    (hPc :
      ({ state with stack := token :: suffix }).pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++
              ReturnAddressLower.Terminator.dynamicReturnTests
                (first :: rest) ++
              post).labelPc site.target =
            some dest) :
    Assembly.Source.Eventually
      (pre ++
        ReturnAddressLower.Terminator.dynamicReturnTests
          (first :: rest) ++
        post)
      { state with stack := token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                ReturnAddressLower.Terminator.dynamicReturnAccumulator
                    (pre ++
                      ReturnAddressLower.Terminator.dynamicReturnTests
                        (first :: rest) ++
                      post).labelPc
                    token (first :: rest) ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      ReturnAddressLower.Terminator.dynamicReturnAccumulator
                          (pre ++
                            ReturnAddressLower.Terminator.dynamicReturnTests
                              (first :: rest) ++
                            post).labelPc
                          token (first :: rest) ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  ReturnAddressLower.Terminator.dynamicReturnTests
                    (first :: rest)).pcAfter
        | _ => False) := by
  let headCode :=
    ReturnAddressLower.Terminator.dynamicReturnFirstTest first
  let tailCode :=
    rest.flatMap ReturnAddressLower.Terminator.dynamicReturnNextTest
  have hHeadFits :
      Assembly.Program.PCFitsFrom pre headCode := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hFits
  have hTailFits :
      Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode := by
    have hRight := Assembly.Program.PCFitsFrom.right hFits
    simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hRight
  obtain ⟨dest, hDest⟩ := hResolved first (by simp)
  have hDest' :
      (pre ++ headCode ++ tailCode ++ post).labelPc first.target =
        some dest := by
    simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hDest
  have hDestAssoc :
      (pre ++ (headCode ++ (tailCode ++ post))).labelPc first.target =
        some dest := by
    simpa [List.append_assoc] using hDest'
  have hHead :=
    dispatchLabelCondition_source_exists
      (state := state) (front := []) (suffix := suffix)
      (token := token) (label := first.target) (dest := dest)
      (pre := pre) (post := tailCode ++ post)
      (by simpa [headCode] using hHeadFits)
      hPc (by simp)
      (by simpa [headCode, List.append_assoc] using hDest')
  have hHead' :
      Assembly.Source.Eventually
        (pre ++ headCode ++ tailCode ++ post)
        { state with stack := token :: suffix }
        (fun outcome =>
          match outcome with
          | .ok (.running mid) =>
              mid.stack =
                  ReturnAddressLower.Terminator.dynamicReturnMatch
                      (pre ++ headCode ++ tailCode ++ post).labelPc
                      token first ::
                    token :: suffix ∧
                Assembly.eraseRuntimeControl mid =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        ReturnAddressLower.Terminator.dynamicReturnMatch
                            (pre ++ headCode ++ tailCode ++ post).labelPc
                            token first ::
                          token :: suffix } ∧
                mid.pc = (pre ++ headCode).pcAfter
          | _ => False) := by
    have hHeadRaw :
        Assembly.Source.Eventually
          (pre ++ headCode ++ tailCode ++ post)
          { state with stack := token :: suffix }
          (fun outcome =>
            match outcome with
            | .ok (.running mid) =>
                mid.stack =
                    EvmYul.UInt256.eq
                        (EvmYul.UInt256.ofNat dest) token ::
                      token :: suffix ∧
                  Assembly.eraseRuntimeControl mid =
                    Assembly.eraseRuntimeControl
                      { state with
                        stack :=
                          EvmYul.UInt256.eq
                              (EvmYul.UInt256.ofNat dest) token ::
                            token :: suffix } ∧
                  mid.pc = (pre ++ headCode).pcAfter
            | _ => False) := by
      simpa [headCode, List.append_assoc] using hHead
    apply Assembly.Source.Eventually.mono hHeadRaw
    intro outcome hOutcome
    cases outcome with
    | error err => cases hOutcome
    | ok result =>
        cases result with
        | halted halt => cases hOutcome
        | running mid =>
            simpa [ReturnAddressLower.Terminator.dynamicReturnMatch,
              hDestAssoc] using hOutcome
  rw [show
    pre ++
        ReturnAddressLower.Terminator.dynamicReturnTests
          (first :: rest) ++
        post =
      pre ++ headCode ++ tailCode ++ post by
    simp [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc]]
  apply Assembly.Source.Eventually.bind_running hHead'
  intro mid hMid
  let firstAccumulator :=
    ReturnAddressLower.Terminator.dynamicReturnMatch
      (pre ++ headCode ++ tailCode ++ post).labelPc token first
  have hTailResolved :
      ∀ site ∈ rest,
        ∃ siteDest,
          ((pre ++ headCode) ++ tailCode ++ post).labelPc site.target =
            some siteDest := by
    intro site hSite
    obtain ⟨siteDest, hSiteDest⟩ :=
      hResolved site (by simp [hSite])
    exact
      ⟨siteDest,
        by
          simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
            headCode, tailCode, List.append_assoc] using hSiteDest⟩
  have hTail :=
    dynamicReturnNextTests_source_exists
      (state := mid) (suffix := suffix) (token := token)
      (accumulator := firstAccumulator)
      (sites := rest) (pre := pre ++ headCode) (post := post)
      hTailFits
      (by simpa [firstAccumulator, hMid.1] using hMid.2.2)
      hTailResolved
  have hMidRecord :
      { mid with stack := firstAccumulator :: token :: suffix } = mid := by
    cases mid
    simpa [firstAccumulator] using hMid.1.symm
  have hTail' := hTail
  rw [hMidRecord] at hTail'
  apply Assembly.Source.Eventually.mono
    (by simpa [tailCode] using hTail')
  intro outcome hOutcome
  cases outcome with
  | error err => cases hOutcome
  | ok result =>
      cases result with
      | halted halt => cases hOutcome
      | running final =>
          rcases hOutcome with
            ⟨hFinalStack, hFinalRuntime, hFinalPc⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [ReturnAddressLower.Terminator.dynamicReturnAccumulator,
              ReturnAddressLower.Terminator.dynamicReturnTests,
              firstAccumulator, headCode, tailCode,
              List.append_assoc] using hFinalStack
          · calc
              Assembly.eraseRuntimeControl final =
                  Assembly.eraseRuntimeControl
                    { mid with
                      stack :=
                        rest.foldl
                            (fun value site =>
                              EvmYul.UInt256.lor
                                (ReturnAddressLower.Terminator.dynamicReturnMatch
                                  (pre ++ headCode ++ tailCode ++ post).labelPc
                                  token site)
                                value)
                            firstAccumulator ::
                          token :: suffix } := by
                simpa [headCode, tailCode, List.append_assoc] using
                  hFinalRuntime
              _ =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        rest.foldl
                            (fun value site =>
                              EvmYul.UInt256.lor
                                (ReturnAddressLower.Terminator.dynamicReturnMatch
                                  (pre ++ headCode ++ tailCode ++ post).labelPc
                                  token site)
                                value)
                            firstAccumulator ::
                          token :: suffix } := by
                exact
                  Assembly.eraseRuntimeControl_with_stack_congr
                    (left := mid)
                    (right :=
                      { state with
                        stack := firstAccumulator :: token :: suffix })
                    hMid.2.1
              _ =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        ReturnAddressLower.Terminator.dynamicReturnAccumulator
                            (pre ++ headCode ++ tailCode ++ post).labelPc
                            token (first :: rest) ::
                          token :: suffix } := by
                simp [ReturnAddressLower.Terminator.dynamicReturnAccumulator,
                  firstAccumulator]
          · simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
              headCode, tailCode, List.append_assoc] using hFinalPc

set_option maxHeartbeats 800000 in
theorem dynamicReturnTests_source_run
    {state : Assembly.EVMState}
    {suffix : List Word} {token : Word}
    {first : ReturnSite} {rest : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (ReturnAddressLower.Terminator.dynamicReturnTests
          (first :: rest)))
    (hPc :
      ({ state with stack := token :: suffix }).pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++
              ReturnAddressLower.Terminator.dynamicReturnTests
                (first :: rest) ++
              post).labelPc site.target =
            some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnTests
              (first :: rest) ++
            post)
          (ReturnAddressLower.Terminator.dynamicReturnTests
            (first :: rest)).length
          { state with stack := token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          ReturnAddressLower.Terminator.dynamicReturnAccumulator
              (pre ++
                ReturnAddressLower.Terminator.dynamicReturnTests
                  (first :: rest) ++
                post).labelPc
              token (first :: rest) ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              ReturnAddressLower.Terminator.dynamicReturnAccumulator
                  (pre ++
                    ReturnAddressLower.Terminator.dynamicReturnTests
                      (first :: rest) ++
                    post).labelPc
                  token (first :: rest) ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          ReturnAddressLower.Terminator.dynamicReturnTests
            (first :: rest)).pcAfter := by
  let headCode :=
    ReturnAddressLower.Terminator.dynamicReturnFirstTest first
  let tailCode :=
    rest.flatMap ReturnAddressLower.Terminator.dynamicReturnNextTest
  have hProgramEq :
      pre ++ headCode ++ tailCode ++ post =
        pre ++
          ReturnAddressLower.Terminator.dynamicReturnTests
            (first :: rest) ++
          post := by
    simp [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc]
  have hHeadFits :
      Assembly.Program.PCFitsFrom pre headCode := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hFits
  have hTailFits :
      Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode := by
    have hRight := Assembly.Program.PCFitsFrom.right hFits
    simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hRight
  obtain ⟨dest, hDest⟩ := hResolved first (by simp)
  have hDest' :
      (pre ++ headCode ++ tailCode ++ post).labelPc first.target =
        some dest := by
    simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hDest
  obtain ⟨mid, hHeadRunRaw, hMidStackRaw,
      hMidRuntimeRaw, hMidPc⟩ :=
    dispatchLabelCondition_source_run
      (state := state) (front := []) (suffix := suffix)
      (token := token) (label := first.target) (dest := dest)
      (pre := pre) (post := tailCode ++ post)
      (by simpa [headCode] using hHeadFits)
      hPc (by simp)
      (by simpa [headCode, List.append_assoc] using hDest')
  let firstAccumulator :=
    ReturnAddressLower.Terminator.dynamicReturnMatch
      (pre ++ headCode ++ tailCode ++ post).labelPc token first
  have hDestAssoc :
      (pre ++ (headCode ++ (tailCode ++ post))).labelPc first.target =
        some dest := by
    simpa [List.append_assoc] using hDest'
  have hMidStack :
      mid.stack = firstAccumulator :: token :: suffix := by
    simpa [firstAccumulator,
      ReturnAddressLower.Terminator.dynamicReturnMatch,
      hDestAssoc] using hMidStackRaw
  have hMidRuntime :
      Assembly.eraseRuntimeControl mid =
        Assembly.eraseRuntimeControl
          { state with
            stack := firstAccumulator :: token :: suffix } := by
    simpa [firstAccumulator,
      ReturnAddressLower.Terminator.dynamicReturnMatch,
      hDestAssoc] using hMidRuntimeRaw
  have hHeadRun :
      Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          headCode.length { state with stack := token :: suffix } =
        .ok (.running mid) := by
    simpa [headCode, List.append_assoc] using hHeadRunRaw
  have hTailResolved :
      ∀ site ∈ rest,
        ∃ siteDest,
          ((pre ++ headCode) ++ tailCode ++ post).labelPc site.target =
            some siteDest := by
    intro site hSite
    obtain ⟨siteDest, hSiteDest⟩ :=
      hResolved site (by simp [hSite])
    exact
      ⟨siteDest,
        by
          simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
            headCode, tailCode, List.append_assoc] using hSiteDest⟩
  obtain ⟨final, hTailRunRaw, hFinalStack,
      hFinalRuntime, hFinalPc⟩ :=
    dynamicReturnNextTests_source_run
      (state := mid) (suffix := suffix) (token := token)
      (accumulator := firstAccumulator)
      (sites := rest) (pre := pre ++ headCode) (post := post)
      hTailFits
      (by simpa [hMidStack] using hMidPc)
      hTailResolved
  have hMidRecord :
      { mid with stack := firstAccumulator :: token :: suffix } = mid := by
    cases mid
    simpa using hMidStack.symm
  have hTailRun :
      Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          tailCode.length mid =
        .ok (.running final) := by
    have hTailRun' := hTailRunRaw
    rw [hMidRecord] at hTailRun'
    simpa [tailCode, List.append_assoc] using hTailRun'
  have hFullRun :
      Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          (headCode.length + tailCode.length)
          { state with stack := token :: suffix } =
        .ok (.running final) := by
    calc
      Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          (headCode.length + tailCode.length)
          { state with stack := token :: suffix } =
        Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          tailCode.length mid :=
            Assembly.Source.runNResult_add_of_running
              (pre ++ headCode ++ tailCode ++ post)
              headCode.length tailCode.length hHeadRun
      _ = .ok (.running final) := hTailRun
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hFullRun
  · simpa [ReturnAddressLower.Terminator.dynamicReturnAccumulator,
      ReturnAddressLower.Terminator.dynamicReturnTests,
      firstAccumulator, headCode, tailCode,
      List.append_assoc] using hFinalStack
  · calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { mid with
              stack :=
                rest.foldl
                    (fun value site =>
                      EvmYul.UInt256.lor
                        (ReturnAddressLower.Terminator.dynamicReturnMatch
                          (pre ++ headCode ++ tailCode ++ post).labelPc
                          token site)
                        value)
                    firstAccumulator ::
                  token :: suffix } := by
        simpa [headCode, tailCode, List.append_assoc] using
          hFinalRuntime
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                rest.foldl
                    (fun value site =>
                      EvmYul.UInt256.lor
                        (ReturnAddressLower.Terminator.dynamicReturnMatch
                          (pre ++ headCode ++ tailCode ++ post).labelPc
                          token site)
                        value)
                    firstAccumulator ::
                  token :: suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := mid)
            (right :=
              { state with
                stack := firstAccumulator :: token :: suffix })
            hMidRuntime
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                ReturnAddressLower.Terminator.dynamicReturnAccumulator
                    (pre ++
                      ReturnAddressLower.Terminator.dynamicReturnTests
                        (first :: rest) ++
                      post).labelPc
                    token (first :: rest) ::
                  token :: suffix } := by
        simp only [
          ReturnAddressLower.Terminator.dynamicReturnAccumulator,
          firstAccumulator]
        rw [hProgramEq]
  · simpa [ReturnAddressLower.Terminator.dynamicReturnTests,
      headCode, tailCode, List.append_assoc] using hFinalPc

set_option maxHeartbeats 800000 in
theorem dynamicReturnCode_openRunUntilTransfer_to_tail
    {depth : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {targetWord : Word} {target : Assembly.EVMState}
    {pre post : Assembly.Program}
    (hBound : depth < 16)
    (hTargetGet : target.stack[depth]? = some targetWord)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (ReturnAddressLower.Terminator.dynamicReturnCode
          depth (first :: rest)))
    (hPc : target.pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++
              ReturnAddressLower.Terminator.dynamicReturnCode
                depth (first :: rest) ++
              post).labelPc site.target =
            some dest) :
    ∃ tested,
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnCode
              depth (first :: rest) ++
            post)
          (ReturnAddressLower.Terminator.dynamicReturnCode
            depth (first :: rest)).length
          target =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnCode
              depth (first :: rest) ++
            post)
          4 tested ∧
      tested.stack =
          ReturnAddressLower.Terminator.dynamicReturnAccumulator
              (pre ++
                ReturnAddressLower.Terminator.dynamicReturnCode
                  depth (first :: rest) ++
                post).labelPc
              targetWord (first :: rest) ::
            targetWord :: target.stack.eraseIdx depth ∧
      Assembly.eraseRuntimeControl tested =
        Assembly.eraseRuntimeControl
          { target with
            stack :=
              ReturnAddressLower.Terminator.dynamicReturnAccumulator
                  (pre ++
                    ReturnAddressLower.Terminator.dynamicReturnCode
                      depth (first :: rest) ++
                    post).labelPc
                  targetWord (first :: rest) ::
                targetWord :: target.stack.eraseIdx depth } ∧
      tested.pc =
        (pre ++
          Assembly.StackShuffle.liftBuriedToTop depth ++
          ReturnAddressLower.Terminator.dynamicReturnTests
            (first :: rest)).pcAfter := by
  let front := target.stack.take depth
  let suffix := target.stack.drop (depth + 1)
  let lift := Assembly.StackShuffle.liftBuriedToTop depth
  let tests :=
    ReturnAddressLower.Terminator.dynamicReturnTests
      (first :: rest)
  let tail : Assembly.Program :=
    [ .jumpi first.caseLabel
    , .prim .invalid
    , .label first.caseLabel
    , .jumpDynamic
    ]
  let code :=
    ReturnAddressLower.Terminator.dynamicReturnCode
      depth (first :: rest)
  have hTargetStack :
      target.stack = front ++ targetWord :: suffix := by
    simpa [front, suffix] using
      (list_eq_take_get_drop hTargetGet)
  have hDepthLt : depth < target.stack.length :=
    (List.getElem?_eq_some_iff.mp hTargetGet).choose
  have hFrontLength : front.length = depth := by
    simp [front, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hDepthLt)]
  have hErase :
      target.stack.eraseIdx depth = front ++ suffix := by
    simpa [front, suffix] using
      (eraseIdx_eq_take_drop_of_get? hTargetGet)
  have hCodeEq : code = lift ++ tests ++ tail := by
    simp [code, lift, tests, tail,
      ReturnAddressLower.Terminator.dynamicReturnCode,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (lift ++ tests ++ tail) := by
    simpa [code, hCodeEq] using hFits
  have hLiftFits :
      Assembly.Program.PCFitsFrom pre lift := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [List.append_assoc] using hFitsAll
  have hAfterLiftFits :
      Assembly.Program.PCFitsFrom (pre ++ lift)
        (tests ++ tail) := by
    apply Assembly.Program.PCFitsFrom.right
    simpa [List.append_assoc] using hFitsAll
  have hTestsFits :
      Assembly.Program.PCFitsFrom (pre ++ lift) tests :=
    Assembly.Program.PCFitsFrom.left hAfterLiftFits
  let mid : Assembly.EVMState :=
    { target with
      stack := targetWord :: front ++ suffix
      pc := (pre ++ lift).pcAfter }
  have hInitialRecord :
      { target with stack := front ++ targetWord :: suffix } =
        target := by
    cases target
    simpa using hTargetStack.symm
  have hLift :=
    Assembly.StackShuffle.InteractionPreservation.liftBuriedToTop_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (front := front) (suffix := suffix)
      (token := targetWord) (pre := pre)
      (post := tests ++ tail ++ post)
      (state := target) (fuel := 4 + tests.length)
      (by simpa [hFrontLength, lift] using hLiftFits)
      (by simpa [hInitialRecord] using hPc)
      (by omega)
  have hLiftRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) code.length target =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) (4 + tests.length) mid := by
    have hLift' := hLift
    rw [hFrontLength] at hLift'
    rw [hInitialRecord] at hLift'
    rw [show
      code.length =
        (4 + tests.length) + lift.length by
      rw [hCodeEq]
      simp [tail]
      omega]
    simpa [hCodeEq, lift, mid, List.append_assoc] using hLift'
  have hResolvedTests :
      ∀ site ∈ first :: rest,
        ∃ dest,
          ((pre ++ lift) ++ tests ++ tail ++ post).labelPc
              site.target =
            some dest := by
    intro site hSite
    obtain ⟨dest, hDest⟩ := hResolved site hSite
    exact
      ⟨dest,
        by
          simpa [code, hCodeEq, List.append_assoc] using hDest⟩
  obtain ⟨tested, hTestsRun, hTestedStack,
      hTestedRuntime, hTestedPc⟩ :=
    dynamicReturnTests_source_run
      (state := mid) (suffix := front ++ suffix)
      (token := targetWord) (first := first) (rest := rest)
      (pre := pre ++ lift) (post := tail ++ post)
      (by simpa [tests] using hTestsFits)
      (by simp [mid])
      (by
        intro site hSite
        simpa [tests, List.append_assoc] using
          hResolvedTests site hSite)
  have hMidRecord :
      { mid with stack := targetWord :: (front ++ suffix) } =
        mid := by
    simp [mid]
  have hTestsRun' :
      Assembly.Source.runNResult
          ((pre ++ lift) ++ tests ++ (tail ++ post))
          tests.length mid =
        .ok (.running tested) := by
    have hRun := hTestsRun
    rw [hMidRecord] at hRun
    simpa [tests, List.append_assoc] using hRun
  have hTestsOpen :=
    returnGuardCode_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (code := tests) (pre := pre ++ lift)
      (post := tail ++ post) (state := mid)
      (final := tested) 4
      (dynamicReturnTests_returnGuard (first :: rest))
      hTestsFits (by simp [mid]) hTestsRun'
  have hTestsOpen' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) (4 + tests.length) mid =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) 4 tested := by
    simpa [hCodeEq, List.append_assoc] using hTestsOpen
  refine ⟨tested, hLiftRun.trans hTestsOpen', ?_, ?_, ?_⟩
  · simpa [code, tests, hCodeEq, hErase, List.append_assoc] using
      hTestedStack
  · calc
      Assembly.eraseRuntimeControl tested =
          Assembly.eraseRuntimeControl
            { mid with
              stack :=
                ReturnAddressLower.Terminator.dynamicReturnAccumulator
                    ((pre ++ lift) ++ tests ++ tail ++ post).labelPc
                    targetWord (first :: rest) ::
                  targetWord :: front ++ suffix } := by
            simpa [tests, List.append_assoc] using hTestedRuntime
      _ =
          Assembly.eraseRuntimeControl
            { target with
              stack :=
                ReturnAddressLower.Terminator.dynamicReturnAccumulator
                    ((pre ++ lift) ++ tests ++ tail ++ post).labelPc
                    targetWord (first :: rest) ::
                  targetWord :: front ++ suffix } := by
            cases target
            rfl
      _ =
          Assembly.eraseRuntimeControl
            { target with
              stack :=
                ReturnAddressLower.Terminator.dynamicReturnAccumulator
                    (pre ++ code ++ post).labelPc
                    targetWord (first :: rest) ::
                  targetWord :: target.stack.eraseIdx depth } := by
            simp [hCodeEq, hErase, List.append_assoc]
  · simpa [tests, List.append_assoc] using hTestedPc

theorem dynamicReturnAccumulator_eq_zero_iff_findTarget?_eq_none
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : Block} {shape : Shape} {returnCount depth : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {token targetWord : Word} {slot : Slot}
    {target source : Assembly.EVMState}
    (hBlock : block ∈ cfg.blocks)
    (hTerm :
      block.term =
        .returnDispatch returnCount (first :: rest))
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hAssemblyFits : assembly.PCFits)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest, assembly.labelPc site.target = some dest)
    (hSlot : shape.slots[depth]? = some slot)
    (hReturn : ReturnSlot slot)
    (hTargetGet : target.stack[depth]? = some targetWord)
    (hSourceGet : source.stack[depth]? = some token)
    (hRel :
      RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        shape target source) :
    ReturnAddressLower.Terminator.dynamicReturnAccumulator
          assembly.labelPc targetWord (first :: rest) =
        EvmYul.UInt256.ofNat 0 ↔
      Block.ReturnSite.findTarget? token (first :: rest) = none := by
  have hAddress :=
    returnSlot_address hSlot hReturn hTargetGet hSourceGet hRel
  obtain
      ⟨globalSite, hGlobal, hGlobalToken,
        globalPc, hGlobalResolve, hTargetWord⟩ :=
    hAddress
  have hTokensUnique' :=
    ReturnAddressLower.tokensUnique_of_check hTokensUnique
  have hTargetsUnique' :=
    ReturnAddressLower.targetsUnique_of_check hTargetsUnique
  cases hFind :
      Block.ReturnSite.findTarget? token (first :: rest) with
  | none =>
      constructor
      · intro _hAccumulator
        rfl
      · intro _hNone
        apply
          (dynamicReturnAccumulator_eq_zero_iff
            assembly.labelPc targetWord first rest).2
        intro candidate hCandidate
        have hCandidateGlobal :
            candidate ∈ ReturnAddressLower.Program.returnSites cfg := by
          apply ReturnAddressLower.term_site_mem_returnSites hBlock
          simp [ReturnAddressLower.Terminator.sites, hTerm, hCandidate]
        obtain ⟨candidatePc, hCandidateResolve⟩ :=
          hResolved candidate hCandidate
        unfold ReturnAddressLower.Terminator.dynamicReturnMatch
        rw [hCandidateResolve]
        have hCandidateTokenNe :
            candidate.token ≠ token :=
          TypedCfg.Preservation.ReturnSite.findTarget?_eq_none_all_ne
            hFind candidate hCandidate
        by_cases hPhysical :
            EvmYul.UInt256.ofNat candidatePc = targetWord
        · have hPcEq : candidatePc = globalPc := by
            have hWords :
                EvmYul.UInt256.ofNat candidatePc =
                  EvmYul.UInt256.ofNat globalPc :=
              hPhysical.trans hTargetWord
            have hNats :=
              congrArg EvmYul.UInt256.toNat hWords
            simpa [
              Assembly.Program.toNat_ofNat_labelPc
                hAssemblyFits hCandidateResolve,
              Assembly.Program.toNat_ofNat_labelPc
                hAssemblyFits hGlobalResolve] using hNats
          have hTargetEq : candidate.target = globalSite.target := by
            exact
              label_eq_of_labelPc_eq_some
                hCandidateResolve
                (by simpa [hPcEq] using hGlobalResolve)
          have hSiteEq : candidate = globalSite :=
            hTargetsUnique'.eq_of_mem
              hCandidateGlobal hGlobal hTargetEq
          subst candidate
          exact False.elim
            (hCandidateTokenNe hGlobalToken.symm)
        · simp [EvmYul.UInt256.eq, hPhysical]
  | some targetLabel =>
      constructor
      · intro hAccumulator
        obtain
            ⟨selected, hSelectedLocal,
              hSelectedToken, _hSelectedTarget⟩ :=
          Block.ReturnSite.mem_token_of_findTarget?_eq_some hFind
        have hSelectedGlobal :
            selected ∈ ReturnAddressLower.Program.returnSites cfg := by
          apply ReturnAddressLower.term_site_mem_returnSites hBlock
          simp [ReturnAddressLower.Terminator.sites, hTerm,
            hSelectedLocal]
        obtain ⟨selectedPc, hSelectedResolve,
            hSelectedWord, _hErasedRel⟩ :=
          returnSlot_target_of_unique hTokensUnique'
            hSelectedGlobal hSelectedToken hRel.2
            hSlot hReturn hTargetGet hSourceGet
        have hAll :=
          (dynamicReturnAccumulator_eq_zero_iff
            assembly.labelPc targetWord first rest).1 hAccumulator
        have hSelectedZero := hAll selected hSelectedLocal
        unfold ReturnAddressLower.Terminator.dynamicReturnMatch at hSelectedZero
        rw [hSelectedResolve] at hSelectedZero
        have hPhysical :
            EvmYul.UInt256.ofNat selectedPc = targetWord :=
          hSelectedWord.symm
        simp [EvmYul.UInt256.eq, hPhysical] at hSelectedZero
        have hOneNeZero :
            EvmYul.UInt256.ofNat 1 ≠
              EvmYul.UInt256.ofNat 0 := by
          decide
        exact False.elim (hOneNeZero hSelectedZero)
      · intro hNone
        simp at hNone

theorem returnDispatch_eventually
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : Block} {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word} {targetLabel : Label}
    {slot : Slot} {targetWord : Word}
    {target source : Assembly.EVMState}
    {pre post : Assembly.Program}
    (hBlock : block ∈ cfg.blocks)
    (hTerm : block.term = .returnDispatch returnCount sites)
    (hUnique : ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hSlot : shape.slots[depth]? = some slot)
    (hReturn : ReturnSlot slot)
    (hCount : depth = returnCount)
    (hBound : depth < 16)
    (hTargetGet : target.stack[depth]? = some targetWord)
    (hSourceGet : source.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = some targetLabel)
    (hAssembly : assembly =
      pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
    (hFits : Assembly.Program.PCFitsFrom pre
      (ReturnAddressLower.Terminator.dynamicReturnTransferCode depth))
    (hPc : target.pc = pre.pcAfter)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    exists targetAfter targetPc,
      Assembly.Source.Eventually assembly target
        (fun outcome => outcome = .ok (.running targetAfter)) ∧
      assembly.labelPc targetLabel = some targetPc ∧
      targetAfter.pc = EvmYul.UInt256.ofNat targetPc ∧
      Block.runTerm shape (.returnDispatch returnCount sites) source =
        .jump targetLabel
          { source with stack := source.stack.eraseIdx depth } ∧
      RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (shape.erase depth) targetAfter
        { source with stack := source.stack.eraseIdx depth } := by
  subst returnCount
  subst assembly
  obtain ⟨selected, hSelectedLocal, hSelectedToken, hSelectedTarget⟩ :=
    Block.ReturnSite.mem_token_of_findTarget?_eq_some hFind
  have hSelectedGlobal :
      selected ∈ ReturnAddressLower.Program.returnSites cfg := by
    apply ReturnAddressLower.term_site_mem_returnSites hBlock
    simp [ReturnAddressLower.Terminator.sites, hTerm, hSelectedLocal]
  have hUnique' := ReturnAddressLower.tokensUnique_of_check hUnique
  obtain ⟨targetPc, hResolve, hTargetWord, hErasedRel⟩ :=
    returnSlot_target_of_unique hUnique' hSelectedGlobal hSelectedToken
      hRel.2 hSlot hReturn hTargetGet hSourceGet
  have hTargetStack :
      target.stack = target.stack.take depth ++
        targetWord :: target.stack.drop (depth + 1) :=
    list_eq_take_get_drop hTargetGet
  have hDepthLt : depth < target.stack.length :=
    (List.getElem?_eq_some_iff.mp hTargetGet).choose
  have hFrontLength : (target.stack.take depth).length = depth := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hDepthLt)]
  have hLiftFits : Assembly.Program.PCFitsFrom pre
      (Assembly.StackShuffle.liftBuriedToTop depth) := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
      List.append_assoc] using hFits
  have hJumpFits :
      Assembly.Program.PCFitsFrom
        (pre ++ Assembly.StackShuffle.liftBuriedToTop depth)
        [.jumpDynamic] := by
    have := Assembly.Program.PCFitsFrom.right hFits
    simpa [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
      List.append_assoc] using this
  have hLift :=
    Assembly.StackShuffle.liftBuriedToTop_source_exists
      (state := target)
      (front := target.stack.take depth)
      (suffix := target.stack.drop (depth + 1))
      (token := targetWord) (pre := pre)
      (post := [.jumpDynamic] ++ post)
      (by simpa [hFrontLength] using hLiftFits)
      (by simpa [hTargetStack] using hPc)
      (by omega)
  have hLift' :
      Assembly.Source.Eventually
        (pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
        target
        (fun outcome =>
          match outcome with
          | .ok (.running final) =>
              final.stack = targetWord :: target.stack.take depth ++
                  target.stack.drop (depth + 1) ∧
                Assembly.eraseRuntimeControl final =
                  Assembly.eraseRuntimeControl
                    { target with
                      stack := targetWord :: target.stack.take depth ++
                        target.stack.drop (depth + 1) } ∧
                final.pc =
                  (pre ++ Assembly.StackShuffle.liftBuriedToTop depth).pcAfter
          | _ => False) := by
    have hLiftNormalized := hLift
    rw [hFrontLength] at hLiftNormalized
    rw [← hTargetStack] at hLiftNormalized
    simpa only [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
      List.append_assoc] using hLiftNormalized
  have hErase :
      target.stack.eraseIdx depth =
        target.stack.take depth ++ target.stack.drop (depth + 1) :=
    eraseIdx_eq_take_drop_of_get? hTargetGet
  have hRunRel :
      Assembly.Source.Eventually
        (pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
        target
        (fun outcome =>
          match outcome with
          | .ok (.running final) =>
              final.pc = targetWord ∧
                RuntimeRel
                  (pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++
                    post).labelPc
                  (ReturnAddressLower.Program.returnSites cfg)
                  (shape.erase depth) final
                  { source with stack := source.stack.eraseIdx depth }
          | _ => False) := by
    apply Assembly.Source.Eventually.bind_running hLift'
    intro mid hMid
    have hJump := jumpDynamic_eventually
      (pre := pre ++ Assembly.StackShuffle.liftBuriedToTop depth)
      (post := post) (state := mid) (destination := targetWord)
      (stack := target.stack.take depth ++ target.stack.drop (depth + 1))
      (Assembly.Program.PCFitsFrom.start hJumpFits) hMid.2.2
      (by simpa [hFrontLength] using hMid.1)
    have hJump' := hJump
    rw [show
      pre ++ Assembly.StackShuffle.liftBuriedToTop depth ++
          [.jumpDynamic] ++ post =
        pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post by
      simp [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
        List.append_assoc]] at hJump'
    apply Assembly.Source.Eventually.mono hJump'
    intro outcome hOutcome
    rw [hOutcome]
    constructor
    · simp
    · constructor
      · have hShared := congrArg EvmYul.EVM.State.toSharedState hMid.2.1
        calc
          mid.toSharedState = target.toSharedState := by
            simpa [Assembly.eraseRuntimeControl] using hShared
          _ = source.toSharedState := hRel.1
      · simpa [ShapeStackRel, Shape.erase, hErase] using hErasedRel
  rcases hRunRel with ⟨fuel, outcome, hRun, hPost⟩
  cases outcome with
  | error err => cases hPost
  | ok result =>
    cases result with
    | halted halt => cases hPost
    | running targetAfter =>
      simp only at hPost
      refine ⟨targetAfter, targetPc, ⟨fuel, _, hRun, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simpa [hSelectedTarget] using hResolve
      · exact hPost.1.trans hTargetWord
      · simp [Block.runTerm, hDepth, hSourceGet, hFind]
      · exact hPost.2

set_option maxHeartbeats 1000000 in
theorem returnDispatch_guarded_openRunUntilTransfer_runtimeRel
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : Block} {shape : Shape} {returnCount depth : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {token targetWord : Word} {slot : Slot}
    {target source : Assembly.EVMState}
    {pre post : Assembly.Program}
    (hBlock : block ∈ cfg.blocks)
    (hTerm :
      block.term =
        .returnDispatch returnCount (first :: rest))
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hSlot : shape.slots[depth]? = some slot)
    (hReturn : ReturnSlot slot)
    (hCount : depth = returnCount)
    (hBound : depth < 16)
    (hTargetGet : target.stack[depth]? = some targetWord)
    (hSourceGet : source.stack[depth]? = some token)
    (hAssembly :
      assembly =
        pre ++
          ReturnAddressLower.Terminator.dynamicReturnCode
            depth (first :: rest) ++
          post)
    (hAssemblyFits : assembly.PCFits)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (ReturnAddressLower.Terminator.dynamicReturnCode
          depth (first :: rest)))
    (hPc : target.pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest, assembly.labelPc site.target = some dest)
    (hLabels : assembly.labels.Nodup)
    (hRel :
      RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        shape target source) :
    Simulation.Interaction.Rel
      (LoweredTerminatorResultRel
        assembly assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (shape.erase depth))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        assembly
        (ReturnAddressLower.Terminator.dynamicReturnCode
          depth (first :: rest)).length
        target)
      (.done
        (TypedCfg.Block.runTermChecked shape
          (.returnDispatch returnCount (first :: rest)) source)) := by
  subst returnCount
  subst assembly
  let code :=
    ReturnAddressLower.Terminator.dynamicReturnCode
      depth (first :: rest)
  let lift := Assembly.StackShuffle.liftBuriedToTop depth
  let tests :=
    ReturnAddressLower.Terminator.dynamicReturnTests
      (first :: rest)
  let tail : Assembly.Program :=
    [ .jumpi first.caseLabel
    , .prim .invalid
    , .label first.caseLabel
    , .jumpDynamic
    ]
  have hCodeEq : code = lift ++ tests ++ tail := by
    simp [code, lift, tests, tail,
      ReturnAddressLower.Terminator.dynamicReturnCode,
      List.append_assoc]
  have hResolved' :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++ code ++ post).labelPc site.target =
            some dest := by
    simpa [code] using hResolved
  obtain ⟨tested, hPrefixRun, hTestedStack,
      hTestedRuntime, hTestedPc⟩ :=
    dynamicReturnCode_openRunUntilTransfer_to_tail
      (depth := depth) (first := first) (rest := rest)
      (targetWord := targetWord) (target := target)
      (pre := pre) (post := post)
      hBound hTargetGet
      (by simpa [code] using hFits)
      hPc
      (by simpa [code] using hResolved')
  let accumulator :=
    ReturnAddressLower.Terminator.dynamicReturnAccumulator
      (pre ++ code ++ post).labelPc
      targetWord (first :: rest)
  have hTestedStack' :
      tested.stack =
        accumulator :: targetWord ::
          target.stack.eraseIdx depth := by
    simpa [accumulator, code] using hTestedStack
  have hTestedRecord :
      { tested with
        stack :=
          accumulator :: targetWord ::
            target.stack.eraseIdx depth } =
        tested := by
    cases tested
    simpa using hTestedStack'.symm
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (lift ++ tests ++ tail) := by
    simpa [code, hCodeEq] using hFits
  have hAfterLiftFits :
      Assembly.Program.PCFitsFrom (pre ++ lift)
        (tests ++ tail) := by
    apply Assembly.Program.PCFitsFrom.right
    simpa [List.append_assoc] using hFitsAll
  have hTailFits :
      Assembly.Program.PCFitsFrom
        (pre ++ lift ++ tests) tail := by
    have hRight :=
      Assembly.Program.PCFitsFrom.right hAfterLiftFits
    simpa [List.append_assoc] using hRight
  have hTailRunRaw :=
    dynamicReturnTail_openRunUntilTransferWithPolicy
      (caseLabel := first.caseLabel)
      (accumulator := accumulator) (token := targetWord)
      (suffix := target.stack.eraseIdx depth)
      (pre := pre ++ lift ++ tests) (post := post)
      (state := tested)
      (by simpa [tail] using hTailFits)
      (by
        simpa [hTestedRecord, lift, tests,
          List.append_assoc] using hTestedPc)
      (by
        simpa [code, hCodeEq, tail,
          List.append_assoc] using hLabels)
  have hTailRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) 4 tested =
        if accumulator = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done
            (.ok
              (.running
                { tested with
                  stack := target.stack.eraseIdx depth
                  pc := targetWord })) := by
    have hRun := hTailRunRaw
    rw [hTestedRecord] at hRun
    simpa [hCodeEq, tail, List.append_assoc] using hRun
  have hFullRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) code.length target =
        if accumulator = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done
            (.ok
              (.running
                { tested with
                  stack := target.stack.eraseIdx depth
                  pc := targetWord })) := by
    have hPrefixRun' :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ code ++ post) code.length target =
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ code ++ post) 4 tested := by
      simpa [code] using hPrefixRun
    exact hPrefixRun'.trans hTailRun
  have hAccumulator :=
    dynamicReturnAccumulator_eq_zero_iff_findTarget?_eq_none
      (cfg := cfg) (assembly := pre ++ code ++ post)
      (block := block) (shape := shape)
      (returnCount := depth) (depth := depth)
      (first := first) (rest := rest)
      (token := token) (targetWord := targetWord)
      (slot := slot) (target := target) (source := source)
      hBlock hTerm hTokensUnique hTargetsUnique
      (by simpa [code] using hAssemblyFits)
      (by simpa [code] using hResolved')
      hSlot hReturn hTargetGet hSourceGet
      (by simpa [code] using hRel)
  cases hFind :
      Block.ReturnSite.findTarget? token (first :: rest) with
  | none =>
      have hZero : accumulator = EvmYul.UInt256.ofNat 0 :=
        hAccumulator.2 hFind
      have hRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              (pre ++ code ++ post) code.length target =
            .done (.error .InvalidInstruction) := by
        simpa [hZero] using hFullRun
      have hSourceRun :
          TypedCfg.Block.runTermChecked shape
              (.returnDispatch depth (first :: rest)) source =
            .ok (.invalid source) := by
        simp [TypedCfg.Block.runTermChecked,
          TypedCfg.Block.runTerm, hDepth, hSourceGet, hFind]
      rw [hRun, hSourceRun]
      apply Simulation.Interaction.Rel.done
      refine ⟨.ok (.invalid source), ?_, ?_⟩
      · simp [TypedCfg.Preservation.Block.RunSimulates,
          TypedCfg.Preservation.Outcome.Simulates]
      · exact Simulation.Interaction.ExceptRel.ok
          (by simp [OutcomeRuntimeRel])
  | some targetLabel =>
      have hNonzero :
          accumulator ≠ EvmYul.UInt256.ofNat 0 := by
        intro hZero
        have hNone := hAccumulator.1 hZero
        rw [hFind] at hNone
        cases hNone
      let final : Assembly.EVMState :=
        { tested with
          stack := target.stack.eraseIdx depth
          pc := targetWord }
      have hRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              (pre ++ code ++ post) code.length target =
            .done (.ok (.running final)) := by
        simpa [hNonzero, final] using hFullRun
      obtain ⟨selected, hSelectedLocal,
          hSelectedToken, hSelectedTarget⟩ :=
        Block.ReturnSite.mem_token_of_findTarget?_eq_some hFind
      have hSelectedGlobal :
          selected ∈
            ReturnAddressLower.Program.returnSites cfg := by
        apply ReturnAddressLower.term_site_mem_returnSites hBlock
        simp [ReturnAddressLower.Terminator.sites,
          hTerm, hSelectedLocal]
      have hTokensUnique' :=
        ReturnAddressLower.tokensUnique_of_check hTokensUnique
      obtain ⟨targetPc, hResolve, hTargetWord,
          _hErasedSelected⟩ :=
        returnSlot_target_of_unique hTokensUnique'
          hSelectedGlobal hSelectedToken hRel.2
          hSlot hReturn hTargetGet hSourceGet
      have hErasedStack :=
        stackRel_eraseIdx hRel.2 hSlot
      have hTestedShared :
          tested.toSharedState = target.toSharedState := by
        have hShared :=
          congrArg EvmYul.EVM.State.toSharedState
            hTestedRuntime
        simpa [accumulator, code,
          Assembly.eraseRuntimeControl] using hShared
      have hFinalRel :
          RuntimeRel
            (pre ++ code ++ post).labelPc
            (ReturnAddressLower.Program.returnSites cfg)
            (shape.erase depth) final
            { source with
              stack := source.stack.eraseIdx depth } := by
        constructor
        · calc
            final.toSharedState = tested.toSharedState := by
              simp [final]
            _ = target.toSharedState := hTestedShared
            _ = source.toSharedState := hRel.1
        · simpa [final, ShapeStackRel, Shape.erase] using
            hErasedStack
      have hSourceRun :
          TypedCfg.Block.runTermChecked shape
              (.returnDispatch depth (first :: rest)) source =
            .ok
              (.jump targetLabel
                { source with
                  stack := source.stack.eraseIdx depth }) := by
        simp [TypedCfg.Block.runTermChecked,
          TypedCfg.Block.runTerm, hDepth, hSourceGet, hFind]
      rw [hRun, hSourceRun]
      apply Simulation.Interaction.Rel.done
      refine
        ⟨.ok (.jump targetLabel final), ?_, ?_⟩
      · change TypedCfg.Preservation.Outcome.Simulates
          (pre ++ code ++ post)
          (.jump targetLabel final)
          (.ok (.running final))
        refine ⟨targetPc, ?_, ?_, ?_⟩
        · simpa [hSelectedTarget] using hResolve
        · exact
            calc
              final.pc = targetWord := by rfl
              _ = EvmYul.UInt256.ofNat targetPc :=
                hTargetWord
        · exact Assembly.SameRuntimeData.refl final
      · exact Simulation.Interaction.ExceptRel.ok
          (by simpa [OutcomeRuntimeRel] using hFinalRel)

set_option maxHeartbeats 1000000 in
theorem terminator_lowerAt_openRunUntilTransfer_runtimeRel
    {cfg : TypedCfg.Program} {block : Block}
    {shape : Shape} {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hBlock : block ∈ cfg.blocks)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hType : block.term.type? cfg shape = some ())
    (hLower :
      ReturnAddressLower.Terminator.lowerAt?
          shape block.term =
        some code)
    (hAssemblyFits : (pre ++ code ++ post).PCFits)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        shape target source) :
    Simulation.Interaction.Rel
      (LoweredTerminatorResultRel
        (pre ++ code ++ post)
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (terminatorOutputShape shape block.term))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
          block.term)
        (pre ++ code ++ post) code.length target)
      (.done
        (TypedCfg.Block.runTermChecked
          shape block.term source)) := by
  cases hTerm : block.term with
  | fallthrough next =>
      exact
        lowerAt_openRunUntilTransfer_runtimeRel_of_not_returnDispatch
          (cfg := cfg)
          (term := .fallthrough next)
          (fun returnCount sites hFalse =>
            by cases hFalse)
          (by simpa [hTerm] using hType)
          (by simpa [hTerm] using hLower)
          hFits hPc
          (by
            constructor
            · simpa [hTerm] using hResolved
            · intro internal hInternal
              simp [TypedCfg.Terminator.definedLabels] at hInternal)
          hLabels
          (by simpa using hRel)
  | jump label =>
      exact
        lowerAt_openRunUntilTransfer_runtimeRel_of_not_returnDispatch
          (cfg := cfg)
          (term := .jump label)
          (fun returnCount sites hFalse =>
            by cases hFalse)
          (by simpa [hTerm] using hType)
          (by simpa [hTerm] using hLower)
          hFits hPc
          (by
            constructor
            · simpa [hTerm] using hResolved
            · intro internal hInternal
              simp [TypedCfg.Terminator.definedLabels] at hInternal)
          hLabels
          (by simpa using hRel)
  | jumpi targetLabel nextLabel =>
      exact
        lowerAt_openRunUntilTransfer_runtimeRel_of_not_returnDispatch
          (cfg := cfg)
          (term := .jumpi targetLabel nextLabel)
          (fun returnCount sites hFalse =>
            by cases hFalse)
          (by simpa [hTerm] using hType)
          (by simpa [hTerm] using hLower)
          hFits hPc
          (by
            constructor
            · simpa [hTerm] using hResolved
            · intro internal hInternal
              simp [TypedCfg.Terminator.definedLabels] at hInternal)
          hLabels
          (by simpa using hRel)
  | halt kind =>
      exact
        lowerAt_openRunUntilTransfer_runtimeRel_of_not_returnDispatch
          (cfg := cfg)
          (term := .halt kind)
          (fun returnCount sites hFalse =>
            by cases hFalse)
          (by simpa [hTerm] using hType)
          (by simpa [hTerm] using hLower)
          hFits hPc
          (by
            constructor
            · simpa [hTerm] using hResolved
            · intro internal hInternal
              simp [TypedCfg.Terminator.definedLabels] at hInternal)
          hLabels
          (by simpa using hRel)
  | invalid =>
      exact
        lowerAt_openRunUntilTransfer_runtimeRel_of_not_returnDispatch
          (cfg := cfg)
          (term := .invalid)
          (fun returnCount sites hFalse =>
            by cases hFalse)
          (by simpa [hTerm] using hType)
          (by simpa [hTerm] using hLower)
          hFits hPc
          (by
            constructor
            · simpa [hTerm] using hResolved
            · intro internal hInternal
              simp [TypedCfg.Terminator.definedLabels] at hInternal)
          hLabels
          (by simpa using hRel)
  | returnDispatch returnCount sites =>
      obtain ⟨depth, hDepth, hSites, hCount,
          hBound, hCode⟩ :=
        ReturnAddressLower.Terminator.lowerAt?_returnDispatch_parts
          (by simpa [hTerm] using hLower)
      cases sites with
      | nil =>
          exact False.elim (hSites rfl)
      | cons first rest =>
          obtain ⟨slot, hSlot, hReturn⟩ :=
            returnSlot_get_of_returnTokenDepth?_eq_some hDepth
          obtain ⟨targetWord, sourceToken,
              hTargetGet, hSourceGet, _hWordRel⟩ :=
            stackRel_get_exists hRel.2 hSlot
          have hResolvedSites :
              ∀ site ∈ first :: rest,
                ∃ dest,
                  (pre ++ code ++ post).labelPc
                      site.target =
                    some dest := by
            intro site hSite
            exact hResolved site.target
              (by
                rw [hTerm]
                exact
                  List.mem_map.mpr
                    ⟨site, hSite, rfl⟩)
          have hGuarded :=
            returnDispatch_guarded_openRunUntilTransfer_runtimeRel
              (cfg := cfg) (assembly := pre ++ code ++ post)
              (block := block) (shape := shape)
              (returnCount := returnCount) (depth := depth)
              (first := first) (rest := rest)
              (token := sourceToken) (targetWord := targetWord)
              (slot := slot) (target := target) (source := source)
              (pre := pre) (post := post)
              hBlock
              (by simpa [hTerm])
              hTokensUnique hTargetsUnique
              hDepth hSlot hReturn hCount hBound
              hTargetGet hSourceGet
              (by simpa [hCode])
              hAssemblyFits
              (by simpa [hCode] using hFits)
              hPc hResolvedSites hLabels hRel
          simpa [hTerm, hDepth, hCode,
            terminatorOutputShape,
            TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy]
            using hGuarded

set_option maxHeartbeats 1000000 in
theorem block_lower?_openRun_runtimeRel
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {code pre post : Assembly.Program}
    {target source : Assembly.EVMState}
    (hBlock : block ∈ cfg.blocks)
    (hTyped : block.WellTyped cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hLower :
      ReturnAddressLower.Block.lower? cfg block = some code)
    (hAssemblyFits : (pre ++ code ++ post).PCFits)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : target.pc = pre.pcAfter)
    (hTargets :
      ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
        ∃ pc, (pre ++ code ++ post).labelPc site.target = some pc)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup)
    (hRel :
      RuntimeRel (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input target.incrPC source) :
    Simulation.Interaction.Rel
      (LoweredBlockResultRel
        (pre ++ code ++ post)
        (pre ++ code ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (terminatorOutputShape block.output block.term))
      (CompiledBlock.openRun cfg block
        (pre ++ code ++ post) target)
      (TypedCfg.InteractionSemantics.Block.openRun block source) := by
  unfold ReturnAddressLower.Block.lower? at hLower
  cases hBody :
      ReturnAddressLower.Block.lowerBodyFrom?
        cfg block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm :
            ReturnAddressLower.Terminator.lowerAt?
              block.output block.term with
        | none =>
            simp [hBody, hTerm] at hLower
        | some termCode =>
            simp [hBody, hTerm] at hLower
            subst code
            let program :=
              pre ++ Assembly.Instr.label block.label ::
                (bodyCode ++ termCode) ++ post
            let entry := target.incrPC
            have hLabelOpen :
                Assembly.InteractionSemantics.Source.openStepAtResult
                    (pre ++ Assembly.Instr.label block.label ::
                      ((bodyCode ++ termCode) ++ post))
                    pre.byteLength
                    (.label block.label) target =
                  .done (.ok (.running entry)) := by
              rw [
                Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
                  (by rfl)]
              simp [Assembly.Source.stepAtResult,
                Assembly.Source.stepAt,
                Assembly.Instr.haltKind?,
                Assembly.Target.stepInstr, entry]
            have hLabelRun :
                Assembly.InteractionSemantics.Source.openRunNResult
                    program 1 target =
                  .done (.ok (.running entry)) := by
              rw [show
                program =
                  pre ++ Assembly.Instr.label block.label ::
                    ((bodyCode ++ termCode) ++ post) by
                simp [program, List.append_assoc]]
              rw [
                Assembly.InteractionPreservation.source_openRunNResult_one_at_boundary
                  hFits.1 hPc]
              exact hLabelOpen
            have hBodyFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label])
                  bodyCode :=
              Assembly.Program.PCFitsFrom.left hFits.2
            have hTermFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label] ++
                    bodyCode)
                  termCode := by
              simpa [List.append_assoc] using
                Assembly.Program.PCFitsFrom.right hFits.2
            have hBodyTargets :
                ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
                  ∃ pc,
                    ((pre ++ [Assembly.Instr.label block.label]) ++
                      bodyCode ++ (termCode ++ post)).labelPc
                        site.target =
                      some pc := by
              simpa [program, List.append_assoc] using hTargets
            have hEntryRel :
                RuntimeRel
                  ((pre ++ [Assembly.Instr.label block.label]) ++
                    bodyCode ++ (termCode ++ post)).labelPc
                  (ReturnAddressLower.Program.returnSites cfg)
                  block.input entry source := by
              simpa [program, entry, List.append_assoc] using hRel
            have hEntryPc :
                entry.pc =
                  (pre ++
                    [Assembly.Instr.label block.label]).pcAfter := by
              calc
                entry.pc =
                    target.pc + EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                  rw [hPc]
                _ =
                    (pre ++
                      [Assembly.Instr.label block.label]).pcAfter := by
                  simp [Assembly.Program.pcAfter,
                    Assembly.Program.byteLength_append,
                    Assembly.Program.byteLength,
                    Assembly.Instr.byteSize,
                    Assembly.UInt256_ofNat_add]
            have hBodyRun :=
              lowerBodyFrom?_openRunNResult_runtimeRel
                (pre := pre ++ [Assembly.Instr.label block.label])
                (post := termCode ++ post)
                hBody hBodyTargets hBodyFits hEntryPc hEntryRel
            have hRest :
                Simulation.Interaction.Rel
                  (LoweredBlockResultRel
                    program program.labelPc
                    (ReturnAddressLower.Program.returnSites cfg)
                    (terminatorOutputShape block.output block.term))
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | .running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | .halted halt =>
                        pure (.halted halt))
                  (TypedCfg.InteractionSemantics.Block.openRun
                    block source) := by
              unfold TypedCfg.InteractionSemantics.Block.openRun
                TypedCfg.Control.Block.run
              apply Simulation.Interaction.Rel.bind_custom
                (by simpa [program, List.append_assoc] using hBodyRun)
              intro targetDone sourceDone hDone
              cases targetDone with
              | error targetError =>
                  cases sourceDone with
                  | error sourceError =>
                      cases hDone with
                      | error _ =>
                          exact Simulation.Interaction.Rel.done
                            (by trivial)
                  | ok sourceResult =>
                      cases hDone
              | ok targetResult =>
                  cases sourceDone with
                  | error sourceError =>
                      cases hDone
                  | ok sourceResult =>
                      cases hDone with
                      | ok hValue =>
                          rcases sourceResult with
                            ⟨sourceAfter, actualOutput⟩
                          cases targetResult with
                          | halted halt =>
                              exact False.elim hValue
                          | running targetAfter =>
                              have hActualOutput :
                                  actualOutput = block.output :=
                                hValue.2.1
                              subst actualOutput
                              have hTermPc :
                                  targetAfter.pc =
                                    (pre ++
                                      [Assembly.Instr.label block.label] ++
                                      bodyCode).pcAfter := by
                                simpa [List.append_assoc] using hValue.1
                              have hTermRel :
                                  RuntimeRel program.labelPc
                                    (ReturnAddressLower.Program.returnSites cfg)
                                    block.output targetAfter sourceAfter := by
                                simpa [program, List.append_assoc] using
                                  hValue.2.2
                              have hTermRun :=
                                terminator_lowerAt_openRunUntilTransfer_runtimeRel
                                  (cfg := cfg) (block := block)
                                  (shape := block.output)
                                  (code := termCode)
                                  (pre :=
                                    pre ++
                                      [Assembly.Instr.label block.label] ++
                                      bodyCode)
                                  (post := post)
                                  (target := targetAfter)
                                  (source := sourceAfter)
                                  hBlock hTokensUnique hTargetsUnique
                                  hTyped.2 hTerm
                                  (by
                                    simpa [program, List.append_assoc] using
                                      hAssemblyFits)
                                  hTermFits hTermPc
                                  (by
                                    simpa [program, List.append_assoc] using
                                      hResolved)
                                  (by
                                    simpa [program, List.append_assoc] using
                                      hLabels)
                                  (by
                                    simpa [program, List.append_assoc] using
                                      hTermRel)
                              have hTermBlock :=
                                Simulation.Interaction.Rel.mono
                                  (by
                                    simpa [program, List.append_assoc] using
                                      hTermRun)
                                  (fun _targetFinal _sourceFinal hFinal =>
                                    LoweredTerminatorResultRel.toBlock
                                      (program :=
                                        pre ++
                                          [Assembly.Instr.label block.label] ++
                                          bodyCode ++ termCode ++ post)
                                      hFinal)
                              cases hChecked :
                                  TypedCfg.Block.runTermChecked
                                    block.output block.term sourceAfter with
                              | error error =>
                                  simpa [program, hChecked, List.append_assoc]
                                    using hTermBlock
                              | ok outcome =>
                                  simpa [program, hChecked, List.append_assoc]
                                    using hTermBlock
            have hCompiledRun :
                CompiledBlock.openRun cfg block program target =
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | .running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | .halted halt =>
                        pure (.halted halt)) := by
              simp only [CompiledBlock.openRun, hBody, hTerm, if_true,
                hLabelRun]
              change
                Simulation.Interaction.bind
                    ((.done
                      (.ok (Assembly.StepResult.running entry))) :
                        Assembly.InteractionSemantics.OpenStepResult)
                    (fun labelResult =>
                      match labelResult with
                      | .halted halt =>
                          pure (.halted halt)
                      | .running entry =>
                          do
                            let bodyResult ←
                              Assembly.InteractionSemantics.Source.openRunNResult
                                program bodyCode.length entry
                            match bodyResult with
                            | .halted halt =>
                                pure (.halted halt)
                            | .running mid =>
                                Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                                  (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                                    block.term)
                                  program termCode.length mid) =
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | .running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | .halted halt =>
                        pure (.halted halt))
              rw [Simulation.Interaction.bind_done_ok]
              simp
              congr 1
              funext bodyResult
              cases bodyResult <;> rfl
            change
              Simulation.Interaction.Rel
                (LoweredBlockResultRel program program.labelPc
                  (ReturnAddressLower.Program.returnSites cfg)
                  (terminatorOutputShape block.output block.term))
                (CompiledBlock.openRun cfg block program target)
                (TypedCfg.InteractionSemantics.Block.openRun
                  block source)
            rw [hCompiledRun]
            exact hRest
      · simp [hBody, hOutput] at hLower

theorem LoweredBlockResultRel.toProgram
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : TypedCfg.Block}
    {target : Assembly.Source.ExecutionOutcome}
    {source : Except Assembly.EVMException TypedCfg.Outcome}
    (hBlock : block ∈ cfg.blocks)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hJumpTarget : BlockJumpTarget block.term source)
    (hRel :
      LoweredBlockResultRel assembly assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (terminatorOutputShape block.output block.term)
        target source) :
    ProgramRunResultRel cfg assembly assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg)
      target source := by
  cases source with
  | error sourceError =>
      cases target with
      | error targetError =>
          trivial
      | ok targetResult =>
          exact False.elim hRel
  | ok sourceOutcome =>
      cases sourceOutcome with
      | jump next sourceAfter =>
          change next ∈ block.term.targets at hJumpTarget
          obtain ⟨nextBlock, hFind, hClasses, hTail⟩ :=
            hEdgeSafe block hBlock next hJumpTarget
          have hTermRel :
              LoweredTerminatorResultRel assembly assembly.labelPc
              (ReturnAddressLower.Program.returnSites cfg)
              (terminatorOutputShape block.output block.term)
              target (.ok (.jump next sourceAfter)) := by
            cases target <;> exact hRel
          rcases hTermRel with ⟨middle, hTarget, hSource⟩
          cases middle with
          | error middleError =>
              cases hSource
          | ok middleOutcome =>
              cases hSource with
              | ok hOutcome =>
                  cases middleOutcome with
                  | fallthrough middleState =>
                      cases hOutcome
                  | returnDispatch middleState =>
                      cases hOutcome
                  | halt kind middleState =>
                      cases hOutcome
                  | invalid middleState =>
                      cases hOutcome
                  | jump middleNext middleState =>
                      rcases hOutcome with
                        ⟨hNext, hRuntime⟩
                      subst middleNext
                      change
                        TypedCfg.Preservation.Outcome.Simulates
                          assembly (.jump next middleState) target
                        at hTarget
                      rcases hTarget with
                        ⟨dest, hLabelPc, hRunning⟩
                      cases target with
                      | error targetError =>
                          exact False.elim hRunning
                      | ok targetResult =>
                          cases targetResult with
                          | halted halt =>
                              exact False.elim hRunning
                          | running targetAfter =>
                              rcases hRunning with
                                ⟨hTargetPc, hSame⟩
                              have hActual :
                                  RuntimeRel assembly.labelPc
                                    (ReturnAddressLower.Program.returnSites cfg)
                                    (terminatorOutputShape
                                      block.output block.term)
                                    targetAfter sourceAfter :=
                                runtimeRel_left_of_sameRuntimeData
                                  hSame hRuntime
                              have hRetyped :
                                  RuntimeRel assembly.labelPc
                                    (ReturnAddressLower.Program.returnSites cfg)
                                    nextBlock.input
                                    targetAfter sourceAfter := by
                                apply runtimeRel_retype_classes
                                    (input :=
                                      terminatorOutputShape
                                        block.output block.term)
                                · simpa [terminatorOutputShape,
                                    ReturnAddressLower.Terminator.outputShape]
                                    using hClasses
                                · simpa [terminatorOutputShape,
                                    ReturnAddressLower.Terminator.outputShape]
                                    using hTail
                                · exact hActual
                              exact
                                ⟨nextBlock, dest, hFind, hLabelPc,
                                  hTargetPc,
                                  runtimeRel_incrPC_left hRetyped⟩
      | fallthrough final
      | returnDispatch final =>
          exact False.elim hJumpTarget
      | halt kind final =>
          have hTerm : block.term = .halt kind := hJumpTarget
          have hSafe :=
            hTerminalPlain block hBlock kind hTerm
          cases target with
          | error targetError =>
              refine
                ⟨terminatorOutputShape block.output block.term,
                  ?_, ?_, hRel⟩
              · simpa [terminatorOutputShape, hTerm] using hSafe.1
              · simpa [terminatorOutputShape, hTerm] using hSafe.2
          | ok targetResult =>
              refine
                ⟨terminatorOutputShape block.output block.term,
                  ?_, ?_, hRel⟩
              · simpa [terminatorOutputShape, hTerm] using hSafe.1
              · simpa [terminatorOutputShape, hTerm] using hSafe.2
      | invalid final =>
          cases target <;> exact ⟨_, hRel⟩

theorem returnSites_targets_resolved
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    (hLower :
      ReturnAddressLower.Program.lower? cfg = some assembly)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg) :
    ∀ site ∈ ReturnAddressLower.Program.returnSites cfg,
      ∃ pc, assembly.labelPc site.target = some pc := by
  intro site hSite
  unfold ReturnAddressLower.Program.returnSites at hSite
  rcases List.mem_flatMap.mp hSite with
    ⟨owner, hOwner, hSite⟩
  have hTarget : site.target ∈ owner.term.targets := by
    cases hTerm : owner.term with
    | returnDispatch returnCount sites =>
        exact
          List.mem_map.mpr
            ⟨site,
              by
                simpa [ReturnAddressLower.Terminator.sites, hTerm]
                  using hSite,
              rfl⟩
    | fallthrough next
    | jump target
    | jumpi target next
    | halt kind
    | invalid =>
        simp [ReturnAddressLower.Terminator.sites, hTerm] at hSite
  obtain ⟨targetBlock, hFind, _hClasses, _hTail⟩ :=
    hEdgeSafe owner hOwner site.target hTarget
  have hTargetBlock : targetBlock ∈ cfg.blocks :=
    List.mem_of_find?_eq_some hFind
  have hTargetLabel : targetBlock.label = site.target := by
    exact
      beq_iff_eq.mp
        (@List.find?_some TypedCfg.Block
          (fun candidate : TypedCfg.Block =>
            candidate.label == site.target)
          targetBlock cfg.blocks hFind)
  simpa [hTargetLabel] using
    (ReturnAddressLower.Program.blockLabel_labelPc_exists_of_lower?
      hLower hTyped.1 hTargetBlock)

theorem term_targets_resolved
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : TypedCfg.Block}
    (hLower :
      ReturnAddressLower.Program.lower? cfg = some assembly)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hBlock : block ∈ cfg.blocks) :
    TypedCfg.Preservation.Terminator.ResolvedTargets
      assembly block.term := by
  intro target hTarget
  obtain ⟨targetBlock, hFind, _hClasses, _hTail⟩ :=
    hEdgeSafe block hBlock target hTarget
  have hTargetBlock : targetBlock ∈ cfg.blocks :=
    List.mem_of_find?_eq_some hFind
  have hTargetLabel : targetBlock.label = target := by
    exact
      beq_iff_eq.mp
        (@List.find?_some TypedCfg.Block
          (fun candidate : TypedCfg.Block =>
            candidate.label == target)
          targetBlock cfg.blocks hFind)
  simpa [hTargetLabel] using
    (ReturnAddressLower.Program.blockLabel_labelPc_exists_of_lower?
      hLower hTyped.1 hTargetBlock)

theorem compiled_openStep_eq_of_labelPc
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : Assembly.EVMState} {entryPc : Nat}
    (hFits : assembly.PCFits)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    CompiledProgram.openStep cfg assembly state =
      CompiledBlock.openRun cfg block assembly state := by
  have hToNat :=
    Assembly.Program.toNat_ofNat_labelPc hFits hLabelPc
  have hAt :=
    Assembly.Program.instrAtPc_of_labelPc hLabelPc
  unfold CompiledProgram.openStep
  rw [hPc, hToNat, hAt]
  simp [hFind]

set_option maxHeartbeats 1000000 in
theorem program_lower?_step_openRun_runtimeRel
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc : Nat}
    (hLower :
      ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState) :
    Simulation.Interaction.Rel
      (ProgramRunResultRel cfg assembly assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg))
      (CompiledProgram.openStep cfg assembly targetState)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg label sourceState) := by
  rcases
      ReturnAddressLower.Program.lower?_fragment_of_findBlock?
        hLower hFind with
    ⟨fragment⟩
  have hBlock : block ∈ cfg.blocks :=
    List.mem_of_find?_eq_some hFind
  have hBlockLabel : block.label = label := by
    have hFound :
        (block.label == label) = true :=
      @List.find?_some TypedCfg.Block
        (fun candidate : TypedCfg.Block =>
          candidate.label == label)
        block cfg.blocks hFind
    exact beq_iff_eq.mp hFound
  subst label
  have hBlockTyped : block.WellTyped cfg :=
    (List.forall_iff_forall_mem.mp hTyped.2.1)
      block hBlock
  have hLabels : assembly.labels.Nodup :=
    Assembly.Program.labels_nodup_of_accepted hAccepted
  have hCodeFits :
      Assembly.Program.PCFitsFrom fragment.pre fragment.code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← fragment.target_eq]
    exact hFits
  have hTargets :=
    returnSites_targets_resolved hLower hTyped hEdgeSafe
  have hResolved :=
    term_targets_resolved hLower hTyped hEdgeSafe hBlock
  rcases
      ReturnAddressLower.Block.lower?_starts_with_label
        fragment.lower with
    ⟨tail, hCode⟩
  have hEntryLabel :
      assembly.labelPc block.label =
        some fragment.pre.byteLength := by
    have hNodup :
        (fragment.pre ++
          Assembly.Instr.label block.label ::
            (tail ++ fragment.post)).labels.Nodup := by
      simpa [fragment.target_eq, hCode, List.append_assoc] using
        hLabels
    have hAt :=
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        fragment.pre (tail ++ fragment.post) hNodup
    simpa [fragment.target_eq, hCode, List.append_assoc] using hAt
  have hEntryPcEq :
      entryPc = fragment.pre.byteLength := by
    rw [hEntryLabel] at hLabelPc
    exact (Option.some.inj hLabelPc).symm
  have hStatePc :
      targetState.pc = fragment.pre.pcAfter := by
    calc
      targetState.pc =
          EvmYul.UInt256.ofNat entryPc := hPc
      _ =
          EvmYul.UInt256.ofNat fragment.pre.byteLength := by
        rw [hEntryPcEq]
      _ = fragment.pre.pcAfter := rfl
  have hBlockRun :=
    block_lower?_openRun_runtimeRel
      (cfg := cfg) (block := block)
      (code := fragment.code)
      (pre := fragment.pre) (post := fragment.post)
      (target := targetState) (source := sourceState)
      hBlock hBlockTyped hTokensUnique hTargetsUnique
      fragment.lower
      (by
        rw [← fragment.target_eq]
        exact hFits)
      hCodeFits hStatePc
      (by
        rw [← fragment.target_eq]
        exact hTargets)
      (by
        rw [← fragment.target_eq]
        exact hResolved)
      (by
        rw [← fragment.target_eq]
        exact hLabels)
      (by
        rw [← fragment.target_eq]
        exact hRel)
  have hBlockRunAssembly :
      Simulation.Interaction.Rel
        (LoweredBlockResultRel assembly assembly.labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          (terminatorOutputShape block.output block.term))
        (CompiledBlock.openRun cfg block assembly targetState)
        (TypedCfg.InteractionSemantics.Block.openRun
          block sourceState) := by
    simpa only [← fragment.target_eq] using hBlockRun
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_right hBlockRunAssembly
      (block_openRun_jumpTarget block sourceState)
  rw [
    compiled_openStep_eq_of_labelPc
      hFits hFind hLabelPc hPc]
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind]
  apply Simulation.Interaction.Rel.mono hStrong
  intro targetDone sourceDone hDone
  exact
    LoweredBlockResultRel.toProgram
      hBlock hEdgeSafe hTerminalPlain hDone.2 hDone.1

theorem LoweredBlockResultRel.targetFinished_halt
    {assembly : Assembly.Program}
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {output : Shape}
    {target : Assembly.Source.ExecutionOutcome}
    {kind : Assembly.HaltKind} {source : Assembly.EVMState}
    (hRel :
      LoweredBlockResultRel assembly resolve sites output
        target (.ok (.halt kind source))) :
    Assembly.InteractionSemantics.Finished target := by
  have hTermRel :
      LoweredTerminatorResultRel assembly resolve sites output
        target (.ok (.halt kind source)) := by
    cases target <;> exact hRel
  rcases hTermRel with ⟨middle, hTarget, hSource⟩
  cases middle with
  | error middleError =>
      cases hSource
  | ok middleOutcome =>
      cases hSource with
      | ok hOutcome =>
          cases middleOutcome with
          | fallthrough middleState =>
              cases hOutcome
          | jump next middleState =>
              cases hOutcome
          | returnDispatch middleState =>
              cases hOutcome
          | invalid middleState =>
              cases hOutcome
          | halt middleKind middleState =>
              rcases hOutcome with
                ⟨hKind, _hRuntime⟩
              subst middleKind
              change
                TypedCfg.Preservation.Outcome.Simulates
                  assembly (.halt kind middleState) target
                at hTarget
              subst target
              unfold Assembly.Target.stepInstrResult
              cases hStep :
                  Assembly.Target.stepInstr
                    (.prim kind.toPrimOp) middleState with
              | error error =>
                  trivial
              | ok final =>
                  have hHalt :
                      (Assembly.TargetInstr.prim
                        kind.toPrimOp).haltKind? =
                        some kind := by
                    cases kind <;> rfl
                  rw [hHalt]
                  trivial

theorem LoweredBlockResultRel.targetFinished_invalid
    {assembly : Assembly.Program}
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {output : Shape}
    {target : Assembly.Source.ExecutionOutcome}
    {source : Assembly.EVMState}
    (hRel :
      LoweredBlockResultRel assembly resolve sites output
        target (.ok (.invalid source))) :
    Assembly.InteractionSemantics.Finished target := by
  have hTermRel :
      LoweredTerminatorResultRel assembly resolve sites output
        target (.ok (.invalid source)) := by
    cases target <;> exact hRel
  rcases hTermRel with ⟨middle, hTarget, hSource⟩
  cases middle with
  | error middleError =>
      cases hSource
  | ok middleOutcome =>
      cases hSource with
      | ok hOutcome =>
          cases middleOutcome with
          | fallthrough middleState =>
              cases hOutcome
          | jump next middleState =>
              cases hOutcome
          | returnDispatch middleState =>
              cases hOutcome
          | halt kind middleState =>
              cases hOutcome
          | invalid middleState =>
              change
                TypedCfg.Preservation.Outcome.Simulates
                  assembly (.invalid middleState) target
                at hTarget
              rcases hTarget with ⟨error, rfl⟩
              trivial

theorem LoweredBlockResultRel.targetError_invalid
    {assembly : Assembly.Program}
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {output : Shape}
    {target : Assembly.Source.ExecutionOutcome}
    {source : Assembly.EVMState}
    (hRel :
      LoweredBlockResultRel assembly resolve sites output
        target (.ok (.invalid source))) :
    ∃ error, target = .error error := by
  have hTermRel :
      LoweredTerminatorResultRel assembly resolve sites output
        target (.ok (.invalid source)) := by
    cases target <;> exact hRel
  rcases hTermRel with ⟨middle, hTarget, hSource⟩
  cases middle with
  | error middleError =>
      cases hSource
  | ok middleOutcome =>
      cases hSource with
      | ok hOutcome =>
          cases middleOutcome with
          | fallthrough middleState =>
              cases hOutcome
          | jump next middleState =>
              cases hOutcome
          | returnDispatch middleState =>
              cases hOutcome
          | halt kind middleState =>
              cases hOutcome
          | invalid middleState =>
              change
                TypedCfg.Preservation.Outcome.Simulates
                  assembly (.invalid middleState) target
                at hTarget
              exact hTarget

set_option maxHeartbeats 1000000 in
theorem program_lower?_openRunN_runtimeRel
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc : Nat} (fuel : Nat)
    (hLower :
      ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState) :
    Simulation.Interaction.Rel
      (ProgramRunResultRel cfg assembly assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg))
      (CompiledProgram.openRunN cfg assembly fuel targetState)
      (TypedCfg.InteractionSemantics.Program.openRunN
        cfg fuel label sourceState) := by
  induction fuel generalizing
      label block targetState sourceState entryPc with
  | zero =>
      simp only [CompiledProgram.openRunN_zero,
        TypedCfg.InteractionSemantics.Program.openRunN_zero]
      apply Simulation.Interaction.Rel.done
      exact
        ⟨block, entryPc, hFind, hLabelPc, hPc, hRel⟩
  | succ fuel ih =>
      rw [CompiledProgram.openRunN_succ,
        TypedCfg.InteractionSemantics.Program.openRunN_succ]
      have hStep :=
        program_lower?_step_openRun_runtimeRel
          hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
          hTokensUnique hTargetsUnique
          hFind hLabelPc hPc hRel
      apply Simulation.Interaction.Rel.bind_custom hStep
      intro targetDone sourceDone hDone
      cases sourceDone with
      | error sourceError =>
          cases targetDone with
          | error targetError =>
              exact Simulation.Interaction.Rel.done hDone
          | ok targetResult =>
              exact False.elim hDone
      | ok sourceOutcome =>
          cases sourceOutcome with
          | fallthrough final =>
              cases targetDone <;> exact False.elim hDone
          | returnDispatch final =>
              cases targetDone <;> exact False.elim hDone
          | jump next sourceAfter =>
              cases targetDone with
              | error targetError =>
                  exact False.elim hDone
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      exact False.elim hDone
                  | running targetAfter =>
                      rcases hDone with
                        ⟨nextBlock, dest, hNextFind,
                          hNextLabelPc, hTargetPc, hNextRel⟩
                      exact
                        ih hNextFind hNextLabelPc hTargetPc hNextRel
          | halt kind final =>
              cases targetDone with
              | error targetError =>
                  exact Simulation.Interaction.Rel.done hDone
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      exact Simulation.Interaction.Rel.done hDone
                  | running targetAfter =>
                      rcases hDone with
                        ⟨output, _hBound, _hPlain, hBlockRel⟩
                      exact False.elim
                        (LoweredBlockResultRel.targetFinished_halt
                          hBlockRel)
          | invalid final =>
              cases targetDone with
              | error targetError =>
                  exact Simulation.Interaction.Rel.done hDone
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      rcases hDone with
                        ⟨output, hBlockRel⟩
                      rcases
                          LoweredBlockResultRel.targetError_invalid
                            hBlockRel with
                        ⟨error, hImpossible⟩
                      cases hImpossible
                  | running targetAfter =>
                      rcases hDone with
                        ⟨output, hBlockRel⟩
                      rcases
                          LoweredBlockResultRel.targetError_invalid
                            hBlockRel with
                        ⟨error, hImpossible⟩
                      cases hImpossible

theorem returnDispatch_openRunUntilTransfer_runtimeRel
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : Block} {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word} {targetLabel : Label}
    {slot : Slot} {targetWord : Word}
    {target source : Assembly.EVMState}
    {pre post : Assembly.Program}
    (hBlock : block ∈ cfg.blocks)
    (hTerm : block.term = .returnDispatch returnCount sites)
    (hUnique : ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hSlot : shape.slots[depth]? = some slot)
    (hReturn : ReturnSlot slot)
    (hCount : depth = returnCount)
    (hBound : depth < 16)
    (hTargetGet : target.stack[depth]? = some targetWord)
    (hSourceGet : source.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = some targetLabel)
    (hAssembly : assembly =
      pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
    (hFits : Assembly.Program.PCFitsFrom pre
      (ReturnAddressLower.Terminator.dynamicReturnTransferCode depth))
    (hPc : target.pc = pre.pcAfter)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    Simulation.Interaction.Rel
      (LoweredTerminatorResultRel assembly assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (shape.erase depth))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        assembly
        (ReturnAddressLower.Terminator.dynamicReturnTransferCode depth).length
        target)
      (.done
        (TypedCfg.Block.runTermChecked shape
          (.returnDispatch returnCount sites) source)) := by
  subst returnCount
  subst assembly
  obtain ⟨selected, hSelectedLocal, hSelectedToken, hSelectedTarget⟩ :=
    Block.ReturnSite.mem_token_of_findTarget?_eq_some hFind
  have hSelectedGlobal :
      selected ∈ ReturnAddressLower.Program.returnSites cfg := by
    apply ReturnAddressLower.term_site_mem_returnSites hBlock
    simp [ReturnAddressLower.Terminator.sites, hTerm, hSelectedLocal]
  have hUnique' := ReturnAddressLower.tokensUnique_of_check hUnique
  obtain ⟨targetPc, hResolve, hTargetWord, hErasedRel⟩ :=
    returnSlot_target_of_unique hUnique' hSelectedGlobal hSelectedToken
      hRel.2 hSlot hReturn hTargetGet hSourceGet
  have hTargetStack :
      target.stack =
        target.stack.take depth ++
          targetWord :: target.stack.drop (depth + 1) :=
    list_eq_take_get_drop hTargetGet
  have hDepthLt : depth < target.stack.length :=
    (List.getElem?_eq_some_iff.mp hTargetGet).choose
  have hFrontLength :
      (target.stack.take depth).length = depth := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hDepthLt)]
  have hLiftFits :
      Assembly.Program.PCFitsFrom pre
        (Assembly.StackShuffle.liftBuriedToTop depth) := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
      List.append_assoc] using hFits
  have hJumpFits :
      Assembly.Program.PCFitsFrom
        (pre ++ Assembly.StackShuffle.liftBuriedToTop depth)
        [.jumpDynamic] := by
    have hRight := Assembly.Program.PCFitsFrom.right hFits
    simpa [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
      List.append_assoc] using hRight
  let mid : Assembly.EVMState :=
    { target with
      stack :=
        targetWord :: target.stack.take depth ++
          target.stack.drop (depth + 1)
      pc :=
        (pre ++ Assembly.StackShuffle.liftBuriedToTop depth).pcAfter }
  let final : Assembly.EVMState :=
    { mid with
      stack :=
        target.stack.take depth ++
          target.stack.drop (depth + 1)
      pc := targetWord }
  have hInitialRecord :
      { target with
        stack :=
          target.stack.take depth ++
            targetWord :: target.stack.drop (depth + 1) } =
        target := by
    cases target
    simpa using hTargetStack.symm
  have hLift :=
    Assembly.StackShuffle.InteractionPreservation.liftBuriedToTop_openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (front := target.stack.take depth)
        (suffix := target.stack.drop (depth + 1))
        (token := targetWord) (pre := pre)
        (post := [.jumpDynamic] ++ post)
        (state := target) (fuel := 1)
        (by simpa [hFrontLength] using hLiftFits)
        (by simpa [hInitialRecord] using hPc)
        (by omega)
  have hLift' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
          (ReturnAddressLower.Terminator.dynamicReturnTransferCode depth).length
          target =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
          1 mid := by
    have hLiftNormalized := hLift
    rw [hFrontLength] at hLiftNormalized
    rw [hInitialRecord] at hLiftNormalized
    rw [show
      1 + (Assembly.StackShuffle.liftBuriedToTop depth).length =
        (Assembly.StackShuffle.liftBuriedToTop depth).length + 1 by
      omega] at hLiftNormalized
    simpa [ReturnAddressLower.Terminator.dynamicReturnTransferCode, mid,
      List.append_assoc] using hLiftNormalized
  have hMidPc :
      mid.pc =
        (pre ++ Assembly.StackShuffle.liftBuriedToTop depth).pcAfter := by
    rfl
  have hJump :=
    Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_one_at_boundary
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre := pre ++ Assembly.StackShuffle.liftBuriedToTop depth)
        (post := post) (instr := .jumpDynamic) (state := mid)
        (Assembly.Program.PCFitsFrom.start hJumpFits) hMidPc
  have hJump' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
          1 mid =
        .done (.ok (.running final)) := by
    rw [show
      pre ++ ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post =
        (pre ++ Assembly.StackShuffle.liftBuriedToTop depth) ++
          Assembly.Instr.jumpDynamic :: post by
      simp [ReturnAddressLower.Terminator.dynamicReturnTransferCode,
        List.append_assoc]]
    rw [hJump]
    simp [Assembly.InteractionSemantics.Source.openStepAtResult,
      Assembly.InteractionSemantics.Source.openStepAt,
      Assembly.Source.stepAt, Assembly.Target.stepInstr,
      Assembly.Target.stepInstrWith, Assembly.Instr.haltKind?,
      Assembly.Instr.classifyFlowWith, Assembly.FlowStep.result,
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy,
      mid, final, EvmYul.Stack.pop, Simulation.Interaction.bind,
      Simulation.Interaction.pure]
    rfl
  have hRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
          (ReturnAddressLower.Terminator.dynamicReturnTransferCode depth).length
          target =
        .done (.ok (.running final)) :=
    hLift'.trans hJump'
  have hErase :
      target.stack.eraseIdx depth =
        target.stack.take depth ++ target.stack.drop (depth + 1) :=
    eraseIdx_eq_take_drop_of_get? hTargetGet
  have hFinalRel :
      RuntimeRel
        (pre ++
          ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post).labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (shape.erase depth) final
        { source with stack := source.stack.eraseIdx depth } := by
    constructor
    · calc
        final.toSharedState = target.toSharedState := by
          simp [final, mid]
        _ = source.toSharedState := hRel.1
    · simpa [final, mid, ShapeStackRel, Shape.erase, hErase] using
        hErasedRel
  have hSourceRun :
      TypedCfg.Block.runTermChecked shape
          (.returnDispatch depth sites) source =
        .ok
          (.jump targetLabel
            { source with stack := source.stack.eraseIdx depth }) := by
    simp [TypedCfg.Block.runTerm, hDepth, hSourceGet, hFind]
  rw [hRun, hSourceRun]
  apply Simulation.Interaction.Rel.done
  refine ⟨.ok (.jump targetLabel final), ?_, ?_⟩
  · change TypedCfg.Preservation.Outcome.Simulates
      (pre ++
        ReturnAddressLower.Terminator.dynamicReturnTransferCode depth ++ post)
      (.jump targetLabel final) (.ok (.running final))
    refine ⟨targetPc, ?_, ?_, ?_⟩
    · simpa [hSelectedTarget] using hResolve
    · exact
        calc
          final.pc = targetWord := by rfl
          _ = EvmYul.UInt256.ofNat targetPc := hTargetWord
    · exact Assembly.SameRuntimeData.refl final
  · exact Simulation.Interaction.ExceptRel.ok
      (by simpa [OutcomeRuntimeRel] using hFinalRel)

end ReturnAddressPreservation
end TypedCfg
end EvmCompiler
