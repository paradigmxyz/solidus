import EvmCompiler.Functions.AllocationLowering
import EvmCompiler.Functions.AllocationObserverRelation

namespace EvmCompiler
namespace Functions
namespace AllocationObserverContext

open Locals.Allocation

/--
Compiler-owned interface connecting one Functions lowering state to the
allocation plan and Locals stack layout used to compile its expressions.

Allocation slots are stable source identifiers. Stack locations convert those
slots to zero-based plan depths and one-based Locals `DUP` depths; scratch
locations keep the allocation slot and resolve the hidden frame pointer in the
same Locals layout. The whole-program allocation theorem must construct this
relation from the checked planner/lowerer artifacts.
-/
structure ExprContext
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name)
    (frameDepth : Nat) : Prop where
  layout :
    localsCtx.layout = lowerState.layout
  stackPrefix :
    AllocationObserverRelation.currentStackOrder plan live =
      lowerState.layout.take frameDepth
  frame :
    Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
      some (frameDepth + 1)
  frameBottom :
    lowerState.layout.length = frameDepth + 1
  location :
    ∀ name,
      name ∈ live →
      ∃ location, plan.location? name = some location
  slot :
    ∀ name,
      name ∈ live →
      ∃ slot,
        AllocationSupport.lookupSlot?
            name lowerState.allocation.env =
          some slot
  stack :
    ∀ name slot,
      name ∈ live →
      AllocationSupport.lookupSlot?
          name lowerState.allocation.env =
        some slot →
      AllocationLowering.isStackSlot lowerCtx slot = true →
      ∃ planDepth depth,
        plan.location? name = some (.stack planDepth) ∧
          Locals.Layout.lookupDepth?
              name
              (AllocationObserverRelation.currentStackOrder plan live) =
            some (depth + 1) ∧
          Locals.Layout.lookupDepth? name lowerState.layout =
            some (depth + 1)
  scratch :
    ∀ name slot,
      name ∈ live →
      AllocationSupport.lookupSlot?
          name lowerState.allocation.env =
        some slot →
      AllocationLowering.isStackSlot lowerCtx slot = false →
      plan.location? name = some (.scratch slot) ∧
        Locals.Layout.lookupDepth?
            lowerCtx.frameName lowerState.layout =
          some (frameDepth + 1)

namespace ExprContext

theorem currentStackOrder_length
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameDepth : Nat}
    (hCtx :
      ExprContext lowerCtx lowerState localsCtx plan live frameDepth) :
    (AllocationObserverRelation.currentStackOrder plan live).length =
      frameDepth := by
  have hFrameAt :
      lowerState.layout[frameDepth]? = some lowerCtx.frameName :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hCtx.frame
  have hFrameBound : frameDepth < lowerState.layout.length :=
    List.getElem?_eq_some_iff.mp hFrameAt |>.1
  rw [hCtx.stackPrefix]
  simp [List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hFrameBound)]

theorem stack_depth_lt_frame
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameDepth depth : Nat} {name : Locals.Name}
    (hCtx :
      ExprContext lowerCtx lowerState localsCtx plan live frameDepth)
    (hDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1)) :
    depth < frameDepth := by
  have hAt :
      (AllocationObserverRelation.currentStackOrder plan live)[depth]? =
        some name :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hBound :
      depth <
        (AllocationObserverRelation.currentStackOrder plan live).length :=
    List.getElem?_eq_some_iff.mp hAt |>.1
  simpa [hCtx.currentStackOrder_length] using hBound

end ExprContext

/--
Compiler context for an activation whose live locals are entirely stack
resident.

Unlike `ExprContext`, this relation does not invent a hidden frame pointer for
an all-stack artifact. The exact dynamic stack order is the Locals layout, and
the lowerer's reserved frame name is absent.
-/
structure StackExprContext
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name) : Prop where
  layout :
    localsCtx.layout = lowerState.layout
  stackOrder :
    AllocationObserverRelation.currentStackOrder plan live =
      lowerState.layout
  frameAbsent :
    lowerCtx.frameName ∉ lowerState.layout
  liveStackOnly :
    AllocationObserverRelation.LiveStackOnly plan live
  location :
    ∀ name,
      name ∈ live →
      ∃ location, plan.location? name = some location
  slot :
    ∀ name,
      name ∈ live →
      ∃ slot,
        AllocationSupport.lookupSlot?
            name lowerState.allocation.env =
          some slot
  stack :
    ∀ name slot,
      name ∈ live →
      AllocationSupport.lookupSlot?
          name lowerState.allocation.env =
        some slot →
      AllocationLowering.isStackSlot lowerCtx slot = true →
      ∃ planDepth depth,
        plan.location? name = some (.stack planDepth) ∧
          Locals.Layout.lookupDepth?
              name
              (AllocationObserverRelation.currentStackOrder plan live) =
            some (depth + 1) ∧
          Locals.Layout.lookupDepth? name lowerState.layout =
            some (depth + 1)

/--
One compiler-context boundary for stack-only and scratch-frame activations.

The mode index prevents a stack-only artifact from acquiring synthetic frame
premises while allowing the recursive expression proof to use one context
type.
-/
inductive ActivationExprContext
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name) :
    AllocationObserverRelation.ActivationMode → Prop where
  | stack
      (ctx :
        StackExprContext lowerCtx lowerState localsCtx plan live) :
      ActivationExprContext lowerCtx lowerState localsCtx plan live .stack
  | scratch
      {frameDepth frameWords : Nat}
      (ctx :
        ExprContext lowerCtx lowerState localsCtx plan live frameDepth) :
      ActivationExprContext lowerCtx lowerState localsCtx plan live
        (.scratch frameDepth frameWords)

namespace ActivationExprContext

/--
Transport an activation compiler context across Locals contexts with the same
layout.

Loop-control metadata changes do not affect expression compilation or the
runtime activation relation.
-/
theorem transport_locals_layout
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {before after : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {mode : AllocationObserverRelation.ActivationMode}
    (hCtx :
      ActivationExprContext
        lowerCtx lowerState before plan live mode)
    (hLayout : after.layout = before.layout) :
    ActivationExprContext
      lowerCtx lowerState after plan live mode := by
  cases hCtx with
  | stack hStack =>
      exact .stack
        { layout := hLayout.trans hStack.layout
          stackOrder := hStack.stackOrder
          frameAbsent := hStack.frameAbsent
          liveStackOnly := hStack.liveStackOnly
          location := hStack.location
          slot := hStack.slot
          stack := hStack.stack }
  | @scratch frameDepth frameWords hScratch =>
      exact .scratch
        { layout := hLayout.trans hScratch.layout
          stackPrefix := hScratch.stackPrefix
          frame := hScratch.frame
          frameBottom := hScratch.frameBottom
          location := hScratch.location
          slot := hScratch.slot
          stack := hScratch.stack
          scratch := hScratch.scratch }

/--
Transport an activation compiler context across lowering-state changes that
leave the concrete layout and live allocation environment unchanged.

Scoped branches use this when only the allocator's fresh-slot cursor advances.
-/
theorem transport_state
    {lowerCtx : AllocationLowering.Ctx}
    {before after : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {mode : AllocationObserverRelation.ActivationMode}
    (hCtx :
      ActivationExprContext
        lowerCtx before localsCtx plan live mode)
    (hEnv : after.allocation.env = before.allocation.env)
    (hLayout : after.layout = before.layout) :
    ActivationExprContext
      lowerCtx after localsCtx plan live mode := by
  cases hCtx with
  | stack hStack =>
      refine .stack
        { layout := hStack.layout.trans hLayout.symm
          stackOrder := hStack.stackOrder.trans hLayout.symm
          frameAbsent := by
            simpa [hLayout] using hStack.frameAbsent
          liveStackOnly := hStack.liveStackOnly
          location := hStack.location
          slot := ?_
          stack := ?_ }
      · intro name hLive
        obtain ⟨slot, hSlot⟩ := hStack.slot name hLive
        exact ⟨slot, by simpa [hEnv] using hSlot⟩
      · intro name slot hLive hSlot hIsStack
        have hBeforeSlot :
            AllocationSupport.lookupSlot?
                name before.allocation.env =
              some slot := by
          simpa [hEnv] using hSlot
        obtain
            ⟨planDepth, depth, hLocation, hCurrent, hDepth⟩ :=
          hStack.stack name slot hLive hBeforeSlot hIsStack
        exact
          ⟨planDepth, depth, hLocation, hCurrent,
            by simpa [hLayout] using hDepth⟩
  | @scratch frameDepth frameWords hScratch =>
      refine .scratch
        { layout := hScratch.layout.trans hLayout.symm
          stackPrefix := by simpa [hLayout] using hScratch.stackPrefix
          frame := by simpa [hLayout] using hScratch.frame
          frameBottom := by simpa [hLayout] using hScratch.frameBottom
          location := hScratch.location
          slot := ?_
          stack := ?_
          scratch := ?_ }
      · intro name hLive
        obtain ⟨slot, hSlot⟩ := hScratch.slot name hLive
        exact ⟨slot, by simpa [hEnv] using hSlot⟩
      · intro name slot hLive hSlot hIsStack
        have hBeforeSlot :
            AllocationSupport.lookupSlot?
                name before.allocation.env =
              some slot := by
          simpa [hEnv] using hSlot
        obtain
            ⟨planDepth, depth, hLocation, hCurrent, hDepth⟩ :=
          hScratch.stack name slot hLive hBeforeSlot hIsStack
        exact
          ⟨planDepth, depth, hLocation, hCurrent,
            by simpa [hLayout] using hDepth⟩
      · intro name slot hLive hSlot hIsScratch
        have hBeforeSlot :
            AllocationSupport.lookupSlot?
                name before.allocation.env =
              some slot := by
          simpa [hEnv] using hSlot
        obtain ⟨hLocation, hFrame⟩ :=
          hScratch.scratch name slot hLive hBeforeSlot hIsScratch
        exact ⟨hLocation, by simpa [hLayout] using hFrame⟩

/--
Two plans certified against the same concrete compiler state realize the same
live locals.

This is the stable plan-transport constructor used at lexical boundaries.
Plan-local stack depths may differ, but both contexts expose the same runtime
layout. Scratch contexts additionally classify both plans from the same
allocation slot.
-/
theorem planAgreesOn
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {leftPlan rightPlan : Plan}
    {live : List Locals.Name}
    {mode : AllocationObserverRelation.ActivationMode}
    (hLeft :
      ActivationExprContext
        lowerCtx lowerState localsCtx leftPlan live mode)
    (hRight :
      ActivationExprContext
        lowerCtx lowerState localsCtx rightPlan live mode) :
    AllocationObserverRelation.PlanAgreesOn leftPlan rightPlan live := by
  cases hLeft with
  | stack left =>
      cases hRight with
      | stack right =>
          refine ⟨left.stackOrder.trans right.stackOrder.symm, ?_⟩
          intro name hLive
          obtain ⟨leftLocation, hLeftLocation⟩ :=
            left.location name hLive
          obtain ⟨rightLocation, hRightLocation⟩ :=
            right.location name hLive
          cases leftLocation with
          | scratch slot =>
              exact False.elim
                (left.liveStackOnly name slot hLive hLeftLocation)
          | stack leftDepth =>
              cases rightLocation with
              | scratch slot =>
                  exact False.elim
                    (right.liveStackOnly name slot hLive hRightLocation)
              | stack rightDepth =>
                  exact
                    ⟨.stack leftDepth, .stack rightDepth,
                      hLeftLocation, hRightLocation,
                      .stack leftDepth rightDepth⟩
  | scratch left =>
      cases hRight with
      | scratch right =>
          refine ⟨left.stackPrefix.trans right.stackPrefix.symm, ?_⟩
          intro name hLive
          obtain ⟨slot, hSlot⟩ := left.slot name hLive
          by_cases hStack :
              AllocationLowering.isStackSlot lowerCtx slot = true
          · obtain
                ⟨leftDepth, _leftRuntimeDepth,
                  hLeftLocation, _hLeftCurrent, _hLeftLayout⟩ :=
              left.stack name slot hLive hSlot hStack
            obtain
                ⟨rightDepth, _rightRuntimeDepth,
                  hRightLocation, _hRightCurrent, _hRightLayout⟩ :=
              right.stack name slot hLive hSlot hStack
            exact
              ⟨.stack leftDepth, .stack rightDepth,
                hLeftLocation, hRightLocation,
                .stack leftDepth rightDepth⟩
          · have hScratch :
                AllocationLowering.isStackSlot lowerCtx slot = false :=
              Bool.eq_false_of_not_eq_true hStack
            obtain ⟨hLeftLocation, _hLeftFrame⟩ :=
              left.scratch name slot hLive hSlot hScratch
            obtain ⟨hRightLocation, _hRightFrame⟩ :=
              right.scratch name slot hLive hSlot hScratch
            exact
              ⟨.scratch slot, .scratch slot,
                hLeftLocation, hRightLocation,
                .scratch slot⟩

/--
The compiler layout described by an activation context is backed by concrete
target stack cells.

For stack-only activations, source-definedness rules out the otherwise
permitted `none = out-of-bounds` store relation at the bottom local. Scratch
activations instead use the concrete hidden frame pointer as their bottom stack
cell.
-/
theorem layout_length_le_target_stack
    {transcript : AllocationObserverRelation.Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hCtx :
      ActivationExprContext lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hDefined :
      AllocationObserverRelation.LiveDefined live source.source)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live 0 frameBase mode source target) :
    localsCtx.layout.length ≤ target.source.evm.stack.length := by
  cases hCtx with
  | stack hStackCtx =>
      cases hRel with
      | stack hOnly _hActive hState =>
          let order :=
            AllocationObserverRelation.currentStackOrder plan live
          by_cases hEmpty : order = []
          · calc
              localsCtx.layout.length = order.length := by
                rw [hStackCtx.layout, ← hStackCtx.stackOrder]
              _ = 0 := by simp [hEmpty]
              _ ≤ target.source.evm.stack.length := Nat.zero_le _
          · let name := order.getLast hEmpty
            have hNameOrder : name ∈ order := by
              exact List.getLast_mem hEmpty
            have hNameLive : name ∈ live :=
              AllocationObserverRelation.mem_live_of_mem_currentStackOrder
                hNameOrder
            obtain ⟨location, hLocation⟩ :=
              hStackCtx.location name hNameLive
            cases location with
            | scratch slot =>
                exact False.elim
                  (hOnly name slot hNameLive hLocation)
            | stack planDepth =>
                obtain ⟨depth, hDepth, hValue⟩ :=
                  hState.core.store name (.stack planDepth)
                    hNameLive hLocation
                obtain ⟨value, hSourceValue⟩ :=
                  hDefined name hNameLive
                have hLastDepth :
                    Locals.Layout.lookupDepth? name order =
                      some order.length := by
                  exact
                    Locals.Layout.lookupDepth?_getLast_of_nodup
                      (AllocationObserverRelation.currentStackOrder_nodup hWF)
                      hEmpty
                have hDepthEq : depth + 1 = order.length := by
                  rw [hLastDepth] at hDepth
                  exact (Option.some.inj hDepth).symm
                have hTargetValue :
                    target.source.evm.stack[depth]? = some value := by
                  simpa [hSourceValue] using hValue
                have hDepthBound :
                    depth < target.source.evm.stack.length :=
                  List.getElem?_eq_some_iff.mp hTargetValue |>.1
                calc
                  localsCtx.layout.length = order.length := by
                    rw [hStackCtx.layout, ← hStackCtx.stackOrder]
                  _ = depth + 1 := hDepthEq.symm
                  _ ≤ target.source.evm.stack.length :=
                    Nat.succ_le_of_lt hDepthBound
  | scratch hScratchCtx =>
      cases hRel with
      | scratch hScratch =>
          have hFrameBound :=
            List.getElem?_eq_some_iff.mp hScratch.framePointer |>.1
          rw [hScratchCtx.layout, hScratchCtx.frameBottom]
          exact Nat.succ_le_of_lt (by simpa using hFrameBound)

end ActivationExprContext

/--
Complete allocation invariant at a Functions statement boundary.

The exact stack-length field rules out a hidden caller suffix inside an active
Structured procedure. Calls store that suffix in the return-frame stack, so
the active data stack contains exactly the compiler layout at source statement
boundaries.
-/
structure ActivationInvariant
    {transcript : AllocationObserverRelation.Trace}
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name)
    (frameBase : Nat)
    (mode : AllocationObserverRelation.ActivationMode)
    (source : Functions.ObserverSemantics.State transcript)
    (target : Structured.ObserverSemantics.State transcript) : Prop where
  compiler :
    ActivationExprContext lowerCtx lowerState localsCtx plan live mode
  planWF :
    plan.WellFormed
  defined :
    AllocationObserverRelation.LiveDefined live source.source
  state :
    AllocationObserverRelation.ActivationStateRel
      contract plan live 0 frameBase mode source target
  stackLength :
    target.source.evm.stack.length = localsCtx.layout.length

namespace ActivationInvariant

/--
Canonical source scope restriction to the invariant's current live set leaves
the complete statement-boundary activation invariant unchanged.
-/
theorem restrict_source_live
    {transcript : AllocationObserverRelation.Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      ActivationInvariant contract lowerCtx lowerState localsCtx plan live
        frameBase mode source target) :
    ActivationInvariant contract lowerCtx lowerState localsCtx plan live
      frameBase mode
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        live source)
      target :=
  { compiler := hInvariant.compiler
    planWF := hInvariant.planWF
    defined := hInvariant.defined.restrictTo (fun _name hLive => hLive)
    state := hInvariant.state.restrict_source_live
    stackLength := hInvariant.stackLength }

/--
Transport a complete activation invariant across Locals contexts with the same
layout.
-/
theorem transport_locals_layout
    {transcript : AllocationObserverRelation.Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {before after : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      ActivationInvariant contract lowerCtx lowerState before plan live
        frameBase mode source target)
    (hLayout : after.layout = before.layout) :
    ActivationInvariant contract lowerCtx lowerState after plan live
      frameBase mode source target :=
  { compiler := hInvariant.compiler.transport_locals_layout hLayout
    planWF := hInvariant.planWF
    defined := hInvariant.defined
    state := hInvariant.state
    stackLength := by
      rw [hInvariant.stackLength, hLayout] }

theorem transport_state
    {transcript : AllocationObserverRelation.Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {before after : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hInvariant :
      ActivationInvariant contract lowerCtx before localsCtx plan live
        frameBase mode source target)
    (hEnv : after.allocation.env = before.allocation.env)
    (hLayout : after.layout = before.layout) :
    ActivationInvariant contract lowerCtx after localsCtx plan live
      frameBase mode source target :=
  { compiler := hInvariant.compiler.transport_state hEnv hLayout
    planWF := hInvariant.planWF
    defined := hInvariant.defined
    state := hInvariant.state
    stackLength := hInvariant.stackLength }

end ActivationInvariant

/--
Exact compiler classification for a lowered source variable.

The constructors retain only semantic location facts and the concrete code
emitted by the existing lowerer plus Locals compiler.
-/
inductive VarCode
    (plan : Plan) (live : List Locals.Name) (name : Locals.Name)
    (offset frameDepth : Nat) : Structured.Code → Prop where
  | stack
      (planDepth depth : Nat) (op : Structured.BasicOp)
      (hLocation :
        plan.location? name = some (.stack planDepth))
      (hCurrentDepth :
        Locals.Layout.lookupDepth?
            name
            (AllocationObserverRelation.currentStackOrder plan live) =
          some (depth + 1))
      (hDup :
        Locals.StackOp.dup? (offset + depth + 1) = some op) :
      VarCode plan live name offset frameDepth [.op op]
  | scratch
      (slot : Nat) (op : Structured.BasicOp)
      (hLocation :
        plan.location? name = some (.scratch slot))
      (hDup :
        Locals.StackOp.dup? (offset + frameDepth + 1) = some op) :
      VarCode plan live name offset frameDepth
        [ .op op,
          .push (AllocationSupport.slotOffset slot),
          .op .add,
          .op .mload ]

theorem classify_var
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameDepth offset : Nat}
    {name : Locals.Name} {lowered : Locals.Expr 1}
    {code : Structured.Code}
    (hCtx :
      ExprContext lowerCtx lowerState localsCtx plan live frameDepth)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState (.var name) =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx offset lowered = some code) :
    VarCode plan live name offset frameDepth code := by
  obtain ⟨slot, hSlot⟩ := hCtx.slot name hLive
  cases hStack :
      AllocationLowering.isStackSlot lowerCtx slot with
  | false =>
      obtain ⟨hLocation, hFrameDepth⟩ :=
        hCtx.scratch name slot hLive hSlot hStack
      have hFrameDepthCtx :
          Locals.Layout.lookupDepth? lowerCtx.frameName localsCtx.layout =
            some (frameDepth + 1) := by
        rw [hCtx.layout]
        exact hFrameDepth
      have hLowered :
          lowered =
            AllocationLowering.scratchLoadExpr lowerCtx.frameName slot := by
        have hParts :
            lowerCtx.frameName ∈ lowerState.layout ∧
              AllocationLowering.scratchLoadExpr
                  lowerCtx.frameName slot =
                lowered := by
          simpa [AllocationLowering.lowerExpr, hSlot, hStack] using hLower
        exact hParts.2.symm
      subst lowered
      cases hDup :
          Locals.StackOp.dup? (offset + (frameDepth + 1)) with
      | none =>
          simp [AllocationLowering.scratchLoadExpr,
            AllocationLowering.scratchAddressExpr,
            AllocationLowering.exprSeqOne,
            AllocationLowering.exprSeqTwo,
            Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
            hFrameDepthCtx, hDup] at hCompile
      | some op =>
          have hCode :
              code =
                [ .op op,
                  .push (AllocationSupport.slotOffset slot),
                  .op .add,
                  .op .mload ] := by
            have hExact :=
              AllocationLowering.scratchLoadExpr_compileCode
                (frameName := lowerCtx.frameName)
                (slot := slot) (offset := offset)
                hFrameDepthCtx hDup
            rw [hExact] at hCompile
            exact Option.some.inj hCompile |>.symm
          subst code
          exact
            .scratch slot op hLocation
              (by simpa [Nat.add_assoc] using hDup)
  | true =>
      obtain
        ⟨planDepth, depth, hLocation, hCurrentDepth, hDepth⟩ :=
        hCtx.stack name slot hLive hSlot hStack
      have hDepthCtx :
          Locals.Layout.lookupDepth? name localsCtx.layout =
            some (depth + 1) := by
        rw [hCtx.layout]
        exact hDepth
      have hLowered : lowered = .var name := by
        have hEq : (.var name : Locals.Expr 1) = lowered := by
          simpa [AllocationLowering.lowerExpr, hSlot, hStack] using hLower
        exact hEq.symm
      subst lowered
      cases hDup :
          Locals.StackOp.dup? (offset + (depth + 1)) with
      | none =>
          simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
      | some op =>
          have hCode : code = [.op op] := by
            simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
            exact hCompile.symm
          subst code
          exact
            .stack planDepth depth op hLocation hCurrentDepth
              (by simpa [Nat.add_assoc] using hDup)

/--
Mode-indexed variable code emitted by the ordinary allocation lowerer and
Locals compiler.

Stack reads carry the dynamic-depth side condition needed to protect a hidden
frame pointer when one exists. Scratch reads are possible only in a scratch
activation.
-/
inductive ActivationVarCode
    (plan : Plan) (live : List Locals.Name) (name : Locals.Name)
    (offset : Nat) :
    AllocationObserverRelation.ActivationMode → Structured.Code → Prop where
  | stack
      {mode : AllocationObserverRelation.ActivationMode}
      (planDepth depth : Nat) (op : Structured.BasicOp)
      (hLocation :
        plan.location? name = some (.stack planDepth))
      (hCurrentDepth :
        Locals.Layout.lookupDepth?
            name
            (AllocationObserverRelation.currentStackOrder plan live) =
          some (depth + 1))
      (hDepthValid : mode.StackDepthValid depth)
      (hDup :
        Locals.StackOp.dup? (offset + depth + 1) = some op) :
      ActivationVarCode plan live name offset mode [.op op]
  | scratch
      (frameDepth frameWords slot : Nat) (op : Structured.BasicOp)
      (hLocation :
        plan.location? name = some (.scratch slot))
      (hDup :
        Locals.StackOp.dup? (offset + frameDepth + 1) = some op) :
      ActivationVarCode plan live name offset
        (.scratch frameDepth frameWords)
        [ .op op,
          .push (AllocationSupport.slotOffset slot),
          .op .add,
          .op .mload ]

theorem classify_activation_var
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {mode : AllocationObserverRelation.ActivationMode}
    {offset : Nat}
    {name : Locals.Name} {lowered : Locals.Expr 1}
    {code : Structured.Code}
    (hCtx :
      ActivationExprContext lowerCtx lowerState localsCtx plan live mode)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState (.var name) =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx offset lowered = some code) :
    ActivationVarCode plan live name offset mode code := by
  cases hCtx with
  | stack hStackCtx =>
      obtain ⟨slot, hSlot⟩ := hStackCtx.slot name hLive
      cases hStack :
          AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          have hFrame :
              lowerCtx.frameName ∈ lowerState.layout := by
            by_contra hFrame
            simp [AllocationLowering.lowerExpr, hSlot, hStack, hFrame]
              at hLower
          exact False.elim (hStackCtx.frameAbsent hFrame)
      | true =>
          obtain
            ⟨planDepth, depth, hLocation, hCurrentDepth, hDepth⟩ :=
            hStackCtx.stack name slot hLive hSlot hStack
          have hDepthCtx :
              Locals.Layout.lookupDepth? name localsCtx.layout =
                some (depth + 1) := by
            rw [hStackCtx.layout]
            exact hDepth
          have hLowered : lowered = .var name := by
            have hEq : (.var name : Locals.Expr 1) = lowered := by
              simpa [AllocationLowering.lowerExpr, hSlot, hStack] using
                hLower
            exact hEq.symm
          subst lowered
          cases hDup :
              Locals.StackOp.dup? (offset + (depth + 1)) with
          | none =>
              simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
          | some op =>
              have hCode : code = [.op op] := by
                simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
                exact hCompile.symm
              subst code
              exact
                .stack planDepth depth op hLocation hCurrentDepth
                  trivial
                  (by simpa [Nat.add_assoc] using hDup)
  | @scratch frameDepth frameWords hScratchCtx =>
      cases classify_var hScratchCtx hLive hLower hCompile with
      | stack planDepth depth op hLocation hCurrentDepth hDup =>
          exact
            .stack planDepth depth op hLocation hCurrentDepth
              (hScratchCtx.stack_depth_lt_frame hCurrentDepth) hDup
      | scratch slot op hLocation hDup =>
          exact
            .scratch frameDepth frameWords slot op hLocation hDup

/--
Allocation-owned transition for one source declaration.

The transition records the dynamic stack-order and hidden-frame-depth changes
that statement preservation needs. It is derived from the real lowering state
and the before/after expression contexts, not from the final plan depth alone.
-/
inductive LetTransition
    (lowerCtx : AllocationLowering.Ctx)
    (beforeState : AllocationLowering.State)
    (plan : Plan) (beforeLive afterLive : List Locals.Name)
    (name : Locals.Name) (beforeFrameDepth afterFrameDepth : Nat) :
    Prop where
  | stack
      (slot planDepth : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack :
        AllocationLowering.isStackSlot lowerCtx slot = true)
      (hLocation : plan.location? name = some (.stack planDepth))
      (hStackOrder :
        AllocationObserverRelation.currentStackOrder plan afterLive =
          name ::
            AllocationObserverRelation.currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth + 1) :
      LetTransition lowerCtx beforeState plan beforeLive afterLive name
        beforeFrameDepth afterFrameDepth
  | scratch
      (slot : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack :
        AllocationLowering.isStackSlot lowerCtx slot = false)
      (hLocation : plan.location? name = some (.scratch slot))
      (hStackOrder :
        AllocationObserverRelation.currentStackOrder plan afterLive =
          AllocationObserverRelation.currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth) :
      LetTransition lowerCtx beforeState plan beforeLive afterLive name
        beforeFrameDepth afterFrameDepth

theorem classify_let_transition
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {beforeFrameDepth afterFrameDepth : Nat}
    {name : Locals.Name} {value : Functions.Expr 1}
    {lowered : List Locals.Stmt}
    (hBefore :
      ExprContext lowerCtx beforeState beforeLocals plan beforeLive
        beforeFrameDepth)
    (hAfter :
      ExprContext lowerCtx afterState afterLocals plan afterLive
        afterFrameDepth)
    (hNameAfter : name ∈ afterLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name value) =
        some (lowered, afterState)) :
    LetTransition lowerCtx beforeState plan beforeLive afterLive name
      beforeFrameDepth afterFrameDepth := by
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx beforeState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
  | some loweredValue =>
      let slot := beforeState.allocation.nextSlot
      have hLookup :
          AllocationSupport.lookupSlot? name
              (AllocationSupport.allocateName
                name beforeState.allocation).2.env =
            some slot := by
        simp [slot, AllocationSupport.allocateName,
          AllocationSupport.lookupSlot?]
      cases hStack :
          AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          by_cases hFrame :
              lowerCtx.frameName ∈ beforeState.layout
          · simp [AllocationLowering.lowerStmt, hLowerValue, slot,
              AllocationSupport.allocateName, hStack, hFrame] at hLower
            rcases hLower with ⟨rfl, rfl⟩
            obtain ⟨hLocation, _hFrame⟩ :=
              hAfter.scratch name slot hNameAfter hLookup hStack
            have hFrameDepth :
                afterFrameDepth = beforeFrameDepth := by
              have hBeforeFrame := hBefore.frame
              have hAfterFrame := hAfter.frame
              rw [hBeforeFrame] at hAfterFrame
              cases hAfterFrame
              omega
            have hStackOrder :
                AllocationObserverRelation.currentStackOrder plan afterLive =
                  AllocationObserverRelation.currentStackOrder
                    plan beforeLive := by
              rw [hAfter.stackPrefix, hBefore.stackPrefix, hFrameDepth]
            exact
              .scratch slot rfl hStack hLocation hStackOrder hFrameDepth
          · simp [AllocationLowering.lowerStmt, hLowerValue, slot,
              AllocationSupport.allocateName, hStack, hFrame] at hLower
      | true =>
          simp [AllocationLowering.lowerStmt, hLowerValue, slot,
            AllocationSupport.allocateName, hStack] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          obtain
            ⟨planDepth, depth, hLocation, _hCurrentDepth, _hLayoutDepth⟩ :=
            hAfter.stack name slot hNameAfter hLookup hStack
          have hShift :=
            Locals.Layout.lookupDepth?_cons_of_ne
              hNameFrame hBefore.frame
          have hFrameDepth :
              afterFrameDepth = beforeFrameDepth + 1 := by
            have hAfterFrame := hAfter.frame
            rw [hAfterFrame] at hShift
            cases hShift
            omega
          have hStackOrder :
              AllocationObserverRelation.currentStackOrder plan afterLive =
                name ::
                  AllocationObserverRelation.currentStackOrder
                    plan beforeLive := by
            rw [hAfter.stackPrefix, hBefore.stackPrefix, hFrameDepth]
            simp [Nat.add_comm]
          exact
            .stack slot planDepth rfl hStack hLocation hStackOrder
              hFrameDepth

end AllocationObserverContext
end Functions
end EvmCompiler
