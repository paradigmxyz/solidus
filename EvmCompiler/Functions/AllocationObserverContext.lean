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
