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
      ∃ depth,
        plan.location? name = some (.stack depth) ∧
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

/--
Exact compiler classification for a lowered source variable.

The constructors retain only semantic location facts and the concrete code
emitted by the existing lowerer plus Locals compiler.
-/
inductive VarCode
    (plan : Plan) (name : Locals.Name)
    (offset frameDepth : Nat) : Structured.Code → Prop where
  | stack
      (depth : Nat) (op : Structured.BasicOp)
      (hLocation :
        plan.location? name = some (.stack depth))
      (hDup :
        Locals.StackOp.dup? (offset + depth + 1) = some op) :
      VarCode plan name offset frameDepth [.op op]
  | scratch
      (slot : Nat) (op : Structured.BasicOp)
      (hLocation :
        plan.location? name = some (.scratch slot))
      (hDup :
        Locals.StackOp.dup? (offset + frameDepth + 1) = some op) :
      VarCode plan name offset frameDepth
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
    VarCode plan name offset frameDepth code := by
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
      obtain ⟨depth, hLocation, hDepth⟩ :=
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
            .stack depth op hLocation
              (by simpa [Nat.add_assoc] using hDup)

end AllocationObserverContext
end Functions
end EvmCompiler
