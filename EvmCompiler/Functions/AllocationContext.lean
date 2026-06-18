import EvmCompiler.Functions.AllocationInteractionRelation
import EvmCompiler.Functions.AllocationLowering

namespace EvmCompiler
namespace Functions
namespace AllocationContext

open AllocationInteractionRelation

/-- Compiler context for one frame-backed allocated expression. -/
structure ExprContext
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name)
    (frameDepth : Nat) : Prop where
  layout : localsCtx.layout = lowerState.layout
  stackPrefix :
    currentStackOrder plan live = lowerState.layout.take frameDepth
  frame :
    Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
      some (frameDepth + 1)
  frameBottom : lowerState.layout.length = frameDepth + 1
  location :
    ∀ name, name ∈ live → ∃ location, plan.location? name = some location
  slot :
    ∀ name, name ∈ live →
      ∃ slot,
        AllocationSupport.lookupSlot? name lowerState.allocation.env = some slot
  stack :
    ∀ name slot,
      name ∈ live →
      AllocationSupport.lookupSlot? name lowerState.allocation.env = some slot →
      AllocationLowering.isStackSlot lowerCtx slot = true →
      ∃ planDepth depth,
        plan.location? name = some (.stack planDepth) ∧
          Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
            some (depth + 1) ∧
          Locals.Layout.lookupDepth? name lowerState.layout =
            some (depth + 1)
  scratch :
    ∀ name slot,
      name ∈ live →
      AllocationSupport.lookupSlot? name lowerState.allocation.env = some slot →
      AllocationLowering.isStackSlot lowerCtx slot = false →
      plan.location? name = some (.scratch slot) ∧
        Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
          some (frameDepth + 1)

namespace ExprContext

theorem currentStackOrder_length
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {frameDepth : Nat}
    (hCtx : ExprContext lowerCtx lowerState localsCtx plan live frameDepth) :
    (currentStackOrder plan live).length = frameDepth := by
  have hFrameAt :
      lowerState.layout[frameDepth]? = some lowerCtx.frameName :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hCtx.frame
  have hFrameBound : frameDepth < lowerState.layout.length :=
    List.getElem?_eq_some_iff.mp hFrameAt |>.1
  rw [hCtx.stackPrefix]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hFrameBound)]

theorem stack_depth_lt_frame
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {frameDepth depth : Nat} {name : Locals.Name}
    (hCtx : ExprContext lowerCtx lowerState localsCtx plan live frameDepth)
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1)) :
    depth < frameDepth := by
  have hAt : (currentStackOrder plan live)[depth]? = some name :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hBound : depth < (currentStackOrder plan live).length :=
    List.getElem?_eq_some_iff.mp hAt |>.1
  simpa [hCtx.currentStackOrder_length] using hBound

/-- A frame-backed context is the active stack order plus its frame pointer. -/
theorem bodyLayout
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {frameDepth : Nat}
    (hCtx : ExprContext lowerCtx lowerState localsCtx plan live frameDepth) :
    lowerState.layout =
      currentStackOrder plan live ++ [lowerCtx.frameName] := by
  have hFrameAt :
      lowerState.layout[frameDepth]? = some lowerCtx.frameName :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hCtx.frame
  have hFrameBound : frameDepth < lowerState.layout.length :=
    List.getElem?_eq_some_iff.mp hFrameAt |>.1
  have hTakeAll :
      lowerState.layout.take (frameDepth + 1) = lowerState.layout := by
    rw [← hCtx.frameBottom]
    simp
  have hFrameElem :
      lowerState.layout[frameDepth] = lowerCtx.frameName :=
    (List.getElem?_eq_some_iff.mp hFrameAt).2
  calc
    lowerState.layout =
        lowerState.layout.take (frameDepth + 1) := hTakeAll.symm
    _ =
        lowerState.layout.take frameDepth ++
          [lowerState.layout[frameDepth]] :=
      List.take_succ_eq_append_getElem hFrameBound
    _ = currentStackOrder plan live ++ [lowerCtx.frameName] := by
      rw [hFrameElem]
      exact congrArg (fun xs => xs ++ [lowerCtx.frameName])
        hCtx.stackPrefix.symm

end ExprContext

/-- Compiler context for an all-stack allocated expression. -/
structure StackExprContext
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name) : Prop where
  layout : localsCtx.layout = lowerState.layout
  stackOrder : currentStackOrder plan live = lowerState.layout
  frameAbsent : lowerCtx.frameName ∉ lowerState.layout
  liveStackOnly : LiveStackOnly plan live
  location :
    ∀ name, name ∈ live → ∃ location, plan.location? name = some location
  slot :
    ∀ name, name ∈ live →
      ∃ slot,
        AllocationSupport.lookupSlot? name lowerState.allocation.env = some slot
  stack :
    ∀ name slot,
      name ∈ live →
      AllocationSupport.lookupSlot? name lowerState.allocation.env = some slot →
      AllocationLowering.isStackSlot lowerCtx slot = true →
      ∃ planDepth depth,
        plan.location? name = some (.stack planDepth) ∧
          Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
            some (depth + 1) ∧
          Locals.Layout.lookupDepth? name lowerState.layout =
            some (depth + 1)

/-- One context indexed by the allocator-selected runtime representation. -/
inductive ActivationExprContext
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name) :
    ActivationMode → Prop where
  | stack
      (ctx : StackExprContext lowerCtx lowerState localsCtx plan live) :
      ActivationExprContext lowerCtx lowerState localsCtx plan live .stack
  | scratch {frameDepth frameWords : Nat}
      (ctx : ExprContext lowerCtx lowerState localsCtx plan live frameDepth) :
      ActivationExprContext lowerCtx lowerState localsCtx plan live
        (.scratch frameDepth frameWords)

namespace ActivationExprContext

/-- Construct an all-stack context from checked layout and plan facts. -/
theorem stack_of_layout
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    (hWF : plan.WellFormed)
    (hLayout : localsCtx.layout = lowerState.layout)
    (hStackOrder : currentStackOrder plan live = lowerState.layout)
    (hFrameAbsent : lowerCtx.frameName ∉ lowerState.layout)
    (hOnly : LiveStackOnly plan live)
    (hLocation :
      ∀ name, name ∈ live →
        ∃ planDepth,
          plan.location? name = some (.stack planDepth))
    (hSlot :
      ∀ name, name ∈ live →
        ∃ slot,
          AllocationSupport.lookupSlot?
              name lowerState.allocation.env =
            some slot) :
    ActivationExprContext lowerCtx lowerState localsCtx plan live .stack := by
  refine .stack
    { layout := hLayout
      stackOrder := hStackOrder
      frameAbsent := hFrameAbsent
      liveStackOnly := hOnly
      location := ?_
      slot := hSlot
      stack := ?_ }
  · intro name hLive
    obtain ⟨planDepth, hPlanLocation⟩ := hLocation name hLive
    exact ⟨.stack planDepth, hPlanLocation⟩
  · intro name slot hLive _hSlot _hClassification
    obtain ⟨planDepth, hPlanLocation⟩ := hLocation name hLive
    have hValid :=
      Locals.Allocation.Plan.bindingValid_of_wellFormed_of_location?_eq_some
        hWF hPlanLocation
    have hPlanMem : name ∈ plan.stackOrder :=
      List.mem_of_getElem? hValid
    have hCurrentMem : name ∈ currentStackOrder plan live := by
      simp [currentStackOrder, hPlanMem, hLive]
    obtain ⟨depth, hDepth⟩ :=
      Locals.Layout.exists_lookupDepth?_eq_some_of_mem hCurrentMem
    exact
      ⟨planDepth, depth, hPlanLocation, hDepth,
        by simpa [← hStackOrder] using hDepth⟩

/-- Construct a frame-backed context from checked layout and plan facts. -/
theorem scratch_of_layout
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameDepth frameWords : Nat}
    (hWF : plan.WellFormed)
    (hLayout : localsCtx.layout = lowerState.layout)
    (hBodyLayout :
      lowerState.layout =
        currentStackOrder plan live ++ [lowerCtx.frameName])
    (hFrameDepth :
      frameDepth = (currentStackOrder plan live).length)
    (hFrameFresh :
      lowerCtx.frameName ∉ currentStackOrder plan live)
    (hSlot :
      ∀ name, name ∈ live →
        ∃ slot,
          AllocationSupport.lookupSlot?
              name lowerState.allocation.env =
            some slot)
    (hStackLocation :
      ∀ name slot,
        name ∈ live →
        AllocationSupport.lookupSlot?
            name lowerState.allocation.env =
          some slot →
        AllocationLowering.isStackSlot lowerCtx slot = true →
        ∃ planDepth,
          plan.location? name = some (.stack planDepth))
    (hScratchLocation :
      ∀ name slot,
        name ∈ live →
        AllocationSupport.lookupSlot?
            name lowerState.allocation.env =
          some slot →
        AllocationLowering.isStackSlot lowerCtx slot = false →
        plan.location? name = some (.scratch slot)) :
    ActivationExprContext lowerCtx lowerState localsCtx plan live
      (.scratch frameDepth frameWords) := by
  let order := currentStackOrder plan live
  have hOrderNodup : order.Nodup :=
    currentStackOrder_nodup hWF
  have hBodyNodup :
      (order ++ [lowerCtx.frameName]).Nodup := by
    apply List.nodup_append.mpr
    exact
      ⟨hOrderNodup, by simp,
        by
          intro left hLeft right hRight hEq
          simp only [List.mem_singleton] at hRight
          subst right
          subst left
          exact hFrameFresh hLeft⟩
  have hFrameLookup :
      Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
        some (frameDepth + 1) := by
    rw [hBodyLayout, hFrameDepth]
    simpa [order] using
      Locals.Layout.lookupDepth?_getLast_of_nodup
        hBodyNodup (by simp)
  refine .scratch
    { layout := hLayout
      stackPrefix := ?_
      frame := hFrameLookup
      frameBottom := ?_
      location := ?_
      slot := hSlot
      stack := ?_
      scratch := ?_ }
  · rw [hBodyLayout, hFrameDepth]
    simp
  · rw [hBodyLayout, hFrameDepth]
    simp
  · intro name hLive
    obtain ⟨slot, hLookup⟩ := hSlot name hLive
    by_cases hStack :
        AllocationLowering.isStackSlot lowerCtx slot = true
    · obtain ⟨planDepth, hPlanLocation⟩ :=
        hStackLocation name slot hLive hLookup hStack
      exact ⟨.stack planDepth, hPlanLocation⟩
    · have hScratch :
          AllocationLowering.isStackSlot lowerCtx slot = false :=
        Bool.eq_false_of_not_eq_true hStack
      exact
        ⟨.scratch slot,
          hScratchLocation name slot hLive hLookup hScratch⟩
  · intro name slot hLive hLookup hClassification
    obtain ⟨planDepth, hPlanLocation⟩ :=
      hStackLocation name slot hLive hLookup hClassification
    have hValid :=
      Locals.Allocation.Plan.bindingValid_of_wellFormed_of_location?_eq_some
        hWF hPlanLocation
    have hPlanMem : name ∈ plan.stackOrder :=
      List.mem_of_getElem? hValid
    have hCurrentMem : name ∈ order := by
      simp [order, currentStackOrder, hPlanMem, hLive]
    obtain ⟨depth, hDepth⟩ :=
      Locals.Layout.exists_lookupDepth?_eq_some_of_mem hCurrentMem
    have hAt : order[depth]? = some name :=
      Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
    have hDepthBound : depth < order.length :=
      List.getElem?_eq_some_iff.mp hAt |>.1
    have hBodyAt : lowerState.layout[depth]? = some name := by
      rw [hBodyLayout]
      rw [List.getElem?_append_left hDepthBound]
      exact hAt
    have hLowerNodup : lowerState.layout.Nodup := by
      simpa [hBodyLayout] using hBodyNodup
    have hLowerDepth :=
      Locals.Layout.lookupDepth?_eq_some_of_getElem?_eq_some_of_nodup
        hLowerNodup hBodyAt
    exact
      ⟨planDepth, depth, hPlanLocation,
        by simpa [order] using hDepth, hLowerDepth⟩
  · intro name slot hLive hLookup hClassification
    exact
      ⟨hScratchLocation name slot hLive hLookup hClassification,
        hFrameLookup⟩

end ActivationExprContext

/-- Runtime-representation change caused by one allocated declaration. -/
inductive DeclarationModeTransition
    (plan : Plan) (name : Locals.Name) :
    ActivationMode → ActivationMode → Prop where
  | stack
      {before : ActivationMode} (planDepth : Nat)
      (hLocation : plan.location? name = some (.stack planDepth)) :
      DeclarationModeTransition plan name
        before before.afterStackDeclaration
  | scratch
      (frameDepth frameWords slot : Nat)
      (hLocation : plan.location? name = some (.scratch slot)) :
      DeclarationModeTransition plan name
        (.scratch frameDepth frameWords)
        (.scratch frameDepth frameWords)

/-- Complete observer-free invariant at a Functions statement boundary. -/
structure ActivationInvariant
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name)
    (frameBase : Nat) (mode : ActivationMode)
    (source : AllocationInteractionRelation.SourceState)
    (target : AllocationInteractionRelation.TargetState) : Prop where
  compiler :
    ActivationExprContext lowerCtx lowerState localsCtx plan live mode
  planWF : plan.WellFormed
  defined : AllocationInteractionRelation.LiveDefined live source
  state :
    ActivationStateRel contract plan live 0 frameBase mode source target
  stackLength : target.evm.stack.length = localsCtx.layout.length

namespace ActivationInvariant

/-- Restricting source scope to the current live set preserves the boundary. -/
theorem restrict_source_live
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {source : AllocationInteractionRelation.SourceState}
    {target : AllocationInteractionRelation.TargetState}
    (hInvariant :
      ActivationInvariant contract lowerCtx lowerState localsCtx plan live
        frameBase mode source target) :
    ActivationInvariant contract lowerCtx lowerState localsCtx plan live
      frameBase mode (source.restrictTo live) target :=
  { compiler := hInvariant.compiler
    planWF := hInvariant.planWF
    defined :=
      hInvariant.defined.restrictTo (fun _name hLive => hLive)
    state := hInvariant.state.restrict_source_live
    stackLength := hInvariant.stackLength }

end ActivationInvariant

/-- Exact lowerer/compiler classification of one frame-backed variable read. -/
inductive VarCode
    (plan : Plan) (live : List Locals.Name) (name : Locals.Name)
    (offset frameDepth : Nat) : Structured.Code → Prop where
  | stack
      (planDepth depth : Nat) (op : Structured.BasicOp)
      (location : plan.location? name = some (.stack planDepth))
      (currentDepth :
        Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
          some (depth + 1))
      (dup : Locals.StackOp.dup? (offset + depth + 1) = some op) :
      VarCode plan live name offset frameDepth [.op op]
  | scratch
      (slot : Nat) (op : Structured.BasicOp)
      (location : plan.location? name = some (.scratch slot))
      (dup : Locals.StackOp.dup? (offset + frameDepth + 1) = some op) :
      VarCode plan live name offset frameDepth
        [.op op, .push (AllocationSupport.slotOffset slot), .op .add, .op .mload]

theorem classify_var
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {frameDepth offset : Nat} {name : Locals.Name}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    (hCtx : ExprContext lowerCtx lowerState localsCtx plan live frameDepth)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState (.var name) =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx offset lowered = some code) :
    VarCode plan live name offset frameDepth code := by
  obtain ⟨slot, hSlot⟩ := hCtx.slot name hLive
  cases hStack : AllocationLowering.isStackSlot lowerCtx slot with
  | false =>
      obtain ⟨hLocation, hFrameDepth⟩ :=
        hCtx.scratch name slot hLive hSlot hStack
      have hFrameDepthCtx :
          Locals.Layout.lookupDepth? lowerCtx.frameName localsCtx.layout =
            some (frameDepth + 1) := by
        rw [hCtx.layout]
        exact hFrameDepth
      have hLowered :
          lowered = AllocationLowering.scratchLoadExpr lowerCtx.frameName slot := by
        have hParts :
            lowerCtx.frameName ∈ lowerState.layout ∧
              AllocationLowering.scratchLoadExpr lowerCtx.frameName slot =
                lowered := by
          simpa [AllocationLowering.lowerExpr, hSlot, hStack] using hLower
        exact hParts.2.symm
      subst lowered
      cases hDup :
          Locals.StackOp.dup? (offset + (frameDepth + 1)) with
      | none =>
          simp [AllocationLowering.scratchLoadExpr,
            AllocationLowering.scratchAddressExpr,
            AllocationLowering.exprSeqOne, AllocationLowering.exprSeqTwo,
            Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
            hFrameDepthCtx, hDup] at hCompile
      | some op =>
          have hCode :
              code =
                [.op op, .push (AllocationSupport.slotOffset slot),
                  .op .add, .op .mload] := by
            have hExact :=
              AllocationLowering.scratchLoadExpr_compileCode
                (frameName := lowerCtx.frameName) (slot := slot)
                (offset := offset) hFrameDepthCtx hDup
            rw [hExact] at hCompile
            exact Option.some.inj hCompile |>.symm
          subst code
          exact .scratch slot op hLocation
            (by simpa [Nat.add_assoc] using hDup)
  | true =>
      obtain ⟨planDepth, depth, hLocation, hCurrentDepth, hDepth⟩ :=
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
      cases hDup : Locals.StackOp.dup? (offset + (depth + 1)) with
      | none =>
          simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
      | some op =>
          have hCode : code = [.op op] := by
            simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
            exact hCompile.symm
          subst code
          exact .stack planDepth depth op hLocation hCurrentDepth
            (by simpa [Nat.add_assoc] using hDup)

/-- Mode-indexed exact code emitted for one variable read. -/
inductive ActivationVarCode
    (plan : Plan) (live : List Locals.Name) (name : Locals.Name)
    (offset : Nat) : ActivationMode → Structured.Code → Prop where
  | stack {mode : ActivationMode}
      (planDepth depth : Nat) (op : Structured.BasicOp)
      (location : plan.location? name = some (.stack planDepth))
      (currentDepth :
        Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
          some (depth + 1))
      (depthValid : mode.StackDepthValid depth)
      (dup : Locals.StackOp.dup? (offset + depth + 1) = some op) :
      ActivationVarCode plan live name offset mode [.op op]
  | scratch
      (frameDepth frameWords slot : Nat) (op : Structured.BasicOp)
      (location : plan.location? name = some (.scratch slot))
      (dup : Locals.StackOp.dup? (offset + frameDepth + 1) = some op) :
      ActivationVarCode plan live name offset (.scratch frameDepth frameWords)
        [.op op, .push (AllocationSupport.slotOffset slot), .op .add, .op .mload]

theorem classify_activation_var
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {mode : ActivationMode} {offset : Nat} {name : Locals.Name}
    {lowered : Locals.Expr 1} {code : Structured.Code}
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
      cases hStack : AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          have hFrame : lowerCtx.frameName ∈ lowerState.layout := by
            by_contra hFrame
            simp [AllocationLowering.lowerExpr, hSlot, hStack, hFrame] at hLower
          exact False.elim (hStackCtx.frameAbsent hFrame)
      | true =>
          obtain ⟨planDepth, depth, hLocation, hCurrentDepth, hDepth⟩ :=
            hStackCtx.stack name slot hLive hSlot hStack
          have hDepthCtx :
              Locals.Layout.lookupDepth? name localsCtx.layout =
                some (depth + 1) := by
            rw [hStackCtx.layout]
            exact hDepth
          have hLowered : lowered = .var name := by
            have hEq : (.var name : Locals.Expr 1) = lowered := by
              simpa [AllocationLowering.lowerExpr, hSlot, hStack] using hLower
            exact hEq.symm
          subst lowered
          cases hDup : Locals.StackOp.dup? (offset + (depth + 1)) with
          | none =>
              simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
          | some op =>
              have hCode : code = [.op op] := by
                simp [Locals.Expr.compileCode, hDepthCtx, hDup] at hCompile
                exact hCompile.symm
              subst code
              exact .stack planDepth depth op hLocation hCurrentDepth trivial
                (by simpa [Nat.add_assoc] using hDup)
  | @scratch frameDepth frameWords hScratchCtx =>
      cases classify_var hScratchCtx hLive hLower hCompile with
      | stack planDepth depth op hLocation hCurrentDepth hDup =>
          exact .stack planDepth depth op hLocation hCurrentDepth
            (hScratchCtx.stack_depth_lt_frame hCurrentDepth) hDup
      | scratch slot op hLocation hDup =>
          exact .scratch frameDepth frameWords slot op hLocation hDup

/--
Runtime-representation transition induced by one allocated declaration.
This compiler-owned classification is independent of any observation model.
-/
inductive LetTransition
    (lowerCtx : AllocationLowering.Ctx)
    (beforeState : AllocationLowering.State)
    (plan : Plan) (beforeLive afterLive : List Locals.Name)
    (name : Locals.Name) (beforeFrameDepth afterFrameDepth : Nat) : Prop where
  | stack
      (slot planDepth : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack : AllocationLowering.isStackSlot lowerCtx slot = true)
      (hLocation : plan.location? name = some (.stack planDepth))
      (hStackOrder :
        currentStackOrder plan afterLive =
          name :: currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth + 1) :
      LetTransition lowerCtx beforeState plan beforeLive afterLive name
        beforeFrameDepth afterFrameDepth
  | scratch
      (slot : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack : AllocationLowering.isStackSlot lowerCtx slot = false)
      (hLocation : plan.location? name = some (.scratch slot))
      (hStackOrder :
        currentStackOrder plan afterLive =
          currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth) :
      LetTransition lowerCtx beforeState plan beforeLive afterLive name
        beforeFrameDepth afterFrameDepth

/-- Classify the exact stack/scratch transition selected by `lowerStmt`. -/
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
      cases hStack : AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          by_cases hFrame : lowerCtx.frameName ∈ beforeState.layout
          · simp [AllocationLowering.lowerStmt, hLowerValue, slot,
              AllocationSupport.allocateName, hStack, hFrame] at hLower
            rcases hLower with ⟨rfl, rfl⟩
            obtain ⟨hLocation, _hFrame⟩ :=
              hAfter.scratch name slot hNameAfter hLookup hStack
            have hFrameDepth : afterFrameDepth = beforeFrameDepth := by
              have hBeforeFrame := hBefore.frame
              have hAfterFrame := hAfter.frame
              rw [hBeforeFrame] at hAfterFrame
              cases hAfterFrame
              omega
            have hStackOrder :
                currentStackOrder plan afterLive =
                  currentStackOrder plan beforeLive := by
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
            Locals.Layout.lookupDepth?_cons_of_ne hNameFrame hBefore.frame
          have hFrameDepth :
              afterFrameDepth = beforeFrameDepth + 1 := by
            have hAfterFrame := hAfter.frame
            rw [hAfterFrame] at hShift
            cases hShift
            omega
          have hStackOrder :
              currentStackOrder plan afterLive =
                name :: currentStackOrder plan beforeLive := by
            rw [hAfter.stackPrefix, hBefore.stackPrefix, hFrameDepth]
            simp [Nat.add_comm]
          exact
            .stack slot planDepth rfl hStack hLocation hStackOrder
              hFrameDepth

end AllocationContext
end Functions
end EvmCompiler
