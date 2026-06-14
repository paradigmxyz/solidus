import EvmCompiler.Functions.MixedAllocation
import EvmCompiler.Functions.SourceSemantics
import EvmCompiler.Compiler.AllocatedTypedCfg

namespace EvmCompiler
namespace Functions
namespace AllocationLowering

open Locals.Allocation

abbrev SlotSet := MixedAllocation.SlotSet

structure State where
  allocation : AllocationSupport.CompileState
  layout : Locals.Layout
  deriving DecidableEq, Repr

structure Ctx where
  functions : List AllocationSupport.FunSlots
  frameConfig? : Option AllocationSupport.ScratchFrameConfig
  frameName : Name
  stackSlots : SlotSet
  root : ScopeId
  scratchBindings : List (Name × Nat)
  frameFunctions : List Name

def isStackSlot (ctx : Ctx) (slot : Nat) : Bool :=
  decide (slot ∈ ctx.stackSlots)

theorem isStackSlot_eq_true_iff
    (ctx : Ctx) (slot : Nat) :
    isStackSlot ctx slot = true ↔ slot ∈ ctx.stackSlots := by
  simp [isStackSlot]

theorem isStackSlot_eq_false_iff
    (ctx : Ctx) (slot : Nat) :
    isStackSlot ctx slot = false ↔ slot ∉ ctx.stackSlots := by
  simp [isStackSlot]

def frameDepth? (ctx : Ctx) (state : State) : Option Nat := do
  let depth ← Locals.Layout.lookupDepth? ctx.frameName state.layout
  some (depth - 1)

def exprSeqOne (expr : Locals.Expr 1) : Locals.ExprSeq 1 := by
  simpa using Locals.ExprSeq.cons expr Locals.ExprSeq.nil

def exprSeqTwo (left right : Locals.Expr 1) : Locals.ExprSeq 2 := by
  simpa using
    Locals.ExprSeq.cons left
      (Locals.ExprSeq.cons right Locals.ExprSeq.nil)

def scratchAddressExpr (frameName : Name) (slot : Nat) : Locals.Expr 1 :=
  .prim .add
    (exprSeqTwo (.var frameName) (.lit (AllocationSupport.slotOffset slot)))

def scratchLoadExpr (frameName : Name) (slot : Nat) : Locals.Expr 1 :=
  .prim .mload (exprSeqOne (scratchAddressExpr frameName slot))

def scratchStoreExpr (frameName : Name) (slot : Nat)
    (value : Locals.Expr 1) : Locals.Expr 0 :=
  .prim .mstore
    (exprSeqTwo value (scratchAddressExpr frameName slot))

mutual
  def lowerExpr (ctx : Ctx) (state : State) {results : Nat} :
      Expr results → Option (Locals.Expr results)
    | .lit value => some (.lit value)
    | .var name => do
        let slot ← AllocationSupport.lookupSlot? name state.allocation.env
        if isStackSlot ctx slot then
          some (.var name)
        else
          if ctx.frameName ∈ state.layout then
            some (scratchLoadExpr ctx.frameName slot)
          else
            none
    | .code code => some (.code code)
    | .prim op args => do
        let lowered ← lowerExprSeq ctx state args
        some (.prim op lowered)

  def lowerExprSeq (ctx : Ctx) (state : State) {results : Nat} :
      Locals.ExprSeq results → Option (Locals.ExprSeq results)
    | .nil => some .nil
    | .cons head tail => do
        let loweredHead ← lowerExpr ctx state head
        let loweredTail ← lowerExprSeq ctx state tail
        some (.cons loweredHead loweredTail)
end

theorem lowerExpr_var_scratch
    {ctx : Ctx} {state : State} {name : Name} {slot : Nat}
    (hSlot :
      AllocationSupport.lookupSlot? name state.allocation.env =
        some slot)
    (hStack : isStackSlot ctx slot = false)
    (hFrame : ctx.frameName ∈ state.layout) :
    lowerExpr ctx state (.var name) =
      some (scratchLoadExpr ctx.frameName slot) := by
  simp [lowerExpr, hSlot, hStack, hFrame]

theorem scratchLoadExpr_compileCode
    {frameName : Name} {slot offset depth : Nat}
    {ctx : Locals.Ctx} {op : Structured.BasicOp}
    (hDepth :
      Locals.Layout.lookupDepth? frameName ctx.layout =
        some depth)
    (hDup :
      Locals.StackOp.dup? (offset + depth) = some op) :
    Locals.Expr.compileCode ctx offset
        (scratchLoadExpr frameName slot) =
      some
        [ .op op,
          .push (AllocationSupport.slotOffset slot),
          .op .add,
          .op .mload ] := by
  simp [scratchLoadExpr, scratchAddressExpr, exprSeqOne, exprSeqTwo,
    Locals.Expr.compileCode, Locals.ExprSeq.compileCode, hDepth, hDup]

theorem scratchStoreExpr_compileCode
    {frameName : Name} {slot offset depth : Nat}
    {ctx : Locals.Ctx} {value : Locals.Expr 1}
    {valueCode : Structured.Code} {op : Structured.BasicOp}
    (hValue :
      Locals.Expr.compileCode ctx offset value = some valueCode)
    (hDepth :
      Locals.Layout.lookupDepth? frameName ctx.layout =
        some depth)
    (hDup :
      Locals.StackOp.dup? (offset + 1 + depth) = some op) :
    Locals.Expr.compileCode ctx offset
        (scratchStoreExpr frameName slot value) =
      some
        (valueCode ++
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mstore ]) := by
  simp [scratchStoreExpr, scratchAddressExpr, exprSeqTwo,
    Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
    hValue, hDepth, hDup]

def lowerExprList (ctx : Ctx) (state : State) :
    List (Expr 1) → Option (List (Locals.Expr 1))
  | [] => some []
  | expr :: rest => do
      let lowered ← lowerExpr ctx state expr
      let tail ← lowerExprList ctx state rest
      some (lowered :: tail)

def exprSeqOfList : (exprs : List (Locals.Expr 1)) →
    Locals.ExprSeq exprs.length
  | [] => .nil
  | expr :: rest => by
      simpa [Nat.add_comm] using
        Locals.ExprSeq.cons expr (exprSeqOfList rest)

@[simp] theorem exprSeqOfList_compileCode_nil
    (ctx : Locals.Ctx) (offset : Nat) :
    Locals.ExprSeq.compileCode ctx offset (exprSeqOfList []) =
      some [] := by
  rfl

theorem exprSeqOfList_compileCode_cons
    (ctx : Locals.Ctx) (offset : Nat)
    (expr : Locals.Expr 1) (rest : List (Locals.Expr 1)) :
    Locals.ExprSeq.compileCode ctx offset (exprSeqOfList (expr :: rest)) =
      (do
        let headCode ← Locals.Expr.compileCode ctx offset expr
        let tailCode ←
          Locals.ExprSeq.compileCode ctx (offset + 1)
            (exprSeqOfList rest)
        some (headCode ++ tailCode)) := by
  rw [exprSeqOfList.eq_2]
  rw [Locals.ExprSeq.compileCode_eqMpr]
  · rfl
  · simp [Nat.add_comm]

def eraseName (name : Name) (layout : Locals.Layout) : Locals.Layout :=
  layout.filter fun candidate => candidate != name

private theorem filter_ne_self
    {name : Name} {layout : Locals.Layout}
    (hNotMem : name ∉ layout) :
    layout.filter (fun candidate => candidate != name) = layout := by
  induction layout with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead : head ≠ name := by
        intro hEq
        subst head
        exact hNotMem (by simp)
      have hTail : name ∉ tail := by
        intro hMem
        exact hNotMem (by simp [hMem])
      simp [hHead, ih hTail]

theorem eraseName_append_name
    {name : Name} {above suffix : Locals.Layout}
    (hAbove : name ∉ above)
    (hSuffix : name ∉ suffix) :
    eraseName name (above ++ name :: suffix) = above ++ suffix := by
  simp [eraseName, List.filter_append,
    filter_ne_self hAbove, filter_ne_self hSuffix]

theorem promoteAt_append_name
    (name : Name) (above suffix : Locals.Layout) :
    Locals.Layout.promoteAt above.length
        (above ++ name :: suffix) =
      name :: above ++ suffix := by
  unfold Locals.Layout.promoteAt
  rw [List.getElem?_append_right (Nat.le_refl above.length)]
  simp

def bindEntryLayout (layout : Locals.Layout) : Locals.Stmt :=
  .expr
    (Locals.Expr.code (results := 0)
      [Structured.BasicInstr.bindLocals 0 layout])

def bindScratchBindings (baseDepth : Nat)
    (bindings : List (Name × Nat)) : Locals.Stmt :=
  .expr
    (Locals.Expr.code (results := 0)
      (AllocationSupport.bindScratchBindingsCode baseDepth bindings))

/--
The function-entry metadata emitted by this pass compiles without changing the
ordinary Locals compiler context.
-/
theorem entryMarkers_compileOpen
    {localsCtx : Locals.Ctx}
    {entryLayout : Locals.Layout}
    {baseDepth : Nat}
    {scratchBindings : List (Name × Nat)}
    {needsFrame : Bool} :
    Locals.Block.compileOpen localsCtx
        { stmts :=
            [bindEntryLayout entryLayout] ++
              if needsFrame then
                [bindScratchBindings baseDepth scratchBindings]
              else
                [] } =
      some
        ([Expressions.Stmt.code
            [Structured.BasicInstr.bindLocals 0 entryLayout]] ++
          if needsFrame then
            [Expressions.Stmt.code
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)]
          else
            [],
         localsCtx) := by
  cases needsFrame <;>
    simp [bindEntryLayout, bindScratchBindings,
      Locals.Block.compileOpen, Locals.Stmt.compile,
      Locals.Expr.compileCode, Locals.codeStmt]

def frameExpr
    (config : AllocationSupport.ScratchFrameConfig) : Locals.Expr 1 :=
  .code (AllocationSupport.scratchFrameAcquireCode config)

def splitPrelude : List Stmt → List Locals.Stmt × List Stmt
  | [] => ([], [])
  | stmt :: rest =>
      match AllocationSupport.compilePreludeStmt? stmt with
      | some (.code code) =>
          let (loweredPrefix, tail) := splitPrelude rest
          (.expr (Locals.Expr.code (results := 0) code) ::
              loweredPrefix,
            tail)
      | _ => ([], stmt :: rest)

def lowerScratchParam (ctx : Ctx) (name : Name) (slot : Nat)
    (layout : Locals.Layout) : List Locals.Stmt × Locals.Layout :=
  let target := eraseName name layout
  ([ .expr (scratchStoreExpr ctx.frameName slot (.var name)),
     .promoteName name,
     .cleanupTo target ],
   target)

/--
The real scratch-parameter lowerer compiles to one value/frame store, the
compiler's promotion swaps, and one final pop.
-/
theorem lowerScratchParam_compileOpen
    {ctx : Ctx} {name : Name} {slot frameDepth : Nat}
    {above suffix : Locals.Layout}
    {localsCtx : Locals.Ctx}
    {nameOp frameOp : Structured.BasicOp}
    {promoteCode : Structured.Code}
    (hLayout :
      localsCtx.layout = above ++ name :: suffix)
    (hAbove : name ∉ above)
    (hSuffix : name ∉ suffix)
    (hBound : above.length ≤ 16)
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName
          (above ++ name :: suffix) =
        some frameDepth)
    (hNameOp :
      Locals.StackOp.dup? (above.length + 1) = some nameOp)
    (hFrameOp :
      Locals.StackOp.dup? (1 + frameDepth) = some frameOp)
    (hPromote :
      Locals.Ctx.swapRestoreUpTo? above.length = some promoteCode) :
    Locals.Block.compileOpen localsCtx
        { stmts := (lowerScratchParam ctx name slot
            (above ++ name :: suffix)).1 } =
      some
        ([ Expressions.Stmt.code
              ([Structured.BasicInstr.op nameOp] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ]),
           Expressions.Stmt.code promoteCode,
           Expressions.Stmt.code [Structured.BasicInstr.op .pop] ],
         localsCtx.withLayout (above ++ suffix)) := by
  have hNameDepth :
      Locals.Layout.lookupDepth? name
          (above ++ name :: suffix) =
        some (above.length + 1) := by
    apply Locals.Layout.lookupDepth?_append_of_not_mem hAbove
    simp [Locals.Layout.lookupDepth?, Locals.Layout.lookupDepthFrom]
  have hValueCompile :
      Locals.Expr.compileCode localsCtx 0 (.var name) =
        some [Structured.BasicInstr.op nameOp] := by
    simp [Locals.Expr.compileCode, hLayout, hNameDepth, hNameOp]
  have hStoreCompile :
      Locals.Expr.compileCode localsCtx 0
          (scratchStoreExpr ctx.frameName slot (.var name)) =
        some
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ]) := by
    apply scratchStoreExpr_compileCode hValueCompile
    · simpa [hLayout] using hFrameDepth
    · simpa using hFrameOp
  have hTarget :
      eraseName name (above ++ name :: suffix) =
        above ++ suffix :=
    eraseName_append_name hAbove hSuffix
  have hPromoteAt :
      Locals.Layout.promoteAt above.length
          (above ++ name :: suffix) =
        name :: above ++ suffix :=
    promoteAt_append_name name above suffix
  have hPromoteCtx :
      localsCtx.promoteNameStackOnly? name =
        some (promoteCode, name :: above ++ suffix) := by
    unfold Locals.Ctx.promoteNameStackOnly?
    rw [hLayout, hNameDepth]
    have hDepthBound : above.length + 1 ≤ 17 := by
      omega
    simp [hDepthBound, hPromote, hPromoteAt]
  have hCleanupCtx :
      (localsCtx.withLayout
          (name :: above ++ suffix)).cleanupTo?
          (above ++ suffix).length =
        some [Structured.BasicInstr.op .pop] := by
    simp [Locals.Ctx.cleanupTo?, Locals.Ctx.withLayout]
  have hStoreStmt :
      Locals.Stmt.compile localsCtx
          (.expr
            (scratchStoreExpr ctx.frameName slot (.var name))) =
        some
          ([Expressions.Stmt.code
              ([Structured.BasicInstr.op nameOp] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ])],
           localsCtx) := by
    simp [Locals.Stmt.compile, hStoreCompile, Locals.codeStmt]
  have hPromoteStmt :
      Locals.Stmt.compile localsCtx (.promoteName name) =
        some
          ([Expressions.Stmt.code promoteCode],
           localsCtx.withLayout (name :: above ++ suffix)) := by
    simp [Locals.Stmt.compile, hPromoteCtx, Locals.codeStmt]
  have hCleanupStmt :
      Locals.Stmt.compile
          (localsCtx.withLayout (name :: above ++ suffix))
          (.cleanupTo (above ++ suffix)) =
        some
          ([Expressions.Stmt.code [Structured.BasicInstr.op .pop]],
           localsCtx.withLayout (above ++ suffix)) := by
    unfold Locals.Stmt.compile
    rw [if_pos (by simp [Locals.Ctx.withLayout])]
    rw [hCleanupCtx]
    rfl
  simp only [lowerScratchParam, hTarget]
  simp only [Locals.Block.compileOpen, hStoreStmt, hPromoteStmt,
    hCleanupStmt, Bind.bind, Option.bind, List.append_nil]
  rfl

theorem lowerScratchParam_compileOpen_depth_bounds
    {ctx : Ctx} {name : Name} {slot frameDepth : Nat}
    {above suffix : Locals.Layout}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hLayout :
      localsCtx.layout = above ++ name :: suffix)
    (hAbove : name ∉ above)
    (hSuffix : name ∉ suffix)
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName
          (above ++ name :: suffix) =
        some frameDepth)
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (lowerScratchParam ctx name slot
                (above ++ name :: suffix)).1 } =
        some (compiled, finalCtx)) :
    above.length + 1 ≤ 16 ∧
      1 + frameDepth ≤ 16 := by
  have hNameDepth :
      Locals.Layout.lookupDepth? name
          (above ++ name :: suffix) =
        some (above.length + 1) := by
    apply Locals.Layout.lookupDepth?_append_of_not_mem hAbove
    simp [Locals.Layout.lookupDepth?, Locals.Layout.lookupDepthFrom]
  have hTarget :
      eraseName name (above ++ name :: suffix) =
        above ++ suffix :=
    eraseName_append_name hAbove hSuffix
  cases hStore :
      Locals.Stmt.compile localsCtx
        (.expr (scratchStoreExpr ctx.frameName slot (.var name))) with
  | none =>
      simp [lowerScratchParam, hTarget, Locals.Block.compileOpen,
        hStore] at hCompile
  | some storeResult =>
      cases hNameOp :
          Locals.StackOp.dup? (above.length + 1) with
      | none =>
          simp [Locals.Stmt.compile, scratchStoreExpr,
            scratchAddressExpr, exprSeqTwo, Locals.Expr.compileCode,
            Locals.ExprSeq.compileCode, hLayout, hNameDepth, hNameOp]
            at hStore
      | some nameOp =>
          cases hFrameOp :
              Locals.StackOp.dup? (1 + frameDepth) with
          | none =>
              simp [Locals.Stmt.compile, scratchStoreExpr,
                scratchAddressExpr, exprSeqTwo,
                Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                hLayout, hNameDepth, hNameOp, hFrameDepth, hFrameOp]
                at hStore
          | some frameOp =>
              exact
                ⟨(Locals.StackOp.bounds_of_dup?_eq_some hNameOp).2,
                  (Locals.StackOp.bounds_of_dup?_eq_some hFrameOp).2⟩

/--
Successful compilation of the real scratch-parameter sequence installs the
layout returned by `lowerScratchParam`.
-/
theorem lowerScratchParam_compileOpen_final_layout
    {ctx : Ctx} {name : Name} {slot : Nat}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (lowerScratchParam ctx name slot localsCtx.layout).1 } =
        some (compiled, finalCtx)) :
    finalCtx.layout =
      (lowerScratchParam ctx name slot localsCtx.layout).2 := by
  let target := eraseName name localsCtx.layout
  have hCompile' :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              [ .expr
                  (scratchStoreExpr ctx.frameName slot (.var name)),
                .promoteName name ] ++
                [.cleanupTo target] } =
        some (compiled, finalCtx) := by
    simpa [lowerScratchParam, target] using hCompile
  obtain
      ⟨prefixCode, middle, cleanupCode,
        _hPrefix, hCleanupBlock, _hCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile'
  cases hCleanup :
      Locals.Stmt.compile middle (.cleanupTo target) with
  | none =>
      simp [Locals.Block.compileOpen, hCleanup] at hCleanupBlock
  | some cleanupResult =>
      rcases cleanupResult with ⟨stmtCode, cleanupCtx⟩
      have hCleanupComponents :=
        Locals.Stmt.compile_cleanupTo_components hCleanup
      simp [Locals.Block.compileOpen, hCleanup] at hCleanupBlock
      rcases hCleanupBlock with ⟨rfl, rfl⟩
      obtain ⟨_cleanup, _hTarget, _hCleanup, _hStmtCode, hFinal⟩ :=
        hCleanupComponents
      rw [hFinal]
      simp [Locals.Ctx.withLayout, lowerScratchParam, target]

/--
The scratch-parameter sequence changes only the Locals layout, installing the
layout returned by `lowerScratchParam`.
-/
theorem lowerScratchParam_compileOpen_final_ctx
    {ctx : Ctx} {name : Name} {slot : Nat}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (lowerScratchParam ctx name slot localsCtx.layout).1 } =
        some (compiled, finalCtx)) :
    finalCtx =
      localsCtx.withLayout
        (lowerScratchParam ctx name slot localsCtx.layout).2 := by
  let target := eraseName name localsCtx.layout
  have hCompile' :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              [ .expr
                  (scratchStoreExpr ctx.frameName slot (.var name)),
                .promoteName name ] ++
                [.cleanupTo target] } =
        some (compiled, finalCtx) := by
    simpa [lowerScratchParam, target] using hCompile
  obtain
      ⟨prefixCode, middle, cleanupCode,
        hPrefix, hCleanupBlock, _hCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile'
  have hPrefix' :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              [.expr
                (scratchStoreExpr ctx.frameName slot (.var name))] ++
                [.promoteName name] } =
        some (prefixCode, middle) := by
    simpa using hPrefix
  obtain
      ⟨storeCode, afterStore, promoteCode,
        hStoreBlock, hPromoteBlock, _hPrefixCode⟩ :=
    Locals.Block.compileOpen_append_components hPrefix'
  have hStoreStmt :=
    Locals.Block.compileOpen_single_components hStoreBlock
  have hAfterStore :=
    Locals.Stmt.compile_expr_final hStoreStmt
  subst afterStore
  have hPromoteStmt :=
    Locals.Block.compileOpen_single_components hPromoteBlock
  obtain ⟨promotedLayout, hMiddle⟩ :=
    Locals.Stmt.compile_promoteName_final hPromoteStmt
  subst middle
  have hCleanupStmt :=
    Locals.Block.compileOpen_single_components hCleanupBlock
  obtain
      ⟨cleanup, _hTarget, _hCleanup, _hCleanupCode, hFinal⟩ :=
    Locals.Stmt.compile_cleanupTo_components hCleanupStmt
  rw [hFinal]
  simp [Locals.Ctx.withLayout, lowerScratchParam, target]

def lowerParams (ctx : Ctx) :
    List (Name × Nat) → Locals.Layout →
      List Locals.Stmt × Locals.Layout
  | [], layout => ([], layout)
  | (name, slot) :: rest, layout =>
      if isStackSlot ctx slot then
        lowerParams ctx rest layout
      else
        let (head, nextLayout) :=
          lowerScratchParam ctx name slot layout
        let (tail, finalLayout) :=
          lowerParams ctx rest nextLayout
        (head ++ tail, finalLayout)

def lowerReturns (ctx : Ctx) :
    List (Name × Nat) → Locals.Layout →
      List Locals.Stmt × Locals.Layout
  | [], layout => ([], layout)
  | (name, slot) :: rest, layout =>
      let (head, nextLayout) :=
        if isStackSlot ctx slot then
          ([Locals.Stmt.let_ name (.lit AllocationSupport.zeroWord)],
            name :: layout)
        else
          ([Locals.Stmt.expr
              (scratchStoreExpr ctx.frameName slot
                (.lit AllocationSupport.zeroWord))],
            layout)
      let (tail, finalLayout) :=
        lowerReturns ctx rest nextLayout
      (head ++ tail, finalLayout)

/--
Parameter lowering removes exactly the scratch-resident signature names from
the canonical raw-entry layout.
-/
theorem lowerParams_layout_eq_stackOrder
    {ctx : Ctx}
    {params : List (Name × Nat)}
    {suffix : Locals.Layout}
    (hNodup : (params.map Prod.fst).Nodup)
    (hDisjoint : List.Disjoint (params.map Prod.fst) suffix) :
    (lowerParams ctx params
        ((params.map Prod.fst).reverse ++ suffix)).2 =
      MixedAllocation.stackOrder ctx.stackSlots params.reverse ++
        suffix := by
  induction params generalizing suffix with
  | nil =>
      simp [lowerParams, MixedAllocation.stackOrder,
        MixedAllocation.stackEntries]
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      have hNames :
          (name :: rest.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hNodup
      have hNameRest := (List.nodup_cons.mp hNames).1
      have hRestNodup := (List.nodup_cons.mp hNames).2
      have hNameSuffix : name ∉ suffix := by
        intro hName
        exact
          (List.disjoint_left.mp hDisjoint)
            (by simp) hName
      have hRestDisjoint :
          List.Disjoint (rest.map Prod.fst) suffix := by
        intro candidate hRestMem hSuffixMem
        exact hDisjoint (by simp [hRestMem]) hSuffixMem
      by_cases hSlot : slot ∈ ctx.stackSlots
      · have hClass : isStackSlot ctx slot = true := by
          simpa [isStackSlot] using hSlot
        have hTailDisjoint :
            List.Disjoint (rest.map Prod.fst) (name :: suffix) := by
          apply List.disjoint_cons_right.mpr
          exact
            ⟨by simpa using hNameRest, hRestDisjoint⟩
        have hTail := ih hRestNodup hTailDisjoint
        simpa [lowerParams, hClass, List.reverse_cons,
          MixedAllocation.stackOrder_append,
          MixedAllocation.stackOrder,
          MixedAllocation.stackEntries, hSlot,
          List.append_assoc] using hTail
      · have hClass : isStackSlot ctx slot = false := by
          simpa [isStackSlot] using hSlot
        have hErase :
            eraseName name
                ((rest.map Prod.fst).reverse ++ name :: suffix) =
              (rest.map Prod.fst).reverse ++ suffix := by
          apply eraseName_append_name
          · simpa using hNameRest
          · exact hNameSuffix
        have hTail := ih hRestNodup hRestDisjoint
        simpa [lowerParams, hClass, lowerScratchParam, hErase,
          List.reverse_cons, MixedAllocation.stackOrder_append,
          MixedAllocation.stackOrder,
          MixedAllocation.stackEntries, hSlot,
          List.append_assoc] using hTail

/--
Return initialization pushes exactly the stack-resident return names in the
allocator's runtime order.
-/
theorem lowerReturns_layout_eq_stackOrder
    (ctx : Ctx) (returns : List (Name × Nat))
    (layout : Locals.Layout) :
    (lowerReturns ctx returns layout).2 =
      MixedAllocation.stackOrder ctx.stackSlots returns.reverse ++
        layout := by
  induction returns generalizing layout with
  | nil =>
      simp [lowerReturns, MixedAllocation.stackOrder,
        MixedAllocation.stackEntries]
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      by_cases hSlot : slot ∈ ctx.stackSlots
      · have hClass : isStackSlot ctx slot = true := by
          simpa [isStackSlot] using hSlot
        simpa [lowerReturns, hClass, List.reverse_cons,
          MixedAllocation.stackOrder_append,
          MixedAllocation.stackOrder,
          MixedAllocation.stackEntries, hSlot,
          List.append_assoc] using ih (name :: layout)
      · have hClass : isStackSlot ctx slot = false := by
          simpa [isStackSlot] using hSlot
        simpa [lowerReturns, hClass, List.reverse_cons,
          MixedAllocation.stackOrder_append,
          MixedAllocation.stackOrder,
          MixedAllocation.stackEntries, hSlot,
          List.append_assoc] using ih layout

theorem lowerStackReturn_compileOpen
    {name : Name} {localsCtx : Locals.Ctx} :
    Locals.Block.compileOpen localsCtx
        { stmts :=
            [Locals.Stmt.let_ name
              (.lit AllocationSupport.zeroWord)] } =
      some
        ([Expressions.Stmt.code
            ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
              Locals.bindLocals 0 (name :: localsCtx.layout))],
          localsCtx.withLayout (name :: localsCtx.layout)) := by
  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
    Locals.Expr.compileCode, Locals.codeStmt]

theorem lowerScratchReturn_compileOpen
    {ctx : Ctx} {name : Name} {slot frameDepth : Nat}
    {localsCtx : Locals.Ctx} {frameOp : Structured.BasicOp}
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName localsCtx.layout =
        some frameDepth)
    (hFrameOp :
      Locals.StackOp.dup? (1 + frameDepth) = some frameOp) :
    Locals.Block.compileOpen localsCtx
        { stmts :=
            [Locals.Stmt.expr
              (scratchStoreExpr ctx.frameName slot
                (.lit AllocationSupport.zeroWord))] } =
      some
        ([Expressions.Stmt.code
            ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
              [ Structured.BasicInstr.op frameOp,
                Structured.BasicInstr.push
                  (AllocationSupport.slotOffset slot),
                Structured.BasicInstr.op .add,
                Structured.BasicInstr.op .mstore ])],
          localsCtx) := by
  have hValue :
      Locals.Expr.compileCode localsCtx 0
          (.lit AllocationSupport.zeroWord) =
        some [Structured.BasicInstr.push AllocationSupport.zeroWord] := by
    rfl
  have hStore :=
    scratchStoreExpr_compileCode
      (frameName := ctx.frameName) (slot := slot)
      (offset := 0) hValue hFrameDepth hFrameOp
  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
    Locals.codeStmt, hStore]

/--
Successful compilation of one scratch return initializer leaves the Locals
compiler context unchanged.
-/
theorem lowerScratchReturn_compileOpen_final_ctx
    {ctx : Ctx} {name : Name} {slot : Nat}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              [Locals.Stmt.expr
                (scratchStoreExpr ctx.frameName slot
                  (.lit AllocationSupport.zeroWord))] } =
        some (compiled, finalCtx)) :
    finalCtx = localsCtx := by
  cases hCode :
      Locals.Expr.compileCode localsCtx 0
        (scratchStoreExpr ctx.frameName slot
          (.lit AllocationSupport.zeroWord)) with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode] at hCompile
      exact hCompile.2.symm

theorem lowerScratchReturn_compileOpen_depth_bound
    {ctx : Ctx} {name : Name} {slot frameDepth : Nat}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName localsCtx.layout =
        some frameDepth)
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts :=
              [Locals.Stmt.expr
                (scratchStoreExpr ctx.frameName slot
                  (.lit AllocationSupport.zeroWord))] } =
        some (compiled, finalCtx)) :
    1 + frameDepth ≤ 16 := by
  cases hFrameOp :
      Locals.StackOp.dup? (1 + frameDepth) with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        scratchStoreExpr, scratchAddressExpr, exprSeqTwo,
        Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
        hFrameDepth, hFrameOp] at hCompile
  | some frameOp =>
      exact (Locals.StackOp.bounds_of_dup?_eq_some hFrameOp).2

/--
Successful compilation of the parameter lowerer installs the exact layout
computed by `lowerParams`.
-/
theorem lowerParams_compileOpen_final_layout
    {ctx : Ctx}
    {pending : List (Name × Nat)}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts := (lowerParams ctx pending localsCtx.layout).1 } =
        some (compiled, finalCtx)) :
    finalCtx.layout =
      (lowerParams ctx pending localsCtx.layout).2 := by
  induction pending generalizing localsCtx finalCtx compiled with
  | nil =>
      symm
      simpa [lowerParams, Locals.Block.compileOpen] using
        congrArg (fun output => output.map (fun result => result.2.layout))
          hCompile
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      by_cases hStack : isStackSlot ctx slot = true
      · have hTailCompile :
            Locals.Block.compileOpen localsCtx
                { stmts := (lowerParams ctx rest localsCtx.layout).1 } =
              some (compiled, finalCtx) := by
          simpa [lowerParams, hStack] using hCompile
        have hFinal := ih hTailCompile
        simpa [lowerParams, hStack] using hFinal
      · have hCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (lowerScratchParam ctx name slot localsCtx.layout).1 ++
                    (lowerParams ctx rest
                      (lowerScratchParam ctx name slot
                        localsCtx.layout).2).1 } =
            some (compiled, finalCtx) := by
          simpa [lowerParams, hStack] using hCompile
        obtain
            ⟨headCode, middle, tailCode,
              hHead, hTail, _hCode⟩ :=
          Locals.Block.compileOpen_append_components hCompile'
        have hMiddle :=
          lowerScratchParam_compileOpen_final_layout hHead
        have hTail' :
            Locals.Block.compileOpen middle
                { stmts :=
                    (lowerParams ctx rest middle.layout).1 } =
              some (tailCode, finalCtx) := by
          simpa [hMiddle] using hTail
        have hFinal := ih hTail'
        simpa [lowerParams, hStack, hMiddle] using hFinal

/--
Successful compilation of the return initializer installs the exact layout
computed by `lowerReturns`.
-/
theorem lowerReturns_compileOpen_final_layout
    {ctx : Ctx}
    {pending : List (Name × Nat)}
    {localsCtx finalCtx : Locals.Ctx}
    {compiled : List Expressions.Stmt}
    (hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts := (lowerReturns ctx pending localsCtx.layout).1 } =
        some (compiled, finalCtx)) :
    finalCtx.layout =
      (lowerReturns ctx pending localsCtx.layout).2 := by
  induction pending generalizing localsCtx finalCtx compiled with
  | nil =>
      symm
      simpa [lowerReturns, Locals.Block.compileOpen] using
        congrArg (fun output => output.map (fun result => result.2.layout))
          hCompile
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      by_cases hStack : isStackSlot ctx slot = true
      · have hCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  [Locals.Stmt.let_ name
                    (.lit AllocationSupport.zeroWord)] ++
                    (lowerReturns ctx rest
                      (name :: localsCtx.layout)).1 } =
            some (compiled, finalCtx) := by
          simpa [lowerReturns, hStack] using hCompile
        obtain
            ⟨headCode, middle, tailCode,
              hHead, hTail, _hCode⟩ :=
          Locals.Block.compileOpen_append_components hCompile'
        have hHeadShape :=
          lowerStackReturn_compileOpen
            (name := name) (localsCtx := localsCtx)
        rw [hHeadShape] at hHead
        have hMiddle :
            middle =
              localsCtx.withLayout (name :: localsCtx.layout) :=
          (congrArg Prod.snd (Option.some.inj hHead)).symm
        subst middle
        have hTail' :
            Locals.Block.compileOpen
                (localsCtx.withLayout (name :: localsCtx.layout))
                { stmts :=
                    (lowerReturns ctx rest
                      (localsCtx.withLayout
                        (name :: localsCtx.layout)).layout).1 } =
              some (tailCode, finalCtx) := by
          simpa [Locals.Ctx.withLayout] using hTail
        have hFinal := ih hTail'
        simpa [lowerReturns, hStack, Locals.Ctx.withLayout] using hFinal
      · have hCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  [Locals.Stmt.expr
                    (scratchStoreExpr ctx.frameName slot
                      (.lit AllocationSupport.zeroWord))] ++
                    (lowerReturns ctx rest localsCtx.layout).1 } =
            some (compiled, finalCtx) := by
          simpa [lowerReturns, hStack] using hCompile
        obtain
            ⟨headCode, middle, tailCode,
              hHead, hTail, _hCode⟩ :=
          Locals.Block.compileOpen_append_components hCompile'
        have hMiddle :=
          lowerScratchReturn_compileOpen_final_ctx
            (name := name) hHead
        subst middle
        have hFinal := ih hTail
        simpa [lowerReturns, hStack] using hFinal

def lowerReturnExprs (ctx : Ctx) (state : State)
    (names : List Name) : Option (Locals.ExprSeq names.length) :=
  lowerExprSeq ctx state (Functions.Lower.returnExprs names)

def stackAssignTopCode? (layout : Locals.Layout)
    (remaining : Nat) (name : Name) : Option Structured.Code := do
  let depth ← Locals.Layout.lookupDepth? name layout
  let swap ← Locals.StackOp.swap? (remaining + depth)
  some
    [ Structured.BasicInstr.op swap,
      Structured.BasicInstr.op .pop ]

def scratchAssignTopCode? (ctx : Ctx) (state : State)
    (remaining slot : Nat) : Option Structured.Code := do
  let frameDepth ← frameDepth? ctx state
  AllocationSupport.storeTopSlotCode?
    (remaining + frameDepth + 1) slot

def lowerCallTargetsCode? (ctx : Ctx) (state : State) :
    List Name → Nat → Option Structured.Code
  | [], _valuesAbove => some []
  | name :: rest, valuesAbove => do
      let slot ←
        AllocationSupport.lookupSlot? name state.allocation.env
      let head ←
        if isStackSlot ctx slot then
          stackAssignTopCode? state.layout (valuesAbove - 1) name
        else
          scratchAssignTopCode? ctx state (valuesAbove - 1) slot
      let tail ←
        lowerCallTargetsCode? ctx state rest (valuesAbove - 1)
      some (head ++ tail)

def scopeRoot : ScopeId → ScopeId
  | .main => .main
  | .function name => .function name
  | .lexical parent _ => scopeRoot parent

def scopedStates
    (recipe : AllocationSupport.AllocationRecipe) :
    List AllocationSupport.ScopedAllocation :=
  { scope := .main, state := recipe.main } ::
    recipe.functions ++ recipe.lexicalScopes

def scratchBindingsForRoot
    (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (root : ScopeId) : List (Name × Nat) :=
  ((scopedStates recipe).filterMap fun entry =>
      if scopeRoot entry.scope = root then
        some
          (entry.state.env.filter fun binding =>
            binding.2 ∉ stackSlots)
      else
        none).flatten.eraseDups

private theorem mem_eraseDups_iff
    {α : Type} [BEq α] [LawfulBEq α]
    {item : α} {items : List α} :
    item ∈ items.eraseDups ↔ item ∈ items := by
  match items with
  | [] =>
      simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff]
      simp only [List.mem_filter, Bool.not_eq_true, beq_iff_eq]
      constructor
      · intro h
        rcases h with hEq | ⟨hMem, _⟩
        · exact Or.inl hEq
        · exact Or.inr hMem
      · intro h
        rcases h with hEq | hMem
        · exact Or.inl hEq
        · by_cases hEq : item = head
          · exact Or.inl hEq
          · exact Or.inr ⟨hMem, by simp [hEq]⟩
termination_by items.length
decreasing_by
  exact
    Nat.lt_succ_of_le
      (List.length_filter_le (fun binding => !binding == head) tail)

theorem mem_scratchBindingsForRoot
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet} {root : ScopeId}
    {entry : AllocationSupport.ScopedAllocation}
    {name : Name} {slot : Nat}
    (hEntry : entry ∈ scopedStates recipe)
    (hRoot : scopeRoot entry.scope = root)
    (hBinding : (name, slot) ∈ entry.state.env)
    (hScratch : slot ∉ stackSlots) :
    (name, slot) ∈ scratchBindingsForRoot recipe stackSlots root := by
  unfold scratchBindingsForRoot
  rw [mem_eraseDups_iff]
  simp only [List.mem_flatten]
  refine
    ⟨entry.state.env.filter fun binding => binding.2 ∉ stackSlots,
      ?_, ?_⟩
  · exact
      List.mem_filterMap.mpr
        ⟨entry, hEntry, by simp [hRoot]⟩
  · exact List.mem_filter.mpr ⟨hBinding, by simpa using hScratch⟩

def rootNeedsFrame (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (root : ScopeId) : Bool :=
  !(scratchBindingsForRoot recipe stackSlots root).isEmpty

theorem slot_mem_of_function_rootNeedsFrame_eq_false
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {entry : AllocationSupport.ScopedAllocation}
    {functionName name : Name} {slot : Nat}
    (hEntry : entry ∈ recipe.functions)
    (hScope : entry.scope = .function functionName)
    (hBinding : (name, slot) ∈ entry.state.env)
    (hNoFrame :
      rootNeedsFrame recipe stackSlots (.function functionName) = false) :
    slot ∈ stackSlots := by
  by_contra hScratch
  have hMem :
      (name, slot) ∈
        scratchBindingsForRoot recipe stackSlots
          (.function functionName) := by
    apply mem_scratchBindingsForRoot
    · simp only [scopedStates, List.mem_cons, List.mem_append]
      exact Or.inl (Or.inr hEntry)
    · rw [hScope]
      rfl
    · exact hBinding
    · exact hScratch
  have hEmpty :
      scratchBindingsForRoot recipe stackSlots (.function functionName) = [] := by
    simpa [rootNeedsFrame] using hNoFrame
  rw [hEmpty] at hMem
  exact False.elim (by simpa using hMem)

def functionNeedsFrame (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (name : Name) : Bool :=
  rootNeedsFrame recipe stackSlots (.function name)

def frameFunctions (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) : List Name :=
  recipe.functionSlots.filterMap fun fn =>
    if functionNeedsFrame recipe stackSlots fn.name then
      some fn.name
    else
      none

mutual
  def lowerBlockOpen (ctx : Ctx) (returns : List Name)
      (state : State) (block : Block) :
      Option (Locals.Block × State) :=
    match block with
    | ⟨stmts⟩ => do
        let (lowered, final) ← lowerStmtList ctx returns state stmts
        some ({ stmts := lowered }, final)

  def lowerBlockScoped (ctx : Ctx) (returns : List Name)
      (state : State) (block : Block) :
      Option (Locals.Block × State) := do
    let (lowered, final) ← lowerBlockOpen ctx returns state block
    some
      (lowered,
        { allocation :=
            { env := state.allocation.env
              nextSlot := final.allocation.nextSlot }
          layout := state.layout })

  def lowerStmtList (ctx : Ctx) (returns : List Name)
      (state : State) :
      List Stmt → Option (List Locals.Stmt × State)
    | [] => some ([], state)
    | stmt :: rest => do
        let (head, next) ← lowerStmt ctx returns state stmt
        let (tail, final) ← lowerStmtList ctx returns next rest
        some (head ++ tail, final)

  def lowerCases (ctx : Ctx) (returns : List Name)
      (state : State) :
      List (Word × Block) →
        Option (List (Word × Locals.Block) × State)
    | [] => some ([], state)
    | (value, body) :: rest => do
        let (loweredBody, afterBody) ←
          lowerBlockScoped ctx returns state body
        let (loweredRest, final) ←
          lowerCases ctx returns afterBody rest
        some ((value, loweredBody) :: loweredRest, final)

  def lowerDefault (ctx : Ctx) (returns : List Name)
      (state : State) :
      Option Block → Option (Option Locals.Block × State)
    | none => some (none, state)
    | some body => do
        let (lowered, final) ← lowerBlockScoped ctx returns state body
        some (some lowered, final)

  def lowerStmt (ctx : Ctx) (returns : List Name)
      (state : State) :
      Stmt → Option (List Locals.Stmt × State)
    | .expr expr => do
        let lowered ← lowerExpr ctx state expr
        some ([.expr lowered], state)
    | .let_ name value => do
        let lowered ← lowerExpr ctx state value
        let (slot, allocation) :=
          AllocationSupport.allocateName name state.allocation
        if isStackSlot ctx slot then
          some
            ([.let_ name lowered],
              { allocation := allocation
                layout := name :: state.layout })
        else
          if ctx.frameName ∈ state.layout then
            some
              ([.expr (scratchStoreExpr ctx.frameName slot lowered)],
                { state with allocation := allocation })
          else
            none
    | .assign name value => do
        let slot ←
          AllocationSupport.lookupSlot? name state.allocation.env
        let lowered ← lowerExpr ctx state value
        if isStackSlot ctx slot then
          some ([.assign name lowered], state)
        else
          if ctx.frameName ∈ state.layout then
            some
              ([.expr (scratchStoreExpr ctx.frameName slot lowered)],
                state)
          else
            none
    | .block body => do
        let (lowered, final) ←
          lowerBlockScoped ctx returns state body
        some ([.block lowered], final)
    | .if_ cond body => do
        let loweredCond ← lowerExpr ctx state cond
        let (loweredBody, final) ←
          lowerBlockScoped ctx returns state body
        some ([.if_ loweredCond loweredBody], final)
    | .switch scrutinee cases defaultBody => do
        let loweredScrutinee ← lowerExpr ctx state scrutinee
        let (loweredCases, afterCases) ←
          lowerCases ctx returns state cases
        let (loweredDefault, final) ←
          lowerDefault ctx returns afterCases defaultBody
        some
          ([.switch loweredScrutinee loweredCases loweredDefault], final)
    | .for_ init cond post body => do
        let (loweredInit, loopState) ←
          lowerBlockOpen ctx returns state init
        let loweredCond ← lowerExpr ctx loopState cond
        let (loweredPost, afterPost) ←
          lowerBlockScoped ctx returns loopState post
        let (loweredBody, afterBody) ←
          lowerBlockScoped ctx returns afterPost body
        some
          ([.for_ loweredInit loweredCond loweredPost loweredBody],
            { allocation :=
                { env := state.allocation.env
                  nextSlot := afterBody.allocation.nextSlot }
              layout := state.layout })
    | .brk => some ([.brk], state)
    | .cont => some ([.cont], state)
    | .leave => do
        let values ← lowerReturnExprs ctx state returns
        some ([.exprs values, .leave], state)
    | .call targets functionName args => do
        let fn ← AllocationSupport.lookupFun? functionName ctx.functions
        if args.length = fn.params.length then pure () else none
        if targets.length = fn.returns.length then pure () else none
        if targets.Nodup then pure () else none
        let loweredArgs ← lowerExprList ctx state args
        let usesFrame := functionName ∈ ctx.frameFunctions
        let callArgs ←
          if usesFrame then do
            let frameConfig ← ctx.frameConfig?
            some (frameExpr frameConfig :: loweredArgs)
          else
            some loweredArgs
        let stores ←
          lowerCallTargetsCode? ctx state targets.reverse targets.length
        let release ←
          if usesFrame then do
            let frameConfig ← ctx.frameConfig?
            some
              [ .expr
                  (Locals.Expr.code (results := 0)
                    (AllocationSupport.scratchFrameReleaseCode frameConfig)) ]
          else
            some []
        some
          ([ .exprs (exprSeqOfList callArgs),
             .call functionName,
             .expr (Locals.Expr.code (results := 0) stores) ] ++ release,
           state)
    | .terminal kind => some ([.terminal kind], state)
    | .terminalArgs kind args => do
        let lowered ← lowerExprSeq ctx state args
        some ([.terminalArgs kind lowered], state)
end

/--
Successful lowering of a source `if` exposes only the adjacent expression and
scoped-block lowerers owned by this pass.
-/
theorem lowerStmt_if_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {cond : Expr 1} {body : Block}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state (.if_ cond body) =
        some (loweredStmts, final)) :
    ∃ loweredCond loweredBody,
      lowerExpr ctx state cond = some loweredCond ∧
      lowerBlockScoped ctx returns state body =
        some (loweredBody, final) ∧
      loweredStmts = [.if_ loweredCond loweredBody] := by
  cases hCond : lowerExpr ctx state cond with
  | none =>
      simp [lowerStmt, hCond] at hLower
  | some loweredCond =>
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerStmt, hCond, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, bodyFinal⟩
          simp [lowerStmt, hCond, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨loweredCond, loweredBody, rfl, rfl, rfl⟩

/--
Successful lowering of a source `switch` exposes only the adjacent expression,
case-list, and default lowerers owned by this pass.
-/
theorem lowerStmt_switch_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {scrutinee : Expr 1}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, final)) :
    ∃ loweredScrutinee loweredCases afterCases loweredDefault,
      lowerExpr ctx state scrutinee = some loweredScrutinee ∧
      lowerCases ctx returns state cases =
        some (loweredCases, afterCases) ∧
      lowerDefault ctx returns afterCases defaultBody =
        some (loweredDefault, final) ∧
      loweredStmts =
        [.switch loweredScrutinee loweredCases loweredDefault] := by
  cases hScrutinee : lowerExpr ctx state scrutinee with
  | none =>
      simp [lowerStmt, hScrutinee] at hLower
  | some loweredScrutinee =>
      cases hCases : lowerCases ctx returns state cases with
      | none =>
          simp [lowerStmt, hScrutinee, hCases] at hLower
      | some casesResult =>
          rcases casesResult with ⟨loweredCases, afterCases⟩
          cases hDefault :
              lowerDefault ctx returns afterCases defaultBody with
          | none =>
              simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
          | some defaultResult =>
              rcases defaultResult with ⟨loweredDefault, defaultFinal⟩
              simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                ⟨loweredScrutinee, loweredCases, afterCases,
                  loweredDefault, rfl, rfl, hDefault, rfl⟩

/--
Successful lowering of a source `for` exposes the adjacent initializer,
condition, post, and body lowerers plus the common restored outer state.
-/
theorem lowerStmt_for_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {init : Block} {cond : Expr 1} {post body : Block}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state (.for_ init cond post body) =
        some (loweredStmts, final)) :
    ∃ loweredInit loopState loweredCond loweredPost afterPost
        loweredBody afterBody,
      lowerBlockOpen ctx returns state init =
        some (loweredInit, loopState) ∧
      lowerExpr ctx loopState cond = some loweredCond ∧
      lowerBlockScoped ctx returns loopState post =
        some (loweredPost, afterPost) ∧
      lowerBlockScoped ctx returns afterPost body =
        some (loweredBody, afterBody) ∧
      loweredStmts =
        [.for_ loweredInit loweredCond loweredPost loweredBody] ∧
      final =
        { allocation :=
            { env := state.allocation.env
              nextSlot := afterBody.allocation.nextSlot }
          layout := state.layout } := by
  cases hInit : lowerBlockOpen ctx returns state init with
  | none =>
      simp [lowerStmt, hInit] at hLower
  | some initResult =>
      rcases initResult with ⟨loweredInit, loopState⟩
      cases hCond : lowerExpr ctx loopState cond with
      | none =>
          simp [lowerStmt, hInit, hCond] at hLower
      | some loweredCond =>
          cases hPost : lowerBlockScoped ctx returns loopState post with
          | none =>
              simp [lowerStmt, hInit, hCond, hPost] at hLower
          | some postResult =>
              rcases postResult with ⟨loweredPost, afterPost⟩
              cases hBody :
                  lowerBlockScoped ctx returns afterPost body with
              | none =>
                  simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
              | some bodyResult =>
                  rcases bodyResult with ⟨loweredBody, afterBody⟩
                  simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact
                    ⟨loweredInit, loopState, loweredCond,
                      loweredPost, afterPost, loweredBody, afterBody,
                      rfl, hCond, hPost, hBody, rfl, rfl⟩

/--
Successful call lowering exposes the source function lookup, arity checks,
argument lowering, return stores, and optional scratch-frame protocol.
-/
theorem lowerStmt_call_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {targets : List Name} {functionName : Name}
    {args : List (Expr 1)}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state (.call targets functionName args) =
        some (loweredStmts, final)) :
    ∃ fn loweredArgs callArgs stores release,
      AllocationSupport.lookupFun? functionName ctx.functions = some fn ∧
      args.length = fn.params.length ∧
      targets.length = fn.returns.length ∧
      targets.Nodup ∧
      lowerExprList ctx state args = some loweredArgs ∧
      (if functionName ∈ ctx.frameFunctions then do
          let frameConfig ← ctx.frameConfig?
          some (frameExpr frameConfig :: loweredArgs)
        else
          some loweredArgs) =
        some callArgs ∧
      lowerCallTargetsCode? ctx state targets.reverse targets.length =
        some stores ∧
      (if functionName ∈ ctx.frameFunctions then do
          let frameConfig ← ctx.frameConfig?
          some
            [ .expr
                (Locals.Expr.code (results := 0)
                  (AllocationSupport.scratchFrameReleaseCode frameConfig)) ]
        else
          some []) =
        some release ∧
      loweredStmts =
        ([ .exprs (exprSeqOfList callArgs),
           .call functionName,
           .expr (Locals.Expr.code (results := 0) stores) ] ++ release) ∧
      final = state := by
  cases hFind :
      AllocationSupport.lookupFun? functionName ctx.functions with
  | none =>
      simp [lowerStmt, hFind] at hLower
  | some fn =>
      by_cases hArgsLength : args.length = fn.params.length
      · by_cases hTargetsLength : targets.length = fn.returns.length
        · by_cases hTargets : targets.Nodup
          · cases hArgs : lowerExprList ctx state args with
            | none =>
                simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                  hTargets, hArgs] at hLower
            | some loweredArgs =>
                by_cases hFrame :
                    functionName ∈ ctx.frameFunctions
                · cases hConfig : ctx.frameConfig? with
                  | none =>
                      simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                        hTargets, hArgs, hFrame, hConfig] at hLower
                  | some frameConfig =>
                      cases hStores :
                          lowerCallTargetsCode? ctx state targets.reverse
                            fn.returns.length with
                      | none =>
                          simp [lowerStmt, hFind, hArgsLength,
                            hTargetsLength, hTargets, hArgs, hFrame,
                            hConfig, hStores] at hLower
                      | some stores =>
                          simp [lowerStmt, hFind, hArgsLength,
                            hTargetsLength, hTargets, hArgs, hFrame,
                            hConfig, hStores] at hLower
                          rcases hLower with ⟨rfl, rfl⟩
                          exact
                            ⟨fn, loweredArgs,
                              frameExpr frameConfig :: loweredArgs, stores,
                              [ .expr
                                  (Locals.Expr.code (results := 0)
                                    (AllocationSupport.scratchFrameReleaseCode
                                      frameConfig)) ],
                              rfl, hArgsLength, hTargetsLength, hTargets,
                              rfl, by simp [hFrame],
                              by simpa [hTargetsLength] using hStores,
                              by simp [hFrame], rfl, rfl⟩
                · cases hStores :
                      lowerCallTargetsCode? ctx state targets.reverse
                        fn.returns.length with
                  | none =>
                      simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                        hTargets, hArgs, hFrame, hStores] at hLower
                  | some stores =>
                      simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                        hTargets, hArgs, hFrame, hStores] at hLower
                      rcases hLower with ⟨rfl, rfl⟩
                      exact
                        ⟨fn, loweredArgs, loweredArgs, stores, [],
                          rfl, hArgsLength, hTargetsLength, hTargets,
                          rfl, by simp [hFrame],
                          by simpa [hTargetsLength] using hStores,
                          by simp [hFrame], rfl, rfl⟩
          · simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
              hTargets] at hLower
        · simp [lowerStmt, hFind, hArgsLength, hTargetsLength] at hLower
      · simp [lowerStmt, hFind, hArgsLength] at hLower

/--
Case/default lowering preserves the absence of a selected source branch.
-/
theorem lowerSwitch_select_none
    {ctx : Ctx} {returns : List Name}
    {state afterCases final : State}
    {value : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {loweredCases : List (Word × Locals.Block)}
    {loweredDefault : Option Locals.Block}
    (hCases :
      lowerCases ctx returns state cases =
        some (loweredCases, afterCases))
    (hDefault :
      lowerDefault ctx returns afterCases defaultBody =
        some (loweredDefault, final))
    (hSelect :
      Source.Switch.select value cases defaultBody = none) :
    Locals.Source.Switch.select value loweredCases loweredDefault = none := by
  induction cases generalizing state afterCases loweredCases with
  | nil =>
      simp [lowerCases] at hCases
      rcases hCases with ⟨rfl, rfl⟩
      cases defaultBody with
      | none =>
          simp [lowerDefault] at hDefault
          rcases hDefault with ⟨rfl, rfl⟩
          rfl
      | some body =>
          simp [Source.Switch.select] at hSelect
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerCases, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, afterBody⟩
          cases hRest :
              lowerCases ctx returns afterBody rest with
          | none =>
              simp [lowerCases, hBody, hRest] at hCases
          | some restResult =>
              rcases restResult with ⟨loweredRest, restFinal⟩
              simp [lowerCases, hBody, hRest] at hCases
              rcases hCases with ⟨rfl, rfl⟩
              by_cases hMatch : caseValue = value
              · simp [Source.Switch.select, hMatch] at hSelect
              · have hTailSelect :
                    Source.Switch.select
                        value rest defaultBody =
                      none := by
                  simpa [Source.Switch.select, hMatch] using hSelect
                have hLoweredTail :=
                  ih hRest hDefault hTailSelect
                simpa [Locals.Source.Switch.select, hMatch] using
                  hLoweredTail

/--
Case/default lowering preserves a selected source branch and exposes the
ordinary scoped-body lowering that produced its Locals counterpart.

Earlier unselected cases may advance the fresh-slot cursor, but scoped lowering
preserves the incoming allocation environment and concrete layout. Those are
the only lowering-state components needed to transport a statement-boundary
activation invariant to the selected body.
-/
theorem lowerSwitch_select_some
    {ctx : Ctx} {returns : List Name}
    {state afterCases final : State}
    {value : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {selected : Block}
    {loweredCases : List (Word × Locals.Block)}
    {loweredDefault : Option Locals.Block}
    (hCases :
      lowerCases ctx returns state cases =
        some (loweredCases, afterCases))
    (hDefault :
      lowerDefault ctx returns afterCases defaultBody =
        some (loweredDefault, final))
    (hSelect :
      Source.Switch.select value cases defaultBody = some selected) :
    ∃ selectedLowered selectedStart selectedFinal,
      Locals.Source.Switch.select value loweredCases loweredDefault =
          some selectedLowered ∧
        lowerBlockScoped ctx returns selectedStart selected =
          some (selectedLowered, selectedFinal) ∧
        selectedStart.allocation.env = state.allocation.env ∧
        selectedStart.layout = state.layout := by
  induction cases generalizing state afterCases loweredCases with
  | nil =>
      simp [lowerCases] at hCases
      rcases hCases with ⟨rfl, rfl⟩
      cases defaultBody with
      | none =>
          simp [Source.Switch.select] at hSelect
      | some body =>
          simp [Source.Switch.select] at hSelect
          subst selected
          cases hBody :
              lowerBlockScoped ctx returns state body with
          | none =>
              simp [lowerDefault, hBody] at hDefault
          | some bodyResult =>
              rcases bodyResult with ⟨loweredBody, bodyFinal⟩
              simp [lowerDefault, hBody] at hDefault
              rcases hDefault with ⟨rfl, rfl⟩
              exact
                ⟨loweredBody, state, bodyFinal,
                  rfl, hBody, rfl, rfl⟩
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerCases, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, afterBody⟩
          cases hRest :
              lowerCases ctx returns afterBody rest with
          | none =>
              simp [lowerCases, hBody, hRest] at hCases
          | some restResult =>
              rcases restResult with ⟨loweredRest, restFinal⟩
              simp [lowerCases, hBody, hRest] at hCases
              rcases hCases with ⟨rfl, rfl⟩
              by_cases hMatch : caseValue = value
              · simp [Source.Switch.select, hMatch] at hSelect
                subst selected
                exact
                  ⟨loweredBody, state, afterBody,
                    by simp [Locals.Source.Switch.select, hMatch],
                    hBody, rfl, rfl⟩
              · have hTailSelect :
                    Source.Switch.select value rest defaultBody =
                      some selected := by
                  simpa [Source.Switch.select, hMatch] using hSelect
                obtain
                    ⟨selectedLowered, selectedStart, selectedFinal,
                      hLoweredSelect, hSelectedBody,
                      hSelectedEnv, hSelectedLayout⟩ :=
                  ih hRest hDefault hTailSelect
                have hBodyShape :
                    afterBody.allocation.env =
                        state.allocation.env ∧
                      afterBody.layout = state.layout := by
                  unfold lowerBlockScoped at hBody
                  cases hOpen :
                      lowerBlockOpen ctx returns state body with
                  | none =>
                      simp [hOpen] at hBody
                  | some openResult =>
                      rcases openResult with
                        ⟨loweredOpen, openFinal⟩
                      simp [hOpen] at hBody
                      rcases hBody with ⟨rfl, rfl⟩
                      exact ⟨rfl, rfl⟩
                exact
                  ⟨selectedLowered, selectedStart, selectedFinal,
                    by
                      simpa [Locals.Source.Switch.select, hMatch] using
                        hLoweredSelect,
                    hSelectedBody,
                    hSelectedEnv.trans hBodyShape.1,
                    hSelectedLayout.trans hBodyShape.2⟩

/--
The part of lowering-state evolution visible at an open source-block boundary.

New stack locals form a removable prefix of the incoming Locals layout, while
lookups for names already in the source scope retain their allocation slots.
-/
def StateExtends
    (live : List Name) (before after : State) : Prop :=
  ∃ dropped : List Name,
    after.layout = dropped ++ before.layout ∧
      (∀ name, name ∈ dropped → name ∉ live) ∧
      ∀ name,
        name ∈ live →
        AllocationSupport.lookupSlot? name after.allocation.env =
          AllocationSupport.lookupSlot? name before.allocation.env

namespace StateExtends

theorem of_shape
    {live : List Name} {before after : State}
    (hLayout : after.layout = before.layout)
    (hSlots : after.allocation.env = before.allocation.env) :
    StateExtends live before after := by
  refine ⟨[], by simpa using hLayout, ?_, ?_⟩
  · simp
  · intro name _hLive
    rw [hSlots]

theorem trans
    {beforeLive afterLive : List Name}
    {before middle after : State}
    (hHead : StateExtends beforeLive before middle)
    (hTail : StateExtends afterLive middle after)
    (hSubset : ∀ name, name ∈ beforeLive → name ∈ afterLive) :
    StateExtends beforeLive before after := by
  rcases hHead with
    ⟨headDropped, hHeadLayout, hHeadFresh, hHeadSlots⟩
  rcases hTail with
    ⟨tailDropped, hTailLayout, hTailFresh, hTailSlots⟩
  refine
    ⟨tailDropped ++ headDropped, ?_, ?_, ?_⟩
  · rw [hTailLayout, hHeadLayout, List.append_assoc]
  · intro name hDropped hLive
    simp only [List.mem_append] at hDropped
    cases hDropped with
    | inl hTailDropped =>
        exact hTailFresh name hTailDropped (hSubset name hLive)
    | inr hHeadDropped =>
        exact hHeadFresh name hHeadDropped hLive
  · intro name hLive
    exact (hTailSlots name (hSubset name hLive)).trans
      (hHeadSlots name hLive)

end StateExtends

theorem lowerBlockScoped_state_shape
    {ctx : Ctx} {returns : List Name}
    {state final : State} {block : Block}
    {lowered : Locals.Block}
    (hLower :
      lowerBlockScoped ctx returns state block =
        some (lowered, final)) :
    final.allocation.env = state.allocation.env ∧
      final.layout = state.layout := by
  unfold lowerBlockScoped at hLower
  cases hOpen : lowerBlockOpen ctx returns state block with
  | none =>
      simp [hOpen] at hLower
  | some result =>
      rcases result with ⟨body, bodyFinal⟩
      simp [hOpen] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/--
Successful scoped lowering exposes its ordinary open-block lowering state.
The scoped result restores the incoming environment and layout while retaining
only the fresh-slot cursor reached by the open body.
-/
theorem lowerBlockScoped_components
    {ctx : Ctx} {returns : List Name}
    {state final : State} {block : Block}
    {lowered : Locals.Block}
    (hLower :
      lowerBlockScoped ctx returns state block =
        some (lowered, final)) :
    ∃ openFinal,
      lowerBlockOpen ctx returns state block =
        some (lowered, openFinal) ∧
      final.allocation.env = state.allocation.env ∧
      final.allocation.nextSlot = openFinal.allocation.nextSlot ∧
      final.layout = state.layout := by
  unfold lowerBlockScoped at hLower
  cases hOpen : lowerBlockOpen ctx returns state block with
  | none =>
      simp [hOpen] at hLower
  | some result =>
      rcases result with ⟨body, bodyFinal⟩
      simp [hOpen] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨bodyFinal, rfl, rfl, rfl, rfl⟩

theorem lowerCases_state_shape
    {ctx : Ctx} {returns : List Name} :
    ∀ {state final : State}
      {cases : List (Word × Block)}
      {lowered : List (Word × Locals.Block)},
      lowerCases ctx returns state cases = some (lowered, final) →
        final.allocation.env = state.allocation.env ∧
          final.layout = state.layout := by
  intro state final cases lowered hLower
  induction cases generalizing state final lowered with
  | nil =>
      simp [lowerCases] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerCases, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, afterBody⟩
          cases hRest :
              lowerCases ctx returns afterBody rest with
          | none =>
              simp [lowerCases, hBody, hRest] at hLower
          | some restResult =>
              rcases restResult with ⟨loweredRest, restFinal⟩
              simp [lowerCases, hBody, hRest] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hBodyShape :=
                lowerBlockScoped_state_shape hBody
              have hRestShape := ih hRest
              exact
                ⟨hRestShape.1.trans hBodyShape.1,
                  hRestShape.2.trans hBodyShape.2⟩

theorem lowerDefault_state_shape
    {ctx : Ctx} {returns : List Name}
    {state final : State} {body : Option Block}
    {lowered : Option Locals.Block}
    (hLower :
      lowerDefault ctx returns state body =
        some (lowered, final)) :
    final.allocation.env = state.allocation.env ∧
      final.layout = state.layout := by
  cases body with
  | none =>
      simp [lowerDefault] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | some body =>
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerDefault, hBody] at hLower
      | some result =>
          rcases result with ⟨loweredBody, bodyFinal⟩
          simp [lowerDefault, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact lowerBlockScoped_state_shape hBody

theorem mem_stmt_outEnv
    {live : List Name} {stmt : Stmt} {name : Name}
    (hLive : name ∈ live) :
    name ∈ Scope.Stmt.outEnv live stmt := by
  cases stmt <;> simp [Scope.Stmt.outEnv, hLive]

/--
Successful lowering of one well-scoped statement preserves incoming allocation
slots and extends the Locals layout only by stack declarations introduced by
that statement.
-/
theorem lowerStmt_stateExtends
    {ctx : Ctx} {returns live : List Name}
    {state final : State} {stmt : Stmt}
    {lowered : List Locals.Stmt}
    (hScoped : Scope.Stmt.Scoped live stmt)
    (hLower :
      lowerStmt ctx returns state stmt =
        some (lowered, final)) :
    StateExtends live state final := by
  cases stmt with
  | expr expr =>
      cases hExpr : lowerExpr ctx state expr with
      | none =>
          simp [lowerStmt, hExpr] at hLower
      | some loweredExpr =>
          simp [lowerStmt, hExpr] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact StateExtends.of_shape rfl rfl
  | let_ name value =>
      have hFresh : name ∉ live := hScoped.1
      cases hValue : lowerExpr ctx state value with
      | none =>
          simp [lowerStmt, hValue] at hLower
      | some loweredValue =>
          by_cases hStack :
              isStackSlot ctx state.allocation.nextSlot = true
          · simp [lowerStmt, hValue, AllocationSupport.allocateName,
              hStack] at hLower
            rcases hLower with ⟨rfl, rfl⟩
            refine ⟨[name], rfl, ?_, ?_⟩
            · intro declared hDeclared
              simp only [List.mem_singleton] at hDeclared
              subst declared
              exact hFresh
            · intro existing hExisting
              have hNe : name ≠ existing := by
                intro hEq
                subst existing
                exact hFresh hExisting
              simp [AllocationSupport.lookupSlot?, hNe]
          · have hStackFalse :
                isStackSlot ctx state.allocation.nextSlot = false :=
              Bool.eq_false_of_not_eq_true hStack
            by_cases hFrame : ctx.frameName ∈ state.layout
            · simp [lowerStmt, hValue, AllocationSupport.allocateName,
                hStackFalse, hFrame] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              refine ⟨[], rfl, ?_, ?_⟩
              · simp
              · intro existing hExisting
                have hNe : name ≠ existing := by
                  intro hEq
                  subst existing
                  exact hFresh hExisting
                simp [AllocationSupport.lookupSlot?, hNe]
            · simp [lowerStmt, hValue, AllocationSupport.allocateName,
                hStackFalse, hFrame] at hLower
  | assign name value =>
      cases hSlot :
          AllocationSupport.lookupSlot?
            name state.allocation.env with
      | none =>
          simp [lowerStmt, hSlot] at hLower
      | some slot =>
          cases hValue : lowerExpr ctx state value with
          | none =>
              simp [lowerStmt, hSlot, hValue] at hLower
          | some loweredValue =>
              by_cases hStack : isStackSlot ctx slot = true
              · simp [lowerStmt, hSlot, hValue, hStack] at hLower
                rcases hLower with ⟨rfl, rfl⟩
                exact StateExtends.of_shape rfl rfl
              · have hStackFalse :
                    isStackSlot ctx slot = false :=
                  Bool.eq_false_of_not_eq_true hStack
                by_cases hFrame : ctx.frameName ∈ state.layout
                · simp [lowerStmt, hSlot, hValue, hStackFalse, hFrame]
                    at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact StateExtends.of_shape rfl rfl
                · simp [lowerStmt, hSlot, hValue, hStackFalse, hFrame]
                    at hLower
  | block body =>
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerStmt, hBody] at hLower
      | some result =>
          rcases result with ⟨loweredBody, bodyFinal⟩
          simp [lowerStmt, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          have hShape := lowerBlockScoped_state_shape hBody
          exact StateExtends.of_shape hShape.2 hShape.1
  | if_ cond body =>
      cases hCond : lowerExpr ctx state cond with
      | none =>
          simp [lowerStmt, hCond] at hLower
      | some loweredCond =>
          cases hBody :
              lowerBlockScoped ctx returns state body with
          | none =>
              simp [lowerStmt, hCond, hBody] at hLower
          | some result =>
              rcases result with ⟨loweredBody, bodyFinal⟩
              simp [lowerStmt, hCond, hBody] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hShape := lowerBlockScoped_state_shape hBody
              exact StateExtends.of_shape hShape.2 hShape.1
  | switch scrutinee cases defaultBody =>
      cases hScrutinee : lowerExpr ctx state scrutinee with
      | none =>
          simp [lowerStmt, hScrutinee] at hLower
      | some loweredScrutinee =>
          cases hCases :
              lowerCases ctx returns state cases with
          | none =>
              simp [lowerStmt, hScrutinee, hCases] at hLower
          | some casesResult =>
              rcases casesResult with ⟨loweredCases, afterCases⟩
              cases hDefault :
                  lowerDefault ctx returns afterCases defaultBody with
              | none =>
                  simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
              | some defaultResult =>
                  rcases defaultResult with
                    ⟨loweredDefault, defaultFinal⟩
                  simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  have hCasesShape := lowerCases_state_shape hCases
                  have hDefaultShape :=
                    lowerDefault_state_shape hDefault
                  exact
                    StateExtends.of_shape
                      (hDefaultShape.2.trans hCasesShape.2)
                      (hDefaultShape.1.trans hCasesShape.1)
  | for_ init cond post body =>
      cases hInit :
          lowerBlockOpen ctx returns state init with
      | none =>
          simp [lowerStmt, hInit] at hLower
      | some initResult =>
          rcases initResult with ⟨loweredInit, loopState⟩
          cases hCond : lowerExpr ctx loopState cond with
          | none =>
              simp [lowerStmt, hInit, hCond] at hLower
          | some loweredCond =>
              cases hPost :
                  lowerBlockScoped ctx returns loopState post with
              | none =>
                  simp [lowerStmt, hInit, hCond, hPost] at hLower
              | some postResult =>
                  rcases postResult with ⟨loweredPost, afterPost⟩
                  cases hBody :
                      lowerBlockScoped ctx returns afterPost body with
                  | none =>
                      simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
                  | some bodyResult =>
                      rcases bodyResult with ⟨loweredBody, afterBody⟩
                      simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
                      rcases hLower with ⟨rfl, rfl⟩
                      exact StateExtends.of_shape rfl rfl
  | brk =>
      simp [lowerStmt] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | cont =>
      simp [lowerStmt] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | leave =>
      cases hValues :
          lowerReturnExprs ctx state returns with
      | none =>
          simp [lowerStmt, hValues] at hLower
      | some values =>
          simp [lowerStmt, hValues] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact StateExtends.of_shape rfl rfl
  | call targets functionName args =>
      cases hFunction :
          AllocationSupport.lookupFun?
            functionName ctx.functions with
      | none =>
          simp [lowerStmt, hFunction] at hLower
      | some fn =>
          by_cases hArgsLength : args.length = fn.params.length
          · by_cases hTargetsLength :
                targets.length = fn.returns.length
            · by_cases hTargetsNodup : targets.Nodup
              · cases hArgs :
                    lowerExprList ctx state args with
                | none =>
                    simp [lowerStmt, hFunction, hArgsLength,
                      hTargetsLength, hTargetsNodup, hArgs] at hLower
                | some loweredArgs =>
                    by_cases hUsesFrame :
                        functionName ∈ ctx.frameFunctions
                    · cases hConfig : ctx.frameConfig? with
                      | none =>
                          simp [lowerStmt, hFunction, hArgsLength,
                            hTargetsLength, hTargetsNodup, hArgs,
                            hUsesFrame, hConfig] at hLower
                      | some frameConfig =>
                          cases hStores :
                              lowerCallTargetsCode? ctx state
                                targets.reverse targets.length with
                          | none =>
                              have hStores' :
                                  lowerCallTargetsCode? ctx state
                                      targets.reverse fn.returns.length =
                                    none := by
                                simpa [hTargetsLength] using hStores
                              simp [lowerStmt, hFunction, hArgsLength,
                                hTargetsLength, hTargetsNodup, hArgs,
                                hUsesFrame, hConfig, hStores'] at hLower
                          | some stores =>
                              have hStores' :
                                  lowerCallTargetsCode? ctx state
                                      targets.reverse fn.returns.length =
                                    some stores := by
                                simpa [hTargetsLength] using hStores
                              simp [lowerStmt, hFunction, hArgsLength,
                                hTargetsLength, hTargetsNodup, hArgs,
                                hUsesFrame, hConfig, hStores'] at hLower
                              rcases hLower with ⟨rfl, rfl⟩
                              exact StateExtends.of_shape rfl rfl
                    · cases hStores :
                          lowerCallTargetsCode? ctx state
                            targets.reverse targets.length with
                      | none =>
                          have hStores' :
                              lowerCallTargetsCode? ctx state
                                  targets.reverse fn.returns.length =
                                none := by
                            simpa [hTargetsLength] using hStores
                          simp [lowerStmt, hFunction, hArgsLength,
                            hTargetsLength, hTargetsNodup, hArgs,
                            hUsesFrame, hStores'] at hLower
                      | some stores =>
                          have hStores' :
                              lowerCallTargetsCode? ctx state
                                  targets.reverse fn.returns.length =
                                some stores := by
                            simpa [hTargetsLength] using hStores
                          simp [lowerStmt, hFunction, hArgsLength,
                            hTargetsLength, hTargetsNodup, hArgs,
                            hUsesFrame, hStores'] at hLower
                          rcases hLower with ⟨rfl, rfl⟩
                          exact StateExtends.of_shape rfl rfl
              · simp [lowerStmt, hFunction, hArgsLength,
                  hTargetsLength, hTargetsNodup] at hLower
            · simp [lowerStmt, hFunction, hArgsLength,
                hTargetsLength] at hLower
          · simp [lowerStmt, hFunction, hArgsLength] at hLower
  | terminal kind =>
      simp [lowerStmt] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | terminalArgs kind args =>
      cases hArgs : lowerExprSeq ctx state args with
      | none =>
          simp [lowerStmt, hArgs] at hLower
      | some loweredArgs =>
          simp [lowerStmt, hArgs] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact StateExtends.of_shape rfl rfl

/--
Successful lowering of a well-scoped statement list preserves every incoming
allocation slot and records the exact removable stack-local prefix.
-/
theorem lowerStmtList_stateExtends
    {ctx : Ctx} {returns live : List Name}
    {state final : State} {stmts : List Stmt}
    {lowered : List Locals.Stmt}
    (hScoped : Scope.StmtList.Scoped live stmts)
    (hLower :
      lowerStmtList ctx returns state stmts =
        some (lowered, final)) :
    StateExtends live state final := by
  induction stmts generalizing live state final lowered with
  | nil =>
      simp [lowerStmtList] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | cons stmt rest ih =>
      have hHeadScoped : Scope.Stmt.Scoped live stmt := hScoped.1
      have hTailScoped :
          Scope.StmtList.Scoped (Scope.Stmt.outEnv live stmt) rest :=
        hScoped.2
      cases hHead :
          lowerStmt ctx returns state stmt with
      | none =>
          simp [lowerStmtList, hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, next⟩
          cases hTail :
              lowerStmtList ctx returns next rest with
          | none =>
              simp [lowerStmtList, hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailFinal⟩
              simp [lowerStmtList, hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                (lowerStmt_stateExtends hHeadScoped hHead).trans
                  (ih hTailScoped hTail)
                  (fun name hLive => mem_stmt_outEnv hLive)

/--
The real open-block lowerer supplies the lexical layout and slot facts consumed
by observer-preserving cleanup.
-/
theorem lowerBlockOpen_stateExtends
    {ctx : Ctx} {returns live : List Name}
    {state final : State} {block : Block}
    {lowered : Locals.Block}
    (hScoped : Scope.Block.Scoped live block)
    (hLower :
      lowerBlockOpen ctx returns state block =
        some (lowered, final)) :
    StateExtends live state final := by
  rcases block with ⟨stmts⟩
  cases hList :
      lowerStmtList ctx returns state stmts with
  | none =>
      simp [lowerBlockOpen, hList] at hLower
  | some result =>
      rcases result with ⟨loweredStmts, listFinal⟩
      simp [lowerBlockOpen, hList] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact lowerStmtList_stateExtends hScoped hList

/--
Successful open-block lowering of a nonempty block decomposes through the
ordinary statement lowerer and the recursively lowered tail.
-/
theorem lowerBlockOpen_cons_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {stmt : Stmt} {rest : List Stmt}
    {lowered : Locals.Block}
    (hLower :
      lowerBlockOpen ctx returns state { stmts := stmt :: rest } =
        some (lowered, final)) :
    ∃ head next tail,
      lowerStmt ctx returns state stmt = some (head, next) ∧
      lowerBlockOpen ctx returns next { stmts := rest } =
        some ({ stmts := tail }, final) ∧
      lowered.stmts = head ++ tail := by
  cases hHead : lowerStmt ctx returns state stmt with
  | none =>
      simp [lowerBlockOpen, lowerStmtList, hHead] at hLower
  | some headResult =>
      rcases headResult with ⟨head, next⟩
      cases hTail :
          lowerStmtList ctx returns next rest with
      | none =>
          simp [lowerBlockOpen, lowerStmtList, hHead, hTail] at hLower
      | some tailResult =>
          rcases tailResult with ⟨tail, tailFinal⟩
          simp [lowerBlockOpen, lowerStmtList, hHead, hTail] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact
            ⟨head, next, tail, rfl,
              by simp [lowerBlockOpen, hTail], rfl⟩

def lowerFunction? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (state : AllocationSupport.CompileState) (fn : FunDef) :
    Option (Locals.Proc × AllocationSupport.CompileState) := do
  let slots ← AllocationSupport.lookupFun? fn.name recipe.functionSlots
  let root := ScopeId.function fn.name
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let entryLayout :=
    fn.params.reverse ++ if needsFrame then [frameName] else []
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameConfig? := frameConfig?
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let markers :=
    [bindEntryLayout entryLayout] ++
      if needsFrame then
        [bindScratchBindings fn.params.length scratchBindings]
      else
        []
  let (paramPrelude, paramLayout) :=
    lowerParams ctx slots.params entryLayout
  let (returnPrelude, bodyLayout) :=
    lowerReturns ctx slots.returns paramLayout
  let bodyStart : State :=
    { allocation :=
        { env := AllocationSupport.functionEnv slots
          nextSlot := state.nextSlot }
      layout := bodyLayout }
  let (body, final) ←
    lowerBlockOpen ctx fn.returns bodyStart fn.body
  let returnValues ← lowerReturnExprs ctx final fn.returns
  let fullBody : Locals.Block :=
    { stmts :=
        markers ++ paramPrelude ++ returnPrelude ++ body.stmts ++
          [.exprs returnValues] }
  some
    ({ name := fn.name
       argc := fn.params.length + if needsFrame then 1 else 0
       retc := fn.returns.length
       entryLayout := entryLayout
       body := fullBody },
     { env := state.env
       nextSlot := final.allocation.nextSlot })

def lowerFunctions? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig) :
    AllocationSupport.CompileState → List FunDef →
      Option (List Locals.Proc × AllocationSupport.CompileState)
  | state, [] => some ([], state)
  | state, fn :: rest => do
      let (proc, next) ←
        lowerFunction? recipe stackSlots frameName frameConfig? state fn
      let (tail, final) ←
        lowerFunctions? recipe stackSlots frameName frameConfig? next rest
      some (proc :: tail, final)

theorem lowerFunction?_name
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet} {frameName : Name}
    {frameConfig? : Option AllocationSupport.ScratchFrameConfig}
    {state final : AllocationSupport.CompileState}
    {fn : FunDef} {proc : Locals.Proc}
    (hLower :
      lowerFunction? recipe stackSlots frameName frameConfig? state fn =
        some (proc, final)) :
    proc.name = fn.name := by
  have hNames :
      (lowerFunction? recipe stackSlots frameName frameConfig? state fn).map
          (fun output => output.1.name) =
        (lowerFunction? recipe stackSlots frameName frameConfig? state fn).map
          (fun _output => fn.name) := by
    simp [lowerFunction?]
  rw [hLower] at hNames
  simpa using hNames

/--
Successful function lowering exposes the exact entry layout, parameter and
return preludes, open body lowering, and final return-expression sequence.
Downstream preservation proofs consume this adjacent-pass interface instead of
unfolding `lowerFunction?`.
-/
theorem lowerFunction?_components
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet} {frameName : Name}
    {frameConfig? : Option AllocationSupport.ScratchFrameConfig}
    {state final : AllocationSupport.CompileState}
    {fn : FunDef} {proc : Locals.Proc}
    (hLower :
      lowerFunction? recipe stackSlots frameName frameConfig? state fn =
        some (proc, final)) :
    ∃ slots body bodyFinal returnValues,
      AllocationSupport.lookupFun? fn.name recipe.functionSlots =
        some slots ∧
      let root := ScopeId.function fn.name
      let scratchBindings :=
        scratchBindingsForRoot recipe stackSlots root
      let needsFrame := !scratchBindings.isEmpty
      let entryLayout :=
        fn.params.reverse ++ if needsFrame then [frameName] else []
      let ctx : Ctx :=
        { functions := recipe.functionSlots
          frameConfig? := frameConfig?
          frameName := frameName
          stackSlots := stackSlots
          root := root
          scratchBindings := scratchBindings
          frameFunctions := frameFunctions recipe stackSlots }
      let markers :=
        [bindEntryLayout entryLayout] ++
          if needsFrame then
            [bindScratchBindings fn.params.length scratchBindings]
          else
            []
      let (paramPrelude, paramLayout) :=
        lowerParams ctx slots.params entryLayout
      let (returnPrelude, bodyLayout) :=
        lowerReturns ctx slots.returns paramLayout
      let bodyStart : State :=
        { allocation :=
            { env := AllocationSupport.functionEnv slots
              nextSlot := state.nextSlot }
          layout := bodyLayout }
      lowerBlockOpen ctx fn.returns bodyStart fn.body =
          some (body, bodyFinal) ∧
        lowerReturnExprs ctx bodyFinal fn.returns =
          some returnValues ∧
        proc =
          { name := fn.name
            argc := fn.params.length + if needsFrame then 1 else 0
            retc := fn.returns.length
            entryLayout := entryLayout
            body :=
              { stmts :=
                  markers ++ paramPrelude ++ returnPrelude ++ body.stmts ++
                    [.exprs returnValues] } } ∧
        final =
          { env := state.env
            nextSlot := bodyFinal.allocation.nextSlot } := by
  cases hSlots :
      AllocationSupport.lookupFun? fn.name recipe.functionSlots with
  | none =>
      simp [lowerFunction?, hSlots] at hLower
  | some slots =>
      let root := ScopeId.function fn.name
      let scratchBindings :=
        scratchBindingsForRoot recipe stackSlots root
      let needsFrame := !scratchBindings.isEmpty
      let entryLayout :=
        fn.params.reverse ++ if needsFrame then [frameName] else []
      let ctx : Ctx :=
        { functions := recipe.functionSlots
          frameConfig? := frameConfig?
          frameName := frameName
          stackSlots := stackSlots
          root := root
          scratchBindings := scratchBindings
          frameFunctions := frameFunctions recipe stackSlots }
      let markers :=
        [bindEntryLayout entryLayout] ++
          if needsFrame then
            [bindScratchBindings fn.params.length scratchBindings]
          else
            []
      let paramResult := lowerParams ctx slots.params entryLayout
      let paramPrelude := paramResult.1
      let paramLayout := paramResult.2
      let returnResult := lowerReturns ctx slots.returns paramLayout
      let returnPrelude := returnResult.1
      let bodyLayout := returnResult.2
      let bodyStart : State :=
        { allocation :=
            { env := AllocationSupport.functionEnv slots
              nextSlot := state.nextSlot }
          layout := bodyLayout }
      simp only [lowerFunction?, hSlots] at hLower
      change
        (do
          let (body, bodyFinal) ←
            lowerBlockOpen ctx fn.returns bodyStart fn.body
          let returnValues ←
            lowerReturnExprs ctx bodyFinal fn.returns
          some
            ({ name := fn.name
               argc := fn.params.length + if needsFrame then 1 else 0
               retc := fn.returns.length
               entryLayout := entryLayout
               body :=
                 { stmts :=
                     markers ++ paramPrelude ++ returnPrelude ++
                       body.stmts ++ [.exprs returnValues] } },
             { env := state.env
               nextSlot := bodyFinal.allocation.nextSlot })) =
          some (proc, final) at hLower
      cases hBody :
          lowerBlockOpen ctx fn.returns bodyStart fn.body with
      | none =>
          simp [hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨body, bodyFinal⟩
          cases hReturns :
              lowerReturnExprs ctx bodyFinal fn.returns with
          | none =>
              simp [hBody, hReturns] at hLower
          | some returnValues =>
              simp [hBody, hReturns] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              refine
                ⟨slots, body, bodyFinal, returnValues, rfl, ?_⟩
              exact
                ⟨hBody, hReturns,
                  by
                    simp [markers, paramPrelude, paramLayout, paramResult,
                      returnPrelude, returnResult, entryLayout,
                      needsFrame, scratchBindings, root, ctx,
                      List.append_assoc],
                  rfl⟩

/--
Successful adjacent compilation of one lowered function exposes the actual
parameter and return prelude compiler phases. All generated layouts are
recovered from `lowerFunction?` and `Locals.Proc.toExpressions?`.
-/
theorem lowerFunction?_toExpressions?_prelude_components
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet} {frameName : Name}
    {frameConfig? : Option AllocationSupport.ScratchFrameConfig}
    {state final : AllocationSupport.CompileState}
    {fn : FunDef} {proc : Locals.Proc}
    {lowerProc : Expressions.Proc}
    (hLower :
      lowerFunction? recipe stackSlots frameName frameConfig? state fn =
        some (proc, final))
    (hCompile : proc.toExpressions? = some lowerProc) :
    ∃ slots paramCode paramCtx returnCode returnCtx,
      AllocationSupport.lookupFun? fn.name recipe.functionSlots =
          some slots ∧
      let root := ScopeId.function fn.name
      let scratchBindings :=
        scratchBindingsForRoot recipe stackSlots root
      let needsFrame := !scratchBindings.isEmpty
      let entryLayout :=
        fn.params.reverse ++ if needsFrame then [frameName] else []
      let ctx : Ctx :=
        { functions := recipe.functionSlots
          frameConfig? := frameConfig?
          frameName := frameName
          stackSlots := stackSlots
          root := root
          scratchBindings := scratchBindings
          frameFunctions := frameFunctions recipe stackSlots }
      let paramResult := lowerParams ctx slots.params entryLayout
      let returnResult :=
        lowerReturns ctx slots.returns paramResult.2
      let entryCtx :=
        Locals.Ctx.procEntryWithLayoutAndRetc
          entryLayout fn.returns.length
      Locals.Block.compileOpen entryCtx
          { stmts := paramResult.1 } =
        some (paramCode, paramCtx) ∧
        paramCtx.layout = paramResult.2 ∧
        Locals.Block.compileOpen paramCtx
            { stmts :=
                (lowerReturns ctx slots.returns paramCtx.layout).1 } =
          some (returnCode, returnCtx) ∧
        returnCtx.layout = returnResult.2 := by
  obtain
      ⟨slots, body, bodyFinal, returnValues, hLookup, hComponents⟩ :=
    lowerFunction?_components hLower
  dsimp only at hComponents
  rcases hComponents with
    ⟨_hBody, _hReturnValues, hProc, _hFinal⟩
  let root := ScopeId.function fn.name
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let entryLayout :=
    fn.params.reverse ++ if needsFrame then [frameName] else []
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameConfig? := frameConfig?
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let markers :=
    [bindEntryLayout entryLayout] ++
      if needsFrame then
        [bindScratchBindings fn.params.length scratchBindings]
      else
        []
  let paramResult := lowerParams ctx slots.params entryLayout
  let returnResult :=
    lowerReturns ctx slots.returns paramResult.2
  let entryCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      entryLayout fn.returns.length
  have hProc' :
      proc =
        { name := fn.name
          argc := fn.params.length + if needsFrame then 1 else 0
          retc := fn.returns.length
          entryLayout := entryLayout
          body :=
            { stmts :=
                markers ++ paramResult.1 ++ returnResult.1 ++
                  body.stmts ++ [.exprs returnValues] } } := by
    simpa [root, scratchBindings, needsFrame, entryLayout, ctx,
      markers, paramResult, returnResult, List.append_assoc] using hProc
  obtain ⟨compiledBody, hPreserving, _hLowerProc⟩ :=
    Locals.Proc.toExpressions?_components hCompile
  obtain ⟨fullCode, fullFinal, hOpen, _hFinish⟩ :=
    Locals.Block.compileToPreserving_components hPreserving
  have hOpen' :
      Locals.Block.compileOpen entryCtx
          { stmts :=
              markers ++
                (paramResult.1 ++
                  (returnResult.1 ++
                    (body.stmts ++ [.exprs returnValues]))) } =
        some (fullCode, fullFinal) := by
    rw [hProc'] at hOpen
    simpa [entryCtx, List.append_assoc] using hOpen
  obtain
      ⟨markerCode, afterMarkers, afterMarkerCode,
        hMarkers, hAfterMarkers, _hFullCode⟩ :=
    Locals.Block.compileOpen_append_components hOpen'
  have hMarkerShape :=
    entryMarkers_compileOpen
      (localsCtx := entryCtx) (entryLayout := entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := scratchBindings)
      (needsFrame := needsFrame)
  have hAfterMarkersEq : afterMarkers = entryCtx := by
    rw [hMarkerShape] at hMarkers
    exact (congrArg Prod.snd (Option.some.inj hMarkers)).symm
  subst afterMarkers
  obtain
      ⟨paramCode, paramCtx, afterParamCode,
        hParam, hAfterParam, _hMarkerRestCode⟩ :=
    Locals.Block.compileOpen_append_components hAfterMarkers
  have hParamLayout :=
    lowerParams_compileOpen_final_layout
      (ctx := ctx) (pending := slots.params) hParam
  have hAfterParam' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              returnResult.1 ++
                (body.stmts ++ [.exprs returnValues]) } =
        some (afterParamCode, fullFinal) := by
    simpa [List.append_assoc] using hAfterParam
  obtain
      ⟨returnCode, returnCtx, afterReturnCode,
        hReturn, _hAfterReturn, _hParamRestCode⟩ :=
    Locals.Block.compileOpen_append_components hAfterParam'
  have hReturn' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              (lowerReturns ctx slots.returns paramCtx.layout).1 } =
        some (returnCode, returnCtx) := by
    simpa [returnResult, hParamLayout] using hReturn
  have hReturnLayout :=
    lowerReturns_compileOpen_final_layout hReturn'
  refine
    ⟨slots, paramCode, paramCtx, returnCode, returnCtx, hLookup, ?_⟩
  dsimp only
  refine ⟨?_, hParamLayout, hReturn', ?_⟩
  · simpa [entryCtx, paramResult, entryLayout, needsFrame,
      scratchBindings, root, ctx] using hParam
  · simpa [returnResult, paramResult, entryCtx, entryLayout,
      needsFrame, scratchBindings, root, ctx, hParamLayout] using
      hReturnLayout

/--
Successful lowering and adjacent compilation of one function expose the
complete emitted procedure body as pass-owned phases: entry markers, parameter
and return preludes, the lowered source body, return-value evaluation, and the
final preserving cleanup.

Observer proofs consume this theorem instead of accepting generated code as a
premise or unfolding either compiler.
-/
theorem lowerFunction?_toExpressions?_body_components
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet} {frameName : Name}
    {frameConfig? : Option AllocationSupport.ScratchFrameConfig}
    {state final : AllocationSupport.CompileState}
    {fn : FunDef} {proc : Locals.Proc}
    {lowerProc : Expressions.Proc}
    (hLower :
      lowerFunction? recipe stackSlots frameName frameConfig? state fn =
        some (proc, final))
    (hCompile : proc.toExpressions? = some lowerProc) :
    ∃ slots body bodyFinal returnValues
      markerCode paramCode paramCtx returnCode returnCtx
      bodyCode bodyCtx returnValueCode cleanup,
      AllocationSupport.lookupFun? fn.name recipe.functionSlots =
          some slots ∧
      let root := ScopeId.function fn.name
      let scratchBindings :=
        scratchBindingsForRoot recipe stackSlots root
      let needsFrame := !scratchBindings.isEmpty
      let entryLayout :=
        fn.params.reverse ++ if needsFrame then [frameName] else []
      let ctx : Ctx :=
        { functions := recipe.functionSlots
          frameConfig? := frameConfig?
          frameName := frameName
          stackSlots := stackSlots
          root := root
          scratchBindings := scratchBindings
          frameFunctions := frameFunctions recipe stackSlots }
      let markers :=
        [bindEntryLayout entryLayout] ++
          if needsFrame then
            [bindScratchBindings fn.params.length scratchBindings]
          else
            []
      let paramResult := lowerParams ctx slots.params entryLayout
      let returnResult := lowerReturns ctx slots.returns paramResult.2
      let bodyStart : State :=
        { allocation :=
            { env := AllocationSupport.functionEnv slots
              nextSlot := state.nextSlot }
          layout := returnResult.2 }
      let entryCtx :=
        Locals.Ctx.procEntryWithLayoutAndRetc
          entryLayout fn.returns.length
      lowerBlockOpen ctx fn.returns bodyStart fn.body =
          some (body, bodyFinal) ∧
        lowerReturnExprs ctx bodyFinal fn.returns =
          some returnValues ∧
        Locals.Block.compileOpen entryCtx { stmts := markers } =
          some (markerCode, entryCtx) ∧
        Locals.Block.compileOpen entryCtx
            { stmts := paramResult.1 } =
          some (paramCode, paramCtx) ∧
        Locals.Block.compileOpen paramCtx
            { stmts :=
                (lowerReturns ctx slots.returns paramCtx.layout).1 } =
          some (returnCode, returnCtx) ∧
        Locals.Block.compileOpen returnCtx body =
          some (bodyCode, bodyCtx) ∧
        Locals.ExprSeq.compileCode bodyCtx 0 returnValues =
          some returnValueCode ∧
        bodyCtx.cleanupToPreserving? fn.returns.length 0 =
          some cleanup ∧
        lowerProc.name = fn.name ∧
        lowerProc.argc =
          fn.params.length + (if needsFrame then 1 else 0) ∧
        lowerProc.retc = fn.returns.length ∧
        lowerProc.body.stmts =
          markerCode ++ paramCode ++ returnCode ++ bodyCode ++
            Locals.codeStmt returnValueCode ++ Locals.codeStmt cleanup := by
  obtain
      ⟨slots, body, bodyFinal, returnValues, hLookup, hComponents⟩ :=
    lowerFunction?_components hLower
  dsimp only at hComponents
  rcases hComponents with
    ⟨hBody, hReturnValues, hProc, _hFinal⟩
  let root := ScopeId.function fn.name
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let entryLayout :=
    fn.params.reverse ++ if needsFrame then [frameName] else []
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameConfig? := frameConfig?
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let markers :=
    [bindEntryLayout entryLayout] ++
      if needsFrame then
        [bindScratchBindings fn.params.length scratchBindings]
      else
        []
  let paramResult := lowerParams ctx slots.params entryLayout
  let returnResult := lowerReturns ctx slots.returns paramResult.2
  let bodyStart : State :=
    { allocation :=
        { env := AllocationSupport.functionEnv slots
          nextSlot := state.nextSlot }
      layout := returnResult.2 }
  let entryCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      entryLayout fn.returns.length
  have hProc' :
      proc =
        { name := fn.name
          argc := fn.params.length + if needsFrame then 1 else 0
          retc := fn.returns.length
          entryLayout := entryLayout
          body :=
            { stmts :=
                markers ++ paramResult.1 ++ returnResult.1 ++
                  body.stmts ++ [.exprs returnValues] } } := by
    simpa [root, scratchBindings, needsFrame, entryLayout, ctx,
      markers, paramResult, returnResult, bodyStart,
      List.append_assoc] using hProc
  obtain ⟨compiledBody, hPreserving, hLowerProc⟩ :=
    Locals.Proc.toExpressions?_components hCompile
  obtain ⟨fullCode, fullFinal, hOpen, hFinish⟩ :=
    Locals.Block.compileToPreserving_components hPreserving
  have hOpen' :
      Locals.Block.compileOpen entryCtx
          { stmts :=
              markers ++
                (paramResult.1 ++
                  (returnResult.1 ++
                    (body.stmts ++ [.exprs returnValues]))) } =
        some (fullCode, fullFinal) := by
    rw [hProc'] at hOpen
    simpa [entryCtx, List.append_assoc] using hOpen
  obtain
      ⟨markerCode, afterMarkers, afterMarkerCode,
        hMarkers, hAfterMarkers, hFullShape⟩ :=
    Locals.Block.compileOpen_append_components hOpen'
  have hMarkerShape :=
    entryMarkers_compileOpen
      (localsCtx := entryCtx) (entryLayout := entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := scratchBindings)
      (needsFrame := needsFrame)
  have hAfterMarkersEq : afterMarkers = entryCtx := by
    rw [hMarkerShape] at hMarkers
    exact (congrArg Prod.snd (Option.some.inj hMarkers)).symm
  subst afterMarkers
  obtain
      ⟨paramCode, paramCtx, afterParamCode,
        hParam, hAfterParam, hMarkerRestShape⟩ :=
    Locals.Block.compileOpen_append_components hAfterMarkers
  have hParamLayout :=
    lowerParams_compileOpen_final_layout
      (ctx := ctx) (pending := slots.params) hParam
  have hAfterParam' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              returnResult.1 ++
                (body.stmts ++ [.exprs returnValues]) } =
        some (afterParamCode, fullFinal) := by
    simpa [List.append_assoc] using hAfterParam
  obtain
      ⟨returnCode, returnCtx, afterReturnCode,
        hReturn, hAfterReturn, hParamRestShape⟩ :=
    Locals.Block.compileOpen_append_components hAfterParam'
  have hReturn' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              (lowerReturns ctx slots.returns paramCtx.layout).1 } =
        some (returnCode, returnCtx) := by
    simpa [returnResult, hParamLayout] using hReturn
  obtain
      ⟨bodyCode, bodyCtx, returnStmtCode,
        hBodyCompile, hReturnCompile, hReturnRestShape⟩ :=
    Locals.Block.compileOpen_append_components hAfterReturn
  have hReturnSingle :=
    Locals.Block.compileOpen_single_components hReturnCompile
  cases hReturnValueCode :
      Locals.ExprSeq.compileCode bodyCtx 0 returnValues with
  | none =>
      simp [Locals.Stmt.compile, hReturnValueCode] at hReturnSingle
  | some returnValueCode =>
      simp [Locals.Stmt.compile, hReturnValueCode] at hReturnSingle
      rcases hReturnSingle with ⟨hReturnStmtCode, hFullFinal⟩
      subst returnStmtCode
      subst fullFinal
      have hMarkerCode : markerCode =
          [Expressions.Stmt.code
            [Structured.BasicInstr.bindLocals 0 entryLayout]] ++
            if needsFrame then
              [Expressions.Stmt.code
                (AllocationSupport.bindScratchBindingsCode
                  fn.params.length scratchBindings)]
            else
              [] := by
        rw [hMarkerShape] at hMarkers
        exact (congrArg Prod.fst (Option.some.inj hMarkers)).symm
      have hCodeShape :
          fullCode =
            markerCode ++ paramCode ++ returnCode ++ bodyCode ++
              Locals.codeStmt returnValueCode := by
        rw [hFullShape, hMarkerRestShape, hParamRestShape,
          hReturnRestShape]
        simp [List.append_assoc]
      have hProcRetc : proc.retc = fn.returns.length :=
        congrArg Locals.Proc.retc hProc'
      rw [hProcRetc] at hFinish
      cases hCleanup :
          bodyCtx.cleanupToPreserving? fn.returns.length 0 with
      | none =>
          simp [Locals.finishToPreserving, hCleanup] at hFinish
      | some cleanup =>
          have hCompiledBody :
              compiledBody.stmts =
                fullCode ++ Locals.codeStmt cleanup := by
            have hBlockEq :
                ({ stmts :=
                    fullCode ++ Locals.codeStmt cleanup } :
                  Expressions.Block) =
                  compiledBody :=
              Option.some.inj
                (by
                  simpa [Locals.finishToPreserving, hCleanup] using hFinish)
            exact (congrArg Expressions.Block.stmts hBlockEq).symm
          have hLowerName : lowerProc.name = proc.name := by
            simpa [hLowerProc]
          have hLowerArgc : lowerProc.argc = proc.argc := by
            simpa [hLowerProc]
          have hLowerRetc : lowerProc.retc = proc.retc := by
            simpa [hLowerProc]
          have hLowerBody : lowerProc.body = compiledBody := by
            simpa [hLowerProc]
          refine
            ⟨slots, body, bodyFinal, returnValues,
              markerCode, paramCode, paramCtx, returnCode, returnCtx,
              bodyCode, bodyCtx, returnValueCode, cleanup,
              hLookup, ?_⟩
          dsimp only
          refine
            ⟨?_, ?_, hMarkers, hParam, hReturn',
              ?_, hReturnValueCode, hCleanup, ?_, ?_, ?_, ?_⟩
          · simpa [root, scratchBindings, needsFrame, entryLayout, ctx,
              paramResult, returnResult, bodyStart] using hBody
          · simpa [root, scratchBindings, needsFrame, entryLayout, ctx,
              paramResult, returnResult, bodyStart] using hReturnValues
          · cases body
            exact hBodyCompile
          · exact hLowerName.trans (congrArg Locals.Proc.name hProc')
          · exact hLowerArgc.trans (congrArg Locals.Proc.argc hProc')
          · exact hLowerRetc.trans (congrArg Locals.Proc.retc hProc')
          · rw [hLowerBody, hCompiledBody, hCodeShape]

/--
State-threaded function-list lowering preserves source function lookup and
returns the actual `lowerFunction?` equation for the selected function.
-/
theorem lowerFunctions?_find_components
    (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (name : Name) :
    ∀ {state final : AllocationSupport.CompileState}
      {functions : List FunDef} {procs : List Locals.Proc} {fn : FunDef},
      lowerFunctions? recipe stackSlots frameName frameConfig?
          state functions =
        some (procs, final) →
      Source.FunList.find? name functions = some fn →
      ∃ before after proc,
        lowerFunction? recipe stackSlots frameName frameConfig? before fn =
          some (proc, after) ∧
        proc ∈ procs ∧
        proc.name = name
  | _state, _final, [], _procs, _fn, hLower, hFind => by
      simp [lowerFunctions?, Source.FunList.find?] at hLower hFind
  | state, final, head :: rest, procs, fn, hLower, hFind => by
      cases hHead :
          lowerFunction? recipe stackSlots frameName frameConfig?
            state head with
      | none =>
          simp [lowerFunctions?, hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨headProc, next⟩
          cases hTail :
              lowerFunctions? recipe stackSlots frameName frameConfig?
                next rest with
          | none =>
              simp [lowerFunctions?, hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailFinal⟩
              simp [lowerFunctions?, hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hHeadName := lowerFunction?_name hHead
              by_cases hName : head.name = name
              · have hFn : fn = head := by
                  simpa [Source.FunList.find?, hName] using hFind.symm
                subst fn
                exact
                  ⟨state, next, headProc, hHead, by simp,
                    hHeadName.trans hName⟩
              · have hFindTail :
                    Source.FunList.find? name rest = some fn := by
                  simpa [Source.FunList.find?, hName] using hFind
                obtain
                    ⟨before, after, proc, hSelected, hMember, hProcName⟩ :=
                  lowerFunctions?_find_components recipe stackSlots frameName
                    frameConfig? name hTail hFindTail
                exact
                  ⟨before, after, proc, hSelected, by simp [hMember],
                    hProcName⟩

/--
Source function lookup through the real function-list lowerer and Locals
procedure compiler recovers the selected compiled procedure.
-/
theorem lowerFunctions?_find_compiled_components
    (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (name : Name)
    {state final : AllocationSupport.CompileState}
    {functions : List FunDef}
    {procs : List Locals.Proc}
    {lowerProcs : List Expressions.Proc}
    {fn : FunDef}
    (hLower :
      lowerFunctions? recipe stackSlots frameName frameConfig?
          state functions =
        some (procs, final))
    (hCompile :
      Locals.ProcList.toExpressions? procs =
        some lowerProcs)
    (hFind :
      Source.FunList.find? name functions = some fn) :
    ∃ before after proc lowerProc,
      lowerFunction? recipe stackSlots frameName frameConfig? before fn =
          some (proc, after) ∧
        proc.toExpressions? = some lowerProc ∧
        lowerProc ∈ lowerProcs ∧
        lowerProc.name = name := by
  obtain ⟨before, after, proc, hSelected, hMember, hProcName⟩ :=
    lowerFunctions?_find_components
      recipe stackSlots frameName frameConfig? name hLower hFind
  obtain ⟨lowerProc, hProcCompile, hLowerMember⟩ :=
    Locals.ProcList.toExpressions?_member_components hCompile hMember
  exact
    ⟨before, after, proc, lowerProc,
      hSelected, hProcCompile, hLowerMember,
      (Locals.Proc.toExpressions?_name hProcCompile).trans hProcName⟩

/--
Source lookup through function lowering and Locals procedure compilation
selects the same procedure through the actual Structured lookup order.

This stronger pass-owned interface avoids turning list membership or generated
name-uniqueness evidence into an observer-proof premise.
-/
theorem lowerFunctions?_find_compiled_lookup
    (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (name : Name) :
    ∀ {state final : AllocationSupport.CompileState}
      {functions : List FunDef}
      {procs : List Locals.Proc}
      {lowerProcs : List Expressions.Proc}
      {fn : FunDef},
      lowerFunctions? recipe stackSlots frameName frameConfig?
          state functions =
        some (procs, final) →
      Locals.ProcList.toExpressions? procs =
        some lowerProcs →
      Source.FunList.find? name functions = some fn →
      ∃ before after proc lowerProc,
        lowerFunction? recipe stackSlots frameName frameConfig? before fn =
            some (proc, after) ∧
          proc.toExpressions? = some lowerProc ∧
          Structured.ProcList.lookup? name
              (Expressions.ProcList.toStructured lowerProcs) =
            some lowerProc.toStructured ∧
          lowerProc.name = name
  | _state, _final, [], _procs, _lowerProcs, _fn,
      hLower, _hCompile, hFind => by
      simp [lowerFunctions?, Source.FunList.find?] at hLower hFind
  | state, final, head :: rest, procs, lowerProcs, fn,
      hLower, hCompile, hFind => by
      cases hHead :
          lowerFunction? recipe stackSlots frameName frameConfig?
            state head with
      | none =>
          simp [lowerFunctions?, hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨headProc, next⟩
          cases hTail :
              lowerFunctions? recipe stackSlots frameName frameConfig?
                next rest with
          | none =>
              simp [lowerFunctions?, hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailFinal⟩
              simp [lowerFunctions?, hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              cases hHeadCompile : headProc.toExpressions? with
              | none =>
                  simp [Locals.ProcList.toExpressions?,
                    hHeadCompile] at hCompile
              | some headLower =>
                  cases hTailCompile :
                      Locals.ProcList.toExpressions? tail with
                  | none =>
                      simp [Locals.ProcList.toExpressions?,
                        hHeadCompile, hTailCompile] at hCompile
                  | some tailLower =>
                      simp [Locals.ProcList.toExpressions?,
                        hHeadCompile, hTailCompile] at hCompile
                      subst lowerProcs
                      have hHeadProcName :=
                        lowerFunction?_name hHead
                      have hHeadLowerName :=
                        Locals.Proc.toExpressions?_name hHeadCompile
                      have hCompiledHeadName :
                          headLower.name = head.name :=
                        hHeadLowerName.trans hHeadProcName
                      by_cases hName : head.name = name
                      · have hFn : fn = head := by
                          simpa [Source.FunList.find?, hName] using
                            hFind.symm
                        subst fn
                        exact
                          ⟨state, next, headProc, headLower,
                            hHead, hHeadCompile,
                            by
                              simp [Expressions.ProcList.toStructured,
                                Structured.ProcList.lookup?,
                                hCompiledHeadName, hName],
                            hCompiledHeadName.trans hName⟩
                      · have hFindTail :
                            Source.FunList.find? name rest = some fn := by
                          simpa [Source.FunList.find?, hName] using hFind
                        obtain
                            ⟨before, after, proc, lowerProc,
                              hSelected, hProcCompile, hLookup,
                              hProcName⟩ :=
                          lowerFunctions?_find_compiled_lookup
                            recipe stackSlots frameName frameConfig?
                            name hTail hTailCompile hFindTail
                        have hCompiledHeadNe :
                            headLower.name ≠ name := by
                          intro hEq
                          exact hName (hCompiledHeadName.symm.trans hEq)
                        exact
                          ⟨before, after, proc, lowerProc,
                            hSelected, hProcCompile,
                            by
                              simpa [Expressions.ProcList.toStructured,
                                Structured.ProcList.lookup?,
                                hCompiledHeadNe] using hLookup,
                            hProcName⟩

def lowerMain? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (state : AllocationSupport.CompileState)
    (body : Block) : Option (Locals.Block × State) := do
  let root := ScopeId.main
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameConfig? := frameConfig?
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let needsAllocator :=
    needsFrame || !(frameFunctions recipe stackSlots).isEmpty
  let allocatorPrelude ←
    if needsAllocator then do
      let frameConfig ← frameConfig?
      some
        [ .expr
            (Locals.Expr.code (results := 0)
              (AllocationSupport.scratchAllocatorInitCode frameConfig)) ]
    else
      some []
  let framePrelude ←
    if needsFrame then do
      let frameConfig ← frameConfig?
      some
        [ Locals.Stmt.let_ frameName (frameExpr frameConfig),
          bindScratchBindings 0 scratchBindings ]
    else
      some []
  let prelude := allocatorPrelude ++ framePrelude
  let start : State :=
    { allocation := state
      layout := if needsFrame then [frameName] else [] }
  let (sourcePrelude, rest) := splitPrelude body.stmts
  let (lowered, final) ←
    lowerBlockOpen ctx [] start { stmts := rest }
  some
    ({ stmts := sourcePrelude ++ prelude ++ lowered.stmts },
      final)

def lowerToLocals? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (program : Program) : Option Locals.Program := do
  let frameConfig? :=
    AllocationSupport.scratchFrameConfig?
      program.memoryContract recipe.frameWords
  let (procs, stateAfterFunctions) ←
    lowerFunctions? recipe stackSlots frameName frameConfig?
      recipe.stateAfterSignatures program.functions
  if stateAfterFunctions = recipe.stateAfterFunctions then pure () else none
  let mainStart : AllocationSupport.CompileState :=
    { env := [], nextSlot := stateAfterFunctions.nextSlot }
  let (main, final) ←
    lowerMain? recipe stackSlots frameName frameConfig? mainStart program.body
  if final.allocation = recipe.main then
    some { procs := procs, body := main }
  else
    none

def allSourceNames (program : Program) : List Name :=
  let functionNames :=
    program.functions.flatMap fun fn =>
      fn.name :: fn.params ++ fn.returns
  functionNames ++
    (AllocationSupport.planRecipeCore? program).toList.flatMap fun recipe =>
      (scopedStates recipe).flatMap fun entry =>
        entry.state.env.map Prod.fst

def freshFrameName (program : Program) : Option Name :=
  let names := allSourceNames program
  (List.range (names.length + 1)).findSome? fun index =>
    let candidate := "__evm_compiler_scratch_frame_" ++ toString index
    if candidate ∈ names then none else some candidate

theorem freshFrameName_not_mem_allSourceNames
    {program : Program} {frameName : Name}
    (hFresh : freshFrameName program = some frameName) :
    frameName ∉ allSourceNames program := by
  unfold freshFrameName at hFresh
  obtain ⟨index, _hIndex, hCandidate⟩ :=
    List.exists_of_findSome?_eq_some hFresh
  let candidate :=
    "__evm_compiler_scratch_frame_" ++ toString index
  by_cases hMem : candidate ∈ allSourceNames program
  · simp [candidate, hMem] at hCandidate
  · simp [candidate, hMem] at hCandidate
    subst frameName
    exact hMem

theorem freshFrameName_not_mem_params
    {program : Program} {frameName : Name} {fn : FunDef}
    (hFresh : freshFrameName program = some frameName)
    (hFn : fn ∈ program.functions) :
    frameName ∉ fn.params := by
  have hNotMem := freshFrameName_not_mem_allSourceNames hFresh
  intro hParam
  apply hNotMem
  simp only [allSourceNames, List.mem_append, List.mem_flatMap,
    List.mem_cons]
  exact Or.inl ⟨fn, hFn, Or.inl (Or.inr hParam)⟩

theorem freshFrameName_not_mem_returns
    {program : Program} {frameName : Name} {fn : FunDef}
    (hFresh : freshFrameName program = some frameName)
    (hFn : fn ∈ program.functions) :
    frameName ∉ fn.returns := by
  have hNotMem := freshFrameName_not_mem_allSourceNames hFresh
  intro hReturn
  apply hNotMem
  simp only [allSourceNames, List.mem_append, List.mem_flatMap,
    List.mem_cons]
  exact Or.inl ⟨fn, hFn, Or.inr hReturn⟩

structure SlotOccurrence where
  scope : ScopeId
  name : Name
  slot : Nat

def slotOccurrences
    (recipe : AllocationSupport.AllocationRecipe) :
    List SlotOccurrence :=
  (scopedStates recipe).flatMap fun entry =>
    entry.state.env.map fun binding =>
      { scope := entry.scope
        name := binding.1
        slot := binding.2 }

def bindingLocation? (allocation : ProgramPlan)
    (scope : ScopeId) (name : Name) : Option LocalLocation := do
  let plan ← allocation.find? scope
  plan.location? name

def inferSlotStack? (allocation : ProgramPlan)
    (occurrences : List SlotOccurrence) (slot : Nat) : Option Bool := do
  let occurrence ←
    occurrences.find? fun candidate => decide (candidate.slot = slot)
  let location ←
    bindingLocation? allocation occurrence.scope occurrence.name
  match location with
  | .stack _ => some true
  | .scratch scratchSlot =>
      if scratchSlot = slot then some false else none

def inferStackSlots? (recipe : AllocationSupport.AllocationRecipe)
    (allocation : ProgramPlan) : Option SlotSet :=
  let occurrences := slotOccurrences recipe
  (List.range recipe.frameWords).filterM fun slot =>
    inferSlotStack? allocation occurrences slot

def compatiblePlan? (allocation : ProgramPlan)
    (program : Program) :
    Option (AllocationSupport.AllocationRecipe × SlotSet) := do
  let recipe ← AllocationSupport.planRecipeCore? program
  let stackSlots ← inferStackSlots? recipe allocation
  if stackSlots.Nodup then pure () else none
  if MixedAllocation.AllocationRecipe.executable?
      recipe stackSlots program then
    pure ()
  else
    none
  if MixedAllocation.AllocationRecipe.toMixedProgramPlan
      recipe stackSlots program.memoryContract = allocation then
    some (recipe, stackSlots)
  else
    none

def Compatible (allocation : ProgramPlan) (program : Program) : Prop :=
  (compatiblePlan? allocation program).isSome = true

theorem compatiblePlan?_eq_some_exact
    {allocation : ProgramPlan} {program : Program}
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    (hCompatible :
      compatiblePlan? allocation program =
        some (recipe, stackSlots)) :
    AllocationSupport.planRecipeCore? program = some recipe ∧
      inferStackSlots? recipe allocation = some stackSlots ∧
      stackSlots.Nodup ∧
      MixedAllocation.AllocationRecipe.executable?
          recipe stackSlots program = true ∧
      MixedAllocation.AllocationRecipe.toMixedProgramPlan
          recipe stackSlots program.memoryContract = allocation := by
  unfold compatiblePlan? at hCompatible
  cases hRecipe : AllocationSupport.planRecipeCore? program with
  | none =>
      simp [hRecipe] at hCompatible
  | some plannedRecipe =>
      cases hSlots :
          inferStackSlots? plannedRecipe allocation with
      | none =>
          simp [hRecipe, hSlots] at hCompatible
      | some plannedSlots =>
          by_cases hNodup : plannedSlots.Nodup
          · by_cases hExecutable :
                MixedAllocation.AllocationRecipe.executable?
                    plannedRecipe plannedSlots program = true
            · by_cases hExact :
                  MixedAllocation.AllocationRecipe.toMixedProgramPlan
                      plannedRecipe plannedSlots
                        program.memoryContract = allocation
              · simp
                  [hRecipe, hSlots, hNodup, hExecutable, hExact]
                  at hCompatible
                rcases hCompatible with ⟨rfl, rfl⟩
                exact
                  ⟨rfl, hSlots, hNodup, hExecutable, hExact⟩
              · simp
                  [hRecipe, hSlots, hNodup, hExecutable, hExact]
                  at hCompatible
            · simp [hRecipe, hSlots, hNodup, hExecutable] at hCompatible
          · simp [hRecipe, hSlots, hNodup] at hCompatible

theorem compatible_witness
    {allocation : ProgramPlan} {program : Program}
    (hCompatible : Compatible allocation program) :
    ∃ recipe stackSlots,
      AllocationSupport.planRecipeCore? program = some recipe ∧
        inferStackSlots? recipe allocation = some stackSlots ∧
        stackSlots.Nodup ∧
        MixedAllocation.AllocationRecipe.executable?
            recipe stackSlots program = true ∧
        MixedAllocation.AllocationRecipe.toMixedProgramPlan
            recipe stackSlots program.memoryContract = allocation := by
  unfold Compatible at hCompatible
  cases hPlan : compatiblePlan? allocation program with
  | none =>
      simp [hPlan] at hCompatible
  | some validated =>
      rcases validated with ⟨recipe, stackSlots⟩
      exact
        ⟨recipe, stackSlots,
          compatiblePlan?_eq_some_exact hPlan⟩

def validatePlan? (allocation : ProgramPlan)
    (program : Program) :
    Option (AllocationSupport.AllocationRecipe × SlotSet) := do
  if allocation.wellFormed? then pure () else none
  if allocation.MemoryAuthorized program.memoryContract then
    pure ()
  else
    none
  compatiblePlan? allocation program

theorem validatePlan?_sound
    {allocation : ProgramPlan} {program : Program}
    {validated : AllocationSupport.AllocationRecipe × SlotSet}
    (hValidate :
      validatePlan? allocation program = some validated) :
    allocation.WellFormed ∧ Compatible allocation program := by
  unfold validatePlan? at hValidate
  by_cases hWF : allocation.wellFormed? = true
  · by_cases hAuthorized :
        allocation.MemoryAuthorized program.memoryContract
    · have hCompatible :
          compatiblePlan? allocation program = some validated := by
        simpa [hWF, hAuthorized] using hValidate
      exact
        ⟨Locals.Allocation.ProgramPlan.wellFormed_of_check hWF,
          by simp [Compatible, hCompatible]⟩
    · simp [hWF, hAuthorized] at hValidate
  · simp [hWF] at hValidate

theorem validatePlan?_memoryAuthorized
    {allocation : ProgramPlan} {program : Program}
    {validated : AllocationSupport.AllocationRecipe × SlotSet}
    (hValidate :
      validatePlan? allocation program = some validated) :
    allocation.MemoryAuthorized program.memoryContract := by
  unfold validatePlan? at hValidate
  by_cases hWF : allocation.wellFormed? = true
  · by_cases hAuthorized :
        allocation.MemoryAuthorized program.memoryContract
    · exact hAuthorized
    · simp [hWF, hAuthorized] at hValidate
  · simp [hWF] at hValidate

theorem validatePlan?_eq_some_exact
    {allocation : ProgramPlan} {program : Program}
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    (hValidate :
      validatePlan? allocation program = some (recipe, stackSlots)) :
    allocation.WellFormed ∧
      allocation.MemoryAuthorized program.memoryContract ∧
      AllocationSupport.planRecipeCore? program = some recipe ∧
      inferStackSlots? recipe allocation = some stackSlots ∧
      stackSlots.Nodup ∧
      MixedAllocation.AllocationRecipe.executable?
          recipe stackSlots program = true ∧
      MixedAllocation.AllocationRecipe.toMixedProgramPlan
          recipe stackSlots program.memoryContract = allocation := by
  have hSound := validatePlan?_sound hValidate
  have hAuthorized := validatePlan?_memoryAuthorized hValidate
  have hCompatible :
      compatiblePlan? allocation program = some (recipe, stackSlots) := by
    unfold validatePlan? at hValidate
    by_cases hWF : allocation.wellFormed? = true
    · by_cases hMemory :
          allocation.MemoryAuthorized program.memoryContract
      · simpa [hWF, hMemory] using hValidate
      · simp [hWF, hMemory] at hValidate
    · simp [hWF] at hValidate
  exact
    ⟨hSound.1, hAuthorized,
      compatiblePlan?_eq_some_exact hCompatible⟩

theorem validatePlan?_function_components
    {allocation : ProgramPlan} {program : Program}
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet} {fn : FunDef}
    (hValidate :
      validatePlan? allocation program = some (recipe, stackSlots))
    (hMem : fn ∈ program.functions) :
    ∃ fnSlots entry added,
      AllocationSupport.lookupFun? fn.name recipe.functionSlots =
          some fnSlots ∧
        fnSlots.Matches fn ∧
        entry ∈ recipe.functions ∧
        entry.scope = .function fn.name ∧
        entry.state.env =
          added ++ AllocationSupport.functionEnv fnSlots ∧
        allocation.find? (.function fn.name) =
          some
            (MixedAllocation.allocationOfState
              program.memoryContract recipe.frameWords
              (MixedAllocation.AllocationRecipe.stackEntriesForScope
                recipe stackSlots entry.scope entry.state)
              entry.state) := by
  rcases validatePlan?_eq_some_exact hValidate with
    ⟨hWF, _hAuthorized, hRecipe, _hInfer, _hNodup,
      _hExecutable, hExact⟩
  obtain
      ⟨fnSlots, entry, added, hLookup, hMatches,
        hEntry, hScope, hEnv⟩ :=
    AllocationSupport.planRecipeCore?_function_entry hRecipe hMem
  have hMixedWF :
      (MixedAllocation.AllocationRecipe.toMixedProgramPlan
        recipe stackSlots program.memoryContract).WellFormed := by
    rw [hExact]
    exact hWF
  have hFind :=
    MixedAllocation.AllocationRecipe.toMixedProgramPlan_find_function_entry
      hMixedWF hEntry
  rw [hExact] at hFind
  exact
    ⟨fnSlots, entry, added, hLookup, hMatches, hEntry, hScope, hEnv,
      by simpa [hScope] using hFind⟩

def lowerLocalsFromAllocation? (allocation : ProgramPlan)
    (program : Program) : Option Locals.Program := do
  let (recipe, stackSlots) ← validatePlan? allocation program
  let frameName ← freshFrameName program
  lowerToLocals? recipe stackSlots frameName program

theorem lowerLocalsFromAllocation?_contract
    {allocation : ProgramPlan} {program : Program}
    {locals : Locals.Program}
    (hLower :
      lowerLocalsFromAllocation? allocation program = some locals) :
    allocation.WellFormed ∧ Compatible allocation program := by
  unfold lowerLocalsFromAllocation? at hLower
  cases hValidate : validatePlan? allocation program with
  | none =>
      simp [hValidate] at hLower
  | some validated =>
      exact validatePlan?_sound hValidate

theorem lowerLocalsFromAllocation?_memoryAuthorized
    {allocation : ProgramPlan} {program : Program}
    {locals : Locals.Program}
    (hLower :
      lowerLocalsFromAllocation? allocation program = some locals) :
    allocation.MemoryAuthorized program.memoryContract := by
  unfold lowerLocalsFromAllocation? at hLower
  cases hValidate : validatePlan? allocation program with
  | none =>
      simp [hValidate] at hLower
  | some validated =>
      exact validatePlan?_memoryAuthorized hValidate

def lowerExpressionsFromAllocation? (allocation : ProgramPlan)
    (program : Program) : Option Expressions.Program := do
  let locals ← lowerLocalsFromAllocation? allocation program
  locals.toExpressions?

theorem lowerExpressionsFromAllocation?_contract
    {allocation : ProgramPlan} {program : Program}
    {expressions : Expressions.Program}
    (hLower :
      lowerExpressionsFromAllocation? allocation program =
        some expressions) :
    allocation.WellFormed ∧ Compatible allocation program := by
  unfold lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      lowerLocalsFromAllocation? allocation program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      exact lowerLocalsFromAllocation?_contract hLocals

theorem lowerExpressionsFromAllocation?_memoryAuthorized
    {allocation : ProgramPlan} {program : Program}
    {expressions : Expressions.Program}
    (hLower :
      lowerExpressionsFromAllocation? allocation program =
        some expressions) :
    allocation.MemoryAuthorized program.memoryContract := by
  unfold lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      lowerLocalsFromAllocation? allocation program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      exact lowerLocalsFromAllocation?_memoryAuthorized hLocals

/--
The real whole-program allocation lowerer exposes the validated artifacts for
the source function selected by name and the exact Structured procedure lookup
produced by Locals and Expressions compilation.

Observer preservation consumes this theorem from the public compiler equation;
it does not accept a selected generated procedure or procedure-body equation as
an independent premise.
-/
theorem lowerExpressionsFromAllocation?_find_compiled_function
    {allocation : ProgramPlan} {program : Program}
    {expressions : Expressions.Program}
    {name : Name} {fn : FunDef}
    (hLower :
      lowerExpressionsFromAllocation? allocation program =
        some expressions)
    (hFind :
      Source.FunList.find? name program.functions = some fn) :
    ∃ recipe stackSlots frameName before after proc lowerProc,
      validatePlan? allocation program = some (recipe, stackSlots) ∧
        freshFrameName program = some frameName ∧
        lowerFunction? recipe stackSlots frameName
            (AllocationSupport.scratchFrameConfig?
              program.memoryContract recipe.frameWords)
            before fn =
          some (proc, after) ∧
        proc.toExpressions? = some lowerProc ∧
        Structured.ProcList.lookup? name
            expressions.toStructured.procs =
          some lowerProc.toStructured := by
  unfold lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      lowerLocalsFromAllocation? allocation program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      have hExpressions :
          locals.toExpressions? = some expressions := by
        simpa [hLocals] using hLower
      unfold lowerLocalsFromAllocation? at hLocals
      cases hValidate : validatePlan? allocation program with
      | none =>
          simp [hValidate] at hLocals
      | some validated =>
          rcases validated with ⟨recipe, stackSlots⟩
          cases hFresh : freshFrameName program with
          | none =>
              simp [hValidate, hFresh] at hLocals
          | some frameName =>
              have hToLocals :
                  lowerToLocals? recipe stackSlots frameName program =
                    some locals := by
                simpa [hValidate, hFresh] using hLocals
              let frameConfig? :=
                AllocationSupport.scratchFrameConfig?
                  program.memoryContract recipe.frameWords
              unfold lowerToLocals? at hToLocals
              cases hFunctions :
                  lowerFunctions? recipe stackSlots frameName frameConfig?
                    recipe.stateAfterSignatures program.functions with
              | none =>
                  simp [frameConfig?, hFunctions] at hToLocals
              | some functionResult =>
                  rcases functionResult with
                    ⟨procs, stateAfterFunctions⟩
                  by_cases hState :
                      stateAfterFunctions = recipe.stateAfterFunctions
                  · subst stateAfterFunctions
                    let mainStart : AllocationSupport.CompileState :=
                      { env := []
                        nextSlot := recipe.stateAfterFunctions.nextSlot }
                    cases hMain :
                        lowerMain? recipe stackSlots frameName frameConfig?
                          mainStart program.body with
                    | none =>
                        simp [frameConfig?, hFunctions,
                          mainStart, hMain] at hToLocals
                    | some mainResult =>
                        rcases mainResult with ⟨main, final⟩
                        by_cases hFinal :
                            final.allocation = recipe.main
                        · simp [frameConfig?, hFunctions,
                            mainStart, hMain, hFinal] at hToLocals
                          subst locals
                          unfold Locals.Program.toExpressions? at hExpressions
                          cases hProcs :
                              Locals.ProcList.toExpressions? procs with
                          | none =>
                              simp [hProcs] at hExpressions
                          | some lowerProcs =>
                              cases hBody :
                                  Locals.Block.compile Locals.Ctx.initial
                                    main with
                              | none =>
                                  simp [hProcs, hBody] at hExpressions
                              | some lowerBody =>
                                  simp [hProcs, hBody] at hExpressions
                                  subst expressions
                                  obtain
                                      ⟨before, after, proc, lowerProc,
                                        hSelected, hProcCompile,
                                        hLookup, _hProcName⟩ :=
                                    lowerFunctions?_find_compiled_lookup
                                      recipe stackSlots frameName
                                      frameConfig? name hFunctions
                                      hProcs hFind
                                  exact
                                    ⟨recipe, stackSlots, frameName,
                                      before, after, proc, lowerProc,
                                      rfl, rfl,
                                      by simpa [frameConfig?] using hSelected,
                                      hProcCompile,
                                      by simpa [Expressions.Program.toStructured]
                                        using hLookup⟩
                        · simp [frameConfig?, hFunctions,
                            mainStart, hMain, hFinal] at hToLocals
                  · simp [frameConfig?, hFunctions, hState] at hToLocals

def allocationLowerer :
    Locals.Allocation.Lowerer Program Expressions.Program where
  lower? program allocation :=
    lowerExpressionsFromAllocation? allocation program

def compileAllocated? (allocation : ProgramPlan)
    (program : Program) :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let expressions ←
    lowerExpressionsFromAllocation? allocation program
  let cfg ←
    Structured.TypedCfgCompiler.lowerWithProcEntryShapes?
      expressions.toStructured []
  (Compiler.AllocatedTypedCfg.Program.ofAllocation
    allocation cfg).compileCertified?

namespace Examples

def mixedWideExpressions : Option Expressions.Program := do
  let allocation ← MixedAllocation.Examples.mixedWidePlan
  lowerExpressionsFromAllocation? allocation
    MixedAllocation.Examples.wideProgram

def mixedWideAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ← MixedAllocation.Examples.mixedWidePlan
  compileAllocated? allocation MixedAllocation.Examples.wideProgram

def mixedCallProgram : Program :=
  { functions :=
      [{ name := "sum"
         params := ["x", "y"]
         returns := ["result"]
         body :=
           { stmts :=
               [.assign "result"
                  (.prim .add
                    (exprSeqTwo (.var "x") (.var "y")))] } }]
    body :=
      { stmts :=
          [ .let_ "out" (.lit AllocationSupport.zeroWord),
            .call ["out"] "sum"
              [ .lit (AllocationSupport.word 2),
                .lit (AllocationSupport.word 3) ] ] } }

def mixedCallPlan : Option ProgramPlan :=
  MixedAllocation.planAllocation? 4 [0, 3] mixedCallProgram

def mixedCallExpressions : Option Expressions.Program := do
  let allocation ← mixedCallPlan
  lowerExpressionsFromAllocation? allocation mixedCallProgram

def mixedCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ← mixedCallPlan
  compileAllocated? allocation mixedCallProgram

def allStackCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllStack? mixedCallProgram
  compileAllocated? allocation mixedCallProgram

def allScratchCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllocation? 4 [] mixedCallProgram
  compileAllocated? allocation mixedCallProgram

def twoReturnCallProgram : Program :=
  { functions :=
      [{ name := "pair"
         params := ["x"]
         returns := ["first", "second"]
         body :=
           { stmts :=
               [ .assign "first" (.var "x"),
                 .assign "second"
                   (.prim .add
                     (exprSeqTwo
                       (.var "x")
                       (.lit (AllocationSupport.word 1)))) ] } }]
    body :=
      { stmts :=
          [ .let_ "left" (.lit AllocationSupport.zeroWord),
            .let_ "right" (.lit AllocationSupport.zeroWord),
            .call ["left", "right"] "pair"
              [.lit (AllocationSupport.word 7)] ] } }

def twoReturnCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllocation? 5 [] twoReturnCallProgram
  compileAllocated? allocation twoReturnCallProgram

def alterMainScratchWords (allocation : ProgramPlan) : ProgramPlan :=
  { scopes :=
      allocation.scopes.map fun scope =>
        if scope.scope = .main then
          { scope with
            allocation :=
              { scope.allocation with
                scratchRegion? :=
                  some
                    { base := .freeMemoryPointer
                      words := scope.allocation.scratchSlots.length + 1 } } }
        else
          scope }

def alteredMixedWideRejected : Bool :=
  match MixedAllocation.Examples.mixedWidePlan with
  | none => false
  | some allocation =>
      (lowerExpressionsFromAllocation?
        (alterMainScratchWords allocation)
        MixedAllocation.Examples.wideProgram).isNone

def foreignPlanRejected : Bool :=
  match MixedAllocation.Examples.mixedWidePlan with
  | none => false
  | some allocation =>
      (lowerExpressionsFromAllocation?
        allocation mixedCallProgram).isNone

end Examples

end AllocationLowering
end Functions
end EvmCompiler
