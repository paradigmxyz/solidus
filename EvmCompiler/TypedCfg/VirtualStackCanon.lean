import EvmCompiler.TypedCfg.ShuffleCanonChain

/-!
# Demand-driven virtual-stack canonicalisation

This pass removes redundant stack transport across lowering-order-adjacent,
single-predecessor jump chains.  It symbolically names each stack value, keeps
the source and candidate layouts separately, and materialises shuffles only
when a primitive needs its operands or when the chain must resynchronise.

The transform is deliberately fail-closed:

* only closed `PrimOp.continuingStep?` primitives are admitted (`MSIZE` is
  excluded because its interaction semantics is resource-observing);
* every emitted `DUP`/`SWAP` is checked against the EVM top-16 window;
* every rewritten block body is checked by `Block.bodyType?`;
* only lowering-order-adjacent jump successors with reference count one are
  allowed to carry a non-canonical intermediate layout;
* a chain fires only when aggregate runtime instruction count decreases.

Primitives remain in their original blocks.  Only stack shuffles and
zero-width typing annotations move or disappear, which keeps CFG steps and
interaction timing aligned with the source program.
-/

namespace EvmCompiler
namespace TypedCfg
namespace VirtualStack

open Peephole (refCount)

abbrev Atom := Nat

def atomRangeFrom : Nat → Nat → List Atom
  | _, 0 => []
  | start, count + 1 => start :: atomRangeFrom (start + 1) count

def findAtomFrom (atom : Atom) : Nat → List Atom → Option Nat
  | _, [] => none
  | offset, head :: tail =>
      if head = atom then some offset
      else findAtomFrom atom (offset + 1) tail

def applySwap (depth : Nat) (stack : List Atom) : List Atom :=
  ShuffleCanon.applySwap (depth + 1) stack

structure CodeState where
  code : List Instr := []
  stack : List Atom := []
  deriving Repr

def emitSwap (depth : Nat) (state : CodeState) : Option CodeState :=
  if depth < 16 ∧ depth + 1 < state.stack.length then
    some
      { code := state.code ++ [.swap depth]
        stack := applySwap depth state.stack }
  else
    none

def emitPop (state : CodeState) : Option CodeState :=
  match state.stack with
  | [] => none
  | _ :: rest =>
      some { code := state.code ++ [.pop], stack := rest }

def emitDup (depth : Nat) (state : CodeState) : Option CodeState := do
  if depth < 16 then pure () else none
  let atom ← state.stack[depth]?
  some
    { code := state.code ++ [.dup depth]
      stack := atom :: state.stack }

def rotateAtomToTop : Nat → CodeState → Option CodeState
  | 0, state => some state
  | depth + 1, state => do
      let state ← rotateAtomToTop depth state
      emitSwap depth state

def placeAtom (atom : Atom) (prepared : Nat)
    (neededBelow : List Atom) (state : CodeState) : Option CodeState := do
  let base := state.stack.drop prepared
  let localDepth ← findAtomFrom atom 0 base
  let depth := prepared + localDepth
  if base.count atom ≤ neededBelow.count atom then
    emitDup depth state
  else
    rotateAtomToTop depth state

def prepareRev : List Atom → Nat → List Atom → CodeState →
    Option CodeState
  | [], _, _, state => some state
  | atom :: rest, prepared, surviving, state => do
      let state ← placeAtom atom prepared (surviving ++ rest) state
      prepareRev rest (prepared + 1) surviving state

def coversAtoms (needed available : List Atom) : Bool :=
  needed.all fun atom =>
    decide (needed.count atom ≤ available.count atom)

def prepareOperands (operands surviving : List Atom)
    (state : CodeState) : Option CodeState := do
  if state.stack.take operands.length = operands &&
      coversAtoms surviving (state.stack.drop operands.length) then
    some state
  else
    let prepared ← prepareRev operands.reverse 0 surviving state
    if prepared.stack.take operands.length = operands then
      some prepared
    else
      none

def findExtra (desired : List Atom) : Nat → List Atom → Option Nat
  | _, [] => none
  | index, atom :: rest =>
      if desired.count atom < (atom :: rest).count atom then
        some index
      else
        findExtra desired (index + 1) rest

partial def deleteExtras (desired : List Atom)
    (state : CodeState) : Option CodeState := do
  match findExtra desired 0 state.stack with
  | none => some state
  | some 0 =>
      deleteExtras desired (← emitPop state)
  | some (depth + 1) =>
      let state ← emitSwap depth state
      deleteExtras desired (← emitPop state)

def reconcile (desired : List Atom)
    (state : CodeState) : Option CodeState := do
  if state.stack = desired then
    some state
  else
    let state ← deleteExtras desired state
    let state ← prepareRev desired.reverse 0 [] state
    if state.stack = desired then some state else none

structure State where
  source : List Atom
  target : CodeState
  nextAtom : Nat
  deriving Repr

structure SourceState where
  stack : List Atom
  nextAtom : Nat
  deriving Repr

def sourceSwap? (depth : Nat) (stack : List Atom) :
    Option (List Atom) :=
  if depth < 16 ∧ depth + 1 < stack.length then
    some (applySwap depth stack)
  else
    none

def sourceDup? (depth : Nat) (stack : List Atom) :
    Option (List Atom) := do
  if depth < 16 then pure () else none
  let atom ← stack[depth]?
  some (atom :: stack)

def primAllowed (op : Assembly.PrimOp) : Bool :=
  match op with
  | .msize | .returndatacopy | .sstore | .tstore
  | .log0 | .log1 | .log2 | .log3 | .log4 | .invalid =>
      false
  | _ =>
      op.continuingStep?.isSome

def sourceStep (instr : Instr) (state : SourceState) :
    Option SourceState :=
  match instr with
  | .swap depth => do
      let stack ← sourceSwap? depth state.stack
      some { state with stack }
  | .dup depth => do
      let stack ← sourceDup? depth state.stack
      some { state with stack }
  | .pop =>
      match state.stack with
      | [] => none
      | _ :: stack => some { state with stack }
  | .push _ | .returnToken _ =>
      some
        { stack := state.nextAtom :: state.stack
          nextAtom := state.nextAtom + 1 }
  | .prim op => do
      let (inputs, outputs) ← op.stackArity?
      if inputs ≤ state.stack.length then pure () else none
      let outputAtoms := atomRangeFrom state.nextAtom outputs
      some
        { stack := outputAtoms ++ state.stack.drop inputs
          nextAtom := state.nextAtom + outputs }
  | .bindLocals _ _ | .bindScratch _ _ _ | .relabel _ =>
      some state
  | .unwind _ => none

inductive Event where
  | push (value : Word) (atom : Atom)
  | returnToken (value : Word) (atom : Atom)
  | prim (op : Assembly.PrimOp)
      (operands outputs : List Atom)
  deriving DecidableEq, Repr

/--
The deliberately narrow set of commutative binary primitives admitted by the
virtual-stack trace certificate. Keeping this list explicit makes the
certificate fail closed for every other primitive.
-/
def traceCommutative? : Assembly.PrimOp → Bool
  | .add | .and | .or => true
  | _ => false

/--
Canonicalise only the operand identities recorded for the explicitly admitted
commutative primitives. Runtime stack order remains untouched. Exact event-list
equality can therefore certify a commuted ADD/AND/OR while continuing to require
ordered operands for every other primitive.
-/
def traceOperands (op : Assembly.PrimOp)
    (operands : List Atom) : List Atom :=
  if traceCommutative? op then
    operands.mergeSort (· ≤ ·)
  else
    operands

structure TraceState where
  stack : List Atom
  nextAtom : Nat
  events : List Event := []
  deriving DecidableEq, Repr

def traceStep (instr : Instr) (state : TraceState) :
    Option TraceState :=
  match instr with
  | .swap depth => do
      let stack ← sourceSwap? depth state.stack
      some { state with stack }
  | .dup depth => do
      let stack ← sourceDup? depth state.stack
      some { state with stack }
  | .pop =>
      match state.stack with
      | [] => none
      | _ :: stack => some { state with stack }
  | .push value =>
      let atom := state.nextAtom
      some
        { stack := atom :: state.stack
          nextAtom := atom + 1
          events := state.events ++ [.push value atom] }
  | .returnToken value =>
      let atom := state.nextAtom
      some
        { stack := atom :: state.stack
          nextAtom := atom + 1
          events := state.events ++ [.returnToken value atom] }
  | .prim op => do
      if primAllowed op then pure () else none
      let (inputs, outputs) ← op.stackArity?
      if inputs ≤ state.stack.length then pure () else none
      let operands := state.stack.take inputs
      let outputAtoms := atomRangeFrom state.nextAtom outputs
      some
        { stack := outputAtoms ++ state.stack.drop inputs
          nextAtom := state.nextAtom + outputs
          events := state.events ++
            [.prim op (traceOperands op operands) outputAtoms] }
  | .bindLocals _ _ | .bindScratch _ _ _ | .relabel _ =>
      some state
  | .unwind _ => none

def traceBody : List Instr → TraceState → Option TraceState
  | [], state => some state
  | instr :: rest, state => do
      traceBody rest (← traceStep instr state)

partial def futureNeeds : List Instr → SourceState →
    Option (List Atom)
  | [], state => some state.stack.eraseDups
  | instr :: rest, state => do
      let operands :=
        match instr with
        | .prim op =>
            match op.stackArity? with
            | some (inputs, _) => state.stack.take inputs
            | none => []
        | _ => []
      let after ← sourceStep instr state
      let later ← futureNeeds rest after
      some (operands ++ later).eraseDups

def translateInstr (instr : Instr) (futureNeeded : List Atom)
    (state : State) : Option State :=
  match instr with
  | .swap depth => do
      let source ← sourceSwap? depth state.source
      some { state with source }
  | .dup depth => do
      let source ← sourceDup? depth state.source
      some { state with source }
  | .pop =>
      match state.source with
      | [] => none
      | _ :: source => some { state with source }
  | .push _ | .returnToken _ =>
      let atom := state.nextAtom
      some
        { source := atom :: state.source
          target :=
            { code := state.target.code ++ [instr]
              stack := atom :: state.target.stack }
          nextAtom := atom + 1 }
  | .prim op => do
      if primAllowed op then pure () else none
      let (inputs, outputs) ← op.stackArity?
      if inputs ≤ state.source.length then pure () else none
      let operands := state.source.take inputs
      let sourceTail := state.source.drop inputs
      let surviving :=
        sourceTail.filter (fun atom => futureNeeded.contains atom)
          |>.eraseDups
      let target ← prepareOperands operands surviving state.target
      let outputAtoms := atomRangeFrom state.nextAtom outputs
      some
        { source := outputAtoms ++ sourceTail
          target :=
            { code := target.code ++ [instr]
              stack := outputAtoms ++ target.stack.drop inputs }
          nextAtom := state.nextAtom + outputs }
  | .bindLocals _ _ | .bindScratch _ _ _ | .relabel _ =>
      some state
  | .unwind _ => none

def translateChunk : List Instr → List Instr → State → Option State
  | [], _, state => some state
  | instr :: rest, future, state => do
      let afterSource ←
        sourceStep instr
          { stack := state.source, nextAtom := state.nextAtom }
      let needed ← futureNeeds (rest ++ future) afterSource
      translateChunk rest future
        (← translateInstr instr needed state)

def runtimeInstrCost : Instr → Nat
  | .bindLocals _ _ | .bindScratch _ _ _ | .relabel _ => 0
  | .unwind target => target.length
  | _ => 1

def runtimeBodyCost (body : List Instr) : Nat :=
  body.foldl (fun total instr => total + runtimeInstrCost instr) 0

def chainStep (program : Program) (left right : Block) : Bool :=
  decide
    (left.term = .jump right.label ∧
      refCount program right.label = 1 ∧
      right.label ≠ program.entry)

def growChain (program : Program) : Block → List Block → List Block
  | block, [] => [block]
  | block, next :: rest =>
      if chainStep program block next then
        block :: growChain program next rest
      else
        [block]

partial def distribute? : List Block → Shape → State →
    Option (List Block)
  | [], _, _ => some []
  | [block], input, state => do
      if state.target.code.isEmpty then pure () else none
      let after ← translateChunk block.body [] state
      let target ← reconcile after.source after.target
      let body := target.code ++ [.relabel block.output]
      if Block.bodyType? body input = some block.output then
        pure ()
      else
        none
      some [{ block with input, body }]
  | block :: next :: rest, input, state => do
      if state.target.code.isEmpty then pure () else none
      let future := (next :: rest).flatMap Block.body
      let after ← translateChunk block.body future state
      let body := after.target.code
      let output ← Block.bodyType? body input
      if after.source.length = block.output.length then pure () else none
      if after.target.stack.length = output.length then pure () else none
      let tailState :=
        { after with target := { after.target with code := [] } }
      let tail ← distribute? (next :: rest) output tailState
      some ({ block with input, body, output } :: tail)

def candidateCore? (chain : List Block) : Option (List Block) := do
  let head ← chain.head?
  let atoms := List.range head.input.length
  distribute? chain head.input
    { source := atoms
      target := { stack := atoms }
      nextAtom := atoms.length }

structure BlockTrace where
  label : Label
  sourceInput : List Atom
  targetInput : List Atom
  sourceOutput : List Atom
  targetOutput : List Atom
  nextAtomIn : Nat
  nextAtomOut : Nat
  events : List Event
  deriving DecidableEq, Repr

structure TracePair where
  source : List Atom
  target : List Atom
  nextAtom : Nat
  deriving DecidableEq, Repr

def certifyBlocks? : List Block → List Block → TracePair →
    Option (List BlockTrace × TracePair)
  | [], [], state => some ([], state)
  | source :: sourceRest, target :: targetRest, state => do
      if source.label = target.label ∧ source.term = target.term then
        pure ()
      else
        none
      let sourceAfter ←
        traceBody source.body
          { stack := state.source, nextAtom := state.nextAtom }
      let targetAfter ←
        traceBody target.body
          { stack := state.target, nextAtom := state.nextAtom }
      if sourceAfter.events = targetAfter.events ∧
          sourceAfter.nextAtom = targetAfter.nextAtom then
        pure ()
      else
        none
      let blockTrace : BlockTrace :=
        { label := source.label
          sourceInput := state.source
          targetInput := state.target
          sourceOutput := sourceAfter.stack
          targetOutput := targetAfter.stack
          nextAtomIn := state.nextAtom
          nextAtomOut := sourceAfter.nextAtom
          events := sourceAfter.events }
      let (tail, final) ←
        certifyBlocks? sourceRest targetRest
          { source := sourceAfter.stack
            target := targetAfter.stack
            nextAtom := sourceAfter.nextAtom }
      some (blockTrace :: tail, final)
  | _, _, _ => none

structure Certificate where
  blocks : List BlockTrace
  final : TracePair
  deriving DecidableEq, Repr

def certify? (source target : List Block) : Option Certificate := do
  let head ← source.head?
  let atoms := List.range head.input.length
  let (blocks, final) ←
    certifyBlocks? source target
      { source := atoms, target := atoms, nextAtom := atoms.length }
  if final.source = final.target then pure () else none
  some { blocks, final }

/--
Erase only the exact residual forms produced by virtual-stack generation.
No attempt is made to commute arbitrary operations or to see through
annotations.
-/
def cleanupObservedCommBody : List Instr → List Instr
  | .swap 0 :: .prim op :: rest =>
      if traceCommutative? op then
        .prim op :: cleanupObservedCommBody rest
      else
        .swap 0 :: cleanupObservedCommBody (.prim op :: rest)
  | instr :: rest => instr :: cleanupObservedCommBody rest
  | [] => []

/--
Fail closed on typing: a changed body is retained only when it computes the
block's exact original output shape from the exact original input shape.
-/
def cleanupObservedCommBlock? (block : Block) : Option Block := do
  let body := cleanupObservedCommBody block.body
  if body = block.body then
    some block
  else if Block.bodyType? body block.input = some block.output then
    some { block with body }
  else
    none

def cleanupObservedCommBlocks? :
    List Block → Option (List Block)
  | [] => some []
  | block :: rest => do
      let block ← cleanupObservedCommBlock? block
      let rest ← cleanupObservedCommBlocks? rest
      some (block :: rest)

def candidate? (source : List Block) : Option (List Block) := do
  let candidate ← candidateCore? source
  let _ ← certify? source candidate
  some candidate

def blocksCost (blocks : List Block) : Nat :=
  runtimeBodyCost (blocks.flatMap Block.body)

/-!
The virtual scheduler can leave a transport identity split exactly across its
one pending block boundary:

* `DUPn | POP`;
* `DUPn | SWAPn POP`.

Both sequences restore the stack at the right block's exit.  Removing them
inside either block would require moving an instruction across a control-flow
edge, so the ordinary block-local peephole pass cannot see them.

`cleanupBoundaryOnce?` is deliberately structural and fail-closed.  It only
edits a literal tail/head match, re-runs the block type checker on both edited
bodies, and requires the right output shape to remain exact.  The production
pair constructor subsequently replays the independent event/atom trace
certificate over the cleaned pair as a second semantic check.
-/
def splitLastRuntimeRev? :
    List Instr → List Instr →
      Option (List Instr × Instr × List Instr)
  | [], _ => none
  | instr :: rest, suffix =>
      if runtimeInstrCost instr = 0 then
        splitLastRuntimeRev? rest (instr :: suffix)
      else
        some (rest.reverse, instr, suffix)

def splitLastRuntime? (body : List Instr) :
    Option (List Instr × Instr × List Instr) :=
  splitLastRuntimeRev? body.reverse []

def splitFirstRuntime? :
    List Instr → Option (List Instr × Instr × List Instr)
  | [] => none
  | instr :: rest =>
      if runtimeInstrCost instr = 0 then
        match splitFirstRuntime? rest with
        | none => none
        | some (metadata, runtime, suffix) =>
            some (instr :: metadata, runtime, suffix)
      else
        some ([], instr, rest)

def typedBoundaryCandidate? (left right : Block)
    (leftBody rightBody : List Instr) : Option (Block × Block) :=
  match Block.bodyType? leftBody left.input with
  | none => none
  | some middle =>
      match Block.bodyType? rightBody middle with
      | none => none
      | some output =>
          if output = right.output then
            some
              ( { left with body := leftBody, output := middle }
              , { right with
                  input := middle
                  body := rightBody
                  output := output } )
          else
            none

def cleanupDropBoundaryOnce? (left right : Block) :
    Option (Block × Block) := do
  let (leftBeforePop, leftRuntime, leftSuffix) ←
    splitLastRuntime? left.body
  if leftRuntime = .pop then pure () else none
  let (leftPrefix, leftSwap, leftMiddle) ←
    splitLastRuntime? leftBeforePop
  if leftSwap = .swap 0 then pure () else none
  let (rightPrefix, rightRuntime, rightRest) ←
    splitFirstRuntime? right.body
  match rightRuntime with
  | .pop =>
      typedBoundaryCandidate? left right
        (leftPrefix ++ leftMiddle ++ .pop :: leftSuffix)
        right.body
  | .swap depth =>
      let (rightMiddle, rightSecond, rightSuffix) ←
        splitFirstRuntime? rightRest
      if rightSecond = .pop then
        typedBoundaryCandidate? left right
          (leftPrefix ++ .swap (depth + 1) :: leftMiddle ++
            .pop :: leftSuffix)
          (rightPrefix ++ rightMiddle ++ .pop :: rightSuffix)
      else
        none
  | _ => none

def cleanupTransportBoundaryOnce? (left right : Block) :
    Option (Block × Block) := do
  let (leftPrefix, leftRuntime, leftSuffix) ←
    splitLastRuntime? left.body
  match leftRuntime with
  | .dup leftDepth =>
      let leftBody := leftPrefix
      let (rightPrefix, rightRuntime, rightRest) ←
        splitFirstRuntime? right.body
      match rightRuntime with
      | .pop =>
          typedBoundaryCandidate? left right
            leftBody rightRest
      | .swap rightDepth =>
          if leftDepth = rightDepth then
            let (middleMeta, secondRuntime, rightSuffix) ←
              splitFirstRuntime? rightRest
            match secondRuntime with
            | .pop =>
                typedBoundaryCandidate? left right leftBody
                  rightSuffix
            | _ => none
          else
            none
      | _ => none
  | _ => none

def cleanupBoundaryOnce? (left right : Block) : Option (Block × Block) :=
  match cleanupDropBoundaryOnce? left right with
  | some cleaned => some cleaned
  | none => cleanupTransportBoundaryOnce? left right

def cleanupBoundary : Nat → Block → Block → Block × Block
  | 0, left, right => (left, right)
  | fuel + 1, left, right =>
      match cleanupBoundaryOnce? left right with
      | none => (left, right)
      | some (cleanLeft, cleanRight) =>
          cleanupBoundary fuel cleanLeft cleanRight

def cleanupPairCandidate? (source : List Block) : Option (List Block) :=
  match source with
  | [left, right] =>
      let (cleanLeft, cleanRight) :=
        cleanupBoundary left.body.length left right
      let candidate := [cleanLeft, cleanRight]
      if blocksCost candidate < blocksCost source then
        some candidate
      else
        none
  | _ => none

def hasRuntimeEvent (block : Block) : Bool :=
  block.body.any fun instr =>
    match instr with
    | .dup _ | .push _ | .returnToken _ | .prim _ => true
    | _ => false

def cleanupCandidate? (source : List Block) : Option (List Block) := do
  let candidate ← cleanupPairCandidate? source
  let _ ← certify? source candidate
  some candidate

def pairCandidateCore? (source : List Block) : Option (List Block) :=
  let scheduled :=
    match source.head? with
    | some left =>
        if hasRuntimeEvent left then
          candidate? source
        else
          none
    | none => none
  match cleanupCandidate? source, scheduled with
  | some cleaned, some scheduled =>
      -- Preserve the established scheduler on exact cost ties.
      if blocksCost scheduled ≤ blocksCost cleaned then
        some scheduled
      else
        some cleaned
  | some cleaned, none => some cleaned
  | none, some scheduled => some scheduled
  | none, none => none

def pairCandidate? (source : List Block) : Option (List Block) := do
  let candidate ← pairCandidateCore? source
  cleanupObservedCommBlocks? candidate

def pairEligible (left right : Block) : Bool :=
  hasRuntimeEvent left

/-!
The production transform deliberately uses pairs rather than arbitrary-length
chains.  Measurements retain most of the distributed win, while the semantic
invariant has exactly one pending boundary: the left block creates it and the
right block must discharge it.

The full source, target, and independently checked trace certificate are kept
in the edit witness.  They are proof data only; `applyEdit` projects the target
block fields used by compilation.
-/
structure PairChoice where
  sourceLeft : Block
  sourceRight : Block
  targetLeft : Block
  targetRight : Block
  certificate : Certificate
  savings : Nat
  deriving Repr

def pairChoice? (program : Program) (left right : Block) :
    Option PairChoice := do
  if pairEligible left right then pure () else none
  if chainStep program left right then pure () else none
  let candidate ← pairCandidate? [left, right]
  let certificate ← certify? [left, right] candidate
  match candidate with
  | [targetLeft, targetRight] =>
      if targetLeft.input = left.input ∧
          targetLeft.output = targetRight.input ∧
          targetRight.output = right.output then
        pure ()
      else
        none
      let oldCost := blocksCost [left, right]
      let newCost := blocksCost [targetLeft, targetRight]
      if newCost < oldCost then
        some
          { sourceLeft := left
            sourceRight := right
            targetLeft
            targetRight
            certificate
            savings := oldCost - newCost }
      else
        none
  | _ => none

inductive Edit where
  | left (choice : PairChoice)
  | right (choice : PairChoice)
  deriving Repr

def PairChoice.edits (choice : PairChoice) : List (Label × Edit) :=
  [ (choice.sourceLeft.label, .left choice)
  , (choice.sourceRight.label, .right choice) ]

def scanEdits (program : Program) : Nat → List Block →
    List (Label × Edit)
  | 0, _ | _, [] | _, [_] => []
  | fuel + 1, left :: right :: rest =>
      match pairChoice? program left right with
      | some choice =>
          choice.edits ++
            scanEdits program fuel rest
      | none =>
          scanEdits program fuel (right :: rest)

def editTable (program : Program) : List (Label × Edit) :=
  match program.blocksInLoweringOrder? with
  | none => []
  | some ordered =>
      scanEdits program program.blocks.length ordered

def applyEdit (edits : List (Label × Edit)) (block : Block) : Block :=
  match edits.lookup block.label with
  | none => block
  | some (.left choice) =>
      { block with
        input := choice.targetLeft.input
        body := choice.targetLeft.body
        output := choice.targetLeft.output }
  | some (.right choice) =>
      { block with
        input := choice.targetRight.input
        body := choice.targetRight.body
        output := choice.targetRight.output }

def canonProgramOnce (program : Program) : Program :=
  let edits := editTable program
  { program with blocks := program.blocks.map (applyEdit edits) }

@[simp] theorem applyEdit_label (edits : List (Label × Edit))
    (block : Block) :
    (applyEdit edits block).label = block.label := by
  unfold applyEdit
  split <;> rfl

@[simp] theorem applyEdit_term (edits : List (Label × Edit))
    (block : Block) :
    (applyEdit edits block).term = block.term := by
  unfold applyEdit
  split <;> rfl

@[simp] theorem canonProgramOnce_entry (program : Program) :
    (canonProgramOnce program).entry = program.entry := rfl

@[simp] theorem canonProgramOnce_blocks (program : Program) :
    (canonProgramOnce program).blocks =
      program.blocks.map (applyEdit (editTable program)) := rfl

theorem canonProgramOnce_block_labels (program : Program) :
    (canonProgramOnce program).blocks.map Block.label =
      program.blocks.map Block.label := by
  simp

/-!
The first scheduling sweep deliberately chooses disjoint adjacent pairs.  A
successful edit can therefore expose a transport identity only at the seam to
the next pair.  A second certified sweep sees those final-program seams.  Its
candidate chooser gives an exact boundary cleanup priority over another
virtual scheduling candidate, and every accepted edit is independently
retyped, trace-certified, and required to be strictly cheaper.
-/
def secondSweepEligible (program : Program) : Bool :=
  program.wellTyped? && program.programCounterIndependent?

def canonProgram (program : Program) : Program :=
  let scheduled := canonProgramOnce program
  { program with
    blocks :=
      if secondSweepEligible scheduled then
        (canonProgramOnce scheduled).blocks
      else
        scheduled.blocks }

@[simp] theorem canonProgram_entry (program : Program) :
    (canonProgram program).entry = program.entry := rfl

theorem canonProgram_eq_double
    {program : Program}
    (hEligible :
      secondSweepEligible (canonProgramOnce program) = true) :
    canonProgram program =
      canonProgramOnce (canonProgramOnce program) := by
  simp only [canonProgram, hEligible, if_true]
  rfl

theorem canonProgram_eq_once
    {program : Program}
    (hEligible :
      secondSweepEligible (canonProgramOnce program) = false) :
    canonProgram program = canonProgramOnce program := by
  simp only [canonProgram, hEligible, if_false]
  rfl

theorem canonProgram_block_labels (program : Program) :
    (canonProgram program).blocks.map Block.label =
      program.blocks.map Block.label := by
  by_cases hEligible :
      secondSweepEligible (canonProgramOnce program) = true
  · simp only [canonProgram, hEligible, if_true]
    rw [canonProgramOnce_block_labels,
      canonProgramOnce_block_labels]
  · have hFalse :
        secondSweepEligible (canonProgramOnce program) = false :=
      Bool.eq_false_of_not_eq_true hEligible
    simp only [canonProgram, hFalse, if_false]
    exact canonProgramOnce_block_labels program

end VirtualStack
end TypedCfg
end EvmCompiler
