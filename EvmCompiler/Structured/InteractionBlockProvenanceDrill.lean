import EvmCompiler.Structured.InteractionBlockProvenanceRoot

/-!
# The statement-list provenance DRILL (gate 2 engine, static route)

Session 32 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-31).

`InteractionBlockProvenanceRoot.lean` (session 31) turned `block_category`'s
main-body arm (`block ∈ context.main.blocks`) into the top-level
`compileStmtListFuel?` fact.  This module builds the **drill** that descends from a
`compileStmtListFuel? … = some result` fact plus `block ∈ result.blocks` down to the
*specific source construct* whose `compileStmtFuel?` emitted the block — the
per-construct compile fact the coupling suppliers
(`realizedWitness_of_{if,call,code}_compile`) consume.

The drill is pure syntactic bookkeeping over the compilation recursion: **no
semantics, no fuel-run coupling, no interaction transcript**.  It mirrors the
generation skeleton of `activeResult_of_compile*`
(`TypedCfgCompilerActive.lean`) MINUS the semantic payload — the very same
`head :: bodyResult.blocks` / `head.append tail` membership splits, but carrying a
*provenance* conclusion rather than `ActiveResult`.

## Phase 1 (this file): the one-layer membership dichotomies

For each `compileStmtFuel?` constructor and for the `compileStmtListFuel?`
nil/cons shapes, from `block ∈ result.blocks` recover *where in the emission* the
block sits: the entry-aligned head block, or a member of a named recursive
subfragment (`compileBlockFuel?` body / `compileCasesFuel?` / `compileDefaultFuel?`
result) — returning the subfragment's own compile fact so the drill can recurse.
These are the reusable substrate the assembled descent (and `block_category`'s
consumer) chains.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace BlockProvenanceDrill

open TypedCfgCompiler

/-! ### Statement-list membership dichotomies -/

/--
**Nil statement-list emission.**  Compiling the empty statement list emits exactly
one block — the join block, entry-labelled with a `.jump regular` terminator and an
empty body.  Every block in the result is that join block.
-/
theorem mem_of_compileStmtListFuel?_nil
    {compilerFuel : Nat}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtListFuel? (compilerFuel + 1) [] ctx supply entry input
          regular = some result)
    (hMem : block ∈ result.blocks) :
    block =
      { label := entry
        input := input
        body := []
        output := input
        term := .jump regular } := by
  simp only [compileStmtListFuel?, mkBlock?, TypedCfg.Block.bodyType?] at hCompile
  cases hCompile
  simpa using hMem

/--
**Cons statement-list membership dichotomy.**  A block emitted by compiling
`stmt :: rest` lands either in the head statement's emission or in the tail's — and
in each case the corresponding compile fact is exposed for the drill to recurse on.

Built directly on `components_of_compileStmtListFuel?_cons`
(`Core.lean`): the tail is present iff the head has a regular fallthrough.
-/
theorem mem_of_compileStmtListFuel?_cons
    {compilerFuel : Nat} {stmt : Structured.Stmt}
    {rest : List Structured.Stmt}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtListFuel? (compilerFuel + 1) (stmt :: rest) ctx supply
          entry input regular = some result)
    (hMem : block ∈ result.blocks) :
    (∃ headResult,
      compileStmtFuel? compilerFuel stmt ctx supply entry input
          (restLabel supply) = some headResult ∧
      block ∈ headResult.blocks) ∨
    (∃ headResult tailInput tailResult,
      compileStmtFuel? compilerFuel stmt ctx supply entry input
          (restLabel supply) = some headResult ∧
      headResult.fallthrough? = some tailInput ∧
      compileStmtListFuel? compilerFuel rest (ctx.advance headResult)
          headResult.next (restLabel supply) tailInput regular =
        some tailResult ∧
      block ∈ tailResult.blocks) := by
  rcases Block.components_of_compileStmtListFuel?_cons hCompile with
    ⟨headResult, hHead, hNoTail | hTail⟩
  · rcases hNoTail with ⟨_hFallthrough, rfl⟩
    exact Or.inl ⟨result, hHead, hMem⟩
  · rcases hTail with ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    simp only [Result.append, List.mem_append] at hMem
    rcases hMem with hHeadMem | hTailMem
    · exact Or.inl ⟨headResult, hHead, hHeadMem⟩
    · exact
        Or.inr
          ⟨headResult, tailInput, tailResult, hHead, hFallthrough,
            hTailCompile, hTailMem⟩

/-! ### Per-constructor one-layer membership dichotomies

For each `compileStmtFuel?` constructor, from `block ∈ result.blocks` recover the
block's position in the emission: the entry-aligned head (concluded as
`block.label = entry`, so the incoming `compileStmtFuel?` fact — at that very entry
— is the head's compile fact the suppliers consume), or a member of a named
recursive subfragment, returned with the subfragment's own compile fact so the
drill recurses. -/

/-- **`code` emission.**  A `.code` statement emits exactly its entry head block. -/
theorem mem_of_compileStmtFuel?_code
    {compilerFuel : Nat} {code : Structured.Code}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtFuel? (compilerFuel + 1) (.code code) ctx supply entry input
          regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = entry := by
  obtain ⟨output, _hType, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code hCompile
  simp only [List.mem_singleton] at hMem
  subst hMem
  rfl

/-- **`terminal` emission.**  A `.terminal` statement emits exactly its entry head
block. -/
theorem mem_of_compileStmtFuel?_terminal
    {compilerFuel : Nat} {kind : Assembly.HaltKind}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtFuel? (compilerFuel + 1) (.terminal kind) ctx supply entry
          input regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = entry := by
  obtain ⟨_hSource, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal hCompile
  simp only [List.mem_singleton] at hMem
  subst hMem
  rfl

/-- **`if` emission dichotomy.**  A block emitted by a `.if_` is either the entry
head (condition) block or a member of the compiled branch body — the latter with
its `compileBlockFuel?` fact exposed for recursion. -/
theorem mem_of_compileStmtFuel?_if
    {compilerFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtFuel? (compilerFuel + 1) (.if_ cond body) ctx supply entry
          input regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = entry ∨
    (∃ output bodyResult,
      Code.type? cond input = some output ∧
      compileBlockFuel? compilerFuel body ctx (supply + 1)
          (LabelSupply.label supply 0)
          { output with slots := output.slots.tail } regular =
        some bodyResult ∧
      block ∈ bodyResult.blocks) := by
  obtain
      ⟨output, _condition, bodyResult,
        hType, _hSource, _hHead, hBody, _hRequire, rfl⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
  simp only [List.mem_cons] at hMem
  rcases hMem with rfl | hBodyMem
  · exact Or.inl rfl
  · exact Or.inr ⟨output, bodyResult, hType, hBody, hBodyMem⟩

/-- **`switch` emission dichotomy.**  A block emitted by a `.switch` is the entry
head (scrutinee) block, a member of the compiled cases fragment, or a member of the
compiled default fragment — the latter two with their compile facts exposed. -/
theorem mem_of_compileStmtFuel?_switch
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtFuel? (compilerFuel + 1) (.switch scrutinee cases defaultBody)
          ctx supply entry input regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = entry ∨
    (∃ valueShape caseResult,
      Code.type? scrutinee input = some valueShape ∧
      compileCasesFuel? compilerFuel cases ctx supply (supply + 1) 0 valueShape
          { valueShape with slots := valueShape.slots.tail } regular =
        some caseResult ∧
      block ∈ caseResult.blocks) ∨
    (∃ valueShape caseResult defaultResult,
      Code.type? scrutinee input = some valueShape ∧
      compileCasesFuel? compilerFuel cases ctx supply (supply + 1) 0 valueShape
          { valueShape with slots := valueShape.slots.tail } regular =
        some caseResult ∧
      compileDefaultFuel? compilerFuel defaultBody (ctx.advance caseResult)
          caseResult.next (LabelSupply.label supply 1) valueShape
          { valueShape with slots := valueShape.slots.tail } regular =
        some defaultResult ∧
      block ∈ defaultResult.blocks) := by
  obtain
      ⟨valueShape, _valueSlot, caseResult, defaultResult,
        hType, _hSource, _hValue, hCases, hDefault, rfl⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch hCompile
  simp only [List.mem_cons, List.mem_append] at hMem
  rcases hMem with (rfl | hCaseMem) | hDefaultMem
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨valueShape, caseResult, hType, hCases, hCaseMem⟩)
  · exact
      Or.inr
        (Or.inr
          ⟨valueShape, caseResult, defaultResult, hType, hCases, hDefault,
            hDefaultMem⟩)

/-- **`for` emission dichotomy.**  A block emitted by a `.for_` lands in the
compiled init fragment, is the loop-condition head block, lands in the compiled
body fragment, or lands in the compiled post fragment — each recursive fragment
returned with its `compileBlockFuel?` fact. -/
theorem mem_of_compileStmtFuel?_for
    {compilerFuel : Nat} {init post body : Structured.Block}
    {cond : Structured.Code} {ctx : Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtFuel? (compilerFuel + 1) (.for_ init cond post body) ctx
          supply entry input regular = some result)
    (hMem : block ∈ result.blocks) :
    (∃ initResult,
      compileBlockFuel? compilerFuel init
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          (supply + 1) entry input (LabelSupply.label supply 0) =
        some initResult ∧
      block ∈ initResult.blocks) ∨
    block.label = LabelSupply.label supply 0 ∨
    (∃ initResult loopInput condOutput bodyResult,
      compileBlockFuel? compilerFuel init
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          (supply + 1) entry input (LabelSupply.label supply 0) =
        some initResult ∧
      initResult.fallthrough? = some loopInput ∧
      Code.type? cond loopInput = some condOutput ∧
      compileBlockFuel? compilerFuel body
          { ctx with
            breakLabel? := some regular
            breakShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            continueLabel? := some (LabelSupply.label supply 2)
            continueShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            callBase := ctx.callBase + initResult.calls.length }
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) =
        some bodyResult ∧
      block ∈ bodyResult.blocks) ∨
    (∃ initResult loopInput condOutput bodyResult postResult,
      compileBlockFuel? compilerFuel init
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          (supply + 1) entry input (LabelSupply.label supply 0) =
        some initResult ∧
      initResult.fallthrough? = some loopInput ∧
      Code.type? cond loopInput = some condOutput ∧
      compileBlockFuel? compilerFuel body
          { ctx with
            breakLabel? := some regular
            breakShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            continueLabel? := some (LabelSupply.label supply 2)
            continueShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            callBase := ctx.callBase + initResult.calls.length }
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) =
        some bodyResult ∧
      compileBlockFuel? compilerFuel post
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none
            callBase :=
              ctx.callBase + initResult.calls.length +
                bodyResult.calls.length }
          bodyResult.next (LabelSupply.label supply 2)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 0) =
        some postResult ∧
      block ∈ postResult.blocks) := by
  obtain
      ⟨initResult, loopInput, condOutput, _condition,
        bodyResult, postResult, hInit, hInitFallthrough,
        hType, _hSource, _hHead, hBody, _hBodyRequire,
        hPost, _hPostRequire, rfl⟩ :=
    TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for hCompile
  rcases List.mem_append.mp hMem with hBeforePost | hPostMem
  · rcases List.mem_append.mp hBeforePost with hBeforeBody | hBodyMem
    · rcases List.mem_append.mp hBeforeBody with hInitMem | hLoopMem
      · exact Or.inl ⟨initResult, hInit, hInitMem⟩
      · refine Or.inr (Or.inl ?_)
        simp only [List.mem_singleton] at hLoopMem
        subst hLoopMem
        rfl
    · exact
        Or.inr (Or.inr (Or.inl
          ⟨initResult, loopInput, condOutput, bodyResult,
            hInit, hInitFallthrough, hType, hBody, hBodyMem⟩))
  · exact
      Or.inr (Or.inr (Or.inr
        ⟨initResult, loopInput, condOutput, bodyResult, postResult,
          hInit, hInitFallthrough, hType, hBody, hPost, hPostMem⟩))

/-! ### Block / cases / default connectors

The remaining three generation functions of the mutual: `compileBlockFuel?` (the
vertical descent into `if`/`for` bodies) unfolds to a `compileStmtListFuel?`, and
`compileCasesFuel?` / `compileDefaultFuel?` (the horizontal descent within a
`switch`) split off their machinery blocks (test / case-entry / default `pop`
blocks) from the recursive case-body fragments. -/

/-- **`compileBlockFuel?` connector.**  A successful block compilation is exactly a
statement-list compilation of the block's statements at one less fuel — the vertical
descent step through `if` / `for` / case bodies. -/
theorem stmtList_of_compileBlockFuel?
    {compilerFuel : Nat} {body : Structured.Block}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result}
    (hCompile :
      compileBlockFuel? (compilerFuel + 1) body ctx supply entry input
          regular = some result) :
    compileStmtListFuel? compilerFuel body.stmts ctx supply entry input
        regular = some result := by
  unfold compileBlockFuel? at hCompile
  exact hCompile

/-- **`compileCasesFuel?` nil emission.**  Compiling an empty case list emits no
blocks; membership is vacuous. -/
theorem mem_of_compileCasesFuel?_nil
    {compilerFuel : Nat} {ctx : Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileCasesFuel? (compilerFuel + 1) [] ctx base supply idx valueShape
          bodyShape regular = some result)
    (hMem : block ∈ result.blocks) :
    False := by
  simp only [compileCasesFuel?] at hCompile
  cases hCompile
  simp at hMem

/-- **`compileCasesFuel?` cons membership dichotomy.**  A block emitted for a
non-empty case list is the case's test-comparison block, its case-entry (`pop`)
block, a member of the compiled case body, or a member of the remaining cases —
each recursive fragment returned with its compile fact. -/
theorem mem_of_compileCasesFuel?_cons
    {compilerFuel : Nat} {caseValue : Word} {body : Structured.Block}
    {rest : List (Word × Structured.Block)}
    {ctx : Context} {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : Result} {block : TypedCfg.Block}
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      compileCasesFuel? (compilerFuel + 1) ((caseValue, body) :: rest) ctx
          base supply idx valueShape bodyShape regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = switchTestLabel base idx ∨
    block.label = switchCaseLabel base idx ∨
    (∃ bodyResult,
      compileBlockFuel? compilerFuel body ctx supply
          (switchBodyLabel base idx) bodyShape regular = some bodyResult ∧
      block ∈ bodyResult.blocks) ∨
    (∃ bodyResult tail,
      compileBlockFuel? compilerFuel body ctx supply
          (switchBodyLabel base idx) bodyShape regular = some bodyResult ∧
      compileCasesFuel? compilerFuel rest (ctx.advance bodyResult) base
          bodyResult.next (idx + 1) valueShape bodyShape regular = some tail ∧
      block ∈ tail.blocks) := by
  obtain ⟨bodyResult, tail, hBody, _hRequire, hTail, rfl⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons hHead hPopType
      hCompile
  rcases List.mem_cons.mp hMem with hTest | hMem1
  · exact Or.inl (by rw [hTest])
  rcases List.mem_cons.mp hMem1 with hCase | hMem2
  · exact Or.inr (Or.inl (by rw [hCase]))
  rcases List.mem_append.mp hMem2 with hBodyMem | hTailMem
  · exact Or.inr (Or.inr (Or.inl ⟨bodyResult, hBody, hBodyMem⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨bodyResult, tail, hBody, hTail, hTailMem⟩))

/-- **`compileDefaultFuel?` (no default) emission.**  An absent default emits the
single entry `pop` block. -/
theorem mem_of_compileDefaultFuel?_none
    {compilerFuel : Nat} {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {valueShape bodyShape : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      compileDefaultFuel? (compilerFuel + 1) none ctx supply entry valueShape
          bodyShape regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = entry := by
  rw [TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_none hPopType
      hCompile] at hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  rfl

/-- **`compileDefaultFuel?` (with default) membership dichotomy.**  A present
default is the entry `pop` block or a member of the compiled default body — the
latter with its compile fact. -/
theorem mem_of_compileDefaultFuel?_some
    {compilerFuel : Nat} {body : Structured.Block} {ctx : Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      compileDefaultFuel? (compilerFuel + 1) (some body) ctx supply entry
          valueShape bodyShape regular = some result)
    (hMem : block ∈ result.blocks) :
    block.label = entry ∨
    (∃ bodyResult,
      compileBlockFuel? compilerFuel body ctx (supply + 1)
          (.generated supply 2000) bodyShape regular = some bodyResult ∧
      block ∈ bodyResult.blocks) := by
  obtain ⟨bodyResult, hBody, _hRequire, rfl⟩ :=
    TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some hPopType
      hCompile
  simp only [List.mem_cons] at hMem
  rcases hMem with rfl | hBodyMem
  · exact Or.inl rfl
  · exact Or.inr ⟨bodyResult, hBody, hBodyMem⟩

end BlockProvenanceDrill
end TypedCfgPreservation
end Structured
end EvmCompiler
