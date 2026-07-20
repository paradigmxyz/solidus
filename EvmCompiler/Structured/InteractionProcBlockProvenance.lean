import EvmCompiler.Structured.InteractionBlockProvenanceRoot

/-!
# Proc-body block-provenance ROOT (membership inversion over `lowerProcBodiesWithShapes?`)

Session 34 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-33,
frontier item 2).

`block_category` (`InteractionBlockProvenance.lean:79`) splits a reached entry's
block into the four generated categories; `main_stmtList_provenance`
(`InteractionBlockProvenanceRoot.lean:49`) turned the main-body arm into a
top-level `compileStmtListFuel?` compile fact.  This module supplies the
**proc-body** analogue: the reverse of
`procFragment_of_lowerProcBodiesWithShapes?` (`Core.lean:3049`).

Whereas the forward `procFragment_of_lowerProcBodiesWithShapes?` is keyed on a
*name lookup* and produces a fragment, the invariant needs the opposite: from
`block ∈ context.procBlocks` (`block_category`'s second arm) recover *which* proc
generated the block, and *how* — either the block IS that proc's entry ADAPTER
(finding 2, session 33; classified into the adapter machinery disjunct feeding
`realizedWitness_of_adapter_jump`), or it is a member of that proc's compiled body
`compileBlock? proc.body …` (feeding the assembled body drill exactly as the main
root feeds it).

The generic lemma `mem_procBlocks_provenance` mirrors the forward proof's
induction over `lowerProcBodiesWithShapes?` (adapter / no-adapter × shape-present /
absent), tracking `procBlocks = body.blocks ++ tailBlocks` with
`body.blocks = compiled.blocks` (no adapter) or `adapter :: compiled.blocks`
(adapter route, `TypedCfgCompiler.lean:677`).  The context wrapper
`GeneratedContext.procBlocks_provenance` specialises it at
`allProcs = procs = source.procs` via `context.procsCompile`.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace Program

/--
**Membership inversion over `lowerProcBodiesWithShapes?`.**

Every block in a successful recursive procedure lowering's output block list is,
for some procedure `proc` in the lowered list, either a member of that procedure's
compiled body (`compileBlock? proc.body …`) or that procedure's entry ADAPTER
(the `.relabel`-then-`.jump` block `mkBlock? (ProcLabel.entry proc.name) …`).

This is the reverse of `procFragment_of_lowerProcBodiesWithShapes?`; it mirrors the
same induction (adapter / no-adapter × shape-present / absent) but keyed on block
membership rather than a name lookup.  `proc ∈ procs` (not a `lookup?` fact) is
surfaced because a block only pins its generating procedure up to list membership;
that suffices for both the adapter supplier (`realizedWitness_of_adapter_jump`,
which is shape-generic) and the body drill (which consumes the compile fact). -/
theorem mem_procBlocks_provenance
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs procs : List Structured.Proc}
    {supply next : LabelSupply}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (hLower :
      TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes allProcs procs
          supply =
        some (procBlocks, next, procCalls))
    {block : TypedCfg.Block}
    (hMem : block ∈ procBlocks) :
    ∃ (proc : Structured.Proc) (bsupply : LabelSupply)
      (entry : Assembly.Label) (input : TypedCfg.Shape)
      (bodyResult : TypedCfgCompiler.Result),
      proc ∈ procs ∧
      TypedCfgCompiler.compileBlock? proc.body
          { procs := allProcs
            leaveLabel? := some (ProcLabel.exit proc.name)
            leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
          bsupply entry input (ProcLabel.exit proc.name) = some bodyResult ∧
      (block ∈ bodyResult.blocks ∨
        TypedCfgCompiler.mkBlock? (ProcLabel.entry proc.name)
            (TypedCfgCompiler.Shape.procEntry proc) [.relabel input]
            (.jump (ProcLabel.body proc.name)) = some block) := by
  induction procs generalizing supply next procBlocks procCalls with
  | nil =>
      simp only [TypedCfgCompiler.lowerProcBodiesWithShapes?, Option.some.injEq,
        Prod.mk.injEq] at hLower
      obtain ⟨hb, -, -⟩ := hLower
      subst hb
      simp at hMem
  | cons head rest ih =>
      unfold TypedCfgCompiler.lowerProcBodiesWithShapes? at hLower
      cases hShape : entryShapes.find? head.name with
      | none =>
          cases hBody :
              TypedCfgCompiler.compileBlock? head.body
                { procs := allProcs
                  leaveLabel? := some (ProcLabel.exit head.name)
                  leaveShape? :=
                    some (TypedCfgCompiler.Shape.procExit head) }
                supply (ProcLabel.entry head.name)
                (TypedCfgCompiler.Shape.procEntry head)
                (ProcLabel.exit head.name) with
          | none =>
              simp [hShape, hBody] at hLower
          | some compiled =>
              cases hRequire :
                  compiled.requireFallthrough?
                    (TypedCfgCompiler.Shape.procExit head) with
              | none =>
                  simp [hShape, hBody, hRequire] at hLower
              | some unit =>
                  cases unit
                  cases hTail :
                      TypedCfgCompiler.lowerProcBodiesWithShapes?
                        entryShapes allProcs rest compiled.next with
                  | none =>
                      simp [hShape, hBody, hRequire, hTail] at hLower
                  | some tailResult =>
                      rcases tailResult with ⟨tailBlocks, tailNext, tailCalls⟩
                      simp [hShape, hBody, hRequire, hTail] at hLower
                      rcases hLower with ⟨rfl, rfl, rfl⟩
                      simp only [List.mem_append] at hMem
                      rcases hMem with hHere | hThere
                      · exact
                          ⟨head, supply, ProcLabel.entry head.name,
                            TypedCfgCompiler.Shape.procEntry head, compiled,
                            List.mem_cons_self, hBody, Or.inl hHere⟩
                      · obtain
                          ⟨proc, bsupply, e, input, bodyResult,
                            hProcMem, hCompile, hDisj⟩ :=
                          ih hTail hThere
                        exact
                          ⟨proc, bsupply, e, input, bodyResult,
                            List.mem_cons_of_mem head hProcMem, hCompile, hDisj⟩
      | some bodyInput =>
          cases hFrame :
              TypedCfgCompiler.Shape.requireReturnTokenDepth?
                head.argc bodyInput with
          | none =>
              simp [hShape, hFrame] at hLower
          | some unit =>
              cases unit
              cases hAdapter :
                  TypedCfgCompiler.mkBlock?
                    (ProcLabel.entry head.name)
                    (TypedCfgCompiler.Shape.procEntry head)
                    [.relabel bodyInput]
                    (.jump (ProcLabel.body head.name)) with
              | none =>
                  simp [hShape, hFrame, hAdapter] at hLower
              | some adapter =>
                  cases hBody :
                      TypedCfgCompiler.compileBlock? head.body
                        { procs := allProcs
                          leaveLabel? := some (ProcLabel.exit head.name)
                          leaveShape? :=
                            some (TypedCfgCompiler.Shape.procExit head) }
                        supply (ProcLabel.body head.name) bodyInput
                        (ProcLabel.exit head.name) with
                  | none =>
                      simp [hShape, hFrame, hAdapter, hBody] at hLower
                  | some compiled =>
                      cases hRequire :
                          compiled.requireFallthrough?
                            (TypedCfgCompiler.Shape.procExit head) with
                      | none =>
                          simp [hShape, hFrame, hAdapter, hBody, hRequire]
                            at hLower
                      | some unit =>
                          cases unit
                          cases hTail :
                              TypedCfgCompiler.lowerProcBodiesWithShapes?
                                entryShapes allProcs rest compiled.next with
                          | none =>
                              simp [hShape, hFrame, hAdapter, hBody, hRequire,
                                hTail] at hLower
                          | some tailResult =>
                              rcases tailResult with
                                ⟨tailBlocks, tailNext, tailCalls⟩
                              simp [hShape, hFrame, hAdapter, hBody, hRequire,
                                hTail] at hLower
                              rcases hLower with ⟨rfl, rfl, rfl⟩
                              simp only [List.cons_append, List.mem_cons,
                                List.mem_append] at hMem
                              rcases hMem with hEq | hIn | hThere
                              · exact
                                  ⟨head, supply, ProcLabel.body head.name,
                                    bodyInput, compiled,
                                    List.mem_cons_self, hBody,
                                    Or.inr (by rw [hEq]; exact hAdapter)⟩
                              · exact
                                  ⟨head, supply, ProcLabel.body head.name,
                                    bodyInput, compiled,
                                    List.mem_cons_self, hBody, Or.inl hIn⟩
                              · obtain
                                  ⟨proc, bsupply, e, input, bodyResult,
                                    hProcMem, hCompile, hDisj⟩ :=
                                  ih hTail hThere
                                exact
                                  ⟨proc, bsupply, e, input, bodyResult,
                                    List.mem_cons_of_mem head hProcMem,
                                    hCompile, hDisj⟩

/--
**Membership inversion over `lowerProcBodiesWithShapes?`, strengthened with the
body-block `⊆ procBlocks` inclusion.**

Identical to `mem_procBlocks_provenance` but additionally emits `∀ b ∈
bodyResult.blocks, b ∈ procBlocks` — the fact needed to promote the local
`compileBlock? proc.body … = some bodyResult` compile fact to a
`BlocksInProgram bodyResult cfg` fact (via `procBlocks ⊆ cfg.blocks` and
`LabelsUnique`), so the body drill `genShape_of_compileBlock?` applies.  The
induction already tracks `procBlocks = body.blocks ++ tailBlocks` with
`body.blocks = compiled.blocks` (no adapter) or `adapter :: compiled.blocks`
(adapter route), so in every leaf the returned `bodyResult = compiled` has
`compiled.blocks ⊆ procBlocks`; the recursive arm composes through `tailBlocks ⊆
procBlocks`. -/
theorem mem_procBlocks_provenance_subset
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs procs : List Structured.Proc}
    {supply next : LabelSupply}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (hLower :
      TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes allProcs procs
          supply =
        some (procBlocks, next, procCalls))
    {block : TypedCfg.Block}
    (hMem : block ∈ procBlocks) :
    ∃ (proc : Structured.Proc) (bsupply : LabelSupply)
      (entry : Assembly.Label) (input : TypedCfg.Shape)
      (bodyResult : TypedCfgCompiler.Result),
      proc ∈ procs ∧
      TypedCfgCompiler.compileBlock? proc.body
          { procs := allProcs
            leaveLabel? := some (ProcLabel.exit proc.name)
            leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
          bsupply entry input (ProcLabel.exit proc.name) = some bodyResult ∧
      (∀ b, b ∈ bodyResult.blocks → b ∈ procBlocks) ∧
      (block ∈ bodyResult.blocks ∨
        TypedCfgCompiler.mkBlock? (ProcLabel.entry proc.name)
            (TypedCfgCompiler.Shape.procEntry proc) [.relabel input]
            (.jump (ProcLabel.body proc.name)) = some block) := by
  induction procs generalizing supply next procBlocks procCalls with
  | nil =>
      simp only [TypedCfgCompiler.lowerProcBodiesWithShapes?, Option.some.injEq,
        Prod.mk.injEq] at hLower
      obtain ⟨hb, -, -⟩ := hLower
      subst hb
      simp at hMem
  | cons head rest ih =>
      unfold TypedCfgCompiler.lowerProcBodiesWithShapes? at hLower
      cases hShape : entryShapes.find? head.name with
      | none =>
          cases hBody :
              TypedCfgCompiler.compileBlock? head.body
                { procs := allProcs
                  leaveLabel? := some (ProcLabel.exit head.name)
                  leaveShape? :=
                    some (TypedCfgCompiler.Shape.procExit head) }
                supply (ProcLabel.entry head.name)
                (TypedCfgCompiler.Shape.procEntry head)
                (ProcLabel.exit head.name) with
          | none =>
              simp [hShape, hBody] at hLower
          | some compiled =>
              cases hRequire :
                  compiled.requireFallthrough?
                    (TypedCfgCompiler.Shape.procExit head) with
              | none =>
                  simp [hShape, hBody, hRequire] at hLower
              | some unit =>
                  cases unit
                  cases hTail :
                      TypedCfgCompiler.lowerProcBodiesWithShapes?
                        entryShapes allProcs rest compiled.next with
                  | none =>
                      simp [hShape, hBody, hRequire, hTail] at hLower
                  | some tailResult =>
                      rcases tailResult with ⟨tailBlocks, tailNext, tailCalls⟩
                      simp [hShape, hBody, hRequire, hTail] at hLower
                      rcases hLower with ⟨rfl, rfl, rfl⟩
                      simp only [List.mem_append] at hMem
                      rcases hMem with hHere | hThere
                      · exact
                          ⟨head, supply, ProcLabel.entry head.name,
                            TypedCfgCompiler.Shape.procEntry head, compiled,
                            List.mem_cons_self, hBody,
                            (fun b hb => List.mem_append_left _ hb),
                            Or.inl hHere⟩
                      · obtain
                          ⟨proc, bsupply, e, input, bodyResult,
                            hProcMem, hCompile, hSub, hDisj⟩ :=
                          ih hTail hThere
                        exact
                          ⟨proc, bsupply, e, input, bodyResult,
                            List.mem_cons_of_mem head hProcMem, hCompile,
                            (fun b hb => List.mem_append_right _ (hSub b hb)),
                            hDisj⟩
      | some bodyInput =>
          cases hFrame :
              TypedCfgCompiler.Shape.requireReturnTokenDepth?
                head.argc bodyInput with
          | none =>
              simp [hShape, hFrame] at hLower
          | some unit =>
              cases unit
              cases hAdapter :
                  TypedCfgCompiler.mkBlock?
                    (ProcLabel.entry head.name)
                    (TypedCfgCompiler.Shape.procEntry head)
                    [.relabel bodyInput]
                    (.jump (ProcLabel.body head.name)) with
              | none =>
                  simp [hShape, hFrame, hAdapter] at hLower
              | some adapter =>
                  cases hBody :
                      TypedCfgCompiler.compileBlock? head.body
                        { procs := allProcs
                          leaveLabel? := some (ProcLabel.exit head.name)
                          leaveShape? :=
                            some (TypedCfgCompiler.Shape.procExit head) }
                        supply (ProcLabel.body head.name) bodyInput
                        (ProcLabel.exit head.name) with
                  | none =>
                      simp [hShape, hFrame, hAdapter, hBody] at hLower
                  | some compiled =>
                      cases hRequire :
                          compiled.requireFallthrough?
                            (TypedCfgCompiler.Shape.procExit head) with
                      | none =>
                          simp [hShape, hFrame, hAdapter, hBody, hRequire]
                            at hLower
                      | some unit =>
                          cases unit
                          cases hTail :
                              TypedCfgCompiler.lowerProcBodiesWithShapes?
                                entryShapes allProcs rest compiled.next with
                          | none =>
                              simp [hShape, hFrame, hAdapter, hBody, hRequire,
                                hTail] at hLower
                          | some tailResult =>
                              rcases tailResult with
                                ⟨tailBlocks, tailNext, tailCalls⟩
                              simp [hShape, hFrame, hAdapter, hBody, hRequire,
                                hTail] at hLower
                              rcases hLower with ⟨rfl, rfl, rfl⟩
                              simp only [List.cons_append, List.mem_cons,
                                List.mem_append] at hMem
                              rcases hMem with hEq | hIn | hThere
                              · exact
                                  ⟨head, supply, ProcLabel.body head.name,
                                    bodyInput, compiled,
                                    List.mem_cons_self, hBody,
                                    (fun b hb =>
                                      List.mem_cons_of_mem _
                                        (List.mem_append_left _ hb)),
                                    Or.inr (by rw [hEq]; exact hAdapter)⟩
                              · exact
                                  ⟨head, supply, ProcLabel.body head.name,
                                    bodyInput, compiled,
                                    List.mem_cons_self, hBody,
                                    (fun b hb =>
                                      List.mem_cons_of_mem _
                                        (List.mem_append_left _ hb)),
                                    Or.inl hIn⟩
                              · obtain
                                  ⟨proc, bsupply, e, input, bodyResult,
                                    hProcMem, hCompile, hSub, hDisj⟩ :=
                                  ih hTail hThere
                                exact
                                  ⟨proc, bsupply, e, input, bodyResult,
                                    List.mem_cons_of_mem head hProcMem,
                                    hCompile,
                                    (fun b hb =>
                                      List.mem_cons_of_mem _
                                        (List.mem_append_right _ (hSub b hb))),
                                    hDisj⟩

namespace GeneratedContext

/--
**Proc-body provenance root.**  Every proc-category block (`block ∈
context.procBlocks`, the second arm of `block_category`) is, for some source
procedure `proc ∈ source.procs`, either a member of `proc`'s compiled body
(`compileBlock? proc.body …`) — the entry point of the body statement-list drill —
or `proc`'s entry ADAPTER block.  Specialisation of `mem_procBlocks_provenance`
at `context.procsCompile`. -/
theorem procBlocks_provenance
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.procBlocks) :
    ∃ (proc : Structured.Proc) (bsupply : LabelSupply)
      (entry : Assembly.Label) (input : TypedCfg.Shape)
      (bodyResult : TypedCfgCompiler.Result),
      proc ∈ source.procs ∧
      TypedCfgCompiler.compileBlock? proc.body
          { procs := source.procs
            leaveLabel? := some (ProcLabel.exit proc.name)
            leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
          bsupply entry input (ProcLabel.exit proc.name) = some bodyResult ∧
      (block ∈ bodyResult.blocks ∨
        TypedCfgCompiler.mkBlock? (ProcLabel.entry proc.name)
            (TypedCfgCompiler.Shape.procEntry proc) [.relabel input]
            (.jump (ProcLabel.body proc.name)) = some block) :=
  mem_procBlocks_provenance context.procsCompile hMem

/--
**Proc-body provenance root, strengthened with `BlocksInProgram bodyResult cfg`.**

Same as `procBlocks_provenance` but the body compile fact is already promoted to
`BlocksInProgram bodyResult cfg` — every block of the compiled body is found in
`cfg` — which is exactly the hypothesis the body drill `genShape_of_compileBlock?`
consumes.  Combines `mem_procBlocks_provenance_subset`
(`bodyResult.blocks ⊆ procBlocks`) with `procBlocks ⊆ cfg.blocks` (from
`context.cfgEq`) and `LabelsUnique` (from `context.wellTyped`). -/
theorem procBlocks_provenance_inProgram
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.procBlocks) :
    ∃ (proc : Structured.Proc) (bsupply : LabelSupply)
      (entry : Assembly.Label) (input : TypedCfg.Shape)
      (bodyResult : TypedCfgCompiler.Result),
      proc ∈ source.procs ∧
      TypedCfgCompiler.compileBlock? proc.body
          { procs := source.procs
            leaveLabel? := some (ProcLabel.exit proc.name)
            leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
          bsupply entry input (ProcLabel.exit proc.name) = some bodyResult ∧
      BlocksInProgram bodyResult cfg ∧
      (block ∈ bodyResult.blocks ∨
        TypedCfgCompiler.mkBlock? (ProcLabel.entry proc.name)
            (TypedCfgCompiler.Shape.procEntry proc) [.relabel input]
            (.jump (ProcLabel.body proc.name)) = some block) := by
  obtain ⟨proc, bsupply, entry, input, bodyResult, hProcMem, hCompile, hSub, hDisj⟩ :=
    mem_procBlocks_provenance_subset context.procsCompile hMem
  refine ⟨proc, bsupply, entry, input, bodyResult, hProcMem, hCompile, ?_, hDisj⟩
  intro b hb
  refine TypedCfg.Program.findBlock?_eq_some_of_mem context.wellTyped.1 ?_
  rw [context.cfgEq]
  simp only [List.append_assoc, List.mem_append]
  have hbProc : b ∈ context.procBlocks := hSub b hb
  tauto

end GeneratedContext
end Program
end TypedCfgPreservation
end Structured
end EvmCompiler
