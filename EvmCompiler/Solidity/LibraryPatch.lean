import EvmCompiler.Solidity.ImmutablePatch
import EvmCompiler.Solidity.Public

/-!
# Unlinked libraries, verified

Unlinked-library support rewrites every `linkersymbol` occurrence whose
library name has no provided address into a `loadimmutable` occurrence of the
same fully-qualified name (`substituteUnlinkedLibraries`), and then reuses
the immutable marker machinery unchanged: the unlinked names appear as extra
`immutableReferences` entries keyed by library name, re-windowed by
`ObjectImage.linkReferences` into solc-compatible `{start := r.start + 12,
length := 20}` link references.

This module proves the two facts that make the export meaningful:

* the substitution bridge: resolving the substituted object with the missing
  addresses supplied as immutable values equals resolving the original
  object with those addresses supplied as linker symbols
  (`Object.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries`), and
* the link-time patch endpoint: 20-byte address writes at the exported link
  windows (together with ordinary immutable patching) reproduce, byte for
  byte, the pipeline's own compile with those addresses resolved
  (`Object.patchImmutablesAndLibraries_image_ofCompileUnlinked`).
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

/-! ## Bridge contexts

The substituted compile carries the missing addresses in `immutableValues`;
the original carries them in `linkerSymbols`.  Everything else the resolver
consults must agree. -/

structure LinkBridgeContexts (missing : List Name)
    (cSub cOrig : ObjectBuiltinContext) : Prop where
  layout_eq : cSub.layout = cOrig.layout
  dataSizes_eq : cSub.dataSizes = cOrig.dataSizes
  dataOffsets_eq : cSub.dataOffsets = cOrig.dataOffsets
  immutableReferences_eq :
    cSub.immutableReferences = cOrig.immutableReferences
  selfSize_eq : cSub.selfSize? = cOrig.selfSize?
  missing_value : ∀ name, missing.contains name = true →
    cSub.findImmutableValue? name = cOrig.findLinkerSymbol? name
  kept_value : ∀ name, missing.contains name = false →
    cSub.findImmutableValue? name = cOrig.findImmutableValue? name
  kept_linker : ∀ name, missing.contains name = false →
    cSub.findLinkerSymbol? name = cOrig.findLinkerSymbol? name

namespace LinkBridgeContexts

theorem size_eq {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (h : LinkBridgeContexts missing cSub cOrig) (name : Name) :
    cSub.size? name = cOrig.size? name := by
  simp [ObjectBuiltinContext.size?, ObjectBuiltinContext.findDataSize?,
    ObjectBuiltinContext.findSelfSize?, h.dataSizes_eq, h.selfSize_eq,
    h.layout_eq]

theorem offset_eq {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (h : LinkBridgeContexts missing cSub cOrig) (name : Name) :
    cSub.offset? name = cOrig.offset? name := by
  simp [ObjectBuiltinContext.offset?, ObjectBuiltinContext.findDataOffset?,
    h.dataOffsets_eq, h.layout_eq]

theorem findImmutableReferences_eq {missing : List Name}
    {cSub cOrig : ObjectBuiltinContext}
    (h : LinkBridgeContexts missing cSub cOrig) (name : Name) :
    cSub.findImmutableReferences? name = cOrig.findImmutableReferences? name := by
  simp [ObjectBuiltinContext.findImmutableReferences?,
    h.immutableReferences_eq]

theorem withMemoryContract {missing : List Name}
    {cSub cOrig : ObjectBuiltinContext}
    (h : LinkBridgeContexts missing cSub cOrig)
    (memoryContract : MemoryContract.Contract) :
    LinkBridgeContexts missing
      { cSub with memoryContract := memoryContract }
      { cOrig with memoryContract := memoryContract } := by
  constructor <;>
    first
      | exact h.layout_eq
      | exact h.dataSizes_eq
      | exact h.dataOffsets_eq
      | exact h.immutableReferences_eq
      | exact h.selfSize_eq
      | exact h.missing_value
      | exact h.kept_value
      | exact h.kept_linker

end LinkBridgeContexts

/-! ## Shape helpers for the substitution -/

theorem Expr.List.substituteUnlinkedLibraries_length
    (missing : List Name) (exprs : List Expr) :
    (Expr.List.substituteUnlinkedLibraries missing exprs).length =
      exprs.length := by
  induction exprs with
  | nil => rfl
  | cons head rest ih =>
      simp [Expr.List.substituteUnlinkedLibraries, ih]

theorem Expr.substituteUnlinkedLibraries_call_shape
    (missing : List Name) (kind : CallKind) (callee : Name)
    (args : List Expr) :
    ∃ kind' callee' args',
      Expr.substituteUnlinkedLibraries missing (.call kind callee args) =
        .call kind' callee' args' := by
  unfold Expr.substituteUnlinkedLibraries
  split
  all_goals (rename_i heq; cases heq)
  · repeat' split
    all_goals exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

theorem Expr.objectBuiltinNameArg?_substituteUnlinkedLibraries
    (missing : List Name) (expr : Expr) :
    Expr.objectBuiltinNameArg?
        (expr.substituteUnlinkedLibraries missing) =
      Expr.objectBuiltinNameArg? expr := by
  cases expr with
  | lit value => rfl
  | stringLit value => rfl
  | bytesLit bytes => rfl
  | var name => rfl
  | call kind callee args =>
      obtain ⟨kind', callee', args', hShape⟩ :=
        Expr.substituteUnlinkedLibraries_call_shape missing kind callee args
      rw [hShape]
      rfl

theorem Expr.substituteUnlinkedLibraries_call_notLinker
    (missing : List Name) (kind : CallKind) (callee : Name)
    (args : List Expr)
    (h : ∀ nameArg, kind = .objectBuiltin → callee = "linkersymbol" →
      args = [nameArg] → False) :
    Expr.substituteUnlinkedLibraries missing (.call kind callee args) =
      .call kind callee (Expr.List.substituteUnlinkedLibraries missing args) := by
  unfold Expr.substituteUnlinkedLibraries
  split
  all_goals (rename_i heq; cases heq)
  · exact (h _ rfl rfl rfl).elim
  · rfl

theorem Expr.loadImmutableNames_call_generic
    (kind : CallKind) (callee : Name) (args : List Expr)
    (h : ∀ nameArg, kind = .objectBuiltin → callee = "loadimmutable" →
      args = [nameArg] → False) :
    Expr.loadImmutableNames (.call kind callee args) =
      Expr.List.loadImmutableNames args := by
  unfold Expr.loadImmutableNames
  split
  all_goals (rename_i heq; cases heq)
  · exact (h _ rfl rfl rfl).elim
  · rfl

theorem Expr.resolveObjectBuiltinsIn?_call_generic
    (kind : CallKind) (callee : Name) (args : List Expr)
    (context : ObjectBuiltinContext)
    (h1 : ∀ nameArg, kind = .objectBuiltin → callee = "datasize" →
      args = [nameArg] → False)
    (h2 : ∀ nameArg, kind = .objectBuiltin → callee = "dataoffset" →
      args = [nameArg] → False)
    (h3 : ∀ nameArg, kind = .objectBuiltin → callee = "linkersymbol" →
      args = [nameArg] → False)
    (h4 : ∀ nameArg, kind = .objectBuiltin → callee = "loadimmutable" →
      args = [nameArg] → False)
    (h5 : ∀ target offset size, kind = .objectBuiltin →
      callee = "datacopy" → args = [target, offset, size] → False)
    (h6 : ∀ value, kind = .objectBuiltin → callee = "memoryguard" →
      args = [value] → False) :
    Expr.resolveObjectBuiltinsIn? (.call kind callee args) context =
      (do
        let args' ← Expr.List.resolveObjectBuiltinsIn? args context
        some (.call kind callee args')) := by
  unfold Expr.resolveObjectBuiltinsIn?
  split
  all_goals (rename_i heq; cases heq)
  · exact (h1 _ rfl rfl rfl).elim
  · exact (h2 _ rfl rfl rfl).elim
  · exact (h3 _ rfl rfl rfl).elim
  · exact (h4 _ rfl rfl rfl).elim
  · exact (h5 _ _ _ rfl rfl rfl).elim
  · exact (h6 _ rfl rfl rfl).elim
  · rfl

/-! ## The substitution bridge, expression level -/

theorem Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) :
    ∀ expr : Expr,
      (∀ name ∈ Expr.loadImmutableNames expr,
        missing.contains name = false) →
      Expr.resolveObjectBuiltinsIn?
          (Expr.substituteUnlinkedLibraries missing expr) cSub =
        Expr.resolveObjectBuiltinsIn? expr cOrig := by
  apply Expr.resolveObjectBuiltinsIn?.induct
    (motive1 := fun expr =>
      (∀ name ∈ Expr.loadImmutableNames expr,
        missing.contains name = false) →
      Expr.resolveObjectBuiltinsIn?
          (Expr.substituteUnlinkedLibraries missing expr) cSub =
        Expr.resolveObjectBuiltinsIn? expr cOrig)
    (motive2 := fun exprs =>
      (∀ name ∈ Expr.List.loadImmutableNames exprs,
        missing.contains name = false) →
      Expr.List.resolveObjectBuiltinsIn?
          (Expr.List.substituteUnlinkedLibraries missing exprs) cSub =
        Expr.List.resolveObjectBuiltinsIn? exprs cOrig)
  -- lit
  · intro value _
    simp [Expr.substituteUnlinkedLibraries, Expr.resolveObjectBuiltinsIn?]
  -- stringLit
  · intro value _
    simp [Expr.substituteUnlinkedLibraries, Expr.resolveObjectBuiltinsIn?]
  -- bytesLit
  · intro bytes _
    simp [Expr.substituteUnlinkedLibraries, Expr.resolveObjectBuiltinsIn?]
  -- var
  · intro name _
    simp [Expr.substituteUnlinkedLibraries, Expr.resolveObjectBuiltinsIn?]
  -- datasize
  · intro nameArg _
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Expr.resolveObjectBuiltinsIn?]
    rw [Expr.objectBuiltinNameArg?_substituteUnlinkedLibraries]
    cases hName : Expr.objectBuiltinNameArg? nameArg <;>
      simp [hCtx.size_eq]
  -- dataoffset
  · intro nameArg _
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Expr.resolveObjectBuiltinsIn?]
    rw [Expr.objectBuiltinNameArg?_substituteUnlinkedLibraries]
    cases hName : Expr.objectBuiltinNameArg? nameArg <;>
      simp [hCtx.offset_eq]
  -- linkersymbol
  · intro nameArg _
    simp only [Expr.substituteUnlinkedLibraries]
    cases hName : Expr.objectBuiltinNameArg? nameArg with
    | none =>
        simp [Expr.resolveObjectBuiltinsIn?, hName]
    | some name =>
        by_cases hMem : missing.contains name = true
        · simp only [hName, hMem, if_pos]
          simp [Expr.resolveObjectBuiltinsIn?, hName,
            hCtx.missing_value name hMem]
        · have hMem' : missing.contains name = false := by
            simpa using hMem
          simp only [hName, hMem', Bool.false_eq_true, if_neg,
            not_false_eq_true]
          simp [Expr.resolveObjectBuiltinsIn?, hName,
            hCtx.kept_linker name hMem']
  -- loadimmutable
  · intro nameArg hNames
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Expr.resolveObjectBuiltinsIn?]
    rw [Expr.objectBuiltinNameArg?_substituteUnlinkedLibraries]
    cases hName : Expr.objectBuiltinNameArg? nameArg with
    | none => rfl
    | some name =>
        have hMemName : name ∈ Expr.loadImmutableNames
            (.call .objectBuiltin "loadimmutable" [nameArg]) := by
          simp [Expr.loadImmutableNames, hName]
        simp [hCtx.kept_value name (hNames name hMemName)]
  -- datacopy
  · intro target offset size ihTarget ihOffset ihSize hNames
    have hNamesAll :
        ∀ name ∈ Expr.List.loadImmutableNames [target, offset, size],
          missing.contains name = false := by
      intro name hMem
      apply hNames
      rw [Expr.loadImmutableNames_call_generic _ _ _
        (fun _ _ hc _ => absurd hc (by decide))]
      exact hMem
    have hTargetNames : ∀ name ∈ Expr.loadImmutableNames target,
        missing.contains name = false := by
      intro name hMem
      exact hNamesAll name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inl hMem)
    have hOffsetNames : ∀ name ∈ Expr.loadImmutableNames offset,
        missing.contains name = false := by
      intro name hMem
      exact hNamesAll name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inr (Or.inl hMem))
    have hSizeNames : ∀ name ∈ Expr.loadImmutableNames size,
        missing.contains name = false := by
      intro name hMem
      exact hNamesAll name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inr (Or.inr hMem))
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Expr.resolveObjectBuiltinsIn?]
    rw [ihTarget hTargetNames, ihOffset hOffsetNames, ihSize hSizeNames]
  -- memoryguard
  · intro value ihValue hNames
    have hValueNames : ∀ name ∈ Expr.loadImmutableNames value,
        missing.contains name = false := by
      intro name hMem
      apply hNames
      rw [Expr.loadImmutableNames_call_generic _ _ _
        (fun _ _ hc _ => absurd hc (by decide))]
      simp [Expr.List.loadImmutableNames]
      exact hMem
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Expr.resolveObjectBuiltinsIn?]
    rw [ihValue hValueNames]
  -- generic call
  · intro kind callee args h1 h2 h3 h4 h5 h6 ihArgs hNames
    have hNamesArgs :
        ∀ name ∈ Expr.List.loadImmutableNames args,
          missing.contains name = false := by
      intro name hMem
      apply hNames
      rw [Expr.loadImmutableNames_call_generic _ _ _ h4]
      exact hMem
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _ h3]
    rw [Expr.resolveObjectBuiltinsIn?_call_generic _ _ _ _
      (fun x hk hc ha => by
        obtain ⟨a, hA⟩ := List.length_eq_one_iff.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h1 a hk hc hA)
      (fun x hk hc ha => by
        obtain ⟨a, hA⟩ := List.length_eq_one_iff.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h2 a hk hc hA)
      (fun x hk hc ha => by
        obtain ⟨a, hA⟩ := List.length_eq_one_iff.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h3 a hk hc hA)
      (fun x hk hc ha => by
        obtain ⟨a, hA⟩ := List.length_eq_one_iff.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h4 a hk hc hA)
      (fun x y z hk hc ha => by
        obtain ⟨a, b, c, hA⟩ := List.length_eq_three.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h5 a b c hk hc hA)
      (fun x hk hc ha => by
        obtain ⟨a, hA⟩ := List.length_eq_one_iff.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h6 a hk hc hA)]
    rw [Expr.resolveObjectBuiltinsIn?_call_generic _ _ _ _ h1 h2 h3 h4 h5 h6]
    rw [ihArgs hNamesArgs]
  -- list nil
  · intro _
    simp [Expr.List.substituteUnlinkedLibraries,
      Expr.List.resolveObjectBuiltinsIn?]
  -- list cons
  · intro expr rest ihExpr ihRest hNames
    have hExprNames : ∀ name ∈ Expr.loadImmutableNames expr,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inl hMem)
    have hRestNames : ∀ name ∈ Expr.List.loadImmutableNames rest,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inr hMem)
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Expr.List.resolveObjectBuiltinsIn?]
    rw [ihExpr hExprNames, ihRest hRestNames]

/-- List-level companion of the expression bridge. -/
theorem Expr.List.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) :
    ∀ exprs : List Expr,
      (∀ name ∈ Expr.List.loadImmutableNames exprs,
        missing.contains name = false) →
      Expr.List.resolveObjectBuiltinsIn?
          (Expr.List.substituteUnlinkedLibraries missing exprs) cSub =
        Expr.List.resolveObjectBuiltinsIn? exprs cOrig := by
  intro exprs
  induction exprs with
  | nil =>
      intro _
      simp [Expr.List.substituteUnlinkedLibraries,
        Expr.List.resolveObjectBuiltinsIn?]
  | cons expr rest ih =>
      intro hNames
      have hExprNames : ∀ name ∈ Expr.loadImmutableNames expr,
          missing.contains name = false := by
        intro name hMem
        exact hNames name (by
          simp [Expr.List.loadImmutableNames]
          exact Or.inl hMem)
      have hRestNames : ∀ name ∈ Expr.List.loadImmutableNames rest,
          missing.contains name = false := by
        intro name hMem
        exact hNames name (by
          simp [Expr.List.loadImmutableNames]
          exact Or.inr hMem)
      simp only [Expr.List.substituteUnlinkedLibraries]
      simp only [Expr.List.resolveObjectBuiltinsIn?]
      rw [Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx
        expr hExprNames, ih hRestNames]

/-! ## The substitution bridge, statement level -/

theorem Expr.substituteUnlinkedLibraries_not_setimmutable
    (missing : List Name) (expr : Expr)
    (h : ∀ base nameArg value,
      expr = .call .objectBuiltin "setimmutable" [base, nameArg, value] →
        False) :
    ∀ base nameArg value,
      Expr.substituteUnlinkedLibraries missing expr =
          .call .objectBuiltin "setimmutable" [base, nameArg, value] →
        False := by
  intro base nameArg value hEq
  cases expr with
  | lit v => simp [Expr.substituteUnlinkedLibraries] at hEq
  | stringLit v => simp [Expr.substituteUnlinkedLibraries] at hEq
  | bytesLit b => simp [Expr.substituteUnlinkedLibraries] at hEq
  | var n => simp [Expr.substituteUnlinkedLibraries] at hEq
  | call kind callee args =>
      revert hEq
      unfold Expr.substituteUnlinkedLibraries
      split
      all_goals (rename_i heq; cases heq)
      · intro hEq
        split at hEq
        · split at hEq <;> simp_all
        · simp_all
      · intro hEq
        rw [Expr.call.injEq] at hEq
        obtain ⟨hk, hc, ha⟩ := hEq
        obtain ⟨b0, n0, v0, hArgs⟩ := List.length_eq_three.mp (by
          simpa [Expr.List.substituteUnlinkedLibraries_length] using
            congrArg List.length ha)
        exact h b0 n0 v0 (by rw [hk, hc, hArgs])

theorem Stmt.resolveObjectBuiltinsIn?_exprStmt_generic
    (expr : Expr) (context : ObjectBuiltinContext)
    (h : ∀ base nameArg value,
      expr = .call .objectBuiltin "setimmutable" [base, nameArg, value] →
        False) :
    Stmt.resolveObjectBuiltinsIn? (.exprStmt expr) context =
      (do
        let expr' ← Expr.resolveObjectBuiltinsIn? expr context
        some (.exprStmt expr')) := by
  unfold Stmt.resolveObjectBuiltinsIn?
  split
  all_goals (rename_i heq; cases heq)
  · exact (h _ _ _ rfl).elim
  · rfl

theorem Stmt.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) :
    ∀ stmt : Stmt,
      (∀ name ∈ Stmt.loadImmutableNames stmt,
        missing.contains name = false) →
      Stmt.resolveObjectBuiltinsIn?
          (Stmt.substituteUnlinkedLibraries missing stmt) cSub =
        Stmt.resolveObjectBuiltinsIn? stmt cOrig := by
  apply Stmt.resolveObjectBuiltinsIn?.induct
    (motive1 := fun stmt =>
      (∀ name ∈ Stmt.loadImmutableNames stmt,
        missing.contains name = false) →
      Stmt.resolveObjectBuiltinsIn?
          (Stmt.substituteUnlinkedLibraries missing stmt) cSub =
        Stmt.resolveObjectBuiltinsIn? stmt cOrig)
    (motive2 := fun cases =>
      (∀ name ∈ Stmt.CaseList.loadImmutableNames cases,
        missing.contains name = false) →
      Stmt.CaseList.resolveObjectBuiltinsIn?
          (Stmt.CaseList.substituteUnlinkedLibraries missing cases) cSub =
        Stmt.CaseList.resolveObjectBuiltinsIn? cases cOrig)
    (motive3 := fun stmts =>
      (∀ name ∈ Stmt.List.loadImmutableNames stmts,
        missing.contains name = false) →
      Stmt.List.resolveObjectBuiltinsIn?
          (Stmt.List.substituteUnlinkedLibraries missing stmts) cSub =
        Stmt.List.resolveObjectBuiltinsIn? stmts cOrig)
  -- block
  · intro stmts ihStmts hNames
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [ihStmts (fun name hMem => hNames name (by
      simpa [Stmt.loadImmutableNames] using hMem))]
  -- letDecl none
  · intro names _
    simp [Stmt.substituteUnlinkedLibraries, Stmt.resolveObjectBuiltinsIn?]
  -- letDecl some
  · intro names value hNames
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx value
      (fun name hMem => hNames name (by
        simpa [Stmt.loadImmutableNames] using hMem))]
  -- assign
  · intro names value hNames
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx value
      (fun name hMem => hNames name (by
        simpa [Stmt.loadImmutableNames] using hMem))]
  -- setimmutable
  · intro base nameArg value hNames
    have hNamesArgs :
        ∀ name ∈ Expr.List.loadImmutableNames [base, nameArg, value],
          missing.contains name = false := by
      intro name hMem
      apply hNames
      have hCall :
          Expr.loadImmutableNames
              (.call .objectBuiltin "setimmutable" [base, nameArg, value]) =
            Expr.List.loadImmutableNames [base, nameArg, value] :=
        Expr.loadImmutableNames_call_generic _ _ _
          (fun _ _ hc _ => absurd hc (by decide))
      simp only [Stmt.loadImmutableNames, hCall]
      exact hMem
    have hBaseNames : ∀ name ∈ Expr.loadImmutableNames base,
        missing.contains name = false := by
      intro name hMem
      exact hNamesArgs name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inl hMem)
    have hValueNames : ∀ name ∈ Expr.loadImmutableNames value,
        missing.contains name = false := by
      intro name hMem
      exact hNamesArgs name (by
        simp [Expr.List.loadImmutableNames]
        exact Or.inr (Or.inr hMem))
    simp only [Stmt.substituteUnlinkedLibraries]
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp only [Expr.List.substituteUnlinkedLibraries]
    simp only [Stmt.resolveObjectBuiltinsIn?]
    rw [Expr.objectBuiltinNameArg?_substituteUnlinkedLibraries,
      Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx base
        hBaseNames,
      Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx value
        hValueNames]
    simp only [hCtx.findImmutableReferences_eq]
  -- exprStmt generic
  · intro expr hNotSet hNames
    simp only [Stmt.substituteUnlinkedLibraries]
    rw [Stmt.resolveObjectBuiltinsIn?_exprStmt_generic _ _
      (Expr.substituteUnlinkedLibraries_not_setimmutable missing expr
        hNotSet)]
    rw [Stmt.resolveObjectBuiltinsIn?_exprStmt_generic _ _ hNotSet]
    rw [Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx expr
      (fun name hMem => hNames name (by
        simpa [Stmt.loadImmutableNames] using hMem))]
  -- functionDef
  · intro name params returns body ihBody hNames
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [ihBody (fun n hMem => hNames n (by
      simpa [Stmt.loadImmutableNames] using hMem))]
  -- switch
  · intro scrutinee cases default ihCases ihDefault hNames
    have hScrutineeNames : ∀ name ∈ Expr.loadImmutableNames scrutinee,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inl hMem)
    have hCasesNames :
        ∀ name ∈ Stmt.CaseList.loadImmutableNames cases,
          missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inr (Or.inl hMem))
    have hDefaultNames :
        ∀ name ∈ Stmt.List.loadImmutableNames default,
          missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inr (Or.inr hMem))
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx
        scrutinee hScrutineeNames,
      ihCases hCasesNames, ihDefault hDefaultNames]
  -- forLoop
  · intro pre condition post body ihPre ihPost ihBody hNames
    have hConditionNames :
        ∀ name ∈ Expr.loadImmutableNames condition,
          missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inl hMem)
    have hPreNames : ∀ name ∈ Stmt.List.loadImmutableNames pre,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inr (Or.inl hMem))
    have hPostNames : ∀ name ∈ Stmt.List.loadImmutableNames post,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inr (Or.inr (Or.inl hMem)))
    have hBodyNames : ∀ name ∈ Stmt.List.loadImmutableNames body,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inr (Or.inr (Or.inr hMem)))
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [ihPre hPreNames,
      Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx
        condition hConditionNames,
      ihPost hPostNames, ihBody hBodyNames]
  -- ifThen
  · intro condition body ihBody hNames
    have hConditionNames :
        ∀ name ∈ Expr.loadImmutableNames condition,
          missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inl hMem)
    have hBodyNames : ∀ name ∈ Stmt.List.loadImmutableNames body,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.loadImmutableNames]
        exact Or.inr hMem)
    simp only [Stmt.substituteUnlinkedLibraries,
      Stmt.resolveObjectBuiltinsIn?]
    rw [Expr.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx
        condition hConditionNames,
      ihBody hBodyNames]
  -- break
  · intro _
    simp [Stmt.substituteUnlinkedLibraries, Stmt.resolveObjectBuiltinsIn?]
  -- continue
  · intro _
    simp [Stmt.substituteUnlinkedLibraries, Stmt.resolveObjectBuiltinsIn?]
  -- leave
  · intro _
    simp [Stmt.substituteUnlinkedLibraries, Stmt.resolveObjectBuiltinsIn?]
  -- caselist nil
  · intro _
    simp [Stmt.CaseList.substituteUnlinkedLibraries,
      Stmt.CaseList.resolveObjectBuiltinsIn?]
  -- caselist cons
  · intro value body rest ihBody ihRest hNames
    have hBodyNames : ∀ name ∈ Stmt.List.loadImmutableNames body,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.CaseList.loadImmutableNames]
        exact Or.inl hMem)
    have hRestNames :
        ∀ name ∈ Stmt.CaseList.loadImmutableNames rest,
          missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.CaseList.loadImmutableNames]
        exact Or.inr hMem)
    simp only [Stmt.CaseList.substituteUnlinkedLibraries,
      Stmt.CaseList.resolveObjectBuiltinsIn?]
    rw [ihBody hBodyNames, ihRest hRestNames]
  -- stmtlist nil
  · intro _
    simp [Stmt.List.substituteUnlinkedLibraries,
      Stmt.List.resolveObjectBuiltinsIn?]
  -- stmtlist cons
  · intro stmt rest ihStmt ihRest hNames
    have hStmtNames : ∀ name ∈ Stmt.loadImmutableNames stmt,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.List.loadImmutableNames]
        exact Or.inl hMem)
    have hRestNames : ∀ name ∈ Stmt.List.loadImmutableNames rest,
        missing.contains name = false := by
      intro name hMem
      exact hNames name (by
        simp [Stmt.List.loadImmutableNames]
        exact Or.inr hMem)
    simp only [Stmt.List.substituteUnlinkedLibraries,
      Stmt.List.resolveObjectBuiltinsIn?]
    rw [ihStmt hStmtNames, ihRest hRestNames]

theorem Stmt.List.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) :
    ∀ stmts : List Stmt,
      (∀ name ∈ Stmt.List.loadImmutableNames stmts,
        missing.contains name = false) →
      Stmt.List.resolveObjectBuiltinsIn?
          (Stmt.List.substituteUnlinkedLibraries missing stmts) cSub =
        Stmt.List.resolveObjectBuiltinsIn? stmts cOrig := by
  intro stmts
  induction stmts with
  | nil =>
      intro _
      simp [Stmt.List.substituteUnlinkedLibraries,
        Stmt.List.resolveObjectBuiltinsIn?]
  | cons stmt rest ih =>
      intro hNames
      have hStmtNames : ∀ name ∈ Stmt.loadImmutableNames stmt,
          missing.contains name = false := by
        intro name hMem
        exact hNames name (by
          simp [Stmt.List.loadImmutableNames]
          exact Or.inl hMem)
      have hRestNames : ∀ name ∈ Stmt.List.loadImmutableNames rest,
          missing.contains name = false := by
        intro name hMem
        exact hNames name (by
          simp [Stmt.List.loadImmutableNames]
          exact Or.inr hMem)
      simp only [Stmt.List.substituteUnlinkedLibraries,
        Stmt.List.resolveObjectBuiltinsIn?]
      rw [Stmt.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx
        stmt hStmtNames, ih hRestNames]

theorem FunctionDef.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) (fn : FunctionDef)
    (hNames : ∀ name ∈ fn.loadImmutableNames,
      missing.contains name = false) :
    FunctionDef.resolveObjectBuiltinsIn?
        (fn.substituteUnlinkedLibraries missing) cSub =
      FunctionDef.resolveObjectBuiltinsIn? fn cOrig := by
  unfold FunctionDef.resolveObjectBuiltinsIn?
  simp only [FunctionDef.substituteUnlinkedLibraries]
  rw [Stmt.List.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx
    fn.body hNames]

theorem FunctionDef.List.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) :
    ∀ functions : List (Name × FunctionDef),
      (∀ name ∈ FunctionDef.List.loadImmutableNames functions,
        missing.contains name = false) →
      FunctionDef.List.resolveObjectBuiltinsIn?
          (FunctionDef.List.substituteUnlinkedLibraries missing functions)
          cSub =
        FunctionDef.List.resolveObjectBuiltinsIn? functions cOrig := by
  intro functions
  induction functions with
  | nil =>
      intro _
      simp [FunctionDef.List.substituteUnlinkedLibraries,
        FunctionDef.List.resolveObjectBuiltinsIn?]
  | cons entry rest ih =>
      rcases entry with ⟨name, fn⟩
      intro hNames
      have hFnNames : ∀ n ∈ fn.loadImmutableNames,
          missing.contains n = false := by
        intro n hMem
        exact hNames n (by
          simp [FunctionDef.List.loadImmutableNames]
          exact Or.inl hMem)
      have hRestNames :
          ∀ n ∈ FunctionDef.List.loadImmutableNames rest,
            missing.contains n = false := by
        intro n hMem
        exact hNames n (by
          simp [FunctionDef.List.loadImmutableNames]
          exact Or.inr hMem)
      simp only [FunctionDef.List.substituteUnlinkedLibraries,
        FunctionDef.List.resolveObjectBuiltinsIn?]
      rw [FunctionDef.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
        hCtx fn hFnNames, ih hRestNames]

/-! ## Memory-guard invariance under substitution -/

theorem Expr.substituteUnlinkedLibraries_eq_lit
    (missing : List Name) (expr : Expr) (value : Word)
    (h : Expr.substituteUnlinkedLibraries missing expr = .lit value) :
    expr = .lit value := by
  cases expr with
  | lit v => simpa [Expr.substituteUnlinkedLibraries] using h
  | stringLit v => simp [Expr.substituteUnlinkedLibraries] at h
  | bytesLit b => simp [Expr.substituteUnlinkedLibraries] at h
  | var n => simp [Expr.substituteUnlinkedLibraries] at h
  | call kind callee args =>
      obtain ⟨kind', callee', args', hShape⟩ :=
        Expr.substituteUnlinkedLibraries_call_shape missing kind callee args
      rw [hShape] at h
      simp at h

theorem MemoryGuard.Expr.sizes?_call_notMemoryguard
    (kind : CallKind) (callee : Name) (args : List Expr)
    (h : kind = .objectBuiltin → callee = "memoryguard" → False) :
    MemoryGuard.Expr.sizes? (.call kind callee args) =
      MemoryGuard.Expr.List.sizes? args := by
  unfold MemoryGuard.Expr.sizes?
  split
  all_goals (rename_i heq; cases heq)
  · exact (h rfl rfl).elim
  · exact (h rfl rfl).elim
  · rfl

theorem MemoryGuard.Expr.sizes?_memoryguard_notLit
    (args : List Expr)
    (h : ∀ size, args = [Expr.lit size] → False) :
    MemoryGuard.Expr.sizes?
        (.call .objectBuiltin "memoryguard" args) = none := by
  unfold MemoryGuard.Expr.sizes?
  split
  all_goals (rename_i heq; cases heq)
  · exact (h _ rfl).elim
  · rfl
  · rename_i hNot _
    exact ((hNot rfl rfl).elim :
      MemoryGuard.Expr.List.sizes? args = none)

theorem MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries
    (missing : List Name) :
    ∀ expr : Expr,
      MemoryGuard.Expr.sizes?
          (Expr.substituteUnlinkedLibraries missing expr) =
        MemoryGuard.Expr.sizes? expr := by
  apply MemoryGuard.Expr.sizes?.induct
    (motive_1 := fun expr =>
      MemoryGuard.Expr.sizes?
          (Expr.substituteUnlinkedLibraries missing expr) =
        MemoryGuard.Expr.sizes? expr)
    (motive_2 := fun exprs =>
      MemoryGuard.Expr.List.sizes?
          (Expr.List.substituteUnlinkedLibraries missing exprs) =
        MemoryGuard.Expr.List.sizes? exprs)
  · intro value
    simp [Expr.substituteUnlinkedLibraries]
  · intro value
    simp [Expr.substituteUnlinkedLibraries, MemoryGuard.Expr.sizes?]
  · intro bytes
    simp [Expr.substituteUnlinkedLibraries, MemoryGuard.Expr.sizes?]
  · intro name
    simp [Expr.substituteUnlinkedLibraries, MemoryGuard.Expr.sizes?]
  -- memoryguard [.lit size]
  · intro size
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    simp [Expr.List.substituteUnlinkedLibraries,
      Expr.substituteUnlinkedLibraries]
  -- memoryguard args, not a literal
  · intro args hNotLit
    rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _
      (fun _ _ hc _ => absurd hc (by decide))]
    have hNotLit' : ∀ size,
        Expr.List.substituteUnlinkedLibraries missing args =
          [Expr.lit size] → False := by
      intro size hEq
      cases args with
      | nil => simp [Expr.List.substituteUnlinkedLibraries] at hEq
      | cons head rest =>
          cases rest with
          | cons second more =>
              simp [Expr.List.substituteUnlinkedLibraries] at hEq
          | nil =>
              simp only [Expr.List.substituteUnlinkedLibraries,
                List.cons.injEq, and_true] at hEq
              exact hNotLit size (by
                rw [Expr.substituteUnlinkedLibraries_eq_lit missing head
                  size hEq])
    rw [MemoryGuard.Expr.sizes?_memoryguard_notLit _ hNotLit',
      MemoryGuard.Expr.sizes?_memoryguard_notLit _ hNotLit]
  -- generic call
  · intro kind callee args _hNotLit hNotGuard ihArgs
    by_cases hL : kind = .objectBuiltin ∧ callee = "linkersymbol" ∧
        ∃ x, args = [x]
    · obtain ⟨hk, hc, x, ha⟩ := hL
      subst hk; subst hc; subst ha
      simp only [Expr.substituteUnlinkedLibraries]
      cases hName : Expr.objectBuiltinNameArg? x with
      | none =>
          simp
      | some name =>
          by_cases hMem : missing.contains name = true
          · simp only [hName, hMem, if_pos]
            rw [MemoryGuard.Expr.sizes?_call_notMemoryguard _ _ _
              (fun _ hc => absurd hc (by decide)),
              MemoryGuard.Expr.sizes?_call_notMemoryguard _ _ _
              (fun _ hc => absurd hc (by decide))]
          · simp only [hName, hMem, if_neg]
            simp
    · have hNot : ∀ nameArg, kind = .objectBuiltin →
          callee = "linkersymbol" → args = [nameArg] → False := by
        intro nameArg hk hc ha
        exact hL ⟨hk, hc, nameArg, ha⟩
      rw [Expr.substituteUnlinkedLibraries_call_notLinker missing _ _ _ hNot]
      rw [MemoryGuard.Expr.sizes?_call_notMemoryguard _ _ _ hNotGuard,
        MemoryGuard.Expr.sizes?_call_notMemoryguard _ _ _ hNotGuard]
      exact ihArgs
  -- list nil
  · simp [Expr.List.substituteUnlinkedLibraries,
      MemoryGuard.Expr.List.sizes?]
  -- list cons
  · intro expr rest ihExpr ihRest
    simp only [Expr.List.substituteUnlinkedLibraries,
      MemoryGuard.Expr.List.sizes?]
    rw [ihExpr, ihRest]

theorem MemoryGuard.Stmt.sizes?_substituteUnlinkedLibraries
    (missing : List Name) :
    ∀ stmt : Stmt,
      MemoryGuard.Stmt.sizes?
          (Stmt.substituteUnlinkedLibraries missing stmt) =
        MemoryGuard.Stmt.sizes? stmt := by
  apply MemoryGuard.Stmt.sizes?.induct
    (motive_1 := fun stmt =>
      MemoryGuard.Stmt.sizes?
          (Stmt.substituteUnlinkedLibraries missing stmt) =
        MemoryGuard.Stmt.sizes? stmt)
    (motive_2 := fun cases =>
      MemoryGuard.Stmt.CaseList.sizes?
          (Stmt.CaseList.substituteUnlinkedLibraries missing cases) =
        MemoryGuard.Stmt.CaseList.sizes? cases)
    (motive_3 := fun stmts =>
      MemoryGuard.Stmt.List.sizes?
          (Stmt.List.substituteUnlinkedLibraries missing stmts) =
        MemoryGuard.Stmt.List.sizes? stmts)
  · intro stmts ihStmts
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [ihStmts]
  · intro names
    simp [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
  · intro names value
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries]
  · intro names value
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries]
  · intro expr
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries]
  · intro name params returns body ihBody
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [ihBody]
  · intro scrutinee cases default ihCases ihDefault
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries,
      ihCases, ihDefault]
  · intro pre condition post body ihPre ihPost ihBody
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries,
      ihPre, ihPost, ihBody]
  · intro condition body ihBody
    simp only [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
    rw [MemoryGuard.Expr.sizes?_substituteUnlinkedLibraries, ihBody]
  · simp [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
  · simp [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
  · simp [Stmt.substituteUnlinkedLibraries, MemoryGuard.Stmt.sizes?]
  · simp [Stmt.List.substituteUnlinkedLibraries,
      MemoryGuard.Stmt.List.sizes?]
  · intro stmt rest ihStmt ihRest
    simp only [Stmt.List.substituteUnlinkedLibraries,
      MemoryGuard.Stmt.List.sizes?]
    rw [ihStmt, ihRest]
  · simp [Stmt.CaseList.substituteUnlinkedLibraries,
      MemoryGuard.Stmt.CaseList.sizes?]
  · intro value body rest ihBody ihRest
    simp only [Stmt.CaseList.substituteUnlinkedLibraries,
      MemoryGuard.Stmt.CaseList.sizes?]
    rw [ihBody, ihRest]

theorem MemoryGuard.Stmt.List.sizes?_substituteUnlinkedLibraries
    (missing : List Name) (stmts : List Stmt) :
    MemoryGuard.Stmt.List.sizes?
        (Stmt.List.substituteUnlinkedLibraries missing stmts) =
      MemoryGuard.Stmt.List.sizes? stmts := by
  induction stmts with
  | nil =>
      simp [Stmt.List.substituteUnlinkedLibraries,
        MemoryGuard.Stmt.List.sizes?]
  | cons stmt rest ih =>
      simp only [Stmt.List.substituteUnlinkedLibraries,
        MemoryGuard.Stmt.List.sizes?]
      rw [MemoryGuard.Stmt.sizes?_substituteUnlinkedLibraries, ih]

theorem MemoryGuard.FunctionDef.List.sizes?_substituteUnlinkedLibraries
    (missing : List Name) (functions : List (Name × FunctionDef)) :
    MemoryGuard.FunctionDef.List.sizes?
        (FunctionDef.List.substituteUnlinkedLibraries missing functions) =
      MemoryGuard.FunctionDef.List.sizes? functions := by
  induction functions with
  | nil =>
      simp [FunctionDef.List.substituteUnlinkedLibraries,
        MemoryGuard.FunctionDef.List.sizes?]
  | cons entry rest ih =>
      rcases entry with ⟨name, fn⟩
      simp only [FunctionDef.List.substituteUnlinkedLibraries,
        MemoryGuard.FunctionDef.List.sizes?]
      rw [ih]
      simp only [MemoryGuard.FunctionDef.sizes?,
        FunctionDef.substituteUnlinkedLibraries]
      rw [MemoryGuard.Stmt.List.sizes?_substituteUnlinkedLibraries]

theorem MemoryGuard.Object.sizes?_substituteUnlinkedLibraries
    (missing : List Name) (object : Object) :
    MemoryGuard.Object.sizes?
        (object.substituteUnlinkedLibraries missing) =
      MemoryGuard.Object.sizes? object := by
  unfold MemoryGuard.Object.sizes?
  rw [Object.substituteUnlinkedLibraries]
  simp only
  rw [MemoryGuard.Stmt.List.sizes?_substituteUnlinkedLibraries,
    MemoryGuard.FunctionDef.List.sizes?_substituteUnlinkedLibraries]

theorem MemoryGuard.Object.inferredContract?_substituteUnlinkedLibraries
    (missing : List Name) (object : Object) :
    MemoryGuard.Object.inferredContract?
        (object.substituteUnlinkedLibraries missing) =
      MemoryGuard.Object.inferredContract? object := by
  unfold MemoryGuard.Object.inferredContract?
  rw [MemoryGuard.Object.sizes?_substituteUnlinkedLibraries]

/-! ## The substitution bridge, object level -/

namespace NameList

theorem mem_insertUnique_self (name : Name) :
    ∀ names : List Name, name ∈ insertUnique name names
  | [] => by simp [insertUnique]
  | head :: rest => by
      unfold insertUnique
      by_cases hHead : head == name
      · have : head = name := by simpa using hHead
        simp [hHead, this]
      · simp only [hHead, Bool.false_eq_true, if_neg, not_false_eq_true]
        exact List.mem_cons_of_mem head (mem_insertUnique_self name rest)

theorem mem_insertUnique_of_mem {a : Name} (name : Name) :
    ∀ {names : List Name}, a ∈ names → a ∈ insertUnique name names
  | [], h => by cases h
  | head :: rest, h => by
      unfold insertUnique
      by_cases hHead : head == name
      · simpa [hHead] using h
      · simp only [hHead, Bool.false_eq_true, if_neg, not_false_eq_true]
        rcases List.mem_cons.mp h with hHere | hTail
        · exact hHere ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem head (mem_insertUnique_of_mem name hTail)

theorem unique_mem {a : Name} : ∀ {names : List Name},
    a ∈ names → a ∈ unique names
  | [], h => by cases h
  | head :: rest, h => by
      unfold unique
      rcases List.mem_cons.mp h with hHere | hTail
      · exact hHere ▸ mem_insertUnique_self a (unique rest)
      · exact mem_insertUnique_of_mem head (unique_mem hTail)

end NameList

/-- **The unlinked-library bridge.**  Resolving the substituted object with
the missing library addresses supplied as immutable values produces the same
dispatcher and functions as resolving the original object with those
addresses supplied as linker symbols. -/
theorem Object.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
    {missing : List Name} {cSub cOrig : ObjectBuiltinContext}
    (hCtx : LinkBridgeContexts missing cSub cOrig) (object : Object)
    (hNames : ∀ name ∈ object.loadImmutableNames,
      missing.contains name = false) :
    Object.resolveObjectBuiltinsIn?
        (object.substituteUnlinkedLibraries missing) cSub =
      (Object.resolveObjectBuiltinsIn? object cOrig).map
        (fun resolved =>
          { resolved with
              objects :=
                Object.List.substituteUnlinkedLibraries missing
                  object.objects }) := by
  have hDispatcherNames :
      ∀ name ∈ Stmt.List.loadImmutableNames object.dispatcher,
        missing.contains name = false := by
    intro name hMem
    apply hNames
    unfold Object.loadImmutableNames
    have : name ∈ Stmt.List.loadImmutableNames object.dispatcher ++
        FunctionDef.List.loadImmutableNames object.functions :=
      List.mem_append.mpr (Or.inl hMem)
    exact NameList.unique_mem this
  have hFunctionNames :
      ∀ name ∈ FunctionDef.List.loadImmutableNames object.functions,
        missing.contains name = false := by
    intro name hMem
    apply hNames
    unfold Object.loadImmutableNames
    have : name ∈ Stmt.List.loadImmutableNames object.dispatcher ++
        FunctionDef.List.loadImmutableNames object.functions :=
      List.mem_append.mpr (Or.inr hMem)
    exact NameList.unique_mem this
  unfold Object.resolveObjectBuiltinsIn?
  rw [MemoryGuard.Object.inferredContract?_substituteUnlinkedLibraries]
  cases hContract : MemoryGuard.Object.inferredContract? object with
  | none => rfl
  | some memoryContract =>
      have hCtx' := hCtx.withMemoryContract memoryContract
      have hDisp :=
        Stmt.List.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
          hCtx' object.dispatcher hDispatcherNames
      have hFuns :=
        FunctionDef.List.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries
          hCtx' object.functions hFunctionNames
      cases hDispatcher :
          Stmt.List.resolveObjectBuiltinsIn? object.dispatcher
            { cOrig with memoryContract := memoryContract } with
      | none =>
          rw [hDispatcher] at hDisp
          simp [Object.substituteUnlinkedLibraries, hDisp, hDispatcher]
      | some dispatcher =>
          rw [hDispatcher] at hDisp
          cases hFunctions :
              FunctionDef.List.resolveObjectBuiltinsIn? object.functions
                { cOrig with memoryContract := memoryContract } with
          | none =>
              rw [hFunctions] at hFuns
              simp [Object.substituteUnlinkedLibraries, hDisp, hFuns,
                hDispatcher, hFunctions]
          | some functions =>
              rw [hFunctions] at hFuns
              simp [Object.substituteUnlinkedLibraries, hDisp, hFuns,
                hDispatcher, hFunctions]

/-! ## Link windows: 20-byte address writes equal 32-byte word writes -/

namespace Bytecode

private theorem toBytesLE_append (w1 w2 n : Nat) :
    Assembly.Bytecode.toBytesLE (w1 + w2) n =
      Assembly.Bytecode.toBytesLE w1 n ++
        Assembly.Bytecode.toBytesLE w2 (n / 256 ^ w1) := by
  induction w1 generalizing n with
  | zero =>
      simp [Assembly.Bytecode.toBytesLE]
  | succ w ih =>
      have hAdd : w + 1 + w2 = (w + w2) + 1 := by omega
      rw [hAdd]
      simp only [Assembly.Bytecode.toBytesLE, List.cons_append,
        List.cons.injEq, true_and]
      rw [ih]
      have hDiv : n / 256 / 256 ^ w = n / 256 ^ (w + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ w) 256]
      rw [hDiv]

private theorem toBytesLE_zero_val (w : Nat) :
    Assembly.Bytecode.toBytesLE w 0 = List.replicate w 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
      simp [Assembly.Bytecode.toBytesLE, ih, List.replicate_succ]

theorem encodeAddress20_length (value : Word) :
    (encodeAddress20 value).length = 20 := by
  unfold encodeAddress20
  rw [List.length_drop, Assembly.Bytecode.encodeWord32_length]

/-- The 32-byte big-endian encoding of an address-sized word is 12 zero
bytes followed by its 20 address bytes. -/
theorem encodeWord32_eq_zeroPrefix (value : Word)
    (hValue : value.toNat < 2 ^ 160) :
    Assembly.Bytecode.encodeWord32 value =
      List.replicate 12 0 ++ encodeAddress20 value := by
  have hLt : value.toNat < 256 ^ 20 := by
    have h : (256 : Nat) ^ 20 = 2 ^ 160 := by norm_num
    omega
  have hSplit : Assembly.Bytecode.toBytesLE 32 value.toNat =
      Assembly.Bytecode.toBytesLE 20 value.toNat ++ List.replicate 12 0 := by
    have h := toBytesLE_append 20 12 value.toNat
    rw [Nat.div_eq_of_lt hLt, toBytesLE_zero_val] at h
    exact h
  have hWord : Assembly.Bytecode.encodeWord32 value =
      List.replicate 12 0 ++
        (Assembly.Bytecode.toBytesLE 20 value.toNat).reverse := by
    unfold Assembly.Bytecode.encodeWord32
    rw [hSplit, List.reverse_append, List.reverse_replicate]
  rw [hWord]
  unfold encodeAddress20
  rw [hWord]
  congr 1

theorem patchBytesAt_encodeAddress20 {start : Nat} {value : Word}
    {bytes : List UInt8}
    (hValue : value.toNat < 2 ^ 160)
    (hIn : start + 32 ≤ bytes.length)
    (hZero : ∀ i, i < 12 → bytes[start + i]? = some 0) :
    patchBytesAt (start + 12) (encodeAddress20 value) bytes =
      patchBytesAt start (Assembly.Bytecode.encodeWord32 value) bytes := by
  have hEnc := encodeWord32_eq_zeroPrefix value hValue
  have hIn20 : start + 12 + (encodeAddress20 value).length ≤ bytes.length := by
    rw [encodeAddress20_length]
    omega
  have hIn32 : start + (Assembly.Bytecode.encodeWord32 value).length ≤
      bytes.length := by
    rw [Assembly.Bytecode.encodeWord32_length]
    omega
  apply List.ext_getElem?
  intro p
  by_cases h1 : p < start
  · rw [patchBytesAt_getElem?_left hIn20 (by omega),
      patchBytesAt_getElem?_left hIn32 h1]
  · by_cases h2 : p < start + 12
    · rw [patchBytesAt_getElem?_left hIn20 (by omega),
        patchBytesAt_getElem?_inside hIn32 (by omega)
          (by rw [Assembly.Bytecode.encodeWord32_length]; omega)]
      have hIndex : start + (p - start) = p := by omega
      have hBytes : bytes[p]? = some 0 := by
        rw [← hIndex]
        exact hZero (p - start) (by omega)
      rw [hBytes, hEnc,
        List.getElem?_append_left (by simp; omega)]
      rw [List.getElem?_replicate]
      simp
      omega
    · by_cases h3 : p < start + 32
      · rw [patchBytesAt_getElem?_inside hIn20 (by omega)
            (by rw [encodeAddress20_length]; omega),
          patchBytesAt_getElem?_inside hIn32 (by omega)
            (by rw [Assembly.Bytecode.encodeWord32_length]; omega),
          hEnc,
          List.getElem?_append_right (by simp; omega)]
        simp only [List.length_replicate]
        congr 1
      · rw [patchBytesAt_getElem?_right hIn20
            (by rw [encodeAddress20_length]; omega),
          patchBytesAt_getElem?_right hIn32
            (by rw [Assembly.Bytecode.encodeWord32_length]; omega)]

/-! ### Window disjointness -/

theorem windowDisjointFrom?_spec {reference : ImmutableReference}
    {rest : List ImmutableReference}
    (h : windowDisjointFrom? reference rest = true) :
    ∀ s ∈ rest, reference.start + 32 ≤ s.start ∨
      s.start + 32 ≤ reference.start := by
  intro s hMem
  have hAll := (List.all_eq_true.mp h) s hMem
  rcases Bool.or_eq_true_iff.mp hAll with h' | h'
  · exact Or.inl (of_decide_eq_true h')
  · exact Or.inr (of_decide_eq_true h')

theorem windowsPairwiseDisjoint?_cons
    {reference : ImmutableReference} {rest : List ImmutableReference}
    (h : windowsPairwiseDisjoint? (reference :: rest) = true) :
    windowDisjointFrom? reference rest = true ∧
      windowsPairwiseDisjoint? rest = true := by
  simpa [windowsPairwiseDisjoint?, Bool.and_eq_true] using h

theorem windowsPairwiseDisjoint?_append :
    ∀ {left right : List ImmutableReference},
      windowsPairwiseDisjoint? (left ++ right) = true →
      windowsPairwiseDisjoint? left = true ∧
        windowsPairwiseDisjoint? right = true ∧
        ∀ r ∈ left, ∀ s ∈ right,
          r.start + 32 ≤ s.start ∨ s.start + 32 ≤ r.start
  | [], right, h => by
      refine ⟨rfl, h, ?_⟩
      intro r hr
      cases hr
  | reference :: left, right, h => by
      rw [List.cons_append] at h
      obtain ⟨hHead, hTail⟩ := windowsPairwiseDisjoint?_cons h
      obtain ⟨hLeft, hRight, hCross⟩ := windowsPairwiseDisjoint?_append hTail
      have hHeadSpec := windowDisjointFrom?_spec hHead
      refine ⟨?_, hRight, ?_⟩
      · rw [windowsPairwiseDisjoint?, Bool.and_eq_true]
        refine ⟨List.all_eq_true.mpr ?_, hLeft⟩
        intro s hMem
        rcases hHeadSpec s (List.mem_append.mpr (Or.inl hMem)) with h' | h'
        · exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true h'))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true h'))
      · intro r hr s hs
        rcases List.mem_cons.mp hr with hHere | hThere
        · subst hHere
          exact hHeadSpec s (List.mem_append.mpr (Or.inr hs))
        · exact hCross r hThere s hs

/-! ### Group-level equivalence -/

theorem patchLinkReferences_eq_patchImmutableReferences (value : Word)
    (hValue : value.toNat < 2 ^ 160) :
    ∀ (references : List ImmutableReference) (bytes : List UInt8),
      (∀ r ∈ references, r.start + 32 ≤ bytes.length) →
      (∀ r ∈ references, ∀ i, i < 12 → bytes[r.start + i]? = some 0) →
      windowsPairwiseDisjoint? references = true →
      patchLinkReferences value bytes
          (ImmutableReference.linkWindows references) =
        patchImmutableReferences value bytes references
  | [], bytes, _, _, _ => rfl
  | reference :: rest, bytes, hIn, hZero, hDisjoint => by
      obtain ⟨hHead, hTail⟩ := windowsPairwiseDisjoint?_cons hDisjoint
      have hHeadSpec := windowDisjointFrom?_spec hHead
      have hHeadIn := hIn reference (List.mem_cons_self ..)
      have hHeadZero := hZero reference (List.mem_cons_self ..)
      have hWrite := patchBytesAt_encodeAddress20
        (start := reference.start) (value := value) (bytes := bytes)
        hValue hHeadIn hHeadZero
      simp only [ImmutableReference.linkWindows, List.map_cons,
        ImmutableReference.linkWindow, patchLinkReferences,
        patchImmutableReferences]
      rw [hWrite]
      have hIn32 : reference.start +
          (Assembly.Bytecode.encodeWord32 value).length ≤ bytes.length := by
        rw [Assembly.Bytecode.encodeWord32_length]
        omega
      have hLen := patchBytesAt_length
        (start := reference.start)
        (replacement := Assembly.Bytecode.encodeWord32 value)
        (bytes := bytes) hIn32
      have hRest := patchLinkReferences_eq_patchImmutableReferences value
        hValue rest
        (patchBytesAt reference.start
          (Assembly.Bytecode.encodeWord32 value) bytes)
        (by
          intro r hr
          rw [hLen]
          exact hIn r (List.mem_cons_of_mem _ hr))
        (by
          intro r hr i hi
          have hUntouched :
              (patchBytesAt reference.start
                  (Assembly.Bytecode.encodeWord32 value)
                  bytes)[r.start + i]? =
                bytes[r.start + i]? := by
            rcases hHeadSpec r hr with hBefore | hAfter
            · exact patchBytesAt_getElem?_right hIn32
                (by rw [Assembly.Bytecode.encodeWord32_length]; omega)
            · exact patchBytesAt_getElem?_left hIn32 (by omega)
          rw [hUntouched]
          exact hZero r (List.mem_cons_of_mem _ hr) i hi)
        hTail
      exact hRest

/-! ### Whole-image equivalence -/

theorem patchImmutablesAndLibraries_eq_patchImmutables
    (libraryNames : List Name) (values : List (Name × Word)) :
    ∀ (refs : List (Name × List ImmutableReference)) (bytes : List UInt8),
      (∀ e ∈ refs, ∀ r ∈ e.snd, r.start + 32 ≤ bytes.length) →
      windowsPairwiseDisjoint? (refs.flatMap (fun e => e.snd)) = true →
      (∀ e ∈ refs, libraryNames.contains e.fst = true →
        ∀ r ∈ e.snd, ∀ i, i < 12 → bytes[r.start + i]? = some 0) →
      (∀ e ∈ refs, libraryNames.contains e.fst = true →
        ∀ entry, values.find? (fun v => v.fst == e.fst) = some entry →
          entry.snd.toNat < 2 ^ 160) →
      patchImmutablesAndLibraries bytes refs libraryNames values =
        patchImmutables bytes refs values
  | [], bytes, _, _, _, _ => rfl
  | (name, references) :: rest, bytes, hIn, hDisjoint, hZero, hBound => by
      rw [List.flatMap_cons] at hDisjoint
      obtain ⟨hSelf, hRest, hCross⟩ :=
        windowsPairwiseDisjoint?_append hDisjoint
      have hHeadIn := hIn (name, references) (List.mem_cons_self ..)
      have hRestArgs :
          ∀ patched : List UInt8,
            patched.length = bytes.length →
            (∀ p, ¬ CoveredByReferences references p →
              patched[p]? = bytes[p]?) →
            patchImmutablesAndLibraries patched rest libraryNames values =
              patchImmutables patched rest values := by
        intro patched hLen hOutside
        apply patchImmutablesAndLibraries_eq_patchImmutables libraryNames
          values rest patched
        · intro e he r hr
          rw [hLen]
          exact hIn e (List.mem_cons_of_mem _ he) r hr
        · exact hRest
        · intro e he hLib r hr i hi
          have hNotCovered :
              ¬ CoveredByReferences references (r.start + i) := by
            rintro ⟨s, hs, hLo, hHi⟩
            have hMemRest : r ∈ rest.flatMap (fun e => e.snd) :=
              List.mem_flatMap.mpr ⟨e, he, hr⟩
            rcases hCross s hs r hMemRest with h' | h' <;> omega
          rw [hOutside _ hNotCovered]
          exact hZero e (List.mem_cons_of_mem _ he) hLib r hr i hi
        · intro e he hLib entry hFind
          exact hBound e (List.mem_cons_of_mem _ he) hLib entry hFind
      cases hFind : values.find? (fun v => v.fst == name) with
      | none =>
          simp only [patchImmutablesAndLibraries, patchImmutables, hFind]
          exact hRestArgs bytes rfl (fun _ _ => rfl)
      | some entry =>
          have hOutside : ∀ p, ¬ CoveredByReferences references p →
              (patchImmutableReferences entry.snd bytes references)[p]? =
                bytes[p]? :=
            fun p hNC =>
              patchImmutableReferences_getElem?_notCovered hHeadIn hNC
          have hLen := patchImmutableReferences_length
            (value := entry.snd) (references := references)
            (bytes := bytes) hHeadIn
          by_cases hLib : libraryNames.contains name = true
          · have hGroup := patchLinkReferences_eq_patchImmutableReferences
              entry.snd
              (hBound (name, references) (List.mem_cons_self ..) hLib
                entry hFind)
              references bytes hHeadIn
              (hZero (name, references) (List.mem_cons_self ..) hLib)
              hSelf
            simp only [patchImmutablesAndLibraries, patchImmutables, hFind,
              hLib, if_pos]
            rw [hGroup]
            exact hRestArgs _ hLen hOutside
          · have hLib' : libraryNames.contains name = false := by
              simpa using hLib
            simp only [patchImmutablesAndLibraries, patchImmutables, hFind,
              hLib', Bool.false_eq_true, if_neg, not_false_eq_true]
            exact hRestArgs _ hLen hOutside

end Bytecode

/-! ## Context extraction: the artifact context carries the provided
linker symbols -/

private theorem stabilizeObjectCodeBaseArtifact?_context_linkerSymbols
    {α : Type}
    {object : Object} {linkerSymbols : List (Name × Word)}
    {childImages : List ObjectImage}
    {childImmutableReferences : List (Name × List ImmutableReference)}
    {immutableValues dataSizes : List (Name × Word)}
    {items : List ObjectItemRef} {payload : List UInt8}
    {compileArtifactIn? : ObjectBuiltinContext → Option α}
    {artifactBytes : α → List UInt8}
    {fuel candidate : Nat} {plan : Object.ObjectCodeBasePlan} {artifact : α}
    (hStabilize :
      Object.stabilizeObjectCodeBaseArtifact? object linkerSymbols
        childImages childImmutableReferences immutableValues dataSizes items
        payload compileArtifactIn? artifactBytes fuel candidate =
          some (plan, artifact)) :
    plan.context.linkerSymbols = linkerSymbols := by
  induction fuel generalizing candidate with
  | zero =>
      unfold Object.stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, _hLayout, hAfterLayout⟩ :=
        Option.bind_eq_some_iff.mp hStabilize
      obtain ⟨dataOffsets, _hOffsets, hAfterOffsets⟩ :=
        Option.bind_eq_some_iff.mp hAfterLayout
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      change (if (!context.objectDataNamesUnique?) = true then none else
        (compileArtifactIn? context).bind fun compiled =>
          if ((artifactBytes compiled).length == candidate) = true then
            some
              ({ codeBase := candidate, layout, dataOffsets, context },
                compiled)
          else none) = some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, _hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context },
                  compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          rfl
        · simp [hLength] at hAfterCompiled
      · simp [hUnique] at hAfterOffsets
  | succ fuel ih =>
      unfold Object.stabilizeObjectCodeBaseArtifact? at hStabilize
      obtain ⟨layout, _hLayout, hAfterLayout⟩ :=
        Option.bind_eq_some_iff.mp hStabilize
      obtain ⟨dataOffsets, _hOffsets, hAfterOffsets⟩ :=
        Option.bind_eq_some_iff.mp hAfterLayout
      let context : ObjectBuiltinContext :=
        { layout := { entries := layout }
          dataSizes := dataSizes
          dataOffsets := dataOffsets
          linkerSymbols := linkerSymbols
          immutableValues := immutableValues
          immutableReferences := childImmutableReferences
          selfSize? := some
            (object.name, EvmYul.UInt256.ofNat (candidate + payload.length)) }
      change (if (!context.objectDataNamesUnique?) = true then none else
        (compileArtifactIn? context).bind fun compiled =>
          if ((artifactBytes compiled).length == candidate) = true then
            some
              ({ codeBase := candidate, layout, dataOffsets, context },
                compiled)
          else
            Object.stabilizeObjectCodeBaseArtifact? object linkerSymbols
              childImages childImmutableReferences immutableValues dataSizes
              items payload compileArtifactIn? artifactBytes fuel
                (artifactBytes compiled).length) =
          some (plan, artifact) at hAfterOffsets
      by_cases hUnique : context.objectDataNamesUnique?
      · simp only [hUnique, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at hAfterOffsets
        obtain ⟨compiled, _hCompiled, hAfterCompiled⟩ :=
          Option.bind_eq_some_iff.mp hAfterOffsets
        by_cases hLength : (artifactBytes compiled).length = candidate
        · have hEq :
              ({ codeBase := candidate, layout, dataOffsets, context },
                  compiled) =
                (plan, artifact) := by
            simpa [hLength] using hAfterCompiled
          cases hEq
          rfl
        · simp [hLength] at hAfterCompiled
          exact ih hAfterCompiled
      · simp [hUnique] at hAfterOffsets

private theorem planObjectArtifactFromChildImagesArtifactWith?_context_linkerSymbols
    {α : Type}
    {object : Object} {linkerSymbols : List (Name × Word)}
    {childImages : List ObjectImage}
    {compileArtifactIn? : ObjectBuiltinContext → Option α}
    {artifactBytes : α → List UInt8}
    {plan : Object.ObjectArtifactPlan} {artifact : α}
    (hPlan :
      Object.planObjectArtifactFromChildImagesArtifactWith? object
        linkerSymbols childImages compileArtifactIn? artifactBytes =
          some (plan, artifact)) :
    plan.context.linkerSymbols = linkerSymbols := by
  unfold Object.planObjectArtifactFromChildImagesArtifactWith? at hPlan
  obtain ⟨items, _hItems, hAfterItems⟩ :=
    Option.bind_eq_some_iff.mp hPlan
  obtain ⟨dataSizes, _hDataSizes, hAfterDataSizes⟩ :=
    Option.bind_eq_some_iff.mp hAfterItems
  obtain ⟨payload, _hPayload, hAfterPayload⟩ :=
    Option.bind_eq_some_iff.mp hAfterDataSizes
  obtain ⟨stabilizedArtifact, hStabilized, hAfterStabilized⟩ :=
    Option.bind_eq_some_iff.mp hAfterPayload
  rcases stabilizedArtifact with ⟨stabilized, compiled⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at hAfterStabilized
  rcases hAfterStabilized with ⟨hPlanEq, hArtifactEq⟩
  subst plan
  subst artifact
  exact stabilizeObjectCodeBaseArtifact?_context_linkerSymbols hStabilized

theorem Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_context_linkerSymbols
    {object : Object} {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    (hCompile :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    artifact.computed.context.linkerSymbols = linkerSymbols := by
  obtain ⟨_childArtifacts, plan, _codeArtifact, _hChildren, hPlan, _hFinish,
      _hCode, _hChildrenEq, hContextEq, _hChildImages, _hPayload, _hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hCompile
  rw [hContextEq]
  unfold Object.planVerifiedStackObjectArtifactFromChildren? at hPlan
  exact
    planObjectArtifactFromChildImagesArtifactWith?_context_linkerSymbols
      hPlan

/-! ## List helpers for the endpoint contexts -/

private theorem find?_filter_of_imp {α : Type} (p q : α → Bool)
    (h : ∀ x, q x = true → p x = true) :
    ∀ l : List α, (l.filter p).find? q = l.find? q
  | [] => rfl
  | head :: rest => by
      by_cases hq : q head = true
      · have hp := h head hq
        rw [List.filter_cons, if_pos hp, List.find?_cons_of_pos hq,
          List.find?_cons_of_pos hq]
      · have hq' : q head = false := by simpa using hq
        rw [List.find?_cons_of_neg (by simp [hq']), List.filter_cons]
        by_cases hp : p head = true
        · rw [if_pos hp, List.find?_cons_of_neg (by simp [hq'])]
          exact find?_filter_of_imp p q h rest
        · rw [if_neg (by simpa using hp)]
          exact find?_filter_of_imp p q h rest

private theorem find?_append_left_none {α : Type} {p : α → Bool}
    {left : List α}
    (h : left.find? p = none) (right : List α) :
    (left ++ right).find? p = right.find? p := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
      rw [List.find?_cons] at h
      cases hp : p head with
      | true => rw [hp] at h; cases h
      | false =>
          rw [hp] at h
          rw [List.cons_append, List.find?_cons_of_neg (by simp [hp])]
          exact ih h

private theorem find?_append_right_none {α : Type} {p : α → Bool}
    {right : List α}
    (h : right.find? p = none) (left : List α) :
    (left ++ right).find? p = left.find? p := by
  induction left with
  | nil => simpa using h
  | cons head rest ih =>
      cases hp : p head with
      | true =>
          rw [List.cons_append, List.find?_cons_of_pos hp,
            List.find?_cons_of_pos hp]
      | false =>
          rw [List.cons_append, List.find?_cons_of_neg (by simp [hp]),
            List.find?_cons_of_neg (by simp [hp])]
          exact ih

namespace NameList

theorem mem_of_mem_insertUnique {a name : Name} :
    ∀ {names : List Name}, a ∈ insertUnique name names →
      a = name ∨ a ∈ names
  | [], h => by
      unfold insertUnique at h
      rcases List.mem_singleton.mp h with h'
      exact Or.inl h'
  | head :: rest, h => by
      unfold insertUnique at h
      by_cases hHead : head == name
      · rw [if_pos hHead] at h
        exact Or.inr h
      · rw [if_neg hHead] at h
        rcases List.mem_cons.mp h with hHere | hTail
        · exact Or.inr (hHere ▸ List.mem_cons_self ..)
        · rcases mem_of_mem_insertUnique hTail with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons_of_mem head h')

theorem mem_of_unique_mem {a : Name} : ∀ {names : List Name},
    a ∈ unique names → a ∈ names
  | [], h => by cases h
  | head :: rest, h => by
      unfold unique at h
      rcases mem_of_mem_insertUnique h with h' | h'
      · exact h' ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem head (mem_of_unique_mem h')

end NameList

theorem Object.loadImmutableNames_subset_all
    {object : Object} {name : Name}
    (h : name ∈ object.loadImmutableNames) :
    name ∈ object.allLoadImmutableNames := by
  unfold Object.loadImmutableNames at h
  have hMem := NameList.mem_of_unique_mem h
  rw [Object.allLoadImmutableNames]
  apply NameList.unique_mem
  rcases List.mem_append.mp hMem with h' | h'
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h')))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h')))

/-! ## Gate elimination -/

theorem Object.unlinkedLibraryGate?_elim
    {object : Object} {missing : List Name}
    {artifact : VerifiedStackObjectArtifact}
    (hGate : object.unlinkedLibraryGate? missing artifact = true) :
    (∀ name ∈ missing,
      object.allLoadImmutableNames.contains name = false) ∧
    Bytecode.windowsPairwiseDisjoint?
      ((artifact.ownImmutableReferences
          (object.substituteUnlinkedLibraries missing)).flatMap
        (fun entry => entry.snd)) = true ∧
    (∀ entry ∈ artifact.ownImmutableReferences
        (object.substituteUnlinkedLibraries missing),
      ∀ reference ∈ entry.snd,
        reference.start + 32 ≤ artifact.image.bytes.length) ∧
    (∀ entry ∈ artifact.ownImmutableReferences
        (object.substituteUnlinkedLibraries missing),
      missing.contains entry.fst = true →
      ∀ reference ∈ entry.snd,
        Bytecode.startsWithAt (List.replicate 12 0)
          artifact.image.bytes reference.start = true) := by
  unfold Object.unlinkedLibraryGate? at hGate
  simp only [Bool.and_eq_true, List.all_eq_true] at hGate
  obtain ⟨⟨⟨hNames, hDisjoint⟩, hBounds⟩, hZeros⟩ := hGate
  refine ⟨?_, hDisjoint, ?_, ?_⟩
  · intro name hMem
    have := hNames name hMem
    simpa using this
  · intro entry hEntry reference hReference
    exact of_decide_eq_true (hBounds entry hEntry reference hReference)
  · intro entry hEntry hLib reference hReference
    have hOr := hZeros entry hEntry
    rcases Bool.or_eq_true_iff.mp hOr with h' | h'
    · rw [hLib] at h'
      cases h'
    · exact (List.all_eq_true.mp h') reference hReference

/-! ## Link-time patch endpoint -/

/-- **Link-time patching is the value compile, unconditionally.**  For any
successful unlinked compile (the exported pipeline plus the fail-closed
link gate) and any successful code compile with deploy `values` in the
artifact's own context, patching the exported image bytes — ordinary
32-byte window writes for immutables, solc-shaped 20-byte address writes at
`start + 12` for the unlinked library windows — reproduces the value
compile's code bytes followed by the unchanged payload.  The only semantic
hypothesis is that the library addresses are address-sized. -/
theorem Object.patchImmutablesAndLibraries_image_ofCompileUnlinked
    {object : Object} {provided values : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {withValues : Object.VerifiedStackCodeArtifact}
    (hUnlinked :
      object.compileVerifiedStackObjectArtifactUnlinked? provided =
        some artifact)
    (hValues :
      Object.compileVerifiedStackCodeArtifactWithImmutableValues?
        (object.substituteUnlinkedLibraries
          (object.missingLinkerSymbolNames provided))
        artifact.computed.context values = some withValues)
    (hAddresses : ∀ name,
      (object.missingLinkerSymbolNames provided).contains name = true →
      ∀ entry, values.find? (fun v => v.fst == name) = some entry →
        entry.snd.toNat < 2 ^ 160) :
    Bytecode.patchImmutablesAndLibraries artifact.image.bytes
      (artifact.ownImmutableReferences
        (object.substituteUnlinkedLibraries
          (object.missingLinkerSymbolNames provided)))
      (object.missingLinkerSymbolNames provided) values =
      withValues.bytes ++ artifact.computed.payload := by
  obtain ⟨hInner, hGate⟩ :=
    Object.compileVerifiedStackObjectArtifactUnlinked?_parts hUnlinked
  obtain ⟨_hNames, hDisjoint, hBounds, hZeros⟩ :=
    Object.unlinkedLibraryGate?_elim hGate
  have hZeroPt : ∀ entry ∈ artifact.ownImmutableReferences
      (object.substituteUnlinkedLibraries
        (object.missingLinkerSymbolNames provided)),
      (object.missingLinkerSymbolNames provided).contains entry.fst = true →
      ∀ reference ∈ entry.snd, ∀ i, i < 12 →
        artifact.image.bytes[reference.start + i]? = some 0 := by
    intro entry hEntry hLib reference hReference i hi
    have hStarts := hZeros entry hEntry hLib reference hReference
    have := Bytecode.getElem?_of_startsWithAt hStarts
      (Nat.le_add_right _ _)
      (by simpa using hi)
    rw [this]
    have hSub : reference.start + i - reference.start = i := by omega
    rw [hSub, List.getElem?_replicate, if_pos hi]
  rw [Bytecode.patchImmutablesAndLibraries_eq_patchImmutables
    (object.missingLinkerSymbolNames provided) values
    (artifact.ownImmutableReferences
      (object.substituteUnlinkedLibraries
        (object.missingLinkerSymbolNames provided)))
    artifact.image.bytes hBounds hDisjoint hZeroPt
    (fun entry hEntry hLib e hFind => hAddresses entry.fst hLib e hFind)]
  exact
    Object.patchImmutables_image_compileWithImmutableValues?_ofCompile
      hInner hValues

/-! ## The value compile resolves the original object -/

theorem Object.toSolcYulOrderedProgram?_setObjects
    (object : Object) (objects : List Object) :
    Object.toSolcYulOrderedProgram? { object with objects := objects } =
      object.toSolcYulOrderedProgram? :=
  rfl

/-- **Patching addresses in is compiling with those addresses.**  The
resolved source whose compile the patch endpoint reproduces is exactly the
original (unsubstituted) object resolved with the deploy addresses supplied
as linker symbols alongside the provided ones — and its ordered Yul program
is the value compile's own ordered program, so every downstream semantic
theorem about the supported pipeline applies to the linked result as a
compile of the original source. -/
theorem Object.compileVerifiedStackObjectArtifactUnlinked?_withValues_resolvesOriginal
    {object : Object} {provided values : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {withValues : Object.VerifiedStackCodeArtifact}
    (hUnlinked :
      object.compileVerifiedStackObjectArtifactUnlinked? provided =
        some artifact)
    (hValues :
      Object.compileVerifiedStackCodeArtifactWithImmutableValues?
        (object.substituteUnlinkedLibraries
          (object.missingLinkerSymbolNames provided))
        artifact.computed.context values = some withValues) :
    ∃ resolvedOriginal : Object,
      object.resolveObjectBuiltinsIn?
          { artifact.computed.context with
              linkerSymbols :=
                artifact.computed.context.linkerSymbols ++
                  values.filter (fun entry =>
                    (object.missingLinkerSymbolNames provided).contains
                      entry.fst)
              immutableValues :=
                values.filter (fun entry =>
                  !((object.missingLinkerSymbolNames provided).contains
                    entry.fst)) } =
        some resolvedOriginal ∧
      withValues.resolved =
        { resolvedOriginal with
            objects :=
              Object.List.substituteUnlinkedLibraries
                (object.missingLinkerSymbolNames provided) object.objects } ∧
      resolvedOriginal.toSolcYulOrderedProgram? = some withValues.ordered := by
  obtain ⟨hInner, hGate⟩ :=
    Object.compileVerifiedStackObjectArtifactUnlinked?_parts hUnlinked
  obtain ⟨hDisjointNames, _hDisjoint, _hBounds, _hZeros⟩ :=
    Object.unlinkedLibraryGate?_elim hGate
  set missing := object.missingLinkerSymbolNames provided with hMissing
  set ctx := artifact.computed.context with hCtxDef
  have hLinker :
      ctx.linkerSymbols = provided :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_context_linkerSymbols
      hInner
  -- the two contexts of the bridge
  set cSub : ObjectBuiltinContext := { ctx with immutableValues := values }
    with hCSub
  set cOrig : ObjectBuiltinContext :=
    { ctx with
        linkerSymbols := ctx.linkerSymbols ++
          values.filter (fun entry => missing.contains entry.fst)
        immutableValues :=
          values.filter (fun entry => !(missing.contains entry.fst)) }
    with hCOrig
  have hProvidedNone : ∀ name, missing.contains name = true →
      provided.find? (fun entry => entry.fst == name) = none := by
    intro name hContains
    have hMem : name ∈ missing := by
      simpa using hContains
    rw [hMissing] at hMem
    unfold Object.missingLinkerSymbolNames at hMem
    have := List.of_mem_filter hMem
    simpa [Option.isNone_iff_eq_none] using this
  have hCtx : LinkBridgeContexts missing cSub cOrig := by
    constructor
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro name hContains
      show ObjectBuiltinContext.findImmutableValue? cSub name =
        ObjectBuiltinContext.findLinkerSymbol? cOrig name
      unfold ObjectBuiltinContext.findImmutableValue?
        ObjectBuiltinContext.findLinkerSymbol?
      simp only [hCSub, hCOrig]
      rw [find?_append_left_none (by rw [hLinker]; exact hProvidedNone name hContains)]
      rw [find?_filter_of_imp _ _ (fun entry hq => by
        have hEq : entry.fst = name := by simpa using hq
        rw [hEq]
        exact hContains)]
    · intro name hContains
      show ObjectBuiltinContext.findImmutableValue? cSub name =
        ObjectBuiltinContext.findImmutableValue? cOrig name
      unfold ObjectBuiltinContext.findImmutableValue?
      simp only [hCSub, hCOrig]
      rw [find?_filter_of_imp _ _ (fun entry hq => by
        have hEq : entry.fst = name := by simpa using hq
        rw [hEq, hContains]
        rfl)]
    · intro name hContains
      show ObjectBuiltinContext.findLinkerSymbol? cSub name =
        ObjectBuiltinContext.findLinkerSymbol? cOrig name
      unfold ObjectBuiltinContext.findLinkerSymbol?
      simp only [hCSub, hCOrig]
      rw [find?_append_right_none (by
        apply List.find?_eq_none.mpr
        intro entry hEntry hBeq
        have hEq : entry.fst = name := by simpa using hBeq
        have hLib := List.of_mem_filter hEntry
        rw [hEq, hContains] at hLib
        cases hLib)]
  have hNamesFree : ∀ name ∈ object.loadImmutableNames,
      missing.contains name = false := by
    intro name hMem
    by_cases hContains : missing.contains name = true
    · have hName : name ∈ missing := by simpa using hContains
      have := hDisjointNames name hName
      have hAll : name ∈ object.allLoadImmutableNames :=
        Object.loadImmutableNames_subset_all hMem
      rw [List.contains_eq_mem] at this
      simp [hAll] at this
    · simpa using hContains
  have hBridge :=
    Object.resolveObjectBuiltinsIn?_substituteUnlinkedLibraries hCtx object
      hNamesFree
  obtain ⟨hResolved, hOrdered, _hLower, _hCompiled, _pushPlan, _hPlan,
      _hCompact, _hBytes, _hMarker⟩ :=
    Object.compileVerifiedStackCodeArtifactIn?_parts hValues
  rw [hBridge] at hResolved
  cases hOrig : object.resolveObjectBuiltinsIn? cOrig with
  | none =>
      rw [hOrig] at hResolved
      cases hResolved
  | some resolvedOriginal =>
      rw [hOrig] at hResolved
      simp only [Option.map_some, Option.some.injEq] at hResolved
      refine ⟨resolvedOriginal, rfl, hResolved.symm, ?_⟩
      rw [← hOrdered, ← hResolved,
        Object.toSolcYulOrderedProgram?_setObjects]

end Frontend
end Solidity
end EvmCompiler
