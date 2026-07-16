import EvmCompiler.Structured.TypedCfgPreservation.Core
import EvmCompiler.TypedCfg.PeepholeStackRealizes

/-!
# Block-entry target-stack realization (Route A substrate for the swap peephole)

The `swap d ; swap d → ε` peephole arm needs, at every straight-line body it
rewrites, the runtime depth guard `d + 2 ≤ target.stack.length`.  Via
`TypedCfg.runBody_stackRealizes` (landed) this only has to be established at each
**block entry** as `TypedCfg.StackRealizes input target`, i.e.
`input.length ≤ target.stack.length`, where `target` is the *cfg* EVM state.

Sessions 5–7 established that this full-length target bound is **not** a
standalone invariant of `openRunN` over arbitrary well-typed programs (a caller-
tailed block may be jumped to "wider" than the jumping block's output, so the
extra depth is a runtime call-convention property, not a CFG-typing property).
The maintained invariant is instead the strictly weaker
`TypedCfgCompiler.Shape.SourceFrameFits shape source.evm.stack.length` — which
bounds only the *source-visible* prefix (`sourceLength`, the slots above the
return token) — threaded together with `StateRel` and `ActivationFrameMatches`
across the whole-program Structured→cfg simulation.

This module is the reusable bridge from that maintained invariant to the
target-stack realization the swap arm consumes.  It splits the problem exactly
along the return-token boundary:

* **`stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none`** — the closed /
  token-free half closes **outright** from `StateRel` + `SourceFrameFits`:
  with no return token `sourceLength = length`, and `StateRel` only *appends*
  realized frames beneath the source stack, so
  `input.length = sourceLength ≤ source.stack.length ≤ target.stack.length`.

* **`stackRealizes_of_stateRel`** — the general reduction.  It proves
  `StackRealizes shape target` from `StateRel` + `SourceFrameFits` **plus** one
  crisp residual hypothesis `hBelow`:
  `shape.length - depth ≤ hidden.length`, where `depth = returnTokenDepth?` and
  `hidden = realizeStack [] source.returns tokens` is the realized ghost caller
  frame.  This is the single "the shape's slots at and below the return token
  are covered by the realized caller frame" fact that sessions 6/7 located as the
  deep blocker — here isolated to its minimal form.

* **`stackRealizes_of_stateRel_of_token_last`** — discharges `hBelow` for exactly
  the shapes the compiler emits at procedure entries.  `TypedCfgCompiler` places
  `.returnToken` as the **last** slot of every procedure input shape
  (`TypedCfgCompiler.lean:147/153/160/935`), so `depth = shape.length - 1` and
  `shape.length - depth = 1`; the residual collapses to "the realized frame is
  non-empty", which follows from `source.returns ≠ []` (being inside a
  procedure).  What remains for a full spine wiring is the *structural* fact that
  every reachable block-**input** shape keeps its token at the bottom (or has
  none) and the source coupling `returnTokenDepth? = some _ → source.returns ≠ []`
  — both far simpler than the general below-token layout invariant, and
  documented in `PEEPHOLE_PROGRESS.md`.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

open Assembly

/--
`realizeStack` only ever *appends* to its seed, so a successful realization is at
least as tall as the seed.  (Immediate from `realizeStack_append_prefix` with an
empty tail.)
-/
theorem realizeStack_seed_le
    {seed out : EvmYul.Stack Word}
    {returns : List ReturnDest} {tokens : List Word}
    (h : realizeStack seed returns tokens = some out) :
    seed.length ≤ out.length := by
  have hAppend :=
    realizeStack_append_prefix seed [] returns tokens
  simp only [List.append_nil] at hAppend
  rw [hAppend] at h
  rcases hBase : realizeStack [] returns tokens with _ | base
  · rw [hBase] at h; simp at h
  · rw [hBase] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    simp [List.length_append]

/--
A live return frame realizes to a non-empty hidden suffix: the first frame
contributes at least its return token.
-/
theorem realizeStack_length_pos_of_returns_ne_nil
    {out : EvmYul.Stack Word}
    {returns : List ReturnDest} {tokens : List Word}
    (hReturns : returns ≠ [])
    (h : realizeStack [] returns tokens = some out) :
    1 ≤ out.length := by
  cases returns with
  | nil => exact absurd rfl hReturns
  | cons frame rest =>
      cases tokens with
      | nil => simp [realizeStack] at h
      | cons token tokens =>
          -- first step seeds the accumulator with `token :: frame.callerStack`
          have hStep :
              realizeStack ([] ++ [token] ++ frame.callerStack) rest tokens =
                some out := by
            simpa [realizeStack] using h
          have hSeed := realizeStack_seed_le hStep
          simp only [List.nil_append, List.length_append,
            List.length_cons, List.length_nil] at hSeed
          omega

/--
**Route A reduction.**  The block-entry target-stack realization
`StackRealizes shape target` follows from the maintained source invariants
`StateRel` + `SourceFrameFits`, plus the single residual "below-token slots are
realized-frame slots" fact `hBelow`.  When there is no return token `hBelow` is
vacuous and this closes unconditionally
(see `stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none`).
-/
theorem stackRealizes_of_stateRel
    {source : RunState} {tokens : List Word}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hRel : StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape source.evm.stack.length)
    (hBelow :
      ∀ depth hidden,
        shape.returnTokenDepth? = some depth →
        realizeStack [] source.returns tokens = some hidden →
        shape.length - depth ≤ hidden.length) :
    TypedCfg.StackRealizes shape target := by
  apply TypedCfg.StackRealizes.of_le
  rcases hRel with ⟨realized, hRealize, hSame⟩
  have hAppend :=
    realizeStack_append_prefix source.evm.stack [] source.returns tokens
  simp only [List.append_nil] at hAppend
  rw [hAppend] at hRealize
  rcases hHidden : realizeStack [] source.returns tokens with _ | hidden
  · rw [hHidden] at hRealize; simp at hRealize
  · rw [hHidden] at hRealize
    simp only [Option.map_some, Option.some.injEq] at hRealize
    subst hRealize
    have hTargetStack :
        target.stack = source.evm.stack ++ hidden := by
      simpa using Assembly.SameRuntimeData.stack_eq hSame
    have hLen :
        target.stack.length = source.evm.stack.length + hidden.length := by
      rw [hTargetStack, List.length_append]
    cases hDepth : shape.returnTokenDepth? with
    | none =>
        have hSrc :
            TypedCfgCompiler.Shape.sourceLength shape = shape.length := by
          simp [TypedCfgCompiler.Shape.sourceLength,
            TypedCfgCompiler.Shape.sourceView, hDepth, TypedCfg.Shape.length]
        have hFit := hFits.1
        rw [hSrc] at hFit
        omega
    | some depth =>
        have hSrcLen : source.evm.stack.length = depth := hFits.2 depth hDepth
        have hBT := hBelow depth hidden hDepth hHidden
        have hLt :=
          TypedCfgCompilerFacts.Shape.returnTokenDepth?_lt_length hDepth
        omega

/--
**Closed / token-free half — closes unconditionally.**  For a block whose input
shape carries no compiler-owned return token, `StateRel` + `SourceFrameFits`
already give the full target-stack realization the swap arm needs.
-/
theorem stackRealizes_of_stateRel_of_returnTokenDepth?_eq_none
    {source : RunState} {tokens : List Word}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hRel : StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape source.evm.stack.length)
    (hDepth : shape.returnTokenDepth? = none) :
    TypedCfg.StackRealizes shape target :=
  stackRealizes_of_stateRel hRel hFits
    (fun _ _ hSome _ => by rw [hDepth] at hSome; cases hSome)

/--
**Procedure-entry half.**  When the return token sits at the bottom of the
visible shape (`depth = shape.length - 1`, as `TypedCfgCompiler` emits for every
procedure input shape) and the source is inside a live procedure activation
(`source.returns ≠ []`), the residual `hBelow` collapses to "the realized frame
is non-empty" and the full realization holds.
-/
theorem stackRealizes_of_stateRel_of_token_last
    {source : RunState} {tokens : List Word}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hRel : StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape source.evm.stack.length)
    (hLast : shape.returnTokenDepth? = some (shape.length - 1))
    (hFrames : source.returns ≠ []) :
    TypedCfg.StackRealizes shape target := by
  apply stackRealizes_of_stateRel hRel hFits
  intro depth hidden hDepth hHidden
  have hDepthEq : depth = shape.length - 1 :=
    Option.some.inj (hDepth.symm.trans hLast)
  have hPos :=
    realizeStack_length_pos_of_returns_ne_nil hFrames hHidden
  have hLt :=
    TypedCfgCompilerFacts.Shape.returnTokenDepth?_lt_length hDepth
  omega

end TypedCfgPreservation
end Structured
end EvmCompiler
