import EvmCompiler.TypedCfg.ShuffleCanonChainStep

/-!
# Chain-transform residual construction (session-82)

Item 1 (residual construction) of the PEEPHOLE_PROGRESS §Session-81 frontier: define
a concrete `residual : Label → List Nat` and discharge `ChainResidualSpec program
residual`, closing the last hypothesis of the §81 step congruence
`openStep_chainCanon_congr`.

`residual` follows the terminator chain through *consumed* members, accumulating each
member's runtime swap positions (`bodyRunPositions`).  The construction is fuel-bounded
(fuel = `blocks.length`); the correctness reduces, via a for-all-fuel suffix induction,
to the banked chain-consistency (`growChain`/`editTable`/`consumed_edit_spec`/
`head_edit_spec`/`chainEdits_fired`).

Imported by **nobody** in the spine ⟹ cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState)
open ShuffleCanon (editTable Edit chainCanonProgram chainBodyDepths?)

/-! ## The residual definition (fuel-bounded terminator-follow through consumed members) -/

/-- One-fuel unfolding of the residual: the current block's runtime swap positions,
plus (when its terminator jumps to a *consumed* successor) the successor's residual. -/
def residualAux (program : Program) : Nat → Label → List Nat
  | 0, _ => []
  | fuel + 1, label =>
      match program.findBlock? label with
      | none => []
      | some b0 =>
          bodyRunPositions b0.body ++
            (match b0.term with
             | .jump next =>
                 match (editTable program).lookup next with
                 | some (.consumed _) => residualAux program fuel next
                 | _ => []
             | _ => [])

/-- The concrete per-label residual consumed by `ChainResidualSpec`: a terminator-follow
through consumed members bounded by the block count. -/
def residual (program : Program) (label : Label) : List Nat :=
  residualAux program program.blocks.length label

/-! ## The `merged` ↔ `flatMap bodyRunPositions` bridge -/

/-- A chain-eligible body's runtime positions are its stored depths shifted by one
(the `getD` form). -/
theorem bodyRunPositions_eq_getD {body : List Instr}
    (h : (chainBodyDepths? body).isSome) :
    bodyRunPositions body = ((chainBodyDepths? body).getD []).map (· + 1) := by
  cases hd : chainBodyDepths? body with
  | none => rw [hd] at h; simp at h
  | some ds =>
      rw [bodyRunPositions_eq_of_chainBodyDepths hd]; simp [hd]

/-- **The merged bridge.**  For a chain of eligible blocks, the concatenated depths
shifted by one equal the concatenated runtime positions:
`(chain.flatMap depths).map (·+1) = chain.flatMap bodyRunPositions`. -/
theorem merged_map_succ_eq_flatMap (chain : List Block)
    (helig : ∀ b ∈ chain, (chainBodyDepths? b.body).isSome) :
    (chain.flatMap (fun b => (chainBodyDepths? b.body).getD [])).map (· + 1)
      = chain.flatMap (fun b => bodyRunPositions b.body) := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro b hb
  exact (bodyRunPositions_eq_getD (helig b hb)).symm

/-! ## The residual run predicate + the for-all-fuel suffix induction -/

/-- A *residual run* is a list of consumed chain members threaded by the terminator
follow: each non-last member jumps to the next (a consumed successor), and the last
member's terminator does not jump to any consumed block.  This is exactly the shape the
fuel-bounded `residualAux` walks. -/
def IsResidualRun (program : Program) : List Block → Prop
  | [] => True
  | [Z] =>
      program.findBlock? Z.label = some Z ∧
      ∀ W o, Z.term = Terminator.jump W →
        (editTable program).lookup W ≠ some (Edit.consumed o)
  | C :: D :: rest =>
      program.findBlock? C.label = some C ∧
      C.term = Terminator.jump D.label ∧
      (∃ o, (editTable program).lookup D.label = some (Edit.consumed o)) ∧
      IsResidualRun program (D :: rest)

/-- **The residual walk realises the run's concatenated positions.**  On a residual run
`C :: cs` with fuel at least its length, `residualAux` returns exactly the concatenated
`bodyRunPositions` of the run's members. -/
theorem residualAux_of_run {program : Program} :
    ∀ (cs : List Block) (C : Block) (fuel : Nat),
      IsResidualRun program (C :: cs) →
      (C :: cs).length ≤ fuel →
      residualAux program fuel C.label = (C :: cs).flatMap (fun b => bodyRunPositions b.body)
  | [], C, fuel, hrun, hlen => by
      obtain ⟨hfind, hlast⟩ := hrun
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [residualAux, hfind, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have hbranch :
              (match C.term with
               | .jump next =>
                   match (editTable program).lookup next with
                   | some (.consumed _) => residualAux program f next
                   | _ => []
               | _ => []) = ([] : List Nat) := by
            cases hterm : C.term with
            | jump W =>
                cases hlk : (editTable program).lookup W with
                | none => simp only [hlk]
                | some e =>
                    cases e with
                    | head _ _ => simp only [hlk]
                    | consumed o => exact absurd hlk (hlast W o hterm)
            | fallthrough _ => rfl
            | jumpi _ _ => rfl
            | returnDispatch _ _ => rfl
            | halt _ => rfl
            | invalid => rfl
          rw [hbranch, List.append_nil]
  | D :: rest, C, fuel, hrun, hlen => by
      obtain ⟨hfind, hterm, ⟨o, hlkD⟩, hrun'⟩ := hrun
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          have hlen' : (D :: rest).length ≤ f := by
            simp only [List.length_cons] at hlen ⊢; omega
          have hIH := residualAux_of_run rest D f hrun' hlen'
          simp only [residualAux, hfind, hterm, hlkD, hIH]
          simp only [List.flatMap_cons]

end Peephole
end TypedCfg
end EvmCompiler
