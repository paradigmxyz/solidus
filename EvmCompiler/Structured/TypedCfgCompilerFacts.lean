import EvmCompiler.Structured.TypedCfgCompiler

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompilerFacts

open Assembly

namespace Result

theorem requireFallthrough?_eq_some_iff
    {result : TypedCfgCompiler.Result} {expected : TypedCfg.Shape} :
    result.requireFallthrough? expected = some () ↔
      result.fallthrough? = none ∨
        result.fallthrough? = some expected := by
  cases hFallthrough : result.fallthrough? with
  | none =>
      simp [TypedCfgCompiler.Result.requireFallthrough?, hFallthrough]
  | some actual =>
      by_cases hShape : actual = expected
      · subst actual
        simp [TypedCfgCompiler.Result.requireFallthrough?, hFallthrough]
      · simp [TypedCfgCompiler.Result.requireFallthrough?,
          hFallthrough, hShape]

end Result

namespace Shape

namespace SourceFrameFits

theorem bound
    {shape : TypedCfg.Shape} {stackLength : Nat}
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape stackLength) :
    TypedCfgCompiler.Shape.sourceLength shape ≤ stackLength :=
  hFits.1

theorem exact
    {shape : TypedCfg.Shape} {stackLength depth : Nat}
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape stackLength)
    (hDepth : shape.returnTokenDepth? = some depth) :
    stackLength = depth :=
  hFits.2 depth hDepth

end SourceFrameFits

theorem sourceLength_eq_of_returnTokenDepth?_eq_some
    {shape : TypedCfg.Shape} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    TypedCfgCompiler.Shape.sourceLength shape = depth := by
  rcases shape with ⟨slots, tail⟩
  unfold TypedCfgCompiler.Shape.sourceLength
    TypedCfgCompiler.Shape.sourceView
  rw [hDepth]
  simp only [TypedCfg.Shape.length]
  unfold TypedCfg.Shape.returnTokenDepth? at hDepth
  induction slots generalizing depth with
  | nil =>
      simp [TypedCfg.Shape.returnTokenDepthList?] at hDepth
  | cons slot rest ih =>
      cases slot
      case returnToken | returnPC =>
        simp [TypedCfg.Shape.returnTokenDepthList?] at hDepth
        subst depth
        simp
      all_goals
        simp only [TypedCfg.Shape.returnTokenDepthList?,
          Option.map_eq_some_iff] at hDepth
        obtain ⟨restDepth, hRest, rfl⟩ := hDepth
        simp only [List.take_succ_cons, List.length_cons]
        have hTake := ih hRest
        omega

theorem returnTokenDepth?_lt_length
    {shape : TypedCfg.Shape} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    depth < shape.length := by
  rcases shape with ⟨slots, tail⟩
  unfold TypedCfg.Shape.returnTokenDepth? at hDepth
  change depth < slots.length
  induction slots generalizing depth with
  | nil =>
      simp [TypedCfg.Shape.returnTokenDepthList?] at hDepth
  | cons slot rest ih =>
      cases slot
      case returnToken | returnPC =>
        simp [TypedCfg.Shape.returnTokenDepthList?] at hDepth
        subst depth
        simp
      all_goals
        simp only [TypedCfg.Shape.returnTokenDepthList?,
          Option.map_eq_some_iff] at hDepth
        obtain ⟨restDepth, hRest, rfl⟩ := hDepth
        simp only [List.length_cons]
        have hRestLt := ih hRest
        omega

theorem sourceView_eq_self_of_returnTokenDepth?_eq_none
    {shape : TypedCfg.Shape}
    (hDepth : shape.returnTokenDepth? = none) :
    TypedCfgCompiler.Shape.sourceView shape = shape := by
  simp [TypedCfgCompiler.Shape.sourceView, hDepth]

theorem sourceView_ne_self_of_returnTokenDepth?_eq_some
    {shape : TypedCfg.Shape} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    TypedCfgCompiler.Shape.sourceView shape ≠ shape := by
  intro hEq
  have hLengthEq :
      (TypedCfgCompiler.Shape.sourceView shape).length = shape.length :=
    congrArg TypedCfg.Shape.length hEq
  have hSourceLength :
      (TypedCfgCompiler.Shape.sourceView shape).length = depth := by
    simpa [TypedCfgCompiler.Shape.sourceLength] using
      sourceLength_eq_of_returnTokenDepth?_eq_some hDepth
  have hLt := returnTokenDepth?_lt_length hDepth
  omega

theorem sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
    {shape : TypedCfg.Shape} {stackLength depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    TypedCfgCompiler.Shape.SourceFrameFits shape stackLength ↔
      stackLength = depth := by
  constructor
  · intro hFits
    exact hFits.2 depth hDepth
  · intro hLength
    constructor
    · rw [sourceLength_eq_of_returnTokenDepth?_eq_some hDepth,
        hLength]
    · intro actualDepth hActual
      have : actualDepth = depth :=
        Option.some.inj (hActual.symm.trans hDepth)
      simpa [this] using hLength

theorem sourceFrameFits_of_returnTokenDepth?_eq_none
    {shape : TypedCfg.Shape} {stackLength : Nat}
    (hDepth : shape.returnTokenDepth? = none)
    (hBound :
      TypedCfgCompiler.Shape.sourceLength shape ≤ stackLength) :
    TypedCfgCompiler.Shape.SourceFrameFits shape stackLength := by
  exact
    ⟨hBound, fun depth hSome => by
      rw [hDepth] at hSome
      cases hSome⟩

theorem requireSourceWords?_eq_some_iff
    {count : Nat} {shape : TypedCfg.Shape} :
    TypedCfgCompiler.Shape.requireSourceWords? count shape = some () ↔
      count ≤ TypedCfgCompiler.Shape.sourceLength shape := by
  simp [TypedCfgCompiler.Shape.requireSourceWords?]

theorem requireReturnTokenDepth?_eq_some_iff
    {depth : Nat} {shape : TypedCfg.Shape} :
    TypedCfgCompiler.Shape.requireReturnTokenDepth? depth shape = some () ↔
      shape.returnTokenDepth? = some depth := by
  simp [TypedCfgCompiler.Shape.requireReturnTokenDepth?]

theorem sourceLength_le_length (shape : TypedCfg.Shape) :
    TypedCfgCompiler.Shape.sourceLength shape ≤ shape.length := by
  unfold TypedCfgCompiler.Shape.sourceLength
    TypedCfgCompiler.Shape.sourceView
  split <;> simp [TypedCfg.Shape.length]

theorem sourceLength_tail_of_one_le
    (shape : TypedCfg.Shape)
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape) :
    TypedCfgCompiler.Shape.sourceLength
        { shape with slots := shape.slots.tail } =
      TypedCfgCompiler.Shape.sourceLength shape - 1 := by
  rcases shape with ⟨slots, tail⟩
  cases slots with
  | nil =>
      simp [TypedCfgCompiler.Shape.sourceLength,
        TypedCfgCompiler.Shape.sourceView, TypedCfg.Shape.length,
        TypedCfg.Shape.returnTokenDepth?,
        TypedCfg.Shape.returnTokenDepthList?] at hSource
  | cons slot rest =>
      cases slot <;>
        simp [TypedCfgCompiler.Shape.sourceLength,
          TypedCfgCompiler.Shape.sourceView, TypedCfg.Shape.length,
          TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] at hSource ⊢
      all_goals
        cases hDepth :
            TypedCfg.Shape.returnTokenDepthList? rest <;>
          simp [hDepth, TypedCfgCompiler.Shape.sourceLength,
            TypedCfgCompiler.Shape.sourceView, TypedCfg.Shape.length,
            TypedCfg.Shape.returnTokenDepth?,
            TypedCfg.Shape.returnTokenDepthList?] at hSource ⊢

theorem returnTokenDepth?_tail_lift
    {shape : TypedCfg.Shape} {depth : Nat}
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (hTail :
      ({ shape with slots := shape.slots.tail } :
        TypedCfg.Shape).returnTokenDepth? = some depth) :
    shape.returnTokenDepth? = some (depth + 1) := by
  rcases shape with ⟨slots, tail⟩
  cases slots with
  | nil =>
      simp [TypedCfgCompiler.Shape.sourceLength,
        TypedCfgCompiler.Shape.sourceView, TypedCfg.Shape.length,
        TypedCfg.Shape.returnTokenDepth?,
        TypedCfg.Shape.returnTokenDepthList?] at hSource
  | cons slot rest =>
      cases slot
      case returnToken | returnPC =>
        simp [TypedCfgCompiler.Shape.sourceLength,
          TypedCfgCompiler.Shape.sourceView, TypedCfg.Shape.length,
          TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] at hSource
      all_goals
        simpa [TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] using hTail

theorem returnTokenDepth?_some_of_tail_some
    {shape : TypedCfg.Shape} {depth : Nat}
    (hTail :
      ({ shape with slots := shape.slots.tail } :
        TypedCfg.Shape).returnTokenDepth? = some depth) :
    ∃ inputDepth, shape.returnTokenDepth? = some inputDepth := by
  rcases shape with ⟨slots, tail⟩
  cases slots with
  | nil =>
      simp [TypedCfg.Shape.returnTokenDepth?,
        TypedCfg.Shape.returnTokenDepthList?] at hTail
  | cons slot rest =>
      cases slot
      case returnToken | returnPC =>
        exact
          ⟨0, by
            simp [TypedCfg.Shape.returnTokenDepth?,
              TypedCfg.Shape.returnTokenDepthList?]⟩
      all_goals
        refine ⟨depth + 1, ?_⟩
        simpa [TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] using hTail

theorem returnTokenDepth?_some_of_pop_some
    {shape : TypedCfg.Shape} {count depth : Nat}
    (hOutput :
      (TypedCfg.Shape.pop count shape).returnTokenDepth? =
        some depth) :
    ∃ inputDepth, shape.returnTokenDepth? = some inputDepth := by
  induction count generalizing shape depth with
  | zero =>
      exact ⟨depth, by simpa [TypedCfg.Shape.pop] using hOutput⟩
  | succ count ih =>
      rcases shape with ⟨slots, tail⟩
      cases slots with
      | nil =>
          simp [TypedCfg.Shape.pop,
            TypedCfg.Shape.returnTokenDepth?,
            TypedCfg.Shape.returnTokenDepthList?] at hOutput
      | cons slot rest =>
          have hTailOutput :
              (TypedCfg.Shape.pop count
                { slots := rest, tail := tail }).returnTokenDepth? =
                  some depth := by
            simpa [TypedCfg.Shape.pop] using hOutput
          obtain ⟨tailDepth, hTailDepth⟩ := ih hTailOutput
          exact
            returnTokenDepth?_some_of_tail_some
              (shape := { slots := slot :: rest, tail := tail })
              hTailDepth

theorem returnTokenDepth?_some_of_pushWords_some
    {shape : TypedCfg.Shape} {count depth : Nat}
    (hOutput :
      (TypedCfg.Shape.pushWords count shape).returnTokenDepth? =
        some depth) :
    ∃ inputDepth, shape.returnTokenDepth? = some inputDepth := by
  induction count generalizing depth with
  | zero =>
      exact ⟨depth, by simpa [TypedCfg.Shape.pushWords] using hOutput⟩
  | succ count ih =>
      cases hTail :
          (TypedCfg.Shape.pushWords count shape).returnTokenDepth? with
      | none =>
          have hCons :
              (TypedCfg.Shape.pushWords (count + 1) shape).returnTokenDepth? =
                ((TypedCfg.Shape.pushWords count shape).returnTokenDepth?).map
                  (· + 1) := by
            simp [TypedCfg.Shape.pushWords, List.replicate_succ,
              List.append_assoc, TypedCfg.Shape.returnTokenDepth?,
              TypedCfg.Shape.returnTokenDepthList?]
          rw [hCons, hTail] at hOutput
          cases hOutput
      | some tailDepth =>
          exact ih hTail

theorem returnTokenDepth?_some_of_afterCall_some
    {input output : TypedCfg.Shape} {argc retc depth : Nat}
    (hAfter :
      TypedCfgCompiler.Shape.afterCall input argc retc = some output)
    (hOutput : output.returnTokenDepth? = some depth) :
    ∃ inputDepth, input.returnTokenDepth? = some inputDepth := by
  unfold TypedCfgCompiler.Shape.afterCall at hAfter
  split at hAfter
  · cases hAfter
    obtain ⟨popDepth, hPopDepth⟩ :=
      returnTokenDepth?_some_of_pushWords_some hOutput
    exact returnTokenDepth?_some_of_pop_some hPopDepth
  · contradiction

theorem returnTokenDepth?_tail_some_of_some
    {shape : TypedCfg.Shape} {depth : Nat}
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (hDepth : shape.returnTokenDepth? = some depth) :
    ∃ tailDepth,
      ({ shape with slots := shape.slots.tail } :
        TypedCfg.Shape).returnTokenDepth? = some tailDepth := by
  rcases shape with ⟨slots, tail⟩
  cases slots with
  | nil =>
      simp [TypedCfg.Shape.returnTokenDepth?,
        TypedCfg.Shape.returnTokenDepthList?] at hDepth
  | cons slot rest =>
      cases slot
      case returnToken | returnPC =>
        simp [TypedCfgCompiler.Shape.sourceLength,
          TypedCfgCompiler.Shape.sourceView, TypedCfg.Shape.length,
          TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] at hSource
      all_goals
        cases hRest :
            TypedCfg.Shape.returnTokenDepthList? rest with
        | none =>
            simp [TypedCfg.Shape.returnTokenDepth?,
              TypedCfg.Shape.returnTokenDepthList?, hRest] at hDepth
        | some tailDepth =>
            exact
              ⟨tailDepth, by
                simpa [TypedCfg.Shape.returnTokenDepth?,
                  TypedCfg.Shape.returnTokenDepthList?] using hRest⟩

theorem returnTokenDepth?_pop_some_of_some
    {shape : TypedCfg.Shape} {count depth : Nat}
    (hCount : count ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (hDepth : shape.returnTokenDepth? = some depth) :
    ∃ outputDepth,
      (TypedCfg.Shape.pop count shape).returnTokenDepth? =
        some outputDepth := by
  induction count generalizing shape depth with
  | zero =>
      exact ⟨depth, by simpa [TypedCfg.Shape.pop] using hDepth⟩
  | succ count ih =>
      have hSource :
          1 ≤ TypedCfgCompiler.Shape.sourceLength shape := by
        omega
      obtain ⟨tailDepth, hTailDepth⟩ :=
        returnTokenDepth?_tail_some_of_some hSource hDepth
      have hTailLength :=
        sourceLength_tail_of_one_le shape hSource
      have hTailCount :
          count ≤
            TypedCfgCompiler.Shape.sourceLength
              { shape with slots := shape.slots.tail } := by
        omega
      obtain ⟨outputDepth, hOutputDepth⟩ :=
        ih hTailCount hTailDepth
      exact
        ⟨outputDepth, by
          simpa [TypedCfg.Shape.pop] using hOutputDepth⟩

theorem returnTokenDepth?_pushWords_some_of_some
    {shape : TypedCfg.Shape} {count depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth) :
    ∃ outputDepth,
      (TypedCfg.Shape.pushWords count shape).returnTokenDepth? =
        some outputDepth := by
  induction count with
  | zero =>
      exact ⟨depth, by simpa [TypedCfg.Shape.pushWords] using hDepth⟩
  | succ count ih =>
      obtain ⟨tailDepth, hTailDepth⟩ := ih
      exact
        ⟨tailDepth + 1, by
          simpa [TypedCfg.Shape.pushWords, List.replicate_succ,
            List.append_assoc, TypedCfg.Shape.returnTokenDepth?,
            TypedCfg.Shape.returnTokenDepthList?] using hTailDepth⟩

theorem returnTokenDepth?_afterCall_some_of_some
    {input output : TypedCfg.Shape} {argc retc depth : Nat}
    (hSource : argc ≤ TypedCfgCompiler.Shape.sourceLength input)
    (hInputDepth : input.returnTokenDepth? = some depth)
    (hAfter :
      TypedCfgCompiler.Shape.afterCall input argc retc = some output) :
    ∃ outputDepth, output.returnTokenDepth? = some outputDepth := by
  unfold TypedCfgCompiler.Shape.afterCall at hAfter
  split at hAfter
  · cases hAfter
    obtain ⟨popDepth, hPopDepth⟩ :=
      returnTokenDepth?_pop_some_of_some hSource hInputDepth
    exact returnTokenDepth?_pushWords_some_of_some hPopDepth
  · contradiction

theorem sourceFrameFits_tail
    {shape : TypedCfg.Shape} {stackLength : Nat}
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape (stackLength + 1)) :
    TypedCfgCompiler.Shape.SourceFrameFits
      { shape with slots := shape.slots.tail } stackLength := by
  constructor
  · have hTailLength := sourceLength_tail_of_one_le shape hSource
    have hBound := hFits.1
    have hRestore :=
      Nat.sub_add_cancel hSource
    omega
  · intro depth hDepth
    have hLift := returnTokenDepth?_tail_lift hSource hDepth
    have hExact := hFits.2 (depth + 1) hLift
    omega

theorem sourceFrameFits_cons_word
    {shape : TypedCfg.Shape} {stackLength : Nat}
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape stackLength) :
    TypedCfgCompiler.Shape.SourceFrameFits
      { shape with slots := .word :: shape.slots } (stackLength + 1) := by
  cases hDepth : shape.returnTokenDepth? with
  | none =>
      have hNewDepth :
          ({ shape with slots := .word :: shape.slots } :
            TypedCfg.Shape).returnTokenDepth? = none := by
        simpa [TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] using hDepth
      apply sourceFrameFits_of_returnTokenDepth?_eq_none hNewDepth
      have hSource :
          TypedCfgCompiler.Shape.sourceLength
              { shape with slots := .word :: shape.slots } =
            TypedCfgCompiler.Shape.sourceLength shape + 1 := by
        unfold TypedCfgCompiler.Shape.sourceLength
        rw [show
          TypedCfgCompiler.Shape.sourceView
              { shape with slots := .word :: shape.slots } =
            { shape with slots := .word :: shape.slots } by
              exact sourceView_eq_self_of_returnTokenDepth?_eq_none hNewDepth,
          sourceView_eq_self_of_returnTokenDepth?_eq_none hDepth]
        simp [TypedCfg.Shape.length]
      have hBound := hFits.1
      omega
  | some depth =>
      have hNewDepth :
          ({ shape with slots := .word :: shape.slots } :
            TypedCfg.Shape).returnTokenDepth? = some (depth + 1) := by
        simpa [TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] using hDepth
      rw [sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some hNewDepth]
      have hExact := hFits.2 depth hDepth
      omega

theorem sourceFrameFits_pop
    {shape : TypedCfg.Shape} {stackLength count : Nat}
    (hCount :
      count ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape stackLength) :
    TypedCfgCompiler.Shape.SourceFrameFits
      (TypedCfg.Shape.pop count shape) (stackLength - count) := by
  induction count generalizing shape stackLength with
  | zero =>
      simpa using hFits
  | succ count ih =>
      have hSource :
          1 ≤ TypedCfgCompiler.Shape.sourceLength shape := by
        omega
      have hStack : 1 ≤ stackLength := by
        have hBound := hFits.1
        omega
      obtain ⟨stackLength, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : stackLength ≠ 0)
      have hTailFits :=
        sourceFrameFits_tail hSource hFits
      have hTailSource :=
        sourceLength_tail_of_one_le shape hSource
      have hCountTail :
          count ≤
            TypedCfgCompiler.Shape.sourceLength
              { shape with slots := shape.slots.tail } := by
        omega
      simpa [TypedCfg.Shape.pop, Nat.succ_sub_succ_eq_sub] using
        ih hCountTail hTailFits

theorem sourceFrameFits_pushWords
    {shape : TypedCfg.Shape} {stackLength count : Nat}
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape stackLength) :
    TypedCfgCompiler.Shape.SourceFrameFits
      (TypedCfg.Shape.pushWords count shape) (stackLength + count) := by
  induction count with
  | zero =>
      simpa using hFits
  | succ count ih =>
      have hCons :=
        sourceFrameFits_cons_word (ih)
      simpa [TypedCfg.Shape.pushWords, List.replicate_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCons

theorem sourceFrameFits_afterCall
    {input output : TypedCfg.Shape}
    {stackLength argc retc : Nat}
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? argc input = some ())
    (hAfter :
      TypedCfgCompiler.Shape.afterCall input argc retc = some output)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input stackLength) :
    TypedCfgCompiler.Shape.SourceFrameFits output
      (stackLength - argc + retc) := by
  have hCount :
      argc ≤ TypedCfgCompiler.Shape.sourceLength input :=
    requireSourceWords?_eq_some_iff.mp hSource
  unfold TypedCfgCompiler.Shape.afterCall at hAfter
  have hInputCount : argc ≤ input.length := by
    exact Nat.le_trans hCount (sourceLength_le_length input)
  simp [hInputCount] at hAfter
  subst output
  exact
    sourceFrameFits_pushWords
      (sourceFrameFits_pop hCount hFits)

theorem sourceLength_of_type?_pop
    {input output : TypedCfg.Shape}
    (hSource :
      1 ≤ TypedCfgCompiler.Shape.sourceLength input)
    (hType : TypedCfg.Instr.type? .pop input = some output) :
    TypedCfgCompiler.Shape.sourceLength output =
      TypedCfgCompiler.Shape.sourceLength input - 1 := by
  cases input with
  | mk slots tail =>
      cases slots with
      | nil =>
          simp [TypedCfg.Instr.type?] at hType
      | cons slot rest =>
          simp [TypedCfg.Instr.type?] at hType
          cases hType
          exact
            sourceLength_tail_of_one_le
              { slots := slot :: rest, tail := tail } hSource

theorem eq_tail_of_type?_pop
    {input output : TypedCfg.Shape}
    (hType : TypedCfg.Instr.type? .pop input = some output) :
    output = { input with slots := input.slots.tail } := by
  rcases input with ⟨slots, tail⟩
  cases slots with
  | nil =>
      simp [TypedCfg.Instr.type?] at hType
  | cons slot rest =>
      simp [TypedCfg.Instr.type?] at hType
      cases hType
      rfl

end Shape

namespace Block

theorem fallthrough_nil_of_compileBlockFuel?
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result) :
    result.fallthrough? = some input := by
  unfold TypedCfgCompiler.compileBlockFuel? at hCompile
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  rfl

end Block

namespace Stmt

theorem components_of_compileStmtFuel?_code
    {compilerFuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result) :
    ∃ output,
      TypedCfgCompiler.Code.type? code input = some output ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body := TypedCfgCompiler.Code.toCfg code
               output := output
               term := .jump regular }]
          next := supply + 1
          calls := []
          fallthrough? := some output } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? code input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
      cases hCompile
      exact ⟨output, rfl, rfl⟩

theorem components_of_compileStmtFuel?_terminal
    {compilerFuel : Nat} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result) :
    TypedCfgCompiler.Shape.requireSourceWords? kind.argCount input =
        some () ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body := []
               output := input
               term := .halt kind }]
          next := supply + 1
          calls := []
          fallthrough? := none } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hSource :
      TypedCfgCompiler.Shape.requireSourceWords? kind.argCount input with
  | none =>
      simp [hSource] at hCompile
  | some unit =>
      cases unit
      simp [hSource, TypedCfgCompiler.mkBlock?] at hCompile
      cases hCompile
      exact ⟨rfl, rfl⟩

theorem components_of_compileStmtFuel?_if
    {compilerFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result) :
    ∃ output condition bodyResult,
      TypedCfgCompiler.Code.type? cond input =
        some output ∧
      TypedCfgCompiler.Shape.requireSourceWords? 1 output =
        some () ∧
      output.slots.head? = some condition ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
          (supply + 1) (LabelSupply.label supply 0)
          { output with slots := output.slots.tail } regular =
        some bodyResult ∧
      bodyResult.requireFallthrough?
          { output with slots := output.slots.tail } =
        some () ∧
      result =
        { blocks :=
            { label := entry
              input := input
              body := TypedCfgCompiler.Code.toCfg cond
              output := output
              term :=
                .jumpi (LabelSupply.label supply 0) regular } ::
              bodyResult.blocks
          next := bodyResult.next
          calls := bodyResult.calls
          fallthrough? :=
            some { output with slots := output.slots.tail } } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? cond input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some output =>
      cases hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 output with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource] at hCompile
      | some unit =>
          cases unit
          cases hHead : output.slots.head? with
          | none =>
              simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource,
                hHead] at hCompile
          | some condition =>
              cases hBody :
                  TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                    (supply + 1) (LabelSupply.label supply 0)
                    { output with slots := output.slots.tail } regular with
              | none =>
                  simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource, hHead,
                    hBody] at hCompile
              | some bodyResult =>
                  cases hRequire :
                      bodyResult.requireFallthrough?
                        { output with slots := output.slots.tail } with
                  | none =>
                      simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource,
                        hHead, hBody, hRequire] at hCompile
                  | some unit =>
                      cases unit
                      simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource,
                        hHead, hBody, hRequire] at hCompile
                      cases hCompile
                      exact
                        ⟨output, condition, bodyResult,
                          rfl, hSource, hHead, hBody, hRequire, rfl⟩

theorem components_of_compileStmtFuel?_brk
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry target regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hTarget : ctx.breakLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .brk ctx supply entry input regular =
        some result) :
    ctx.breakShape? = some input ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body := []
               output := input
               term := .jump target }]
          next := supply + 1
          calls := []
          fallthrough? := none } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hShape : ctx.breakShape? with
  | none =>
      simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape] at hCompile
  | some expected =>
      by_cases hExpected : input = expected
      · subst expected
        simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape,
          TypedCfgCompiler.mkBlock?] at hCompile
        cases hCompile
        exact ⟨rfl, rfl⟩
      · simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape,
          hExpected] at hCompile

theorem components_of_compileStmtFuel?_cont
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry target regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hTarget : ctx.continueLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .cont ctx supply entry input regular =
        some result) :
    ctx.continueShape? = some input ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body := []
               output := input
               term := .jump target }]
          next := supply + 1
          calls := []
          fallthrough? := none } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hShape : ctx.continueShape? with
  | none =>
      simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape] at hCompile
  | some expected =>
      by_cases hExpected : input = expected
      · subst expected
        simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape,
          TypedCfgCompiler.mkBlock?] at hCompile
        cases hCompile
        exact ⟨rfl, rfl⟩
      · simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape,
          hExpected] at hCompile

theorem components_of_compileStmtFuel?_leave
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry target regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hTarget : ctx.leaveLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          .leave ctx supply entry input regular =
        some result) :
    ctx.leaveShape? = some input ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body := []
               output := input
               term := .jump target }]
          next := supply + 1
          calls := []
          fallthrough? := none } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hShape : ctx.leaveShape? with
  | none =>
      simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape] at hCompile
  | some expected =>
      by_cases hExpected : input = expected
      · subst expected
        simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape,
          TypedCfgCompiler.mkBlock?] at hCompile
        cases hCompile
        exact ⟨rfl, rfl⟩
      · simp [TypedCfgCompiler.checkedJumpOrInvalid, hTarget, hShape,
          hExpected] at hCompile

/--
A conditional whose regularly completing body changes the branch join shape is
rejected. This prevents later code from treating compiler-owned frame data as a
source stack value.
-/
theorem compileStmtFuel?_if_eq_none_of_body_fallthrough_mismatch
    {compilerFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input output actual : TypedCfg.Shape}
    {condition : TypedCfg.Slot}
    {bodyResult : TypedCfgCompiler.Result}
    (hType :
      TypedCfgCompiler.Code.type? cond input =
        some output)
    (hHead : output.slots.head? = some condition)
    (hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
          (supply + 1) (LabelSupply.label supply 0)
          { output with slots := output.slots.tail } regular =
        some bodyResult)
    (hFallthrough : bodyResult.fallthrough? = some actual)
    (hMismatch :
      actual ≠ { output with slots := output.slots.tail }) :
    TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular =
      none := by
  unfold TypedCfgCompiler.compileStmtFuel?
  simp [TypedCfgCompiler.mkCodeBlock?, hType, hHead, hBody,
    TypedCfgCompiler.Result.requireFallthrough?,
    hFallthrough, hMismatch]

theorem fallthrough_code_of_compileStmtFuel?
    {compilerFuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result) :
    ∃ output, result.fallthrough? = some output := by
  obtain ⟨output, _hType, rfl⟩ :=
    components_of_compileStmtFuel?_code hCompile
  exact ⟨output, rfl⟩

theorem fallthrough_if_of_compileStmtFuel?
    {compilerFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result) :
    ∃ output, result.fallthrough? = some output := by
  obtain ⟨output, _condition, _bodyResult,
      _hType, _hSource, _hHead, _hBody, _hRequire, rfl⟩ :=
    components_of_compileStmtFuel?_if hCompile
  exact
    ⟨{ output with slots := output.slots.tail }, rfl⟩

end Stmt

/--
Any block property inherited by every case body and the default is inherited
by the body selected by the source switch semantics.
-/
theorem switch_property_of_select
    {property : Structured.Block → Prop}
    {scrutinee : Word} {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    (hCases :
      ∀ value body, (value, body) ∈ cases → property body)
    (hDefault :
      ∀ body, defaultBody = some body → property body)
    (hSelect :
      Structured.Switch.select scrutinee cases defaultBody =
        some selected) :
    property selected := by
  revert selected
  induction cases with
  | nil =>
      intro selected hSelect
      exact hDefault selected hSelect
  | cons head rest ih =>
      intro selected hSelect
      rcases head with ⟨value, body⟩
      by_cases hEq : value = scrutinee
      · have hBodyEq : body = selected := by
          simpa [Structured.Switch.select, hEq] using hSelect
        subst selected
        exact hCases value body (by simp)
      · apply ih
        · intro caseValue caseBody hMem
          exact hCases caseValue caseBody (by simp [hMem])
        · simpa [Structured.Switch.select, hEq] using hSelect

namespace Switch

def testOutput (valueShape : TypedCfg.Shape) : TypedCfg.Shape :=
  { valueShape with slots := .word :: valueShape.slots }

def casesEntryLabel (base idx : Nat) :
    List (Word × Structured.Block) → Assembly.Label
  | [] => LabelSupply.label base 1
  | _ => TypedCfgCompiler.switchTestLabel base idx

def nextTestLabel (base idx : Nat)
    (rest : List (Word × Structured.Block)) : Assembly.Label :=
  casesEntryLabel base (idx + 1) rest

theorem testBody_type
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue : Word}
    (hHead : valueShape.slots.head? = some slot) :
    TypedCfg.Block.bodyType?
        [.dup 0, .push caseValue, .prim .eq] valueShape =
      some (testOutput valueShape) := by
  cases valueShape with
  | mk slots tail =>
      cases slots with
      | nil =>
          simp at hHead
      | cons head rest =>
          simp [TypedCfg.Block.bodyType?, TypedCfg.Instr.type?,
            TypedCfg.Shape.get?, TypedCfg.Shape.length,
            TypedCfg.Shape.pop, TypedCfg.Shape.pushWords,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α, testOutput]

theorem components_of_compileCasesFuel?_cons
    {compilerFuel : Nat} {caseValue : Word}
    {body : Structured.Block}
    {rest : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result}
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx
          valueShape bodyShape regular =
        some result) :
    ∃ bodyResult tail,
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
          supply (TypedCfgCompiler.switchBodyLabel base idx) bodyShape regular =
        some bodyResult ∧
      bodyResult.requireFallthrough? bodyShape = some () ∧
      TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx
          base bodyResult.next (idx + 1) valueShape bodyShape regular =
        some tail ∧
      result =
        { blocks :=
            { label := TypedCfgCompiler.switchTestLabel base idx
              input := valueShape
              body := [.dup 0, .push caseValue, .prim .eq]
              output := testOutput valueShape
              term :=
                .jumpi (TypedCfgCompiler.switchCaseLabel base idx)
                  (nextTestLabel base idx rest) } ::
              { label := TypedCfgCompiler.switchCaseLabel base idx
                input := valueShape
                body := [.pop]
                output := bodyShape
                term := .jump (TypedCfgCompiler.switchBodyLabel base idx) } ::
              bodyResult.blocks ++ tail.blocks
          next := tail.next
          calls := bodyResult.calls ++ tail.calls
          fallthrough? := some bodyShape } := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileCasesFuel? at hCompile
  simp only at hCompile
  simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
    hPopBodyType, Bind.bind, Option.bind] at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
        supply (TypedCfgCompiler.switchBodyLabel base idx) bodyShape regular with
  | none =>
      simp [hBody] at hCompile
  | some bodyResult =>
      simp only [hBody] at hCompile
      cases hRequire :
          bodyResult.requireFallthrough? bodyShape with
      | none =>
          simp [hRequire] at hCompile
      | some unit =>
          cases unit
          simp only [hRequire] at hCompile
          cases hTail :
              TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx
                base bodyResult.next (idx + 1)
                valueShape bodyShape regular with
          | none =>
              simp [hTail] at hCompile
          | some tail =>
              simp only [hTail] at hCompile
              cases hCompile
              exact
                ⟨bodyResult, tail, rfl, hRequire, hTail, rfl⟩

theorem fallthrough_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result}
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          base supply idx valueShape bodyShape regular =
        some result) :
    result.fallthrough? = some bodyShape := by
  cases cases with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          rfl
  | cons head rest =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          obtain ⟨bodyResult, tail, _hBody, _hRequire, _hTail, rfl⟩ :=
            components_of_compileCasesFuel?_cons
              hHead hPopType hCompile
          rfl

theorem components_of_compileDefaultFuel?_some
    {compilerFuel : Nat} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          (some body) ctx supply entry valueShape bodyShape regular =
        some result) :
    ∃ bodyResult,
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
          (supply + 1) (.generated supply 2000) bodyShape regular =
        some bodyResult ∧
      bodyResult.requireFallthrough? bodyShape = some () ∧
      result =
        { blocks :=
            { label := entry
              input := valueShape
              body := [.pop]
              output := bodyShape
              term := .jump (.generated supply 2000) } ::
              bodyResult.blocks
          next := bodyResult.next
          calls := bodyResult.calls
          fallthrough? := some bodyShape } := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  simp only [TypedCfgCompiler.mkBlock?, hPopBodyType,
    Bind.bind, Option.bind] at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
        (supply + 1) (.generated supply 2000) bodyShape regular with
  | none =>
      simp [hBody] at hCompile
  | some bodyResult =>
      simp only [hBody] at hCompile
      cases hRequire :
          bodyResult.requireFallthrough? bodyShape with
      | none =>
          simp [hRequire] at hCompile
      | some unit =>
          cases unit
          simp only [hRequire] at hCompile
          cases hCompile
          exact ⟨bodyResult, rfl, hRequire, rfl⟩

theorem components_of_compileDefaultFuel?_none
    {compilerFuel : Nat}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
          none ctx supply entry valueShape bodyShape regular =
        some result) :
    result =
      { blocks :=
          [{ label := entry
             input := valueShape
             body := [.pop]
             output := bodyShape
             term := .jump regular }]
        next := supply + 1
        calls := []
        fallthrough? := some bodyShape } := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?, hPopBodyType] at hCompile
  cases hCompile
  rfl

theorem fallthrough_of_compileDefaultFuel?
    {compilerFuel : Nat}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel
          defaultBody ctx supply entry valueShape bodyShape regular =
        some result) :
    result.fallthrough? = some bodyShape := by
  cases defaultBody with
  | none =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileDefaultFuel?] at hCompile
      | succ compilerFuel =>
          rw [
            components_of_compileDefaultFuel?_none
              hPopType hCompile]
  | some body =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileDefaultFuel?] at hCompile
      | succ compilerFuel =>
          obtain ⟨bodyResult, _hBody, _hRequire, rfl⟩ :=
            components_of_compileDefaultFuel?_some
              hPopType hCompile
          rfl

theorem components_of_compileStmtFuel?_switch
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result) :
    ∃ valueShape valueSlot caseResult defaultResult,
      TypedCfgCompiler.Code.type? scrutinee input =
        some valueShape ∧
      TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape =
        some () ∧
      valueShape.slots.head? = some valueSlot ∧
      TypedCfgCompiler.compileCasesFuel? compilerFuel
          cases ctx supply (supply + 1) 0 valueShape
          { valueShape with slots := valueShape.slots.tail }
          regular =
        some caseResult ∧
      TypedCfgCompiler.compileDefaultFuel? compilerFuel
          defaultBody ctx caseResult.next
          (LabelSupply.label supply 1) valueShape
          { valueShape with slots := valueShape.slots.tail }
          regular =
        some defaultResult ∧
      result =
        { blocks :=
            { label := entry
              input := input
              body := TypedCfgCompiler.Code.toCfg scrutinee
              output := valueShape
              term := .jump (casesEntryLabel supply 0 cases) } ::
              caseResult.blocks ++ defaultResult.blocks
          next := defaultResult.next
          calls := caseResult.calls ++ defaultResult.calls
          fallthrough? :=
            some { valueShape with slots := valueShape.slots.tail } } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfgCompiler.Code.type? scrutinee input with
  | none =>
      simp [TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
  | some valueShape =>
      cases hSource :
          TypedCfgCompiler.Shape.requireSourceWords? 1 valueShape with
      | none =>
          simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource] at hCompile
      | some unit =>
          cases unit
          cases hValue : valueShape.slots.head? with
          | none =>
              simp [TypedCfgCompiler.mkCodeBlock?, hType, hSource,
                hValue] at hCompile
          | some valueSlot =>
              simp only [TypedCfgCompiler.mkCodeBlock?, hType, hSource,
                hValue, Bind.bind, Option.bind] at hCompile
              cases hCases :
                  TypedCfgCompiler.compileCasesFuel? compilerFuel
                    cases ctx supply (supply + 1) 0 valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hCases] at hCompile
              | some caseResult =>
                  simp only [hCases] at hCompile
                  cases hDefault :
                      TypedCfgCompiler.compileDefaultFuel? compilerFuel
                        defaultBody ctx caseResult.next
                        (LabelSupply.label supply 1) valueShape
                        { valueShape with slots := valueShape.slots.tail }
                        regular with
                  | none =>
                      simp [hDefault] at hCompile
                  | some defaultResult =>
                      simp only [hDefault] at hCompile
                      cases hCompile
                      refine
                        ⟨valueShape, valueSlot, caseResult, defaultResult,
                          rfl, hSource, hValue, hCases, hDefault, ?_⟩
                      cases cases <;> rfl

theorem fallthrough_of_compileStmtFuel?_switch
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result) :
    ∃ output, result.fallthrough? = some output := by
  obtain
      ⟨valueShape, _valueSlot, _caseResult, _defaultResult,
        _hType, _hSource, _hValue, _hCases, _hDefault, rfl⟩ :=
    components_of_compileStmtFuel?_switch hCompile
  exact
    ⟨{ valueShape with slots := valueShape.slots.tail }, rfl⟩

theorem compileStmtFuel?_switch_one_eq_none
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape} :
    TypedCfgCompiler.compileStmtFuel? 1
        (.switch scrutinee cases defaultBody) ctx
        supply entry input regular =
      none := by
  unfold TypedCfgCompiler.compileStmtFuel?
  cases hType :
      TypedCfgCompiler.Code.type? scrutinee input <;>
    simp [hType, TypedCfgCompiler.mkCodeBlock?,
      TypedCfgCompiler.compileCasesFuel?]

end Switch

namespace Loop

theorem components_of_compileStmtFuel?_for
    {compilerFuel : Nat} {init post body : Structured.Block}
    {cond : Structured.Code} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.for_ init cond post body) ctx supply entry input regular =
          some result) :
    ∃ initResult loopInput condOutput condition bodyResult postResult,
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          (supply + 1) entry input (LabelSupply.label supply 0) =
        some initResult ∧
      initResult.fallthrough? = some loopInput ∧
      TypedCfgCompiler.Code.type? cond loopInput =
        some condOutput ∧
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput =
        some () ∧
      condOutput.slots.head? = some condition ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel body
          { ctx with
            breakLabel? := some regular
            breakShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            continueLabel? := some (LabelSupply.label supply 2)
            continueShape? :=
              some { condOutput with slots := condOutput.slots.tail } }
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) =
        some bodyResult ∧
      bodyResult.requireFallthrough?
          { condOutput with slots := condOutput.slots.tail } =
        some () ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel post
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          bodyResult.next (LabelSupply.label supply 2)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 0) =
        some postResult ∧
      postResult.requireFallthrough? loopInput = some () ∧
      result =
        { blocks :=
            initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term :=
                   .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
          next := postResult.next
          calls :=
            initResult.calls ++ bodyResult.calls ++ postResult.calls
          fallthrough? :=
            some { condOutput with slots := condOutput.slots.tail } } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hInit :
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
        { ctx with
          breakLabel? := none
          breakShape? := none
          continueLabel? := none
          continueShape? := none }
        (supply + 1) entry input (LabelSupply.label supply 0) with
  | none =>
      simp [hInit] at hCompile
  | some initResult =>
      cases hLoopInput : initResult.fallthrough? with
      | none =>
          simp [hInit, hLoopInput] at hCompile
      | some loopInput =>
          cases hType :
              TypedCfgCompiler.Code.type? cond loopInput with
          | none =>
              simp [hInit, hLoopInput,
                TypedCfgCompiler.mkCodeBlock?, hType] at hCompile
          | some condOutput =>
              cases hSource :
                  TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput with
              | none =>
                  simp [hInit, hLoopInput,
                    TypedCfgCompiler.mkCodeBlock?, hType, hSource] at hCompile
              | some unit =>
                  cases unit
                  cases hHead : condOutput.slots.head? with
                  | none =>
                      simp [hInit, hLoopInput,
                        TypedCfgCompiler.mkCodeBlock?, hType, hSource,
                        hHead] at hCompile
                  | some condition =>
                      cases hBody :
                          TypedCfgCompiler.compileBlockFuel? compilerFuel body
                            { ctx with
                              breakLabel? := some regular
                              breakShape? :=
                                some { condOutput with
                                  slots := condOutput.slots.tail }
                              continueLabel? :=
                                some (LabelSupply.label supply 2)
                              continueShape? :=
                                some { condOutput with
                                  slots := condOutput.slots.tail } }
                            initResult.next (LabelSupply.label supply 1)
                            { condOutput with
                              slots := condOutput.slots.tail }
                            (LabelSupply.label supply 2) with
                      | none =>
                          simp [hInit, hLoopInput, hType, hSource, hHead,
                            TypedCfgCompiler.mkCodeBlock?, hBody] at hCompile
                      | some bodyResult =>
                          cases hBodyRequire :
                              bodyResult.requireFallthrough?
                                { condOutput with
                                  slots := condOutput.slots.tail } with
                          | none =>
                              simp [hInit, hLoopInput, hType, hSource, hHead,
                                TypedCfgCompiler.mkCodeBlock?, hBody,
                                hBodyRequire] at hCompile
                          | some unit =>
                              cases unit
                              cases hPost :
                                  TypedCfgCompiler.compileBlockFuel?
                                    compilerFuel post
                                    { ctx with
                                      breakLabel? := none
                                      breakShape? := none
                                      continueLabel? := none
                                      continueShape? := none }
                                    bodyResult.next
                                    (LabelSupply.label supply 2)
                                    { condOutput with
                                      slots := condOutput.slots.tail }
                                    (LabelSupply.label supply 0) with
                              | none =>
                                  simp [hInit, hLoopInput, hType, hSource,
                                    hHead, TypedCfgCompiler.mkCodeBlock?,
                                    hBody, hBodyRequire, hPost] at hCompile
                              | some postResult =>
                                  cases hPostRequire :
                                      postResult.requireFallthrough?
                                        loopInput with
                                  | none =>
                                      simp [hInit, hLoopInput, hType, hSource,
                                        hHead, TypedCfgCompiler.mkCodeBlock?,
                                        hBody, hBodyRequire, hPost,
                                        hPostRequire] at hCompile
                                  | some unit =>
                                      cases unit
                                      simp [hInit, hLoopInput, hType, hSource,
                                        hHead, TypedCfgCompiler.mkCodeBlock?,
                                        hBody, hBodyRequire, hPost,
                                        hPostRequire] at hCompile
                                      cases hCompile
                                      refine
                                        ⟨initResult, loopInput, condOutput,
                                          condition, bodyResult, postResult,
                                          ?_⟩
                                      simp [hInit, hLoopInput, hType, hSource,
                                        hHead, hBody, hBodyRequire, hPost,
                                        hPostRequire, List.append_assoc]

end Loop

namespace Call

theorem exists_lookup_of_compileStmtFuel?_call
    {compilerFuel : Nat} {name : Structured.Name}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result) :
    ∃ proc, Structured.ProcList.lookup? name ctx.procs = some proc := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hLookup : Structured.ProcList.lookup? name ctx.procs with
  | none =>
      simp [hLookup] at hCompile
  | some proc =>
      exact ⟨proc, rfl⟩

theorem returnTokenDepth?_procEntry (proc : Structured.Proc) :
    (TypedCfgCompiler.Shape.procEntry proc).returnTokenDepth? =
      some proc.argc := by
  unfold TypedCfgCompiler.Shape.procEntry TypedCfg.Shape.returnTokenDepth?
  induction proc.argc with
  | zero =>
      simp [TypedCfg.Shape.returnTokenDepthList?]
  | succ argc ih =>
      simp [List.replicate_succ, TypedCfg.Shape.returnTokenDepthList?, ih]

theorem returnTokenDepth?_procExit (proc : Structured.Proc) :
    (TypedCfgCompiler.Shape.procExit proc).returnTokenDepth? =
      some proc.retc := by
  unfold TypedCfgCompiler.Shape.procExit TypedCfg.Shape.returnTokenDepth?
  induction proc.retc with
  | zero =>
      simp [TypedCfg.Shape.returnTokenDepthList?]
  | succ retc ih =>
      simp [List.replicate_succ, TypedCfg.Shape.returnTokenDepthList?, ih]

theorem findTarget?_returnSitesFor_of_mem
    {calls : List TypedCfgCompiler.DispatchSite}
    {site : TypedCfgCompiler.DispatchSite}
    (hUnique :
      (calls.map TypedCfgCompiler.DispatchSite.token).Nodup)
    (hMem : site ∈ calls) :
    TypedCfg.Block.ReturnSite.findTarget? site.token
        (TypedCfgCompiler.returnSitesFor site.procName calls) =
      some site.returnLabel := by
  induction calls with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      have hHeadNot :
          head.token ∉
            tail.map TypedCfgCompiler.DispatchSite.token := by
        exact (List.nodup_cons.mp hUnique).1
      have hTailUnique :
          (tail.map TypedCfgCompiler.DispatchSite.token).Nodup :=
        (List.nodup_cons.mp hUnique).2
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hHead =>
          subst site
          simp [TypedCfgCompiler.returnSitesFor,
            TypedCfg.Block.ReturnSite.findTarget?]
      | inr hTail =>
          have hTokenNe : head.token ≠ site.token := by
            intro hEq
            apply hHeadNot
            exact List.mem_map.mpr ⟨site, hTail, hEq.symm⟩
          have hFound := ih hTailUnique hTail
          by_cases hName : head.procName = site.procName
          · unfold TypedCfgCompiler.returnSitesFor
            simp [hName, TypedCfg.Block.ReturnSite.findTarget?, hTokenNe]
            simpa [TypedCfgCompiler.returnSitesFor] using hFound
          · unfold TypedCfgCompiler.returnSitesFor
            simp [hName]
            simpa [TypedCfgCompiler.returnSitesFor] using hFound

theorem components_of_compileStmtFuel?_call
    {compilerFuel : Nat} {name : Structured.Name}
    {proc : Structured.Proc} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result) :
    ∃ returnShape output,
      TypedCfgCompiler.Shape.requireSourceWords? proc.argc input =
          some () ∧
      TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc =
          some returnShape ∧
      TypedCfg.Block.bodyType?
          (.returnToken (Structured.Stmt.callToken supply) ::
            TypedCfgCompiler.sinkTopUnder proc.argc) input =
        some output ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body :=
                 .returnToken (Structured.Stmt.callToken supply) ::
                   TypedCfgCompiler.sinkTopUnder proc.argc
               output := output
               term := .jump (ProcLabel.entry name) }]
          next := supply + 1
          calls :=
            [{ procName := name
               token := Structured.Stmt.callToken supply
               returnLabel := regular
               caseLabel := .generated supply 10000 }]
          fallthrough? := some returnShape } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [hLookup] at hCompile
  cases hSource :
      TypedCfgCompiler.Shape.requireSourceWords? proc.argc input with
  | none =>
      simp [hSource] at hCompile
  | some unit =>
      cases unit
      cases hReturnShape :
          TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc with
      | none =>
          simp [hSource, hReturnShape] at hCompile
      | some returnShape =>
          cases hType :
              TypedCfg.Block.bodyType?
                (.returnToken (Structured.Stmt.callToken supply) ::
                  TypedCfgCompiler.sinkTopUnder proc.argc) input with
          | none =>
              simp [hSource, hReturnShape,
                TypedCfgCompiler.mkBlock?, hType] at hCompile
          | some output =>
              simp [hSource, hReturnShape,
                TypedCfgCompiler.mkBlock?, hType] at hCompile
              cases hCompile
              exact ⟨returnShape, output, rfl, rfl, rfl, rfl⟩

end Call

end TypedCfgCompilerFacts
end Structured
end EvmCompiler
