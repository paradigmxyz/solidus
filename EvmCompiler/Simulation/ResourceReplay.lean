import EvmCompiler.Assembly.Observer

namespace EvmCompiler
namespace Simulation
namespace ResourceReplay

abbrev Trace := Assembly.ResourceTrace
abbrev Observation := Assembly.ResourceObservation
abbrev Observer := Assembly.ResourceObserver
abbrev Word := Assembly.Word

/--
State extension for replaying a fixed resource-observation transcript.

The transcript is an immutable type index. Evaluation can only advance the
cursor, so every intermediate and terminal state remains tied to the exact
ordered transcript supplied at entry.
-/
structure State (σ : Type) (transcript : Trace) where
  source : σ
  cursor : Nat := 0

namespace State

def withSource {σ : Type} {transcript : Trace}
    (state : State σ transcript) (source : σ) : State σ transcript :=
  { state with source := source }

def observed {σ : Type} {transcript : Trace}
    (state : State σ transcript) : Trace :=
  transcript.take state.cursor

def remaining {σ : Type} {transcript : Trace}
    (state : State σ transcript) : Trace :=
  transcript.drop state.cursor

def ConsumedExactly {σ : Type} {transcript : Trace}
    (state : State σ transcript) : Prop :=
  state.cursor = transcript.length

@[simp] theorem withSource_source {σ : Type} {transcript : Trace}
    (state : State σ transcript) (source : σ) :
    (state.withSource source).source = source := rfl

@[simp] theorem withSource_cursor {σ : Type} {transcript : Trace}
    (state : State σ transcript) (source : σ) :
    (state.withSource source).cursor = state.cursor := rfl

@[simp] theorem withSource_observed {σ : Type} {transcript : Trace}
    (state : State σ transcript) (source : σ) :
    (state.withSource source).observed = state.observed := rfl

@[simp] theorem withSource_remaining {σ : Type} {transcript : Trace}
    (state : State σ transcript) (source : σ) :
    (state.withSource source).remaining = state.remaining := rfl

theorem observed_eq_transcript_of_consumedExactly
    {σ : Type} {transcript : Trace} {state : State σ transcript}
    (hConsumed : state.ConsumedExactly) :
    state.observed = transcript := by
  change state.cursor = transcript.length at hConsumed
  change transcript.take state.cursor = transcript
  rw [hConsumed]
  simp

theorem remaining_eq_nil_of_consumedExactly
    {σ : Type} {transcript : Trace} {state : State σ transcript}
    (hConsumed : state.ConsumedExactly) :
    state.remaining = [] := by
  change state.cursor = transcript.length at hConsumed
  change transcript.drop state.cursor = []
  rw [hConsumed]
  simp

end State

def consume? {σ : Type} {transcript : Trace}
    (kind : Observer) (state : State σ transcript) :
    Option (Word × State σ transcript) :=
  match transcript[state.cursor]? with
  | none => none
  | some observation =>
      if observation.kind = kind then
        some (observation.value, { state with cursor := state.cursor + 1 })
      else
        none

@[simp] theorem consume?_zero_cons
    {σ : Type} (kind : Observer) (source : σ)
    (value : Word) (rest : Trace) :
    consume? (transcript := { kind := kind, value := value } :: rest)
        kind { source := source } =
      some (value, { source := source, cursor := 1 }) := by
  simp [consume?]

theorem consume?_cursor_succ
    {σ : Type} {transcript : Trace} {kind : Observer}
    {state state' : State σ transcript} {value : Word}
    (hConsume : consume? kind state = some (value, state')) :
    state'.cursor = state.cursor + 1 := by
  unfold consume? at hConsume
  cases hGet : transcript[state.cursor]? with
  | none =>
      simp [hGet] at hConsume
  | some observation =>
      by_cases hKind : observation.kind = kind
      · simp [hGet, hKind] at hConsume
        exact congrArg State.cursor hConsume.2.symm
      · simp [hGet, hKind] at hConsume

theorem consume?_source
    {σ : Type} {transcript : Trace} {kind : Observer}
    {state state' : State σ transcript} {value : Word}
    (hConsume : consume? kind state = some (value, state')) :
    state'.source = state.source := by
  unfold consume? at hConsume
  cases hGet : transcript[state.cursor]? with
  | none =>
      simp [hGet] at hConsume
  | some observation =>
      by_cases hKind : observation.kind = kind
      · simp [hGet, hKind] at hConsume
        simpa using congrArg State.source hConsume.2.symm
      · simp [hGet, hKind] at hConsume

theorem consume_remaining
    {σ : Type} {transcript : Trace} {kind : Observer}
    {state state' : State σ transcript} {value : Word}
    (hConsume : consume? kind state = some (value, state')) :
    Assembly.ResourceObserver.consume kind state.remaining =
      .ok (value, state'.remaining) := by
  unfold consume? at hConsume
  cases hGet : transcript[state.cursor]? with
  | none =>
      simp [hGet] at hConsume
  | some observation =>
      by_cases hKind : observation.kind = kind
      · simp [hGet, hKind] at hConsume
        rcases hConsume with ⟨rfl, rfl⟩
        rcases List.getElem?_eq_some_iff.mp hGet with ⟨hLt, hObservation⟩
        rw [State.remaining, List.drop_eq_getElem_cons hLt]
        simp [Assembly.ResourceObserver.consume, hObservation,
          hKind, State.remaining]
      · simp [hGet, hKind] at hConsume

theorem consume?_of_consume_remaining
    {σ : Type} {transcript : Trace} {kind : Observer}
    {state : State σ transcript} {value : Word} {rest : Trace}
    (hConsume :
      Assembly.ResourceObserver.consume kind state.remaining =
        .ok (value, rest)) :
    ∃ state' : State σ transcript,
      consume? kind state = some (value, state') ∧
        state'.remaining = rest := by
  cases hDrop : transcript.drop state.cursor with
  | nil =>
      simp [State.remaining, hDrop,
        Assembly.ResourceObserver.consume] at hConsume
  | cons observation tail =>
      by_cases hKind : observation.kind = kind
      · simp [State.remaining, hDrop,
          Assembly.ResourceObserver.consume, hKind] at hConsume
        rcases hConsume with ⟨rfl, rfl⟩
        have hHead :
            transcript[state.cursor]? = some observation := by
          have hAtDrop :
              (transcript.drop state.cursor)[0]? =
                some observation := by
            simp [hDrop]
          simpa [List.getElem?_drop] using hAtDrop
        refine
          ⟨{ state with cursor := state.cursor + 1 }, ?_, ?_⟩
        · simp [consume?, hHead, hKind]
        · change transcript.drop (state.cursor + 1) = tail
          have hTail := congrArg (List.drop 1) hDrop
          simpa [List.drop_drop] using hTail
      · simp [State.remaining, hDrop,
          Assembly.ResourceObserver.consume, hKind] at hConsume

theorem consume_remaining_eq
    {σ : Type} {transcript : Trace} (kind : Observer)
    (state : State σ transcript) :
    (match consume? kind state with
    | none =>
        (Except.error .InvalidInstruction :
          Except EvmCompiler.Assembly.EVMException (Word × Trace))
    | some (value, state') => .ok (value, state'.remaining)) =
    Assembly.ResourceObserver.consume kind state.remaining := by
  cases hSource : consume? kind state with
  | none =>
      cases hTarget :
          Assembly.ResourceObserver.consume kind state.remaining with
      | error err =>
          unfold Assembly.ResourceObserver.consume at hTarget
          cases hRemaining : state.remaining with
          | nil =>
              simp [hRemaining] at hTarget
              cases hTarget
              simp [hSource]
          | cons observation rest =>
              by_cases hKind : observation.kind = kind
              · simp [hRemaining, hKind] at hTarget
              · simp [hRemaining, hKind] at hTarget
                cases hTarget
                simp [hSource]
      | ok result =>
          rcases result with ⟨value, rest⟩
          obtain ⟨state', hConsume, _hRemaining⟩ :=
            consume?_of_consume_remaining hTarget
          rw [hSource] at hConsume
          cases hConsume
  | some result =>
      rcases result with ⟨value, state'⟩
      simp [hSource, consume_remaining hSource]

theorem consume?_of_cursor_eq
    {σ τ : Type} {transcript : Trace} {kind : Observer}
    {left : State σ transcript} {right : State τ transcript}
    {value : Word} {left' : State σ transcript}
    (hCursor : left.cursor = right.cursor)
    (hConsume : consume? kind left = some (value, left')) :
    ∃ right' : State τ transcript,
      consume? kind right = some (value, right') ∧
        left'.cursor = right'.cursor := by
  unfold consume? at hConsume ⊢
  rw [← hCursor]
  cases hGet : transcript[left.cursor]? with
  | none =>
      simp [hGet] at hConsume
  | some observation =>
      by_cases hKind : observation.kind = kind
      · simp [hGet, hKind] at hConsume
        rcases hConsume with ⟨hValue, hState⟩
        subst value
        refine
          ⟨{ right with cursor := left.cursor + 1 }, ?_, ?_⟩
        · simp [hKind]
        · simpa using
            congrArg (fun state : State σ transcript => state.cursor)
              hState.symm
      · simp [hGet, hKind] at hConsume

theorem consume?_rel
    {σ τ : Type} {transcript : Trace} {kind : Observer}
    {rel : σ → τ → Prop}
    {left : State σ transcript} {right : State τ transcript}
    {value : Word} {left' : State σ transcript}
    (hCursor : left.cursor = right.cursor)
    (hSource : rel left.source right.source)
    (hConsume : consume? kind left = some (value, left')) :
    ∃ right' : State τ transcript,
      consume? kind right = some (value, right') ∧
        left'.cursor = right'.cursor ∧
        rel left'.source right'.source := by
  obtain ⟨right', hRight, hCursor'⟩ :=
    consume?_of_cursor_eq hCursor hConsume
  refine ⟨right', hRight, hCursor', ?_⟩
  rw [consume?_source hConsume, consume?_source hRight]
  exact hSource

end ResourceReplay
end Simulation
end EvmCompiler
