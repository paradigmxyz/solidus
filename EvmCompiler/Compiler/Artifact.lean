import Mathlib.Data.List.Basic

namespace EvmCompiler
namespace Compiler

/-!
Small common vocabulary for compiler passes.

The artifact deliberately keeps executable output and pass metadata together.
Pass-specific preservation theorems can validate the metadata without forcing
every pass into one dependent framework.
-/

structure Artifact (Target Metadata : Type) where
  target : Target
  metadata : Metadata
  deriving DecidableEq, Repr

inductive Failure where
  | rejected
  | invalidMetadata
  | loweringFailed
  deriving DecidableEq, Repr

abbrev Result (Target Metadata : Type) :=
  Except Failure (Artifact Target Metadata)

namespace Artifact

def target? {Target Metadata : Type}
    (artifact? : Option (Artifact Target Metadata)) : Option Target :=
  artifact?.map Artifact.target

@[simp] theorem target?_none {Target Metadata : Type} :
    target? (none : Option (Artifact Target Metadata)) = none :=
  rfl

@[simp] theorem target?_some
    {Target Metadata : Type} (artifact : Artifact Target Metadata) :
    target? (some artifact) = some artifact.target :=
  rfl

theorem target?_eq_some_iff
    {Target Metadata : Type}
    {artifact? : Option (Artifact Target Metadata)} {target : Target} :
    target? artifact? = some target ↔
      ∃ artifact, artifact? = some artifact ∧ artifact.target = target := by
  cases artifact? <;> simp [target?]

theorem target?_of_eq_some
    {Target Metadata : Type}
    {artifact? : Option (Artifact Target Metadata)}
    {artifact : Artifact Target Metadata}
    (hArtifact : artifact? = some artifact) :
    target? artifact? = some artifact.target := by
  simp [target?, hArtifact]

def mapTarget {Target Target' Metadata : Type}
    (f : Target → Target') (artifact : Artifact Target Metadata) :
    Artifact Target' Metadata :=
  { target := f artifact.target, metadata := artifact.metadata }

def mapMetadata {Target Metadata Metadata' : Type}
    (f : Metadata → Metadata') (artifact : Artifact Target Metadata) :
    Artifact Target Metadata' :=
  { target := artifact.target, metadata := f artifact.metadata }

def attach {Source Target SourceMetadata TargetMetadata : Type}
    (source : Artifact Source SourceMetadata)
    (target : Artifact Target TargetMetadata) :
    Artifact Target (SourceMetadata × TargetMetadata) :=
  { target := target.target
    metadata := (source.metadata, target.metadata) }

end Artifact

structure Pass (Source Target Metadata : Type) where
  compile? : Source → Option (Artifact Target Metadata)

namespace Pass

def run {Source Target Metadata : Type}
    (pass : Pass Source Target Metadata) (source : Source) :
    Result Target Metadata :=
  match pass.compile? source with
  | some artifact => .ok artifact
  | none => .error .rejected

def identity (Source : Type) : Pass Source Source Unit where
  compile? source := some { target := source, metadata := () }

def andThen {Source Middle Target FirstMetadata SecondMetadata : Type}
    (first : Pass Source Middle FirstMetadata)
    (second : Pass Middle Target SecondMetadata) :
    Pass Source Target (FirstMetadata × SecondMetadata) where
  compile? source := do
    let firstArtifact ← first.compile? source
    let secondArtifact ← second.compile? firstArtifact.target
    some (firstArtifact.attach secondArtifact)

theorem andThen_eq_some_iff
    {Source Middle Target FirstMetadata SecondMetadata : Type}
    {first : Pass Source Middle FirstMetadata}
    {second : Pass Middle Target SecondMetadata}
    {source : Source}
    {artifact : Artifact Target (FirstMetadata × SecondMetadata)} :
    (first.andThen second).compile? source = some artifact ↔
      ∃ firstArtifact secondArtifact,
        first.compile? source = some firstArtifact ∧
        second.compile? firstArtifact.target = some secondArtifact ∧
        firstArtifact.attach secondArtifact = artifact := by
  constructor
  · intro hCompile
    unfold andThen at hCompile
    cases hFirst : first.compile? source with
    | none =>
        simp [hFirst] at hCompile
    | some firstArtifact =>
        cases hSecond : second.compile? firstArtifact.target with
        | none =>
            simp [hFirst, hSecond] at hCompile
        | some secondArtifact =>
            simp [hFirst, hSecond] at hCompile
            exact
              ⟨firstArtifact, secondArtifact, rfl, hSecond, hCompile⟩
  · rintro ⟨firstArtifact, secondArtifact, hFirst, hSecond, rfl⟩
    simp [andThen, hFirst, hSecond]

end Pass

structure PassContract (Source Target Metadata : Type) where
  pass : Pass Source Target Metadata
  Accepted : Source → Prop
  MetaValid : Source → Artifact Target Metadata → Prop

namespace PassContract

def Compiles {Source Target Metadata : Type}
    (contract : PassContract Source Target Metadata)
    (source : Source) (artifact : Artifact Target Metadata) : Prop :=
  contract.pass.compile? source = some artifact

structure Checked {Source Target Metadata : Type}
    (contract : PassContract Source Target Metadata)
    (source : Source) (artifact : Artifact Target Metadata) : Prop where
  accepted : contract.Accepted source
  compiles : contract.Compiles source artifact
  metadataValid : contract.MetaValid source artifact

end PassContract

end Compiler
end EvmCompiler
