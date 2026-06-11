import EvmCompiler.Compiler.Artifact
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace TypedCfg

structure Effects where
  readsMemory : Bool := false
  writesMemory : Bool := false
  observesResources : Bool := false
  readsProgramCounter : Bool := false
  callsOrCreates : Bool := false
  deriving DecidableEq, Repr

namespace Effects

def empty : Effects := {}

def append (left right : Effects) : Effects where
  readsMemory := left.readsMemory || right.readsMemory
  writesMemory := left.writesMemory || right.writesMemory
  observesResources :=
    left.observesResources || right.observesResources
  readsProgramCounter :=
    left.readsProgramCounter || right.readsProgramCounter
  callsOrCreates := left.callsOrCreates || right.callsOrCreates

def ofPrim (op : Assembly.PrimOp) : Effects where
  readsMemory :=
    decide
      (op = .mload ∨ op = .keccak256 ∨ op = .return ∨ op = .revert ∨
        op = .mcopy ∨ op = .call ∨ op = .callcode ∨
        op = .delegatecall ∨ op = .staticcall)
  writesMemory :=
    decide
      (op = .mstore ∨ op = .mstore8 ∨ op = .calldatacopy ∨
        op = .codecopy ∨ op = .extcodecopy ∨
        op = .returndatacopy ∨ op = .mcopy)
  observesResources := decide (op = .gas ∨ op = .msize)
  readsProgramCounter := decide (op = .pc)
  callsOrCreates := op.isExternalCallCreate

@[simp] theorem ofPrim_gas_observesResources :
    (ofPrim .gas).observesResources = true := by
  native_decide

@[simp] theorem ofPrim_msize_observesResources :
    (ofPrim .msize).observesResources = true := by
  native_decide

@[simp] theorem ofPrim_gas_noCallCreate :
    (ofPrim .gas).callsOrCreates = false := by
  native_decide

@[simp] theorem ofPrim_msize_noCallCreate :
    (ofPrim .msize).callsOrCreates = false := by
  native_decide

/--
Effects whose meaning is invariant under compiler-owned control counters and
does not require an external call/create response.
-/
def ReplaySafe (effects : Effects) : Prop :=
  effects.readsProgramCounter = false ∧
    effects.callsOrCreates = false

@[simp] theorem empty_append (effects : Effects) :
    empty.append effects = effects := by
  cases effects
  rfl

@[simp] theorem append_empty (effects : Effects) :
    effects.append empty = effects := by
  cases effects
  simp [append, empty]

theorem append_assoc (first second third : Effects) :
    (first.append second).append third =
      first.append (second.append third) := by
  cases first
  cases second
  cases third
  simp [append, Bool.or_assoc]

end Effects

structure SafetySummary where
  maxAdditionalStack : Nat
  mayHalt : Bool
  effects : Effects
  deriving DecidableEq, Repr

namespace SafetySummary

def readsMemory (summary : SafetySummary) : Bool :=
  summary.effects.readsMemory

def writesMemory (summary : SafetySummary) : Bool :=
  summary.effects.writesMemory

def observesResources (summary : SafetySummary) : Bool :=
  summary.effects.observesResources

def readsProgramCounter (summary : SafetySummary) : Bool :=
  summary.effects.readsProgramCounter

def callsOrCreates (summary : SafetySummary) : Bool :=
  summary.effects.callsOrCreates

def memoryIndependent (summary : SafetySummary) : Bool :=
  !summary.readsMemory && !summary.writesMemory

def observerIndependent (summary : SafetySummary) : Bool :=
  !summary.observesResources

def programCounterIndependent (summary : SafetySummary) : Bool :=
  !summary.readsProgramCounter

def noCallCreate (summary : SafetySummary) : Bool :=
  !summary.callsOrCreates

def empty : SafetySummary where
  maxAdditionalStack := 0
  mayHalt := false
  effects := Effects.empty

def append (left right : SafetySummary) : SafetySummary where
  maxAdditionalStack :=
    max left.maxAdditionalStack right.maxAdditionalStack
  mayHalt := left.mayHalt || right.mayHalt
  effects := left.effects.append right.effects

@[simp] theorem empty_append (summary : SafetySummary) :
    empty.append summary = summary := by
  cases summary with
  | mk maxAdditionalStack mayHalt effects =>
      cases effects
      simp [empty, append, Effects.empty, Effects.append]

@[simp] theorem append_empty (summary : SafetySummary) :
    summary.append empty = summary := by
  cases summary with
  | mk maxAdditionalStack mayHalt effects =>
      cases effects
      simp [empty, append, Effects.empty, Effects.append]

theorem append_assoc (first second third : SafetySummary) :
    (first.append second).append third =
      first.append (second.append third) := by
  cases first
  cases second
  cases third
  simp [append, max_assoc, Bool.or_assoc, Effects.append_assoc]

end SafetySummary

structure FragmentCert where
  entry : Shape
  exit : Shape
  maxAdditionalStack : Nat
  definedLabels : List Label
  referencedLabels : List Label
  mayHalt : Bool
  effects : Effects
  deriving DecidableEq, Repr

namespace FragmentCert

def safety (cert : FragmentCert) : SafetySummary where
  maxAdditionalStack := cert.maxAdditionalStack
  mayHalt := cert.mayHalt
  effects := cert.effects

def empty (shape : Shape) : FragmentCert where
  entry := shape
  exit := shape
  maxAdditionalStack := 0
  definedLabels := []
  referencedLabels := []
  mayHalt := false
  effects := {}

def seq? (left right : FragmentCert) : Option FragmentCert :=
  if left.exit = right.entry then
    some
      { entry := left.entry
        exit := right.exit
        maxAdditionalStack :=
          max left.maxAdditionalStack
            (left.exit.length - left.entry.length +
              right.maxAdditionalStack)
        definedLabels := left.definedLabels ++ right.definedLabels
        referencedLabels :=
          left.referencedLabels ++ right.referencedLabels
        mayHalt := left.mayHalt || right.mayHalt
        effects := left.effects.append right.effects }
  else
    none

end FragmentCert

namespace Instr

def effects : Instr → Effects
  | .prim op => Effects.ofPrim op
  | _ => {}

def ReplaySafe (instr : Instr) : Prop :=
  instr.effects.ReplaySafe

def certificate? (instr : Instr) (entry : Shape) :
    Option FragmentCert := do
  let exit ← instr.type? entry
  some
    { entry := entry
      exit := exit
      maxAdditionalStack := exit.length - entry.length
      definedLabels := []
      referencedLabels := []
      mayHalt := false
      effects := instr.effects }

end Instr

namespace Terminator

def effects : Terminator → Effects
  | .halt .return | .halt .revert =>
      { readsMemory := true }
  | _ => {}

def certificate (term : Terminator) (shape : Shape) : FragmentCert where
  entry := shape
  exit := shape
  maxAdditionalStack :=
    match term with
    | .jumpi _ _ => 0
    | .returnDispatch _ _ => 2
    | _ => 0
  definedLabels := term.definedLabels
  referencedLabels := term.targets
  mayHalt :=
    match term with
    | .halt _ | .invalid => true
    | _ => false
  effects := term.effects

end Terminator

namespace Block

def ReplaySafe (block : Block) : Prop :=
  block.body.Forall Instr.ReplaySafe

def bodyCertificate? : List Instr → Shape → Option FragmentCert
  | [], shape => some (FragmentCert.empty shape)
  | instr :: rest, shape => do
      let head ← instr.certificate? shape
      let tail ← bodyCertificate? rest head.exit
      head.seq? tail

def certificate? (block : Block) : Option FragmentCert := do
  let body ← bodyCertificate? block.body block.input
  if body.exit = block.output then
    let term := block.term.certificate block.output
    let cert ← body.seq? term
    some
      { cert with
        definedLabels := block.label :: cert.definedLabels }
  else
    none

end Block

structure ProgramCert where
  entry : Label
  blocks : List FragmentCert
  definedLabels : List Label
  referencedLabels : List Label
  maxAdditionalStack : Nat
  effects : Effects
  mayHalt : Bool
  deriving DecidableEq, Repr

namespace ProgramCert

def safety (cert : ProgramCert) : SafetySummary where
  maxAdditionalStack := cert.maxAdditionalStack
  mayHalt := cert.mayHalt
  effects := cert.effects

def empty (entry : Label) : ProgramCert where
  entry := entry
  blocks := []
  definedLabels := []
  referencedLabels := []
  maxAdditionalStack := 0
  effects := Effects.empty
  mayHalt := false

/--
Combine independently generated CFG regions. The left entry remains the entry
of the combined region; labels, block certificates, stack bounds, terminal
behavior, and effects compose uniformly for branches, switch arms, loop
fragments, and procedure bodies.
-/
def append (left right : ProgramCert) : ProgramCert where
  entry := left.entry
  blocks := left.blocks ++ right.blocks
  definedLabels := left.definedLabels ++ right.definedLabels
  referencedLabels := left.referencedLabels ++ right.referencedLabels
  maxAdditionalStack :=
    max left.maxAdditionalStack right.maxAdditionalStack
  effects := left.effects.append right.effects
  mayHalt := left.mayHalt || right.mayHalt

def concat (entry : Label) (certs : List ProgramCert) : ProgramCert :=
  certs.foldl append (empty entry)

@[simp] theorem append_blocks (left right : ProgramCert) :
    (left.append right).blocks = left.blocks ++ right.blocks :=
  rfl

@[simp] theorem append_definedLabels (left right : ProgramCert) :
    (left.append right).definedLabels =
      left.definedLabels ++ right.definedLabels :=
  rfl

@[simp] theorem append_referencedLabels (left right : ProgramCert) :
    (left.append right).referencedLabels =
      left.referencedLabels ++ right.referencedLabels :=
  rfl

@[simp] theorem append_safety (left right : ProgramCert) :
    (left.append right).safety =
      left.safety.append right.safety :=
  rfl

theorem append_assoc (first second third : ProgramCert) :
    (first.append second).append third =
      first.append (second.append third) := by
  cases first
  cases second
  cases third
  simp [append, max_assoc, Bool.or_assoc, Effects.append_assoc,
    List.append_assoc]

end ProgramCert

namespace Program

def ReplaySafe (program : Program) : Prop :=
  program.blocks.Forall Block.ReplaySafe

def collectCertificates? : List Block → Option (List FragmentCert)
  | [] => some []
  | block :: rest => do
      let head ← block.certificate?
      let tail ← collectCertificates? rest
      some (head :: tail)

def certificate? (program : Program) : Option ProgramCert := do
  let blocks ← collectCertificates? program.blocks
  some
    { entry := program.entry
      blocks := blocks
      definedLabels := blocks.flatMap FragmentCert.definedLabels
      referencedLabels := blocks.flatMap FragmentCert.referencedLabels
      maxAdditionalStack :=
        blocks.foldl
          (fun bound cert => max bound cert.maxAdditionalStack) 0
      effects :=
        blocks.foldl
          (fun effects cert => effects.append cert.effects) {}
      mayHalt :=
        blocks.foldl (fun mayHalt cert => mayHalt || cert.mayHalt) false }

def ProgramCert.ValidFor (cert : ProgramCert) (program : Program) : Prop :=
  program.WellTyped ∧ program.certificate? = some cert

abbrev CertifiedArtifact :=
  Compiler.Artifact Assembly.Program ProgramCert

def compileCertified? (program : Program) : Option CertifiedArtifact := do
  if program.wellTyped? then pure () else none
  let metadata ← program.certificate?
  let target ← program.lower?
  if target.accepted then pure () else none
  if decide target.PCFits then
    pure ()
  else
    none
  some { target := target, metadata := metadata }

def compilePass :
    Compiler.Pass Program Assembly.Program ProgramCert where
  compile? := compileCertified?

def compileContract :
    Compiler.PassContract Program Assembly.Program ProgramCert where
  pass := compilePass
  Accepted := Program.WellTyped
  MetaValid := fun program artifact =>
    ProgramCert.ValidFor artifact.metadata program

theorem compileCertified?_target {program : Program}
    {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.lower? = some artifact.target := by
  unfold compileCertified? at hCompile
  by_cases hTyped : program.wellTyped? = true
  · simp [hTyped] at hCompile
    cases hCert : program.certificate? with
    | none =>
        simp [hCert] at hCompile
    | some cert =>
        cases hLower : program.lower? with
        | none =>
            simp [hCert, hLower] at hCompile
        | some target =>
            by_cases hAccepted : target.accepted = true
            · by_cases hFits :
                  target.PCFits
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
                cases hCompile
                simpa using hLower
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
            · simp [hCert, hLower, hAccepted] at hCompile
  · simp [hTyped] at hCompile

theorem compileCertified?_wellTyped {program : Program}
    {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.WellTyped := by
  unfold compileCertified? at hCompile
  by_cases hTyped : program.wellTyped? = true
  · exact Program.wellTyped_of_check hTyped
  · simp [hTyped] at hCompile

theorem compileCertified?_certificate {program : Program}
    {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    program.certificate? = some artifact.metadata := by
  unfold compileCertified? at hCompile
  by_cases hTyped : program.wellTyped? = true
  · simp [hTyped] at hCompile
    cases hCert : program.certificate? with
    | none =>
        simp [hCert] at hCompile
    | some cert =>
        cases hLower : program.lower? with
        | none =>
            simp [hCert, hLower] at hCompile
        | some target =>
            by_cases hAccepted : target.accepted = true
            · by_cases hFits :
                  target.PCFits
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
                cases hCompile
                simpa using hCert
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
            · simp [hCert, hLower, hAccepted] at hCompile
  · simp [hTyped] at hCompile

theorem compileCertified?_targetAccepted {program : Program}
    {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    artifact.target.accepted = true := by
  unfold compileCertified? at hCompile
  by_cases hTyped : program.wellTyped? = true
  · simp [hTyped] at hCompile
    cases hCert : program.certificate? with
    | none =>
        simp [hCert] at hCompile
    | some cert =>
        cases hLower : program.lower? with
        | none =>
            simp [hCert, hLower] at hCompile
        | some target =>
            by_cases hAccepted : target.accepted = true
            · by_cases hFits :
                  target.PCFits
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
                cases hCompile
                exact hAccepted
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
            · simp [hCert, hLower, hAccepted] at hCompile
  · simp [hTyped] at hCompile

theorem compileCertified?_pcFits {program : Program}
    {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    artifact.target.PCFits := by
  unfold compileCertified? at hCompile
  by_cases hTyped : program.wellTyped? = true
  · simp [hTyped] at hCompile
    cases hCert : program.certificate? with
    | none =>
        simp [hCert] at hCompile
    | some cert =>
        cases hLower : program.lower? with
        | none =>
            simp [hCert, hLower] at hCompile
        | some target =>
            by_cases hAccepted : target.accepted = true
            · by_cases hFits :
                  target.PCFits
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
                cases hCompile
                exact hFits
              · simp [hCert, hLower, hAccepted, hFits] at hCompile
            · simp [hCert, hLower, hAccepted] at hCompile
  · simp [hTyped] at hCompile

theorem compileCertified?_labelPc_exists
    {program : Program} {artifact : CertifiedArtifact}
    {label : Label} {block : Block}
    (hCompile : program.compileCertified? = some artifact)
    (hFind : program.findBlock? label = some block) :
    ∃ entryPc, artifact.target.labelPc label = some entryPc := by
  rcases
      Program.lower?_fragment_of_findBlock?
        (compileCertified?_target hCompile) hFind with
    ⟨fragment⟩
  have hBlockLabel : block.label = label := by
    have hFound :
        (block.label == label) = true :=
      @List.find?_some Block
        (fun candidate : Block => candidate.label == label)
        block program.blocks hFind
    exact beq_iff_eq.mp hFound
  subst label
  rcases Block.lower?_starts_with_label fragment.lower with
    ⟨tail, hCode⟩
  have hLabelMem :
      Assembly.Instr.label block.label ∈ artifact.target := by
    rw [fragment.target_eq]
    simp [hCode]
  exact
    Assembly.Program.labelPc_exists_of_mem_labels artifact.target
      (Assembly.Program.mem_labels_of_label_mem hLabelMem)

theorem compileCertified?_checked {program : Program}
    {artifact : CertifiedArtifact}
    (hCompile : program.compileCertified? = some artifact) :
    Compiler.PassContract.Checked compileContract program artifact := by
  have hTyped := compileCertified?_wellTyped hCompile
  exact
    { accepted := hTyped
      compiles := hCompile
      metadataValid :=
        ⟨hTyped, compileCertified?_certificate hCompile⟩ }

theorem compileCertified?_step_eventually
    {program : Program} {artifact : CertifiedArtifact}
    {label : Label} {block : Block}
    {state : EVMState} {entryPc : Nat}
    (hCompile : program.compileCertified? = some artifact)
    (hFind : program.findBlock? label = some block)
    (hLabelPc :
      artifact.target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Assembly.Source.Eventually artifact.target state
      (Preservation.Block.RunSimulates artifact.target
        (program.step label state.incrPC)) := by
  exact
    Preservation.Program.lower?_step_eventually
      (compileCertified?_target hCompile)
      (compileCertified?_targetAccepted hCompile)
      (compileCertified?_pcFits hCompile)
      hFind hLabelPc hPc

end Program

end TypedCfg
end EvmCompiler
