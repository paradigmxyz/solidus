import EvmCompiler.Compiler.Artifact
import EvmCompiler.TypedCfg.Lower
import EvmCompiler.Assembly.Accepted

namespace EvmCompiler
namespace TypedCfg

structure Effects where
  readsMemory : Bool := false
  writesMemory : Bool := false
  observesResources : Bool := false
  callsOrCreates : Bool := false
  deriving DecidableEq, Repr

namespace Effects

def append (left right : Effects) : Effects where
  readsMemory := left.readsMemory || right.readsMemory
  writesMemory := left.writesMemory || right.writesMemory
  observesResources :=
    left.observesResources || right.observesResources
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
  callsOrCreates := op.isCallCreate

end Effects

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
  definedLabels := []
  referencedLabels := term.targets
  mayHalt :=
    match term with
    | .halt _ | .invalid => true
    | _ => false
  effects := term.effects

end Terminator

namespace Block

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
    some { cert with definedLabels := [block.label] }
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

namespace Program

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
            simp [hCert, hLower] at hCompile
            cases hCompile
            simpa using hLower
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
            simp [hCert, hLower] at hCompile
            cases hCompile
            simpa using hCert
  · simp [hTyped] at hCompile

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

end Program

end TypedCfg
end EvmCompiler
