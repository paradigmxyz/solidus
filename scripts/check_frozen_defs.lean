/-
  Definition-level frozen-closure checker for the Solidus Arena freeze cone.

  Run:  lake env lean --run scripts/check_frozen_defs.lean

  WHY THIS EXISTS (vs. scripts/check_frozen_closure.py)
  -----------------------------------------------------
  The Python checker verifies IMPORT-level closure: every frozen `.lean` file
  may only `import` another frozen file, a pinned external package, or a module
  explicitly `#allow`-ed. That cannot see the attack this tool closes: an
  adversary redefines a constant in a *mutable* module that a frozen DEFINITION
  or a frozen THEOREM STATEMENT semantically depends on. Import-level analysis
  is blind to which symbols of an imported module are actually used; this tool
  walks the actual definitional cone.

  ALGORITHM
  ---------
  Roots:
    * the TYPES (statements) of `EvmCompiler.Solidus.compile_correct` and
      `compile_correct_creation`, and
    * every declaration living in the frozen *spec* modules (the relocated
      statement-vocabulary modules: Solidus.Defs/.Bridge/.SourceRun/.Decode/
      .Frontend and Correctness).

  Reference collection per constant:
    * THEOREMS (`thmInfo`): used constants of the TYPE only — proofs are
      mutable by design.
    * DEFINITIONS (everything else with a value): used constants of TYPE and
      VALUE — their bodies are frozen semantics.

  Transitive closure (memoized), terminating at:
    * any allowlisted constant (the deliberately-mutable compile? entry family),
    * any EvmYul.* constant (pinned package, treated as terminal — not walked),
    * any Lean core / Init / Std / Batteries constant.

  PASS iff every reached constant's origin module is a frozen-manifest module,
  an EvmYul.* module, or Lean core. On FAIL: the offending constant, its
  module, and the immediate frozen parent that referenced it.
-/
import EvmCompiler.Correctness
open Lean

namespace CheckFrozenDefs

/-- Roots whose full definitional cone (type only, for theorems) is checked.
The FOUR public theorem statements. Every other root is also discovered by
scanning the spec modules below (all four live in `Correctness`, so they are
covered by `declsInSpecModules` too; they are listed explicitly here so the
root set is legible and robust to a module move). -/
def rootTheorems : List Name :=
  [ ``EvmCompiler.Solidus.compile_correct
  , ``EvmCompiler.Solidus.compile_correct_creation
  , ``EvmCompiler.Solidus.compile_correct_unlinked
  , ``EvmCompiler.Solidus.compile_correct_unlinked_patch ]

/-- Frozen "spec" modules: every declaration in these is a root. These are the
relocated statement-vocabulary modules created by the freeze relocation. -/
def specModules : List Name :=
  [ `EvmCompiler.Solidus.Defs
  , `EvmCompiler.Solidus.Bridge
  , `EvmCompiler.Solidus.SourceRun
  , `EvmCompiler.Solidus.Decode
  , `EvmCompiler.Solidus.Frontend
  , `EvmCompiler.Correctness ]

/-- The full frozen-manifest module set (every `.lean` entry of
benchmarks/frozen_manifest.txt, mapped path -> module). Reaching a constant in
one of these is OK. Kept in sync with the manifest by hand; if the manifest
changes, update this list (the script prints any escape's module so drift is
visible). -/
def frozenManifestModules : List Name :=
  [ -- relocated statement-spec modules
    `EvmCompiler.Solidus.Bridge
  , `EvmCompiler.Solidus.Decode
  , `EvmCompiler.Solidus.Frontend
  , `EvmCompiler.Solidus.SourceRun
  , `EvmCompiler.Solidus.Defs
  , `EvmCompiler.Correctness
    -- semantic-base frozen files
  , `EvmCompiler.Assembly.StateRelation
  , `EvmCompiler.Assembly.Syntax
  , `EvmCompiler.Assembly.Semantics
  , `EvmCompiler.Assembly.Bytecode
  , `EvmCompiler.Simulation.OpenWorld
  , `EvmCompiler.Simulation.Interaction
  , `EvmCompiler.Yul.Syntax
  , `EvmCompiler.Yul.EffectSemantics
  , `EvmCompiler.Yul.Installation
  , `EvmCompiler.Yul.InteractionSemantics
  , `EvmCompiler.Solidity.RawAstSourceSemantics
  , `EvmCompiler.Core.MemoryContract ]

/-- Root-component string of a (module) name, for package-prefix trust checks. -/
def rootComponent (n : Name) : String :=
  match n.components.head? with
  | some c => c.toString
  | none   => ""

/-- Trusted external-package / core module prefixes: pinned by
lake-manifest.json (EvmYul and the dependency toolchain) or Lean core. Constants
in these modules are terminal and never walked. -/
def trustedRoots : List String :=
  [ "EvmYul", "Init", "Lean", "Std", "Batteries", "Mathlib", "Qq", "Aesop",
    "Cli", "ImportGraph", "LeanSearchClient", "Plausible", "ProofWidgets" ]

/-- ALLOWLIST — the deliberately-mutable compiler entry family.

`Solidus.compile?` / `compileUnlinked?` (frozen defs in Solidus.Defs) call into
the MUTABLE compiler to produce the output bytes. The public theorems quantify
over that output (`compile? rawJson selection = some bytes` is a hypothesis);
trivializing these only changes *which* bytes are produced, and the theorem must
still hold for those bytes. So the cone-walk stops at each of these instead of
descending into (mutable) compiler internals.

Each entry is a constant referenced *inside the body of* `compile?`/
`compileUnlinked?` that resolves to a non-frozen module. The concrete set is
DISCOVERED empirically (run once, inspect escapes whose parent is compile?/
compileUnlinked?) and every member is justified here. Anything NOT in the
compile?-entry family that escapes is reported as a finding, never silently
added. -/
def allowlist : List Name :=
  [ -- `compile?`  : linked compile entry (raw solc Standard-JSON -> artifact).
    `EvmCompiler.Solidity.RawAst.compileArtifactFromRawSolcIr?
    -- `compileUnlinked?` : unlinked compile entry (artifact + link references).
  , `EvmCompiler.Solidity.RawAst.compileArtifactUnlinkedFromRawSolcIrRefs?
    -- The mutable artifact TYPE returned by the two entries above. It appears
    -- only inside the entry bodies as the carrier of the quantified-over output.
  , `EvmCompiler.Solidity.Frontend.Program.Artifact
    -- Fail-closed stack-headroom certificate gate `artifact.stackHeadroomCert?`:
    -- the theorem quantifies over the certificate being PRESENT (its `some`-ness
    -- gates emission), not over its contents.
  , `EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.stackHeadroomCert?
    -- The certificate's (mutable) type, reached only as the element type of the
    -- `stackHeadroomCert?` option gate above.
  , `EvmCompiler.Assembly.StackHeadroom.Cert
    -- Output projections `artifact.image` / `.image.bytes`: they read the
    -- quantified-over emitted bytes, so they belong to the entry family, not to
    -- frozen semantics.
  , `EvmCompiler.Solidity.Frontend.VerifiedStackObjectArtifact.image
  , `EvmCompiler.Solidity.Frontend.ObjectImage.bytes ]

/-- A recorded boundary crossing: an escaped constant, its origin module, and
the immediate frozen parent that referenced it. -/
structure Escape where
  constant : Name
  module   : Name
  parent   : Name
  deriving Inhabited

def isTrustedModule (m : Name) : Bool :=
  trustedRoots.contains (rootComponent m)

/-- Used constants to walk for a constant: TYPE always; VALUE too unless it is a
theorem (proof is mutable). -/
def refsOf (ci : ConstantInfo) : Array Name :=
  let tyRefs := ci.type.getUsedConstants
  match ci with
  | .thmInfo _ => tyRefs
  | _ => match ci.value? with
         | some v => tyRefs ++ v.getUsedConstants
         | none   => tyRefs

partial def visit (env : Environment)
    (visited : IO.Ref (Std.HashSet Name))
    (escapes : IO.Ref (Array Escape))
    (parent : Name) (n : Name) : IO Unit := do
  if (← visited.get).contains n then return
  visited.modify (·.insert n)
  -- Allowlisted compile?-entry family: terminal, not a finding.
  if allowlist.contains n then return
  match env.getModuleFor? n with
  | none =>
      -- No origin module (should not happen for imported decls); surface it.
      escapes.modify (·.push { constant := n, module := `«no-module», parent })
      return
  | some m =>
      if isTrustedModule m then
        -- EvmYul / Lean core: pinned & terminal, do not walk.
        return
      if !(frozenManifestModules.contains m) then
        -- Boundary crossing into a mutable module: record, do not descend.
        escapes.modify (·.push { constant := n, module := m, parent })
        return
      -- Frozen module: walk its cone.
      match env.find? n with
      | none => return
      | some ci =>
          for c in refsOf ci do
            visit env visited escapes n c

/-- Collect every declaration name that lives in one of the spec modules. -/
def declsInSpecModules (env : Environment) : Array Name := Id.run do
  let specSet : Std.HashSet Name := specModules.foldl (·.insert ·) {}
  let mut acc : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some m := env.getModuleFor? n then
      if specSet.contains m then
        acc := acc.push n
  return acc

def run : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `EvmCompiler.Correctness }] {} (loadExts := true)
  let visited ← IO.mkRef ({} : Std.HashSet Name)
  let escapes ← IO.mkRef (#[] : Array Escape)

  -- Roots: the two theorem statements (type-only handled by visit's thm rule)
  -- plus every declaration in the spec modules.
  let mut roots := rootTheorems.toArray
  roots := roots ++ declsInSpecModules env
  IO.println s!"[check_frozen_defs] roots: {roots.size} declarations across {specModules.length} spec modules + {rootTheorems.length} theorems"

  for r in roots do
    visit env visited escapes r r

  let esc ← escapes.get
  IO.println s!"[check_frozen_defs] reached {(← visited.get).size} constants"

  -- Deduplicate escapes by (constant) keeping the first parent seen; group by module.
  let mut seen : Std.HashSet Name := {}
  let mut uniq : Array Escape := #[]
  for e in esc do
    if !seen.contains e.constant then
      seen := seen.insert e.constant
      uniq := uniq.push e

  if uniq.isEmpty then
    IO.println "[check_frozen_defs] PASS — every reached constant is frozen / EvmYul / core."
    return

  -- Group by module.
  let mut byModule : Std.HashMap Name (Array Escape) := {}
  for e in uniq do
    byModule := byModule.insert e.module ((byModule.getD e.module #[]).push e)

  IO.eprintln s!"[check_frozen_defs] FAIL — {uniq.size} constant(s) escape the frozen set:\n"
  for (m, es) in byModule.toList do
    IO.eprintln s!"  module {m}  ({es.size} constant(s)):"
    for e in es do
      IO.eprintln s!"    - {e.constant}   [referenced by {e.parent}]"
    IO.eprintln ""
  -- Nonzero exit for CI.
  throw (IO.userError s!"frozen definition-closure violated: {uniq.size} escaping constant(s)")

end CheckFrozenDefs

def main : IO Unit := CheckFrozenDefs.run
