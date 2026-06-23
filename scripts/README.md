# Solidity Front Half

## Architecture verification

Run the repository verification gate with:

```sh
scripts/verify.sh
```

The gate checks dependency-direction rules before invoking `lake build`.
Focused builds may be supplied as arguments:

```sh
scripts/verify.sh EvmCompiler.Locals.SourceLowering
```

Record reproducible architecture metrics with:

```sh
scripts/architecture_metrics.sh \
  --cache-label warm \
  --build EvmCompiler.Public \
  --build EvmCompiler.Compiler.AllocatedTypedCfg \
  --build EvmCompiler.Objects.Compiler
```

The default output is
`proof_artifacts/architecture_baseline.json`.

Focused architecture layers are available through:

```sh
scripts/verify_layer.sh effects
scripts/verify_layer.sh allocator
scripts/verify_layer.sh typedcfg
scripts/verify_layer.sh public
scripts/verify_layer.sh proofs
```

The `allocator` layer checks Functions liveness, symbolic stack layouts,
top-16 accessibility, scheduling, and stack-only lowering. The `typedcfg`
layer checks the Structured-to-TypedCfg compiler and its CFG certificate.

The production backend uses `Functions.StackPressureNormalization` followed by
`Functions.StackLowering`. Scheduling is stack-only and fails closed when no
checked top-16 layout exists. Solc-generated `MLOAD`/`MSTORE` spills remain
ordinary source Yul; this backend reserves and accesses no private memory.

To share dependency package builds across worktrees while retaining a local
`.lake/build`, run:

```sh
scripts/setup_shared_lake_cache.sh
```

## Oracle Reviews

`oracle.py` builds compact review packets and submits them to the OpenAI
Responses API for Pro/oracle architecture review.  It stores prompts, raw
responses, answers, and a local conversation index under
`$ORACLE_STATE_DIR`, or `$CODEX_HOME/state/oracle` by default.

```sh
export OPENAI_API_KEY=...

scripts/oracle.py build-architecture-context \
  --output /tmp/evm-compiler-architecture.md

scripts/oracle.py ask-architecture --dry-run \
  --output /tmp/evm-compiler-architecture.md

scripts/oracle.py ask-architecture \
  --output /tmp/evm-compiler-architecture.md

scripts/oracle.py poll --all
scripts/oracle.py list
scripts/oracle.py show RESPONSE_OR_CONVERSATION_ID --latest
```

For a hand-written packet or a follow-up in the same stored conversation:

```sh
scripts/oracle.py ask \
  --title "locals abstraction review" \
  --context /tmp/locals-context.md

scripts/oracle.py reply \
  --conversation RESPONSE_OR_CONVERSATION_ID \
  --context /tmp/followup.md
```

`solidity_to_yul_lean.py` bridges Solidity into the current Lean Yul compiler
entrypoint without reparsing textual Yul:

```sh
scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --namespace Generated.Simple \
  --definition program \
  --output /tmp/SimpleYul.lean \
  --check
```

Use `-` as the input path to read Solidity from stdin.  In that mode, pass
`--source-name` when the solc source name should be stable:

```sh
printf '%s\n' 'contract C { function f() public pure returns (uint) { return 1; } }' |
  scripts/solidity_to_yul_lean.py - \
    --source-name C.sol \
    --contract C \
    --format bytecode-artifact \
    --output /tmp/C.artifact.json
```

You can also hand the bridge solc's native Standard JSON input directly.  The
bridge augments `settings.outputSelection` with the Yul representation it
needs, plus bytecode fields only for artifact/comparison modes, then invokes
`solc --standard-json` unchanged apart from those output requests:

```sh
scripts/solidity_to_yul_lean.py /tmp/solc-input.json \
  --input-format standard-json \
  --source-name contracts/C.sol \
  --contract C \
  --format standard-json-output \
  --output /tmp/solc-output-with-lean-bytecode.json

scripts/solidity_to_yul_lean.py /tmp/solc-input.json \
  --input-format standard-json \
  --format lean-json-check \
  --all-contracts \
  --output /tmp/lean-json-check.json

scripts/solidity_to_yul_lean.py /tmp/solc-input.json \
  --input-format standard-json \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir /tmp/bridge-json \
  --output /tmp/bridge-json/manifest.json
```

The same package mode also works directly from a Solidity source file:

```sh
scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir /tmp/simple-bridge-json \
  --output /tmp/simple-bridge-json/manifest.json
```

For source files, local relative imports such as `./MathLib.sol` and
`../lib/MathLib.sol` are auto-collected into the Standard JSON source graph.
Use `--remapping PREFIX=PATH` or `--remappings-file remappings.txt` for
project-style imports such as `@openzeppelin/...` or `forge-std/...`; the
logical import path remains the Standard JSON source name while the remapping
only chooses the local file to read.  Use `--include-source
[SOURCE_NAME=]PATH` when a source unit needs a custom Standard JSON name, and
`--no-auto-include-imports` to disable the local import collector:

```sh
scripts/solidity_to_yul_lean.py examples/UsesLibrary.sol \
  --linker-symbol 'MathLib.sol:MathLib=0' \
  --contract UsesLibrary \
  --format bytecode-artifact \
  --output /tmp/UsesLibrary.artifact.json

scripts/solidity_to_yul_lean.py examples/UsesRemapping.sol \
  --remapping sample-lib/=examples/vendor/ \
  --linker-symbol 'sample-lib/ScaleLib.sol:ScaleLib=0' \
  --contract UsesRemapping \
  --format bytecode-artifact \
  --output /tmp/UsesRemapping.artifact.json
```

`--linker-symbol NAME=VALUE` resolves solc's `linkersymbol("NAME")` object
builtin before the current backend handoff.  For a real externally linked
library, `VALUE` should be the deployed library address.  The example above
uses zero only because the emitted symbol is dead in this internal-library
fixture.

For Solidity input the script invokes `solc --standard-json`, requests the
`irAst`/`irOptimizedAst` output and exact textual `ir`/`irOptimized`, parses the
Yul JSON AST, selects the runtime
`*_deployed` object by default, and emits an `EvmCompiler.Yul.Program`
definition. When an older source compiler emits only textual Yul, pass
`--yul-ast-solc` naming a newer solc: the source compiler still determines the
exact Yul text, while the second binary only parses that immutable text as
standalone Yul; bridge provenance records `frontend.ast = "yulAst"`. Pass
`--object creation` to select the constructor object, or pass
an explicit Yul object name.  Standalone Yul sources are accepted with
`--input-format yul`; that path asks solc for the source-level Yul object AST
(`frontend.ast = "yulAst"`) and sends the same object/function/data frontend to
Lean.  Because solc's standalone source AST omits `YulData.name`, the bridge
recovers only object/data header names from the original Yul source while still
using solc's AST for code statements and expressions.  Solidity artifact
formats still require Solidity ABI/metadata output.

Useful inspection modes:

```sh
scripts/solidity_to_yul_lean.py examples/Simple.sol --contract Simple --list-objects

scripts/solidity_to_yul_lean.py examples/Object.yul \
  --input-format yul \
  --format bridge-json \
  --object creation \
  --output /tmp/Object.bridge.json

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format bridge-json \
  --object creation \
  --output /tmp/SimpleYul.bridge.json

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format bridge-json-summary \
  --object runtime \
  --output /tmp/SimpleYul.summary.json

scripts/solidity_to_yul_lean.py /tmp/SimpleYul.bridge.json \
  --input-format bridge-json \
  --format bytecode \
  --object creation \
  --output /tmp/Simple.creation.hex

scripts/solidity_to_yul_lean.py /tmp/SimpleYul.bridge.json \
  --input-format bridge-json \
  --format lean-json-check \
  --output /tmp/SimpleYul.lean-json-check.txt

scripts/solidity_to_yul_lean.py /tmp/SimpleYul.bridge.json \
  --input-format bridge-json \
  --format lean-backend-check \
  --output /tmp/SimpleYul.lean-backend-check.txt

scripts/solidity_to_yul_lean.py /tmp/bridge-json/manifest.json \
  --input-format bridge-json-manifest \
  --format lean-backend-check \
  --output /tmp/bridge-json-backend-check.json

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format lean-ir \
  --object creation \
  --namespace Generated.Simple \
  --output /tmp/SimpleYulFrontend.lean \
  --check

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format lean-json-ir \
  --object creation \
  --namespace Generated.Simple \
  --output /tmp/SimpleYulFrontendJson.lean \
  --check

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format lean-ir \
  --object creation \
  --auto-object-layout \
  --namespace Generated.Simple \
  --output /tmp/SimpleYulFrontendAutoLayout.lean \
  --check

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format lean-ir \
  --object creation \
  --object-layout Simple_14_deployed=43:418 \
  --data-base 461 \
  --namespace Generated.Simple \
  --output /tmp/SimpleYulFrontendWithLayout.lean \
  --check

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format bytecode \
  --object creation \
  --namespace Generated.SimpleCreation \
  --output /tmp/Simple.creation.hex

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format bytecode-artifact \
  --namespace Generated.SimpleArtifact \
  --output /tmp/Simple.artifact.json

scripts/solidity_to_yul_lean.py examples/Simple.sol \
  --contract Simple \
  --format forge-artifact \
  --namespace Generated.SimpleForgeArtifact \
  --output /tmp/Simple.forge-artifact.json

scripts/solidity_to_yul_lean.py /tmp/solc-input.json \
  --input-format standard-json \
  --source-name Simple.sol \
  --contract Simple \
  --format standard-json-output \
  --namespace Generated.SimpleStandardJson \
  --output /tmp/Simple.solc-output.json
```

The `bridge-json` format is the normalized structural IR used by the importer,
and `--input-format bridge-json` reads the same schema back without invoking
solc.  That lets a toolchain run solc/Yul normalization once in Python, inspect
or cache the bridge file, then hand that file to Lean for compilation.  It can
preserve object/dialect builtins that the current Lean `YulContract` entrypoint
still rejects during Lean emission.  Bridge JSON schema v3 represents data
sections as `{ "name": ..., "bytes": [...] }` objects, matching the typed Lean
IR's explicit `DataSection` byte-list shape even when solc emits anonymous
metadata.  Frontend metadata uses `frontend.ast = "irAst"` or
`"irOptimizedAst"` for Solidity-produced IR, and `"yulAst"` for standalone Yul
source ASTs.  The machine-readable contract for external producers is
`scripts/bridge-json-v3.schema.json`; persisted bridge directories also have
`scripts/bridge-json-manifest-v1.schema.json` for their `manifest.json` file,
`bridgeJson` provenance blocks are covered by
`scripts/bridge-json-provenance-v1.schema.json`, and `--format bridge-json-summary`
outputs are covered by
`scripts/bridge-json-summary-v1.schema.json`.  Package backend reports from
`--format lean-backend-check` are covered by
`scripts/lean-backend-check-v1.schema.json`.  The standalone
`--format bytecode-artifact` envelope is covered by
`scripts/bytecode-artifact-v1.schema.json`, and the `evmCompiler` metadata
block embedded in Forge artifacts and solc Standard JSON output is covered by
`scripts/evm-compiler-metadata-v1.schema.json`.
Validate externally produced bridge files before replaying them:

```sh
scripts/validate_bridge_json.py /tmp/SimpleYul.bridge.json
```

The validator also accepts a bridge `manifest.json`, recursively validating
every listed bridge file and checking each file matches the manifest metadata:

```sh
scripts/validate_bridge_json.py /tmp/bridge-json/manifest.json
```

The same validator accepts bridge summary files, batch/manifest summary files,
`bridgeJson` provenance blocks, Lean backend check reports, Lean-produced
bytecode artifacts, Forge artifacts, and solc Standard JSON output with
embedded `evmCompiler` metadata.  It also accepts solc-shaped Standard JSON
outputs with no Lean replacements, which is the expected pass-through result
for interface-only or abstract-only batches.  It checks their schema,
duplicate-free positive inventory entries, internal count consistency,
byte-size consistency, and copied provenance entries against their manifest:

```sh
scripts/validate_bridge_json.py /tmp/bridge-json-summary.json
scripts/validate_bridge_json.py /tmp/bridge-json-backend-check.json
scripts/validate_bridge_json.py /tmp/Simple.bytecode-artifact.json
scripts/validate_bridge_json.py /tmp/Simple.forge-artifact.json
scripts/validate_bridge_json.py /tmp/Simple.solc-output.json
```

Use `--bridge-json-dir DIR` with bytecode/artifact/Standard JSON output modes
to keep the exact normalized creation/runtime bridge files that were handed to
Lean; those files can be replayed later with `--input-format bridge-json`.
Use `--format bridge-json-summary` on a Solidity source, one bridge JSON file,
or a bridge manifest to get a Lean-free structural inventory of the normalized
Yul object: object/function/data counts, statement/expression counts, primitive
and user call names, object/dialect builtin calls, current-backend
compatibility metadata, and backend handoff hints.
For manifest summaries, that compatibility metadata is aggregated across all
included objects so a Standard JSON batch can be preflighted as one package.
That is the quickest way to inspect what solc handed to the bridge before
asking Lean to decode or compile it:

```sh
scripts/solidity_to_yul_lean.py /tmp/bridge-json/manifest.json \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --object runtime \
  --output /tmp/bridge-json-summary.json
```

With `--input-format standard-json --all-contracts --format bridge-json`, the
same directory can be produced without invoking Lean at all; the command emits
the manifest JSON and writes the normalized creation/runtime bridge files for
every solc output that includes Yul IR.  If `--output` is supplied for that
mode, use `DIR/manifest.json` so the manifest's relative paths remain valid.
If the selected contracts all lack Yul IR, as interfaces usually do, the
command still emits a valid manifest with no entries and a populated
`skippedContracts` list.
The directory also contains `manifest.json` with schema
`evm-compiler.bridge-json-manifest.v1`, listing each emitted bridge file by
source, contract, selector (`creation`, `runtime`, or explicit object selector),
object name, and relative path.  Package manifests also include
`skippedContracts` plus structured `skippedContractEntries` for selected
contracts where solc emitted no Yul IR, such as interfaces.  Creation entries
may also carry persisted `objectLayout` and `localDataBase` hints when the
package was produced through a bytecode/artifact mode that had those backend
handoff hints available.  Bridge files and manifest entries produced from solc
record frontend metadata identifying whether the normalized object came from
`irAst` or `irOptimizedAst`, and the validator checks that the manifest and
bridge file agree.  Each structured skipped entry records the source, contract,
and skip reason.
Replay the whole directory through Lean's bridge decoder without rerunning solc.
The replay and bridge summaries preserve `skippedContracts`; bridge summaries
also carry per-object frontend metadata (`irAst` or `irOptimizedAst`) and
`skippedContractEntries`, and Lean JSON/backend package reports preserve the
same per-object frontend metadata.  Downstream tools can read the source,
contract, frontend, and skip reason without reopening every bridge file or
parsing labels.
Skipped-only manifests produce a valid summary with zero checked objects:

```sh
scripts/solidity_to_yul_lean.py /tmp/bridge-json/manifest.json \
  --input-format bridge-json-manifest \
  --format lean-json-check \
  --output /tmp/bridge-json-replay.json
```

Use `--source-name`, `--contract`, or `--object runtime` to narrow the replay to
one source, contract, selector, or object name.
You can also replay a cached package into a bytecode artifact without rerunning
solc.  Select exactly one contract creation entry with `--contract` or
`--source-name`; persisted manifest `linkerSymbols`, creation `objectLayout`,
and `localDataBase` hints are reused automatically.  Explicit
`--linker-symbol`, `--object-layout`, or `--data-base` values still override
the persisted package hints:

```sh
scripts/solidity_to_yul_lean.py /tmp/bridge-json/manifest.json \
  --input-format bridge-json-manifest \
  --format bytecode-artifact \
  --contract Simple \
  --output /tmp/Simple.replayed-artifact.json
```

The `lean-ir` format emits the same front-end shape as a typed
`EvmCompiler.Solidity.Frontend.Program`, plus `programToYul : Option
EvmCompiler.Yul.Program` and `programToYulWithLayout : Option
EvmCompiler.Yul.Program` conversions into the current Yul backend entrypoint.
The `lean-json-ir` format embeds the normalized bridge JSON and decodes it in
Lean through `EvmCompiler.Solidity.Frontend.BridgeJson`, so Python owns the
solc-facing AST normalization and Lean receives a small versioned JSON
contract before entering the backend.  The executable bytecode/artifact paths
write that JSON as a temporary sidecar file and pass only the file path to the
Lean runner; direct constructor-style `lean-ir` emission remains available for
inspection.
Use `--format lean-json-check` to run the same sidecar decode in Lean without
asking the backend to produce bytecode; this is useful for large real-world
contracts where you want to prove Lean accepts the normalized bridge file before
debugging backend lowering.  With `--input-format standard-json --all-contracts`,
`lean-json-check` checks the creation object and, when present, the runtime
object for every contract output that includes a Yul IR AST.  It reports any
contracts skipped because solc did not emit an IR object, such as some
interfaces, and records whether each checked object came from solc `irAst` or
`irOptimizedAst`.
Use `--format lean-backend-check` when decode succeeds but executable bytecode
generation returns `none`.  It runs through the cached native
`evm-compiler-backend` executable over the same normalized bridge JSON and
reports whether `solc_validation` or `object_image` first failed, without
treating an expected current-backend gap as malformed bridge input. The more
detailed legacy stage trace remains a failure-only diagnostic for object-image
generation. With
`--input-format bridge-json-manifest`, or with solc/Standard JSON input plus
`--all-contracts`, it emits a JSON package report with per-object status counts
and `firstNoneCounts`; those package reports also retain the per-object solc
frontend metadata.
It also emits `programToObjects : Option EvmCompiler.Objects.Program`,
`programToObjectsWithLayout : Option EvmCompiler.Objects.Program`, and the
computed object-data entrypoints `programResolvedObjectData`,
`programToYulWithComputedObjectData`, `programToObjectsWithComputedObjectData`,
and `programCheckedAssemblyWithComputedObjectData`.  The computed path derives
object/data placement from the typed object tree itself: nested object/data
paths, solc payload order, `.metadata`-last placement, immutable placeholders,
and `datasize`/`dataoffset` resolution are computed before the Yul layer sees
the program.  The checked object lowering then runs the resolved Yul through
`EvmCompiler.Yul.SolcValidation.ProgramOk?` before handing it to the compiler;
the backend-check report exposes that boundary as `solc_validation`.  Generated
Lean modules also expose noncomputable checked object-image definitions,
including `programCheckedObjectImage` and
`programCheckedObjectImageWithLinkerSymbols`, for proof-facing use.  The
executable backend-check runner keeps using the computable `object_image` stage
plus `solc_validation`, because the checked image path depends on the
noncomputable checked compiler API.  The older explicit-layout entrypoints
remain as debugging and compatibility witnesses.
When `--data-base NAT` is supplied, the module also emits
`programToYulWithLocalDataBase` and `programToObjectsWithLocalDataBase`, which
compute named local `dataoffset` entries by walking the ordered local
`DataSection` byte lists from that base.
The base is still an explicit placement witness.  When `--auto-object-layout`
is supplied, the script also asks solc for creation and deployed bytecode,
locates the deployed bytecode inside the creation bytecode, and emits the
inferred layout entry for the main `*_deployed` Yul object.  Explicit
`--object-layout NAME=OFFSET:SIZE` entries may be supplied as overrides.
`datacopy(dst, off, len)` lowers to `codecopy(dst, off, len)` after its
arguments resolve.  The checked imported-Yul preflight now carries an explicit
local code-image relation for `codesize`/`codecopy`, so `datacopy`, `datasize`,
`dataoffset`, `loadimmutable`, and `setimmutable` are handled by the computed
object-image path.

For executable MVP testing, `--format bytecode` emits unchecked backend bytecode
hex by normalizing solc's Yul JSON AST in Python, writing the normalized bridge
JSON to a temporary sidecar file, and invoking the native
`evm-compiler-backend` executable to decode and evaluate
`Program.bytecodeImageUnchecked?`. Lake keeps that executable current, avoiding
the much slower Lean IR interpreter used by `lean --run`. The same
path can start from a cached bridge file with `--input-format bridge-json`, so
the Solidity/solc half and the Lean backend half are separable.  That path is
the Solidity-facing object-image lane: it recursively compiles child objects,
computes object/data offsets from this backend's emitted byte lengths, resolves
object builtins, and appends child object/data payloads in the recorded solc
order.  The older generated `programUncheckedBytecode` definitions are
code-only lower-layer debugging helpers; the bytecode/artifact commands use the
object-image definitions.
The current smoke fixtures include storage reads/writes, checked arithmetic,
event logs across the LOG0-through-LOG4 surface, payable value flow,
low-level external calls (`call`, `staticcall`, `delegatecall`), contract
creation (`create`, `create2`), account-code queries (`extcodesize`,
`extcodecopy`, `extcodehash`), environmental reads including
header/base-fee/prevrandao/gas-price fields and contract self-balance,
immutables, imports/remappings,
custom errors, string literals, dynamic calldata bytes/strings and `uint256[]`
arrays round-tripping through ABI helpers, and mapping storage hashing through
solc-emitted `keccak256` helper code, plus Solidity loops with break/continue
lowered through Yul `for` and memory-struct allocation, field writes, and field
reads through solc's memory helpers, plus unsigned bitwise operations, shifts,
signed division/modulo/arithmetic-shift paths, inheritance, overrides, and
modifiers with pre/post storage effects.
`--format bytecode-artifact` uses the same Lean-evaluated path but emits a
single JSON artifact with both creation and runtime bytecode, the selected Yul
object names, runtime immutable-reference offsets computed from the Lean object
image, byte lengths, and the aggregate `backendCompatibility` preflight when
available.  When `--bridge-json-dir` is supplied it also records `bridgeJson`
provenance pointing at the manifest entries for the exact normalized creation
and runtime Yul bridge files.  That is the closest current command to a dumb
Solidity-to-bytecode
compiler front end.
`--format forge-artifact` emits a Foundry-shaped per-contract artifact: it
preserves solc ABI, method identifiers, and metadata, but replaces
`bytecode.object` and `deployedBytecode.object` with the Lean-produced creation
and runtime bytecode, and rewrites `deployedBytecode.immutableReferences` from
the Lean image when immutables are present.  Its `evmCompiler` provenance block
also includes backend compatibility when available.  Source maps are
intentionally blank because the bytecode was not emitted by solc.
`--format standard-json-output` emits the full solc Standard JSON output and
replaces the selected contract's `evm.bytecode.object` and
`evm.deployedBytecode.object` with Lean-produced hex in solc's unprefixed
format.  It also replaces `evm.deployedBytecode.immutableReferences` with
Lean-computed runtime offsets so solc offsets from differently sized bytecode do
not leak through.  It clears bytecode-specific solc source maps, generated
sources, and link-reference tables on replaced bytecode sections because those
refer to solc's original bytecode, not the Lean-produced image.  Other solc
output fields are preserved, and the selected contract gets an `evmCompiler`
provenance block naming the Yul objects and byte sizes.  When the replacement
was produced from normalized Yul bridge input, the same block also carries the
aggregate `backendCompatibility` preflight used by `bridge-json-summary`
outputs.  When `--bridge-json-dir` is supplied, the block also carries
`bridgeJson` provenance with the manifest path plus the exact creation/runtime
bridge file entries and hashes consumed by the Lean handoff.  Add
`--all-contracts` to replace every contract selected by the
Standard JSON output instead of one `--contract`.  In
all-contract mode,
interface and abstract contract outputs that have no deployable IR/bytecode are
preserved unchanged; the bridge only replaces artifacts that solc exposes with
a Yul AST plus nonempty creation and runtime bytecode.

For Forge experiments, `scripts/solc_lean_standard_json.py` is a narrow
solc-compatible wrapper.  It delegates probes such as `--version` to the real
solc, and for `--standard-json` it returns `standard-json-output` for all
contracts.  Extra solc arguments from Forge are forwarded to the real solc
invocation used inside the bridge:

```sh
SOLC_LEAN_REAL_SOLC=/Users/dan/.local/bin/solc \
SOLC_LEAN_LAKE=/Users/dan/.elan/bin/lake \
SOLC_LEAN_BRIDGE_JSON_DIR=/tmp/solc-lean-bridge-json \
SOLC_LEAN_OPTIMIZED=1 \
SOLC_LEAN_LAKE_CWD="$PWD" \
  forge test --use "$PWD/scripts/solc_lean_standard_json.py" \
    --no-auto-detect --force --match-test testName
```

That wrapper compiles the whole Foundry Standard JSON batch through the Lean
bytecode path, including test contracts.  `SOLC_LEAN_LAKE` is optional when
`~/.elan/bin/lake` exists, and `SOLC_LEAN_BRIDGE_JSON_DIR` is optional but
useful when you want the normalized Yul bridge input for a failed Forge run.
Successful wrapper output is validated before it is returned to Forge, checking
the solc-shaped `evmCompiler` metadata, byte sizes, and attached bridge JSON
provenance when present.  Batches with no deployable contracts are valid
pass-through outputs and are still checked for solc-shaped contract-map
structure.  Set `SOLC_LEAN_VALIDATE_OUTPUT=0` only when you need to bypass that
local validation while debugging the wrapper itself.
Set `SOLC_LEAN_OPTIMIZED=1` when the wrapper should request solc's
`irOptimizedAst` path instead of the default `irAst` path.
To run the same selected Forge tests through both compilers and compare
pass/fail status, use:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/compare_forge_solc_lean.sh --match-test testName
```

Set `PYTHON=/path/to/python` when schema validation should use a specific
runtime, for example the bundled Codex Python with `jsonschema` installed.

The comparison script also validates the persisted `bridge-json/manifest.json`
package after a successful solc-lean compilation, emits and validates a
`bridge-json-summary.json` preflight, and only then reports
`forge_compare=pass`.  If a comparison fails or both runs fail the same way but
solc-lean already wrote bridge JSON, the runner still validates and summarizes
that package before printing the final status.  A passing comparison therefore
includes both the structural handoff package check and the machine-readable
backend compatibility inventory for every normalized bridge file produced by
that run, while many non-passing comparisons still carry the same preflight
diagnostics.

For real project checkouts, `scripts/run_forge_project_compare.py` wraps that
same comparison in a repo-level pipeline.  It can reuse a local Foundry project
or shallow-fetch a Git ref, run setup commands/submodule updates, run the
two-compiler comparison, and write `report.json` plus stdout/stderr logs:

```sh
PYTHON=/path/to/python-with-jsonschema \
  scripts/run_forge_project_compare.py \
    --repo https://github.com/Uniswap/v4-core.git \
    --ref 46c6834698c48bc4a463a86d8420f4eb1d7f3b75 \
    --submodule lib/solmate \
    --solc-version 0.8.26 \
    --match-test test_getSqrtPriceTarget
```

Use `--project-dir /path/to/checkout` to test an existing repo, and pass extra
Forge arguments after `--`.

The runner normalizes Forge's `[PASS]`/`[FAIL]`/`[SKIP]` lines and final test
summary from both runs, ignoring gas differences and result order, so a
successful comparison means the selected test outcome set matched, not merely
that both commands exited with status 0.  After validating the summary, the
runner prints
`forge_compare_result_count=...`,
`forge_compare_result_N=...`,
`forge_compare_tests_passed=...`,
`forge_compare_tests_failed=...`,
`forge_compare_tests_skipped=...`,
`bridge_json_backend_compatibility=...`,
`bridge_json_summary_unsupported_primitives=...`,
`bridge_json_summary_object_builtins=...`,
`bridge_json_summary_dialect_builtins=...`,
`bridge_json_summary_objects=...`, and
`bridge_json_summary_skipped_contracts=...` so the package-level backend
preflight is visible in the comparison output.  The solc-lean run writes
normalized bridge JSON files under the comparison temp directory
(`bridge-json/`) and prints `bridge_json_dir=...` plus
`bridge_json_summary=...` when logs are kept, so a mismatch can be replayed
through `--input-format bridge-json` without rerunning solc and inspected with
the same summary preflight.  If a selector typo or overly narrow Forge filter
matches no tests, the runner fails with `reason=no_forge_test_results` instead
of treating two empty result sets as an equivalence proof.  The runner also
requires Forge's final summary line to be present and to agree with the number
of normalized `[PASS]`/`[FAIL]`/`[SKIP]` result lines; otherwise it fails with
`reason=forge_summary_missing` or `reason=forge_result_count_mismatch`.  The persisted
manifest also records selected
contracts that were skipped because solc did not emit the Yul/bytecode inputs
needed by the Lean bytecode path, such as interfaces or abstract contracts.
The wrapper comparison is most useful once the test contract's generated Yul is
inside the current backend subset.  For targeted comparisons where the test
harness should stay compiled by full solc, use `--format forge-artifact` or
`--format bytecode-artifact` and write the test to deploy/etch the Lean-produced
subject bytecode, as `scripts/test_solidity_forge_smoke.sh` does.
There is also a repeatable helper for that target-only pattern.  It compiles
the selected contract once with full solc and once through the solc -> Yul AST
-> Lean bytecode path, then writes a temporary Forge harness compiled by full
solc.  The harness deploys both creation bytecodes, etches both runtime
bytecodes, replays the supplied calldata sequence, and compares each call's
success bit, returndata, and emitted log topics/data.  It deliberately ignores
the log emitter address because the two bytecode copies run at different
addresses.  Repeat `--value` alongside `--calldata` to replay payable calls,
and use `--constructor-value` for payable constructors.  The helper now persists
the normalized bridge JSON package under `bridge-json/` inside its temporary
directory plus a validated `bridge-json-summary.json` inventory of the exact
creation/runtime bridge files. Successful runs print `bridge_summary_count=...`
and per-summary backend compatibility diagnostics such as
`bridge_summary_1_backend_compatibility=...`,
`bridge_summary_1_objects=...`,
`bridge_summary_1_object_selectors=Contract:runtime`,
`bridge_summary_1_frontends=solc:irAst`, and
`bridge_summary_1_unsupported_primitives=...`. With `--keep-tmp`, successful runs print
`bridge_summary=...`; bytecode-generation failures leave behind the exact
bridge files, manifest, and summary when the manifest was produced before the
backend failed:

Use `--creation-only` for constructor-state comparisons where etching runtime
bytecode would skip initialization, and `--runtime-only` for pure deployed-code
comparisons where creation bytecode still needs code-image or linker work that
the runtime object does not need.

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/compare_contract_call_bytecode.py examples/Simple.sol \
    --contract Simple \
    --calldata 0xc744c4860000000000000000000000000000000000000000000000000000000000000029
```

This is the cleaner lane for specific behavioral checks while the wrapper lane
still requires every contract in the Forge compilation batch, including tests
and dependencies, to fit the current Lean backend subset.
The repeatable smoke gate is:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_bytecode_smoke.sh
```

That smoke also validates the bridge manifests generated by the all-contracts
Standard JSON replacement path and by the solc-compatible wrapper, including
structured skipped-contract entries and skip reasons for non-deployable
interface/abstract outputs.  It includes the ABI fixtures from the behavioral
comparison lane, so bytecode-artifact and all-contracts Standard JSON output
also cover constructor-patched immutables from dynamic constructor arguments,
custom errors, panic reverts, require strings, checked arithmetic, unchecked
wraparound, event logs, and storage rollback after revert paths.
It also includes the inline-assembly artifact fixture, covering the same
solc-Yul handoff surface as the target-bytecode and wrapper lanes through
`sload`/`sstore`, memory hashing, and assembly-built reverts.

The optimized-AST smoke exercises solc's `irOptimizedAst` output instead of
the default `irAst` output.  It compares optimized `Simple` bytecode behavior
against full solc through Forge, then packages optimized `ModifierBox` bridge
JSON and replays the manifest through Lean:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_optimized_ast_smoke.sh
```

There is also a Lean-free optimized summary smoke for the same structured-AST
front-half path.  It packages selected fixtures with `--optimized`, validates
the cached bridge manifests and summaries, and asserts that frontend metadata is
`irOptimizedAst` rather than the default `irAst`:

```sh
SOLC=/Users/dan/.local/bin/solc \
  scripts/test_solidity_frontend_optimized_summary_smoke.sh
```

The paired Lean-free summary runner executes both the default `irAst` summary
preflight and the optimized `irOptimizedAst` summary preflight:

```sh
SOLC=/Users/dan/.local/bin/solc \
  scripts/test_solidity_frontend_summary_all.sh
```

For the user-facing Foundry wrapper path, the optimized Forge comparison smoke
runs the same Forge test once with full solc and once with the solc-lean
wrapper, using Foundry `via_ir` plus optimizer settings and
`SOLC_LEAN_OPTIMIZED=1`:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_compare_optimized.sh
```

There is also a structural object-tree smoke for Solidity `new Child(...)` and
`new Child{salt: ...}(...)` lowering.  It packages `FactoryBox`/`ChildBox` into
bridge JSON, validates and replays the manifest through Lean's JSON decoder,
runs the Lean backend-check preflight, and asserts that the `FactoryBox` runtime
bridge preserves the child subobject, data payload, `create`, and `create2`
surface.  The summary compatibility classifier now treats CREATE/CREATE2 as
supported external-boundary primitives.  The proof model relates matching open
creation requests/responses; it does not pretend to be a closed concrete
deployment-world simulator.

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_object_tree_smoke.sh
```

There is also a front-half decode smoke for Solidity features that the bridge
can normalize and Lean can decode, even when the current executable object-image
path is not yet broad enough for a bytecode-equivalence claim.  It packages
`PackedStorageBox`, validates/replays the manifest through Lean, and asserts
that packed storage, narrow signed storage sign-extension, enum storage, packed
struct fields, and owner capture preserve the expected primitive surface in
bridge JSON.  Its summary also checks that current checked-backend preflight
metadata no longer treats local storage writes as a static classifier blocker,
while its Lean backend-check report records the current executable handoff blockers
(`to_yul_contract` for creation and `functions_compile` for runtime):

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_frontend_decode_smoke.sh
```

Another front-half decode smoke covers low-level external-call lowering.  It
packages `ExternalCallBox`, validates/replays the manifest through Lean, runs
the Lean backend-check preflight, and asserts that the runtime bridge summary
preserves `call`, `staticcall`, `delegatecall`, `returndatasize`, and
`returndatacopy`.  Solc-emitted `gas()` is executable through the unchecked
bytecode lowering path and remains a theorem-boundary observer rather than a
summary blocker.  The summary compatibility classifier treats the CALL-family
primitives as supported open-boundary operations, separate from exact
resource-observer preservation.  Backend-check output may still report a later
first failing stage for a concrete executable artifact, but the CALL-family
primitive surface itself is no longer classified as unsupported:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_external_call_decode_smoke.sh
```

Another front-half smoke covers Solidity `receive`/`fallback` dispatch.  It
packages `FallbackBox`, validates/replays the manifest through Lean, runs the
Lean backend-check preflight, and checks that the runtime bridge summary
preserves payable empty-calldata dispatch, payable fallback calldata
loading/sizing, `msg.value`, ABI returndata, storage writes, and `Hit` event
logs.  The current backend check reaches object-image generation for both
creation and runtime, and the static summary classifier reports that storage
and log primitives are inside the current non-external backend surface:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_fallback_decode_smoke.sh
```

Another front-half smoke covers the log opcode surface.  It packages
`EventMatrix`, validates/replays the manifest through Lean, runs the Lean
backend-check preflight, and checks that the runtime bridge summary preserves
anonymous and non-anonymous events spanning `log0`, `log1`, `log2`, `log3`,
and `log4`.  The current backend check reaches object-image generation for both
creation and runtime, and the static summary classifier reports the log surface
as backend-compatible:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_event_matrix_decode_smoke.sh
```

Another front-half smoke covers Solidity `selfdestruct` lowering, including a
high-level `selfdestruct(recipient)` path and an inline-assembly
`selfdestruct(0)` path.  It validates/replays the bridge manifest through Lean,
runs the Lean backend-check preflight, and checks that summary preflight
preserves `selfdestruct` as a primitive while not treating the payable/storage
setup as a summary-compatibility blocker.  The current backend check reaches
object-image generation for both creation and runtime:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_selfdestruct_decode_smoke.sh
```

Another front-half smoke covers Solidity `try`/`catch` lowering over an external
contract call.  It packages a target contract plus a caller that handles
successful returns, `Error(string)`, `Panic(uint256)`, and raw bytes catches,
then checks that Lean can decode the four-object manifest, runs the Lean
backend-check preflight, and checks that the bridge summary preserves the
expected `call`, return-data-copy, `revert`, and log primitive surface.  The
summary compatibility classifier treats the `call` as supported by the
open-boundary proof surface; the smoke still reports backend-check status and
first failing stage for both the caller runtime and target runtime:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_try_catch_decode_smoke.sh
```

Another front-half smoke covers direct custom-error, require-string, and panic
lowering.  It packages `ErrorPanicBox`, validates/replays the manifest through
Lean, runs the Lean backend-check preflight, and checks that checked arithmetic,
`assert`, `require`, custom-error reverts, unchecked wraparound, event logs, and
storage writes remain visible in the bridge summary.  The smoke reports the
current backend-check status and first failing stage for the runtime object:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_error_panic_decode_smoke.sh
```

Another front-half smoke covers an ERC20-style local token shape before asking
the backend for executable bytecode.  It packages `MiniToken`, validates/replays
the manifest through Lean, runs the Lean backend-check preflight, and checks
that nested allowance mappings, balance mappings, `Transfer`/`Approval` logs,
`caller`, `keccak256`, storage reads/writes, and revert paths are visible in
the bridge summary with frontend metadata preserved through the Lean check
report.  The smoke reports the current runtime backend-check status and first
failing stage alongside the static storage/log backend-compatibility blocker:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_minitoken_decode_smoke.sh
```

There is also a Lean-free front-half summary runner for quickly checking the
solc-to-bridge-json package surface before asking Lean to decode anything.  It
packages local fixtures for packed storage, external calls, fallback/receive
dispatch, event logs, try/catch, custom errors and panics, token-like mappings,
contract creation, dynamic storage arrays, ABI dynamic data, and environment
opcodes, then validates each manifest plus its bridge-summary preflight:

```sh
SOLC=/Users/dan/.local/bin/solc \
  scripts/test_solidity_frontend_summary_smokes.sh
```

The paired front-half decode runner executes the object-tree, packed-storage,
external-call, fallback/receive, event-matrix, selfdestruct, try/catch,
custom-error/panic, and MiniToken structural smokes:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  scripts/test_solidity_frontend_decode_smokes.sh
```

There is also a networked real-repository smoke against a pinned Uniswap
v4-core checkout.  It generates and validates bridge JSON for
`SwapMath` creation code and the real `PoolManager` runtime object, then
replays the smaller `SwapMath` bridge file through the Lean bytecode path. The
larger linked `PoolManager` creation and runtime objects each pass the strict
checked-artifact path independently; decode sidecars and the all-contracts
package remain as front-half diagnostics. It also compiles a tiny wrapper around
the real Uniswap v4 `SwapMath.getSqrtPriceTarget` helper, a second wrapper
around `FullMath`, `LiquidityMath`, and `LPFeeLibrary`, a `BitMath` wrapper
covering most/least-significant-bit scans and the zero-input revert path in
both creation+runtime and runtime-only comparison modes, and a `Currency`
custom-value-type wrapper covering address masking, global
operators, and library extension methods.  A `Slot0` wrapper compares packed
`bytes32` custom-value-type field setters/getters, bit masks, signed tick
extraction, and overwrite paths against full solc bytecode through Forge.  A
`TickMath` wrapper adds decode/summary coverage for fixed-point sqrt price
calculations, inverse tick recovery, usable tick rounding, and an out-of-range
custom-error revert.  A
`SqrtPriceMath` wrapper adds summary coverage for delta rounding, next-price
paths, signed deltas, and an input-validation revert.  A `Lock` wrapper adds
decode/summary coverage for Uniswap v4's transient storage lock path and checks
that `tload`/`tstore` are preserved as supported transient-storage primitives.
A `CurrencyDelta` wrapper covers Uniswap v4's transient
mapping-style delta helper, preserving the `keccak256` slot derivation plus
`tload`/`tstore` in the same backend-compatibility preflight lane.  A lighter
`ProtocolFeeLibrary` wrapper compares packed-fee extraction, validity checks,
and swap-fee arithmetic against full solc bytecode through Forge.  A
`SafeCast` wrapper adds narrow integer downcasts, signed casts, and custom-error
overflow reverts to the same full-solc-vs-solc-lean behavioral comparison lane.
A `Hooks` wrapper adds decode/summary coverage for permission-bit checks,
hook-address validation, dynamic-fee zero-address handling, permission-struct
validation, and custom reverts:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_uniswap_v4_bridge_smoke.sh
```

The script defaults to Uniswap v4-core commit
`46c6834698c48bc4a463a86d8420f4eb1d7f3b75`, uses solc `0.8.26` through
`SOLC_VERSION`, and fetches only `lib/solmate` from the repo's submodules.
Pass `UNISWAP_V4_DIR=/path/to/v4-core` to reuse a local checkout or
`KEEP_TMP=1` to keep the generated bridge JSON files.

The `Position` smoke is a smaller Uniswap v4 behavioral comparison lane around
the real `Position` library.  It compares full solc and solc-lean runtime
bytecode through Forge for position-key calculation, `mapping(bytes32 => struct)`
storage lookups, struct field mutation, zero-delta fee accrual, unchecked
fee-growth wraparound, liquidity reduction, and the `CannotUpdateEmptyPosition`
custom revert emitted through Uniswap's `CustomRevert` helper:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_uniswap_v4_position_bridge_smoke.sh
```

For a faster Lean-free Uniswap v4 front-half check, the extload summary smoke
wraps the real `Extsload` and `Exttload` contracts and verifies that bridge
summary metadata preserves arbitrary-slot `sload`, transient `tload`/`tstore`,
log primitives, and solc `irAst` frontend provenance without reintroducing
old storage/log summary blockers:

```sh
SOLC=/Users/dan/.local/bin/solc \
  scripts/test_uniswap_v4_extload_summary_smoke.sh
```

Another Uniswap-family smoke targets a pinned Universal Router checkout.  It
compiles the real `UnsupportedProtocol` deploy placeholder, covering a
fallback-only contract that reverts with a custom error.  The smoke validates
the runtime bridge JSON, runs the Lean JSON decoder, emits a bytecode artifact,
validates/replays a Lean-free package manifest, validates bridge-summary
compatibility so the creation object/data boundary, creation `codecopy`
code-image support, and backend-ready runtime surface are explicit, and
compares a fallback call against full solc bytecode through Forge.  It also runs
Lean decode, bridge-summary, and backend-check preflight over a wrapper around
the real `Commands` library, covering command-byte flag masking, command-type
masking, nested dispatch bands, `EXECUTE_SUB_PLAN`, and the reserved/third-party
command range while recording the current runtime `functions_compile` blocker:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_uniswap_universal_router_smoke.sh
```

The script defaults to Universal Router commit
`5a5336a2aa69faea5407ad610feabed6d5a1c4fa` and solc `0.8.26`.  Pass
`UNISWAP_UNIVERSAL_ROUTER_DIR=/path/to/universal-router` to reuse a local
checkout or `KEEP_TMP=1` to keep the generated bridge JSON files.

A second Uniswap-family smoke targets a pinned Permit2 checkout.  It compares
a wrapper around the real `SafeCast160` library against full solc bytecode
through Forge, including a custom-error overflow revert.  It also compares a
Permit2-style unordered nonce bitmap fixture with an `InvalidNonce` custom error,
 nested mappings, xor/shift bit math, explicit invalidation, events, and revert
 rollback.  Separately, it runs Lean decode, bridge-summary coverage, and
 Lean backend-check preflight over a wrapper around `PermitHash`.
That summary lane exercises EIP-712 style struct hashing, dynamic memory arrays,
`abi.encode`/`abi.encodePacked`, `keccak256`, and `msg.sender` lowered through
solc's Yul AST.  A second decode/summary fixture around the real
`SignatureVerification` library covers calldata signature slicing, compact and
full signature decoding, `ecrecover` lowering through the precompile
 `staticcall` path, and timestamp/deadline checks surfaced by solc's Yul.  Both
 summary-only fixtures also report their runtime backend-check status and first
 failing stage so they can graduate into Forge comparison once the backend
 accepts the emitted Yul shape:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_uniswap_permit2_bridge_smoke.sh
```

The script defaults to Permit2 commit
`cc56ad0f3439c502c246fc5cfcc3db92bb8b7219` and solc `0.8.26`.  Pass
`UNISWAP_PERMIT2_DIR=/path/to/permit2` to reuse a local checkout or
`KEEP_TMP=1` to keep the generated bridge JSON files.  The source fixture uses
Permit2's `^0.8.17` library/interface files, but the smoke intentionally runs a
newer solc because the bridge consumes solc's structured Yul AST fields, which
the older repo-default compiler does not emit for this lane.

A networked smoke also targets a pinned Aave v3 Core checkout.  It runs Lean
decode, validated bridge-summary coverage, and Lean backend-check preflight for
wrappers around the real `WadRayMath`, `PercentageMath`, and `MathUtils`
libraries.  The fixtures cover wad/ray multiplication and division, ray/wad
conversion, percentage multiply/divide, zero-denominator revert paths from
Aave's inline assembly guards, and pure plus timestamp-based compounded-interest
arithmetic.  The smoke reports each runtime backend-check status and first
failing stage so these shapes can move from preflight into Forge comparison once
the current function compiler accepts the broader checked-arithmetic/runtime-data
pattern:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_aave_v3_bridge_smoke.sh
```

The script defaults to Aave v3 Core commit
`b74526a7bc67a3a117a1963fc871b3eb8cea8435` and solc `0.8.26`.  Pass
`AAVE_V3_DIR=/path/to/aave-v3-core` to reuse a local checkout or `KEEP_TMP=1`
to keep the generated bridge JSON files.

The full-contract backend gate compiles the actual Permit2 runtime and linked
Aave v3 Pool runtime through the checked recursive stack-object artifact.
Permit2 is sourced from solc 0.8.17 and parsed, without changing its Yul text,
by solc 0.8.26. Aave compiles stack-only and requires no compiler memory
reservation:

```sh
PYTHON=/path/to/python LAKE=/path/to/lake \
  scripts/test_full_contract_backend_smoke.sh
```

Use `PERMIT2_DIR` and `AAVE_V3_DIR` to reuse pinned local checkouts.

The adversarial stack-pressure gate confirms conventional stack-too-deep on a
fixture retaining 32 `SLOAD` values across an external call, checks solc's
optimized `memoryguard`/`MSTORE`/`MLOAD` output, and compiles both object
selectors through the verified stack-only backend. It also generates pressure
coverage for tuples, parameters, nested control, loops, internal calls,
dynamic memory, CALL/CREATE/CREATE2, and memory-unsafe assembly:

```sh
scripts/test_solc_stack_spill_adversarial.sh
```

The dynamic-storage surface gate compiles both creation and runtime objects and
replays one persistent 15-call sequence against full-solc and checked backend
bytecode. It covers short/long `bytes` storage at the 31/32-byte boundary,
long-to-empty cleanup, packed structs with dynamic members, nested storage and
calldata arrays, dynamic ABI returns, events, and an intentional bounds panic.
It is included in the supported solc `0.8.26`/`0.8.35` matrix:

```sh
scripts/test_dynamic_storage_surface_backend.sh
scripts/test_supported_solc_versions.sh
```

The reentrant try/catch surface runs a persistent self-call sequence through
checked creation/runtime images and full solc. Nested successful calls commit
storage, while reason strings, panics, custom errors, raw revert bytes, and a
child `INVALID` must all roll back storage and reach the matching catch arm. It
is also part of the supported solc matrix:

```sh
scripts/test_reentrant_try_catch_surface_backend.sh
```

The EigenLayer BN254 gate pins the official `v1.12.0` source commit and executes
its real `BN254.sol` library. Checked creation and runtime images are compared
against full solc for modular exponentiation, curve addition, scalar
multiplication, pairing, gas-limited pairing, tiny-scalar loops, and point
hashing. This concretely exercises precompiles `0x05` through `0x08`, including
the library's ordered `gas()`/`STATICCALL` pattern:

```sh
scripts/test_eigenlayer_bn254_bridge_smoke.sh
```

A networked smoke targets a pinned Compound v3 Comet checkout.  It builds an
ABI-shaped wrapper around the real `CometMath` internal functions and compares
safe-cast, signed/unsigned conversion, boolean conversion, and custom-error
revert paths against full solc bytecode through Forge.  The smoke also runs
Lean decode, bridge-summary validation, and backend-check preflight before the
Forge comparison.  Because the pinned Comet source uses exact pragma
`0.8.15`, and solc 0.8.15 does not emit the structured Yul AST fields consumed
by this bridge, the smoke copies `CometMath.sol` into the temporary fixture with
only the pragma relaxed and then compiles it with structured-AST solc `0.8.26`:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge INSTALL_SOLC=0 \
  scripts/test_compound_comet_bridge_smoke.sh
```

The script defaults to Comet commit
`d5a30b0aaeff7755f1431e87f818990902237b03`, bridge solc `0.8.26`, and Forge
EVM version `cancun`.  Pass `COMPOUND_COMET_DIR=/path/to/comet` to reuse a
local checkout or `KEEP_TMP=1` to keep the generated bridge JSON files.

A networked smoke also targets a pinned Solmate checkout.  It builds a local
`SolmateHarness` fixture against Solmate's `ERC20`, `Owned`, and
`SafeTransferLib`, covering compact inheritance, immutables, receive handlers,
EIP-2612 helper code, and memory-safe inline assembly.  The smoke runs Lean
decode checks, validates/replays the generated manifest, and separately
validates a Lean-free bridge package.  It also runs Lean backend-check preflight
and validates the bridge summary as a current-backend preflight, checking that
external `call`/`staticcall` and immutable/object resolution needs are reported
explicitly.  The smoke reports runtime backend-check status plus first failing
stage for the Solmate harness.  A tiny wrapper around the real
`FixedPointMathLib` library compares fixed-point arithmetic, integer square
root, and an assembly overflow revert against full solc bytecode through Forge:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solmate_bridge_smoke.sh
```

The script defaults to Solmate commit
`4b47a19038b798b4a33d9749d25e570443520647` and solc `0.8.26`.  Pass
`SOLMATE_DIR=/path/to/solmate` to reuse a local checkout or `KEEP_TMP=1` to
keep the generated bridge JSON files.

A networked smoke also targets a pinned Solady checkout.  It builds a tiny
wrapper around Solady's real `LibBit` utility library, validates Lean JSON
decode and Lean-free bridge packages, runs Lean backend-check preflight,
validates bridge-summary compatibility including linker-symbol resolution,
creation `codecopy` support, and bit-manipulation primitive inventory, and
compares bit-scan, popcount, zero-byte counting, power-of-two, and byte-reversal
behavior against full solc bytecode through Forge.  The smoke reports runtime
backend-check status plus first failing stage for the Solady wrapper:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solady_bridge_smoke.sh
```

The script defaults to Solady commit
`5dc5fc87374e6e9de15e8139c09d80fde5a22303` and solc `0.8.26`. Pass
`SOLADY_DIR=/path/to/solady` to reuse a local checkout or `KEEP_TMP=1` to keep
the generated bridge JSON files.

A third networked smoke targets a pinned OpenZeppelin Contracts checkout.  It
builds a local ERC20/Ownable/Pausable fixture through the normal source-file
path with an `@openzeppelin/contracts/` remapping, asks Lean to decode both the
creation/runtime bridge objects, validates the persisted bridge JSON files, and
replays the generated manifest.  It also runs Lean backend-check preflight and
validates bridge-summary backend compatibility for the ERC20 package and the
`Strings` wrapper, checking that linker resolution needs and local
code-image/storage/log support are explicit while runtime
primitives stay visible.  The smoke reports runtime backend-check status plus first failing stage
for both preflight lanes.  A small wrapper around the real OpenZeppelin
`SafeCast` library compares successful casts plus an overflow custom-error
revert against full solc bytecode through Forge.  A separate `Strings` wrapper
exercises dynamic string formatting, helper functions, a data section, and
manifest replay through the Lean bridge JSON decoder; it is decode-only because
this library shape still falls outside the current executable bytecode image
path:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_openzeppelin_bridge_smoke.sh
```

The script defaults to OpenZeppelin Contracts commit
`dbb6104ce834628e473d2173bbc9d47f81a9eec3` (`v5.0.2`) and solc `0.8.26`.
Pass `OPENZEPPELIN_DIR=/path/to/openzeppelin-contracts` to reuse a local
checkout or `KEEP_TMP=1` to keep the generated bridge JSON files.

A networked smoke targets a pinned Chainlink contracts checkout.  It builds a
fallback wrapper around the real `BufferChainlink` and `CBORChainlink`
libraries, validating a bridge package, replaying that package through Lean's
JSON decoder, running the Lean backend-check preflight, and checking the summary
for dynamic byte buffers, buffer resizing, byte writes, CBOR
unsigned/signed/string/bytes encoding, indefinite arrays, calldata copying,
`keccak256`, user-library calls, and frontend metadata preservation.
The same pinned checkout now also builds an `AggregatorV3Interface`-shaped
fallback wrapper that records signed oracle rounds in storage, emits
`AnswerUpdated`, returns ABI-encoded `latestRoundData`/`getRoundData` tuples,
and exercises stale/no-data custom error reverts.  That lane runs Lean decode,
bridge-summary validation, backend-check preflight, and a runtime-only Forge
comparison automatically when the backend check reaches bytecode generation.

The current pinned Chainlink runtime reaches bridge-summary compatibility
`ready`, but the Lean backend-check still blocks at `functions_compile`.  The
runtime-only full-solc-vs-Lean bytecode comparison is wired into the smoke and
will run automatically once that backend check passes; until then the smoke
reports `chainlink_cbor_runtime_compare=blocked` and
`chainlink_cbor_runtime_backend_first_none=functions_compile`.  The aggregator
lane reports its own `chainlink_aggregator_runtime_backend_check` and
`chainlink_aggregator_runtime_backend_first_none` fields:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake INSTALL_SOLC=0 \
  scripts/test_chainlink_cbor_bridge_smoke.sh
```

The script defaults to Chainlink Brownie Contracts commit
`f82d1ac09fc5d3190600d308be99a4a509854686` and solc `0.8.26`.  Pass
`CHAINLINK_DIR=/path/to/chainlink-brownie-contracts` to reuse a local checkout
or `KEEP_TMP=1` to keep the generated bridge JSON files.

The famous-repo smoke runner executes the pinned Uniswap v4 extload summary,
Uniswap v4 bridge, Uniswap v4 Position, Uniswap Universal Router, Uniswap
Permit2, Aave v3, Compound Comet, Solmate, Solady, OpenZeppelin, Chainlink,
PRBMath, Solbase, Balancer v3, and OpenSea Seaport bridge smokes in one pass:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge INSTALL_SOLC=0 \
  scripts/test_famous_repo_bridge_smokes.sh
```

The additional real-contract smoke pins four independent repositories and runs
48 exact Forge call comparisons against wrappers that import their source
unchanged:

- PRBMath UD60x18 arithmetic, including custom value types, iterative `log2`,
  exponentiation, square root, and a division-by-zero revert;
- Solbase fixed-point arithmetic, including assembly-heavy `expWad`, `lnWad`,
  `powWad`, rounding, signed results, and custom-error behavior;
- Balancer v3 fixed-point and logarithmic exponentiation paths, including
  rounding variants and zero-division behavior; and
- OpenSea Seaport's Merkle helper, including dynamic arrays, internal function
  pointers, root/proof generation, proof verification, and revert data.

The Balancer comparison is runtime-only because the current unchecked fallback
backend emits runtime bytecode above the EIP-170 deployment-size limit. The
other three suites compare both creation and runtime behavior.

Run that focused suite with:

```sh
scripts/test_additional_real_contracts_bridge_smoke.sh
```

The Forge smoke gate goes one step further: it writes a temporary Foundry
project, etches Lean-produced runtime bytecode into an address, deploys
Lean-produced creation bytecode with `CREATE`, and checks ABI calls through
Forge.  It covers a pure `Simple.addOne(41) == 42` call, a stateful `Counter`
flow through `value()`, `inc()`, and `add(uint256)`, and an imported
`UsesLibrary`/`MathLib` flow through `twice(21) == 42`:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_smoke.sh
```

There is also a minimal whole-Forge comparison smoke for the wrapper path.  It
runs a selected pure arithmetic/revert Forge test once with full solc and once
with the solc-lean wrapper, then compares the normalized Forge result lines:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_compare.sh
```

A second wrapper smoke writes a multi-source Foundry project with relative
imports, an imported base helper contract, inheritance from an imported
contract, and two imported helper calls.  It checks that Forge can feed the
whole Standard JSON source graph through the solc-lean wrapper and that the
bridge manifest records the generated creation/runtime objects without skipped
contracts:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_compare_imports.sh
```

A third wrapper smoke keeps the same multi-source shape but uses a Solidity
`library` plus Foundry's native `libraries` setting.  The solc-lean wrapper
extracts `settings.libraries` from Standard JSON and passes it into the Lean
linker-symbol path, so full solc and solc-lean can compare the same linked
library-shaped bytecode:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_compare_libraries.sh
```

Another whole-Forge wrapper smoke covers Solidity inline assembly inside the
test compilation batch.  It runs both compilers over a tiny project with
`add`/`mul`/shift/xor arithmetic, `sload`/`sstore`, event emission, memory
`keccak256`, and an assembly-built panic revert, then compares the selected
Forge test outcomes and validates the persisted bridge JSON package:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_compare_inline_assembly.sh
```

The paired comparison runner executes the default `irAst` path, the imported
multi-source path, the library-linker path, the inline-assembly wrapper path,
and the optimized `irOptimizedAst` path:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_forge_compare_all.sh
```

The local Solidity smoke runner executes the non-network front-half gates in
one pass: bytecode-artifact and all-contract Standard JSON output checks,
Lean-free summary preflight smokes for both `irAst` and `irOptimizedAst`,
structural decode/preflight smokes, target-bytecode comparisons, and the
default/imported/library/inline-assembly/optimized Forge wrapper comparisons:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_local_smokes.sh
```

And a target-only full-solc-vs-Lean-bytecode comparison smoke.  This runs the
pure `Simple.addOne(41)` comparison, a stateful `Counter` sequence:
`value()`, `inc()`, `value()`, `add(41)`, `value()`, a constructor-argument
`ConstructorCounter` sequence with ABI-encoded initial value `7`, a
creation-only `ConstructorAbiBox` sequence that checks dynamic constructor
`bytes`/`string` decoding and constructor-patched immutable state, and an
`ImmutableBox` sequence that checks constructor-patched immutable reads, plus
an `EventCounter` sequence that checks event log topics/data while mutating
storage, an `EventMatrix` sequence that emits anonymous and non-anonymous logs
covering LOG0 through LOG4 in one call, a `PayableVault` sequence that
accumulates constructor value and runtime `msg.value` through checked-add
storage updates, and a `BytesBox`
sequence that compares dynamic ABI bytes returndata. It also replays an
`FallbackBox` sequence over empty-calldata `receive()` dispatch with value,
unknown-selector fallback dispatch, payable fallback storage effects, event
logs, fallback returndata, and storage snapshots. It also replays an
`StorageArrayBox` sequence over dynamic storage-array length, `push`, `pop`,
indexed storage reads/writes, calldata-array-to-storage appends, event logs,
and looped storage summation. It also replays a `StorageStructBox` sequence
over mapping-to-storage-struct field writes, storage-reference mutation,
signed-delta checked arithmetic, struct copy into a snapshot slot, `delete`,
logs, and an underflow revert. It also replays a `MiniToken` sequence over
constructor minting, balance mappings, nested allowance mappings, `Transfer`
and `Approval` logs, `transfer`, `approveSelf`, `spendSelf`, and an
insufficient-balance revert. It also replays an
`ArithmeticBox` sequence over checked arithmetic success, Solidity panic
reverts for overflow/underflow/multiply overflow/division by zero, and
`unchecked` wrapping behavior. It also replays an
`AbiBox` sequence over multi-value returns, `abi.encode` for static and
dynamic payloads, `abi.decode` from calldata bytes, and hashing decoded dynamic
bytes. It also replays an
`ArrayBox` sequence over empty and nonempty `uint256[]` calldata for length and
indexed reads, an `EnvBox` sequence over sender/origin, block environment
fields, header/base-fee/prevrandao/gas-price fields, direct payable value
returns, and contract self-balance, plus a `StringBox` sequence over literal
and calldata strings, and a `LoopBox` sequence over calldata-array
iteration, counted loops, and break/continue control flow. It also replays a
`StructBox` sequence over memory struct construction, field swaps, repeated
field reads, and calldata-array writes into a memory struct, plus a
`BitwiseBox` sequence over unsigned bitwise ops, shifts, and signed
division/modulo/arithmetic shift. It also replays a `ModifierBox` sequence
over inherited constructor state, overrides, modifier pre/post storage writes,
custom-error reverts, and `require` string reverts. It also replays an
`EnumBytesBox` sequence over enum ABI decoding and bounds rejection, fixed
`bytes4` constructor/runtime ABI values, fixed-bytes storage/returns, indexed
byte reads, bitwise fixed-bytes operations, event logs, and revert rollback.
It also replays `ResourceObserverBox.observe()` to pin executable lowering for
inline-assembly `gas()` and `msize()` observer opcodes.

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_contract_call_compare.sh
```

The paired target-bytecode runner executes both target-only lanes: the etched
Lean runtime/deployed creation Forge smoke above and the broader
full-solc-vs-Lean-bytecode call-sequence comparison:

```sh
SOLC=/Users/dan/.local/bin/solc LAKE=/Users/dan/.elan/bin/lake \
  FORGE=/Users/dan/.foundry/bin/forge \
  scripts/test_solidity_target_bytecode_smokes.sh
```

Current bridge limits are intentionally explicit:

- Standalone Yul files are accepted with `--input-format yul`, including Yul
  object trees, object-code blocks, nested objects, data sections, functions,
  for-initializer blocks, switches, and the same expression/statement syntax
  accepted from Solidity-produced Yul ASTs.  Solc Standard JSON requests with
  `language: "Yul"` are accepted through `--input-format standard-json` and use
  the same `sources[...].ast` frontend path.
- Single-result user calls are accepted anywhere a one-word expression is
  expected.  Direct `let x := f(...)`, `x := f(...)`, and statement-level
  `f(...)` calls lower to direct `Functions.Stmt.call` statements after any
  nonempty argument list is bound through the proved generated-argument prelude.
  Nested uses such as `add(f(), 1)`, `if f()`, `switch f()`, and loop
  conditions lower through generated temporaries.
- Multi-result user calls are accepted in their Yul statement forms, including
  `let x, y := f(...)` and `x, y := f(...)`, and lower to direct
  `Functions.Stmt.call` statements with the full destination list.
- Yul function definitions are represented in the frontend statement syntax.
  Object-code top-level definitions still populate the `YulContract.functions`
  map; nested definitions, including those in `for` initializer blocks, are
  preserved as declaration statements and also emitted into the generated flat
  function table with local calls rewritten to generated function names before
  core lowering.
- `datasize(currentObject)` is resolved inside the executable object-image path
  so solc constructor-argument helpers can compute appended ABI argument size
  from `codesize() - datasize(currentObject)`.
- `loadimmutable("id")` is resolved to a 32-byte placeholder in executable
  object images, while the image builder computes Lean byte offsets for those
  placeholders with a marker pass.  Creation-code `setimmutable(base, "id",
  value)` expands to `mstore(add(base, offset), value)` for each computed
  placeholder offset, so constructor-patched immutable values work without
  trusting solc byte offsets.
- `memoryguard(n)` is validated as a consistent literal object builtin and
  resolves to exactly `n`. The stack-only backend reserves and accesses no
  compiler memory; solc-generated memory spills are ordinary source Yul.
- `--optimized` requests solc's `irOptimizedAst` output and enables the Yul
  optimizer in generated Standard JSON.  That path is covered separately from
  default `irAst` because older solc versions may emit only textual optimized
  IR, which this bridge intentionally does not parse.
- Yul data sections are preserved structurally with optional names and byte
  payloads.  The bytecode-image path appends data and child objects in solc
  item order, moves `.metadata` data payloads last, and excludes dotted
  object/data names from builtin path lookup.
- Yul string literals are preserved in bridge JSON and typed Lean IR; when they
  are used as values, backend conversion encodes their UTF-8 bytes as a
  right-padded EVM word.  Hex string literals are preserved as byte literals
  and use the same right-padding rule.
- Yul switch case labels preserve number, string, hex-string, and boolean
  literal syntax in bridge JSON and the Lean frontend before lowering to core
  word-valued cases.
- Yul object builtins such as `datasize`, `dataoffset`, `loadimmutable`, and
  `setimmutable` are preserved in bridge JSON and resolved by the computed
  object-image path before conversion to core Yul. `memoryguard` is preserved
  as an object builtin and resolved to its literal argument by the Lean
  frontend. Compiler scratch contracts in bridge JSON are rejected.
  `linkersymbol("name")` can be resolved with explicit
  `--linker-symbol name=value` entries.  Checked object lowering runs
  solc-style Yul validation after these resolutions and before compiler
  lowering.  Generated Lean modules expose noncomputable checked object-image
  witnesses that go through that boundary.  `datacopy` lowers to `codecopy`,
  which is covered by the explicit local code-image relation used by the
  checked imported-Yul preflight.
- CALL-family primitives (`call`, `callcode`, `delegatecall`, `staticcall`) and
  CREATE-family primitives (`create`, `create2`) are recognized by the Solidity
  frontend and classified as supported open external-boundary operations.  The
  theorem surface compares the emitted requests and resumes under matching
  abstract responses; it does not model a concrete external world.
- Account-code/state queries (`balance`, `extcodesize`, `extcodecopy`,
  `extcodehash`) are recognized by the frontend and covered through
  state/query plus code-image preservation, not by adding new suspending
  external-boundary events.
- Direct resource observer primitives `gas()` and `msize()` are executable in
  unchecked bytecode/object-image lowering through their EVM opcodes.  Exact
  preservation of those observer values is not part of the current verified
  theorem boundary.
- The position observer primitive `pc()` remains an explicit dialect/raw-EVM
  exclusion before executable core-Yul lowering.
- Raw EVM opcode-style calls such as `jump`, `jumpi`, `jumpdest`, `push*`,
  `dup*`, and `swap*`, plus verbatim/EOF dialect builtins, are preserved in
  bridge JSON for diagnostics but rejected before checked executable core-Yul
  lowering.  Solc AST `clz(x)` calls are expanded to a generated helper before
  that boundary.
