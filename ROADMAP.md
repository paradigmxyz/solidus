# Roadmap

The exact release trust and semantic boundary is maintained in
[`PRODUCTION_ASSUMPTIONS.md`](PRODUCTION_ASSUMPTIONS.md).

## Production Boundary

The trusted frontend is a supported pinned `solc` producing optimized Yul
through `irOptimizedAst`. Solidity lowering, source optimization,
rematerialization, and source-level memory spilling belong to that frontend.
The checked backend starts at the resulting Yul program.

The executable raw-frontend adapter matrix currently pins solc 0.8.26 and
0.8.35 to Cancun because those pins emit structured `irOptimizedAst` for the
production corpus. Older exact-version suites, including Permit2 on solc
0.8.17/London, may remain legacy bridge regression coverage, but they do not
join the raw production theorem unless that solc output contains structured
`irOptimizedAst`.
Accepted frontend requests must name London, Paris, Shanghai, or Cancun;
newer fork targets fail closed until their instruction semantics are modeled.

## Public Spine

```text
optimized solc Yul
  -> Functions
  -> verified pressure normalization
  -> verified stack-only allocation
  -> Locals/Expressions
  -> Structured
  -> TypedCfg
  -> Assembly
  -> raw bytecode
```

`Compiler.StackArtifact` is the sole code-body artifact and
`Solidity.Frontend.VerifiedStackObjectArtifact` is the sole recursive object
artifact. Compilation fails closed when stack-only scheduling fails. The
backend performs no compiler-owned memory access.

## Raw solc Frontend Migration

Goal: remove Python semantic normalization from the trusted production path.
Python may invoke solc, transport Standard JSON, and run differential tests,
but the checked compiler source program must be derived in Lean from raw solc
Standard JSON `irOptimizedAst`.

Current split:

- Raw decoding: `Solidity.RawAst` owns Standard JSON contract selection,
  `irOptimizedAst` object selection, pinned fork metadata decoding, raw Yul
  object/code/data syntax, and fail-closed malformed-node rejection.
- Checked elaboration: `Solidity.RawAst.Elab` owns literal decoding, canonical
  call classification, lexical binding checks, nested-function hoisting with
  alpha-renamed generated functions, and `clz` helper insertion.
- Source normalization: existing `Solidity.Frontend` still owns memoryguard
  inference, object-builtin resolution, local data/object layout, linker and
  immutable resolution, fork spelling validation, and object image planning.
- Orchestration: Python remains temporarily as solc transport and old-bridge
  differential tooling; it must stop constructing the theorem's
  `Solidity.Frontend.Program` before this migration is complete.

Transformation inventory from `scripts/solidity_to_yul_lean.py`:

- [x] Literal decoding moved into Lean for raw numbers, booleans, strings, and
  hex bytes.
- [x] Call classification moved into Lean using `Frontend.Primitive.ofName?`,
  object-builtin, unsupported-dialect, and user-call tables.
- [x] Lexical scope checking and name resolution moved into Lean for the raw
  elaborator.
- [x] Nested-function hoisting and alpha-renamed generated callees implemented
  in Lean; nested `Stmt.functionDef` nodes are preserved, not erased.
- [x] `clz` lowering moved into the Lean raw elaborator as a generated helper;
  the generated helper/call now has a local source-reference preservation
  theorem, with broader frontend theorem composition still tracked below.
- [x] Object/data ordering preserved and fail-closed in Lean through explicit
  raw-derived `ObjectItemRef`s plus `itemRefsPreserveOrder?` validation.
- [ ] Standalone Yul data-name recovery remains Python-only and is not part of
  the raw Solidity `irOptimizedAst` production theorem.
- [x] Source/contract/object selection moved into Lean for raw Standard JSON.
- [x] Fork/linker metadata moved for the raw Standard JSON output path: fork
  metadata and selected-contract `metadata.settings.libraries` linker symbols
  are decoded in Lean. Explicit linker-symbol arguments remain only as a
  transition/differential hook.
- [x] Memoryguard inference remains reused in `Solidity.Frontend`; Python does
  not need to normalize it for the raw path.

Next raw frontend layer:

- [x] Add a local raw-vs-normalized bridge differential gate over both pinned
  solc versions, creation/runtime selection, recursive frontend digests, and
  checked artifact sizes for representative real fixtures, including a linked
  library fixture that exercises raw metadata linker-symbol decoding.
- [x] Add a pinned Aave Pool raw corpus gate over both pinned solc versions and
  creation/runtime object selection; Lean raw elaboration consumes the raw
  Standard JSON, preserves seven metadata linker symbols, matches the legacy
  bridge frontend object shape, and reproduces the checked artifact sizes.
- [x] Add a pinned Uniswap v4 PoolManager raw corpus gate for the compatible
  exact-pragma solc 0.8.26 source; creation/runtime raw Lean elaboration
  matches the legacy bridge frontend object shape and reproduces checked
  artifact sizes, while solc 0.8.35 fails closed before raw AST production
  because the source pins `pragma solidity 0.8.26`.
- [x] Add pinned Safe and ERC-4337 EntryPoint raw corpus gates over both
  supported solc pins. Safe is covered through raw optimized Yul plus metadata
  because solc's own bytecode backend rejects the pinned source
  stack-too-deep; EntryPoint includes solc bytecode and raw Lean artifact
  checks for creation/runtime. Both now compare raw Standard JSON Lean
  elaboration against the legacy bridge frontend object shape across both
  pins and creation/runtime selections.
- [x] Add a pinned Permit2 version-boundary gate: unmodified full Permit2 pins
  `pragma solidity 0.8.17`; exact solc 0.8.17 compiles Permit2 bytecode under
  London but emits no `irOptimizedAst`, so the Lean raw path fails closed.
  Supported raw solc 0.8.26 and 0.8.35 also fail closed before raw AST
  production because of the exact pragma. The legacy
  solc-0.8.17/Python-normalized bridge path remains regression coverage, not
  production raw-theorem coverage.
- [ ] Differentially compare raw Lean elaboration against the old bridge over
  both pinned solc versions and the full corpus: Aave frontend shape now
  compares raw Standard JSON against the legacy bridge for creation/runtime on
  both pins, and PoolManager frontend shape now compares raw Standard JSON
  against the legacy bridge for creation/runtime on its compatible exact
  solc 0.8.26 pin. Safe and EntryPoint frontend shapes now compare raw
  Standard JSON against the legacy bridge for creation/runtime on both pins.
  Permit2 remains fail-closed legacy coverage because solc 0.8.17 emits no
  structured `irOptimizedAst`. All real suites and adversarial fixtures remain
  to be widened.
- [x] Add a raw-bridge transition path: `evm-compiler-backend raw-*` consumes
  raw solc Standard JSON directly through `RawAstPublic`, and the transition
  smoke proves normalized-bridge mutations cannot affect raw input compilation.
- [ ] Add local preservation/validation theorems for raw elaboration,
  nested-function hoisting, and `clz` expansion. `elaborateCode_parts`
  reconstructs the checked raw elaboration core state from successful public
  code elaboration, and `decodeAndElaborateSolcIrJson_parts` reconstructs the
  selected raw Standard JSON source/contract/object plus checked raw-object
  elaboration from a successful frontend program decode.
  `decodeAndElaborateSolcIr?_parts` lifts that evidence to the public raw
  string interface. `Raw.Object.elaborate?_parts`,
  `decodeAndElaborateSolcIrJson_objectParts`, and
  `decodeAndElaborateSolcIr?_objectParts` reconstruct the successful checked
  code elaboration, object-item elaboration, and final `Frontend.Object`
  fields. `itemRefsPreserveOrder?` validates that the elaborated frontend
  object keeps the mixed raw object/data order through raw-derived
  `ObjectItemRef`s; the raw string and artifact wrapper theorems expose this
  checked condition. `compileArtifactFromRawSolcIr?_rawParts` and the
  explicit-linker variant lift the same raw parse/selection/elaboration
  evidence through the artifact-facing wrappers, including Lean-decoded linker
  metadata for the default path. First checked `clz` validation invariant:
  successful code
  elaboration that returns generated `clz` helper/argument/result names also
  returns the corresponding generated helper function definition. First checked
  nested-hoist validation invariant: every function accumulated in the raw
  elaborator's `hoistedFunctions` state is retained in the successful returned
  function list. `Raw.Object.ClzExpansionOk` and
  `Raw.Object.HoistedFunctionsRetained` lift these invariants through raw
  object elaboration, raw string decoding, and artifact-wrapper success. The
  generated `clz` helper theorem now also exposes its one-argument/one-result
  shape plus successful Yul function-definition conversion. The helper is
  factored through a named `ClzHelperSpec` over the generated binary-search
  schedule and exact helper body. Successful raw object elaboration, raw string
  decoding, and artifact-wrapper compilation now expose
  `Raw.Object.ClzHelperSpecOk`. The local `ClzHelperModel` now gives the
  generated schedule a checked executable semantic target: it proves the
  highest-bit schedule returns `255 - highestBit` for all 256 nonzero bit
  positions and checks representative `UInt256` executions against the
  `255 - log2(x)` reference. `ClzHelperExecution` executes the exact generated
  helper-body frontend fragment over the same `UInt256` primitives and proves
  its returned word equals `ClzHelperModel.run`; the spec and raw-code
  elaboration lift theorems expose that fact for generated helper entries
  returned by successful elaboration. `ClzCallReplacement` now proves that an
  evaluated raw `clz(x)` replacement call to the generated helper returns
  `ClzHelperModel.run x`, and successful production raw object elaboration
  exposes that theorem for its generated helper entry. The word/log bridge now
  proves the helper branch condition: for nonzero values and solc's checked
  shifts below 256, the generated `shr`/`iszero` test is equivalent to
  `log2(value) < checkShift`. It also proves that checked non-overflowing
  helper left shifts add the shift amount to `log2`. Production raw elaboration
  now composes those branch/shift facts through the generated eight-step
  schedule: `ClzHelperModel.runNonzero_ret_eq_runHighestBit` proves the nonzero
  fold result, `ClzHelperModel.run_eq_reference` proves the all-word model
  equals the declared `255 - log2(x)` source reference, and
  `ClzCallReplacement.evalHelperCallExpr_eq_reference` plus the production raw
  object wrapper expose that a generated helper-call replacement returns the
  source reference value. Production raw elaboration
  now fail-closes unless the generated `clz` argument/result names are distinct,
  and exposes the checked condition through a wrapper theorem that discharges
  the helper-execution theorem's name premise. Retained
  nested function-definition statements are alpha-renamed to generated function
  names before their checked frontend no-op lowering. Raw production elaboration
  now also fail-closes on any
  frontend object that still contains an unlowered callee named exactly `clz`,
  with decode and artifact wrapper theorems exposing
  `Frontend.Object.noRawClzCall? = true`. It also fail-closes unless every
  retained nested-function staging node has an identical callable entry in the
  same frontend object's function table, with decode and artifact wrapper
  theorems exposing `Frontend.Object.functionDefStubsRetained? = true`.
  Production Yul
  conversion now separately fail-closes unless every retained nested-function
  staging node lowers through the frontend Yul lowering function to one of the
  exact ordered Yul function entries consumed by the backend, with
  `Frontend.Object.toSolcYulOrderedProgram?_functionDefStubsLoweredToEntries`
  pinned in the verification root. The nested-stub no-silent-erasure facts now
  expose the local boolean evidence at the exact erased node: a retained
  `functionDef` staging node has a matching callable `FunctionDef` entry, and
  a staging node erased during Yul conversion has an ordered lowered Yul
  function entry for its body. Raw production elaboration now also fail-closes
  unless every frontend `.call .user` resolves to a function entry in the
  current frontend object's function table, checking each child object against
  its own function table. The raw object, raw JSON/string decode, and
  artifact-wrapper theorems expose
  `Frontend.Object.userCallsResolved? = true` for successful production raw
  elaboration. The raw elaborator now also exposes local alpha-resolution
  equations: singleton and cons-case nested-function scope construction create
  the raw-name to generated-name mapping, ordinary user-call elaboration
  rewrites a raw source callee to the generated name returned by that active
  function-scope resolver, and nested function-definition elaboration emits the
  retained frontend stub under that same resolved generated name. The hoist
  pass also exposes the corresponding single-definition equation: when the
  active local function scope maps a raw nested name to a generated name,
  hoisting inserts the elaborated function entry under that generated name in
  `hoistedFunctions`. The active pushed scope now has checked lookup/resolve
  facts for that head mapping, and singleton hoist insertion has a local
  preservation fact showing entries produced while elaborating the nested
  function body remain present after the generated entry is prepended. The
  declaration and assignment name-check loops are now structural helpers with
  local hoisted-accumulator preservation lemmas. Raw expression/list
  elaboration now has checked hoisted-entry preservation, including user-call
  resolution, `memoryguard`, and `clz` helper allocation. Raw statement,
  block, case-list, function-definition, and local-hoist elaboration now
  preserve accumulated hoisted entries through recursive tails, including
  entries just added for generated nested functions. Successful local scope
  lookup now has checked witnesses back to a raw nested definition and forward
  to the generated hoisted frontend function entry inserted by the production
  hoist pass. Raw user-call elaboration through such a local scope now has a
  checked bridge to both the generated frontend call target and the generated
  hoisted callee entry. Full block elaboration now carries successful local
  generated-name lookups through production nested-function hoisting,
  statement elaboration, and scope popping to a generated hoisted callee entry
  in the block final state, for both scope-creating and non-scope-creating
  blocks. Raw blocks now also have a source-facing `Raw.Source.LocalFunction`
  declaration relation, independent of generated names, and successful local
  scope construction/block elaboration realizes each such source declaration
  as a generated hoisted entry. Source-name user-call elaboration under that
  local scope now also has checked evidence for the generated frontend call
  target and the corresponding hoisted callee entry after production block
  elaboration and scope popping; the bridge derives reserved-name exclusions
  from successful scope construction rather than exposing them as caller
  premises, and successful source local-function validation now also derives
  `CallClass.classifyCall name = .user` for those source names. Raw
  expression/list argument elaboration now also preserves the active function
  scope stack, so the source-call bridge requires only the pre-argument active
  local scope and derives the post-argument resolver scope internally. Raw
  statement, statement-list, block, local-hoist, for-init block, case-list, and
  function-definition elaboration now preserve/restore the active
  `functionScopes` stack, giving the source-call proof a checked way to carry
  actual source-name local call scopes through production block elaboration.
  Direct head source-name calls in both scope-creating and non-scope-creating
  raw blocks now have checked occurrence theorems: successful production block
  elaboration emits the generated frontend `.user` call and retains the
  matching generated callee entry. This has been generalized to arbitrary
  direct expression-statement source calls in a block: `Raw.Source.LocalCall`
  records the source occurrence, `elaborate_source_local_call_mem` carries it
  through statement-list elaboration under the active generated function scope,
  and block wrappers expose the generated frontend call occurrence plus the
  retained generated callee entry. The expression layer now also has a
  source/target occurrence handle: `Raw.Source.ExprCall.Direct` records an
  exact raw function-call expression, `FrontendOccurrence.UserCall` records the
  generated frontend `.user` call occurrence, and
  `Expr.elaborate_direct_source_user_call_occurrence` proves successful
  expression elaboration connects the two under the checked local scope.
  `Raw.Source.ExprCall.Occurs` and `ListOccurs` now lift that handle through
  recursive raw function-call argument occurrences; successful expression/list
  elaboration carries those source occurrences to generated frontend user-call
  occurrences, including through ordinary calls and the one-argument
  `memoryguard`/`clz` special elaboration paths. `Raw.Source.StmtExprCall`
  and `FrontendOccurrence.StmtIncomingUserCall` now lift those recursive
  expression facts into incoming-scope statement expression fields:
  variable declarations, assignments, expression statements, switch scrutinees,
  and `if` conditions, and successful statement-list elaboration preserves
  those occurrences into the returned frontend statement list. Successful
  scope-creating and non-scope-creating block elaboration now also exposes the
  generated frontend occurrence plus the retained generated callee entry for
  such incoming-scope source occurrences, and
  `FrontendOccurrence.StmtUserCall`/`StmtListUserCall` provide the recursive
  frontend occurrence target needed to carry those calls through nested
  statements. `Raw.Source.StmtCall`/`StmtListCall`/`CaseListCall` now provide
  the matching recursive raw source occurrence grammar, and incoming
  statement-expression leaves have checked transport into the recursive
  frontend target. `Raw.Source.NoShadowStmtCall`/`NoShadowStmtListCall`/
  `NoShadowCaseListCall` now refine that grammar with the no-shadow path facts
  required for an outer resolver entry to remain valid through nested
  block-like scopes, including `for` initializer local-function scopes, and
  erase back to the plain source occurrence grammar.
  No-shadow structural wrappers now carry those incoming leaves through raw
  block statements, `if` bodies, switch case bodies, and switch defaults into
  the recursive frontend target. Raw expression/list occurrences now also have
  resolver-stack variants, so the source-call preservation theorem can follow
  `resolveFunctionIn name state.functionScopes = some generated` through
  shadowing nested scopes instead of assuming the callee is found in the head
  scope. Incoming statement expression fields and statement lists have matching
  resolver-stack occurrence theorems. `for` initializer local-function scope
  handoff is now checked for condition calls, and for post/body calls when the
  post/body block does not declare a shadowing local function with the same
  source name: a source local function declared in the initializer is retained
  as a hoisted generated callee and these calls elaborate to the generated
  frontend user call. Non-scope-creating blocks and `for` initializer blocks
  now also have no-shadow resolver transport helpers, so outer resolved calls
  in initializer statements survive local function-scope construction when the
  initializer does not shadow the callee name, and the `Stmt.elaborate`
  wrappers now carry such initializer statement occurrences to frontend
  `forPre` user-call occurrences and condition expression occurrences to
  frontend `forCondition` user-call occurrences. Post-block occurrences now
  also have a no-shadow wrapper when neither the initializer nor the post block
  shadows the callee, and body-block occurrences have a wrapper when the
  initializer and body do not shadow the callee; post-local functions are
  allowed because the post block restores the function-scope stack before body
  elaboration. Function-definition bodies now also have no-shadow wrappers
  through `FunctionDef.elaborate` and the enclosing statement elaboration,
  carrying body occurrences to frontend `functionBody` user-call occurrences.
  Recursive source-side nested block/body occurrence traversal is now checked
  by the no-shadow theorem family
  `Elab.Stmt.elaborate_noShadow_resolved_source_stmt_call`,
  `Elab.Stmt.List.elaborate_noShadow_resolved_source_stmt_list_call`,
  `Elab.Stmt.List.elaborateBlock_noShadow_resolved_source_stmt_list_call`,
  `Elab.Stmt.List.elaborateForInitBlockWithScope_noShadow_resolved_source_stmt_list_call`,
  `Elab.Stmt.CaseList.elaborate_noShadow_resolved_source_case_list_call`,
  and
  `Elab.FunctionDef.elaborate_noShadow_resolved_source_stmt_list_call`,
  including block/function/switch/for/if bodies and shadow-aware post/body
  composition. Source-local block composition now also combines these
  recursive occurrence facts with local-function scope construction and hoist
  retention:
  `Elab.Stmt.List.sourceLocalFunction_elaborateBlock_false_noShadow_stmtUserCall_entry`,
  `Elab.Stmt.List.sourceLocalFunction_elaborateBlock_true_noShadow_stmtUserCall_entry`,
  and
  `Elab.Stmt.List.sourceLocalFunction_elaborateForInitBlockWithScope_noShadow_stmtUserCall_entry`
  prove that a block declaring the source local function and containing a
  resolver-safe recursive call elaborates to the generated frontend user-call
  occurrence while retaining the generated callee entry. Function bodies and
  retained `functionDef` staging statements now lift that same evidence through
  `Elab.FunctionDef.elaborate_sourceLocalFunction_noShadow_stmtUserCall_entry`
  and
  `Elab.Stmt.elaborate_functionDefinition_sourceLocalFunction_noShadow_stmtUserCall_entry`.
  Successful `FunctionDef.elaborate` now also realizes source local-function
  declarations in the raw function body as generated hoisted callee entries in
  the final elaborator state, without exposing the block's internal scope
  construction witnesses. The top-level raw-code elaborator loop is now a
  structural helper with preservation/source-local-entry theorems; its
  no-shadow caller/callee wrappers now carry both the top-level caller function
  containing the generated frontend user-call occurrence and the generated
  hoisted callee entry through raw code, checked object elaboration, and the
  checked JSON/raw-string decode interface. Raw object elaboration carries
  source local-function declarations through the returned frontend function
  table to the ordered Yul function-entry list consumed by the backend.
  Successful
  ordered-Yul conversion now also
  exposes a checked
  function entry for every name present in `object.functions.map Prod.fst`,
  giving resolved user-call names a concrete emitted callee entry at the
  frontend/Yul boundary, and stack-code artifact construction carries such
  names through object-builtin resolution to artifact-level function entries.
  The raw compiler wrapper now exposes that artifact-level evidence for
  decoded programs produced by `decodeAndElaborateSolcIr?`, and successful raw
  artifact compilation now carries source-local no-shadow caller/callee
  occurrence-entry evidence together with checked artifact validity. Hoisted
  frontend function entries now also have a
  checked path through `toSolcYulOrderedProgram?` to the emitted ordered Yul
  function-entry list consumed by the backend, and successful raw artifact
  compilation now carries hoisted raw callees through object-builtin
  resolution into the artifact's production ordered Yul function entries.
  The public raw end-to-end theorem now also has source-local no-shadow
  variants that compose caller/callee occurrence-entry evidence with both the
  finite-prefix and `hFinished` bytecode preservation results. The same public
  boundary now also exposes
  `Raw.Source.AlphaRenamedLocalCallPreserved`, a source-facing relation that
  bundles the raw local declaration, resolver-safe source call, and generated
  frontend caller/callee resolution without exposing the generated alpha name
  as separate public plumbing. That relation now has a checked ordered-Yul
  lowering theorem:
  `AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_entries` proves the
  alpha-preserved caller and generated callee are both emitted as exact ordered
  Yul function entries consumed by the backend, and
  `AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_callable_entries`
  proves those same entries populate the ordered program's function map, which
  is the lookup used by `Yul.InteractionSemantics.call`. The end-to-end layer
  now also has
  `alphaRenamedLocalCallPreserved_call_succ_of_local_body`, a semantic
  corollary showing that, once the generated callee body executes from the
  initialized call frame, the generic Yul call rule returns exactly through
  that generated callee body. The frontend/Yul boundary now also exposes
  `FrontendOccurrence.UserCall.toYul?_occurrence` and
  `FrontendOccurrence.StmtIncomingUserCall.toYul?_occurrence`, proving that
  incoming generated frontend user-call occurrences lower to concrete generated
  Yul call occurrences with lowered argument lists.
  `FrontendOccurrence.LowerableStmtListUserCall.toYul?_occurrence` lifts that
  fact through lowerable frontend statement-list contexts, including blocks,
  switches, loops, and if bodies, while still excluding erased `functionDef`
  staging nodes from the current-body claim.
  `FrontendOccurrence.LowerableResolvedLocalCall.toSolcYulOrderedProgram?_entries`
  now packages the lowerable caller-body occurrence with ordered-Yul conversion,
  yielding the concrete lowered caller-body occurrence plus the generated callee
  ordered function entry.
  `FrontendOccurrence.StmtListUserCall.lowerable_or_stubBody` and
  `FrontendOccurrence.ResolvedLocalCall.lowerable_or_stubBody` now split the
  broad resolved-call relation into lowerable caller-body and retained
  `functionDef` body routes, while
  `FrontendOccurrence.StubBodyStmtListUserCall.lowered_function_entry` uses the
  existing `functionDefStubsLoweredToEntries?` validator to expose the concrete
  lowered function entry for the first retained-stub body branch. The
  one-step theorem
  `FrontendOccurrence.StubBodyStmtListUserCall.lowered_function_entry_step`
  then either exposes a concrete generated Yul call occurrence inside that
  lowered stub body or returns the next retained-stub body branch to chase.
  `FrontendOccurrence.StubBodyStmtListUserCall.lowered_function_entry_chaseFuel`
  carries the validator through any supplied number of retained-stub hops,
  returning either a concrete generated Yul call occurrence in a lowered stub
  entry or a validated residual stub branch when the supplied fuel is exhausted.
  The structural theorem
  `FrontendOccurrence.StubBodyStmtListUserCall.lowered_function_entry_chase`
  now removes that public fuel/residual shape by proving every validated
  retained-stub hop decreases the frontend statement-list `sizeOf`, so the
  chase reaches a concrete generated Yul call occurrence in an emitted lowered
  function entry.
  `FrontendOccurrence.StubBodyResolvedLocalCall.toSolcYulOrderedProgram?_chase`
  uses that structural chase with ordinary object Yul conversion, exposing the
  retained-stub generated Yul call occurrence plus the generated callee entry
  consumed by the backend.
  `AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_call_occurrence_routes`
  packages the lowerable and retained-stub ordered-occurrence routes behind
  the source-facing alpha-preservation relation.
  `YulOccurrence.UserCall.direct_or_arg_split` now separates a lowered
  expression occurrence into either the direct generated call or an outer call
  with the recursive occurrence isolated inside its argument list, matching
  the existing `evalArgs_append_*` semantic interface.
  `Yul.Source.Effectful.evalArgs_split_focus_of_parts` now composes right-side
  argument evaluation, focused generated-call evaluation, and left-side
  argument evaluation for the reversed Yul argument order used by
  `evalValues`.
  `Yul.Source.Effectful.evalValues_primitive_split_focus_of_parts` and
  `Yul.Source.Effectful.evalValues_function_split_focus_of_parts` lift the
  same focused-argument composition through primitive and user-function outer
  calls.
  `YulOccurrence.StmtListUserCall.exists_split_stmt` and
  `YulOccurrence.CaseListUserCall.exists_split_body` now decompose recursive
  lowered Yul occurrences into the concrete focused statement or switch case
  body plus its surrounding prefix/suffix, preparing the recursive semantic
  composition to consume the sequence-prefix lemmas.
  `alphaRenamedLocalCallPreserved_call_occurrence_routes_succ` composes that
  route split with the Yul `Effectful.call` rule, so both occurrence routes now
  share the exact generated callee lookup used by the interpreter.
  `alphaRenamedLocalCallPreserved_evalValues_call_occurrence_routes_succ`
  extends this through lowered Yul argument evaluation for the generated call
  expression itself.
  `alphaRenamedLocalCallPreserved_eval_call_occurrence_routes_succ` exposes
  the single-value `eval` view used by condition-like expression contexts,
  returning the generated call's head value after argument evaluation and
  generated callee execution.
  `alphaRenamedLocalCallPreserved_outerArg_evalValues_call_occurrence_routes_succ`
  now composes that single-value generated-call view through one surrounding
  primitive or user-function call argument list.
  `alphaRenamedLocalCallPreserved_outerArg_eval_call_occurrence_routes_succ`
  exposes the corresponding one-return `eval` view for condition and switch
  scrutinee contexts.
  `alphaRenamedLocalCallPreserved_ifCondition_outerArg_call_occurrence_routes_succ`
  composes that one-return outer-call view through zero and nonzero Yul `if`
  condition execution.
  `alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_call_occurrence_routes_succ`
  composes the same outer-call view through Yul `switch` scrutinee evaluation
  and selected case/default execution.
  `alphaRenamedLocalCallPreserved_ifCondition_outerArg_seqHead_call_occurrence_routes_succ`
  and
  `alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_seqHead_call_occurrence_routes_succ`
  expose those outer control contexts in direct `execSeq` form for recursive
  statement-list composition.
  `alphaRenamedLocalCallPreserved_assignLet_outerArg_call_occurrence_routes_succ`
  composes the same outer-call argument view through assignment and declaration
  statement writeback for both primitive and user-function outer calls.
  `alphaRenamedLocalCallPreserved_assignLet_outerArg_seqHead_call_occurrence_routes_succ`
  exposes those outer assignment/declaration writeback contexts in direct
  `execSeq` form for recursive statement-list composition.
  `alphaRenamedLocalCallPreserved_exprStmt_outerArg_call_occurrence_routes_succ`
  covers the no-target expression-statement sibling, including the extra fuel
  step in Yul's user-function expression-statement rule.
  `alphaRenamedLocalCallPreserved_exprStmt_outerArg_seqHead_call_occurrence_routes_succ`
  exposes that outer expression-statement context in direct `execSeq` form for
  recursive statement-list composition.
  `alphaRenamedLocalCallPreserved_exprStmt_outerArg_seqPrefix_call_occurrence_routes_succ`
  composes that outer expression-statement sequence-head fact after arbitrary
  regularly executed prefixes.
  `alphaRenamedLocalCallPreserved_ifCondition_call_occurrence_routes_succ` and
  `alphaRenamedLocalCallPreserved_switchScrutinee_call_occurrence_routes_succ`
  compose that view through direct Yul `if` and `switch` condition contexts.
  `alphaRenamedLocalCallPreserved_ifCondition_seqHead_call_occurrence_routes_succ`
  and
  `alphaRenamedLocalCallPreserved_switchScrutinee_seqHead_call_occurrence_routes_succ`
  expose those direct control contexts in `execSeq` form for recursive
  statement-list composition.
  `alphaRenamedLocalCallPreserved_ifCondition_seqPrefix_call_occurrence_routes_succ`
  and
  `alphaRenamedLocalCallPreserved_switchScrutinee_seqPrefix_call_occurrence_routes_succ`
  compose those control-context sequence-head facts after arbitrary regularly
  executed prefixes, giving checked tail-occurrence bridges for branches and
  switches.
  `alphaRenamedLocalCallPreserved_ifCondition_blockHead_call_occurrence_routes_succ`
  and
  `alphaRenamedLocalCallPreserved_switchScrutinee_blockHead_call_occurrence_routes_succ`
  lift those direct control contexts through the head of a surrounding Yul
  block.
  `alphaRenamedLocalCallPreserved_assignLet_call_occurrence_routes_succ`
  adds the ordinary Yul statement writeback for assignment and declaration
  call contexts using `multifill`.
  `alphaRenamedLocalCallPreserved_assignLet_seqHead_call_occurrence_routes_succ`
  exposes those returned-value writeback contexts in direct `execSeq` form for
  recursive statement-list composition.
  `alphaRenamedLocalCallPreserved_assignLet_seqPrefix_call_occurrence_routes_succ`
  composes the assignment/declaration sequence-head facts after arbitrary
  regularly executed prefixes.
  `alphaRenamedLocalCallPreserved_assignLet_blockHead_call_occurrence_routes_succ`
  lifts those returned-value writeback contexts through the head of a
  surrounding Yul block.
  `alphaRenamedLocalCallPreserved_exprStmt_call_occurrence_routes_succ`
  covers the expression-statement/no-target call context.
  `alphaRenamedLocalCallPreserved_exprStmt_seqHead_call_occurrence_routes_succ`
  exposes the same expression-statement case in direct `execSeq` form, which
  is the recursive statement-list interface needed for tail occurrences.
  `alphaRenamedLocalCallPreserved_exprStmt_seqPrefix_call_occurrence_routes_succ`
  composes that expression-statement sequence-head fact after an arbitrary
  regularly executed prefix, giving the first checked tail-occurrence bridge.
  `alphaRenamedLocalCallPreserved_exprStmt_blockHead_call_occurrence_routes_succ`
  lifts that expression-statement context through the head of a surrounding
  Yul block, leaving the remaining sequence as the next composition premise.
  The remaining raw frontend semantic gap is source-level preservation for
  alpha-renamed nested-function call execution/observation in the full caller
  statement/control context and broader composition into the final source
  theorem.
- [x] Expose the production interface
  `decodeAndElaborateSolcIr? rawJson selection = some frontendProgram` without
  public certificate premises, and expose artifact-facing raw wrappers whose
  success reconstructs the internally selected raw source/contract/object,
  checked object elaboration, and artifact validity.
- [x] Add the isolated raw theorem composition:
  `Solidity.RawAst.optimizedRawSolcIrToRawBytecode` composes checked raw
  Standard JSON decoding, Lean-decoded linker metadata, frontend validation,
  and artifact construction into the unconditional optimized-Yul
  finite-prefix theorem without a normalized Python program premise.
- [ ] Close the remaining raw frontend semantic-preservation work by proving
  nested-function hoist/alpha-renaming preservation and composing the local raw
  frontend facts into the final source theorem; do not create a Yul-to-bytecode
  proof corridor or depend on the parallel hFinished work.

## Migration

- [x] Preserve the mixed-allocation research line on
  `codex/archive-mixed-allocation-safety`.
- [x] Remove mixed/scratch allocation from production entrypoints, metadata,
  schemas, CLI routes, architecture exceptions, and verification roots.
- [x] Delete compiler-owned spill planning, slots, cells, frame setup/cleanup,
  and scratch-specific proof modules once unreachable.
- [x] Resolve every validated `memoryguard(size)` to exactly `size` and prove
  the frontend-owned resolution theorem.
- [x] Remove fixed `defaultReservedWords`/8,193-word behavior and explicit
  source scratch-reservation inputs.
- [x] Expose a short optimized-Yul-to-bytecode composition theorem using only
  adjacent pass-owned preservation results and checked compiler artifacts.
- [x] Ensure no generated schedule, layout, certificate, spill plan, replay
  witness, or semantic oracle appears as a public premise.

## Preserved Semantics

- [x] Honest ordered `GAS` and `MSIZE` observations.
- [x] Ordered logs and open-world CALL/CREATE-family effects.
- [x] Generic source `MLOAD`/`MSTORE`, dynamic memory, and solc-generated
  explicit memory spills.
- [x] Liveness, next-use scheduling, joins, dormant caller frames, internal
  calls, and pressure normalization.
- [x] Legitimate gas/OOG, host-memory, fork, initial-state, and trusted-frontend
  assumptions remain explicit.
- [x] Carry the requested EVM version through recursive frontend objects and
  validate primitive availability against that exact profile in Lean; bridge
  inputs without metadata and Cancun operations relabeled as London fail closed.

## Adversarial Coverage

- [x] Add a fixture retaining at least 30 non-rematerializable `SLOAD` values
  across an external call.
- [x] Confirm conventional codegen reports stack-too-deep.
- [x] Confirm optimized Yul contains solc-generated `memoryguard`, `MSTORE`,
  and `MLOAD` spills.
- [x] Compile creation and runtime objects through the checked stack-only path.
- [x] Add generated tuple, parameter, nested-control, loop, internal-call,
  dynamic-memory, CALL/CREATE, and memory-unsafe-assembly pressure cases.
- [x] Record honest rejection when memory-unsafe pressure prevents solc from
  producing stack-schedulable optimized output.

## Completion Gates

- [x] Raw-capable pinned corpus gates pass through checked raw-byte artifacts,
  including linked Aave Pool, PoolManager on its compatible exact 0.8.26 pin,
  Safe, EntryPoint, and adversarial fixtures. Exact Permit2 remains covered as
  a fail-closed solc-0.8.17 version-boundary/legacy-bridge regression because
  that compiler emits no structured `irOptimizedAst`.
- [x] Focused and full `EvmCompiler.Verification` builds pass.
- [x] Architecture and proof-smoke checks pass.
- [x] Repository hole, trust, `unsafe`, and axiom audits pass.
- [x] Frontend regressions and adversarial tests pass.
- [x] `git diff --check` passes.
- [x] Green commits exist at coherent deletion and theorem boundaries.

Deployment-size optimization, source maps, and full gas-aware refinement remain
separate production-hardening goals; they are not prerequisites for this
stack-only correctness boundary.

## Release Hardening

- [x] Derive public initial-state/domain relations from canonical constructors
  wherever they are computational consequences rather than caller assumptions.
- [x] Classify every remaining public premise as trusted frontend input,
  source execution/resource fact, or unfinished derivation; remove the latter.
- [x] Inventory supported optimized-Yul primitives, control outcomes, object
  features, and compiler passes against executable creation/runtime coverage.
- [x] Separate structural proof-fuel exhaustion (`OutOfFuel`) from genuine EVM
  `INVALID` execution (`InvalidInstruction`) at every upper interpreter and
  derive checked call-arity facts instead of classifying malformed calls as
  truncation.
- [x] Extend adjacent preservation and the public theorem from halting outcomes
  to all supported non-truncated runtime errors, beginning with intentional
  `INVALID`; do not count executable bytecode generation as execution proof.
  Yul -> Functions, Functions -> allocated Expressions, and the transparent
  Expressions -> Structured adapter now expose checked finished/stopped
  interfaces. Structured -> TypedCfg now preserves all genuine runtime errors
  and halts through a compiler-owned static budget. TypedCfg -> ordinary
  Assembly source execution now preserves the same all-finished branches;
  compact Assembly encoding now preserves them through a compiler-sized
  `INVALID` sentinel before object payload. The allocation relation now proves
  the one-way structural invariant `target OutOfFuel -> source OutOfFuel`, and
  the public optimized-solc-Yul theorem composes all finished branches through
  the exact recursive object image.
- [ ] Add pinned real-world suites and generated adversarial cases for uncovered
  semantic families, then fix every backend rejection generically or record an
  honest supported-version/input-boundary rejection. The strict corpus now
  includes full pinned Safe and ERC-4337 EntryPoint creation/runtime objects,
  in addition to their smaller executable helper probes; Safe is deliberately
  compile-only because solc's own optimized-Yul backend rejects that pinned
  source with stack-too-deep. The generated execution matrix also covers an
  upgradeable EIP-1967-style proxy with delegated storage, reentrant self-calls,
  revert rollback, event ordering, CREATE-based upgrade, and post-upgrade
  dispatch under both supported solc pins.
  A separate fork-adversarial gate checks honest London and Cancun compilation
  and rejects a schema-valid Cancun object whose metadata is changed to London.
  Raw frontend validation also preserves solc's opcode `0x44` spelling split:
  London accepts `difficulty()`, Paris and later accept `prevrandao()`, and the
  opposite cross-fork relabelings fail before those names reach the shared core
  operation.
- [x] Separate genuine source completion/fuel sufficiency from malformed-source
  exclusion in the all-finished theorem. `truncated_iff_outOfFuel` proves the
  public truncation predicate is exactly structural source `OutOfFuel`;
  validation, scoped variable lookup, and compiler-success inversions discharge
  missing contracts/functions, invalid expressions, unknown identifiers,
  duplicate declarations, and obsolete unsupported failures internally.
- [ ] Keep exact Permit2, Aave Pool, PoolManager, adversarial pressure, broad
  corpus, Lean, architecture, trust, frontend, and diff gates green.

Pinned solc 0.8.26 rejects explicit `msize()` whenever its Yul optimizer is
enabled. This is an honest trusted-frontend limitation, not a backend semantic
restriction: the Yul proof retains real ordered `MSIZE`, while optimized
Solidity coverage records the solc rejection explicitly.

## Unconditional Prefix Theorem

The primary compiler-correctness result will be an unconditional
`Simulation.Interaction.ForwardRel`. Its truncation constructor is the finite
prefix boundary: every ordered request before source semantic-fuel exhaustion
must match exactly, while the theorem makes no claim about the unobserved target
suffix. The all-finished theorem remains a corollary, not the primary boundary.

- [x] Add shared composition for adjacent `ForwardRel` theorems when the first
  pass reflects second-pass truncation back to source truncation.
- [x] Expose Yul -> Functions -> allocated Expressions forward preservation
  with compiler-computed target fuel and no `hFinished` premise.
- [x] Lift the transparent Expressions -> Structured adapter without changing
  the prefix relation.
- [x] Extend Structured -> TypedCfg with source-`OutOfFuel` prefix preservation
  at the existing compiler-owned uniform target budget.
- [x] Compose TypedCfg -> Assembly source prefixes with branch-local terminal
  safety and exact structural-truncation reflection.
- [x] Compose Assembly -> compact decoded bytecode through pass-owned
  preparation and physical-encoding prefix theorems.
- [x] Compose compact bytecode through recursive objects
  without requiring terminal or finished source trees.
- [x] Publish a short canonical `Yul.EndToEnd` forward theorem requiring only
  checked compilation and canonical related initial states.
- [x] Derive the canonical all-finished theorem from the forward
  theorem plus their explicit run properties.
- [x] Guard the public theorem against `hFinished`, generated evidence, replay
  witnesses, or imports that cross nonadjacent compiler owners.
