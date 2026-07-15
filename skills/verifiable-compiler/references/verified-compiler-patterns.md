# Verified Compiler Patterns

Use this reference when choosing theorem boundaries or auditing claims.

## Design Patterns

- **Target-up vertical slice first**: start near the declared target
  interpreter, add one abstraction layer above it, and prove that adjacent
  lowering before adding more features or higher layers.
- **Semantic preservation**: state that target execution behavior is included in
  or refines source behavior under explicit assumptions.
- **Layered passes**: prove each transformation or keep transformations fused
  until the theorem shape is stable.
- **Primitive classifier boundary**: for large opcode/operator surfaces, route
  proofs through a small semantic-family API. Either make it the declared
  lower-layer step API or prove it agrees with the real target dispatcher.
- **Interpreter endpoint**: a theorem ending at emitted IR is not end-to-end
  unless that IR has its own verified interpreter/encoder path.
- **Trusted boundary minimization**: unverified parsers/wrappers may feed
  candidate data, but Lean must check/admit only the trusted subset.
- **Certificate option**: if full verification is too expensive, make external
  tools produce certificates checked by Lean.
- **Assumption ledger**: undefined behavior, fuel, nontermination, environment
  calls, crypto/hashes, memory model, gas/resources, and parser trust must be
  in theorem statements or state documents.

## Influential References

- CompCert reports semantic preservation for a realistic C compiler, with Coq
  used both to program the compiler and prove correctness:
  https://xavierleroy.org/bibrefs/Leroy-Compcert-CACM.html
- CakeML separates language definition, verified backend, verified frontend
  properties, bootstrapping, and verified applications. Its public overview is
  especially useful for trust-boundary thinking:
  https://cakeml.org/
- CakeML's latest compiler overview notes multiple intermediate languages and
  multiple concrete machine-code targets, a useful model for staged growth:
  https://cakeml.org/
- Software Foundations' compiler chapters are useful for tiny first slices:
  expression/statement semantics, stack machines, and preservation proofs:
  https://softwarefoundations.cis.upenn.edu/
- AutoResearch's useful process lesson is not ML-specific: constrain the action
  space, keep a fixed metric/harness, log every experiment, and only keep
  changes validated by the harness:
  https://github.com/karpathy/autoresearch
- Parallel-agent research patterns are not the default for this skill. Prefer
  one orchestrating agent that preserves the theorem spine; use delegation only
  for explicitly requested, bounded, non-blocking tasks.

## Anti-Patterns

- Starting with full language syntax, full ABI, optimizer, or realistic machine
  model before a tiny theorem works.
- Building many executable features whose proofs are "obvious later".
- Reporting a theorem name in metadata for functions/features outside its
  accepted subset.
- Trusting parser output because tests pass.
- Letting a toy backend theorem become a real-backend claim without a bridge.
- Using `native_decide` or external automation as proof evidence without
  auditing its trusted assumptions.
- Full rebuild loops for every proof edit; this pushes the agent toward broad
  unverified coding instead of proof-driven iteration.
- Treating a simplified primitive classifier as target fidelity without an
  equality/refinement theorem to the declared target interpreter.
