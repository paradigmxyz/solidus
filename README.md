# Solidus

Solidus is a work-in-progress compiler from Solidity to the EVM, implemented
and formally verified in [Lean 4](https://lean-lang.org/).

> **⚠️ Pre-alpha.** Solidus is a research project, not production software. Do
> not use it to compile contracts that hold real value. The formal verification
> has known and (likely) unknown gaps — part of the point of opening this
> project up is to pressure-test them.

## What is here today

The **backend** of Solidus — from Yul (the intermediate representation used by
the Solidity compiler) down to EVM bytecode — is essentially complete and
formally verified. A single Lean theorem, `Solidus.compile_correct`, connects
the source program's semantics to the emitted bytes on a pinned EVM
interpreter. The repository also contains a proposed formal semantics for Yul.

The **frontend** (Solidity → Yul) does not exist yet. Today the supported
pipeline takes the `irOptimizedAst` Yul object emitted by a pinned `solc` and
compiles it to bytecode, with a machine-checked preservation proof from
compile success alone. Finalizing a frozen Solidity source semantics and
building a verified frontend against it is the next phase of the project.

Because the correctness claim is a machine-checked theorem over a frozen
specification, contributions do not need a "did you break something" review
step: if the compiler builds, the axiom audit is clean, and the frozen spec
still elaborates, a rewrite is correct by construction. That is what makes
aggressive, trustless optimization — including by untrusted automated
contributors — possible. See [`CHALLENGE.md`](CHALLENGE.md) for the
optimization challenge built on this property.

## How it was built

Solidus is an automated-research project: no human read or wrote a line of its
code. It was built over roughly ten weeks of aggregate agent time across many
parallel threads, primarily with OpenAI's Codex, with Harmonic's Aristotle
used for some of the hardest proofs and Claude used for some of the final
steps. Humans supplied the spec judgment and some of the higher-level proof
architecture.

## Trust boundary and proof status

- [`PRODUCTION_ASSUMPTIONS.md`](PRODUCTION_ASSUMPTIONS.md) — the authoritative
  trust and theorem boundary, including a "Which theorem should I rely on?"
  guide.
- [`ROADMAP.md`](ROADMAP.md) — current proof scope and remaining gaps.
- [`CHALLENGE.md`](CHALLENGE.md) — the Solidus optimization challenge: make
  compiled contracts cheaper while the theorem still proves.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — how to contribute.

## Install on macOS or Linux

The bootstrap script installs user-local tooling and project dependencies. It
does not use `sudo`.

System prerequisites:

- macOS: install the Xcode command-line tools (`xcode-select --install`) and
  `jq` (`brew install jq`).
- Debian/Ubuntu: `sudo apt-get install -y build-essential ca-certificates curl git jq`.
- Other Linux distributions: install a C/C++ toolchain, `curl`, `git`, and
  `jq` with the system package manager.
- Linux ARM64 also needs `qemu-x86_64` (for example,
  `sudo apt-get install qemu-user-static`) because the pinned solc binaries are
  x86-64.

Then run:

```sh
git clone https://github.com/paradigmxyz/solidus.git
cd solidus
./scripts/setup.sh
```

Setup installs and selects:

- Python 3.12 and the locked Python environment through
  [uv](https://docs.astral.sh/uv/getting-started/installation/);
- elan and the Lean version pinned by `lean-toolchain`;
- the Lake dependencies pinned by `lake-manifest.json` and the Mathlib cache;
- [solc-select](https://github.com/crytic/solc-select) 1.2.0 with solc
  0.8.17, 0.8.19, 0.8.26, and 0.8.35;
- Foundry v1.5.1 (`forge`, `cast`, `anvil`, and `chisel`).

The official installers used by the script are documented by
[Lean/elan](https://lean-lang.org/install/),
[uv](https://docs.astral.sh/uv/getting-started/installation/), and
[Foundry](https://getfoundry.sh/getting-started/installation/). Set
`SKIP_MATHLIB_CACHE=1` to skip only the optional prebuilt Mathlib download, or
`FOUNDRY_VERSION=vX.Y.Z` to test another Foundry release.

## Run the tests

Run every Lean, Python, shell, real-contract, and supported-solc test exactly
once (with the nine compiler-surface tests run once for each supported solc):

```sh
make test
# equivalent: ./scripts/test_all.sh
```

The full suite fetches pinned public contract repositories, so it requires
network access. It continues after individual failures and writes one log per
test under `.test-results/<timestamp>/`, then exits nonzero with a summary.

Useful focused commands:

```sh
make verify       # architecture checks, full Lean build, proof smokes
make python-test  # Python unit suite in the uv environment
uv run -- scripts/test_advanced_type_surface_backend.sh
```

No manual virtual-environment activation or `pip install` is needed. Use
`uv add <package>` when changing Python dependencies, commit both
`pyproject.toml` and `uv.lock`, and use `uv run -- <command>` for an individual
script that imports project Python dependencies.

Detailed bridge and diagnostic command documentation lives in
[`scripts/README.md`](scripts/README.md).
