# Verified Yul-to-EVM compiler

This repository contains a Lean implementation and preservation proof for the
solc Yul-to-EVM bytecode pipeline, plus Python and Forge-based integration
tests.

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
git clone <repository-url> evm-compiler
cd evm-compiler
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
[`scripts/README.md`](scripts/README.md). Current proof scope and remaining
gaps are tracked in [`ROADMAP.md`](ROADMAP.md).
