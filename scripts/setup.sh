#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

case "$(uname -s)" in
  Darwin|Linux) ;;
  *)
    printf 'error: setup supports macOS and Linux only\n' >&2
    exit 1
    ;;
esac

missing=()
for command_name in curl git jq; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    missing+=("$command_name")
  fi
done
if (( ${#missing[@]} > 0 )); then
  printf 'error: missing system prerequisites: %s\n' "${missing[*]}" >&2
  if [[ "$(uname -s)" == "Darwin" ]]; then
    printf 'install the Xcode command-line tools and jq, then retry:\n' >&2
    printf '  xcode-select --install\n  brew install jq\n' >&2
  else
    printf 'on Debian/Ubuntu, install them with:\n' >&2
    printf '  sudo apt-get update\n' >&2
    printf '  sudo apt-get install -y build-essential ca-certificates curl git jq\n' >&2
  fi
  exit 1
fi

export PATH="$HOME/.local/bin:$HOME/.elan/bin:$HOME/.foundry/bin:$PATH"

if ! command -v uv >/dev/null 2>&1; then
  printf 'installing uv\n'
  curl -LsSf https://astral.sh/uv/install.sh | sh
fi

printf 'syncing the locked Python 3.12 environment\n'
uv python install 3.12
uv sync --locked

if ! command -v elan >/dev/null 2>&1; then
  printf 'installing elan\n'
  curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- \
    -y --default-toolchain none
fi

lean_toolchain="$(tr -d '[:space:]' < lean-toolchain)"
if ! elan toolchain list | grep -Fxq "$lean_toolchain"; then
  printf 'installing the pinned Lean toolchain: %s\n' "$lean_toolchain"
  elan toolchain install "$lean_toolchain"
else
  printf 'pinned Lean toolchain is already installed: %s\n' "$lean_toolchain"
fi

printf 'syncing pinned Lake dependencies\n'
lake update
if [[ "${SKIP_MATHLIB_CACHE:-0}" != "1" ]]; then
  printf 'downloading the Mathlib build cache when available\n'
  if ! lake exe cache get; then
    printf 'warning: Mathlib cache download failed; Lake will build it locally\n' >&2
  fi
fi

if ! uv tool list | grep -Fxq 'solc-select v1.2.0'; then
  printf 'installing solc-select 1.2.0 with uv\n'
  uv tool install --force 'solc-select==1.2.0'
fi

if [[ "$(uname -s)" == "Linux" ]] &&
    [[ "$(uname -m)" == "arm64" || "$(uname -m)" == "aarch64" ]] &&
    ! command -v qemu-x86_64 >/dev/null 2>&1; then
  printf 'error: Linux ARM64 needs qemu-x86_64 for the pinned solc binaries\n' >&2
  printf 'Debian/Ubuntu: sudo apt-get install qemu-user-static\n' >&2
  exit 1
fi

solc_versions=(0.8.17 0.8.19 0.8.26 0.8.35)
for version in "${solc_versions[@]}"; do
  compiler="$HOME/.solc-select/artifacts/solc-$version/solc-$version"
  if [[ ! -x "$compiler" ]]; then
    printf 'installing solc %s\n' "$version"
    solc-select install "$version"
  fi
  SOLC_VERSION="$version" solc --version >/dev/null
done
solc-select use 0.8.26

foundry_version="${FOUNDRY_VERSION:-v1.5.1}"
foundry_numeric="${foundry_version#v}"
if ! command -v foundryup >/dev/null 2>&1; then
  printf 'installing foundryup\n'
  curl -L https://foundry.paradigm.xyz | bash
  export PATH="$HOME/.foundry/bin:$PATH"
fi
if ! command -v forge >/dev/null 2>&1 ||
    ! command -v cast >/dev/null 2>&1 ||
    [[ "$(forge --version 2>/dev/null || true)" != *"Version: $foundry_numeric"* ]]; then
  printf 'installing Foundry %s\n' "$foundry_version"
  foundryup --install "$foundry_version"
fi

printf '\nsetup complete\n'
printf '  uv:      %s\n' "$(uv --version)"
printf '  python:  %s\n' "$(.venv/bin/python --version)"
printf '  lean:    %s\n' "$(lean --version | head -n 1)"
printf '  lake:    %s\n' "$(lake --version | head -n 1)"
printf '  solc:    %s\n' "$(SOLC_VERSION=0.8.26 solc --version | tail -n 1)"
printf '  forge:   %s\n' "$(forge --version | head -n 1)"
printf '\nRun the full suite with: make test\n'
