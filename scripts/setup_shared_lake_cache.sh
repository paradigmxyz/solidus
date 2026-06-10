#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

cache_root="${EVM_COMPILER_LAKE_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/evm-compiler/lake-deps}"
key="$(
  {
    cat lean-toolchain
    shasum -a 256 lake-manifest.json
  } | shasum -a 256 | awk '{ print $1 }'
)"
shared_dir="$cache_root/$key"
shared_packages="$shared_dir/packages"

mkdir -p "$shared_dir" .lake

if [[ -L .lake/packages ]]; then
  current="$(readlink .lake/packages)"
  if [[ "$current" == "$shared_packages" ]]; then
    printf 'shared Lake package cache already active: %s\n' "$shared_packages"
    exit 0
  fi
  printf '.lake/packages already points to a different cache: %s\n' \
    "$current" >&2
  exit 1
fi

if [[ -d .lake/packages && ! -e "$shared_packages" ]]; then
  mv .lake/packages "$shared_packages"
elif [[ -d .lake/packages && -e "$shared_packages" ]]; then
  printf 'both local and shared package directories exist; refusing to discard either\n' >&2
  exit 1
elif [[ ! -e "$shared_packages" ]]; then
  mkdir -p "$shared_packages"
fi

ln -s "$shared_packages" .lake/packages
printf 'shared Lake package cache active: %s\n' "$shared_packages"
