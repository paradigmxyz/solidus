#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
SOLC_VERSION="${EIGENLAYER_SOLC_VERSION:-0.8.35}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-$SOLC_VERSION/solc-$SOLC_VERSION}"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

EIGENLAYER_REPO_URL="${EIGENLAYER_REPO_URL:-https://github.com/Layr-Labs/eigenlayer-contracts.git}"
EIGENLAYER_REF="${EIGENLAYER_REF:-d302f65042164c8d8d0a983c1540d85a8710030b}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-eigenlayer-bn254.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

if [[ ! -x "$SOLC_BIN" ]]; then
  if [[ "$INSTALL_SOLC" != "1" ]] || ! command -v solc-select >/dev/null 2>&1; then
    printf 'error: pinned solc %s is unavailable\n' "$SOLC_VERSION" >&2
    exit 1
  fi
  solc-select install "$SOLC_VERSION"
fi

if [[ -n "${EIGENLAYER_DIR:-}" ]]; then
  EIGENLAYER_REPO="$EIGENLAYER_DIR"
else
  EIGENLAYER_REPO="$OUTDIR/eigenlayer-contracts"
  git init -q "$EIGENLAYER_REPO"
  git -C "$EIGENLAYER_REPO" remote add origin "$EIGENLAYER_REPO_URL"
  git -C "$EIGENLAYER_REPO" fetch --depth 1 origin "$EIGENLAYER_REF"
  git -C "$EIGENLAYER_REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ACTUAL_REF="$(git -C "$EIGENLAYER_REPO" rev-parse HEAD)"
SOURCE="$ROOT/examples/EigenLayerBN254Corpus.sol"
REMAP="eigen/=$EIGENLAYER_REPO/src/contracts/"
COMPARE="$OUTDIR/eigenlayer-bn254.compare.txt"

for object in creation runtime; do
  report="$OUTDIR/$object.lean-backend-check.txt"
  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$SOURCE" \
    --solc "$SOLC_BIN" \
    --yul-ast-solc "$SOLC_BIN" \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --remapping "$REMAP" \
    --contract EigenLayerBN254Corpus \
    --object "$object" \
    --optimized \
    --optimizer-runs 200 \
    --evm-version cancun \
    --format lean-backend-check \
    --output "$report"
  grep -qx 'lean_backend_check=pass' "$report"
  grep -qx 'first_none=none' "$report"
done

"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --forge-evm-version cancun \
  --remapping "$REMAP" \
  --contract EigenLayerBN254Corpus \
  --optimized \
  --optimizer-runs 200 \
  --evm-version cancun \
  --calldata "$("$CAST_BIN" calldata 'generators()')" \
  --calldata "$("$CAST_BIN" calldata 'addGenerator()')" \
  --calldata "$("$CAST_BIN" calldata 'multiplyGenerator(uint256)' 17)" \
  --calldata "$("$CAST_BIN" calldata 'tinyMultiply(uint16)' 13)" \
  --calldata "$("$CAST_BIN" calldata 'pairingIdentity()')" \
  --calldata "$("$CAST_BIN" calldata 'safePairingIdentity(uint256)' 1000000)" \
  --calldata "$("$CAST_BIN" calldata 'hashToPoint(bytes32)' 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)" \
  --calldata "$("$CAST_BIN" calldata 'pointHashes()')" \
  > "$COMPARE"

grep -qx 'contract_call_compare=pass' "$COMPARE"
grep -qx 'calls=8' "$COMPARE"
grep -qx 'bridge_summary_1_backend_compatibility=ready' "$COMPARE"
grep -qx 'bridge_summary_1_unsupported_primitives=none' "$COMPARE"

printf 'eigenlayer_bn254_bridge_smoke=pass\n'
printf 'eigenlayer_bn254_repo_ref=%s\n' "$ACTUAL_REF"
printf 'eigenlayer_bn254_checked_objects=2\n'
printf 'eigenlayer_bn254_compare_calls=8\n'
printf 'eigenlayer_bn254_precompiles=5,6,7,8\n'
