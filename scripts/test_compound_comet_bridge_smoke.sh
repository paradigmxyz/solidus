#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi
FORGE_BIN="${FORGE:-forge}"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-compound-comet-smoke.XXXXXX")"
COMPOUND_COMET_REPO_URL="${COMPOUND_COMET_REPO_URL:-https://github.com/compound-finance/comet.git}"
COMPOUND_COMET_REF="${COMPOUND_COMET_REF:-d5a30b0aaeff7755f1431e87f818990902237b03}"
COMPOUND_COMET_SOLC_VERSION="${COMPOUND_COMET_SOLC_VERSION:-0.8.26}"
COMPOUND_COMET_FORGE_EVM_VERSION="${COMPOUND_COMET_FORGE_EVM_VERSION:-cancun}"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

ensure_solc_version() {
  local version="$1"
  local output
  output="$(SOLC_VERSION="$version" "$SOLC_BIN" --version 2>/dev/null || true)"
  if [[ "$output" == *"Version: $version"* ]]; then
    return
  fi
  if [[ "$INSTALL_SOLC" == "1" ]] && command -v solc-select >/dev/null 2>&1; then
    solc-select install "$version"
  fi
  output="$(SOLC_VERSION="$version" "$SOLC_BIN" --version 2>&1 || true)"
  if [[ "$output" != *"Version: $version"* ]]; then
    printf 'error: %s cannot provide solc %s\n%s\n' "$SOLC_BIN" "$version" "$output" >&2
    return 1
  fi
}

if [[ -n "${COMPOUND_COMET_DIR:-}" ]]; then
  REPO="$COMPOUND_COMET_DIR"
else
  REPO="$OUTDIR/comet"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$COMPOUND_COMET_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$COMPOUND_COMET_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$COMPOUND_COMET_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
RELAXED_REPO="$OUTDIR/comet-relaxed/contracts"
FIXTURE="$OUTDIR/CompoundCometMathFallback.sol"
BRIDGE_DIR="$OUTDIR/bridge-json"
DECODE_CHECK="$OUTDIR/CompoundCometMathFallback.lean-json-check.json"
SUMMARY="$OUTDIR/CompoundCometMathFallback.bridge-json-summary.json"
BACKEND_CHECK="$OUTDIR/CompoundCometMathFallback.lean-backend-check.json"
COMPARE="$OUTDIR/CompoundCometMathFallback.call-compare.txt"

mkdir -p "$RELAXED_REPO"
"$PYTHON_BIN" - "$REPO/contracts/CometMath.sol" "$RELAXED_REPO/CometMath.sol" <<'PY'
import pathlib
import sys

source = pathlib.Path(sys.argv[1])
target = pathlib.Path(sys.argv[2])
content = source.read_text()
needle = "pragma solidity 0.8.15;"
if needle not in content:
    raise SystemExit(f"expected exact CometMath pragma {needle!r}")
target.write_text(content.replace(needle, "pragma solidity >=0.8.15;", 1))
PY

cat > "$FIXTURE" <<'SOL'
// SPDX-License-Identifier: BUSL-1.1
pragma solidity >=0.8.15;

import {CometMath} from "comet/CometMath.sol";

contract CompoundCometMathFallback is CometMath {
    function callSafe64(uint256 n) external pure returns (uint64) {
        return safe64(n);
    }

    function callSafe104(uint256 n) external pure returns (uint104) {
        return safe104(n);
    }

    function callSafe128(uint256 n) external pure returns (uint128) {
        return safe128(n);
    }

    function callSigned104(uint104 n) external pure returns (int104) {
        return signed104(n);
    }

    function callSigned256(uint256 n) external pure returns (int256) {
        return signed256(n);
    }

    function callUnsigned104(int104 n) external pure returns (uint104) {
        return unsigned104(n);
    }

    function callUnsigned256(int256 n) external pure returns (uint256) {
        return unsigned256(n);
    }

    function callToUInt8(bool x) external pure returns (uint8) {
        return toUInt8(x);
    }

    function callToBool(uint8 x) external pure returns (bool) {
        return toBool(x);
    }
}
SOL

COMPARE_CALLDATA=()
add_abi_call() {
  local selector="$1"
  local value="$2"
  local encoded
  encoded="$("$PYTHON_BIN" - "$selector" "$value" <<'PY'
import sys

selector = sys.argv[1].removeprefix("0x").lower()
value = int(sys.argv[2], 0)
if len(selector) != 8 or any(ch not in "0123456789abcdef" for ch in selector):
    raise SystemExit("selector must be four bytes of hex")
encoded_value = value % (1 << 256)
print(f"0x{selector}{encoded_value:064x}")
PY
)"
  COMPARE_CALLDATA+=(--calldata "$encoded")
}

add_abi_call 0x51bcbc25 42
add_abi_call 0x51bcbc25 0x10000000000000000
add_abi_call 0x211fd09f 123456789
add_abi_call 0x211fd09f 0x100000000000000000000000000
add_abi_call 0xdb713ee3 170141183460469231731687303715884105727
add_abi_call 0xdb713ee3 0x100000000000000000000000000000000
add_abi_call 0x3fa9c9c6 5000
add_abi_call 0x3fa9c9c6 0x80000000000000000000000000
add_abi_call 0x84fed6d9 123456789
add_abi_call 0x84fed6d9 0x8000000000000000000000000000000000000000000000000000000000000000
add_abi_call 0x5b53d133 7
add_abi_call 0x5b53d133 -1
add_abi_call 0x0ad7312c 9
add_abi_call 0x0ad7312c -1
add_abi_call 0xf61bd00f 1
add_abi_call 0x37204cc1 0

SOLC_VERSION="$COMPOUND_COMET_SOLC_VERSION" "$PYTHON_BIN" \
  "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --remapping "comet/=$RELAXED_REPO/" \
  --contract CompoundCometMathFallback \
  --optimized \
  --format lean-json-check \
  --bridge-json-dir "$BRIDGE_DIR" \
  --output "$DECODE_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$BRIDGE_DIR/manifest.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$BACKEND_CHECK"

SOLC_VERSION="$COMPOUND_COMET_SOLC_VERSION" "$PYTHON_BIN" \
  "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --remapping "comet/=$RELAXED_REPO/" \
  --contract CompoundCometMathFallback \
  --optimized \
  --forge-evm-version "$COMPOUND_COMET_FORGE_EVM_VERSION" \
  "${COMPARE_CALLDATA[@]}" > "$COMPARE"

printf 'compound_comet_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'source_pragma_relaxed=1\n'
printf 'solc_version=%s\n' "$COMPOUND_COMET_SOLC_VERSION"
printf 'forge_evm_version=%s\n' "$COMPOUND_COMET_FORGE_EVM_VERSION"
printf 'math_fallback_compare_calls=%s\n' "$(
  sed -n 's/^calls=//p' "$COMPARE"
)"
"$PYTHON_BIN" - "$DECODE_CHECK" "$SUMMARY" "$BACKEND_CHECK" "$COMPARE" <<'PY'
import json
import sys

decode = open(sys.argv[1]).read()
summary = json.load(open(sys.argv[2]))
backend = json.load(open(sys.argv[3]))
compare_lines = open(sys.argv[4]).read().splitlines()

if "lean_bridge_json_decode=pass" not in decode:
    raise SystemExit("Compound Comet Lean decode did not report pass")
if "items=1" not in decode:
    raise SystemExit("Compound Comet Lean decode did not report exactly one item")

if summary["counts"]["objects"] != 1:
    raise SystemExit(
        f"expected 1 Compound Comet summary object, got "
        f"{summary['counts']['objects']}"
    )
compatibility = summary.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(f"unexpected Compound Comet compatibility: {compatibility!r}")
for key in ["unsupportedPrimitiveNames", "dialectBuiltinNames"]:
    if compatibility.get(key):
        raise SystemExit(f"Compound Comet summary unexpectedly reports {key}")
object_builtins = compatibility.get("objectBuiltinNames", [])
if object_builtins not in ([], ["memoryguard"]):
    raise SystemExit(
        f"Compound Comet summary reports unexpected object builtins: "
        f"{object_builtins!r}"
    )

if backend["counts"]["checkedObjects"] != 1:
    raise SystemExit(
        f"expected 1 Compound Comet backend object, got "
        f"{backend['counts']['checkedObjects']}"
    )
if backend["counts"]["failedObjects"] != 0:
    raise SystemExit(f"Compound Comet backend check failed: {backend!r}")

if "contract_call_compare=pass" not in compare_lines:
    raise SystemExit("Compound Comet Forge bytecode comparison did not pass")
if "calls=16" not in compare_lines:
    raise SystemExit("Compound Comet Forge comparison did not run 16 calls")
PY
