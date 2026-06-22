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

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-uniswap-v4-smoke.XXXXXX")"
UNISWAP_V4_REPO_URL="${UNISWAP_V4_REPO_URL:-https://github.com/Uniswap/v4-core.git}"
UNISWAP_V4_REF="${UNISWAP_V4_REF:-46c6834698c48bc4a463a86d8420f4eb1d7f3b75}"
UNISWAP_V4_SOLC_VERSION="${UNISWAP_V4_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${UNISWAP_V4_DIR:-}" ]]; then
  REPO="$UNISWAP_V4_DIR"
else
  REPO="$OUTDIR/v4-core"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$UNISWAP_V4_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$UNISWAP_V4_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$UNISWAP_V4_SOLC_VERSION"
git -C "$REPO" submodule update --init --depth 1 lib/solmate

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
SWAPMATH_BRIDGE="$OUTDIR/SwapMath.creation.bridge.json"
SWAPMATH_HEX="$OUTDIR/SwapMath.creation.hex"
POOLMANAGER_BRIDGE="$OUTDIR/PoolManager.runtime.bridge.json"
POOLMANAGER_LEAN_CHECK="$OUTDIR/PoolManager.runtime.lean-json-check.txt"
POOLMANAGER_BATCH_CHECK="$OUTDIR/PoolManager.all.lean-json-check.json"
UNISWAP_BRIDGE_DIR="$OUTDIR/bridge-json"
UNISWAP_MANIFEST_CHECK="$OUTDIR/uniswap.manifest.lean-json-check.json"
POOLMANAGER_PACKAGE_DIR="$OUTDIR/poolmanager-package"
POOLMANAGER_PACKAGE_MANIFEST="$POOLMANAGER_PACKAGE_DIR/manifest.json"
SWAPMATH_FALLBACK_SOURCE="$OUTDIR/UniswapV4SwapMathFallback.sol"
SWAPMATH_FALLBACK_COMPARE="$OUTDIR/UniswapV4SwapMathFallback.call-compare.txt"
MATH_FALLBACK_SOURCE="$OUTDIR/UniswapV4MathLibraryFallback.sol"
MATH_FALLBACK_COMPARE="$OUTDIR/UniswapV4MathLibraryFallback.call-compare.txt"
BITMATH_FALLBACK_SOURCE="$OUTDIR/UniswapV4BitMathFallback.sol"
BITMATH_FALLBACK_COMPARE="$OUTDIR/UniswapV4BitMathFallback.call-compare.txt"
BITMATH_RUNTIME_ONLY_COMPARE="$OUTDIR/UniswapV4BitMathFallback.runtime-only.call-compare.txt"
CURRENCY_FALLBACK_SOURCE="$OUTDIR/UniswapV4CurrencyFallback.sol"
CURRENCY_FALLBACK_COMPARE="$OUTDIR/UniswapV4CurrencyFallback.call-compare.txt"
SLOT0_FALLBACK_SOURCE="$OUTDIR/UniswapV4Slot0Fallback.sol"
SLOT0_FALLBACK_COMPARE="$OUTDIR/UniswapV4Slot0Fallback.call-compare.txt"
TICKMATH_FALLBACK_SOURCE="$OUTDIR/UniswapV4TickMathFallback.sol"
TICKMATH_BRIDGE_DIR="$OUTDIR/tickmath-bridge-json"
TICKMATH_CHECK="$OUTDIR/UniswapV4TickMathFallback.runtime.lean-json-check.txt"
TICKMATH_SUMMARY="$OUTDIR/UniswapV4TickMathFallback.bridge-json-summary.json"
SQRT_PRICE_FALLBACK_SOURCE="$OUTDIR/UniswapV4SqrtPriceMathFallback.sol"
SQRT_PRICE_BRIDGE_DIR="$OUTDIR/sqrt-price-bridge-json"
SQRT_PRICE_BRIDGE="$OUTDIR/UniswapV4SqrtPriceMathFallback.runtime.bridge.json"
SQRT_PRICE_SUMMARY="$OUTDIR/UniswapV4SqrtPriceMathFallback.bridge-json-summary.json"
SQRT_PRICE_BACKEND_CHECK="$OUTDIR/UniswapV4SqrtPriceMathFallback.runtime.backend-check.json"
LOCK_FALLBACK_SOURCE="$OUTDIR/UniswapV4LockFallback.sol"
LOCK_BRIDGE_DIR="$OUTDIR/lock-bridge-json"
LOCK_BRIDGE="$OUTDIR/UniswapV4LockFallback.runtime.bridge.json"
LOCK_SUMMARY="$OUTDIR/UniswapV4LockFallback.bridge-json-summary.json"
CURRENCY_DELTA_FALLBACK_SOURCE="$OUTDIR/UniswapV4CurrencyDeltaFallback.sol"
CURRENCY_DELTA_BRIDGE_DIR="$OUTDIR/currency-delta-bridge-json"
CURRENCY_DELTA_BRIDGE="$OUTDIR/UniswapV4CurrencyDeltaFallback.runtime.bridge.json"
CURRENCY_DELTA_SUMMARY="$OUTDIR/UniswapV4CurrencyDeltaFallback.bridge-json-summary.json"
PROTOCOL_FEE_FALLBACK_SOURCE="$OUTDIR/UniswapV4ProtocolFeeFallback.sol"
PROTOCOL_FEE_FALLBACK_COMPARE="$OUTDIR/UniswapV4ProtocolFeeFallback.call-compare.txt"
SAFECAST_FALLBACK_SOURCE="$OUTDIR/UniswapV4SafeCastFallback.sol"
SAFECAST_FALLBACK_COMPARE="$OUTDIR/UniswapV4SafeCastFallback.call-compare.txt"
HOOKS_FALLBACK_SOURCE="$OUTDIR/UniswapV4HooksFallback.sol"
HOOKS_BRIDGE_DIR="$OUTDIR/hooks-bridge-json"
HOOKS_CHECK="$OUTDIR/UniswapV4HooksFallback.runtime.lean-json-check.txt"
HOOKS_SUMMARY="$OUTDIR/UniswapV4HooksFallback.bridge-json-summary.json"
STRICT_BACKEND_DIR="$OUTDIR/strict-backend"

run_strict_backend() {
  local label="$1"
  local input_format="$2"
  local input="$3"
  shift 3
  local output="$STRICT_BACKEND_DIR/$label.lean-backend-check.json"

  mkdir -p "$STRICT_BACKEND_DIR"
  python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$input" \
    --input-format "$input_format" \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --format lean-backend-check \
    --output "$output" \
    "$@"
  python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$output"
  python3 - "$label" "$output" <<'PY'
import json
import sys

label = sys.argv[1]
result = json.load(open(sys.argv[2]))
counts = result.get("counts", {})
if counts.get("checkedObjects", 0) < 1:
    raise SystemExit(f"{label}: strict backend did not inspect an object")
if counts.get("failedObjects") != 0:
    raise SystemExit(f"{label}: strict backend failed: {result!r}")
for checked in result.get("checkedObjects", []):
    if checked.get("status") != "pass" or checked.get("firstNone") != "none":
        raise SystemExit(f"{label}: incomplete checked artifact: {checked!r}")
print(f"{label}_strict_backend_objects={counts['checkedObjects']}")
PY
}

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$REPO/src/libraries/SwapMath.sol" \
  --solc "$SOLC_BIN" \
  --contract SwapMath \
  --format bridge-json \
  --object creation \
  --bridge-json-dir "$UNISWAP_BRIDGE_DIR" \
  --output "$SWAPMATH_BRIDGE"

python3 "$ROOT/scripts/validate_bridge_json.py" "$SWAPMATH_BRIDGE"

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SWAPMATH_BRIDGE" \
  --input-format bridge-json \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format bytecode \
  --object creation \
  --output "$SWAPMATH_HEX"

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$REPO/src/PoolManager.sol" \
  --solc "$SOLC_BIN" \
  --remappings-file "$REPO/remappings.txt" \
  --contract PoolManager \
  --format bridge-json \
  --object runtime \
  --bridge-json-dir "$UNISWAP_BRIDGE_DIR" \
  --output "$POOLMANAGER_BRIDGE"

python3 "$ROOT/scripts/validate_bridge_json.py" "$POOLMANAGER_BRIDGE"

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$POOLMANAGER_BRIDGE" \
  --input-format bridge-json \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$POOLMANAGER_LEAN_CHECK"

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$REPO/src/PoolManager.sol" \
  --solc "$SOLC_BIN" \
  --remappings-file "$REPO/remappings.txt" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --bridge-json-dir "$UNISWAP_BRIDGE_DIR" \
  --output "$POOLMANAGER_BATCH_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$UNISWAP_BRIDGE_DIR/manifest.json"

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$REPO/src/PoolManager.sol" \
  --solc "$SOLC_BIN" \
  --remappings-file "$REPO/remappings.txt" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$POOLMANAGER_PACKAGE_DIR" \
  --output "$POOLMANAGER_PACKAGE_MANIFEST"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$POOLMANAGER_PACKAGE_MANIFEST"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$UNISWAP_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$UNISWAP_MANIFEST_CHECK"

cat > "$SWAPMATH_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {SwapMath} from "v4-core/src/libraries/SwapMath.sol";

contract UniswapV4SwapMathFallback {
    fallback() external {
        uint160 a = SwapMath.getSqrtPriceTarget(true, 100, 120);
        uint160 b = SwapMath.getSqrtPriceTarget(false, 100, 80);
        uint256 result = uint256(a) + uint256(b);
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SWAPMATH_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4SwapMathFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x12345678 \
  --optimized > "$SWAPMATH_FALLBACK_COMPARE"

cat > "$MATH_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {FullMath} from "v4-core/src/libraries/FullMath.sol";
import {LiquidityMath} from "v4-core/src/libraries/LiquidityMath.sol";
import {LPFeeLibrary} from "v4-core/src/libraries/LPFeeLibrary.sol";

contract UniswapV4MathLibraryFallback {
    using LPFeeLibrary for uint24;

    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint256 result;
        if (mode == 0) {
            uint256 exact = FullMath.mulDiv(uint256(1) << 200, 123456789, uint256(1) << 128);
            uint256 rounded = FullMath.mulDivRoundingUp(10, 21, 6);
            result = exact ^ rounded;
        } else if (mode == 1) {
            uint128 plus = LiquidityMath.addDelta(1000, 23);
            uint128 minus = LiquidityMath.addDelta(1000, -123);
            result = (uint256(plus) << 128) | uint256(minus);
        } else if (mode == 2) {
            uint24 feeInput = uint24(LPFeeLibrary.OVERRIDE_FEE_FLAG | 500);
            uint24 fee = feeInput.removeOverrideFlagAndValidate();
            uint24 dynamicFee = LPFeeLibrary.DYNAMIC_FEE_FLAG.getInitialLPFee();
            result = uint256(fee) | (uint256(dynamicFee) << 24);
        } else {
            uint24 badFee = uint24(LPFeeLibrary.OVERRIDE_FEE_FLAG | 1000001);
            badFee.removeOverrideFlagAndValidate();
            result = 0xff;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$MATH_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4MathLibraryFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --optimized > "$MATH_FALLBACK_COMPARE"

cat > "$BITMATH_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {BitMath} from "v4-core/src/libraries/BitMath.sol";

contract UniswapV4BitMathFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint256 x;
        uint256 result;
        if (mode == 0) {
            x = 1;
            result = uint256(BitMath.mostSignificantBit(x))
                | (uint256(BitMath.leastSignificantBit(x)) << 8);
        } else if (mode == 1) {
            x = uint256(1) << 255;
            result = uint256(BitMath.mostSignificantBit(x))
                | (uint256(BitMath.leastSignificantBit(x)) << 8);
        } else if (mode == 2) {
            x = (uint256(1) << 200) | (uint256(1) << 17);
            result = uint256(BitMath.mostSignificantBit(x))
                | (uint256(BitMath.leastSignificantBit(x)) << 8);
        } else {
            BitMath.mostSignificantBit(0);
            result = 0xff;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$BITMATH_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4BitMathFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --optimized > "$BITMATH_FALLBACK_COMPARE"

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$BITMATH_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4BitMathFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --optimized \
  --runtime-only > "$BITMATH_RUNTIME_ONLY_COMPARE"

cat > "$CURRENCY_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Currency, CurrencyLibrary} from "v4-core/src/types/Currency.sol";

contract UniswapV4CurrencyFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint256 result;
        if (mode == 0) {
            Currency masked = CurrencyLibrary.fromId(type(uint256).max);
            Currency small = Currency.wrap(address(0x0000000000000000000000000000000000000123));
            result = masked.toId() ^ (small.toId() << 8);
        } else {
            Currency native = Currency.wrap(address(0));
            Currency other = Currency.wrap(address(1));
            result = native.isAddressZero() ? (other > native ? 2 : 1) : 0;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$CURRENCY_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4CurrencyFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --optimized > "$CURRENCY_FALLBACK_COMPARE"

cat > "$SLOT0_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Slot0} from "v4-core/src/types/Slot0.sol";

contract UniswapV4Slot0Fallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        Slot0 packed = Slot0.wrap(bytes32(0));
        uint256 result;
        if (mode == 0) {
            packed = packed.setSqrtPriceX96(0x1234567890abcdef);
            packed = packed.setTick(-321);
            packed = packed.setProtocolFee(0xabc);
            packed = packed.setLpFee(0xdef123);
            result = uint256(packed.sqrtPriceX96())
                ^ (uint256(uint24(packed.tick())) << 160)
                ^ (uint256(packed.protocolFee()) << 184)
                ^ (uint256(packed.lpFee()) << 208);
        } else if (mode == 1) {
            packed = Slot0.wrap(bytes32(type(uint256).max));
            packed = packed.setSqrtPriceX96(0x123);
            packed = packed.setTick(123456);
            packed = packed.setProtocolFee(777);
            packed = packed.setLpFee(999999);
            result = uint256(packed.sqrtPriceX96())
                | (uint256(uint24(packed.tick())) << 160)
                | (uint256(packed.protocolFee()) << 184)
                | (uint256(packed.lpFee()) << 208);
        } else {
            packed = packed.setTick(-1);
            result = uint256(uint24(packed.tick()));
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SLOT0_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4Slot0Fallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --optimized > "$SLOT0_FALLBACK_COMPARE"

cat > "$TICKMATH_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {TickMath} from "v4-core/src/libraries/TickMath.sol";

contract UniswapV4TickMathFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint256 result;
        if (mode == 0) {
            result = uint256(TickMath.getSqrtPriceAtTick(0));
        } else if (mode == 1) {
            uint160 price = TickMath.getSqrtPriceAtTick(-120);
            int24 tick = TickMath.getTickAtSqrtPrice(price);
            result = uint256(uint24(tick));
        } else if (mode == 2) {
            int24 minTick = TickMath.minUsableTick(60);
            int24 maxTick = TickMath.maxUsableTick(60);
            result = uint256(uint24(minTick)) | (uint256(uint24(maxTick)) << 24);
        } else {
            TickMath.getSqrtPriceAtTick(887273);
            result = 0xff;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$TICKMATH_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UniswapV4TickMathFallback \
  --remapping "v4-core/=$REPO/" \
  --format lean-json-check \
  --object runtime \
  --bridge-json-dir "$TICKMATH_BRIDGE_DIR" \
  --output "$TICKMATH_CHECK" \
  --optimized

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$TICKMATH_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$TICKMATH_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$TICKMATH_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$TICKMATH_SUMMARY"

python3 - "$TICKMATH_SUMMARY" <<'PY'
import json
import sys

summary = json.load(open(sys.argv[1]))
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected TickMath summary schema: {summary.get('schema')!r}")
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(f"unexpected TickMath summary counts: {summary.get('counts')!r}")

objects = summary.get("objects", [])
if len(objects) != 1:
    raise SystemExit(f"unexpected TickMath summary objects: {objects!r}")
runtime = objects[0]
if runtime.get("contract") != "UniswapV4TickMathFallback" or runtime.get("selector") != "runtime":
    raise SystemExit(f"unexpected TickMath runtime summary: {runtime!r}")
compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(f"unexpected TickMath backend compatibility: {compatibility!r}")

primitive_entries = runtime.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required = {
    "signextend",
    "sar",
    "shl",
    "shr",
    "xor",
    "mul",
    "div",
    "sgt",
    "lt",
    "mstore",
    "revert",
}
missing = sorted(required - primitives)
if missing:
    raise SystemExit(f"TickMath summary missing primitives: {missing!r}")

print("tickmath_runtime_summary_primitives=yes")
print("tickmath_runtime_backend_compatibility=ready")
PY

cat > "$SQRT_PRICE_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {SqrtPriceMath} from "v4-core/src/libraries/SqrtPriceMath.sol";

contract UniswapV4SqrtPriceMathFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint160 base = 79228162514264337593543950336;
        uint160 upper = 158456325028528675187087900672;
        uint128 liquidity = 1000000;
        uint256 result;
        if (mode == 0) {
            uint256 down = SqrtPriceMath.getAmount0Delta(base, upper, liquidity, false);
            uint256 up = SqrtPriceMath.getAmount0Delta(base, upper, liquidity, true);
            result = down | (up << 128);
        } else if (mode == 1) {
            uint256 down = SqrtPriceMath.getAmount1Delta(base, upper, liquidity, false);
            uint256 up = SqrtPriceMath.getAmount1Delta(base, upper, liquidity, true);
            result = down | (up << 128);
        } else if (mode == 2) {
            uint160 next0 = SqrtPriceMath.getNextSqrtPriceFromInput(base, liquidity, 12345, true);
            uint160 next1 = SqrtPriceMath.getNextSqrtPriceFromInput(base, liquidity, 67890, false);
            result = uint256(next0) ^ (uint256(next1) << 128);
        } else if (mode == 3) {
            int256 neg0 = SqrtPriceMath.getAmount0Delta(base, upper, int128(1234));
            int256 pos1 = SqrtPriceMath.getAmount1Delta(base, upper, int128(-5678));
            result = uint256(neg0) ^ (uint256(pos1) << 1);
        } else {
            SqrtPriceMath.getNextSqrtPriceFromInput(0, liquidity, 1, true);
            result = 0xff;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SQRT_PRICE_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --contract UniswapV4SqrtPriceMathFallback \
  --remapping "v4-core/=$REPO/" \
  --format bridge-json \
  --object runtime \
  --bridge-json-dir "$SQRT_PRICE_BRIDGE_DIR" \
  --output "$SQRT_PRICE_BRIDGE" \
  --optimized

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SQRT_PRICE_BRIDGE"
python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SQRT_PRICE_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SQRT_PRICE_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$SQRT_PRICE_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SQRT_PRICE_SUMMARY"

python3 - "$SQRT_PRICE_SUMMARY" <<'PY'
import json
import sys

summary = json.load(open(sys.argv[1]))
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected SqrtPriceMath summary schema: {summary.get('schema')!r}")
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(f"unexpected SqrtPriceMath summary counts: {summary.get('counts')!r}")

objects = summary.get("objects", [])
if len(objects) != 1:
    raise SystemExit(f"unexpected SqrtPriceMath summary objects: {objects!r}")
runtime = objects[0]
if runtime.get("contract") != "UniswapV4SqrtPriceMathFallback":
    raise SystemExit(f"unexpected SqrtPriceMath runtime contract: {runtime!r}")
if runtime.get("selector") != "runtime":
    raise SystemExit(f"unexpected SqrtPriceMath runtime selector: {runtime!r}")
compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(f"unexpected SqrtPriceMath backend compatibility: {compatibility!r}")

primitive_entries = runtime.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required = {
    "mulmod",
    "sar",
    "shl",
    "shr",
    "xor",
    "mstore",
    "revert",
}
missing = sorted(required - primitives)
if missing:
    raise SystemExit(f"SqrtPriceMath summary missing primitives: {missing!r}")

print("sqrt_price_runtime_summary_primitives=yes")
print("sqrt_price_runtime_backend_compatibility=ready")
PY

SQRT_PRICE_BACKEND_STATUS="skipped"
SQRT_PRICE_BACKEND_FIRST_NONE="not-run"
if [[ "${RUN_SQRT_PRICE_BACKEND_CHECK:-0}" == "1" ]]; then
  python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$SQRT_PRICE_BRIDGE_DIR/manifest.json" \
    --input-format bridge-json-manifest \
    --lake "$LAKE_BIN" \
    --lake-cwd "$ROOT" \
    --format lean-backend-check \
    --output "$SQRT_PRICE_BACKEND_CHECK"

  python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SQRT_PRICE_BACKEND_CHECK"

  SQRT_PRICE_BACKEND_STATUS="$(
    python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["checkedObjects"][0]["status"])' \
      "$SQRT_PRICE_BACKEND_CHECK"
  )"
  SQRT_PRICE_BACKEND_FIRST_NONE="$(
    python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["checkedObjects"][0]["firstNone"])' \
      "$SQRT_PRICE_BACKEND_CHECK"
  )"
fi

cat > "$LOCK_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Lock} from "v4-core/src/libraries/Lock.sol";

contract UniswapV4LockFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        bool unlocked;
        if (mode == 0) {
            unlocked = Lock.isUnlocked();
        } else if (mode == 1) {
            Lock.unlock();
            unlocked = Lock.isUnlocked();
        } else {
            Lock.lock();
            unlocked = Lock.isUnlocked();
        }
        assembly ("memory-safe") {
            mstore(0, unlocked)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$LOCK_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --contract UniswapV4LockFallback \
  --remapping "v4-core/=$REPO/" \
  --format bridge-json \
  --object runtime \
  --bridge-json-dir "$LOCK_BRIDGE_DIR" \
  --output "$LOCK_BRIDGE" \
  --optimized

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$LOCK_BRIDGE"
python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$LOCK_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$LOCK_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$LOCK_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$LOCK_SUMMARY"

python3 - "$LOCK_SUMMARY" <<'PY'
import json
import sys

summary = json.load(open(sys.argv[1]))
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected Lock summary schema: {summary.get('schema')!r}")
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(f"unexpected Lock summary counts: {summary.get('counts')!r}")

objects = summary.get("objects", [])
if len(objects) != 1:
    raise SystemExit(f"unexpected Lock summary objects: {objects!r}")
runtime = objects[0]
if runtime.get("contract") != "UniswapV4LockFallback":
    raise SystemExit(f"unexpected Lock runtime contract: {runtime!r}")
if runtime.get("selector") != "runtime":
    raise SystemExit(f"unexpected Lock runtime selector: {runtime!r}")

compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(f"unexpected Lock backend compatibility: {compatibility!r}")
if compatibility.get("unsupportedPrimitiveNames") != []:
    raise SystemExit(f"unexpected Lock unsupported primitives: {compatibility!r}")

primitive_entries = runtime.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required = {"tload", "tstore", "mstore", "return"}
missing = sorted(required - primitives)
if missing:
    raise SystemExit(f"Lock summary missing primitives: {missing!r}")

print("lock_runtime_summary_primitives=yes")
print("lock_runtime_backend_compatibility=ready")
PY

cat > "$CURRENCY_DELTA_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {Currency} from "v4-core/src/types/Currency.sol";
import {CurrencyDelta} from "v4-core/src/libraries/CurrencyDelta.sol";

contract UniswapV4CurrencyDeltaFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        Currency currency = Currency.wrap(address(uint160(0xc0de)));
        address target = address(uint160(0xbabe));
        uint256 result;
        if (mode == 0) {
            result = uint256(CurrencyDelta.getDelta(currency, target));
        } else {
            (int256 previous, int256 next) = CurrencyDelta.applyDelta(
                currency,
                target,
                int128(123456)
            );
            result = uint256(previous) ^ (uint256(next) << 128);
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$CURRENCY_DELTA_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --contract UniswapV4CurrencyDeltaFallback \
  --remapping "v4-core/=$REPO/" \
  --format bridge-json \
  --object runtime \
  --bridge-json-dir "$CURRENCY_DELTA_BRIDGE_DIR" \
  --output "$CURRENCY_DELTA_BRIDGE" \
  --optimized

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$CURRENCY_DELTA_BRIDGE"
python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$CURRENCY_DELTA_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$CURRENCY_DELTA_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$CURRENCY_DELTA_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$CURRENCY_DELTA_SUMMARY"

python3 - "$CURRENCY_DELTA_SUMMARY" <<'PY'
import json
import sys

summary = json.load(open(sys.argv[1]))
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(
        f"unexpected CurrencyDelta summary schema: {summary.get('schema')!r}"
    )
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(
        f"unexpected CurrencyDelta summary counts: {summary.get('counts')!r}"
    )

objects = summary.get("objects", [])
if len(objects) != 1:
    raise SystemExit(f"unexpected CurrencyDelta summary objects: {objects!r}")
runtime = objects[0]
if runtime.get("contract") != "UniswapV4CurrencyDeltaFallback":
    raise SystemExit(f"unexpected CurrencyDelta runtime contract: {runtime!r}")
if runtime.get("selector") != "runtime":
    raise SystemExit(f"unexpected CurrencyDelta runtime selector: {runtime!r}")

compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected CurrencyDelta backend compatibility: {compatibility!r}"
    )
if compatibility.get("unsupportedPrimitiveNames") != []:
    raise SystemExit(
        f"unexpected CurrencyDelta unsupported primitives: {compatibility!r}"
    )

primitive_entries = runtime.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required = {"keccak256", "tload", "tstore", "mstore", "return"}
missing = sorted(required - primitives)
if missing:
    raise SystemExit(f"CurrencyDelta summary missing primitives: {missing!r}")

print("currency_delta_runtime_summary_primitives=yes")
print("currency_delta_runtime_backend_compatibility=ready")
PY

cat > "$PROTOCOL_FEE_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {ProtocolFeeLibrary} from "v4-core/src/libraries/ProtocolFeeLibrary.sol";

contract UniswapV4ProtocolFeeFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint24 packed = (uint24(321) << 12) | uint24(123);
        uint256 result;
        if (mode == 0) {
            result = uint256(ProtocolFeeLibrary.getZeroForOneFee(packed))
                | (uint256(ProtocolFeeLibrary.getOneForZeroFee(packed)) << 16);
        } else if (mode == 1) {
            result = ProtocolFeeLibrary.isValidProtocolFee(packed) ? 1 : 0;
        } else if (mode == 2) {
            uint24 invalidPacked = (uint24(1001) << 12) | uint24(1000);
            result = ProtocolFeeLibrary.isValidProtocolFee(invalidPacked) ? 1 : 0;
        } else {
            result = ProtocolFeeLibrary.calculateSwapFee(750, 3000);
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$PROTOCOL_FEE_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4ProtocolFeeFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --optimized > "$PROTOCOL_FEE_FALLBACK_COMPARE"

cat > "$SAFECAST_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {SafeCast} from "v4-core/src/libraries/SafeCast.sol";

contract UniswapV4SafeCastFallback {
    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        uint256 result;
        if (mode == 0) {
            result = SafeCast.toUint160(0x1234567890abcdef);
        } else if (mode == 1) {
            result = SafeCast.toUint128(uint256(type(uint128).max));
        } else if (mode == 2) {
            result = uint256(uint128(SafeCast.toInt128(-123456789)));
        } else if (mode == 3) {
            result = uint256(SafeCast.toInt256((uint256(1) << 255) - 1));
        } else if (mode == 4) {
            result = SafeCast.toUint160(uint256(type(uint160).max) + 1);
        } else if (mode == 5) {
            result = uint256(uint128(SafeCast.toInt128(type(int256).max)));
        } else {
            result = uint256(SafeCast.toInt256(uint256(1) << 255));
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SAFECAST_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapV4SafeCastFallback \
  --remapping "v4-core/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03 \
  --calldata 0x04 \
  --calldata 0x05 \
  --calldata 0x06 \
  --optimized > "$SAFECAST_FALLBACK_COMPARE"

cat > "$HOOKS_FALLBACK_SOURCE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {IHooks} from "v4-core/src/interfaces/IHooks.sol";
import {Hooks} from "v4-core/src/libraries/Hooks.sol";
import {LPFeeLibrary} from "v4-core/src/libraries/LPFeeLibrary.sol";

contract UniswapV4HooksFallback {
    using Hooks for IHooks;

    fallback() external {
        uint8 mode = msg.data.length == 0 ? 0 : uint8(msg.data[0]);
        IHooks hook = IHooks(
            address(
                uint160(
                    Hooks.BEFORE_SWAP_FLAG
                        | Hooks.AFTER_SWAP_FLAG
                        | Hooks.AFTER_SWAP_RETURNS_DELTA_FLAG
                )
            )
        );
        uint256 result;
        if (mode == 0) {
            result = hook.hasPermission(Hooks.BEFORE_SWAP_FLAG) ? 1 : 0;
            result |= hook.hasPermission(Hooks.AFTER_SWAP_FLAG) ? 2 : 0;
            result |= hook.hasPermission(Hooks.AFTER_SWAP_RETURNS_DELTA_FLAG) ? 4 : 0;
            result |= hook.hasPermission(Hooks.BEFORE_INITIALIZE_FLAG) ? 8 : 0;
        } else if (mode == 1) {
            IHooks invalid = IHooks(
                address(uint160(Hooks.AFTER_SWAP_RETURNS_DELTA_FLAG))
            );
            result = hook.isValidHookAddress(500) ? 1 : 0;
            result |= invalid.isValidHookAddress(500) ? 2 : 0;
        } else if (mode == 2) {
            Hooks.Permissions memory permissions = Hooks.Permissions({
                beforeInitialize: false,
                afterInitialize: false,
                beforeAddLiquidity: false,
                afterAddLiquidity: false,
                beforeRemoveLiquidity: false,
                afterRemoveLiquidity: false,
                beforeSwap: true,
                afterSwap: true,
                beforeDonate: false,
                afterDonate: false,
                beforeSwapReturnDelta: false,
                afterSwapReturnDelta: true,
                afterAddLiquidityReturnDelta: false,
                afterRemoveLiquidityReturnDelta: false
            });
            hook.validateHookPermissions(permissions);
            result = 0x1234;
        } else if (mode == 3) {
            IHooks zero = IHooks(address(0));
            result = zero.isValidHookAddress(500) ? 1 : 0;
            result |= zero.isValidHookAddress(LPFeeLibrary.DYNAMIC_FEE_FLAG) ? 2 : 0;
        } else {
            Hooks.Permissions memory badPermissions = Hooks.Permissions({
                beforeInitialize: true,
                afterInitialize: false,
                beforeAddLiquidity: false,
                afterAddLiquidity: false,
                beforeRemoveLiquidity: false,
                afterRemoveLiquidity: false,
                beforeSwap: true,
                afterSwap: true,
                beforeDonate: false,
                afterDonate: false,
                beforeSwapReturnDelta: false,
                afterSwapReturnDelta: true,
                afterAddLiquidityReturnDelta: false,
                afterRemoveLiquidityReturnDelta: false
            });
            hook.validateHookPermissions(badPermissions);
            result = 0xff;
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_V4_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$HOOKS_FALLBACK_SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UniswapV4HooksFallback \
  --remapping "v4-core/=$REPO/" \
  --format lean-json-check \
  --object runtime \
  --bridge-json-dir "$HOOKS_BRIDGE_DIR" \
  --output "$HOOKS_CHECK" \
  --optimized

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$HOOKS_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$HOOKS_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$HOOKS_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$HOOKS_SUMMARY"

python3 - "$HOOKS_SUMMARY" <<'PY'
import json
import sys

summary = json.load(open(sys.argv[1]))
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected Hooks summary schema: {summary.get('schema')!r}")
if summary.get("counts", {}).get("objects") != 1:
    raise SystemExit(f"unexpected Hooks summary counts: {summary.get('counts')!r}")

objects = summary.get("objects", [])
if len(objects) != 1:
    raise SystemExit(f"unexpected Hooks summary objects: {objects!r}")
runtime = objects[0]
if runtime.get("contract") != "UniswapV4HooksFallback":
    raise SystemExit(f"unexpected Hooks runtime contract: {runtime!r}")
if runtime.get("selector") != "runtime":
    raise SystemExit(f"unexpected Hooks runtime selector: {runtime!r}")

primitive_entries = runtime.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required = {"and", "or", "mstore", "revert", "return"}
missing = sorted(required - primitives)
if missing:
    raise SystemExit(f"Hooks summary missing primitives: {missing!r}")

print("hooks_runtime_summary_primitives=yes")
PY

POOL_LINKER_ARGS=()
POOL_LINKER_SYMBOLS=(
  'libraries/BitMath.sol:BitMath'
  'libraries/CurrencyReserves.sol:CurrencyReserves'
  'libraries/CustomRevert.sol:CustomRevert'
  'libraries/FixedPoint128.sol:FixedPoint128'
  'libraries/FixedPoint96.sol:FixedPoint96'
  'libraries/FullMath.sol:FullMath'
  'libraries/Hooks.sol:Hooks'
  'libraries/LiquidityMath.sol:LiquidityMath'
  'libraries/Lock.sol:Lock'
  'libraries/NonzeroDeltaCount.sol:NonzeroDeltaCount'
  'libraries/Pool.sol:Pool'
  'libraries/ProtocolFeeLibrary.sol:ProtocolFeeLibrary'
  'libraries/SqrtPriceMath.sol:SqrtPriceMath'
  'libraries/SwapMath.sol:SwapMath'
  'libraries/TickMath.sol:TickMath'
  'libraries/UnsafeMath.sol:UnsafeMath'
  'types/BalanceDelta.sol:BalanceDeltaLibrary'
  'types/BeforeSwapDelta.sol:BeforeSwapDeltaLibrary'
  'types/Currency.sol:CurrencyLibrary'
)
for i in "${!POOL_LINKER_SYMBOLS[@]}"; do
  POOL_LINKER_ARGS+=(--linker-symbol "${POOL_LINKER_SYMBOLS[$i]}=$((i + 1))")
done

run_strict_backend swapmath_creation bridge-json-manifest \
  "$UNISWAP_BRIDGE_DIR/manifest.json" \
  --contract SwapMath --object creation
run_strict_backend tickmath_runtime bridge-json-manifest \
  "$TICKMATH_BRIDGE_DIR/manifest.json" \
  --contract UniswapV4TickMathFallback --object runtime
run_strict_backend sqrt_price_runtime bridge-json-manifest \
  "$SQRT_PRICE_BRIDGE_DIR/manifest.json" \
  --contract UniswapV4SqrtPriceMathFallback --object runtime
run_strict_backend lock_runtime bridge-json-manifest \
  "$LOCK_BRIDGE_DIR/manifest.json" \
  --contract UniswapV4LockFallback --object runtime
run_strict_backend currency_delta_runtime bridge-json-manifest \
  "$CURRENCY_DELTA_BRIDGE_DIR/manifest.json" \
  --contract UniswapV4CurrencyDeltaFallback --object runtime
run_strict_backend hooks_runtime bridge-json-manifest \
  "$HOOKS_BRIDGE_DIR/manifest.json" \
  --contract UniswapV4HooksFallback --object runtime
run_strict_backend poolmanager_creation bridge-json-manifest \
  "$POOLMANAGER_PACKAGE_MANIFEST" \
  --contract PoolManager --object creation "${POOL_LINKER_ARGS[@]}"

SQRT_PRICE_BACKEND_STATUS="pass"
SQRT_PRICE_BACKEND_FIRST_NONE="none"

SWAPMATH_HEX_BYTES="$(wc -c < "$SWAPMATH_HEX" | tr -d ' ')"
POOLMANAGER_BRIDGE_BYTES="$(wc -c < "$POOLMANAGER_BRIDGE" | tr -d ' ')"
POOLMANAGER_LEAN_DECODE="$(
  sed -n 's/^lean_bridge_json_decode=//p' "$POOLMANAGER_LEAN_CHECK"
)"
POOLMANAGER_BATCH_OBJECTS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["checkedObjects"])' \
    "$POOLMANAGER_BATCH_CHECK"
)"
UNISWAP_MANIFEST_OBJECTS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["checkedObjects"])' \
    "$UNISWAP_MANIFEST_CHECK"
)"
POOLMANAGER_PACKAGE_ENTRIES="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["entries"])' \
    "$POOLMANAGER_PACKAGE_MANIFEST"
)"
POOLMANAGER_PACKAGE_SKIPPED="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["skippedContracts"])' \
    "$POOLMANAGER_PACKAGE_MANIFEST"
)"
SWAPMATH_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$SWAPMATH_FALLBACK_COMPARE")"
MATH_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$MATH_FALLBACK_COMPARE")"
BITMATH_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$BITMATH_FALLBACK_COMPARE")"
BITMATH_RUNTIME_ONLY_CALLS="$(sed -n 's/^calls=//p' "$BITMATH_RUNTIME_ONLY_COMPARE")"
CURRENCY_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$CURRENCY_FALLBACK_COMPARE")"
SLOT0_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$SLOT0_FALLBACK_COMPARE")"
TICKMATH_LEAN_DECODE="$(sed -n 's/^lean_bridge_json_decode=//p' "$TICKMATH_CHECK")"
TICKMATH_SUMMARY_CALLS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["calls"])' \
    "$TICKMATH_SUMMARY"
)"
SQRT_PRICE_SUMMARY_CALLS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["calls"])' \
    "$SQRT_PRICE_SUMMARY"
)"
LOCK_SUMMARY_CALLS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["calls"])' \
    "$LOCK_SUMMARY"
)"
CURRENCY_DELTA_SUMMARY_CALLS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["calls"])' \
    "$CURRENCY_DELTA_SUMMARY"
)"
PROTOCOL_FEE_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$PROTOCOL_FEE_FALLBACK_COMPARE")"
SAFECAST_FALLBACK_CALLS="$(sed -n 's/^calls=//p' "$SAFECAST_FALLBACK_COMPARE")"
HOOKS_LEAN_DECODE="$(sed -n 's/^lean_bridge_json_decode=//p' "$HOOKS_CHECK")"
HOOKS_SUMMARY_CALLS="$(
  python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["counts"]["calls"])' \
    "$HOOKS_SUMMARY"
)"

printf 'uniswap_v4_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'swapmath_creation_hex_bytes=%s\n' "$SWAPMATH_HEX_BYTES"
printf 'poolmanager_runtime_bridge_json_bytes=%s\n' "$POOLMANAGER_BRIDGE_BYTES"
printf 'poolmanager_lean_decode=%s\n' "$POOLMANAGER_LEAN_DECODE"
printf 'poolmanager_batch_decode_objects=%s\n' "$POOLMANAGER_BATCH_OBJECTS"
printf 'poolmanager_package_bridge_objects=%s\n' "$POOLMANAGER_PACKAGE_ENTRIES"
printf 'poolmanager_package_skipped_contracts=%s\n' "$POOLMANAGER_PACKAGE_SKIPPED"
printf 'manifest_lean_decode_objects=%s\n' "$UNISWAP_MANIFEST_OBJECTS"
printf 'swapmath_fallback_compare_calls=%s\n' "$SWAPMATH_FALLBACK_CALLS"
printf 'math_libraries_fallback_compare_calls=%s\n' "$MATH_FALLBACK_CALLS"
printf 'bitmath_fallback_compare_calls=%s\n' "$BITMATH_FALLBACK_CALLS"
printf 'bitmath_runtime_only_compare_calls=%s\n' "$BITMATH_RUNTIME_ONLY_CALLS"
printf 'currency_fallback_compare_calls=%s\n' "$CURRENCY_FALLBACK_CALLS"
printf 'slot0_fallback_compare_calls=%s\n' "$SLOT0_FALLBACK_CALLS"
printf 'tickmath_runtime_lean_decode=%s\n' "$TICKMATH_LEAN_DECODE"
printf 'tickmath_runtime_summary_calls=%s\n' "$TICKMATH_SUMMARY_CALLS"
printf 'sqrt_price_runtime_summary_calls=%s\n' "$SQRT_PRICE_SUMMARY_CALLS"
printf 'sqrt_price_backend_check_status=%s\n' "$SQRT_PRICE_BACKEND_STATUS"
printf 'sqrt_price_backend_check_first_none=%s\n' "$SQRT_PRICE_BACKEND_FIRST_NONE"
printf 'lock_runtime_summary_calls=%s\n' "$LOCK_SUMMARY_CALLS"
printf 'currency_delta_runtime_summary_calls=%s\n' "$CURRENCY_DELTA_SUMMARY_CALLS"
printf 'protocol_fee_fallback_compare_calls=%s\n' "$PROTOCOL_FEE_FALLBACK_CALLS"
printf 'safecast_fallback_compare_calls=%s\n' "$SAFECAST_FALLBACK_CALLS"
printf 'hooks_runtime_lean_decode=%s\n' "$HOOKS_LEAN_DECODE"
printf 'hooks_runtime_summary_calls=%s\n' "$HOOKS_SUMMARY_CALLS"
