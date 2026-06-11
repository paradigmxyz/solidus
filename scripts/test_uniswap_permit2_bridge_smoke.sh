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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-uniswap-permit2-smoke.XXXXXX")"
UNISWAP_PERMIT2_REPO_URL="${UNISWAP_PERMIT2_REPO_URL:-https://github.com/Uniswap/permit2.git}"
UNISWAP_PERMIT2_REF="${UNISWAP_PERMIT2_REF:-cc56ad0f3439c502c246fc5cfcc3db92bb8b7219}"
UNISWAP_PERMIT2_SOLC_VERSION="${UNISWAP_PERMIT2_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${UNISWAP_PERMIT2_DIR:-}" ]]; then
  REPO="$UNISWAP_PERMIT2_DIR"
else
  REPO="$OUTDIR/permit2"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$UNISWAP_PERMIT2_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$UNISWAP_PERMIT2_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$UNISWAP_PERMIT2_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
SAFECAST_FIXTURE="$OUTDIR/UniswapPermit2SafeCastFallback.sol"
SAFECAST_COMPARE="$OUTDIR/UniswapPermit2SafeCastFallback.call-compare.txt"
NONCE_BITMAP_FIXTURE="$OUTDIR/UniswapPermit2NonceBitmapFallback.sol"
NONCE_BITMAP_COMPARE="$OUTDIR/UniswapPermit2NonceBitmapFallback.call-compare.txt"
HASH_FIXTURE="$OUTDIR/UniswapPermit2HashFallback.sol"
HASH_BRIDGE_DIR="$OUTDIR/permit2-hash-bridge-json"
HASH_BATCH_CHECK="$OUTDIR/UniswapPermit2HashFallback.lean-json-check.json"
HASH_MANIFEST_CHECK="$OUTDIR/UniswapPermit2HashFallback.manifest.lean-json-check.json"
HASH_SUMMARY="$OUTDIR/UniswapPermit2HashFallback.bridge-json-summary.json"
HASH_BACKEND_CHECK="$OUTDIR/UniswapPermit2HashFallback.lean-backend-check.json"
SIGNATURE_FIXTURE="$OUTDIR/UniswapPermit2SignatureVerificationFallback.sol"
SIGNATURE_BRIDGE_DIR="$OUTDIR/permit2-signature-bridge-json"
SIGNATURE_CHECK="$OUTDIR/UniswapPermit2SignatureVerificationFallback.lean-json-check.json"
SIGNATURE_SUMMARY="$OUTDIR/UniswapPermit2SignatureVerificationFallback.bridge-json-summary.json"
SIGNATURE_BACKEND_CHECK="$OUTDIR/UniswapPermit2SignatureVerificationFallback.lean-backend-check.json"
SIGNATURE_COMPARE="$OUTDIR/UniswapPermit2SignatureVerificationFallback.call-compare.txt"

cat > "$SAFECAST_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.17;

import {SafeCast160} from "permit2/libraries/SafeCast160.sol";

contract UniswapPermit2SafeCastFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        if (mode == 1) {
            uint256 result = SafeCast160.toUint160(type(uint160).max);
            assembly ("memory-safe") {
                mstore(0, result)
                return(0, 32)
            }
        } else if (mode == 2) {
            SafeCast160.toUint160(uint256(type(uint160).max) + 1);
        }
        uint256 result = SafeCast160.toUint160(0x1234567890abcdef);
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_PERMIT2_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SAFECAST_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapPermit2SafeCastFallback \
  --remapping "permit2/=$REPO/src/" \
  --linker-symbol "permit2/libraries/SafeCast160.sol:SafeCast160=0x1111111111111111111111111111111111111111" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --optimized > "$SAFECAST_COMPARE"

cat > "$NONCE_BITMAP_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.17;

error InvalidNonce();

contract UniswapPermit2NonceBitmapFallback {
    event UnorderedNonceInvalidation(address indexed owner, uint256 word, uint256 mask);

    mapping(address => mapping(uint256 => uint256)) public nonceBitmap;

    function bitmapPositions(uint256 nonce)
        private
        pure
        returns (uint256 wordPos, uint256 bitPos)
    {
        wordPos = uint248(nonce >> 8);
        bitPos = uint8(nonce);
    }

    function _useUnorderedNonce(address from, uint256 nonce) internal {
        (uint256 wordPos, uint256 bitPos) = bitmapPositions(nonce);
        uint256 bit = 1 << bitPos;
        uint256 flipped = nonceBitmap[from][wordPos] ^= bit;

        if (flipped & bit == 0) revert InvalidNonce();
    }

    function _invalidate(address owner, uint256 wordPos, uint256 mask) internal {
        nonceBitmap[owner][wordPos] |= mask;
        emit UnorderedNonceInvalidation(owner, wordPos, mask);
    }

    fallback() external {
        uint8 mode;
        uint256 nonce;
        uint256 mask;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
            nonce := calldataload(1)
            mask := calldataload(33)
        }
        address owner = address(0x000000000000000000000000000000000000bEEF);
        if (mode == 1) {
            _useUnorderedNonce(owner, nonce);
        } else if (mode == 2) {
            _useUnorderedNonce(owner, nonce);
            _useUnorderedNonce(owner, nonce);
        } else if (mode == 3) {
            (uint256 wordPos,) = bitmapPositions(nonce);
            _invalidate(owner, wordPos, mask);
        }
        (uint256 selectedWord,) = bitmapPositions(nonce);
        uint256 result = nonceBitmap[owner][selectedWord];
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

nonce_word() {
  printf '%064x' "$1"
}

NONCE_BITMAP_USE_10="0x01$(nonce_word 10)"
NONCE_BITMAP_USE_16="0x01$(nonce_word 16)"
NONCE_BITMAP_REUSE_10="0x02$(nonce_word 10)"
NONCE_BITMAP_INVALIDATE_WORD_1="0x03$(nonce_word 256)$(nonce_word 3)"
NONCE_BITMAP_USE_INVALIDATED_257="0x01$(nonce_word 257)"

SOLC_VERSION="$UNISWAP_PERMIT2_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$NONCE_BITMAP_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapPermit2NonceBitmapFallback \
  --remapping "permit2/=$REPO/src/" \
  --calldata "$NONCE_BITMAP_USE_10" \
  --calldata "$NONCE_BITMAP_USE_16" \
  --calldata "$NONCE_BITMAP_REUSE_10" \
  --calldata "$NONCE_BITMAP_INVALIDATE_WORD_1" \
  --calldata "$NONCE_BITMAP_USE_INVALIDATED_257" \
  --optimized > "$NONCE_BITMAP_COMPARE"

cat > "$HASH_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.17;

import {IAllowanceTransfer} from "permit2/interfaces/IAllowanceTransfer.sol";
import {ISignatureTransfer} from "permit2/interfaces/ISignatureTransfer.sol";
import {PermitHash} from "permit2/libraries/PermitHash.sol";

contract UniswapPermit2HashFallback {
    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }
        bytes32 result;
        if (mode == 1) {
            IAllowanceTransfer.PermitDetails memory details = IAllowanceTransfer.PermitDetails({
                token: address(0x0000000000000000000000000000000000001234),
                amount: 123,
                expiration: 456,
                nonce: 789
            });
            IAllowanceTransfer.PermitSingle memory permit = IAllowanceTransfer.PermitSingle({
                details: details,
                spender: address(0x000000000000000000000000000000000000bEEF),
                sigDeadline: 987
            });
            result = PermitHash.hash(permit);
        } else if (mode == 2) {
            IAllowanceTransfer.PermitDetails[] memory details =
                new IAllowanceTransfer.PermitDetails[](2);
            details[0] = IAllowanceTransfer.PermitDetails({
                token: address(0x0000000000000000000000000000000000000001),
                amount: 11,
                expiration: 22,
                nonce: 33
            });
            details[1] = IAllowanceTransfer.PermitDetails({
                token: address(0x0000000000000000000000000000000000000002),
                amount: 44,
                expiration: 55,
                nonce: 66
            });
            IAllowanceTransfer.PermitBatch memory permit = IAllowanceTransfer.PermitBatch({
                details: details,
                spender: address(0x000000000000000000000000000000000000c0Fe),
                sigDeadline: 777
            });
            result = PermitHash.hash(permit);
        } else {
            ISignatureTransfer.TokenPermissions memory permitted =
                ISignatureTransfer.TokenPermissions({
                    token: address(0x000000000000000000000000000000000000dEaD),
                    amount: 12345
                });
            ISignatureTransfer.PermitTransferFrom memory permit =
                ISignatureTransfer.PermitTransferFrom({
                    permitted: permitted,
                    nonce: 11,
                    deadline: 22
                });
            result = PermitHash.hash(permit);
        }
        assembly ("memory-safe") {
            mstore(0, result)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_PERMIT2_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$HASH_FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "permit2/=$REPO/src/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --bridge-json-dir "$HASH_BRIDGE_DIR" \
  --optimized \
  --output "$HASH_BATCH_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$HASH_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$HASH_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$HASH_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$HASH_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$HASH_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$HASH_MANIFEST_CHECK"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$HASH_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$HASH_BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$HASH_BACKEND_CHECK"

cat > "$SIGNATURE_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.17;

import {SignatureVerification} from "permit2/libraries/SignatureVerification.sol";

contract UniswapPermit2SignatureVerificationFallback {
    fallback() external {
        bytes32 hash = keccak256("permit2-signature-smoke");
        address claimedSigner = address(0x000000000000000000000000000000000000bEEF);
        bytes calldata signature = msg.data[1:];
        SignatureVerification.verify(signature, hash, claimedSigner);
        assembly ("memory-safe") {
            mstore(0, 1)
            return(0, 32)
        }
    }
}
SOL

SOLC_VERSION="$UNISWAP_PERMIT2_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SIGNATURE_FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "permit2/=$REPO/src/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --all-contracts \
  --bridge-json-dir "$SIGNATURE_BRIDGE_DIR" \
  --optimized \
  --output "$SIGNATURE_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SIGNATURE_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SIGNATURE_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$SIGNATURE_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SIGNATURE_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SIGNATURE_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$SIGNATURE_BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SIGNATURE_BACKEND_CHECK"

SOLC_VERSION="$UNISWAP_PERMIT2_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SIGNATURE_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract UniswapPermit2SignatureVerificationFallback \
  --remapping "permit2/=$REPO/src/" \
  --optimized \
  --runtime-only \
  --calldata 0x00 \
  --calldata 0x010203 \
  --calldata 0x02ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff \
  > "$SIGNATURE_COMPARE"

python3 - "$HASH_BATCH_CHECK" "$HASH_MANIFEST_CHECK" "$HASH_SUMMARY" \
  "$HASH_BACKEND_CHECK" "$SIGNATURE_CHECK" "$SIGNATURE_SUMMARY" \
  "$SIGNATURE_BACKEND_CHECK" <<'PY'
import json
import sys

batch = json.load(open(sys.argv[1]))
manifest_replay = json.load(open(sys.argv[2]))
summary = json.load(open(sys.argv[3]))
hash_backend_check = json.load(open(sys.argv[4]))
signature_check = json.load(open(sys.argv[5]))
signature_summary = json.load(open(sys.argv[6]))
signature_backend_check = json.load(open(sys.argv[7]))

def backend_status(report, expected_count, label, contract):
    counts = report.get("counts", {})
    if (
        counts.get("checkedObjects") != expected_count
        or counts.get("checkedContracts") != 1
        or counts.get("skippedContracts") != 0
    ):
        raise SystemExit(f"unexpected {label} backend-check counts: {counts!r}")

    statuses = {}
    for item in report.get("checkedObjects", []):
        key = (item.get("contract"), item.get("selector"))
        status = item.get("status")
        first_none = item.get("firstNone")
        statuses[key] = (status, first_none)
        if item.get("contract") != contract:
            raise SystemExit(f"unexpected {label} backend contract: {item!r}")
        if status not in {"pass", "fail"}:
            raise SystemExit(f"unexpected {label} backend status: {item!r}")
        if status == "pass" and first_none != "none":
            raise SystemExit(f"{label} backend pass mismatch: {item!r}")
        if status == "fail" and first_none in {"", None, "none"}:
            raise SystemExit(f"{label} backend failure missing firstNone: {item!r}")

    runtime = statuses.get((contract, "runtime"))
    if runtime is None:
        raise SystemExit(f"missing {label} runtime backend check: {statuses!r}")
    return counts, runtime

def runtime_backend_object(report, contract):
    for item in report.get("checkedObjects", []):
        if item.get("contract") == contract and item.get("selector") == "runtime":
            return item
    raise SystemExit(f"missing runtime backend object for {contract}")

def has_deep_assignment_target(item, name, minimum=17):
    for entry in item.get("localsTargets", []):
        if entry.get("name") != name:
            continue
        try:
            access_depth = int(entry.get("accessDepth"))
        except (TypeError, ValueError):
            continue
        if access_depth >= minimum:
            return True
    return False

batch_count = batch["counts"]["checkedObjects"]
replay_count = manifest_replay["counts"]["checkedObjects"]
summary_count = summary["counts"]["objects"]
if batch_count < 2:
    raise SystemExit(f"expected at least 2 PermitHash decoded objects, got {batch_count}")
if replay_count != batch_count:
    raise SystemExit(
        f"manifest replay decoded {replay_count} objects, expected {batch_count}"
    )
if summary_count != batch_count:
    raise SystemExit(
        f"bridge summary listed {summary_count} objects, expected {batch_count}"
    )

compatibility = summary.get("backendCompatibility", {})
if compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(f"unexpected Permit2 compatibility: {compatibility!r}")

primitives = set()
for item in summary.get("objects", []):
    for entry in item.get("calls", {}).get("primitive", {}).get("names", []):
        if isinstance(entry, dict) and isinstance(entry.get("name"), str):
            primitives.add(entry["name"])
missing = sorted({"keccak256", "mstore", "return"} - primitives)
if missing:
    raise SystemExit(f"PermitHash summary missing primitives: {missing!r}")

hash_backend_counts, hash_runtime_backend = backend_status(
    hash_backend_check,
    batch_count,
    "PermitHash",
    "UniswapPermit2HashFallback",
)
hash_runtime_object = runtime_backend_object(
    hash_backend_check,
    "UniswapPermit2HashFallback",
)
if hash_runtime_backend[0] == "fail":
    if hash_runtime_backend[1] != "locals_to_expressions":
        raise SystemExit(
            f"unexpected PermitHash runtime backend blocker: {hash_runtime_backend!r}"
        )
    if not has_deep_assignment_target(hash_runtime_object, "var_result"):
        raise SystemExit(
            "PermitHash locals_to_expressions blocker did not report deep "
            f"assignment target var_result: {hash_runtime_object!r}"
        )

signature_count = signature_check["counts"]["checkedObjects"]
signature_summary_count = signature_summary["counts"]["objects"]
if signature_count < 2:
    raise SystemExit(
        f"expected at least 2 SignatureVerification decoded objects, got {signature_count}"
    )
if signature_summary_count != signature_count:
    raise SystemExit(
        "SignatureVerification summary listed "
        f"{signature_summary_count} objects, expected {signature_count}"
    )

signature_primitives = set()
for item in signature_summary.get("objects", []):
    for entry in item.get("calls", {}).get("primitive", {}).get("names", []):
        if isinstance(entry, dict) and isinstance(entry.get("name"), str):
            signature_primitives.add(entry["name"])
missing_signature = sorted(
    {"calldataload", "calldatasize", "staticcall"} - signature_primitives
)
if missing_signature:
    raise SystemExit(
        f"SignatureVerification summary missing primitives: {missing_signature!r}"
    )

signature_compatibility = signature_summary.get("backendCompatibility", {})
if signature_compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(
        f"unexpected SignatureVerification compatibility: {signature_compatibility!r}"
    )

signature_backend_counts, signature_runtime_backend = backend_status(
    signature_backend_check,
    signature_count,
    "SignatureVerification",
    "UniswapPermit2SignatureVerificationFallback",
)
if (
    signature_runtime_backend[0] == "fail"
    and signature_runtime_backend[1] not in {
        "lower_code_unchecked",
        "solc_validation",
    }
):
    raise SystemExit(
        "unexpected SignatureVerification runtime backend blocker: "
        f"{signature_runtime_backend!r}"
    )

print(f"permit2_hash_decode_objects={batch_count}")
print(f"permit2_hash_summary_objects={summary_count}")
print(f"permit2_hash_backend_compatibility={compatibility.get('status')}")
print(f"permit2_hash_backend_check_objects={hash_backend_counts['checkedObjects']}")
print(f"permit2_hash_backend_check_passed={hash_backend_counts['passedObjects']}")
print(f"permit2_hash_backend_check_failed={hash_backend_counts['failedObjects']}")
print(f"permit2_hash_runtime_backend_check={hash_runtime_backend[0]}")
print(f"permit2_hash_runtime_backend_first_none={hash_runtime_backend[1]}")
print("permit2_hash_summary_primitives=yes")
print(f"permit2_signature_decode_objects={signature_count}")
print(f"permit2_signature_summary_objects={signature_summary_count}")
print(
    "permit2_signature_backend_compatibility="
    f"{signature_compatibility.get('status')}"
)
print(
    "permit2_signature_backend_check_objects="
    f"{signature_backend_counts['checkedObjects']}"
)
print(
    "permit2_signature_backend_check_passed="
    f"{signature_backend_counts['passedObjects']}"
)
print(
    "permit2_signature_backend_check_failed="
    f"{signature_backend_counts['failedObjects']}"
)
print(
    "permit2_signature_runtime_backend_check="
    f"{signature_runtime_backend[0]}"
)
print(
    "permit2_signature_runtime_backend_first_none="
    f"{signature_runtime_backend[1]}"
)
print("permit2_signature_summary_primitives=yes")
PY

printf 'uniswap_permit2_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
printf 'permit2_safecast_compare_calls=%s\n' "$(
  sed -n 's/^calls=//p' "$SAFECAST_COMPARE"
)"
printf 'permit2_nonce_bitmap_compare_calls=%s\n' "$(
  sed -n 's/^calls=//p' "$NONCE_BITMAP_COMPARE"
)"
printf 'permit2_signature_compare_calls=%s\n' "$(
  sed -n 's/^calls=//p' "$SIGNATURE_COMPARE"
)"
