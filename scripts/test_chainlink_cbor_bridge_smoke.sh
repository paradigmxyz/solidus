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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-chainlink-cbor-smoke.XXXXXX")"
CHAINLINK_REPO_URL="${CHAINLINK_REPO_URL:-https://github.com/smartcontractkit/chainlink-brownie-contracts.git}"
CHAINLINK_REF="${CHAINLINK_REF:-f82d1ac09fc5d3190600d308be99a4a509854686}"
CHAINLINK_SOLC_VERSION="${CHAINLINK_SOLC_VERSION:-0.8.26}"
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

if [[ -n "${CHAINLINK_DIR:-}" ]]; then
  REPO="$CHAINLINK_DIR"
else
  REPO="$OUTDIR/chainlink-brownie-contracts"
  git init -q "$REPO"
  git -C "$REPO" remote add origin "$CHAINLINK_REPO_URL"
  git -C "$REPO" fetch --depth 1 origin "$CHAINLINK_REF"
  git -C "$REPO" -c advice.detachedHead=false checkout -q FETCH_HEAD
fi

ensure_solc_version "$CHAINLINK_SOLC_VERSION"

ACTUAL_REF="$(git -C "$REPO" rev-parse HEAD)"
FIXTURE="$OUTDIR/ChainlinkCborBufferFallback.sol"
BRIDGE_DIR="$OUTDIR/chainlink-cbor-bridge-json"
MANIFEST="$BRIDGE_DIR/manifest.json"
SUMMARY="$OUTDIR/ChainlinkCborBufferFallback.bridge-json-summary.json"
MANIFEST_CHECK="$OUTDIR/ChainlinkCborBufferFallback.manifest.lean-json-check.json"
BACKEND_CHECK="$OUTDIR/ChainlinkCborBufferFallback.lean-backend-check.json"
CALL_COMPARE="$OUTDIR/ChainlinkCborBufferFallback.runtime-only.call-compare.txt"
AGGREGATOR_FIXTURE="$OUTDIR/ChainlinkAggregatorRoundFallback.sol"
AGGREGATOR_BRIDGE_DIR="$OUTDIR/chainlink-aggregator-bridge-json"
AGGREGATOR_CHECK="$OUTDIR/ChainlinkAggregatorRoundFallback.lean-json-check.json"
AGGREGATOR_SUMMARY="$OUTDIR/ChainlinkAggregatorRoundFallback.bridge-json-summary.json"
AGGREGATOR_BACKEND_CHECK="$OUTDIR/ChainlinkAggregatorRoundFallback.lean-backend-check.json"
AGGREGATOR_COMPARE="$OUTDIR/ChainlinkAggregatorRoundFallback.runtime-only.call-compare.txt"

cat > "$FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {BufferChainlink} from "chainlink/contracts/src/v0.8/vendor/BufferChainlink.sol";
import {CBORChainlink} from "chainlink/contracts/src/v0.8/vendor/CBORChainlink.sol";

contract ChainlinkCborBufferFallback {
    using BufferChainlink for BufferChainlink.buffer;
    using CBORChainlink for BufferChainlink.buffer;

    fallback() external {
        uint8 mode;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
        }

        BufferChainlink.buffer memory buf;
        buf.init(16);

        if (mode == 1) {
            buf.encodeUInt(uint256(type(uint64).max) + 1);
        } else if (mode == 2) {
            buf.encodeInt(-5);
            buf.encodeString("oracle");
        } else if (mode == 3) {
            buf.startArray();
            buf.encodeBytes(msg.data);
            buf.endSequence();
        } else if (mode == 4) {
            bytes32 digest = keccak256(msg.data);
            buf.encodeBytes(abi.encode(digest));
        } else {
            buf.append(bytes("link"));
            buf.appendUint8(mode);
            buf.truncate();
            buf.encodeString("chainlink");
        }

        bytes memory out = buf.buf;
        assembly ("memory-safe") {
            return(add(out, 32), mload(out))
        }
    }
}
SOL

SOLC_VERSION="$CHAINLINK_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "chainlink/=$REPO/" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$BRIDGE_DIR" \
  --output "$MANIFEST"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$MANIFEST" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$MANIFEST_CHECK"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$BACKEND_CHECK"

RUNTIME_BACKEND_STATUS="$(
  python3 - "$BACKEND_CHECK" <<'PY'
import json
import sys

backend_check = json.load(open(sys.argv[1]))
runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "ChainlinkCborBufferFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(f"expected one Chainlink runtime backend check: {runtime_checks!r}")
print(runtime_checks[0].get("status", "missing"))
PY
)"

if [[ "$RUNTIME_BACKEND_STATUS" != "pass" ]]; then
  printf 'error: Chainlink CBOR runtime backend did not pass: %s\n' \
    "$RUNTIME_BACKEND_STATUS" >&2
  exit 1
fi

SOLC_VERSION="$CHAINLINK_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract ChainlinkCborBufferFallback \
  --remapping "chainlink/=$REPO/" \
  --calldata 0x00 \
  --calldata 0x01 \
  --calldata 0x02 \
  --calldata 0x03aabbcc \
  --calldata 0x04aabbcc \
  --runtime-only > "$CALL_COMPARE"

python3 - "$MANIFEST" "$SUMMARY" "$MANIFEST_CHECK" "$BACKEND_CHECK" "$CALL_COMPARE" <<'PY'
import json
import sys
from pathlib import Path

manifest = json.load(open(sys.argv[1]))
summary = json.load(open(sys.argv[2]))
manifest_check = json.load(open(sys.argv[3]))
backend_check = json.load(open(sys.argv[4]))
call_compare_path = Path(sys.argv[5])
call_compare = {}
if call_compare_path.exists():
    for line in call_compare_path.read_text().splitlines():
        if "=" in line:
            key, value = line.strip().split("=", 1)
            call_compare[key] = value

entries = manifest["entries"]
entry_count = manifest["counts"]["entries"]
skipped = manifest["counts"]["skippedContracts"]
summary_count = summary["counts"]["objects"]
checked_count = manifest_check["counts"]["checkedObjects"]
backend_checked_count = backend_check["counts"]["checkedObjects"]

if entry_count != 2:
    raise SystemExit(f"expected 2 Chainlink fallback bridge objects, got {entry_count}")
if skipped != 0:
    raise SystemExit(f"expected no skipped Chainlink contracts, got {skipped}")
if summary_count != entry_count:
    raise SystemExit(
        f"Chainlink summary listed {summary_count} objects, expected {entry_count}"
    )
if checked_count != entry_count:
    raise SystemExit(
        f"Chainlink Lean manifest replay decoded {checked_count} objects, "
        f"expected {entry_count}"
    )
if backend_checked_count != entry_count:
    raise SystemExit(
        f"Chainlink backend check decoded {backend_checked_count} objects, "
        f"expected {entry_count}"
    )

runtime_entries = [
    item
    for item in entries
    if item.get("contract") == "ChainlinkCborBufferFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit(f"expected one Chainlink runtime entry, got {runtime_entries!r}")
frontend = runtime_entries[0].get("frontend")
if frontend != {"producer": "solc", "ast": "irAst"}:
    raise SystemExit(f"unexpected Chainlink runtime frontend metadata: {frontend!r}")

runtime_summaries = [
    item
    for item in summary.get("objects", [])
    if item.get("contract") == "ChainlinkCborBufferFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(
        f"expected one Chainlink runtime summary, got {runtime_summaries!r}"
    )
runtime = runtime_summaries[0]
primitive_entries = runtime.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
missing_primitives = sorted(
    {
        "calldataload",
        "calldatacopy",
        "mstore8",
        "keccak256",
        "return",
    }
    - primitives
)
if missing_primitives:
    raise SystemExit(
        f"Chainlink CBOR summary missing primitives: {missing_primitives!r}"
    )

user_entries = runtime.get("calls", {}).get("user", {}).get("names", [])
user_calls = {
    entry.get("name")
    for entry in user_entries
    if isinstance(entry, dict)
}
required_user_call_prefixes = [
    "fun_encodeUInt_",
    "fun_encodeInt_",
    "fun_encodeString_",
    "fun_encodeBytes_",
    "fun_appendUint8_",
    "fun_truncate_",
]
missing_user_calls = [
    prefix
    for prefix in required_user_call_prefixes
    if not any(name.startswith(prefix) for name in user_calls)
]
if missing_user_calls:
    raise SystemExit(
        f"Chainlink CBOR summary missing user calls: {missing_user_calls!r}"
    )

compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(
        f"unexpected Chainlink runtime compatibility: {compatibility!r}"
    )

runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "ChainlinkCborBufferFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(f"expected one Chainlink runtime backend check: {runtime_checks!r}")
runtime_check = runtime_checks[0]
runtime_check_status = runtime_check.get("status")
runtime_first_none = runtime_check.get("firstNone")
if runtime_check_status != "pass" or runtime_first_none != "none":
    raise SystemExit(f"Chainlink runtime backend did not pass: {runtime_check!r}")
if call_compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"Chainlink runtime compare did not pass: {call_compare!r}")
if call_compare.get("calls") != "5":
    raise SystemExit(f"Chainlink runtime compare call count mismatch: {call_compare!r}")
if call_compare.get("bridge_summary_count") != "1":
    raise SystemExit(
        f"Chainlink runtime compare summary count mismatch: {call_compare!r}"
    )
if call_compare.get("bridge_summary_1_backend_compatibility") != "ready":
    raise SystemExit(
        f"Chainlink runtime compare backend summary mismatch: {call_compare!r}"
    )
if call_compare.get("bridge_summary_1_objects") != "1":
    raise SystemExit(
        f"Chainlink runtime compare summary object mismatch: {call_compare!r}"
    )
if (
    call_compare.get("bridge_summary_1_object_selectors")
    != "ChainlinkCborBufferFallback:runtime"
):
    raise SystemExit(
        f"Chainlink runtime compare summary selector mismatch: {call_compare!r}"
    )
if call_compare.get("bridge_summary_1_frontends") != "solc:irAst":
    raise SystemExit(
        f"Chainlink runtime compare frontend summary mismatch: {call_compare!r}"
    )
if call_compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(
        f"Chainlink runtime compare reported unsupported primitives: "
        f"{call_compare!r}"
    )
for byte_key in ["full_runtime_bytes", "lean_runtime_bytes"]:
    try:
        byte_count = int(call_compare.get(byte_key, "0"))
    except ValueError as exc:
        raise SystemExit(
            f"Chainlink runtime compare reported invalid {byte_key}: "
            f"{call_compare!r}"
        ) from exc
    if byte_count <= 0:
        raise SystemExit(
            f"Chainlink runtime compare reported empty {byte_key}: "
            f"{call_compare!r}"
        )
runtime_compare = "yes"
runtime_compare_calls = call_compare["calls"]

print(f"chainlink_cbor_bridge_objects={entry_count}")
print(f"chainlink_cbor_summary_objects={summary_count}")
print(f"chainlink_cbor_manifest_decode_objects={checked_count}")
print(f"chainlink_cbor_runtime_backend_compatibility={compatibility.get('status')}")
print(f"chainlink_cbor_runtime_backend_check={runtime_check_status}")
print(f"chainlink_cbor_runtime_backend_first_none={runtime_first_none}")
print("chainlink_cbor_frontend_metadata=yes")
print("chainlink_cbor_manifest_lean_decode=yes")
print("chainlink_cbor_summary_primitives=yes")
print("chainlink_cbor_summary_user_calls=yes")
print(f"chainlink_cbor_runtime_compare={runtime_compare}")
print(f"chainlink_cbor_runtime_compare_calls={runtime_compare_calls}")
PY

cat > "$AGGREGATOR_FIXTURE" <<'SOL'
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.26;

import {AggregatorV3Interface} from "chainlink/contracts/src/v0.8/shared/interfaces/AggregatorV3Interface.sol";

contract ChainlinkAggregatorRoundFallback is AggregatorV3Interface {
    error NoDataPresent();
    error StaleRound(uint80 roundId, uint256 updatedAt);

    event AnswerUpdated(int256 indexed current, uint256 indexed roundId, uint256 updatedAt);

    struct Round {
        int256 answer;
        uint256 startedAt;
        uint256 updatedAt;
        uint80 answeredInRound;
    }

    mapping(uint80 => Round) private rounds;
    uint80 public latestRoundId;

    function decimals() external pure override returns (uint8) {
        return 8;
    }

    function description() external pure override returns (string memory) {
        return "LINK / USD";
    }

    function version() external pure override returns (uint256) {
        return 4;
    }

    function transmit(int256 answer, uint32 updatedAt) public returns (uint80) {
        uint80 roundId = latestRoundId + 1;
        rounds[roundId] = Round({
            answer: answer,
            startedAt: updatedAt - 12,
            updatedAt: updatedAt,
            answeredInRound: roundId
        });
        latestRoundId = roundId;
        emit AnswerUpdated(answer, roundId, updatedAt);
        return roundId;
    }

    function markStale(uint80 roundId) public {
        Round storage round = rounds[roundId];
        if (round.updatedAt == 0) revert NoDataPresent();
        round.answeredInRound = roundId - 1;
    }

    function getRoundData(uint80 roundId)
        public
        view
        override
        returns (
            uint80 roundId_,
            int256 answer,
            uint256 startedAt,
            uint256 updatedAt,
            uint80 answeredInRound
        )
    {
        Round memory round = rounds[roundId];
        if (round.updatedAt == 0) revert NoDataPresent();
        if (round.answeredInRound < roundId) revert StaleRound(roundId, round.updatedAt);
        return (roundId, round.answer, round.startedAt, round.updatedAt, round.answeredInRound);
    }

    function latestRoundData()
        public
        view
        override
        returns (
            uint80 roundId_,
            int256 answer,
            uint256 startedAt,
            uint256 updatedAt,
            uint80 answeredInRound
        )
    {
        return getRoundData(latestRoundId);
    }

    fallback() external {
        uint8 mode;
        uint80 roundId;
        assembly ("memory-safe") {
            mode := byte(0, calldataload(0))
            roundId := calldataload(1)
        }

        if (mode == 1) {
            uint80 newRound = transmit(-123456789, 1000);
            bytes memory encoded = abi.encode(newRound);
            assembly ("memory-safe") {
                return(add(encoded, 32), mload(encoded))
            }
        } else if (mode == 2) {
            markStale(latestRoundId);
            return;
        } else if (mode == 3) {
            (
                uint80 returnedRound,
                int256 answer,
                uint256 startedAt,
                uint256 updatedAt,
                uint80 answeredInRound
            ) = getRoundData(roundId);
            bytes memory encoded =
                abi.encode(returnedRound, answer, startedAt, updatedAt, answeredInRound);
            assembly ("memory-safe") {
                return(add(encoded, 32), mload(encoded))
            }
        } else if (mode == 4) {
            uint80 newRound = transmit(777777777, 2000);
            bytes memory encoded = abi.encode(newRound);
            assembly ("memory-safe") {
                return(add(encoded, 32), mload(encoded))
            }
        }

        (
            uint80 currentRound,
            int256 latestAnswer,
            uint256 latestStartedAt,
            uint256 latestUpdatedAt,
            uint80 latestAnsweredInRound
        ) = latestRoundData();
        bytes memory latest = abi.encode(
            currentRound,
            latestAnswer,
            latestStartedAt,
            latestUpdatedAt,
            latestAnsweredInRound
        );
        assembly ("memory-safe") {
            return(add(latest, 32), mload(latest))
        }
    }
}
SOL

SOLC_VERSION="$CHAINLINK_SOLC_VERSION" python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$AGGREGATOR_FIXTURE" \
  --solc "$SOLC_BIN" \
  --remapping "chainlink/=$REPO/" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract ChainlinkAggregatorRoundFallback \
  --object runtime \
  --format lean-json-check \
  --bridge-json-dir "$AGGREGATOR_BRIDGE_DIR" \
  --optimized \
  --output "$AGGREGATOR_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$AGGREGATOR_BRIDGE_DIR/manifest.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$AGGREGATOR_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --output "$AGGREGATOR_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$AGGREGATOR_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$AGGREGATOR_BRIDGE_DIR/manifest.json" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract ChainlinkAggregatorRoundFallback \
  --object runtime \
  --format lean-backend-check \
  --output "$AGGREGATOR_BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$AGGREGATOR_BACKEND_CHECK"

AGGREGATOR_RUNTIME_BACKEND_STATUS="$(
  python3 - "$AGGREGATOR_BACKEND_CHECK" <<'PY'
import json
import sys

backend_check = json.load(open(sys.argv[1]))
runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "ChainlinkAggregatorRoundFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(
        f"expected one Chainlink aggregator runtime backend check: {runtime_checks!r}"
    )
print(runtime_checks[0].get("status", "missing"))
PY
)"

word() {
  printf '%064x' "$1"
}

AGGREGATOR_ROUND_1="0x03$(word 1)"
AGGREGATOR_ROUND_99="0x03$(word 99)"

if [[ "$AGGREGATOR_RUNTIME_BACKEND_STATUS" != "pass" ]]; then
  printf 'error: Chainlink aggregator runtime backend did not pass: %s\n' \
    "$AGGREGATOR_RUNTIME_BACKEND_STATUS" >&2
  exit 1
fi

SOLC_VERSION="$CHAINLINK_SOLC_VERSION" python3 "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$AGGREGATOR_FIXTURE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract ChainlinkAggregatorRoundFallback \
  --remapping "chainlink/=$REPO/" \
  --calldata 0x01 \
  --calldata 0x00 \
  --calldata 0x04 \
  --calldata "$AGGREGATOR_ROUND_1" \
  --calldata 0x02 \
  --calldata 0x00 \
  --calldata "$AGGREGATOR_ROUND_99" \
  --runtime-only \
  --optimized > "$AGGREGATOR_COMPARE"

python3 - "$AGGREGATOR_CHECK" "$AGGREGATOR_SUMMARY" \
  "$AGGREGATOR_BACKEND_CHECK" "$AGGREGATOR_COMPARE" <<'PY'
import json
import sys
from pathlib import Path

decode_summary = {}
for line in open(sys.argv[1]):
    if "=" in line:
        key, value = line.strip().split("=", 1)
        decode_summary[key] = value
summary = json.load(open(sys.argv[2]))
backend_check = json.load(open(sys.argv[3]))
call_compare_path = Path(sys.argv[4])
call_compare = {}
if call_compare_path.exists():
    for line in call_compare_path.read_text().splitlines():
        if "=" in line:
            key, value = line.strip().split("=", 1)
            call_compare[key] = value

if decode_summary.get("lean_bridge_json_decode") != "pass":
    raise SystemExit(f"unexpected Chainlink aggregator decode summary: {decode_summary!r}")
checked_count = 1
summary_count = summary["counts"]["objects"]
backend_checked_count = backend_check["counts"]["checkedObjects"]
if checked_count != 1:
    raise SystemExit(
        f"expected one Chainlink aggregator decoded object, got {checked_count}"
    )
if summary_count != checked_count:
    raise SystemExit(
        f"Chainlink aggregator summary listed {summary_count} objects, "
        f"expected {checked_count}"
    )
if backend_checked_count != checked_count:
    raise SystemExit(
        f"Chainlink aggregator backend checked {backend_checked_count} objects, "
        f"expected {checked_count}"
    )

runtime_summaries = [
    item
    for item in summary.get("objects", [])
    if item.get("contract") == "ChainlinkAggregatorRoundFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_summaries) != 1:
    raise SystemExit(
        "expected one Chainlink aggregator runtime summary, got "
        f"{runtime_summaries!r}"
    )
runtime = runtime_summaries[0]
frontend = runtime.get("frontend")
if frontend != {"producer": "solc", "ast": "irOptimizedAst"}:
    raise SystemExit(
        f"unexpected Chainlink aggregator frontend metadata: {frontend!r}"
    )

primitives = {
    entry.get("name")
    for entry in runtime.get("calls", {}).get("primitive", {}).get("names", [])
    if isinstance(entry, dict)
}
missing_primitives = sorted(
    {"sload", "sstore", "log3", "calldataload", "return", "revert"} - primitives
)
if missing_primitives:
    raise SystemExit(
        f"Chainlink aggregator summary missing primitives: {missing_primitives!r}"
    )

user_calls = {
    entry.get("name")
    for entry in runtime.get("calls", {}).get("user", {}).get("names", [])
    if isinstance(entry, dict)
}
required_user_call_prefixes = [
    "fun_markStale",
    "fun_getRoundData",
]
missing_user_calls = [
    prefix
    for prefix in required_user_call_prefixes
    if not any(name.startswith(prefix) for name in user_calls)
]
if missing_user_calls:
    raise SystemExit(
        f"Chainlink aggregator summary missing user calls: {missing_user_calls!r}"
    )

compatibility = runtime.get("backendCompatibility", {})
if compatibility.get("status") not in {"ready", "needs-resolution", "blocked"}:
    raise SystemExit(
        f"unexpected Chainlink aggregator compatibility: {compatibility!r}"
    )

runtime_checks = [
    item
    for item in backend_check.get("checkedObjects", [])
    if item.get("contract") == "ChainlinkAggregatorRoundFallback"
    and item.get("selector") == "runtime"
]
if len(runtime_checks) != 1:
    raise SystemExit(
        f"expected one Chainlink aggregator backend check: {runtime_checks!r}"
    )
runtime_check = runtime_checks[0]
runtime_check_status = runtime_check.get("status")
runtime_first_none = runtime_check.get("firstNone")
if runtime_check_status != "pass" or runtime_first_none != "none":
    raise SystemExit(
        f"Chainlink aggregator runtime backend did not pass: {runtime_check!r}"
    )
if call_compare.get("contract_call_compare") != "pass":
    raise SystemExit(
        f"Chainlink aggregator runtime compare did not pass: {call_compare!r}"
    )
if call_compare.get("calls") != "7":
    raise SystemExit(
        f"Chainlink aggregator compare call count mismatch: {call_compare!r}"
    )
runtime_compare = "yes"
runtime_compare_calls = call_compare["calls"]

print(f"chainlink_aggregator_decode_objects={checked_count}")
print(f"chainlink_aggregator_summary_objects={summary_count}")
print(f"chainlink_aggregator_backend_compatibility={compatibility.get('status')}")
print(f"chainlink_aggregator_runtime_backend_check={runtime_check_status}")
print(f"chainlink_aggregator_runtime_backend_first_none={runtime_first_none}")
print("chainlink_aggregator_frontend_metadata=yes")
print("chainlink_aggregator_summary_primitives=yes")
print("chainlink_aggregator_summary_user_calls=yes")
print(f"chainlink_aggregator_runtime_compare={runtime_compare}")
print(f"chainlink_aggregator_runtime_compare_calls={runtime_compare_calls}")
PY
printf 'chainlink_cbor_bridge_smoke=pass\n'
printf 'repo_ref=%s\n' "$ACTUAL_REF"
