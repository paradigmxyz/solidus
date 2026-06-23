#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
FORGE_BIN="${FORGE:-forge}"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
YUL_AST_SOLC="${YUL_AST_SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-protocol-diversity.XXXXXX")"
INSTALL_SOLC="${INSTALL_SOLC:-1}"

MORPHO_BLUE_REPO_URL="${MORPHO_BLUE_REPO_URL:-https://github.com/morpho-org/morpho-blue.git}"
MORPHO_BLUE_REF="${MORPHO_BLUE_REF:-55d2d99304fb3fb930c688462ae2ccabb1d533ad}"
SAFE_SMART_ACCOUNT_REPO_URL="${SAFE_SMART_ACCOUNT_REPO_URL:-https://github.com/safe-global/safe-smart-account.git}"
SAFE_SMART_ACCOUNT_REF="${SAFE_SMART_ACCOUNT_REF:-bf943f80fec5ac647159d26161446ac5d716a294}"
ENS_CONTRACTS_REPO_URL="${ENS_CONTRACTS_REPO_URL:-https://github.com/ensdomains/ens-contracts.git}"
ENS_CONTRACTS_REF="${ENS_CONTRACTS_REF:-9b034936a42f462fc04bc0a929a419ede5e18d59}"
ACCOUNT_ABSTRACTION_REPO_URL="${ACCOUNT_ABSTRACTION_REPO_URL:-https://github.com/eth-infinitism/account-abstraction.git}"
ACCOUNT_ABSTRACTION_REF="${ACCOUNT_ABSTRACTION_REF:-7af70c8993a6f42973f520ae0752386a5032abe7}"

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
    printf 'error: %s cannot provide solc %s\n%s\n' \
      "$SOLC_BIN" "$version" "$output" >&2
    return 1
  fi
}

checkout_repo() {
  local directory="$1"
  local url="$2"
  local ref="$3"
  git init -q "$directory"
  git -C "$directory" remote add origin "$url"
  git -C "$directory" fetch --depth 1 origin "$ref"
  git -C "$directory" -c advice.detachedHead=false checkout -q FETCH_HEAD
}

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$FORGE_BIN" "$YUL_AST_SOLC"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

ensure_solc_version 0.8.19
ensure_solc_version 0.8.26

if [[ -n "${MORPHO_BLUE_DIR:-}" ]]; then
  MORPHO_BLUE_REPO="$MORPHO_BLUE_DIR"
else
  MORPHO_BLUE_REPO="$OUTDIR/morpho-blue"
  checkout_repo "$MORPHO_BLUE_REPO" "$MORPHO_BLUE_REPO_URL" "$MORPHO_BLUE_REF"
fi

if [[ -n "${SAFE_SMART_ACCOUNT_DIR:-}" ]]; then
  SAFE_SMART_ACCOUNT_REPO="$SAFE_SMART_ACCOUNT_DIR"
else
  SAFE_SMART_ACCOUNT_REPO="$OUTDIR/safe-smart-account"
  checkout_repo "$SAFE_SMART_ACCOUNT_REPO" \
    "$SAFE_SMART_ACCOUNT_REPO_URL" "$SAFE_SMART_ACCOUNT_REF"
fi

if [[ -n "${ENS_CONTRACTS_DIR:-}" ]]; then
  ENS_CONTRACTS_REPO="$ENS_CONTRACTS_DIR"
else
  ENS_CONTRACTS_REPO="$OUTDIR/ens-contracts"
  checkout_repo "$ENS_CONTRACTS_REPO" "$ENS_CONTRACTS_REPO_URL" \
    "$ENS_CONTRACTS_REF"
fi

if [[ -n "${ACCOUNT_ABSTRACTION_DIR:-}" ]]; then
  ACCOUNT_ABSTRACTION_REPO="$ACCOUNT_ABSTRACTION_DIR"
else
  ACCOUNT_ABSTRACTION_REPO="$OUTDIR/account-abstraction"
  checkout_repo "$ACCOUNT_ABSTRACTION_REPO" \
    "$ACCOUNT_ABSTRACTION_REPO_URL" "$ACCOUNT_ABSTRACTION_REF"
fi

MORPHO_BLUE_ACTUAL_REF="$(git -C "$MORPHO_BLUE_REPO" rev-parse HEAD)"
SAFE_SMART_ACCOUNT_ACTUAL_REF="$(git -C "$SAFE_SMART_ACCOUNT_REPO" rev-parse HEAD)"
ENS_CONTRACTS_ACTUAL_REF="$(git -C "$ENS_CONTRACTS_REPO" rev-parse HEAD)"
ACCOUNT_ABSTRACTION_ACTUAL_REF="$(git -C "$ACCOUNT_ABSTRACTION_REPO" rev-parse HEAD)"

MORPHO_FIXTURE="$OUTDIR/MorphoCorpus.sol"
SAFE_FIXTURE="$OUTDIR/SafeCreateCorpus.sol"
ENS_FIXTURE="$OUTDIR/ENSBytesCorpus.sol"
ACCOUNT_ABSTRACTION_FIXTURE="$OUTDIR/AccountAbstractionCorpus.sol"

cat > "$MORPHO_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity 0.8.19;

import {Morpho} from "morpho/Morpho.sol";

contract MorphoCorpus is Morpho {
    constructor() Morpho(msg.sender) {}
}
SOL

cat > "$SAFE_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {CreateCall} from "safe/libraries/CreateCall.sol";

contract SafeCreateCorpus is CreateCall {}
SOL

cat > "$ENS_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {BytesUtils} from "ens/utils/BytesUtils.sol";

contract ENSBytesCorpus {
    using BytesUtils for bytes;

    fallback(bytes calldata input) external returns (bytes memory output) {
        require(input.length >= 34);
        uint8 mode = uint8(input[0]);
        bytes memory data = input[1:];

        if (mode == 1) {
            return abi.encode(data.readUint16(1));
        } else if (mode == 2) {
            return abi.encode(data.readUint32(2));
        } else if (mode == 3) {
            return abi.encode(data.readBytes20(3));
        } else if (mode == 4) {
            return abi.encode(data.readBytesN(4, 17));
        } else if (mode == 5) {
            return abi.encode(data.substring(5, 20));
        } else {
            return abi.encode(
                data.equals(1, data.substring(1, data.length - 1))
            );
        }
    }
}
SOL

cat > "$ACCOUNT_ABSTRACTION_FIXTURE" <<'SOL'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.23;

import {UserOperationLib} from "aa/core/UserOperationLib.sol";
import {calldataKeccak} from "aa/core/Helpers.sol";

contract AccountAbstractionCorpus {
    fallback(bytes calldata input) external returns (bytes memory output) {
        require(input.length >= 33);
        uint8 mode = uint8(input[0]);
        bytes calldata payload = input[1:];

        if (mode == 1) {
            (address paymaster, uint256 validationGas, uint256 postOpGas) =
                UserOperationLib.unpackPaymasterStaticFields(payload);
            return abi.encode(paymaster, validationGas, postOpGas);
        } else if (mode == 2) {
            return abi.encode(calldataKeccak(payload));
        } else {
            (uint256 high, uint256 low) =
                UserOperationLib.unpackUints(bytes32(payload[:32]));
            return abi.encode(high, low);
        }
    }
}
SOL

run_protocol_case() {
  local label="$1"
  local fixture="$2"
  local contract="$3"
  local solc_version="$4"
  local remapping="$5"
  local optimizer_runs="$6"
  local yul_ast_solc="$7"
  local forge_evm_version="$8"
  local expected_calls="$9"
  shift 9

  local case_dir="$OUTDIR/$label"
  local compare="$case_dir/call-compare.txt"
  local compile_args=(
    "$fixture"
    --solc "$SOLC_BIN"
    --lake "$LAKE_BIN"
    --lake-cwd "$ROOT"
    --remapping "$remapping"
    --contract "$contract"
    --optimized
  )
  local compare_args=(
    "$fixture"
    --solc "$SOLC_BIN"
    --lake "$LAKE_BIN"
    --lake-cwd "$ROOT"
    --forge "$FORGE_BIN"
    --forge-evm-version "$forge_evm_version"
    --remapping "$remapping"
    --contract "$contract"
    --optimized
  )
  local calldata_args=()
  local calldata object backend

  mkdir -p "$case_dir"
  if [[ "$optimizer_runs" != "none" ]]; then
    compile_args+=(--optimizer-runs "$optimizer_runs")
    compare_args+=(--optimizer-runs "$optimizer_runs")
  fi
  if [[ "$yul_ast_solc" != "none" ]]; then
    compile_args+=(--yul-ast-solc "$yul_ast_solc")
    compare_args+=(--yul-ast-solc "$yul_ast_solc")
  fi
  for calldata in "$@"; do
    calldata_args+=(--calldata "$calldata")
  done

  for object in creation runtime; do
    backend="$case_dir/$object.lean-backend-check.txt"
    SOLC_VERSION="$solc_version" "$PYTHON_BIN" \
      "$ROOT/scripts/solidity_to_yul_lean.py" \
      "${compile_args[@]}" \
      --object "$object" \
      --format lean-backend-check \
      --output "$backend"
    grep -qx 'lean_backend_check=pass' "$backend"
    grep -qx 'first_none=none' "$backend"
  done

  SOLC_VERSION="$solc_version" "$PYTHON_BIN" \
    "$ROOT/scripts/compare_contract_call_bytecode.py" \
    "${compare_args[@]}" \
    "${calldata_args[@]}" > "$compare"

  grep -qx 'contract_call_compare=pass' "$compare"
  grep -qx "calls=$expected_calls" "$compare"
  printf '%s_strict_backend_objects=2\n' "$label"
  printf '%s_compare_calls=%s\n' "$label" "$expected_calls"
}

run_protocol_case \
  morpho_blue \
  "$MORPHO_FIXTURE" \
  MorphoCorpus \
  0.8.19 \
  "morpho/=$MORPHO_BLUE_REPO/src/" \
  999999 \
  "$YUL_AST_SOLC" \
  paris \
  3 \
  0x8da5cb5b \
  0x4d98a93b00000000000000000000000000000000000000000000000006f05b59d3b20000 \
  0xb485f3b800000000000000000000000000000000000000000000000006f05b59d3b20000

# Exercise performCreate(uint256,bytes) and
# performCreate2(uint256,bytes,bytes32) on reverting initcode.
run_protocol_case \
  safe_create \
  "$SAFE_FIXTURE" \
  SafeCreateCorpus \
  0.8.26 \
  "safe/=$SAFE_SMART_ACCOUNT_REPO/contracts/" \
  none \
  none \
  cancun \
  2 \
  0x4c8c9ea1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000000 \
  0x4847be6f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000000

ENS_PAYLOAD=00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
run_protocol_case \
  ens_bytes \
  "$ENS_FIXTURE" \
  ENSBytesCorpus \
  0.8.26 \
  "ens/=$ENS_CONTRACTS_REPO/contracts/" \
  none \
  none \
  cancun \
  6 \
  "0x01$ENS_PAYLOAD" "0x02$ENS_PAYLOAD" "0x03$ENS_PAYLOAD" \
  "0x04$ENS_PAYLOAD" "0x05$ENS_PAYLOAD" "0x06$ENS_PAYLOAD"

ACCOUNT_ABSTRACTION_PAYLOAD=00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff
run_protocol_case \
  account_abstraction \
  "$ACCOUNT_ABSTRACTION_FIXTURE" \
  AccountAbstractionCorpus \
  0.8.26 \
  "aa/=$ACCOUNT_ABSTRACTION_REPO/contracts/" \
  none \
  none \
  cancun \
  3 \
  "0x01$ACCOUNT_ABSTRACTION_PAYLOAD" \
  "0x02$ACCOUNT_ABSTRACTION_PAYLOAD" \
  "0x03$ACCOUNT_ABSTRACTION_PAYLOAD"

printf 'protocol_diversity_bridge_smoke=pass\n'
printf 'morpho_blue_repo_ref=%s\n' "$MORPHO_BLUE_ACTUAL_REF"
printf 'safe_smart_account_repo_ref=%s\n' "$SAFE_SMART_ACCOUNT_ACTUAL_REF"
printf 'ens_contracts_repo_ref=%s\n' "$ENS_CONTRACTS_ACTUAL_REF"
printf 'account_abstraction_repo_ref=%s\n' "$ACCOUNT_ABSTRACTION_ACTUAL_REF"
printf 'protocol_diversity_repositories=4\n'
printf 'protocol_diversity_strict_backend_objects=8\n'
printf 'protocol_diversity_compare_calls=14\n'
