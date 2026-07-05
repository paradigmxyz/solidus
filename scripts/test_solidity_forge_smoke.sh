#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
LAKE_BIN="${LAKE:-lake}"
FORGE_BIN="${FORGE:-forge}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-forge-smoke.XXXXXX")"
SOLC_FORGE_USE="$SOLC_BIN"

if [[ "$SOLC_BIN" != */* ]]; then
  resolved_solc="$(command -v "$SOLC_BIN" || true)"
  if [[ -n "$resolved_solc" ]]; then
    SOLC_FORGE_USE="$resolved_solc"
  fi
fi

cleanup() {
  rm -rf "$OUTDIR"
}
trap cleanup EXIT

creation="$OUTDIR/Simple.creation.hex"
runtime="$OUTDIR/Simple.runtime.hex"
counter_creation="$OUTDIR/Counter.creation.hex"
counter_runtime="$OUTDIR/Counter.runtime.hex"
uses_library_artifact="$OUTDIR/UsesLibrary.artifact.json"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Simple.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format bytecode \
  --unverified-diagnostic \
  --object creation \
  --namespace Generated.SimpleForgeCreationSmoke \
  --output "$creation"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Simple.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --format bytecode \
  --unverified-diagnostic \
  --object runtime \
  --namespace Generated.SimpleForgeRuntimeSmoke \
  --output "$runtime"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Counter.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Counter \
  --format bytecode \
  --unverified-diagnostic \
  --object creation \
  --namespace Generated.CounterForgeCreationSmoke \
  --output "$counter_creation"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/Counter.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Counter \
  --format bytecode \
  --unverified-diagnostic \
  --object runtime \
  --namespace Generated.CounterForgeRuntimeSmoke \
  --output "$counter_runtime"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/UsesLibrary.sol" \
  --linker-symbol 'MathLib.sol:MathLib=0' \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --contract UsesLibrary \
  --format bytecode-artifact \
  --unverified-diagnostic \
  --namespace Generated.UsesLibraryForgeArtifactSmoke \
  --output "$uses_library_artifact"

uses_library_creation_hex="$(
  python3 - "$uses_library_artifact" <<'PY'
import json
import sys
with open(sys.argv[1]) as handle:
    print(json.load(handle)["bytecode"]["creation"])
PY
)"
uses_library_runtime_hex="$(
  python3 - "$uses_library_artifact" <<'PY'
import json
import sys
with open(sys.argv[1]) as handle:
    print(json.load(handle)["bytecode"]["runtime"])
PY
)"

creation_hex="$(tr -d '\n' < "$creation")"
runtime_hex="$(tr -d '\n' < "$runtime")"
counter_creation_hex="$(tr -d '\n' < "$counter_creation")"
counter_runtime_hex="$(tr -d '\n' < "$counter_runtime")"
creation_payload="${creation_hex#0x}"
runtime_payload="${runtime_hex#0x}"
counter_creation_payload="${counter_creation_hex#0x}"
counter_runtime_payload="${counter_runtime_hex#0x}"
uses_library_creation_payload="${uses_library_creation_hex#0x}"
uses_library_runtime_payload="${uses_library_runtime_hex#0x}"

if [[ ! "$creation_hex" =~ ^0x[0-9a-f]+$ ]]; then
  echo "creation bytecode is not nonempty lowercase hex: $creation_hex" >&2
  exit 1
fi

if [[ ! "$runtime_hex" =~ ^0x[0-9a-f]+$ ]]; then
  echo "runtime bytecode is not nonempty lowercase hex: $runtime_hex" >&2
  exit 1
fi

if [[ ! "$counter_creation_hex" =~ ^0x[0-9a-f]+$ ]]; then
  echo "counter creation bytecode is not nonempty lowercase hex: $counter_creation_hex" >&2
  exit 1
fi

if [[ ! "$counter_runtime_hex" =~ ^0x[0-9a-f]+$ ]]; then
  echo "counter runtime bytecode is not nonempty lowercase hex: $counter_runtime_hex" >&2
  exit 1
fi

if [[ ! "$uses_library_creation_hex" =~ ^0x[0-9a-f]+$ ]]; then
  echo "uses-library creation bytecode is not nonempty lowercase hex" >&2
  exit 1
fi

if [[ ! "$uses_library_runtime_hex" =~ ^0x[0-9a-f]+$ ]]; then
  echo "uses-library runtime bytecode is not nonempty lowercase hex" >&2
  exit 1
fi

mkdir -p "$OUTDIR/src" "$OUTDIR/test"

cat > "$OUTDIR/foundry.toml" <<'TOML'
[profile.default]
src = "src"
test = "test"
out = "out"
cache_path = "cache"
evm_version = "cancun"
TOML

cat > "$OUTDIR/test/LeanRuntimeSmoke.t.sol" <<SOL
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

interface Vm {
    function etch(address target, bytes calldata newRuntimeBytecode) external;
}

interface ISimple {
    function addOne(uint256 x) external view returns (uint256);
}

interface ICounter {
    function value() external view returns (uint256);
    function inc() external;
    function add(uint256 amount) external;
}

interface IUsesLibrary {
    function twice(uint256 value) external view returns (uint256);
}

contract LeanRuntimeSmokeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testLeanRuntimeEtchedAddOne() public {
        address target = address(0x1000);
        vm.etch(target, hex"$runtime_payload");
        _assertAddOne(target);
    }

    function testLeanCreationDeploysAddOne() public {
        bytes memory initcode = hex"$creation_payload";
        address deployed;
        assembly {
            deployed := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(deployed != address(0), "create failed");
        _assertAddOne(deployed);
    }

    function testLeanCounterRuntimeEtchedStorage() public {
        address target = address(0x2000);
        vm.etch(target, hex"$counter_runtime_payload");
        _assertCounterStorage(target);
    }

    function testLeanCounterCreationDeploysStorage() public {
        bytes memory initcode = hex"$counter_creation_payload";
        address deployed;
        assembly {
            deployed := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(deployed != address(0), "counter create failed");
        _assertCounterStorage(deployed);
    }

    function testLeanUsesLibraryRuntimeEtchedTwice() public {
        address target = address(0x3000);
        vm.etch(target, hex"$uses_library_runtime_payload");
        _assertTwice(target);
    }

    function testLeanUsesLibraryCreationDeploysTwice() public {
        bytes memory initcode = hex"$uses_library_creation_payload";
        address deployed;
        assembly {
            deployed := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(deployed != address(0), "uses-library create failed");
        _assertTwice(deployed);
    }

    function _assertAddOne(address target) private view {
        (bool ok, bytes memory ret) =
            target.staticcall(abi.encodeWithSignature("addOne(uint256)", 41));
        require(ok, "addOne call failed");
        require(ret.length == 32, "bad return length");
        uint256 value = abi.decode(ret, (uint256));
        require(value == 42, "bad addOne result");
    }

    function _assertCounterStorage(address target) private {
        _assertCounterValue(target, 0);

        (bool ok,) = target.call(abi.encodeWithSignature("inc()"));
        require(ok, "inc call failed");
        _assertCounterValue(target, 1);

        (ok,) = target.call(abi.encodeWithSignature("add(uint256)", 41));
        require(ok, "add call failed");
        _assertCounterValue(target, 42);
    }

    function _assertCounterValue(address target, uint256 expected) private view {
        (bool ok, bytes memory ret) =
            target.staticcall(abi.encodeWithSignature("value()"));
        require(ok, "value call failed");
        require(ret.length == 32, "bad value return length");
        uint256 value = abi.decode(ret, (uint256));
        require(value == expected, "bad counter value");
    }

    function _assertTwice(address target) private view {
        (bool ok, bytes memory ret) =
            target.staticcall(abi.encodeWithSignature("twice(uint256)", 21));
        require(ok, "twice call failed");
        require(ret.length == 32, "bad twice return length");
        uint256 value = abi.decode(ret, (uint256));
        require(value == 42, "bad twice result");
    }
}
SOL

"$FORGE_BIN" test \
  --root "$OUTDIR" \
  --use "$SOLC_FORGE_USE" \
  --offline \
  --match-contract LeanRuntimeSmokeTest \
  --match-test 'testLean*' \
  -q

printf 'forge_smoke=pass\n'
printf 'creation_bytes=%s\n' "$(( ${#creation_payload} / 2 ))"
printf 'runtime_bytes=%s\n' "$(( ${#runtime_payload} / 2 ))"
printf 'counter_creation_bytes=%s\n' "$(( ${#counter_creation_payload} / 2 ))"
printf 'counter_runtime_bytes=%s\n' "$(( ${#counter_runtime_payload} / 2 ))"
printf 'uses_library_creation_bytes=%s\n' "$(( ${#uses_library_creation_payload} / 2 ))"
printf 'uses_library_runtime_bytes=%s\n' "$(( ${#uses_library_runtime_payload} / 2 ))"
