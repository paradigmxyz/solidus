// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Adversarial coverage for low-level operations that ordinary ABI
/// examples rarely retain in optimized Yul.
contract SemanticSurfaceBox {
    function executionContext(address account, uint256 requestedBlock)
        external
        payable
        returns (bytes32 digest)
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, address())
            mstore(add(ptr, 0x20), balance(account))
            mstore(add(ptr, 0x40), origin())
            mstore(add(ptr, 0x60), caller())
            mstore(add(ptr, 0x80), callvalue())
            mstore(add(ptr, 0xa0), calldataload(4))
            mstore(add(ptr, 0xc0), calldatasize())
            mstore(add(ptr, 0xe0), gasprice())
            mstore(add(ptr, 0x100), blockhash(requestedBlock))
            mstore(add(ptr, 0x120), coinbase())
            mstore(add(ptr, 0x140), timestamp())
            mstore(add(ptr, 0x160), number())
            mstore(add(ptr, 0x180), prevrandao())
            mstore(add(ptr, 0x1a0), gaslimit())
            mstore(add(ptr, 0x1c0), chainid())
            mstore(add(ptr, 0x1e0), selfbalance())
            mstore(add(ptr, 0x200), basefee())
            calldatacopy(add(ptr, 0x220), 0, calldatasize())
            digest := keccak256(ptr, add(0x220, calldatasize()))
        }
    }

    function arithmetic(uint256 x, uint256 y, uint256 modulus)
        external
        pure
        returns (bytes32 digest)
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, add(x, y))
            mstore(add(ptr, 0x20), mul(x, y))
            mstore(add(ptr, 0x40), sub(x, y))
            mstore(add(ptr, 0x60), div(x, y))
            mstore(add(ptr, 0x80), sdiv(x, y))
            mstore(add(ptr, 0xa0), mod(x, y))
            mstore(add(ptr, 0xc0), smod(x, y))
            mstore(add(ptr, 0xe0), addmod(x, y, modulus))
            mstore(add(ptr, 0x100), mulmod(x, y, modulus))
            mstore(add(ptr, 0x120), exp(x, and(y, 0xff)))
            mstore(add(ptr, 0x140), signextend(x, y))
            mstore(add(ptr, 0x160), lt(x, y))
            mstore(add(ptr, 0x180), gt(x, y))
            mstore(add(ptr, 0x1a0), slt(x, y))
            mstore(add(ptr, 0x1c0), sgt(x, y))
            mstore(add(ptr, 0x1e0), eq(x, y))
            mstore(add(ptr, 0x200), iszero(x))
            mstore(add(ptr, 0x220), and(x, y))
            mstore(add(ptr, 0x240), or(x, y))
            mstore(add(ptr, 0x260), xor(x, y))
            mstore(add(ptr, 0x280), not(x))
            mstore(add(ptr, 0x2a0), byte(and(x, 31), y))
            mstore(add(ptr, 0x2c0), shl(and(x, 255), y))
            mstore(add(ptr, 0x2e0), shr(and(x, 255), y))
            mstore(add(ptr, 0x300), sar(and(x, 255), y))
            digest := keccak256(ptr, 0x320)
        }
    }

    function storageAndBytes(bytes32 slot, uint256 value)
        external
        returns (bytes32 digest)
    {
        assembly {
            sstore(slot, value)
            let ptr := mload(0x40)
            mstore(ptr, sload(slot))
            mstore8(add(ptr, 31), byte(31, value))
            digest := keccak256(ptr, 0x20)
        }
    }

    function loadStorage(bytes32 slot) external view returns (uint256 value) {
        assembly {
            value := sload(slot)
        }
    }

    function transientAndBlob(bytes32 key, uint256 value, uint256 blobIndex)
        external
        returns (uint256 loaded, bytes32 versionedHash, uint256 blobFee)
    {
        assembly {
            tstore(key, value)
            loaded := tload(key)
            versionedHash := blobhash(blobIndex)
            blobFee := blobbasefee()
        }
    }

    function memoryAndCode(address account, uint256 value)
        external
        view
        returns (
            uint256 copied,
            uint256 localSize,
            uint256 externalSize,
            bytes32 externalHash,
            bytes32 localCodeHash,
            bytes32 externalCodeHash
        )
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, value)
            mcopy(add(ptr, 0x20), ptr, 0x20)
            copied := mload(add(ptr, 0x20))

            localSize := codesize()
            codecopy(add(ptr, 0x40), 0, localSize)
            localCodeHash := keccak256(add(ptr, 0x40), localSize)

            externalSize := extcodesize(account)
            extcodecopy(account, add(ptr, 0x40), 0, externalSize)
            externalCodeHash := keccak256(add(ptr, 0x40), externalSize)
            externalHash := extcodehash(account)
        }
    }

    function calls(address target, bytes calldata payload)
        external
        payable
        returns (
            bool callOk,
            bool callcodeOk,
            bool delegateOk,
            bool staticOk,
            bytes32 returnHash
        )
    {
        assembly {
            let ptr := mload(0x40)
            callOk := call(
                gas(), target, callvalue(), payload.offset, payload.length, ptr, 0x20
            )
            callcodeOk := callcode(
                gas(), target, 0, payload.offset, payload.length, ptr, 0x20
            )
            delegateOk := delegatecall(
                gas(), target, payload.offset, payload.length, ptr, 0x20
            )
            staticOk := staticcall(
                gas(), target, payload.offset, payload.length, ptr, 0x20
            )
            let size := returndatasize()
            returndatacopy(ptr, 0, size)
            returnHash := keccak256(ptr, size)
        }
    }

    function creates(bytes memory initCode, bytes32 salt)
        external
        payable
        returns (address first, address second)
    {
        assembly {
            let start := add(initCode, 0x20)
            let size := mload(initCode)
            first := create(callvalue(), start, size)
            second := create2(0, start, size, salt)
        }
    }

    function logs(bytes32 topic1, bytes32 topic2, bytes32 topic3, bytes32 topic4)
        external
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, caller())
            log0(ptr, 0x20)
            log1(ptr, 0x20, topic1)
            log2(ptr, 0x20, topic1, topic2)
            log3(ptr, 0x20, topic1, topic2, topic3)
            log4(ptr, 0x20, topic1, topic2, topic3, topic4)
        }
    }

    function terminate(uint256 mode, address payable beneficiary) external {
        assembly {
            switch mode
            case 0 { stop() }
            case 1 { selfdestruct(beneficiary) }
            default { invalid() }
        }
    }
}
