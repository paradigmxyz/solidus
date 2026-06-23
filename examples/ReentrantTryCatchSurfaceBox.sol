// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Exercises self-calls, nested call frames, catch dispatch, and rollback.
contract ReentrantTryCatchSurfaceBox {
    error CustomFailure(uint256 value);

    event Probed(
        uint8 indexed mode,
        uint256 depth,
        uint8 kind,
        bytes32 fingerprint,
        uint256 counterAfter
    );

    uint256 public counter;

    function recurse(uint8 mode, uint256 depth)
        external
        returns (uint256 result)
    {
        ++counter;
        if (depth != 0) {
            return this.recurse(mode, depth - 1) + 1;
        }

        if (mode == 1) revert("reasoned failure");
        if (mode == 2) assert(false);
        if (mode == 3) revert CustomFailure(counter);
        if (mode == 4) {
            assembly ("memory-safe") {
                mstore(0, 0xa1b2c3)
                revert(29, 3)
            }
        }
        if (mode == 5) {
            assembly {
                invalid()
            }
        }
        return counter;
    }

    function probe(uint8 mode, uint256 depth)
        external
        returns (uint8 kind, bytes32 fingerprint, uint256 counterAfter)
    {
        try this.recurse(mode, depth) returns (uint256 value) {
            kind = 0;
            fingerprint = bytes32(value);
        } catch Error(string memory reason) {
            kind = 1;
            fingerprint = keccak256(bytes(reason));
        } catch Panic(uint256 code) {
            kind = 2;
            fingerprint = bytes32(code);
        } catch (bytes memory data) {
            kind = 3;
            fingerprint = keccak256(data);
        }

        counterAfter = counter;
        emit Probed(mode, depth, kind, fingerprint, counterAfter);
    }
}
