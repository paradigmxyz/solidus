// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract CancunOpcodeSurface {
    function copyWord(bytes32 value) external pure returns (bytes32 result) {
        assembly {
            mstore(0x80, value)
            mcopy(0xa0, 0x80, 0x20)
            result := mload(0xa0)
        }
    }

    function transientRoundTrip(bytes32 key, uint256 value)
        external
        returns (uint256 result)
    {
        assembly {
            tstore(key, value)
            result := tload(key)
        }
    }
}
