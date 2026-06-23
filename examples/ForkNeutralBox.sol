// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract ForkNeutralBox {
    function mix(uint256 x, uint256 y) external pure returns (uint256) {
        return (x * 17) ^ y;
    }
}
