// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract Opcode44Surface {
    function opcode44Value() external view returns (uint256) {
        return block.difficulty;
    }
}
