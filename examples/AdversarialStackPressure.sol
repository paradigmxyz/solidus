// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

interface IPressureTarget {
    function ping() external returns (uint256);
}

/// Forces the via-IR optimizer to preserve pre-call storage values across a
/// potentially reentrant external call. Those values cannot be rematerialized
/// from storage after the call.
contract AdversarialStackPressure {
    uint256[32] private values;

    function pressure(address target) external returns (uint256 result) {
        uint256 v00 = values[0];
        uint256 v01 = values[1];
        uint256 v02 = values[2];
        uint256 v03 = values[3];
        uint256 v04 = values[4];
        uint256 v05 = values[5];
        uint256 v06 = values[6];
        uint256 v07 = values[7];
        uint256 v08 = values[8];
        uint256 v09 = values[9];
        uint256 v10 = values[10];
        uint256 v11 = values[11];
        uint256 v12 = values[12];
        uint256 v13 = values[13];
        uint256 v14 = values[14];
        uint256 v15 = values[15];
        uint256 v16 = values[16];
        uint256 v17 = values[17];
        uint256 v18 = values[18];
        uint256 v19 = values[19];
        uint256 v20 = values[20];
        uint256 v21 = values[21];
        uint256 v22 = values[22];
        uint256 v23 = values[23];
        uint256 v24 = values[24];
        uint256 v25 = values[25];
        uint256 v26 = values[26];
        uint256 v27 = values[27];
        uint256 v28 = values[28];
        uint256 v29 = values[29];
        uint256 v30 = values[30];
        uint256 v31 = values[31];

        IPressureTarget(target).ping();

        unchecked {
            result = v00 + v01 + v02 + v03 + v04 + v05 + v06 + v07;
            result += v08 + v09 + v10 + v11 + v12 + v13 + v14 + v15;
            result += v16 + v17 + v18 + v19 + v20 + v21 + v22 + v23;
            result += v24 + v25 + v26 + v27 + v28 + v29 + v30 + v31;
        }
    }
}
