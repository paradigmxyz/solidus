// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Exercises stateful storage encodings and nested dynamic ABI shapes.
contract DynamicStorageSurfaceBox {
    struct Entry {
        uint64 nonce;
        bool enabled;
        bytes payload;
        uint256[] words;
    }

    bytes private blob;
    string private label;
    uint256[][] private rows;
    mapping(bytes32 key => Entry) private entries;

    event BlobChanged(uint256 length, bytes32 digest);
    event EntryChanged(bytes32 indexed key, uint64 nonce, bool enabled);

    function replaceBlob(bytes calldata next, string calldata nextLabel)
        external
        returns (uint256 length, bytes32 digest)
    {
        blob = next;
        label = nextLabel;
        length = blob.length;
        digest = keccak256(blob);
        emit BlobChanged(length, digest);
    }

    function patchBlob(uint256 index, bytes1 value)
        external
        returns (bytes32 digest)
    {
        blob[index] = value;
        return keccak256(blob);
    }

    function blobSnapshot()
        external
        view
        returns (bytes memory current, string memory currentLabel)
    {
        return (blob, label);
    }

    function pushRow(uint256[] calldata values)
        external
        returns (uint256 row, bytes32 digest)
    {
        row = rows.length;
        rows.push();
        uint256[] storage destination = rows[row];
        for (uint256 i; i < values.length; ++i) {
            destination.push(values[i]);
        }
        digest = keccak256(abi.encode(destination));
    }

    function replaceRow(uint256 row, uint256[] calldata values)
        external
        returns (bytes32 digest)
    {
        delete rows[row];
        uint256[] storage destination = rows[row];
        for (uint256 i; i < values.length; ++i) {
            destination.push(values[i]);
        }
        digest = keccak256(abi.encode(destination));
    }

    function rowSnapshot(uint256 row)
        external
        view
        returns (uint256[] memory)
    {
        return rows[row];
    }

    function setEntry(
        bytes32 key,
        uint64 nonce,
        bool enabled,
        bytes calldata payload,
        uint256[] calldata words
    ) external returns (bytes32 digest) {
        Entry storage entry = entries[key];
        entry.nonce = nonce;
        entry.enabled = enabled;
        entry.payload = payload;
        delete entry.words;
        for (uint256 i; i < words.length; ++i) {
            entry.words.push(words[i]);
        }
        digest = keccak256(abi.encode(entry.payload, entry.words));
        emit EntryChanged(key, nonce, enabled);
    }

    function mutateEntry(
        bytes32 key,
        uint256 index,
        uint256 value,
        bytes1 tail
    ) external returns (uint256 length, bytes32 digest) {
        Entry storage entry = entries[key];
        entry.words[index] = value;
        entry.payload.push(tail);
        length = entry.payload.length;
        digest = keccak256(abi.encode(entry.payload, entry.words));
    }

    function entrySnapshot(bytes32 key)
        external
        view
        returns (
            uint64 nonce,
            bool enabled,
            bytes memory payload,
            uint256[] memory words
        )
    {
        Entry storage entry = entries[key];
        return (entry.nonce, entry.enabled, entry.payload, entry.words);
    }

    function nestedHash(uint256[][] calldata values, bytes[] calldata chunks)
        external
        pure
        returns (bytes32)
    {
        return keccak256(abi.encode(values, chunks));
    }
}
