// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

import {Owned} from "../../../src/auth/Owned.sol";

/// @notice A dummy implementation for an (empty) owned contract
/// @dev The first owner of this contract is the deployer
contract DummyOwned is Owned {
    constructor() Owned(msg.sender) {}
}
