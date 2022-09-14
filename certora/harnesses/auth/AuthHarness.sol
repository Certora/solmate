// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

import {Authority, Auth} from "../../../src/auth/Auth.sol";

/// More implementations of authorities can be found at "../../auth/authorities"

/// @notice A harness implementation for an Authority
/// @dev This contract is implemented using a mapping of:
///         user => target => functionSig => canCall
contract AuthorityHarness is Authority {
    mapping(address => mapping(address => mapping(bytes4 => bool))) public _canCall;

    function canCall(
        address user,
        address target,
        bytes4 functionSig
    ) external view override returns (bool) {// -> override
        return _canCall[user][target][functionSig];
    }

    function setCanCall(
        address user,
        address target,
        bytes4 functionSig,
        bool value
    ) external {
        _canCall[user][target][functionSig] = value;
    }
}

/// @notice A harness implementation for an Authenticated contract
/// @dev This contract uses the AuthorityHarness contract as an authority
contract AuthHarness is Auth {
    constructor() Auth(msg.sender, new AuthorityHarness()) {}

    fallback() external requiresAuth {}

    function getIsAuthorized(address user, bytes4 functionSig) public view returns (bool) {
        return isAuthorized(user, functionSig);
    }
}