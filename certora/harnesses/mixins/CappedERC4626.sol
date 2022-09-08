// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

import {ERC20} from "../../../src/tokens/ERC20.sol";
import {ERC4626} from "../../../src/mixins/ERC4626.sol";
import {Owned} from "../../../src/auth/Owned.sol";

/// @notice A dummy implementation for the ERC4626 vault standard
/// @dev This contract implements the `totalAssets()` function by accounting 
///      every change to the contract's balance. 
///      The owner can account the accrued rewards using the `accrueRewards()` function.
/// @notice Every user here can deposit `maxDeposit()` on total, 
///         withdrawals aren't subtracted from the deposited balance.
contract DummyERC4626Accounting is ERC4626, Owned {
    constructor(address _asset) 
        ERC4626(ERC20(_asset), "Dummy ERC4626", "DERC4626") 
        Owned(msg.sender) 
    {}

    uint public currentBalance;
    mapping (address => uint256) deposited;

    function afterDeposit(uint256 assets, uint256) internal override {
        deposited[msg.sender] += assets;

        require (deposited[msg.sender] < maxDeposit(msg.sender));
    }

    function maxDeposit(address) public view override returns (uint256) {
        return 100 * 1e18;
    }

    function totalAssets() public view override returns (uint256) {
        return asset.balanceOf(address(this));
    }
}
