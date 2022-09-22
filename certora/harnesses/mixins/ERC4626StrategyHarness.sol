// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

import {ERC20} from "../../../src/tokens/ERC20.sol";
import {ERC4626} from "../../../src/mixins/ERC4626.sol";
import {Owned} from "../../../src/auth/Owned.sol";

interface IStrategy {
    function deposit(uint amount) external;
    function withdraw(uint amount) external;
    function totalAssets() external view returns (uint);
}

/// @notice A harness implementation for the ERC4626 vault standard
/// @dev    This contract implements the afterDeposit and beforeWithdraw functions
///         by depositing and withdrawing from a strategy. 
///         The value returned by the totalAssets function is the value of strategy.totalAssets().
contract ERC4626AccountingHarness is ERC4626, Owned {

    IStrategy strategy;

    constructor(address _asset, address _strategy) 
        ERC4626(ERC20(_asset), "ERC4626 Harness", "ERC4626H") 
        Owned(msg.sender) 
    {
        strategy = IStrategy(_strategy);
    }

    function beforeWithdraw(uint256 assets, uint256) internal override {
        /// Withdraw from strategy
        strategy.withdraw(assets);
    }

    function afterDeposit(uint256 assets, uint256) internal override {
        /// First approve zero and than approve the needed amount
        uint _allowance = asset.allowance(address(this), address(strategy));
        if (_allowance < assets) {
            if (_allowance > 0) {
                asset.approve(address(strategy), 0);
            }
            asset.approve(address(strategy), type(uint256).max);
        }

        /// Deposit to strategy
        strategy.deposit(assets);
    }

    function totalAssets() public view override returns (uint256) {
        return strategy.totalAssets();
    }
}

contract StrategyHarness is IStrategy {
    ERC20 asset;
    ERC4626 vault;
    address owner;

    modifier onlyVault() {
        require(msg.sender == address(vault), "Not authorized");

        _;
    }

    constructor (address _asset, address _vault) {
        asset = ERC20(_asset);
        vault = ERC4626(_vault);
        owner = msg.sender;
    }

    bool deposited;

    function deposit(uint amount) onlyVault external {
        asset.transferFrom(msg.sender, address(this), amount);

        // invest
    }

    function withdraw(uint amount) onlyVault external {
        // remove investment

        asset.transfer(msg.sender, amount);
    }

    function totalAssets() external view returns (uint) {
        return asset.balanceOf(address(this));
    }

    function sweep(ERC20 token, uint256 amount) external {
        require(msg.sender == owner, "Only owner");
        token.transfer(msg.sender, amount);
    }
}