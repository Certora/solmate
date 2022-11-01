using DummyERC20A as asset 


methods {
    // ERC20 Logic
    approve(address, uint256) returns bool
    transfer(address, uint256) returns bool
    transferFrom(address, address, uint256) returns bool
    // EIP-2612 Logic
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32)
    DOMAIN_SEPARATOR() returns bytes32
    computeDomainSeparator() returns bytes32
    // Harness Methods
    mint(address, uint) 
    burn(address, uint)
    // ERC20 Storage
    balanceOf(address) returns uint256 envfree
    allowance(address, address) returns uint256 envfree
    totalSupply() returns uint256 envfree

    convertToAssets(uint256) returns uint256 envfree
    
    asset.balanceOf(address) returns uint256 envfree
}


ghost mathint sumOfBalances { // mathint caused negative value counterexamples
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

rule sumOfAllBalancesIsConstant(method f)
{
    env e;
    calldataarg args;

    uint totalBalancesBefore = asset.totalSupply(e);

    f(e,args);

    uint totalBalancesAfter = asset.totalSupply(e);

    assert totalBalancesBefore == totalBalancesAfter;
}

rule dustFavorsTheHouse()
{
    env e;
    
    uint assets1; address receiver; address owner;
    
    require e.msg.sender != currentContract && e.msg.sender != asset;
    require receiver != currentContract && receiver != asset;

    uint balanceBefore = asset.balanceOf(currentContract);

    uint shares = deposit(e,assets1, receiver);
    uint assets2= redeem(e,shares,receiver,owner);

    uint balanceAfter = asset.balanceOf(currentContract);

    assert balanceAfter >= balanceBefore;
}

rule zeroDepositZeroShares()
{
    env e;

    uint assets; address receiver; uint shares;
    shares = deposit(e,assets, receiver);

    assert shares == 0 <=> assets == 0;
}

rule userSolvency(method f)
{
    env e;
    calldataarg args;

    address user;
    require user != currentContract && user != asset;


    uint assetValueBefore = asset.balanceOf(user) + convertToAssets(balanceOf(user));
    f(e,args);
    uint assetValueAfter  = asset.balanceOf(user) + convertToAssets(balanceOf(user));

    assert assetValueBefore == assetValueAfter;
}

invariant vaultEquilibrium()
    asset.balanceOf(currentContract) == convertToAssets(totalSupply())
