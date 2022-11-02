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
    
    require e.msg.sender != currentContract;
    require receiver != currentContract;

    require totalSupply() >= asset.balanceOf(currentContract);// that is the initial assumption, maybe should  be verified

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

rule userSolvency(method f) filtered{f-> f.selector != transferFrom(address,address,uint256).selector && f.selector != transfer(address,uint256).selector}
{
    env e;
    calldataarg args;

    address user;
    require user != currentContract && e.msg.sender != currentContract;

    // require totalSupply() >= asset.balanceOf(currentContract);// that is the initial assumption, it breaks when transfer directly to the vault
    uint256 assets = asset.balanceOf(user);
    uint256 shares = balanceOf(user);

        uint assetValueBefore = asset.balanceOf(user) + convertToAssets(balanceOf(user));    
        callContributionMethods(e, f, assets, shares, user);
        uint assetValueAfter  = asset.balanceOf(user) + convertToAssets(balanceOf(user));

    assert assetValueBefore == assetValueAfter;
}

invariant vaultEquilibrium()
    asset.balanceOf(currentContract) >= convertToAssets(totalSupply())


///// help functions
function callContributionMethods(env e, method f, uint256 assets, uint256 shares, address receiver) {
    if (f.selector == deposit(uint256,address).selector) {
        deposit(e, assets, receiver);
    }
    if (f.selector == mint(uint256,address).selector) {
        mint(e, shares, receiver);
    }
    if (f.selector == withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, _);
    }
    if (f.selector == redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, _);
    }
}
