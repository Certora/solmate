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
    convertToShares(uint256) returns uint256 envfree
    
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

rule dustFavorsTheHouse(uint assetsIn, address receiver, address owner)
{
    env e;
        
    require e.msg.sender != currentContract && receiver != currentContract;

    require totalSupply() != 0;

        uint balanceBefore = asset.balanceOf(currentContract);

        uint shares = deposit(e,assetsIn, receiver);
        uint assetsOut = redeem(e,shares,receiver,owner);

        uint balanceAfter = asset.balanceOf(currentContract);

    assert balanceAfter >= balanceBefore;
}

rule zeroDepositZeroShares(uint assets, address receiver)
{
    env e;
    
       uint shares = deposit(e,assets, receiver);

    assert shares == 0 <=> assets == 0;
}

// Can the loss be more than double ?
rule lossLimit(uint assetsIn, address receiver, address owner)
{
    env e;
    
    require e.msg.sender != currentContract;
    require assetsIn >= 1000;

        uint shares = deposit(e,assetsIn, receiver);
        uint assetsOut = redeem(e,shares,receiver,owner);

    assert  assetsIn <= assetsOut * 2;
}

// Can the gain be more than double ?
rule gainLimit(uint assetsIn, address receiver, address owner)
{
    env e;
        
    require e.msg.sender != currentContract;
    require assetsIn >= 1000;
    // require totalSupply() != 0; // no gain in this case

        uint shares = deposit(e,assetsIn, receiver);
        uint assetsOut = redeem(e,shares,receiver,owner);

    assert  assetsIn  * 2 >= assetsOut;
}

// 
rule convertToCorrectness(uint256 amount, uint256 shares)
{
    assert amount >= convertToAssets(convertToShares(amount));
    assert shares >= convertToShares(convertToAssets(shares));
}

rule userSolvency(method f, address user)
filtered{f-> f.selector != transferFrom(address,address,uint256).selector && f.selector != transfer(address,uint256).selector}
{
    env e;
    calldataarg args;

    require user != currentContract && e.msg.sender != currentContract;
    require totalSupply() != 0; // start with non zero supply
    require balanceOf(user) <= totalSupply(); // avoid counter example

    uint256 assets = asset.balanceOf(user);
    uint256 shares = balanceOf(user);
    
    uint256 valueOfOneShare = convertToAssets(1); require valueOfOneShare != 0;

    // The combined value of user's assets in terms of the underlying asset
        mathint assetValueBefore = asset.balanceOf(user) + balanceOf(user) * valueOfOneShare;// convertToAssets(balanceOf(user));    
        // callContributionMethods(e, f, assets, shares, user);
        deposit(e,assets, user);
        mathint assetValueAfter  = asset.balanceOf(user) + convertToAssets(balanceOf(user));

    assert assetValueBefore <= assetValueAfter + valueOfOneShare * 2;
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
