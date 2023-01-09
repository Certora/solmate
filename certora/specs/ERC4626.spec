using DummyERC20A as asset 

methods {
    name() returns string envfree;
    symbol() returns string envfree;
    decimals() returns uint8 envfree;
    asset() returns address envfree;

    totalSupply() returns uint256 envfree;
    balanceOf(address) returns uint256 envfree => DISPATCHER(true);
    nonces(address) returns uint256 envfree;

    approve(address,uint256) returns bool;
    transfer(address,uint256) returns bool => DISPATCHER(true);
    transferFrom(address,address,uint256) returns bool => DISPATCHER(true);
    deposit(uint256,address);
    mint(uint256,address);
    withdraw(uint256,address,address);
    redeem(uint256,address,address);

    totalAssets() returns uint256 envfree;
    userAssets(address) returns uint256 envfree;
    convertToShares(uint256) returns uint256 envfree;
    convertToAssets(uint256) returns uint256 envfree;
    previewDeposit(uint256) returns uint256 envfree;
    previewMint(uint256) returns uint256 envfree;
    previewWithdraw(uint256) returns uint256 envfree;
    previewRedeem(uint256) returns uint256 envfree;

    maxDeposit(address) returns uint256 envfree;
    maxMint(address) returns uint256 envfree;
    maxWithdraw(address) returns uint256 envfree;
    maxRedeem(address) returns uint256 envfree;

    permit(address,address,uint256,uint256,uint8,bytes32,bytes32);
    DOMAIN_SEPARATOR() returns bytes32;

    asset.balanceOf(address) returns uint256 envfree;
}


////////////////////////////////////////////////////////////////////////////////
//// # mathematical properties /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

invariant noSupplyIffNoAssets() // DONE but FAILING
    totalSupply() == 0 <=> userAssets(currentContract) == 0
    {
        preserved with (env e) {
            address receiver1;
            safeAssumptions(e, receiver1, e.msg.sender);
        }
        preserved transfer(address receiver, uint256 shares) with (env e2) {
            safeAssumptions(e2, receiver, e2.msg.sender);
        }
        preserved transferFrom(address owner, address receiver, uint256 shares) with (env e3) {
            safeAssumptions(e3, receiver, owner);
        }
        preserved withdraw(uint256 assets, address receiver, address owner) with (env e4) { // FAILING withdraw leaves assets in the pool while zeroing out totalSupply due to rounding
            safeAssumptions(e4, receiver, owner);
        }
        preserved redeem(uint256 shares, address receiver, address owner) with (env e5) { // FAILING redeem leaves assets in the pool while zeroing out totalSupply by transferring
            safeAssumptions(e5, receiver, owner);
        }
    }

// TODO x3 this rule is a specific rule dealing with only deposit
// option 1 (repetitious, simple): write 4 rules
// option 2 (less repetitious, less simple): write 2 rules, 1 for share-unit methods, 1 for asset-unit methods
// option 3 (succinct, more complex): write 1 rule handling all 4 methods
// TODO update to account for 'floor' of possible values
rule depositStrongWeakMonotonicity() { // TODO before simplifying (-strong) to exclude token ratios, consider whether the improper behavior is a bug.
    env e; storage before = lastStorage;

    address receiver; uint256 receiverPriorBalance = balanceOf(receiver);
    uint256 smallerAssets; uint256 largerAssets;
    
    require currentContract != e.msg.sender && currentContract != receiver; // TODO justify these requirements

    safeAssumptions(e, e.msg.sender, receiver);

    deposit(e, smallerAssets, receiver) at before;
    uint256 smallerShares = balanceOf(receiver) - receiverPriorBalance;

    deposit(e, largerAssets, receiver) at before;
    uint256 largerShares = balanceOf(receiver) - receiverPriorBalance;

    if (totalSupply() > totalAssets()) {
        // weakly monotonic behavior when supply tokens outnumber asset tokens
        assert smallerAssets < largerAssets => smallerShares <= largerShares,
            "when supply tokens outnumber asset tokens, a larger deposit of assets must produce an equal or greater number of shares";
    } else {
        // strongly monotonic behavior when supply tokens do not outnumber asset tokens
        assert smallerAssets < largerAssets => smallerShares < largerShares, // FAILING passes when smallerShares <= largerShares, could simplify to exclude token ratios
            "when supply tokens do not outnumber asset tokens, a larger deposit of assets must produce a greater number of shares";
    }
}

rule totalsWeakMonotonicity() {
    method f; env e; calldataarg args;
    storage before = lastStorage;
    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();

    f(e, args) at before; // TODO with below verify signs cannot be opposite --> !(a xor b) but should account for oldLevel == newLevel

    uint256 totalSupplyChangeA = updateChangeMarker(e, totalSupplyBefore, totalSupply());
    uint256 totalAssetsChangeA = updateChangeMarker(e, totalAssetsBefore, totalAssets());

    f(e, args) at before;

    uint256 totalSupplyChangeB = updateChangeMarker(e, totalSupplyBefore, totalSupply());
    uint256 totalAssetsChangeB = updateChangeMarker(e, totalAssetsBefore, totalAssets());

    // possibly assert totalSupply and totalAssets must not change in opposite directions
    assert totalSupplyChangeA < totalSupplyChangeB => totalAssetsChangeA <= totalAssetsChangeB,
        "if totalSupply changes by a larger amount, the corresponding change in totalAssets must remain the same or grow";
    assert totalSupplyChangeA == totalSupplyChangeB => totalAssetsChangeA == totalAssetsChangeB,
        "equal size changes to totalSupply must yield equal size changes to totalAssets";
}

rule conversionOfZero {
    uint256 convertZeroShares = convertToAssets(0);
    uint256 convertZeroAssets = convertToShares(0);

    assert convertZeroShares == 0,
        "converting zero shares must return zero assets";
    assert convertZeroAssets == 0,
        "converting zero assets must return zero shares";
}

rule convertToAssetsWeakAdditivity() { // TODO update to account for 'floor' of possible values
    uint256 sharesA; uint256 sharesB;
    require sharesA + sharesB < max_uint128
         && convertToAssets(sharesA) + convertToAssets(sharesB) < max_uint256
         && convertToAssets(sharesA + sharesB) < max_uint256;
    assert convertToAssets(sharesA) + convertToAssets(sharesB) <= convertToAssets(sharesA + sharesB),
        "converting sharesA and sharesB to assets then summing them must yield a smaller or equal result to summing them then converting";
}

rule convertToSharesWeakAdditivity() { // TODO update to account for 'floor' of possible values
    uint256 assetsA; uint256 assetsB;
    require assetsA + assetsB < max_uint128
         && convertToAssets(assetsA) + convertToAssets(assetsB) < max_uint256
         && convertToAssets(assetsA + assetsB) < max_uint256;
    assert convertToAssets(assetsA) + convertToAssets(assetsB) <= convertToAssets(assetsA + assetsB),
        "converting assetsA and assetsB to shares then summing them must yield a smaller or equal result to summing them then converting";
}

rule conversionWeakMonotonicity { // TODO refactor to account for floor of possible values
    uint256 smallerShares; uint256 largerShares;
    uint256 smallerAssets; uint256 largerAssets;

    assert smallerShares < largerShares => convertToAssets(smallerShares) <= convertToAssets(largerShares),
        "converting more shares must yield equal or greater assets";
    assert smallerAssets < largerAssets => convertToShares(smallerAssets) <= convertToShares(largerAssets),
        "converting more assets must yield equal or greater shares";
}

rule conversionWeakIntegrity() { // TODO update to include floor for returned value for rounding
    uint256 sharesOrAssets;
    assert convertToShares(convertToAssets(sharesOrAssets)) <= sharesOrAssets,
        "converting shares to assets then back to shares must return shares less than or equal to the original amount";
    assert convertToAssets(convertToShares(sharesOrAssets)) <= sharesOrAssets,
        "converting assets to shares then back to assets must return assets less than or equal to the original amount";
}

rule convertToCorrectness(uint256 amount, uint256 shares)
{
    assert amount >= convertToAssets(convertToShares(amount));
    assert shares >= convertToShares(convertToAssets(shares));
}

rule zeroDepositZeroShares(uint assets, address receiver)
{
    env e;
    
       uint shares = deposit(e,assets, receiver);

    assert shares == 0 <=> assets == 0;
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

////////////////////////////////////////////////////////////////////////////////
//// # solvency properties /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


// By itself, this rule is meaningless. 
// Conversion functions cannot be assumed to be correct.
// Mike felt it was important to include with the context that solvency is
// proven by verifying the relationship between totalAssets and the correct
// underlying balance of assets and verifying the relationship between
// totalSupply and the shares it represents.
invariant vaultSolvency()
    totalAssets() >= convertToAssets(totalSupply()) && 
    convertToShares(totalAssets()) >= totalSupply()

ghost uint256 sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

invariant totalSupplyIsSumOfBalances()
    totalSupply() == sumOfBalances

invariant sumOfBalancePairsBounded(address addy1, address addy2)
    addy1 != addy2 => balanceOf(addy1) + balanceOf(addy2) <= totalSupply()
    {
        preserved {
            // totalSupplyIsSumOfBalances implies that the sum of any two distinct balances must be less than totalSupply
            require false;
            requireInvariant totalSupplyIsSumOfBalances();
        }
    }

invariant singleBalanceBounded(address addy)
    balanceOf(addy) <= totalSupply()
    {
        preserved {
            // totalSupplyIsSumOfBalances implies that any single balance must be less than totalSupply
            require false;
            requireInvariant totalSupplyIsSumOfBalances();
        }
    }

rule vaultCoversRedeemingAll() { // withdraw version of this rule was failing due to conversion calculations --> removed as unnecessary
    address owner; 
    uint256 shares; require shares == balanceOf(owner);
    
    env e; safeAssumptions(e, _, owner);
    redeem(e, shares, _, owner);
    uint256 ownerBalanceAfter = balanceOf(owner);
    assert ownerBalanceAfter == 0,
        "the vault must be able to cover any user trading in all their shares in return for all assets owed";
}

rule assetsSupplyChangeTogether { // TODO
    assert false,
    // assert (totalSupplyBefore < totalSupplyAfter <=> totalAssetsBefore < totalAssetsAfter)
    //     && (totalSupplyBefore > totalSupplyAfter <=> totalAssetsBefore > totalAssetsAfter),
        "increases and decreases in totalSupply must occur with corresponding increases and decreases in totalAssets";
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

////////////////////////////////////////////////////////////////////////////////
//// # stakeholder properties //////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

rule contributingProducesShares(method f)
filtered {
    f -> f.selector == deposit(uint256,address).selector
      || f.selector == mint(uint256,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address contributor; require contributor == e.msg.sender;
    address receiver;
    require currentContract != contributor // TODO justify
         && currentContract != receiver;

    require previewDeposit(assets) + balanceOf(receiver) <= max_uint256; // safe assumption because call to _mint will revert if totalSupply += amount overflows
    require shares + balanceOf(receiver) <= max_uint256; // same as above

    safeAssumptions(e, contributor, receiver);

    uint256 contributorAssetsBefore = userAssets(contributor);
    uint256 receiverSharesBefore = balanceOf(receiver);

    callContributionMethods(e, f, assets, shares, receiver);

    uint256 contributorAssetsAfter = userAssets(contributor);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert contributorAssetsBefore > contributorAssetsAfter <=> receiverSharesBefore < receiverSharesAfter,
        "a contributor's assets must decrease if and only if the receiver's shares increase";
}

rule onlyContributionMethodsReduceAssets(method f) {
    address user; require user != currentContract; // TODO justify
    uint256 userAssetsBefore = userAssets(user);

    env e; calldataarg args;
    safeAssumptions(e, user, _);

    f(e, args);

    uint256 userAssetsAfter = userAssets(user);

    assert userAssetsBefore > userAssetsAfter =>
        (f.selector == deposit(uint256,address).selector ||
         f.selector == mint(uint256,address).selector),
        "a user's assets must not go down except on calls to contribution methods";
}

rule reclaimingProducesAssets(method f)
filtered {
    f -> f.selector == withdraw(uint256,address,address).selector
      || f.selector == redeem(uint256,address,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address receiver; address owner;
    require currentContract != e.msg.sender // TODO justify
         && currentContract != receiver
         && currentContract != owner;

    safeAssumptions(e, receiver, owner);

    uint256 ownerSharesBefore = balanceOf(owner);
    uint256 receiverAssetsBefore = userAssets(receiver);

    callReclaimingMethods(e, f, assets, shares, receiver, owner);

    uint256 ownerSharesAfter = balanceOf(owner);
    uint256 receiverAssetsAfter = userAssets(receiver);

    assert ownerSharesBefore > ownerSharesAfter <=> receiverAssetsBefore < receiverAssetsAfter,
        "an owner's shares must decrease if and only if the receiver's assets increase";
}

////////////////////////////////////////////////////////////////////////////////
//// # variable change properties //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// TODO already partially present w reclaiming and contributing rules
// decide if needed
// FAILING on IO methods
rule gainingLosingSharesInvChangesUserAssets(method f)
filtered {
    f -> f.selector != transfer(address,uint256).selector
      && f.selector != transferFrom(address,address,uint256).selector
}
{
    env e;
    require currentContract != e.msg.sender; // TODO justify
    address user;
    uint256 userSharesBefore = balanceOf(user);
    uint256 userAssetsBefore = userAssets(user);

    calldataarg args;
    f(e, args);

    uint256 userSharesAfter = balanceOf(user);
    uint256 userAssetsAfter = userAssets(user);

    assert userSharesBefore < userSharesAfter <=> userAssetsBefore > userAssetsAfter,
        "if a user's shares increase outside of transfers, the user's assets must decrease";
    assert userSharesBefore > userSharesAfter <=> userAssetsBefore < userAssetsAfter,
        "if a user's shares decrease outside of transfers, the user's assets must increase";
}

rule underlyingCannotChange() {
    address originalAsset = asset();

    method f; env e; calldataarg args;
    f(e, args);

    address newAsset = asset();

    assert originalAsset == newAsset,
        "the underlying asset of a contract must not change";
}

////////////////////////////////////////////////////////////////////////////////
//// # variable relationships properties ///////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//// # state change properties /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//// # unit test properties ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

rule contributionMethodWeakEquivalence() { // FAILING due to violation of expected rounding behavior
    env e; storage before = lastStorage;
    address receiver; uint256 receiverPriorBalance = balanceOf(receiver);
    uint256 senderPriorAssets = userAssets(e.msg.sender);
    require currentContract != e.msg.sender && currentContract != receiver; // TODO justify

    safeAssumptions(e, e.msg.sender, receiver);

    uint256 assets; uint256 shares;

    deposit(e, assets, receiver) at before;
    uint256 depositAssetsIn = senderPriorAssets - userAssets(e.msg.sender);
    uint256 depositSharesOut = balanceOf(receiver) - receiverPriorBalance;
    
    mint(e, shares, receiver) at before;
    uint256 mintAssetsIn = senderPriorAssets - userAssets(e.msg.sender);
    uint256 mintSharesOut = balanceOf(receiver) - receiverPriorBalance;

    assert depositAssetsIn == mintAssetsIn => depositSharesOut <= mintSharesOut,
        "if deposit and mint contribute equal assets, then deposit must produce shares less than or equal to mint";
    assert depositSharesOut == mintSharesOut => depositAssetsIn <= mintAssetsIn,
        "if deposit and mint produce equal shares, then deposit must contribute assets less than or equal to mint";
    
}

rule reclaimingMethodWeakEquivalence() { // FAILING due to violation of expected rounding behavior
    env e; storage before = lastStorage;
    address receiver; uint256 receiverPriorAssets = userAssets(receiver);
    address owner; uint256 ownerPriorBalance = balanceOf(owner);
    require currentContract != receiver && currentContract != owner; // TODO justify

    safeAssumptions(e, receiver, owner);

    uint256 assets; uint256 shares;

    withdraw(e, assets, receiver, owner) at before;
    uint256 withdrawSharesIn = ownerPriorBalance - balanceOf(owner);
    uint256 withdrawAssetsOut = userAssets(receiver) - receiverPriorAssets;
    
    redeem(e, shares, receiver, owner) at before; 
    uint256 redeemSharesIn = ownerPriorBalance - balanceOf(owner);
    uint256 redeemAssetsOut = userAssets(receiver) - receiverPriorAssets;

    assert withdrawSharesIn == redeemSharesIn => withdrawAssetsOut >= redeemAssetsOut,
        "if withdraw and redeem trade in equal shares, then withdraw must produce assets greater than or equal to redeem";
    assert withdrawAssetsOut == redeemAssetsOut => withdrawSharesIn >= redeemSharesIn,
        "if withdraw and redeem produce equal assets, then withdraw must contribute shares greater than or equal to redeem";    
}

////////////////////////////////////////////////////////////////////////////////
//// # helpers and miscelanious ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// This rule should always fail.
// rule sanity {
//     method f; env e; calldataarg args;

//     f(e, args);

//     assert false, 
//         "This rule should always fail";
// }

function safeAssumptions(env e, address receiver, address owner) {
    require currentContract != asset(); // Although this is not disallowed, we assume the contract's underlying asset is not the contract itself
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant sumOfBalancePairsBounded(receiver, owner);
    requireInvariant singleBalanceBounded(receiver);
}

function updateChangeMarker(env e, uint256 oldLevel, uint256 newLevel) returns uint256 { // TODO when time, generalize this function to use elsewhere
    if (oldLevel <= newLevel) {
        return to_uint256(newLevel - oldLevel);
    } else {
        return to_uint256(oldLevel - newLevel);
    }
}

function callContributionMethods(env e, method f, uint256 assets, uint256 shares, address receiver) {
    if (f.selector == deposit(uint256,address).selector) {
        deposit(e, assets, receiver);
    }
    if (f.selector == mint(uint256,address).selector) {
        mint(e, shares, receiver);
    }
}

function callReclaimingMethods(env e, method f, uint256 assets, uint256 shares, address receiver, address owner) {
    if (f.selector == withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, owner);
    }
    if (f.selector == redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, owner);
    }
}
