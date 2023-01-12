if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/mixins/ERC4626BalanceOfHarness.sol \
    certora/helpers/DummyERC20A.sol certora/helpers/DummyERC20B.sol \
    --verify ERC4626BalanceOfHarness:certora/specs/ERC4626.spec \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --staging master \
    --rule_sanity \
    --settings -recursionErrorAsAssert=false \
    $RULE \
    --msg "ERC4626 verification: $1"