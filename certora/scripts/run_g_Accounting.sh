if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/mixins/ERC4626AccountingHarness.sol \
    certora/helpers/DummyERC20A.sol \
    --verify ERC4626AccountingHarness:certora/specs/gadi.spec \
    --link ERC4626AccountingHarness:asset=DummyERC20A \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --staging \
    $RULE \
    --msg "ERC4626 verification: $1"