if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/tokens/ERC20Harness.sol \
    --verify ERC20Harness:certora/specs/ERC20.spec \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --cloud \
    $RULE \
    --msg "ERC20 verification: $1"