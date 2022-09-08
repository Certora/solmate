if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/tokens/ERC1155Harness.sol \
    --verify ERC1155Harness:certora/specs/ERC1155.spec \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --cloud \
    $RULE \
    --msg "ERC1155 verification: $1"