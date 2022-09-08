if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/tokens/ERC721Harness.sol \
    --verify ERC721Harness:certora/specs/ERC721.spec \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --cloud \
    $RULE \
    --msg "ERC721 verification: $1"