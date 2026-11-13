#!/bin/bash

# Run verification and validate its witness

set -euo pipefail

INPUT=$1
NAME=$(basename $INPUT)

time ./scripts/seal.py $INPUT
time frama-c -seal -seal-abstraction=none -seal-svcomp-mode -seal-no-memcleanup -seal-validate-witness=witness.yml $INPUT

# Store witness
# TODO

rm witness.yml
