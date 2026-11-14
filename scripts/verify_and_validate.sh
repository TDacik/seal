#!/bin/bash

# Run verification and validate its witness

set -euo pipefail

# Root of SEAL's repository
SEAL_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

INPUT=$1
NAME=$(basename $INPUT)

time $SEAL_ROOT/scripts/seal.py $INPUT $@
time $SEAL_ROOT/scripts/seal.py --validate-witness=witness.yml $INPUT $@

# Store witness
# TODO

rm witness.yml
