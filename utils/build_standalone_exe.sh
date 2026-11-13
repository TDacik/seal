#!/usr/bin/env bash

set -euo pipefail

# Root of SEAL's repository
SEAL_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Output directory is seal-standalone in caller's directory
OUT_DIR="${1:-seal-standalone}"

docker build -t seal_builder:latest -f "$SEAL_ROOT/utils/Dockerfile" "$SEAL_ROOT"
docker rm -f seal_builder 2>/dev/null || true
docker run --name seal_builder seal_builder:latest

mkdir -- "$OUT_DIR"
docker cp seal_builder:/seal/_opam "$OUT_DIR/_opam"
cp "$SEAL_ROOT/scripts/seal.py" "$OUT_DIR/seal.py"

if [[ "$OSTYPE" == "darwin"* ]]; then
    sed -i "" "s/STANDALONE_MODE = False/STANDALONE_MODE = True/g" "$OUT_DIR/seal.py"
else
    sed -i "s/STANDALONE_MODE = False/STANDALONE_MODE = True/g" "$OUT_DIR/seal.py"
fi
