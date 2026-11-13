#!/usr/bin/env bash

set -euo pipefail

docker build -t seal_builder:latest .
docker rm -f seal_builder 2>/dev/null || true
docker run --name seal_builder seal_builder:latest
docker cp seal_builder:/seal/_opam _opam
