#!/usr/bin/env bash
# Bump the project to a new Lean/Mathlib release, e.g.:
#
#   ./scripts/update.sh v4.33.0
#
# Updates lean-toolchain and the pinned mathlib and doc-gen4 revisions in
# lakefile.toml together (they must always match), then re-resolves
# dependencies. Review and commit the resulting changes.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: $0 <lean4-release-tag>   (e.g. $0 v4.33.0)" >&2
  exit 1
fi
TAG="$1"

cd "$(dirname "$0")/.."

echo "leanprover/lean4:${TAG}" > lean-toolchain
sed -i.bak -E "s/^rev = \"v[0-9][^\"]*\"/rev = \"${TAG}\"/" lakefile.toml && rm -f lakefile.toml.bak

lake update mathlib «doc-gen4»
lake exe cache get
lake build
