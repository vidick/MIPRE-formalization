#!/bin/bash
# SessionStart hook: expose the Lean 4 + Mathlib environment provisioned by the
# cloud environment's setup script (.claude/cloud-setup.sh) to the session's
# checkout of this repository. Cloud sessions only; local machines are left
# alone. See docs/lean-cloud.md.
set -uo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

WARM=/opt/warm/MIPRE-formalization
HERE="${CLAUDE_PROJECT_DIR:-$(pwd)}"

if ! command -v lake >/dev/null 2>&1 || [ ! -d "$WARM/.lake" ]; then
  echo "lean-warm: no Lean/Mathlib environment on this VM (the cloud environment's setup script has not been applied). Do NOT install Lean or build Mathlib in this session unless the network policy allows the toolchain and cache hosts; see docs/lean-cloud.md."
  exit 0
fi

# The session's checkout reuses the warm clone's dependencies and build outputs;
# Lake rebuilds only the modules whose sources differ.
if [ ! -e "$HERE/.lake" ]; then
  ln -s "$WARM/.lake" "$HERE/.lake"
fi

if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo "export LEAN_PROJECT_PATH=\"$HERE\"" >> "$CLAUDE_ENV_FILE"
fi

installed=$(lean --version 2>/dev/null | sed -e 's/^Lean (version //' -e 's/,.*$//')   # e.g. 4.33.0
wanted=$(sed 's/.*:v//' "$HERE/lean-toolchain")
if [ "$wanted" != "$installed" ]; then
  echo "lean-warm: WARNING this checkout wants Lean $wanted but the snapshot has $installed. Ask the user to re-save the cloud environment's setup script so the cache is rebuilt; until then lake cannot be used here."
  exit 0
fi

# Mathlib only changes when the pin moves, in which case cache get fetches the new
# oleans; nothing is compiled from source except this repository's changed modules.
( cd "$HERE" && lake exe cache get >/dev/null 2>&1 ) || true

echo "lean-warm: Lean ${installed:-?} + Mathlib ready for $HERE (LEAN_PROJECT_PATH). Check modules with 'lake build MIPRE.<Module>' or the lean-lsp MCP tools (scratch files go in Scratch/). Never run lake build on Mathlib and never lake update."
exit 0
