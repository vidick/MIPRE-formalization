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

# Is the snapshot still in step with the repository? Two kinds of drift, both
# otherwise invisible until a build is mysteriously slow or a host is refused.
STAMP=/opt/warm/SETUP-STAMP
repo_sha=$(sed -n 's/^repo-script-sha256: //p' "$STAMP" 2>/dev/null)
pasted_sha=$(sed -n 's/^pasted-script-sha256: //p' "$STAMP" 2>/dev/null)
here_sha=$(sha256sum "$HERE/.claude/cloud-setup.sh" 2>/dev/null | cut -d' ' -f1)
if [ -n "$repo_sha" ] && [ -n "$here_sha" ] && [ "$repo_sha" != "$here_sha" ]; then
  echo "lean-warm: NOTE .claude/cloud-setup.sh has changed since this snapshot was built. Re-save the environment's setup script (paste the current file) so the snapshot picks it up; see docs/lean-cloud.md."
fi
if [ -n "$pasted_sha" ] && [ -n "$repo_sha" ] && [ "$pasted_sha" != "$repo_sha" ]; then
  echo "lean-warm: NOTE the script pasted into the environment is not the repository's .claude/cloud-setup.sh. Paste the repository's copy so the two cannot drift apart."
fi

# How much is prebuilt decides whether checking a module costs seconds or an hour.
built=$(find "$WARM/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)
total=$(( $(find "$HERE/MIPRE" -name '*.lean' 2>/dev/null | wc -l) + 1 ))
if [ "$built" -eq 0 ]; then
  warm_note="no MIPRE modules prebuilt, so the first build of one importing the vendored repetition trees will take 20-40 minutes: prefer the lean-lsp MCP tools, and raise BUILD_BUDGET in the setup script"
else
  warm_note="$built/$total MIPRE modules prebuilt"
fi

echo "lean-warm: Lean ${installed:-?} + Mathlib ready for $HERE (LEAN_PROJECT_PATH); $warm_note. Iterate with the lean-lsp MCP tools (lean_diagnostic_messages, lean_goal, lean_multi_attempt) — seconds per cycle, against minutes for lake build; confirm with 'lake build MIPRE.<Module>', never a bare 'lake build', never on Mathlib, and never 'lake update'. Scratch files go in Scratch/."
exit 0
