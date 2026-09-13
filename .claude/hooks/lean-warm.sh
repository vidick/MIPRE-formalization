#!/bin/bash
# SessionStart hook: expose the Lean 4 + Mathlib environment provisioned by the
# cloud environment's setup script (.claude/cloud-setup.sh) to the session's
# checkout of this repository, and repair the two things that are cheap to repair
# from inside a session. Cloud sessions only; local machines are left alone.
# See docs/lean-cloud.md.
set -uo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

WARM=/opt/warm/MIPRE-formalization
HERE="${CLAUDE_PROJECT_DIR:-$(pwd)}"
STAMP=/opt/warm/SETUP-STAMP
# Same asset as .claude/cloud-setup.sh; used here only when the snapshot has none.
PREBUILT_URL=${PREBUILT_URL:-https://github.com/vidick/MIPRE-formalization/releases/download/prebuilt-main/mipre-build.tar.zst}

# The pinned Mathlib commit. `rev` sits a few lines above `name` in the manifest,
# so the name has to be found first. Kept identical in .claude/cloud-setup.sh.
mathlib_rev() {
  grep -B4 '"name": "mathlib"' "$1" 2>/dev/null \
    | sed -n 's/.*"rev": "\([0-9a-f]*\)".*/\1/p' | head -1
}

if ! command -v lake >/dev/null 2>&1 || [ ! -d "$WARM/.lake" ]; then
  echo "lean-warm: no Lean/Mathlib environment on this VM (the cloud environment's setup script has not been applied). Do NOT install Lean or build Mathlib in this session unless the network policy allows the toolchain and cache hosts; see docs/lean-cloud.md."
  exit 0
fi

# The session's checkout reuses the warm clone's dependencies and build outputs;
# Lake rebuilds only the modules whose sources differ.
if [ ! -e "$HERE/.lake" ]; then
  ln -s "$WARM/.lake" "$HERE/.lake"
fi

# The scratch directory the docs promise: .gitignore has it, a checkout does not.
mkdir -p "$HERE/Scratch"

if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo "export LEAN_PROJECT_PATH=\"$HERE\"" >> "$CLAUDE_ENV_FILE"
fi

installed=$(lean --version 2>/dev/null | sed -e 's/^Lean (version //' -e 's/,.*$//')   # e.g. 4.33.0
wanted=$(sed 's/.*:v//' "$HERE/lean-toolchain")
if [ "$wanted" != "$installed" ]; then
  echo "lean-warm: WARNING this checkout wants Lean $wanted but the snapshot has $installed. Ask the user to re-save the cloud environment's setup script so the cache is rebuilt; until then lake cannot be used here."
  exit 0
fi

# Mathlib's oleans are in the snapshot already. `lake exe cache get` is only worth
# its time when the pin has actually moved since the snapshot was built.
want_rev=$(mathlib_rev "$HERE/lake-manifest.json")
have_rev=$(sed -n 's/^mathlib: //p' "$STAMP" 2>/dev/null)
[ -n "$have_rev" ] || have_rev=$(mathlib_rev "$WARM/lake-manifest.json")
if [ -n "$want_rev" ] && [ "$want_rev" = "$have_rev" ]; then
  mathlib_note=""
else
  ( cd "$HERE" && lake exe cache get >/dev/null 2>&1 ) || true
  mathlib_note=" Mathlib pin moved since the snapshot, so its oleans were refetched."
fi

# The modules of this repository. A snapshot without them is the difference
# between checking a module in seconds and in 30-45 minutes, so if the setup
# script did not get the bundle in, fetch it here.
built=$(find "$WARM/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)
total=$(( $(find "$HERE/MIPRE" -name '*.lean' 2>/dev/null | wc -l) + 1 ))
if [ "$built" -eq 0 ] && [ -n "$PREBUILT_URL" ]; then
  tmp=$(mktemp -d /opt/warm/.prebuilt.XXXXXX 2>/dev/null)
  if [ -n "$tmp" ] && timeout 300 bash -c \
       'curl -fsSL --retry 1 "$1" | tar --zstd -x -C "$2"' _ "$PREBUILT_URL" "$tmp" 2>/dev/null \
     && [ -d "$tmp/.lake/build" ]; then
    rm -rf "$WARM/.lake/build"
    mv "$tmp/.lake/build" "$WARM/.lake/build"
    built=$(find "$WARM/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)
  fi
  [ -n "$tmp" ] && rm -rf "$tmp"
fi

if [ "$built" -eq 0 ]; then
  warm_note="no MIPRE modules prebuilt and the bundle could not be fetched, so the first build of anything importing the vendored repetition trees will take 30-45 minutes; work in Foundations/TM/LCS (which import only Mathlib) costs seconds either way"
else
  warm_note="$built/$total MIPRE modules prebuilt"
fi

# Is the snapshot still in step with the repository? Two kinds of drift, both
# otherwise invisible until a build is mysteriously slow or a host is refused.
repo_sha=$(sed -n 's/^repo-script-sha256: //p' "$STAMP" 2>/dev/null)
pasted_sha=$(sed -n 's/^pasted-script-sha256: //p' "$STAMP" 2>/dev/null)
here_sha=$(sha256sum "$HERE/.claude/cloud-setup.sh" 2>/dev/null | cut -d' ' -f1)
if [ -n "$repo_sha" ] && [ -n "$here_sha" ] && [ "$repo_sha" != "$here_sha" ]; then
  echo "lean-warm: NOTE .claude/cloud-setup.sh has changed since this snapshot was built. Re-save the environment's setup script (paste the current file) so the snapshot picks it up; see docs/lean-cloud.md."
fi
if [ -n "$pasted_sha" ] && [ -n "$repo_sha" ] && [ "$pasted_sha" != "$repo_sha" ]; then
  echo "lean-warm: NOTE the script pasted into the environment is not the repository's .claude/cloud-setup.sh. Paste the repository's copy so the two cannot drift apart."
fi

echo "lean-warm: Lean ${installed:-?} + Mathlib ready for $HERE (LEAN_PROJECT_PATH); $warm_note.${mathlib_note} Iterate with the lean-lsp MCP tools (lean_diagnostic_messages, lean_goal, lean_multi_attempt): seconds per cycle, and they see edits without a build. Confirm a module with 'lake build MIPRE.<Module>' — seconds when its imports are built. Never a bare 'lake build' (it builds all $total modules), never 'lake build' on Mathlib, never 'lake update', and never 'lake clean' (.lake is shared with the snapshot: it would delete Mathlib's 7.6 GB too). Scratch files go in Scratch/."
exit 0
