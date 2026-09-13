#!/bin/bash
# Cloud environment SETUP SCRIPT for Claude Code on the web, for sessions on this
# repository (vidick/MIPRE-formalization).
#
# This file is not executed from the repository. Paste its contents into the
# "Setup script" box of the cloud environment at claude.ai/code (cloud icon above
# the message box -> gear on the environment -> Setup script).
#
# Anthropic runs it once, snapshots the VM filesystem, and starts every later
# session from that snapshot, so Lean, a compiled Mathlib and this repository's
# own compiled modules are all on disk at session start. The snapshot is rebuilt
# when the script or the allowed hosts change, or after about seven days.
#
# ---------------------------------------------------------------------------
# Two platform rules this script is written around
# (https://code.claude.com/docs/en/cloud-environments#setup-scripts):
#
#   "Exit zero: if the script exits non-zero, the session fails to start."
#       So every path here ends in `exit 0`. A session with no Lean, which says
#       so at startup, beats an environment in which no session starts at all.
#
#   "Finish within five minutes ... so the environment cache can build."
#       Cloning and the Mathlib olean cache take about 140s of that. Compiling
#       the 533 modules of this repository takes 30 to 45 minutes and therefore
#       CANNOT happen here, whatever BUILD_BUDGET is set to. They are downloaded
#       instead, as a bundle built by CI: see PREBUILT_URL below.
# ---------------------------------------------------------------------------
# Network access = Custom, "Also include default list of common package
# managers" ticked, plus these hosts:
#
#   releases.lean-lang.org            Lean toolchain tarballs
#   release.lean-lang.org             Lean release index
#   lakecache.blob.core.windows.net   Mathlib olean cache (~7 GB unpacked)
#   loogle.lean-lang.org              \
#   leansearch.net                     | lean-lsp-mcp search tools
#   premise-search.com                 |
#   leanpremise.net                   /
#
# GitHub needs nothing added: github.com, codeload.github.com,
# objects.githubusercontent.com and release-assets.githubusercontent.com are all
# in the default list, and GitHub traffic takes a separate proxy that does not
# go through the allowlist at all. That is what makes PREBUILT_URL work: a
# release asset of THIS repository is always reachable.
#
# reservoir.lean-lang.org is deliberately NOT in the list: it is unreachable
# from these VMs, and it is not needed, because lake-manifest.json pins every
# dependency's git URL so Lake never has to resolve a `scope`. The price is that
# `lake update` cannot work here. Never run it (see planning/next-steps.md).
#
# See docs/lean-cloud.md.

set -uo pipefail

REPO=https://github.com/vidick/MIPRE-formalization
BRANCH=${BRANCH:-main}          # the branch whose lean-toolchain and lake-manifest are used
WARM=/opt/warm/MIPRE-formalization
REPORT=/opt/warm/SETUP-REPORT.txt
STAMP=/opt/warm/SETUP-STAMP

# The compiled modules, published by .github/workflows/build-project.yml on every
# push to main: some 250 MB, tens of seconds to fetch, against 30-45 minutes to
# compile the same thing. Empty to skip.
PREBUILT_URL=${PREBUILT_URL:-https://github.com/vidick/MIPRE-formalization/releases/download/prebuilt-main/mipre-build.tar.zst}

# Seconds to spend compiling modules the bundle did not cover (a feature branch
# that changed a Foundations file, say). Keep it small or zero: it is spent out
# of what is left of the five minutes, and .claude/hooks/lean-warm.sh builds what
# a session actually needs anyway.
BUILD_BUDGET=${BUILD_BUDGET:-0}

# Wall-clock this script allows itself, in seconds. The platform's limit is "about
# five minutes"; stopping short of it keeps the snapshot buildable.
DEADLINE=${DEADLINE:-270}

T0=$(date +%s)
mkdir -p /opt/warm
: > "$REPORT"
used() { echo $(( $(date +%s) - T0 )); }
left() { echo $(( DEADLINE - $(used) )); }
log()  { printf '[setup +%4ss] %s\n' "$(used)" "$*" | tee -a "$REPORT"; }

# The pinned Mathlib commit. `rev` sits a few lines above `name` in the manifest,
# so the name has to be found first. Kept identical in .claude/hooks/lean-warm.sh.
mathlib_rev() {
  grep -B4 '"name": "mathlib"' "$1" 2>/dev/null \
    | sed -n 's/.*"rev": "\([0-9a-f]*\)".*/\1/p' | head -1
}

# What this snapshot was built from, so that .claude/hooks/lean-warm.sh can tell a
# session at startup whether the snapshot is still in step with the repository —
# drift that is otherwise invisible until something is slow or broken.
# `pasted-script-sha256` is the text actually pasted into the environment box, when
# the shell lets us read it; `repo-script-sha256` is .claude/cloud-setup.sh as
# committed on BRANCH. Their differing means the pasted copy is not the repo's.
stamp() {
  SELF="${BASH_SOURCE[0]:-$0}"
  {
    echo "built-at: $(date -u +%FT%TZ)"
    echo "branch: $BRANCH"
    echo "commit: $(git -C "$WARM" rev-parse --short HEAD 2>/dev/null)"
    echo "toolchain: ${LEAN:-unknown}"
    echo "mathlib: $(mathlib_rev "$WARM/lake-manifest.json")"
    echo "repo-script-sha256: $(sha256sum "$WARM/.claude/cloud-setup.sh" 2>/dev/null | cut -d' ' -f1)"
    [ -r "$SELF" ] && echo "pasted-script-sha256: $(sha256sum "$SELF" | cut -d' ' -f1)"
    echo "mipre-oleans: $(find "$WARM/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)"
    echo "prebuilt: ${PREBUILT:-none}"
    echo "setup-seconds: $(used)"
  } > "$STAMP"
}
finish() {
  stamp
  chmod -R a+rwX /opt/lean /opt/warm 2>/dev/null || true
  log "done in $(used)s; $(df -h / | awk 'NR==2{print $4}') disk free"
  exit 0                       # always: see "Exit zero" above
}
bail() { log "GIVING UP: $*"; finish; }

# 0. zstd, for the Lean tarball and the prebuilt bundle. Releases also ship
#    .tar.gz, so a missing zstd is not fatal for the toolchain — fall back.
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq          >/dev/null 2>&1 || log "apt-get update failed, continuing"
apt-get install -y -qq zstd >/dev/null 2>&1 || log "could not install zstd, continuing"

# 1. Shallow warm clone. Its lean-toolchain decides the Lean version and its
#    lake-manifest.json decides every dependency commit. The session's own
#    checkout reuses this clone's .lake directory, linked in by
#    .claude/hooks/lean-warm.sh, so keep BRANCH's toolchain equal to the one you
#    will be working on or that hook will refuse the snapshot.
log "cloning $BRANCH"
rm -rf "$WARM"
git clone --depth 1 --branch "$BRANCH" "$REPO" "$WARM" >/dev/null 2>&1 \
  || bail "git clone failed — is github.com allowed?"
LEAN=$(sed 's/.*://' "$WARM/lean-toolchain")
log "toolchain wanted: $LEAN"

# 2. Lean toolchain, straight from the release tarball (no elan: one less moving
#    part, and elan would need the same hosts anyway).
mkdir -p /opt/lean
if command -v zstd >/dev/null 2>&1; then EXT=tar.zst; TARFLAG=--zstd
else                                     EXT=tar.gz;  TARFLAG=-z
fi
CANDIDATES=( "${TOOLCHAIN_URL:-}"
             "https://releases.lean-lang.org/lean4/${LEAN}/lean-${LEAN#v}-linux.${EXT}"
             "https://github.com/leanprover/lean4/releases/download/${LEAN}/lean-${LEAN#v}-linux.${EXT}" )
got=""
for u in "${CANDIDATES[@]}"; do
  [ -n "$u" ] || continue
  log "trying $u"
  if curl -fsSL --retry 2 --retry-delay 3 "$u" \
       | tar "$TARFLAG" -x -C /opt/lean --strip-components=1; then
    got="$u"; break
  fi
  log "  that one failed"
done
[ -n "$got" ] || bail "no toolchain source worked. Allow releases.lean-lang.org; if the failures were 403s from the GitHub proxy, upload lean-${LEAN#v}-linux.${EXT} as a release asset of this repository and set TOOLCHAIN_URL to its URL."
log "toolchain from $got"
ln -sf /opt/lean/bin/lean /opt/lean/bin/lake /usr/local/bin/
export PATH=/opt/lean/bin:$PATH
command -v lake >/dev/null 2>&1 || bail "lake is not on PATH after extraction"
log "installed $(lean --version 2>&1 | head -1)"

# 3. Dependencies at their pinned commits, then Mathlib's compiled oleans from the
#    official cache. Nothing of Mathlib is compiled from source; the one thing
#    built here is Mathlib's own `cache` executable.
cd "$WARM" || bail "cannot enter $WARM"
log "fetching dependencies and the Mathlib olean cache"
lake exe cache get \
  || bail "lake exe cache get failed — allow lakecache.blob.core.windows.net"
log "Mathlib in place: $(find .lake/packages/mathlib/.lake/build/lib -name '*.olean' 2>/dev/null | wc -l) oleans, $(du -sh .lake 2>/dev/null | cut -f1) on disk, $(left)s of the deadline left"

# 4. This repository's own compiled modules, as a bundle. Lake's traces are
#    path-independent, so oleans built on a CI runner are replayed here rather
#    than rebuilt; this is the same trick as `lake exe cache get` itself.
PREBUILT=none
TOTAL=$(( $(find "$WARM/MIPRE" -name '*.lean' 2>/dev/null | wc -l) + 1 ))
if [ -n "$PREBUILT_URL" ] && [ "$(left)" -gt 30 ]; then
  log "fetching the prebuilt module bundle"
  tmp=$(mktemp -d /opt/warm/.prebuilt.XXXXXX)
  if curl -fsSL --retry 1 --max-time "$(left)" "$PREBUILT_URL" \
       | tar --zstd -x -C "$tmp" 2>/dev/null && [ -d "$tmp/.lake/build" ]; then
    rm -rf "$WARM/.lake/build"
    mv "$tmp/.lake/build" "$WARM/.lake/build"
    PREBUILT="$PREBUILT_URL"
    log "bundle in place: $(tr '\n' ' ' < "$WARM/.lake/build/BUNDLE-INFO" 2>/dev/null)"
  else
    log "no usable bundle at $PREBUILT_URL (not published yet, no zstd, or out of time)"
  fi
  rm -rf "$tmp"
fi

# 5. Whatever the bundle did not cover, within what is left of the deadline.
budget=$BUILD_BUDGET
[ "$budget" -gt "$(left)" ] && budget=$(left)
if [ "$budget" -gt 0 ]; then
  log "compiling for at most ${budget}s"
  timeout "$budget" lake build >/tmp/mipre-build.log 2>&1 \
    || grep -E '^error|^[^ ]*\.lean:[0-9]+' /tmp/mipre-build.log 2>/dev/null | head -10 | tee -a "$REPORT"
fi
log "MIPRE modules present: $(find .lake/build/lib -name '*.olean' 2>/dev/null | wc -l) of $TOTAL"

# 6. Pre-fetch lean-lsp-mcp so uvx starts instantly inside sessions. The MCP
#    server is the fast feedback loop — see docs/lean-cloud.md.
uvx lean-lsp-mcp --help >/dev/null 2>&1 || log "uvx prefetch skipped"

finish
