#!/bin/bash
# Cloud environment SETUP SCRIPT for Claude Code on the web, for sessions on this
# repository (vidick/MIPRE-formalization).
#
# This file is not executed from the repository. Paste its contents into the
# "Setup script" box of the cloud environment at claude.ai/code (cloud icon above
# the message box -> gear on the environment -> Setup script).
#
# Anthropic runs it once, snapshots the VM filesystem, and starts every later
# session from that snapshot, so Lean, a compiled Mathlib and (as far as the
# budget below reaches) this repository's own modules are on disk at session
# start. The snapshot is rebuilt when the script or the allowed hosts change, or
# after about seven days.
#
# ---------------------------------------------------------------------------
# Network access = Custom, "Also include default list of common package
# managers" ticked, plus these hosts:
#
#   github.com                            every Lake dependency; the manifest
#                                         pins 15 git URLs, all on github.com
#   release-assets.githubusercontent.com  where the Lean tarball's bytes really
#                                         come from (~575 MB)
#   objects.githubusercontent.com         the older name of the same thing,
#                                         still served for some releases
#   releases.lean-lang.org                302s to github.com, which 302s again
#                                         to the two hosts above
#   release.lean-lang.org                 Lean release index
#   lakecache.blob.core.windows.net       Mathlib olean cache (~7 GB unpacked)
#   loogle.lean-lang.org                  \
#   leansearch.net                         | lean-lsp-mcp search tools
#   premise-search.com                     |
#   leanpremise.net                       /
#
# The redirect targets are the part that is easy to miss: allowing only
# releases.lean-lang.org lets the request start and then fails on the hop that
# carries the payload, so the toolchain never lands and nothing afterwards works.
#
# reservoir.lean-lang.org is deliberately NOT in that list: it is unreachable
# from these VMs, and it is not needed, because lake-manifest.json pins every
# dependency's git URL so Lake never has to resolve a `scope`. The price is that
# `lake update` cannot work here. Never run it (see planning/next-steps.md).
# ---------------------------------------------------------------------------
#
# Time. The expensive steps are the Mathlib olean cache (a few minutes) and
# building this repository (30 to 45 minutes for all 533 modules, most of it the
# two vendored repetition trees). BUILD_BUDGET below caps the build so the script
# always exits cleanly instead of being killed: Lake keeps every module it
# finished, so a partial build is still a win, and nothing is lost by lowering it.
# Raise it once you know how long this environment lets a setup script run.
#
# See docs/lean-cloud.md.

set -uo pipefail

REPO=https://github.com/vidick/MIPRE-formalization
BRANCH=${BRANCH:-main}          # the branch whose lean-toolchain and lake-manifest are used
WARM=/opt/warm/MIPRE-formalization
REPORT=/opt/warm/SETUP-REPORT.txt

# Seconds to spend pre-building this repository's own modules.
#     0  skip it. Setup is then only a few minutes, but the first in-session
#        build of any module importing the vendored trees costs 20-40 minutes.
#  1200  ~20 min: Foundations, TM, LCS, Cost and the LIDT bridge, typically.
#  2700  ~45 min: everything, including the vendored repetition trees.
BUILD_BUDGET=${BUILD_BUDGET:-1200}

T0=$(date +%s)
mkdir -p /opt/warm
: > "$REPORT"
log() { printf '[setup +%5ss] %s\n' "$(( $(date +%s) - T0 ))" "$*" | tee -a "$REPORT"; }
die() { log "FATAL: $*"; exit 1; }

# 0. zstd, for the Lean tarball. Releases also ship .tar.gz, so a missing zstd
#    is not fatal — fall back rather than abort.
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
  || die "git clone failed — is github.com allowed?"
LEAN=$(sed 's/.*://' "$WARM/lean-toolchain")
log "toolchain wanted: $LEAN"

# 2. Lean toolchain, straight from the release tarball (no elan: one less moving
#    part, and elan would need the same hosts anyway).
mkdir -p /opt/lean
if command -v zstd >/dev/null 2>&1; then EXT=tar.zst; TARFLAG=--zstd
else                                     EXT=tar.gz;  TARFLAG=-z
fi
# Tried in order. Both public ones end at a GitHub release asset of
# leanprover/lean4, and the cloud GitHub proxy only serves release assets of
# repositories attached to the session — so if both 403, upload the tarball as a
# release asset of THIS repository and set TOOLCHAIN_URL to it.
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
[ -n "$got" ] || die "no toolchain source worked. If these were 403s, the GitHub proxy is refusing leanprover/lean4's release assets: upload lean-${LEAN#v}-linux.${EXT} as a release asset of this repository and set TOOLCHAIN_URL to its URL. If they were connection errors, allow github.com and release-assets.githubusercontent.com."
log "toolchain from $got"
ln -sf /opt/lean/bin/lean /opt/lean/bin/lake /usr/local/bin/
export PATH=/opt/lean/bin:$PATH
command -v lake >/dev/null 2>&1 || die "lake is not on PATH after extraction"
log "installed $(lean --version 2>&1 | head -1)"

# 3. Dependencies at their pinned commits, then Mathlib's compiled oleans from the
#    official cache. Nothing of Mathlib is compiled from source; the one thing
#    built here is Mathlib's own `cache` executable.
cd "$WARM" || die "cannot enter $WARM"
log "fetching dependencies and the Mathlib olean cache"
lake exe cache get \
  || die "lake exe cache get failed — allow github.com and lakecache.blob.core.windows.net"
log "Mathlib in place: $(find .lake/packages/mathlib/.lake/build/lib -name '*.olean' 2>/dev/null | wc -l) oleans, $(du -sh .lake 2>/dev/null | cut -f1) on disk"

# 4. This repository's own modules, best effort within the budget. `lake build`
#    uses the default target, the whole MIPRE library.
if [ "${BUILD_BUDGET}" -gt 0 ]; then
  log "pre-building MIPRE with a ${BUILD_BUDGET}s budget"
  if timeout "${BUILD_BUDGET}" lake build >/tmp/mipre-build.log 2>&1; then
    log "MIPRE built in full"
  else
    # A budget stop is expected and harmless; a real error is not, so show it.
    log "build did not complete; everything that finished is cached. Tail:"
    grep -E '^error|^[^ ]*\.lean:[0-9]+' /tmp/mipre-build.log 2>/dev/null | head -15 | tee -a "$REPORT"
  fi
fi
log "MIPRE modules built: $(find .lake/build/lib -name '*.olean' 2>/dev/null | wc -l) of 533"

# 5. Pre-fetch lean-lsp-mcp so uvx starts instantly inside sessions. The MCP
#    server is the fast feedback loop — see docs/lean-cloud.md.
uvx lean-lsp-mcp --help >/dev/null 2>&1 || log "uvx prefetch skipped"

chmod -R a+rwX /opt/lean /opt/warm 2>/dev/null || true
log "done in $(( $(date +%s) - T0 ))s; $(df -h / | awk 'NR==2{print $4}') disk free"
exit 0
