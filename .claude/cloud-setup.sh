#!/bin/bash
# Cloud environment SETUP SCRIPT for Claude Code on the web, for sessions on this
# repository (vidick/MIPRE-formalization).
#
# This file is not executed from the repository. Paste its contents into the
# "Setup script" box of the cloud environment at claude.ai/code (cloud icon
# above the message box -> gear on the environment -> Setup script).
#
# Anthropic runs it once, snapshots the VM filesystem, and starts every later
# session from that snapshot, so Lean and a compiled Mathlib are on disk at
# session start without rebuilding. The script re-runs only when it or the
# environment's allowed hosts change, or after about seven days.
#
# The environment also needs Network access = Custom, with "Also include
# default list of common package managers" ticked and these hosts added:
#   lakecache.blob.core.windows.net    Mathlib olean cache
#   release.lean-lang.org              Lean release index
#   releases.lean-lang.org             Lean toolchain tarballs
#   loogle.lean-lang.org leansearch.net premise-search.com leanpremise.net
#                                      lean-lsp-mcp search tools
#
# Budget: the whole script must finish in about five minutes or the snapshot
# is not built. See docs/lean-cloud.md.
set -euxo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq && apt-get install -y -qq zstd

REPO=https://github.com/vidick/MIPRE-formalization
BRANCH=main                        # the branch whose lean-toolchain and lake-manifest are used
WARM=/opt/warm/MIPRE-formalization

# 1. Shallow warm clone. Its lean-toolchain decides the Lean version and its
#    lake-manifest decides the Mathlib commit; the session's own checkout of the
#    repository reuses the warm clone's .lake directory (see .claude/hooks/lean-warm.sh).
git clone --depth 1 --branch "$BRANCH" "$REPO" "$WARM"
LEAN=$(sed 's/.*://' "$WARM/lean-toolchain")                        # e.g. v4.33.0

# 2. Toolchain tarball.
TOOLCHAIN_URL="https://releases.lean-lang.org/lean4/${LEAN}/lean-${LEAN#v}-linux.tar.zst"
mkdir -p /opt/lean
curl -fsSL "$TOOLCHAIN_URL" | tar --zstd -x -C /opt/lean --strip-components=1
ln -sf /opt/lean/bin/lean /opt/lean/bin/lake /usr/local/bin/

# 3. Dependencies at their pinned commits and the compiled Mathlib from the official
#    olean cache (nothing is compiled from source), then this repository's own modules.
cd "$WARM"
lake exe cache get
lake build MIPRE || true          # drop this line if setup overruns five minutes

chmod -R a+rwX /opt/lean /opt/warm

# 4. Pre-fetch lean-lsp-mcp so uvx starts instantly inside sessions.
uvx lean-lsp-mcp --help >/dev/null 2>&1 || true
