# Lean 4 + Mathlib in cloud sessions

Cloud sessions of Claude Code on the web start in a fresh VM (about 4 vCPU,
16 GB of memory, 30 GB of disk) whose default network policy does not reach the
Lean release server or the Mathlib olean cache, and in which compiling Mathlib
from source never finishes. Without preparation, the only way to check Lean
code from such a session is a CI run of 35 to 40 minutes per attempt.

## How it works

Cloud environments snapshot the VM filesystem after the environment's **setup
script** has run once, and start every later session from that snapshot. The
setup script kept in [`.claude/cloud-setup.sh`](../.claude/cloud-setup.sh)
installs:

| What | Where |
| --- | --- |
| Lean toolchain (`lean`, `lake`), version taken from this repository's `lean-toolchain` | `/opt/lean`, symlinked into `/usr/local/bin` |
| A warm clone of this repository with the Lake dependencies, the Mathlib olean cache and the built `MIPRE` modules | `/opt/warm/MIPRE-formalization` |
| lean-lsp-mcp, pre-fetched | the uv cache |

Nothing is compiled from source except this repository's own modules; Mathlib
comes from the official olean cache. The snapshot is rebuilt only when the setup
script or the allowed hosts change, or after about seven days.

Per session, the SessionStart hook
[`.claude/hooks/lean-warm.sh`](../.claude/hooks/lean-warm.sh) links the warm
clone's `.lake` directory into the session's checkout, so that `lake build`
there rebuilds only the modules whose sources differ, exports
`LEAN_PROJECT_PATH`, and refreshes the Mathlib cache if the pin moved.
[`.mcp.json`](../.mcp.json) starts the `lean-lsp` MCP server against the
checkout, so the agent has goal states, diagnostics, `lean_run_code`, Loogle and
LeanSearch available.

## One-time configuration on claude.ai

1. Open [claude.ai/code](https://claude.ai/code), click the cloud icon showing
   the environment name above the message box, hover the environment and click
   its gear, or choose **Add cloud environment**.
2. **Network access**: Custom, tick *Also include default list of common
   package managers*, and add:

   ```text
   lakecache.blob.core.windows.net
   release.lean-lang.org
   releases.lean-lang.org
   loogle.lean-lang.org
   leansearch.net
   premise-search.com
   leanpremise.net
   ```

3. **Setup script**: paste the contents of `.claude/cloud-setup.sh`, adjusting
   `BRANCH` if the toolchain of a feature branch differs from `main`.
4. Save. The first session in the environment runs the script (a few minutes);
   later sessions start from the snapshot.

The warm tree is about 8 GB on disk (the Mathlib cache alone is 7.6 GB). Do not
enable lean-lsp-mcp's local Loogle (13 GiB peak).

## Using Lean from a session

* Check a module: `lake build MIPRE.Foundations.Compression` (only its
  dependencies are built).
* Standalone snippets: `lean_run_code` with `import Mathlib`, plus
  `import MIPRE.<Module>` for definitions from this repository.
* Scratch files: write them under `Scratch/` (ignored by git) and use the
  file-based tools, or `lake env lean Scratch/Foo.lean`.
* Never run `lake build` on Mathlib and never `lake update`; both would try to
  compile Mathlib and will not finish on the VM.
* When the network policy allows the hosts above but the snapshot has no Lean
  (for example in a session started before the environment was configured),
  the setup can be reproduced by hand in a few minutes: install `zstd`,
  download and unpack the toolchain tarball to `/opt/lean`, symlink `lean` and
  `lake`, and run `lake exe cache get` in the checkout.

## Maintenance

* **Bumping Lean or Mathlib**: the setup script reads the version from
  `lean-toolchain`, so after a bump re-save the environment's setup script (any
  edit, even a comment) to trigger a rebuild. The hook refuses to use the warm
  clone when the checkout wants another Lean version than the snapshot has.
* **Toolchain download returns 403**: the cloud GitHub proxy only serves
  release assets of repositories attached to the session, and
  `releases.lean-lang.org` redirects to a GitHub release asset. If the download
  fails, upload the tarball as a release asset of this repository and set
  `TOOLCHAIN_URL` in the setup script to the asset URL.
* **Setup exceeds the five-minute budget**: drop `lake build MIPRE` from the
  setup script; the first session then builds the modules once.
* **Local use**: the project-scope `.mcp.json` points `LEAN_PROJECT_PATH` at
  the cloud checkout path by default; set `LEAN_PROJECT_PATH` to your local
  checkout to use lean-lsp from this repository locally.
