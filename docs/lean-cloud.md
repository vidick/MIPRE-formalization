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
| A warm clone of this repository with the Lake dependencies, the Mathlib olean cache and as many built `MIPRE` modules as `BUILD_BUDGET` reached | `/opt/warm/MIPRE-formalization` |
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
   github.com
   release-assets.githubusercontent.com
   objects.githubusercontent.com
   releases.lean-lang.org
   release.lean-lang.org
   lakecache.blob.core.windows.net
   loogle.lean-lang.org
   leansearch.net
   premise-search.com
   leanpremise.net
   ```

   The first three are the ones easy to miss. `lake-manifest.json` pins fifteen
   dependencies, all on `github.com`. And the toolchain URL is a chain:
   `releases.lean-lang.org` 302s to `github.com`, which 302s again to
   `release-assets.githubusercontent.com`, and that last hop is where the 575 MB
   actually comes from — allow only the first and the request starts and then dies
   on the hop carrying the payload.

   `reservoir.lean-lang.org` is **not** in the list: it is unreachable from these
   VMs, and it is not needed, because the manifest pins every dependency's git URL
   so Lake never resolves a `scope`. The price is that `lake update` cannot work
   here at all.

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
* Prefer the `lean-lsp` MCP tools to `lake build` for iterating. Once a
  module's imports are built, `lean_diagnostic_messages` returns the file's
  errors in ten seconds or so, against minutes for `lake build`, and
  `lean_goal` / `lean_multi_attempt` let a tactic be tried without touching the
  file. This is the single largest difference in feedback speed available here.
* A bare `lake build` is never quick even when nothing changed: it replays the
  traces of all 8855 modules. Always name the module you care about.
* Never run `lake build` on Mathlib and never `lake update`; the first would
  compile Mathlib from source and not finish, and the second needs Reservoir,
  which is unreachable.
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
  release assets of repositories attached to the session, and every public
  toolchain URL ends at a release asset of `leanprover/lean4`, which is not
  attached. The script tries `releases.lean-lang.org` and then the direct
  `github.com` release URL, logging each attempt; if both 403, upload
  `lean-<version>-linux.tar.zst` as a release asset of *this* repository and set
  `TOOLCHAIN_URL` at the top of the script to it. That URL is tried first.
* **Setup takes too long**: lower `BUILD_BUDGET` at the top of the setup
  script. It caps the pre-build with `timeout`, so the script always exits
  cleanly rather than being killed, and Lake keeps every module that finished —
  a partial pre-build is still a win. `BUILD_BUDGET=0` skips the pre-build
  entirely: setup is then only a few minutes, but the first in-session build of
  anything importing the vendored repetition trees costs 20 to 40 minutes.
  Building all 533 modules takes 30 to 45 minutes.
* **Local use**: the project-scope `.mcp.json` points `LEAN_PROJECT_PATH` at
  the cloud checkout path by default; set `LEAN_PROJECT_PATH` to your local
  checkout to use lean-lsp from this repository locally.
