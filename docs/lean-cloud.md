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
| A warm clone of this repository with the Lake dependencies and the Mathlib olean cache | `/opt/warm/MIPRE-formalization` |
| This repository's own compiled modules, downloaded as a bundle | `/opt/warm/MIPRE-formalization/.lake/build` |
| lean-lsp-mcp, pre-fetched | the uv cache |

**Nothing is compiled during setup.** That is not an optimisation, it is forced:
the platform stops a setup script at about five minutes
([docs](https://code.claude.com/docs/en/cloud-environments#setup-scripts)), of
which the clone and the Mathlib olean cache already take about 140 seconds, while
compiling the 533 modules of this repository takes 30 to 45 minutes. So Mathlib
comes from the official olean cache and this repository's modules come from a
bundle that `.github/workflows/build-project.yml` publishes on every push to
`main` — the `prebuilt-main` release asset. Lake's build traces are
path-independent, so an olean compiled on a CI runner is *replayed*, not rebuilt,
under `/opt/warm` on a session VM; it is the same trick as `lake exe cache get`.

The snapshot is rebuilt only when the setup script or the allowed hosts change, or
after about seven days. Between rebuilds the bundle ages: Lake recompiles whatever
changed on `main` since, and nothing else.

Per session, the SessionStart hook
[`.claude/hooks/lean-warm.sh`](../.claude/hooks/lean-warm.sh) links the warm
clone's `.lake` directory into the session's checkout, so that `lake build`
there rebuilds only the modules whose sources differ, exports
`LEAN_PROJECT_PATH`, creates `Scratch/`, and refreshes the Mathlib oleans only if
the pin moved (comparing the checkout's `lake-manifest.json` against the stamp, so
that an unchanged pin costs nothing at session start). If the snapshot holds no
compiled modules at all it fetches the bundle itself, which is the difference
between a session that can check a bridge module and one that cannot.
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
   releases.lean-lang.org
   release.lean-lang.org
   lakecache.blob.core.windows.net
   loogle.lean-lang.org
   leansearch.net
   premise-search.com
   leanpremise.net
   ```

   GitHub needs nothing added. `github.com`, `codeload.github.com`,
   `objects.githubusercontent.com` and `release-assets.githubusercontent.com` are
   all in the default list, and GitHub traffic takes a
   [separate proxy](https://code.claude.com/docs/en/cloud-environments#github-proxy)
   that does not go through the allowlist at all — which is what makes the
   prebuilt bundle reachable, since it is a release asset of this repository. The
   toolchain URL is a chain (`releases.lean-lang.org` 302s to `github.com`, which
   302s again to `release-assets.githubusercontent.com`, where the 575 MB
   actually is), so only its first hop has to be listed.

   Two of the search hosts did not answer from a session on 2026-09-13
   (`premise-search.com`, `leanpremise.net`), so lean-lsp-mcp's premise search is
   unavailable; `leansearch.net` and `loogle.lean-lang.org` did answer.

   `reservoir.lean-lang.org` is **not** in the list: it is unreachable from these
   VMs, and it is not needed, because the manifest pins every dependency's git URL
   so Lake never resolves a `scope`. The price is that `lake update` cannot work
   here at all.

3. **Setup script**: paste the contents of `.claude/cloud-setup.sh`, adjusting
   `BRANCH` if the toolchain of a feature branch differs from `main`.
4. Save. The first session in the environment runs the script; later sessions
   start from the snapshot.

## Checking that it took

The setup script and the SessionStart hook are two halves of one mechanism, and
the script has to be pasted by hand into a web form, so they can drift apart. Both
halves now say so rather than leaving it to be noticed:

* The script writes `/opt/warm/SETUP-STAMP` (what branch, commit, toolchain and
  Mathlib pin the snapshot was built from, the sha256 of both the pasted text and
  the repository's `.claude/cloud-setup.sh`, which bundle it fetched and how many
  modules are in place) and
  `/opt/warm/SETUP-REPORT.txt` (every step, timestamped — read this first when
  setup fails).
* The hook compares them against the checkout at every session start and prints,
  in its `lean-warm:` line, how many MIPRE modules are prebuilt out of how many
  exist. It adds a note when `.claude/cloud-setup.sh` has changed since the
  snapshot was built (re-save needed), and another when the text pasted into the
  environment is not the repository's copy at all (which is how the toolchain
  override and the pre-build went missing).

So a healthy session opens with one line naming the Lean version and a module
count close to the total, and no notes. A count of zero means the bundle did not
land — the hook then tries to fetch it itself, so a zero that survives into the
`lean-warm:` line means the asset is missing, `zstd` is not installed, or the
download timed out; `SETUP-REPORT.txt` has the setup-side reason. A missing
`lean-warm:` line altogether means the snapshot has no Lean, so the script never
got that far — `SETUP-REPORT.txt` says where it stopped.

The warm tree is about 8 GB on disk (the Mathlib cache alone is 7.6 GB). Do not
enable lean-lsp-mcp's local Loogle (13 GiB peak).

## Using Lean from a session

* Know which regime you are in: `MIPRE/Foundations`, `MIPRE/TM`, `MIPRE/LCS` and
  `MIPRE/Cslib` never import `MIPRE/Background`, so they cost seconds to check
  whatever the snapshot holds. Only the nine modules that reach the vendored trees
  (`Repetition/Entangled.lean`, `Repetition/{Commuting,TracialDensity}.lean`, the
  six `LIDT/Bridge/*.lean`) depend on the bundle having landed.
* Check a module: `lake build MIPRE.Foundations.Compression` (only its
  dependencies are built).
* After adding or removing a file, run `lake exe mk_all`; CI fails if `MIPRE.lean`
  does not list every module.
* Standalone snippets: `lean_run_code` with `import Mathlib`, plus
  `import MIPRE.<Module>` for definitions from this repository.
* Scratch files: write them under `Scratch/` (ignored by git) and use the
  file-based tools, or `lake env lean Scratch/Foo.lean`.
* Prefer the `lean-lsp` MCP tools to `lake build` for iterating: they answer in
  seconds and they see the buffer, so no build is needed between edits.
  `lean_diagnostic_messages` gives a file's errors, `lean_goal` the proof state,
  `lean_multi_attempt` tries a tactic without touching the file. They are not a
  way around missing oleans, though: the language server runs `lake setup-file`,
  which builds a file's import closure on demand, so the first request on a file
  whose imports are unbuilt costs what building them costs.
* A bare `lake build` builds all 533 modules of this repository, and even with
  nothing to do it replays the traces of all 8855. Always name the module.
* Never run `lake build` on Mathlib, never `lake update` (it needs Reservoir,
  which is unreachable), and never `lake clean`: `.lake` here is a symlink into
  the shared warm tree, and clean "deletes the build directories of every package
  in the workspace" — Mathlib's 7.6 GB with it, to be refetched at best.
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
* **Toolchain download fails**: the script tries `TOOLCHAIN_URL`, then
  `releases.lean-lang.org`, then the direct `github.com` release URL, logging each
  attempt. All three end at a release asset of `leanprover/lean4`; that download
  worked from a session on 2026-09-13, but if it ever 403s (the GitHub proxy
  refusing assets of a repository not attached to the session), upload
  `lean-<version>-linux.tar.zst` as a release asset of *this* repository and set
  `TOOLCHAIN_URL` to it. It is tried first.
* **The prebuilt bundle**: `build-project.yml` rebuilds it on every push to `main`
  and replaces the asset on the `prebuilt-main` release; the tag is a fixed
  anchor, not a version. A session holding a bundle can read
  `.lake/build/BUNDLE-INFO` for the commit, toolchain and Mathlib pin it was built
  from. It is skipped when it would exceed the 2 GiB release-asset limit, which
  the run's log warns about; if that ever happens, either split it or drop the
  vendored trees from it. `PREBUILT_URL=` (empty) in the setup script turns the
  whole mechanism off.
* **Setup takes too long**: it should now take about three minutes, nearly all of
  it `lake exe cache get` and the bundle. `BUILD_BUDGET` (default 0) is the only
  part that compiles anything, and it is capped by `DEADLINE` in any case. Raising
  it cannot buy a full build: the platform's limit is about five minutes total.
* **Local use**: the project-scope `.mcp.json` leaves `LEAN_PROJECT_PATH` at `.`,
  the checkout the server is started in, which is what a local clone wants; cloud
  sessions get the absolute path from the hook instead. Nothing in
  `.claude/hooks/lean-warm.sh` runs outside a cloud session.
