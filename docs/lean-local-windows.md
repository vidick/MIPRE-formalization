# Local Lean development on Windows

Use native Windows Lean at the version in `lean-toolchain`, with the exact
dependency revisions in `lake-manifest.json`. PowerShell 7, Git, Elan, and Python 3
are the prerequisites. WSL is not required. Run the commands below from a
PowerShell 7 terminal at the repository root.

## One-time setup

Keep this checkout's text files in LF form so `mk_all --check` can compare the
generated import file byte for byte:

```powershell
git config --local core.autocrlf input
```

If an earlier checkout or merge wrote `MIPRE.lean` with CRLF endings, regenerate
it with the pinned `lake exe mk_all` command before validation. The Git diff
should then show only any actual import changes.

Keep Lake's numerous cache files outside OneDrive. The source checkout can stay
in OneDrive; make its `.lake` directory a junction to a persistent local directory.
Use a separate Lake directory for each checkout and toolchain/dependency combination.
Do not point independent working branches at the same writable Lake directory.
The compressed Mathlib download cache can be shared between those directories.

Use a short directory directly under the user profile, for example:

```text
%USERPROFILE%\MIPRECache\
  mathlib\
  intro-433\                 # this checkout's .lake junction target
```

Avoid `%LOCALAPPDATA%` for this cache when running from the Codex desktop MSIX
app. Windows can resolve it through an additional
`AppData\Local\Packages\OpenAI.Codex_...\LocalCache\Local\...` prefix. That
can turn an apparently short path into one long enough to make native cache
extraction fail with `os error 3`, even after Git accepts the checkout. The
user-profile cache location avoids that extra prefix. Inspect the resolved
junction target as well as the path used to create it.

Create the target directory and junction only when `.lake` does not already exist.
For an existing `.lake`, inspect its location and contents before moving anything;
do not overwrite or remove a warm cache. A junction can be created with
`New-Item -ItemType Junction -Path .lake -Target <absolute-target-directory>`.

Create the ignored `Scratch/lean-local-config.json` with your actual paths:

```json
{
  "elanHome": "C:/Users/thoma/.elan",
  "mathlibCacheDir": "C:/Users/thoma/MIPRECache/mathlib"
}
```

Install the exact toolchain into that Elan home, if it is not already present:

```powershell
# Run in a setup terminal; replace the path with your configured elanHome.
$env:ELAN_HOME = 'C:\Users\thoma\.elan'
& "$env:ELAN_HOME\bin\elan.exe" toolchain install (Get-Content ./lean-toolchain -Raw).Trim()
```

Then fetch dependencies and Mathlib's compiled artifacts through the wrapper:

```powershell
./scripts/lean-local.ps1 Doctor
./scripts/lean-local.ps1 Cache
```

`Cache` invokes `lake exe cache get` from this repository, preserving its manifest
pins. GitHub and `lakecache.blob.core.windows.net` must be reachable. The first run
checks out dependencies and compiles the small cache utility; it does not need a
source build of Mathlib. Allow ample disk space for the toolchain, dependency
sources, compressed cache downloads, and unpacked artifacts.

Mathlib has long filenames. The wrapper supplies `core.longpaths=true` through
Git's child-process environment, so Lake's dependency clones inherit it even
before they have local Git configuration. It preserves existing
`GIT_CONFIG_COUNT` entries and appends this one; no global Git setting changes.
Setting `core.longpaths` only in the root checkout does not fix dependency clones.

If available, reuse the repository's
[prebuilt main bundle](https://github.com/vidick/MIPRE-formalization/releases/download/prebuilt-main/mipre-build.tar.zst).
It contains `.lake/build`; download it to an ignored location, check its current
SHA-256 against the GitHub release asset metadata, inspect the archive paths, and
extract it with a zstd-capable tar tool. Check `.lake/build/BUNDLE-INFO` for the
toolchain, Mathlib pin, and built commit. This is a rolling main bundle, not a
guarantee that the current branch is already built. Avoid overwriting newer local
work with an older bundle. Lake will rebuild modules whose inputs changed.

Mathlib's Linux-built Lean artifacts are intended to work on Windows. Preserve
their companion `.olean.server`, `.olean.private`, `.ilean`, `.ir`, `.ir.sig`,
`.trace`, and `.hash` files and generated C files. Linux native executables,
objects, and shared libraries must be rebuilt for Windows. Run executable targets
through Lake so that its toolchain DLLs are discoverable. See the pinned
[Mathlib configuration](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/lakefile.lean#L62)
and [Lake's platform settings](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

## Daily checks

The wrapper reads its paths from `Scratch/lean-local-config.json`, falling back
to `ELAN_HOME` and `MATHLIB_CACHE_DIR`, then to the current user's `.elan` and
`%USERPROFILE%\MIPRECache\mathlib`. Configured relative paths are relative to the
repository. It resolves the repository from the script location, so it also works
when called from another directory.

It invokes `elan run <pinned-toolchain> lake` without Elan's `--install` flag.
A missing toolchain is an error, including during `Doctor`; it is not installed
silently. Environment settings apply only to child processes, leaving the calling
terminal unchanged on success, failure, timeout, or interruption. Commands and
their output, exit codes, and elapsed times are logged in ignored
`Scratch/lean-local-*.log` files. Lean receives `LEAN_NUM_THREADS=4` by default;
use `-Threads N` to change that per invocation. Run one Lake build at a time
against a given Lake directory. The persistent checkers below can run independently
once their imports are built; bound their number by available memory.

```powershell
# Report paths, cached bundle metadata, and installed tool versions.
./scripts/lean-local.ps1 Doctor

# Confirm one finished module, building its missing/stale imports as needed.
./scripts/lean-local.ps1 Build -Targets MIPRE.Foundations.Introspection.AuxiliaryReadProgram

# Confirm several explicit modules in one Lake invocation.
./scripts/lean-local.ps1 Build -Targets @(
  'MIPRE.Foundations.Introspection.AuxiliaryReadProgram',
  'MIPRE.Foundations.Introspection.AuxiliarySamplingCorrect'
)

# Check a scratch proof without adding it to the library or umbrella.
./scripts/lean-local.ps1 Check -File Scratch/Example.lean -TimeoutSeconds 300

# Build the full MIPRE library.
./scripts/lean-local.ps1 Build

# Final local gate; stop at the first failure.
./scripts/lean-local.ps1 Validate
# Select a specific Python installation when needed.
./scripts/lean-local.ps1 Validate -Python 'C:/path/to/python.exe'
```

`Check` uses `lake lean` to check one file with its Lake environment and import
dependencies. It has a default 300-second timeout. `Build`, `Cache`, and
`Validate` have no default timeout; `Doctor` allows 30 seconds per command.
`-TimeoutSeconds N` sets a per-command limit, and `0` means unlimited (except
`Doctor`, whose default remains 30 seconds). On timeout, the wrapper stops the
command's process tree and exits with code 124. Other command failures propagate
their exit code. Existing artifacts are kept; rerun the relevant check after
correcting the error.

Prefer the persistent checker below for tactic iteration, then `Check` for a
small standalone scratch experiment and `Build -Targets ...` to confirm the
finished module. Scratch proofs should import the specific module they need,
not the whole `MIPRE` umbrella. A cold full build can be expensive; a warm full
build mostly replays existing traces.

## Persistent checks across edits

[`scripts/lean-lsp-check.py`](../scripts/lean-lsp-check.py) wraps the pinned
[`leanclient`](https://github.com/oOo0oOo/leanclient) Python library. It keeps
Lean's language server and open-file workers alive, preserving imports and
unchanged command snapshots across edits. Install the helper dependencies once
into the ignored directory, using the same Python installation for every command:

```powershell
python -m pip install --target Scratch/lean-lsp-deps leanclient==0.13.2
python scripts/lean-lsp-check.py start --session root
python scripts/lean-lsp-check.py check Scratch/Example.lean --session root --timeout 300

# Check another buffer as Example.lean, without changing the file on disk.
python scripts/lean-lsp-check.py check Scratch/Example.lean --session root `
  --text-file Scratch/Alternative.lean --timeout 300

python scripts/lean-lsp-check.py status --session root
python scripts/lean-lsp-check.py stop --session root
```

`start` launches a hidden local helper; `serve` runs the same helper in the
foreground. Use named sessions `root`, `transport`, `sampler`, and `decider` for
independent editing streams. Each session accepts one check at a time and retains
two file workers by default. `--max-open-files N` at startup can lower or raise
that limit from one to four; `--threads N` controls Lean's thread count. The first
check still pays the import-loading cost. A check of an edited file in an existing
worker sends only the changed text range, allowing Lean to reuse earlier work.

The helper reads `lean-local-config.json`, selects the installed pinned Lake
binary, and gets each file's options through Lake. Thus settings such as
`autoImplicit = false` remain active. It disables both initial cache fetching
and dependency builds: a `didOpen` uses `dependencyBuildMode: "never"`, which
Lean 4.33 translates into `lake setup-file --no-build --no-cache`.

An import of a new or stale module requires a deliberate targeted build first.
Coordinate that build with other work using the same cache. Once it succeeds,
discard the importing file's old worker and check it again:

```powershell
./scripts/lean-local.ps1 Build -Targets MIPRE.Foundations.Introspection.MyDependency
python scripts/lean-lsp-check.py close Scratch/Example.lean --session root
python scripts/lean-lsp-check.py check Scratch/Example.lean --session root
```

Changing a file's import header also restarts its Lean worker. Changes to the
toolchain, manifest, or Lake configuration require stopping and restarting the
whole helper session. Unsaved buffers are not shared across sessions; only
explicitly built artifacts can satisfy another file's imports.

Every result includes its source hash, document version, elapsed time, diagnostics,
and `completed` status. Success requires the version-specific
`textDocument/waitForDiagnostics` reply; empty diagnostics alone do not establish
success. Exit codes are zero for a completed check without errors, one for Lean
errors, two for setup/protocol failures, and 124 for a timeout. Timeouts include
any diagnostics already received, mark the result incomplete, and close that
session's Lean client. The next check creates a fresh client.

Control requests use an authenticated loopback endpoint, with its descriptor and
logs under `Scratch/lean-lsp-*.json` and `Scratch/lean-lsp-*.log`. No source files
are written by the checker. If a helper crashes, verify the PID in its state file
is no longer running before removing that one stale state file and starting it
again. Stop idle sessions to release their Lean workers' memory.

## Final validation

`Validate` runs the full `lake build MIPRE`, `lake exe mk_all --check`,
`scripts/lean-coverage.py --check`, `scripts/ledger-sync.py`, and
`git diff --check`. Its Git trust override applies only to this command and this
checkout, useful when an agent runs under a separate Windows account.

After adding/removing Lean files, deliberately regenerate `MIPRE.lean` with the
pinned `lake exe mk_all` before validation. `Validate` only checks the umbrella;
it never rewrites it. For example, in a setup terminal with the configured
`ELAN_HOME`, run:

```powershell
& "$env:ELAN_HOME\bin\elan.exe" run (Get-Content ./lean-toolchain -Raw).Trim() lake exe mk_all
```

Never run `lake clean`, a source build of Mathlib, or `lake update` as a repair
step. Do not edit cache traces or hashes to suppress rebuilding. If a cache seems
stale, first compare the actual toolchain, manifest pins, and bundle metadata.
The wrapper does not install tools, download the MIPRE bundle, change dependencies,
delete caches, or modify global Git configuration.
