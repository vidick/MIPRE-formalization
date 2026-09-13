# MIPRE-formalization

A Lean 4 + Mathlib formalization of MIP* = RE, with a leanblueprint under
`blueprint/`. Roadmap and open items: `planning/next-steps.md`.

## The shape of the library decides your feedback loop

The import graph is one-way. `MIPRE/Foundations/`, `MIPRE/TM/`, `MIPRE/LCS/` and
`MIPRE/Cslib/` — 62 files, 18k lines, the mathematics this project writes itself —
import Mathlib and each other, and **never** `MIPRE/Background/`. The vendored
trees under `MIPRE/Background/` (453 files, 253k lines: 92% of the repository) are
reached by exactly nine modules, all of them in `MIPRE/Background/` too:
`Repetition/Entangled.lean` (→ `TenProofs`, one module of 71k lines),
`Repetition/{Commuting,TracialDensity}.lean` (→ `CommutingRepetition`) and the six
`LIDT/Bridge/*.lean` (→ `MIPStarRE`).

So there are two regimes, and it is worth knowing which one you are in before
choosing a tool:

* **Foundations, TM, LCS** — seconds per check, always. Nothing there reaches the
  vendored trees.
* **The nine bridges, or any whole-library build** — seconds if the modules are
  already built, 30 to 45 minutes if they are not. Cloud sessions get them
  prebuilt (`docs/lean-cloud.md`); the `lean-warm:` line at session start says how
  many are in place.

## Checking Lean code

In order of preference:

1. **`lean-lsp` MCP tools** — `lean_diagnostic_messages` for a file's errors,
   `lean_goal` for the proof state, `lean_multi_attempt` to try tactics without
   editing. Seconds per cycle, and they see the buffer rather than the last build.
   Use these for all iteration. They are not a way around missing oleans: the
   language server runs `lake setup-file`, which builds a file's import closure on
   demand, so the first request on a file whose imports are unbuilt costs exactly
   what building them costs.
2. **`lake build MIPRE.<Module>`** — to confirm a finished module. About 8 seconds
   for a Foundations module when its imports are built, most of that replaying
   Mathlib's traces.
3. CI — only as the final check. Three to four minutes when the build cache hits.

Four commands to never run:

* a bare **`lake build`** — it builds all 533 modules;
* **`lake build` on Mathlib** — it would compile Mathlib from source and not finish;
* **`lake update`** — it needs Reservoir, which the cloud VMs cannot reach; every
  dependency is pinned in `lake-manifest.json`;
* **`lake clean`** — `.lake` is a symlink into the shared warm tree, and clean
  "deletes the build directories of every package in the workspace", Mathlib's
  7.6 GB included.

After adding or removing a file, run **`lake exe mk_all`**: `MIPRE.lean` must list
every module, and CI fails the build if it does not.

Scratch files go in `Scratch/` (git-ignored). In them, import the specific module
you need and never `import MIPRE`, which pulls all 533 including the 71k-line one.
138 of the vendored modules do a wholesale `import Mathlib`; that is much of why a
full build is slow, and not a habit to copy.

Environment setup, the allowed-host list and troubleshooting: `docs/lean-cloud.md`.

## Things that will bite

- **Vendored trees are read-only**: `MIPRE/Background/Repetition/TenProofs/`,
  `MIPRE/Background/Repetition/CommutingRepetition/` and
  `MIPRE/Background/LIDT/MIPStarRE/`. Change them only through
  `scripts/vendor-*.py`, which records each fix. Nothing outside
  `MIPRE/Background/` may name their namespaces.
- **`backward.isDefEq.respectTransparency false`** appears at specific
  declarations and files. Never set it project-wide; it broke other modules.
- **Blueprint** builds only on `main`, never on a branch. Before merging LaTeX,
  check mechanically that every `\ref`, `\uses`, `\cite` target exists and every
  `\lean{}` name resolves — there is no plastex or pdflatex in a session.
- **`intentions / lifecycle`** is red on every PR: its project-board token is
  rejected repository-wide. Not a PR's fault; do not try to fix it from a PR.

## Conventions

- Editing files with a script: use exact-string replacement with a `--check`
  mode that asserts each anchor occurs exactly once. A patch script that appends
  instead of replacing has corrupted `planning/next-steps.md` once already.
- Pull requests: `Closes #N`, label `awaiting-review`, squash merge. Commit
  messages name the tracking issue. Squash merge deletes the branch, so restart
  it from `origin/main` before the next piece of work.
