# MIPRE-formalization

A Lean 4 + Mathlib formalization of MIP* = RE, with a leanblueprint under
`blueprint/`. Roadmap and open items: `planning/next-steps.md`.

## Checking Lean code

The feedback loop here is the thing that decides how much gets done in a session.
In order of preference:

1. **`lean-lsp` MCP tools** — `lean_diagnostic_messages` for a file's errors,
   `lean_goal` for the proof state, `lean_multi_attempt` to try tactics without
   editing. Roughly ten seconds per cycle once the imports are built. Use these
   for all iteration.
2. **`lake build MIPRE.<Module>`** — to confirm a finished module. Minutes.
3. CI — only as the final check.

Never run a **bare `lake build`** (it replays all ~8850 module traces and does not
finish quickly even when nothing changed), never `lake build` Mathlib, and never
`lake update` (it needs Reservoir, which the cloud VMs cannot reach; every
dependency is pinned in `lake-manifest.json`).

Scratch files go in `Scratch/` (git-ignored). Environment setup, the allowed-host
list and troubleshooting: `docs/lean-cloud.md`.

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
