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

A bare **`lake build`** is worth understanding rather than avoiding: it is the
whole library, so it costs 44 minutes (110 CPU-minutes; 25 of them are the single
71k-line vendored module) when the modules are not built, and **8 seconds** when
they are, replaying all 9239 jobs. With the bundle in place it is the cheapest
possible final check before pushing. Without it, it is your afternoon.

Three commands to never run:

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

## The companion proof repository

`vidick/MIPRE-proof` (private) holds the paper source under `paper/` and the vibefeld
adversarial-verification ledger under `proofs/mipre-undecidability/ledger/`. **Before
formalizing a blueprint statement, read the paper's own statement and proof of it.** The
blueprint is a paraphrase written to be formalizable; the paper is the authority, and the
paraphrase has been wrong.

It is not attached to a session by default. Attach it with `add_repo` for
`vidick/MIPRE-proof`, or ask the maintainer. If it is unavailable, formalize from the
blueprint — but do not record a paraphrase question as settled, and say in the PR that the
paper was not consulted.

Where things are (`paper/README.md` has the full map):

| blueprint | paper file |
|---|---|
| ch. 2 games, values, PCC, `Ent` | `games.tex`, `linear.tex`, `types.tex` |
| ch. 3 low-degree test, Magic Square, Pauli | `ldt.tex`; `external/` for its dependencies |
| ch. 3 `thm:qld` (Pauli basis test soundness) | `qld-appendix.tex` and `qld-{prelim,commutation,combining,separating,isometry}.tex` |
| ch. 3 Cook--Levin, succinct SAT | `answer_reduction.tex` |
| ch. 6 introspection | `introspection.tex` |
| ch. 6 oracularization | `oracularization.tex` |
| ch. 6 answer reduction | `answer_reduction.tex`, `ld_compiler.tex` |
| ch. 6 repetition | `parallel_amplification.tex` |
| ch. 6 compression, halting; ch. 8 separation | `recursive.tex` |
| preliminaries, TM conventions, low-degree encoding | `preliminaries.tex` |

Two things to know about reading it:

- **The ledger's node statements are paraphrases too, and are not self-certifying.** Node
  `1.6.3` is marked *validated* and states a lemma that is false; only `paper/recursive.tex`
  settles it (`reports/ledger-node-1.6.3-overstated.md`). Where a node and the paper
  disagree, the paper wins and the disagreement is worth a report. A node's `\cnote{}`
  repairs and challenge history, on the other hand, are gold: they say exactly which steps
  are delicate.
- **Nothing from it may be copied into this repository.** `MIPRE-proof` is private and
  `MIPRE-formalization` is public; `paper/external/` additionally holds third-party paper
  sources and unpublished errata against other people's work. Read it, cite it in
  `blueprint/src/content/bibliography.tex` at a pinned commit, and quote at most a
  statement you are formalizing. Do not vendor `paper/`.

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
  `scripts/lean-coverage.py` is that check — labels, refs, uses, cites, environment
  nesting, `\lean{}` resolution — and it also guards against a reorganization
  dropping Lean code; `scripts/ledger-sync.py` checks the ledger correspondence. CI
  runs both before the Lean build. Tags and `\uses` lists wrap across lines here, so
  never check them with a per-line grep: that silently skips the continuations.
- **`\leanok` is two marks, not one**: inside the environment it claims the
  *statement* is formalized, inside `\begin{proof}` that the *proof* is. Only ever
  add the second after `#print axioms` shows the declaration free of `sorryAx`;
  `planning/lean-coverage.md` records the audit that established the current state.
- **`intentions / lifecycle`** is red on every PR: its project-board token is
  rejected repository-wide. Not a PR's fault; do not try to fix it from a PR.

## Conventions

- Editing files with a script: use exact-string replacement with a `--check`
  mode that asserts each anchor occurs exactly once. A patch script that appends
  instead of replacing has corrupted `planning/next-steps.md` once already.
- Pull requests: `Closes #N`, label `awaiting-review`, squash merge. Commit
  messages name the tracking issue. Squash merge deletes the branch, so restart
  it from `origin/main` before the next piece of work.
