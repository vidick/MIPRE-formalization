# Direct parallel repetition — port plan (vendor two artifacts, state in MIPRE vocabulary)

Tracking issue: #27. Branch: `claude/mipre-proof-repo-0z4oee`. Companion of
`planning/lidt-port.md` (whose conventions this plan follows) and of
`planning/compression-track.md` (whose Lean toolkit the abstract-lemma work below reuses).

## Context

Two complete, sorry-free formalizations of *direct* (non-anchored) parallel repetition
exist outside this repository:

| Result | Upstream | Root | Size | Lean |
|---|---|---|---|---|
| Uniform direct repetition for commuting-operator strategies, rate `exp(-c n ε⁷/(ε+log|A||B|))`; also Lin's tracial density theorem | `vidick/commuting-repetition`, branch `claude/install-vibefled-mplweo`, commit `cfa2f1b` | `CommutingRepetition.uniform_parallel_repetition`, `MainStatement.uniform_parallel_repetition`, `CommutingRepetition.Density.tracialDensity` | 130 modules / 54.8k lines (import closure of the roots; 140 modules upstream) | v4.33.0 |
| Uniform exponential repetition for entangled (finite-dimensional tensor-product) strategies, rate `exp(-c n ε¹³/(ε+log|A||B|))` | `openai/ten-proofs`, commit `94bc0fe`, `QuantumParallelRepetition.lean` | `QuantumParallelRepetition.distributionUniformExponential` | 1 module / 71.0k lines | v4.32.0 (Mathlib `81a5d25`, identical to this repository's pin before the bump below) |

Both are Apache 2.0; both upstream axiom audits report `propext`, `Classical.choice`,
`Quot.sound` only. The blueprint's parallel repetition chapter (`05_anchored_repetition.tex`)
was, before this port, entirely unformalized: `thm:bvy` (anchored repetition in
entanglement form) and its toolkit (Uhlmann, relative entropy, quantum Raz, Holenstein,
dependency breaking, local unitaries) carried no `\lean` tags.

### Verified facts this plan relies on (checked 2026-09-11)

- Neither artifact states a dimension-tracking (entanglement-requirement) form: both are
  value statements. The OpenAI proof rounds via embezzlement (`embezzlementState`,
  `QuantumParallelRepetition.lean:5229–6331`); the commuting-repetition proof discards the
  original strategy after Lin's density step (manuscript §7.3).
- JNVWY (`recursive.tex:62`) state compression soundness as
  `Ent(V^compr_n, ½) ≥ ½ max{Ent(V_N, ½), 2^{N^λ−1}}` — a factor ½ per level that the
  blueprint's `thm:compression` currently omits — and their halting proof
  (`recursive.tex:1063–1210`) tolerates any per-level loss dominated by the tower growth.
  JNVWY's remark (`parallel_amplification.tex:78–85`) rejects DSV/Yuen-style direct
  repetition for giving only `Ent(G^k, v) ≥ log Ent(G, 1−ε)`.
- **Lin 2025 (arXiv:2510.07162, `CompressionCond.tex`, `thm:compressRE`) proves
  RE-hardness from value-form gap compression alone**: the self-referential verifier
  sequence has three exits — halt within `n` steps → accepting game; the search-from-below
  algorithm (`lem:value-lower-approx`), run on the sequence's own `C₀`-th game, halts
  within `n − C₀` steps → rejecting game; otherwise the compressed game at index `n + 1`.
  Downward induction on value-form completeness/soundness shows the second exit never
  fires, so in the non-halting case the search never halts and the value is ≤ ½. No
  entanglement lower bound is used ("the entanglement lower bound condition is **not**
  needed for the proof of MIP* = RE", `Introduction.tex`). Lin still uses *anchored*
  repetition (`Parallelrepetition.tex`) only because no direct theorem was available.
- `lake exe mk_all` orders imports as `LC_ALL=C sort` of module names (verified against
  the committed `MIPRE.lean`); the scripts regenerate the file that way.

## Decisions

**D1 — Location.** `MIPRE/Background/Repetition/CommutingRepetition/` and
`MIPRE/Background/Repetition/TenProofs/`, generated; hand-written bridge files live
directly in `MIPRE/Background/Repetition/`. Mirrors LIDT's D1.

**D2 — Namespaces unchanged** (`CommutingRepetition`, `MainStatement`,
`QuantumParallelRepetition`). Nothing outside `MIPRE/Background/Repetition/` refers to
them; the bridge exposes everything in the `MIPRE` namespace. Mirrors LIDT's D2.

**D3 — Vendored code is read-only** except for (a) the import-prefix rewrite,
(b) the provenance header, (c) the `set_option autoImplicit true` line inserted after
the import block (both upstreams build with Lean's default; `lakefile.toml` sets
`autoImplicit = false`), and (d) compile fixes recorded in each directory's README.
Re-test with `--no-auto-implicit` once CI is green; drop (c) if it is unnecessary.

**D4 — What is copied.** From commuting-repetition, the import closure of `CR_ROOTS`
(`MainTheorem.Main`, `StatementBridge`; `Statement.lean` is in the closure) plus
`NOTICE`; not `Fidelity/Nodes.lean` (documentation only) nor the nine modules the roots
do not need. From ten-proofs, the single module and, as an audit aid,
`ComparatorChallenges/G_QuantumParallelRepetition.lean` as `.lean.expected`.

**D5 — Vendoring is done by `scripts/vendor-repetition.py`**, never by hand; the
README provenance blocks are generated. Mirrors LIDT's D5–D6.

**D6 — Toolchain: the project moves to Lean/Mathlib v4.33.0** (commit "Bump Lean and
Mathlib to v4.33.0"), so commuting-repetition is vendored natively and ten-proofs and
LIDT cross one release forward. Fallback if LIDT does not survive: backport
commuting-repetition to v4.32.0 instead. Dependency revisions come from Mathlib and
doc-gen4 at their `v4.33.0` tags; `checkdecls` is unchanged.

**D7 — Statements in MIPRE vocabulary.** `def:direct-repetition` is `MIPRE.Game.repeat`
(product law, product Bool predicate — literally the upstream construction, which uses
a Bool predicate like `MIPRE.Game`). For the commuting theorem, Foundations gains a
*bipartite* commuting-operator strategy and value (`def:co-strategy-bipartite`,
`def:co-value-bipartite`; the existing `commValue` is the synchronous tracial value and
exact equality is not available — the blueprint routes that through
`thm:almost-sync`, issues #22/#23). The bridge is then field-by-field, as upstream's own
`StatementBridge.lean`. For the entangled theorem, `quantumValue` (pure state,
projective) must be related to upstream's `entangledValue` (mixed state, POVM):
`lem:povm-value-eq` (purification + Naimark, finite dimension) is the one genuinely new
lemma, tracked by a sub-issue and allowed to land as a `sorry`.

**D8 — Direction of the blueprint (Option B, confirmed by the maintainer on 2026-09-11).**
Following Lin's compressibility criterion, the pipeline's soundness can be stated in
value form throughout: the entanglement-requirement clauses of `thm:introspection`,
`thm:oracularization`, `thm:answer-reduction`, `thm:parallel-repetition`,
`thm:compression` are dropped, `thm:bvy` and its toolkit are replaced by the direct
theorems (which are stated for both models at once), and `lem:recursive-compression`
(MNY, `f`-growth) is replaced by `lem:compressible-criterion` (Lin's `thm:compressRE`:
value-form compression + a coRE algorithm for the no-instances + Kleene). The
search-from-below algorithm is `lem:value-lower-approx`, already in the blueprint's
background table. The same criterion with NPA in place of the search gives the
`MIPco = coRE` track. Done: `thm:bvy` and its toolkit stay in the blueprint as the
record of the entanglement-form route (`rem:entanglement-form`), off the path to the main
theorem.

## Phases

| Phase | Content | Status |
|---|---|---|
| 0 | Issue #27 opened and claimed; decisions above | done 2026-09-11 |
| 1 | Toolchain bump to v4.33.0; CI on LIDT + `Cost/` | v4.33 transparency fix pushed (`ee03405`); CI pending |
| 2 | `scripts/vendor-repetition.py`; both artifacts vendored; `MIPRE.lean` regenerated; READMEs, NOTICE | done 2026-09-11 (CI pending) |
| 3 | Bridge: `Game.repeat`, bipartite co-value, `thm:direct-repetition-co` (sorry-free), `thm:direct-repetition-q` (modulo `lem:povm-value-eq`), `thm:tracial-density`, axiom guards | done 2026-09-11 (CI pending) |
| 4 | Blueprint: `05_parallel_repetition.tex` with a formalized direct-repetition section; ch03 table; bibliography; under D8 the value-form restructuring | done 2026-09-11, including the D8 value-form restructuring |
| 5 | Lean: `lem:compressible-criterion` from the `Cost/` toolkit (`Compression.lean`), old lemma kept | written 2026-09-11 (CI pending) |
| 6 | PR with `Closes #27`, `awaiting-review` | after CI green |

## Risks

1. Toolchain crossing (ten-proofs and LIDT from v4.32 to v4.33): unknown until CI runs.
   Every compile check goes through `workflow_dispatch` on the branch (no local Lean in
   the porting environment).
2. `autoImplicit` reliance in 131 upstream files: handled mechanically by D3(c).
3. Build and doc-gen time: +126k lines, all `import Mathlib`.
4. `lem:povm-value-eq` is proof work, not plumbing.
5. Under D8, the value-form pipeline statements must be re-audited against Lin's
   propositions (`Seqandcompression.tex:408–587`), whose index convention (same `n`,
   runtime `n^α → polylog n`) differs from JNVWY's (`N = 2^n`).
