# Next steps after the direct-repetition port — roadmap

Written 2026-09-11 at the maintainer's request ("make and record a plan so we don't
forget what we are doing"), when PR #30 was open and awaiting review. Companion of
`planning/repetition-port.md` (the port itself, decisions D1–D8),
`planning/compression-track.md` (the `Cost/` toolkit) and `planning/tm-infrastructure.md`
(universal machine, issues #17/#18). Conventions as in those files: verified facts,
decisions, items with a done criterion, risks. Update the status column as items move.

## Where things stand (2026-09-11)

- PR #30 (`claude/mipre-proof-repo-0z4oee` → `main`, `Closes #27`) is open, labeled
  `awaiting-review`. Its Lean state was green in CI on `c7d27e5` (run 34600947205); the
  two later commits add configuration and documentation only. A full local build of the
  branch under Lean v4.33.0 inside a cloud session (533 modules of this repository plus
  the Mathlib cache) finished with exit code 0 and no errors in 41 minutes of wall-clock
  time (105 CPU-minutes) — the first Lean check ever run inside a session for this
  repository.
- After the merge the path to the main theorem is in *value form* throughout (D8): no
  entanglement lower bound is stated or needed anywhere.
- Still `sorry` or blueprint-only on that path, in order of appearance:
  `lem:povm-value-eq` (#28, one `sorry`), `thm:almost-sync` (#22, no Lean),
  `lem:value-lower-approx` (no Lean), and the whole of chapter 6 (introspection,
  oracularization, answer reduction, `thm:parallel-repetition`, `thm:compression`,
  `thm:halting`), unchanged by the port. The `Cost/` toolkit statements that the
  universal machine still owes are tracked in `planning/tm-infrastructure.md`.
- Off the main path but part of the port's follow-ups: `lem:tracial-le-co` (#29),
  the restatement of `thm:tracial-density` in foundations vocabulary, and the
  commuting-operator (MIP^co) track that `thm:direct-repetition-co` opens.

## Items, in the recommended order

| # | Item | Blocks | Effort | Status |
|---|---|---|---|---|
| 1 | PR #30 review and merge; cloud environment re-save | 2 | maintainer | in progress |
| 2 | First blueprint build on `main`; fix plastex/checkdecls/doc-gen issues | — | small | waiting on 1 |
| 3 | #28 `lem:povm-value-eq`: close the entangled bridge | `\leanok` on `thm:direct-repetition-q` | medium | open |
| 4 | `lem:value-lower-approx` in Lean (MIP* ⊆ RE; hypothesis `hS` of the criterion) | `thm:halting`, `thm:mipstar-eq-re` | medium–hard | open |
| 5 | #22 `thm:almost-sync` (then #23, commuting case) | `thm:parallel-repetition` soundness | hard | open |
| 6 | #29 `lem:tracial-le-co` (GNS); restate `thm:tracial-density` | MIP^co track | medium–hard | open |
| 7 | Audit chapter 6 (value form) against Lin's propositions | chapter-6 formalization track | blueprint only | open |
| 8 | Maintenance decisions (`try rfl` rule, transparency options, `autoImplicit`, upstream pins, CI time) | — | small each | open |

### 1. PR #30 → `main`, then the cloud environment (maintainer)

- Review and merge (squash, as PR #26 was). `Closes #27` closes the tracking issue; the
  sub-issues #28 and #29 stay open on purpose.
- **After the merge, on claude.ai/code, re-save the environment's setup script**
  (`.claude/cloud-setup.sh`; procedure in `docs/lean-cloud.md`, section "One-time
  configuration"). The script clones `main` and reads *its* `lean-toolchain`, which is
  v4.32.0 until the merge; a snapshot taken before the merge carries the wrong Lean and
  the SessionStart hook refuses it ("toolchain mismatch") in every later session. Check
  at the same time that the seven network hosts listed there are allowed.
- Done when: a fresh cloud session prints a `lean-warm:` line for v4.33.0 and
  `lake build MIPRE.Foundations.Compression` is a no-op. The session that opened the PR
  is subscribed to its events (CI, reviews) until it is merged.

### 2. The first blueprint build on `main` after the merge

- `.github/workflows/blueprint.yml` runs on push to `main` (also daily and by dispatch),
  never on a branch. The port's LaTeX — 518 insertions and 87 deletions across nine
  files (chapters 1, 3, 4, 5, 6, 8, `content.tex`, `macros/common.tex`,
  `bibliography.tex`) — has been checked only mechanically (every `\ref`, `\uses`,
  `\cite` target exists; environments balanced), never by plastex or pdflatex (no TeX in
  the sessions).
- Watch, in the run's log: plastex (unknown macros — `\omegaco` is new; `\uses` graph
  cycles or undefined labels); `checkdecls` on the `\lean{}` names introduced by the port
  (`MIPRE.Game.repeat`, `MIPRE.SynchronousGame.repeat`, `MIPRE.CommutingOperatorStrategy`
  and `.value`, `MIPRE.commutingOperatorValue`, `MIPRE.Repetition.commutingOperatorValue_repeat_le`,
  `MIPRE.Repetition.quantumValue_repeat_le`, `MIPRE.Repetition.quantumValue_eq_entangledValue`,
  `MIPRE.Repetition.tracialDensity`, `MIPRE.Cost.compressibility_criterion`); doc-gen4
  time and disk (126k more lines of Lean, all importing Mathlib; the workflow queues
  rather than cancels, and already ran over an hour before the port).
- Fix forward with a small PR. Done when: the pages deploy with the new chapter 5 and the
  dependency graph shows `thm:direct-repetition-co`, `thm:direct-repetition-q` and
  `lem:compressible-criterion` with their Lean status, and the dashboard refreshes.

### 3. #28 — `lem:povm-value-eq`: close the entangled repetition bridge

- Target: `MIPRE.Repetition.quantumValue_eq_entangledValue`
  (`MIPRE/Background/Repetition/Entangled.lean`), the only `sorry` under
  `MIPRE/Background/Repetition/`. Issue #28 has the full sketch.
- Decomposition. (a) `≤`: a `TensorProductStrategy` is a vendored `Strategy` with
  `Alice = Fin dA`, `Bob = Fin dB`, density matrix `|ψ⟩⟨ψ|`, projective measurements as
  POVMs; the winning probabilities agree termwise. (b) `≥`: three general lemmas that
  belong in `MIPRE/Foundations/` (nothing outside `Background/Repetition/` may mention the
  vendored namespaces, so only the glue stays in `Entangled.lean`): purification of a
  density matrix on `Alice × Bob` into a unit vector on `Alice × (Bob × R)`; Naimark
  dilation of a finite POVM on a finite-dimensional space into a projective measurement on
  `H ⊗ ℂ^k` (check Mathlib's `Analysis.CStarAlgebra` / `LinearAlgebra.Matrix` first — as
  far as known there is no packaged Naimark theorem at v4.33); reindexing of Kronecker
  products along `Fintype.equivFin`. (c) The `sSup`/`iSup` comparison: both sides bounded
  by 1 over nonempty sets.
- Then: add `quantumValue_repeat_le` to `MIPRE/Background/Repetition/Axioms.lean`; in
  `05_parallel_repetition.tex` mark the proofs of `lem:povm-value-eq` and
  `thm:direct-repetition-q` `\leanok`; drop the dagger from the chapter-3 table.
- Independent of everything else and self-contained (finite-dimensional linear algebra):
  a good first Lean task in the cloud environment.

### 4. `lem:value-lower-approx` in Lean — MIP* ⊆ RE and the halting theorem's semidecider

- Why now: it is the hypothesis `hS : ∀ x, Halts S (encode x) ↔ x ∉ B` of
  `MIPRE.Cost.compressibility_criterion` with `B` the descriptions of games of synchronous
  value at most ½ (`rem:compression-abstract`, `thm:halting`), and by itself the easy
  inclusion of `thm:mipstar-eq-re`. It has no Lean today, and `def:game-description`
  (chapter 2) carries no `\lean` tag either.
- Statement (blueprint): `{(g, p) : g a game description, p ∈ ℚ, synval(G_g) > p}` is
  recursively enumerable, and likewise for `val*`. Lean shape: a `RePred` on
  `GameData × ℚ` in Mathlib's model, then a `Prog` semidecider for the criterion. The
  second step is generic and belongs in `Cost/FromPartrec.lean`: "every `RePred` has a
  well-scoped `Prog` that halts exactly on its members", from
  `Turing.ToPartrec.Code.exists_code` and `ofCode_halts_iff`, the same route as
  `exists_compile`.
- Mathematics (no rounding needed): enumerate *exact* rational strategies. Dimension
  `d`; a unitary with entries in `ℚ[i]` as the Cayley transform `(1 − K)(1 + K)⁻¹` of a
  skew-Hermitian `K` with `ℚ[i]` entries; projective measurements `U P_S U*` for the
  diagonal projections `P_S` of a partition of `Fin d`; for the tensor-product value an
  unnormalized `ℚ[i]` vector, the value being a ratio. The value of such a strategy is an
  exact rational computed by a primitive recursive function, and `synval(G) > p` iff some
  enumerated strategy has value `> p`: every projective measurement is `U P U*` with `U`
  unitary, `U ↦ e^{iθ}U` does not change `U P U*` and can be chosen without eigenvalue
  `−1`, so `U` is a Cayley transform, rational skew-Hermitian matrices are dense, and the
  value is continuous in the strategy. Search over the enumeration semidecides.
  Alternative: enumerate approximately projective rational tuples and round — needs a
  rounding lemma, so the Cayley route is recommended.
- Decision to take first: game descriptions. `MIPRE/HaltingGameValue.lean` is a
  self-contained statement of Theorem 12.2 with its own `GameData`, `toGame` and
  `gameValue`, separate from `MIPRE/Foundations/Games.lean` (`syncValue`, `quantumValue`).
  Either give `def:game-description` a foundations definition and prove it agrees with
  `HaltingGameValue.GameData.toGame`, or make the foundations chapter use `GameData`.
  Recommended: a foundations `GameDescription` with `toSynchronousGame`, and one lemma
  relating it to `HaltingGameValue`.
- Deliverables: `MIPRE/Foundations/ValueApprox.lean` (enumeration, density, the `RePred`
  statement, its `Prog` form); the `FromPartrec.lean` lemma; `\lean`/`\leanok` on
  `lem:value-lower-approx` and `def:game-description`; the chapter-3 table row.

### 5. #22 / #23 — synchronous transport (`thm:almost-sync`)

- Why: the soundness of `thm:parallel-repetition` (value form) argues
  `synval(V_n) ≤ 1 − ε ⇒ val*(V_n) ≤ 1 − ε'` through `thm:almost-sync` (Vidick 2022,
  arXiv:2103.02468v3, Corollary 3.3) before applying `thm:direct-repetition-q`, and
  returns with `lem:sync-le-valstar` (formalized). The chapter-6 soundness statements are
  all in `synval`, so the same transport appears wherever a tensor-product result (the
  direct repetition theorem, the LIDT soundness theorem) is invoked.
- Plan: (i) `thm:orthonormalization` as a standalone lemma (issue #22 suggests it first);
  (ii) `thm:almost-sync` in finite dimension (#22); (iii) the commuting case (#23, Lin
  2023, arXiv:2304.01940), needed only for the MIP^co track and best done after (ii) with
  a parallel statement. Suggested location: `MIPRE/Background/Synchronous/`, statements in
  the vocabulary of `Foundations/Games.lean`.
- The constants `a` and `b = 13a` in `thm:parallel-repetition` are provisional
  (`sec:conventions`) and are fixed by whatever (ii) proves.

### 6. #29 — `lem:tracial-le-co` (GNS), and the tracial-density restatement

- `commValue G ≤ commutingOperatorValue G.toGame` via the GNS representation
  `L²(𝒜, τ)` of a tracial state, with left multiplication for Alice and right
  multiplication for Bob (issue #29 has the sketch and the Mathlib notes; the vendored
  `StdTracialAlgebra` of `CommutingRepetition/Statement.lean` is a template but may not be
  referred to). Location: `MIPRE/Foundations/` (`CommutingOperator.lean` or a new
  `GNS.lean`). Needed to use `thm:direct-repetition-co` for tracial values of repeated
  synchronous games and for the MIP^co track; not on the main-theorem path.
- `thm:tracial-density`: `MIPRE.Repetition.tracialDensity`
  (`MIPRE/Background/Repetition/TracialDensity.lean`) re-exports the vendored hypothesis
  `CommutingRepetition.TracialDensityHypothesis` verbatim. Restate it through the
  foundations definitions (tracial states and projective measurements of
  `Foundations/Games.lean`, `commValue`) once the GNS material of #29 exists, since both
  use the same `L²(𝒜, τ)` construction; then point the blueprint's `\lean` at the
  restated theorem.

### 7. Audit chapter 6 (value form) against Lin's propositions — blueprint only

- Risk 5 of `repetition-port.md`. The D8 restatements of `thm:introspection`,
  `thm:oracularization`, `thm:answer-reduction`, `thm:parallel-repetition` and
  `thm:compression` were obtained from JNVWY's value-form clauses by removing the
  entanglement clauses and replacing the repetition step; Lin's versions
  (arXiv:2510.07162, `Seqandcompression.tex:408–587`) use a different index convention
  (same `n`, runtime `n^α → polylog n`, against JNVWY's `N = 2^n`).
- Check node by node: parameters and time bounds compose across the four
  transformations; the instantiation of `lem:compressible-criterion` in
  `rem:compression-abstract` — the classes `A` (descriptions with a value-1 PCC strategy)
  and `B` (synchronous value at most ½), and whether the paper's compression input
  (a normal-form verifier `V` and an index) is a succinct description in the sense of
  `IsSuccinctDesc c m x` (a program computing the bits of the game description `x` from
  the index `m`), which is what `Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr` receives;
  and that no per-level loss appears in value form (JNVWY's factor ½ per level lives only
  in the `Ent` clause, `rem:entanglement-form`).
- Output: corrections to chapter 6 and, from them, the sub-issue list for the chapter-6
  formalization track (the next large track after this one).

### 8. Maintenance decisions (open)

- (a) The tree-wide `try rfl` rule of `scripts/vendor-lidt.py` (292 lines in the vendored
  LIDT tree) versus a recorded per-site list. Recommendation: keep the rule until the
  next upstream MIPStarRE update; if upstream has moved to Lean ≥ v4.33 by then, drop
  both the rule and the tree-wide transparency option and re-vendor.
- (b) `backward.isDefEq.respectTransparency false` at project sites (file-wide in
  `TM/Code/Evaluator`, `LCS/SolutionGroup/Representation`, `LIDT/Bridge/Measurement`; per
  declaration in `TM/Code/Semantics`, `LCS/WinningCondition`, `LCS/Strategy/Equivalence`):
  each is a small proof rewrite away from not needing the option. Do it when touching the
  file; never reintroduce a project-wide setting (it broke other modules).
- (c) `set_option autoImplicit true` in the 131 vendored files (D3(c)): test removal now
  that Lean runs in sessions; drop the insertion from both vendoring scripts if unneeded.
- (d) Upstream pins: commuting-repetition `cfa2f1b`, ten-proofs `94bc0fe`, MIPStarRE
  `507e812`. Re-vendor only with the scripts, then re-validate every recorded fix.
- (e) CI wall time is 35–40 minutes per run (the ten-proofs module alone 20–32 minutes);
  if it becomes a bottleneck, cache `.lake/build` of the vendored directories keyed on
  their tree hash. With Lean in sessions, prefer local `lake build MIPRE.<Module>` and
  use CI runs for the final check only.
- (f) Untouched open issues: #17, #18 (universal machine, `planning/tm-infrastructure.md`),
  #5 (QuantumLib dependency).

## Working conventions for the next sessions

- Lean in cloud sessions: `docs/lean-cloud.md`. Check a module with
  `lake build MIPRE.<Module>`; never `lake build` Mathlib, never `lake update`. Until
  item 1's re-save has happened, a session can reproduce the setup by hand in a few
  minutes (same page, "Using Lean from a session").
- CI (`build-project.yml`): dispatch only when no run is in progress on the branch
  (the concurrency group cancels the running one); Lake skips dependents of a failing
  module, so a CI-only workflow surfaces failures one dependency layer per run.
- Blueprint: builds only on `main`; check labels, `\uses`, `\cite` targets and `\lean{}`
  names mechanically before merging, and watch the first run after each merge (item 2).
- Pull requests: `Closes #N`, label `awaiting-review`, squash merge; commit messages
  name the tracking issue.

## Dependencies

```
1 → 2
3 ─────────────────────→ thm:direct-repetition-q \leanok
4 ─────────────────────→ thm:halting (hypothesis hS); thm:mipstar-eq-re (⊆)
5 (with 3) ────────────→ thm:parallel-repetition soundness
6 ─────────────────────→ MIP^co track; tracial statements of chapter 5
7 ─────────────────────→ chapter-6 formalization track (statements fixed first)
```
