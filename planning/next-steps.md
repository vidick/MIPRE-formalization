# Next steps after the direct-repetition port — roadmap

Written 2026-09-11 at the maintainer's request ("make and record a plan so we don't
forget what we are doing"), when PR #30 was open and awaiting review. Companion of
`planning/repetition-port.md` (the port itself, decisions D1–D8),
`planning/compression-track.md` (the `Cost/` toolkit) and `planning/tm-infrastructure.md`
(universal machine, issues #17/#18). Conventions as in those files: verified facts,
decisions, items with a done criterion, risks. Update the status column as items move.

## Where things stand (2026-09-11)

- PR #30 was squash-merged into `main` as `0f8b408` on 2026-09-11 at 14:06 UTC, closing
  #27. The project build on `main` after the merge passed (run 34608202234, 43 minutes),
  and so did the first blueprint deployment (run 34608202078: 43 minutes of Lean, then
  2 h 06 of blueprint, doc-gen and Pages, all green). A full local build of the branch
  under Lean v4.33.0 inside a cloud session (533 modules of this repository plus the
  Mathlib cache) finished with exit code 0 and no errors in 41 minutes of wall-clock time
  (105 CPU-minutes) — the first Lean check ever run inside a session for this repository.
- An external referee report on the blueprint arrived the same day and is the source of
  the repairs recorded in the last section of this file; the value-form pipeline now
  carries its soundness in `val*` from the repetition step outwards.
- After the merge the path to the main theorem is in *value form* throughout (D8): no
  entanglement lower bound is stated or needed anywhere.
- Still `sorry` or blueprint-only on that path, in order of appearance:
  `lem:sync-le-valstar` (a `sorry` in `MIPRE/Foundations/Games.lean:653`, and after the
  value-form repair it is load-bearing in three places: the soundness clause of
  `thm:compression`, `thm:halting` and `cor:main-quantum`),
  `lem:povm-value-eq` (#28, one `sorry`), `thm:almost-sync` (#22, no Lean, and false as
  printed until 2026-09-11), `lem:value-lower-approx` (no Lean), and the whole of chapter 6
  (introspection,
  oracularization, answer reduction, `thm:parallel-repetition`, `thm:compression`,
  `thm:halting`), unchanged by the port. The `Cost/` toolkit statements that the
  universal machine still owes are tracked in `planning/tm-infrastructure.md`.
- Off the main path but part of the port's follow-ups: `lem:tracial-le-co` (#29),
  the restatement of `thm:tracial-density` in foundations vocabulary, and the
  commuting-operator (MIP^co) track that `thm:direct-repetition-co` opens.

## Items, in the recommended order

| # | Item | Blocks | Effort | Status |
|---|---|---|---|---|
| 1 | PR #30 review and merge; cloud environment re-save | 2 | maintainer | merged 2026-09-11; re-save outstanding |
| 2 | First blueprint build on `main` | — | small | done 2026-09-11 (run 34608202078 green) |
| 3 | #28 `lem:povm-value-eq`: close the entangled bridge | `\leanok` on `thm:direct-repetition-q`, item 4 | medium | open |
| 4 | `lem:value-lower-approx` in Lean, `val*` half (MIP* ⊆ RE; hypothesis `hS` of the criterion) | `thm:halting`, `thm:mipstar-eq-re` | medium–hard | open |
| 5 | #22 `thm:almost-sync`, with the diagonal-weight hypothesis (then #23, commuting case) | `thm:parallel-repetition` soundness | hard | open |
| 6 | #29 `lem:tracial-le-co` (GNS); restate `thm:tracial-density` | MIP^co track | medium–hard | open |
| 7 | Audit chapter 6 (value form) against Lin's propositions | chapter-6 formalization track | blueprint only | open |
| 8 | Maintenance decisions (`try rfl` rule, transparency options, `autoImplicit`, upstream pins, CI time) | — | small each | open |
| 9 | `lem:sync-le-valstar` in Lean (a `sorry`; transpose of a synchronous strategy on the maximally entangled state) | `thm:compression`, `thm:halting`, `cor:main-quantum` | small | open |
| 10 | The referee report's deferred findings (last section of this file) | chapter-6 track | see there | open |
| 11 | The synchronization invariant `rem:sync-invariant`: preserved by each transformation | `thm:parallel-repetition` soundness | medium | open |

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
  `MIPRE.Cost.compressibility_criterion` with `B` the descriptions of games of **quantum**
  value at most ½ (`rem:compression-abstract`, `thm:halting`, both in `val*` since the
  value-form repair), and by itself the easy inclusion of `thm:mipstar-eq-re`. It has no
  Lean today, and `def:game-description` (chapter 2) carries no `\lean` tag either.
- Statement (blueprint): `{(g, p) : g a game description, p ∈ ℚ, synval(G_g) > p}` is
  recursively enumerable, and likewise for `val*`. Only the `val*` half is needed: the
  `synval` half is not a corollary of it, since rounding a strategy's entries preserves
  neither projectivity nor synchronicity. Lean shape: a `RePred` on
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
  exact rational computed by a primitive recursive function, and the value `> p` iff some
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

- Why: the soundness of `thm:parallel-repetition` argues
  `synval(V_n) ≤ 1 − ε ⇒ val*(V_n) ≤ 1 − ε'` through `thm:almost-sync` (Vidick 2022,
  arXiv:2103.02468v3, Corollary 3.3) before applying `thm:direct-repetition-q`. After the
  value-form repair this is the *only* use of the transport in the blueprint, and it is on
  the un-repeated game: the repeated game's soundness stays in `val*`, so the transport is
  never applied to a `k`-fold product (whose diagonal weight decays as `κ^k`). The
  statement to formalize is the corrected one, with the diagonal-weight hypothesis
  `μ(x,x) ≥ κ·Σ_y μ(x,y)`; without it the theorem is false (`rem:almost-sync-hypothesis`).
  The other direction, `synval ≤ val*` (`lem:sync-le-valstar`), is item 9: it is a `sorry`.
  Chapter 6's soundness analyses still invoke bipartite rigidity results
  (`thm:lidt-soundness`, `thm:qld`, both stated for tensor-product strategies), whose
  synchronous restatement is separate work; that is a different use of the transport from
  the one inside repetition, and it does not disappear with the value-form repair.",
     "item 5: the corrected hypothesis and the single use site")

edit("planning/next-steps.md", ## The external referee report of 2026-09-11

Source: the adversarial-verification campaign on `vidick/mipre-proof` (paper and
ledger at `4768735`, branch `claude/install-vibefeld-mipre-eythiq`), reporting against
`main` at `7f5a45a` and the port branch at `d3e6b95`. Five referees read one departure
each, plus a sixth pass over their own 120-node ledger. Verdict: *adopt the architecture,
not yet the text* — the value-form pipeline with Lin's criterion and direct repetition
dissolves an obstruction their round 7 spent two rounds on, and their parameter sweep
closes the pipeline arithmetic with room to spare, but one theorem on the critical path
was false as printed.

Every finding acted on below was re-derived here before being accepted; the
counterexample of §1 and the ¼ arithmetic of §11 were checked independently, and one
defect the report missed was found in the process (`thm:answer-reduction`, like
`ComputeRepeatedVerifier`, takes no level parameter although its output level is
`max{ℓ+2,5}`).

### Adopted

| Finding | Report | Change |
|---|---|---|
| `thm:almost-sync` is false as printed: no diagonal-weight hypothesis, and a two-question game separates the two values (`val* = 1`, `synval = ½`) | §1 | corrected statement with `μ(x,x) ≥ κ·Σ_y μ(x,y)` and the bound `C(ε/κ)^c`; `rem:almost-sync-hypothesis` records the counterexample and that the hypothesis decays as `κ^k` under repetition |
| The corrected theorem is unusable where chapter 7 used it (the final game is a `k`-fold repetition) | §1 | `thm:parallel-repetition` and `thm:compression` soundness conclude in `val*`; `B = {val* ≤ ½}`; `thm:halting` concludes `val* ≤ ½`; chapter 7 gains `cor:main-quantum` and no longer transports between the values |
| Only the `val*` half of `lem:value-lower-approx` is available (rounding breaks synchronicity), and it is the half the criterion needs | §2 | recorded in the lemma's comments and in `rem:compression-abstract` |
| Level counts inconsistent: the chain gives 7, `thm:compression` claimed 9 | §5 | 7 in and 7 out, with the chain, the padding convention and the reason the paper says 9 |
| The level parameter is not an input of the repetition machine (it never was, on either side of the change; the report calls it dropped) | §5 | added to `ComputeRepeatedVerifier` and to `ComputeAnsRedVerifier`, where the output level `max{ℓ+2,5}` makes it indispensable |
| Additive approximation: ¼, not ½ | §11 | `08_downstream.tex` states `c < ¼`, and `c < ½` after amplification by direct repetition, flagged as depending on the repetition theorem |
| The factor ½ appears in the composed entanglement bound but in no stage | §7 | attributed to answer reduction in `rem:entanglement-form`, with its origin (Schmidt-rank doubling in symmetrization) and why the synchronous framework does not pay it |
| "Symmetrizing makes it synchronous" is false | §9 | corrected in `def:normal-verifier`; `rem:sync-invariant` states the invariant the pipeline actually needs and marks it open |
| "symmetric PCC" survives although PCC and SPCC were identified | §9 | both occurrences in chapter 6 |
| Chapter 5 over-claims ("these theorems are formalized") | §4 G1 | the opening now says which of the two is formalized end to end |
| The criterion's inductions are along the chain levels, not "every level"; two facts are used implicitly | §3 | proof text in chapter 4 corrected and the two facts stated |

Not adopted: G6 ("nothing on the branch had compiled") is out of date — CI was green on
`c7d27e5`, the merge commit's build passed, and the whole library builds locally under
Lean v4.33.0.

### Deferred, with owners

- **R1 — the four obligations of the instantiation** (§3). Named in
  `rem:compression-abstract` now, unsolved: (a) the criterion's strings are descriptions,
  never games; (b) `Compr` receives a succinct description and cannot read the described
  verifier, whereas `thm:compression` reads it verbatim — closing this touches the
  introspection and answer-reduction machines, whose descriptions hardwire the decider;
  (c) the criterion demands preservation of `A` and `B` for *every* string while
  `λ`-boundedness is undecidable, so either the lemma is re-quantified over a
  `Compr`-closed class or preservation is proved for junk inputs; (d) `λ` must be chosen
  along the recursion, whose descriptions grow with the level. The report considers the
  trade favourable even so (the criterion retires their `fig:halt_f`, the `C_halt`
  non-circularity argument and `lem:dhalt-values`). This is the substance of item 7 and
  needs a new issue.
- **R2 — the semidecider is available** (§2, §14). `paper/recursive.tex`, `cor:mip-re`:
  a machine that on `(t, G)` halts iff `val*(G) > t`, boundary case `val* = t` correctly
  non-halting, candidate strategies with entries in `(1/k)ℤ[i]`, stability and density
  with explicit constants, three verification passes and a claim-test. Feeds item 4
  directly. Caveat for this repository: `MIPRE.quantumValue` ranges over *projective*
  measurements, so their rounding argument transfers only after #28
  (`quantumValue = entangledValue`, POVMs and mixed states) — which makes #28 a
  dependency of item 4, or else the Cayley-transform route of item 4 is needed. Totality
  (malformed strings must land in `B`, and the decoder must be total) is the place where
  the deferred timeout-counter layer is genuinely consumed.
- **R3 — obligations the direct route inherits** (§6). The answer alphabet of `V^rep_n`
  is all strings of length `≤ TIME_{D^rep}(n)`, which strictly contains `A^k`, so the
  decider must parse a self-delimiting tuple and reject malformed ones; the `Λ(n)` band
  between `TIME_D(n)` and the decider's cutoff is papered over by the answer-length
  convention; and the repeated sampler being "a product of conditionally linear functions
  of the same level" is a closure lemma the blueprint does not have — there is no CL
  closure lemma anywhere, and `thm:parallel-repetition`'s `\uses` cites none. Their
  `lem:answer-truncation` and `cor:timeout-truncation` are offered and referee-verified.
  New issue; blocks the chapter-6 formalization track.
- **R4 — `thm:orthonormalization` is over-hypothesized** (§8). It assumes a normal
  *faithful tracial* state; de la Salle's Theorem 1.2 needs only a normal state, gives
  constant 9 and exponent 1, and returns a full PVM in the algebra. The tracial
  hypothesis blocks the bipartite vector-state applications that most projectivization
  sites need. They also offer `lem:ortho` with `η = O(δ)` in place of `O(δ^{1/4})`
  (`paper/qld-prelim.tex`, two independent verifiers). Citation slip to fix at the same
  time: the `ε^{1/4}` predecessor is attributed here to KPS18 and JNVWY20, by de la Salle
  to the JNVWY low-degree paper and KV11. Attach to #22 (the transport work uses it).
- **R5 — typed verifiers: dropped in name, kept in arithmetic** (§10). `def:sampler`
  admits one pair of CL functions on one space, and nothing assembles a question
  distribution from structurally different sub-distributions selected by a type graph,
  which introspection and answer reduction both need. Every number the blueprint carries
  (5 levels for introspection, `max{ℓ+2,5}`, now 7 for compression) is a detyped number;
  typed, they would be 3, `max{ℓ,3}` and smaller. Decide whether to carry typed samplers
  or to own the detyping: two graph-simulation constructions and four bespoke CL
  realizations, each with a `16^{|T|}` loss. New issue.
- **R6 — vendored-source errata to record** (§12). NW19's Tseitin construction omits the
  output-wire conjunct (their `AUDIT-ERRATA.md` F7.2): `thm:succinct-sat` states only the
  end-to-end iff, so it does not inherit the defect, but it drops the two hypotheses the
  repair needs and never fixes the variable count the PCP parameters depend on. Tensor
  codes and the Vid21 interface: `κ`-convexity needs `c₁ ≤ 1`, `δ_sync ≤ 4ε` not `3ε`, a
  transpose slip in `extensions.tex`. Also: Magic Square rigidity's source becomes WBMS16,
  and whether the self-dual-basis import is needed at all. Comments paragraphs, cheap.
- **R7 — round-11 additions** (§13). Their `lem:ar-ora` had a real gap (decoded answers
  longer than the oracularized decider's parsing bound), repaired by truncating the
  decoding; the blueprint states `thm:answer-reduction` without proof, so the gap will
  appear when that proof is written. A `q²` loss in one of the 17 internal lemmas of
  `thm:qld` needs Parseval over `F_q²`. And the identical-measurement-operators provenance
  chain, which their proof needs through four transformations, is definitional in the
  synchronous framework: a simplification this blueprint gets for free and should claim.
- **R8 — errata on the transport's own sources** (§1, end). Vid21 `cor:c2`'s proof applies
  `lem:close-cor` one-sidedly and needs two mirrored applications, each costing
  `O(√γ_λ)`; and the exact interface between JNVWY's product-basis transposes and Vid21's
  Schmidt-diagonal symmetric strategies is *false* (2×2 counterexample, ledger
  `1.2.1.7.2.4`), needing their approximate Takagi bridge
  (`paper/external/vid21/INTERFACE-BRIDGE.tex`). Their re-derivation puts the source
  exponent at `c = 1/64` for the main theorem and about `1/256` in value form; the
  constants of `thm:almost-sync` and `thm:parallel-repetition` should be pinned to that
  when item 5 is worked out. Attach to #22.
- **R9 — offered contributions** (§14). Besides R2, R3 and R4: CL closure lemmas
  (`paper/linear.tex`), a parameter table for compression with two large claim-tests, and
  the errata files. Their side has adopted `B = val*` and the de la Salle bridge, and is
  gating the synchronous route and the abstract compression on their items 1–4.

### Working conventions for the next sessions
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
  and `B` (quantum value at most ½), and whether the paper's compression input
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
