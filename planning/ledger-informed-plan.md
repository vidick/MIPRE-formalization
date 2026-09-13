# Formalization plan informed by the vibefeld ledger

Written 2026-09-13. Companion of `planning/next-steps.md` (the roadmap, items 1–11),
which it *reorders and corrects* rather than replaces. Source: the `af`/vibefeld
campaign in `vidick/mipre-proof`, branch `claude/install-vibefeld-mipre-eythiq`
(HEAD `11a03e8`, "Round 12 closed"), whose ledger is
`proofs/mipre-undecidability/ledger/` — 1732 events, 18 Aug to 12 Sep 2026.

## What the ledger is, and why it is worth reorganizing around

Replayed from the event log rather than read from a summary:

| | |
|---|---|
| nodes | 123 |
| currently validated | 120 |
| admitted (assumed) | 3 |
| challenges raised / still open | 291 / **0** |
| claim-tests | 12 Python checkers, each with a recorded `.out` |
| repairs marked in the paper source (`\cnote{}`) | 318 |

The three admitted nodes are declared external imports, not gaps: anchored parallel
repetition (BVY Thm 6.1, node `1.4.2`), Magic Square rigidity (Coladangelo–Stark
Thm 6.9, `1.2.2.4.1`), efficient self-dual normal bases (Shoup/Lenstra/Wang,
`1.1.6.1`).

So the ledger is a *dependency-ordered decomposition of the whole proof into 123
statements, each adversarially challenged and re-validated*. That is precisely the
artifact a blueprint wants and does not have.

## Finding 1 — chapter 6 is nine monoliths; the ledger has the decomposition

Blueprint Lean coverage, counted over labelled environments:

| chapter | envs | `\lean{}` | proof `\leanok` |
|---|---|---|---|
| 02 foundations | 28 | 20 | 1 |
| 03 background | 14 | 4 | 2 |
| 04 computability | 11 | 11 | 5 |
| 05 repetition | 24 | 7 | 4 |
| **06 pipeline** | **9** | **0** | **0** |
| 07 main theorem | 4 | 0 | 0 |
| 08 downstream | 5 | 0 | 0 |

Chapter 6 is `thm:introspection`, `thm:oracularization`, `thm:answer-reduction`,
`thm:parallel-repetition`, `thm:compression`, `thm:halting` and three supporting
items — six statements each of which is an entire paper chapter, with no `\lean{}`
name and therefore no work surface. The ledger covers the same material in ~110
nodes. Its challenge counts are a measured risk map:

| ledger stage | nodes | challenges | amendments | admitted | blueprint counterpart |
|---|---|---|---|---|---|
| 1.1 framework | 21 | 35 | 11 | 1 | chapter 2 (well covered) |
| **1.2 introspection + QLDT** | **62** | **169** | **44** | 1 | `thm:introspection`, `thm:qld` |
| 1.3 answer reduction | 13 | 46 | 5 | 0 | `thm:answer-reduction` |
| 1.4 parallel repetition | 8 | 19 | 7 | 1 | `thm:parallel-repetition` |
| 1.5 compression | 9 | **6** | 4 | 0 | `thm:compression` |
| 1.6 recursion / halting | 8 | 13 | 6 | 0 | `thm:halting` |
| 1.7 conclusion | 1 | 1 | 2 | 0 | `cor:main-quantum` |

Two things fall out. Stage 1.2 absorbed 58% of all challenges over 50% of the
nodes and is where formalization would catch the most — and cost the most; node
`1.3.4` (answer-reduction composition, `ld_compiler.tex`) alone took **29
challenges**, the most contested single node in the campaign. Stage 1.5
(compression) took **6 challenges over 9 nodes** and is the cleanest part of the
pipeline — and the one whose abstract engine, `MIPRE.Cost.compressibility_criterion`,
is already proved sorry-free here.

## Finding 2 — the audited proof never uses the synchronous value

**No ledger node mentions the synchronous value, `val^s`, or synchronisation at
all.** Searched over all 123 statements. The audited proof is in the bipartite
tensor-product value `val*` from node 1 to node 1.7.

This repository, by contrast, states chapter 6's three inner transformations in
`\synval` and therefore owes:

* `lem:sync-le-valstar` — a `sorry` at `MIPRE/Foundations/Games.lean:653`, roadmap item 9;
* `thm:almost-sync` — roadmap item 5, issue #22, effort *hard*, **false as printed**
  until the 2026-09-11 repair, and needing the diagonal-weight hypothesis
  `μ(x,x) ≥ κ·Σ_y μ(x,y)` that `rem:almost-sync-hypothesis` shows cannot be dropped;
* `rem:sync-invariant` — roadmap item 11, establishing that synchronicity and
  diagonal weight survive each transformation, currently open.

None of that debt is incurred by the proof the ledger validated. It is the price of
a framing choice. The 2026-09-11 referee report already forced soundness back into
`val*` from the repetition step outwards, and showed the transport can never
conclude better than `val* ≤ 1/2` — so the synchronous route is already not
load-bearing for the *threshold*; what remains is its use inside chapter 6.

**This is a decision for the maintainer, not something to act on unilaterally**, and
it is the highest-leverage question on the table: restating chapter 6 bipartitely, as
the ledger does, retires roadmap items 5, 9 and 11 and one hard external theorem.
Against that, `MIPRE.syncValue` and the synchronous machinery already exist here and
chapter 6's sources (Vid21/Vid22) are synchronous, so the cost is a re-derivation of
chapter 6's statements against JNVWY's bipartite originals — which is what
`paper/` in `mipre-proof` already contains.

## Finding 3 — MIP* ⊆ RE is fully decomposed in the ledger, and roadmap item 4's open decision is settled

Nodes `1.1.7.2` and its five children are validated, challenge-free at the leaves,
and carry four of the twelve claim-tests. They give the semidecider end to end:

| node | content | tests |
|---|---|---|
| `1.1.7.2` | statement S: a machine `E` that on `(G, t)` halts iff `val*(G) > t`; **no infinite-dimensional truncation and no SDP**, because `val*` is by definition a sup over finite-dimensional strategies | — |
| `1.1.7.2.1` | exact arithmetic: the value of a Gaussian-rational candidate is exactly computable; psd of a Gaussian-rational Hermitian matrix is decidable by the characteristic-polynomial sign criterion `(-1)^{n-j} c_j ≥ 0`; `‖M‖ ≤ c` reduces to two psd tests | 1 |
| `1.1.7.2.2` | candidate set at stage `(d,k)`: `k₀ = 2d(|A|+|B|+2)`, `η = d/k`, entries in `(1/k)ℤ[i]` of modulus ≤ 2; constraints (i)–(iv) force finiteness | — |
| `1.1.7.2.3` | **stability**: every candidate is within `Δ(d,k) = 250(|A|+|B|)²d/k` of an exact strategy, via `T_x^{-1/2}` normalization with `spec(T_x) ⊆ [1/2,2]` | 1 |
| `1.1.7.2.4` | **density**: every exact strategy has a candidate within `Δ(d,k)`, by entrywise rounding to `(1/k)ℤ[i]` with ties toward zero | 1 |
| `1.1.7.2.5` | the halting biconditional, dovetailing over `(d,k)`, including `val* = t` correctly non-halting | 1 |
| `1.1.7.2.6` | extensions; notes the exact side is **WLOG projective by Naimark**, and why the argument fails for `val^co` (whence MIP^co ⊆ coRE) | 1 |

Roadmap item 4 currently records two candidate routes and recommends the Cayley
transform, because the alternative — "enumerate approximately projective rational
tuples and round" — "needs a rounding lemma". **The ledger takes that second route
and supplies the rounding lemma** (`1.1.7.2.4`), with the stability counterpart
(`1.1.7.2.3`), explicit constants, and claim-tests on both. So item 4's open
decision is settled in favour of the route the roadmap set aside, and the Cayley
machinery is not needed.

Its one dependency also just cleared: `1.1.7.2.6`'s "WLOG projective by Naimark" is
exactly `lem:povm-value-eq`, proved sorry-free here on 2026-09-12
(`MIPRE.Repetition.quantumValue_eq_entangledValue`).

## Priorities

**P1 — MIP* ⊆ RE, along nodes `1.1.7.2.1`–`.6`.** Delivers the `⊆` half of
`thm:mipstar-eq-re` and the `hS` hypothesis of `MIPRE.Cost.compressibility_criterion`,
hence `thm:halting`'s semidecidability side. It is finite-dimensional linear algebra
plus computability — the two things this repository is already strongest at — it is
independent of the entire chapter-6 pipeline, and it now has a validated
six-node decomposition with explicit constants instead of an open route choice.
Done when `lem:value-lower-approx` carries `\lean{}` and a `\leanok` proof and the
`⊆` direction of `thm:mipstar-eq-re` follows.

**P2 — ~~put Finding 2 to the maintainer~~ — decided 2026-09-13: follow the ledger, carry
`val*` throughout.** Applied to the blueprint the same day: every soundness clause of
chapter 6 is now in `\valstar`, the new `rem:bipartite-route` records the decision and its
evidence, `rem:sync-invariant` keeps its mathematics but loses its obligations, and
`thm:parallel-repetition` loses both the transport's polynomial loss and the factor
`κ^13` — its exponent is now the `13` of `thm:direct-repetition-q` itself. Roadmap items 5
and 11 are off the critical path, item 9 is no longer load-bearing. The cost, recorded
there: the rigidity and approximate-measurement lemmas must be stated bipartitely rather
than tracially, which is what the sources do anyway.

**P3 — expand blueprint chapter 6 along the ledger. Stages 1.5 and 1.6 done 2026-09-13.**
Turn six monoliths into the
ledger's stage decomposition with a `\lean{}` name per statement, starting with
stage 1.5 (compression, 6 challenges, engine already proved) and 1.6 (recursion, 13).
This is blueprint-only work and it is what makes chapter 6 formalizable at all.

**P4 — the inner transformations**, bipartitely, as P2 settled. 169 challenges over
62 nodes; the long haul. `1.3.4` (29 challenges) is where to expect trouble, and the
rigidity and approximate-measurement lemmas are now to be stated bipartitely rather than
tracially.

No longer on the path at all: `thm:almost-sync` (item 5) and the synchronization invariant
(item 11); `lem:sync-le-valstar` (item 9) survives only as the free comparison, used to
read a `val*` conclusion synchronously and never the other way.

## Progress

| ledger node | blueprint | Lean | state |
|---|---|---|---|
| `1.1.7.2.1` (norm constraint half) | `lem:norm-two-psd` | `MIPRE.ValueApprox.posSemidef_realSmul_one_add_and_sub_iff` | proved 2026-09-13 |
| `1.1.7.2.1` (exact arithmetic, psd decidability) | — | — | open |
| `1.1.7.2.2` candidate set finiteness | — | — | open |
| `1.1.7.2.3` stability (the split) | `lem:perturbation-split` | `MIPRE.ValueApprox.dotProduct_mulVec_perturb` | proved 2026-09-13 |
| `1.1.7.2.3` stability (the bound) | — | — | open |
| `1.1.7.2.4` density (the split) | `lem:perturbation-split` | `MIPRE.ValueApprox.kronecker_sub_kronecker`, `dotProduct_kronecker_perturb` | proved 2026-09-13 |
| `1.1.7.2.4` density (the bound) | — | — | open |
| `1.1.7.2.5` halting biconditional | `lem:value-lower-approx` | — | open |
| `1.1.7.2.6` application, MIP* ⊆ RE | `thm:mipstar-eq-re` (⊆) | — | open |
| `1.1.7.2.6` "WLOG projective by Naimark" | `lem:povm-value-eq` | `MIPRE.Repetition.quantumValue_eq_entangledValue` | proved 2026-09-12 |

`MIPRE/Foundations/ValueApprox.lean` is the file; it is sorry-free and stays that way.
The next increment is the rest of node `1.1.7.2.1` — that the value of a
Gaussian-rational candidate is computable exactly, and that psd of a Gaussian-rational
Hermitian matrix is decidable by the characteristic-polynomial sign criterion, neither
of which is in Mathlib — followed by `1.1.7.2.3`/`1.1.7.2.4`, whose engine is a
Lipschitz bound on the Born value in the entries of the data. The three transport
lemmas proved for `lem:povm-value-eq` (`dotProduct_mulVec_submatrix`,
`dotProduct_mulVec_conj`, `dotProduct_comp_equiv`) are the tools for that.

## The ledger is fully accounted for, 2026-09-13

123 of 123 nodes. Stages 1.1 (21), 1.4 (8), 1.7 (1) and the root (1) closed the remainder,
by thirteen annotations on statements that already existed and three new remarks for the
node groups that had no home: `rem:typed-detyping` (node 1.1.4 — typed verifiers, the
`16^-|T|` detyping loss and the +2 levels this blueprint inherits without stating a type
graph), `rem:tm-conventions` (nodes 1.1.5.x — the paper's timeout-counter formalism, which
the cost model of `sec:rr-computability` replaces, keeping the three details a formalization
would otherwise rediscover the hard way) and `rem:admitted-nodes`.

`rem:admitted-nodes` is the one worth reading. With everything named, the assumptions are
countable: of 123 nodes, 120 are validated and exactly three are admitted, and the
value-form route treats them very differently.

- **Anchored parallel repetition** (1.4.2, `thm:bvy`) — **not used at all.** Direct
  repetition replaces it, is formalized end to end, and takes a value hypothesis. One of
  the three admitted nodes leaves the pipeline entirely.
- **Magic Square rigidity** (1.2.2.4.1, `thm:ms-rigidity`) — used through a single
  anticommutation consequence, and not at all by the completeness leg, whose in-file
  argument is already in Lean (`lem:mermin-peres`).
- **Efficient self-dual normal bases** (1.1.6.1, `lem:self-dual-basis`) — unavoidable, and
  the only genuinely load-bearing one. Also the most benign: three classical
  computational-algebra results, and the source of the `q = 2^k`, `k` odd convention.

So what this blueprint assumes beyond Mathlib is one classical algebra lemma and one
rigidity theorem used through one consequence — a smaller surface than the paper's, and
smaller *because of* the value form and direct repetition.

Also checked while closing the root: live node `1` gives undecidability of approximating
`val*` to additive error `< 1/4`, and notes that pushing the threshold to `1/2` needs a
further gap-amplification step it does not carry out. `ch:downstream` already says exactly
this, with the reason (`at c = 1/4 the estimate 3/4 is consistent with both`) and with the
`1/2` form flagged as depending on the repetition theorem. No correction needed — the
blueprint was already the more careful of the two.

## Stage 1.2, done 2026-09-13

62/62 nodes — the heaviest stage, 169 of the campaign's 291 challenges — by four
annotations and three new remarks, plus five new chapter-2 statements that give the `LCS/`
Lean development something to be named by. Three findings.

**The formalization is stronger than the paper on node `1.2.1`.** The ledger marks it
*imported*: the paper obtains quantum soundness of the simultaneous low-degree test by
reducing to the tensor-codes theorem, which it does not reprove. But
`MIPRE.LIDT.lowIndividualDegree_soundness` is proved from Mathlib alone through the
vendored MIPStarRE formalization, with an `#print axioms` guard that fails the build if it
ever becomes an axiom. All 28 nodes of the subtree are therefore accounted for as the
internal structure of a finished proof. The formalization also corrected the statement:
the printed constraint is `md <= k`, the proof needs `400 md <= k` and `k > 0`, and the
blueprint already states the corrected form (checked, not assumed). Recorded in
`rem:lidt-formalized`, which also carries node `1.2.1.7.2.4`: the interface between
JNVWY's product-basis transposes and Vid22's Schmidt-diagonal symmetric strategies is
*false* as stated, with a 2x2 counterexample. It does not touch `thm:lidt-soundness`, but
it is a hazard for anything reusing the transpose trick.

**Stage 1.2 holds the only admitted node the pipeline actually consumes.**
`thm:ms-rigidity` is node `1.2.2.4.1`, one of three admitted nodes in the whole campaign,
an import of Coladangelo--Stark Thm 6.9 that is neither vendored nor reproved. It is
consumed narrowly — one anticommutation consequence, and not at all by the completeness
leg, which uses the in-file argument that anticommuting observables give a perfect Magic
Square strategy. That argument is already in Lean, and is now `lem:mermin-peres`.
`scripts/ledger-sync.py` emits a standing Note that a cited node is admitted, which is the
checker working as designed.

**The soundness of `thm:qld` is not in the main text.** It is deferred to a five-file
appendix, which is where most of stage 1.2's challenge weight sits, including the
campaign's only *critical* finding (node `1.2.2.15`: the exact-Pauli construction rested
on a false identity between a codeword's coordinates and the polynomial's values, replaced
by a Schwartz--Zippel bound). A formalization should treat the appendix as the content and
the main-text statement as its interface. Recorded in `rem:qld-admitted`.

**The `LCS/` coverage gap is now half closed.** Five new chapter-2 statements name 16 Lean
declarations, all verified sorry-free: `def:observable`, `lem:observable-projector`,
`lem:observable-strategy` (the observable-to-projective-strategy construction of
`LCS/Strategy/Equivalence.lean`), `def:magic-square` and `lem:mermin-peres`. Modules the
blueprint accounts for: 29 -> 34 of 80; distinct Lean names cited: 75 -> 91. What remains
unnamed in `LCS/` is the Pauli group development (`LCS/Pauli.lean`, 31 declarations),
`LCS/EPR.lean` and `LCS/SolutionGroup/Representation.lean` — the natural next increment,
and the one that would give `thm:qld` a Lean-side foothold.

Stage coverage now: 1.2 at 62/62, 1.3 at 13/13, 1.5 at 9/9, 1.6 at 8/8; 95 of 123 nodes
annotated. What is left is 1.1 (framework, 21 nodes, carried by chapter 2 without
annotations), 1.4 (repetition, 8 nodes, chapter 5), 1.7 (separation, chapter 8) and the
root.

## Stage 1.3, done 2026-09-13

13/13 nodes, by three annotations, two new statements and three new remarks. Two
statement-level repairs came out of reading `paper/oracularization.tex` and
`paper/ld_compiler.tex` against the blueprint:

- `thm:oracularization` said `\delta(\eps) = \poly(\eps)`. The audit shows `\delta_ora`
  carries one square root (the step from measurement closeness to a value statement is
  NW19 Fact 4.31, not an identity), and `\sqrt\eps` is not a polynomial in `\eps`. Now
  `O(\sqrt\eps)`. Its completeness clause also gains *identical measurement operators* —
  SPCC was withdrawn upstream because nothing symmetrizes a value-1 PCC strategy while
  preserving projectivity, consistency and value 1 — and a note that the oracle families
  are projective, outcomes failing the bounded parse being grouped into one distinguished
  outcome.
- `thm:pcp-decider` (new) states the validity inequalities as *exact* (`|x|, |y| <= Q`)
  and carries the hypothesis that `m` is a power of two. That is a confirmed upstream
  defect: the `m`-variate low-degree test needs `m | q` with `q` a power of two, but only
  the outer count `m' = 5m + 5 + s` was guaranteed to be one. `rem:pcp-power-of-two`
  records it.

`rem:ar-composition` accounts for node `1.3.4`, which carries 29 challenges — more than
any other node of the campaign. Four are structural (the direct sum over two different
fields, the consistency subtest omitted from the low-degree hypothesis, projectivity
missing from Claim ar-4, and the `B_D(n)` truncation), and one does not reach this
blueprint at all: JNVWY's answer reduction carries `Ent(V^ans_n, 1-\eps) >= (1/2)
Ent(V_n, 1-\delta)`, the recursion consumes that `1/2`, and the campaign found the factor
is not delivered by the written proof because the symmetrization it opens with doubles the
Schmidt rank. The value-form pipeline has no entanglement clause to get wrong. That is the
fourth place it is strictly cheaper rather than merely equivalent, after
`rem:direct-vs-anchored`, `rem:compression-chain` and node `1.5.8`.

Stage coverage now: 1.3 at 13/13, 1.5 at 9/9, 1.6 at 8/8; 33 of 123 nodes annotated.

## Stages 1.5 and 1.6, done 2026-09-13

Both are fully accounted for: 9/9 nodes of stage 1.5 and 8/8 of stage 1.6, which
`scripts/ledger-sync.py` reports. Eight new blueprint statements, not seventeen — the
principle is that every node is *accounted for*, not that every node becomes a statement.
The umbrella and assembly nodes are annotations on `thm:compression` and `thm:halting`,
the three per-stage bookkeeping nodes are annotations on the chain remark, and the
remaining nine are statements in their own right:

| ledger node | blueprint | why |
|---|---|---|
| `1.5`, `1.5.7` | `thm:compression` (annotated) | umbrella and assembly |
| `1.5.1` | `lem:compress-sampler-indep` | the recursion needs it: a fixed point must quote its own sampler |
| `1.5.3` | `lem:compress-margin` | pure arithmetic on the imported constants; claim-tested upstream |
| `1.5.5` | `lem:compress-tau` | ditto |
| `1.5.2`, `1.5.4`, `1.5.6`, `1.5.8` | `rem:compression-chain` | the staged chain and its margins |
| `1.6`, `1.6.6` | `thm:halting` (annotated) | umbrella and assembly |
| `1.6.1` | `lem:halt-construction` | the self-referential decider |
| `1.6.4` | `lem:lambda-bound` | pure arithmetic; claim-tested upstream |
| `1.6.5` | `lem:lambda` | the verifier's parameter |
| `1.6.2`, `1.6.3` | `lem:dhalt-values` | the two value cases |
| `1.6.7` | `rem:identical-operators` | a paragraph promoted to a labelled remark |

**The finding this turned up** is in `rem:compression-chain`, from node `1.5.8`, and it
favours the architecture already chosen. Compression's soundness clause is proved by
applying each transformation's clause contrapositively with a strict margin, which is an
implication between `val*` bounds at every step. The route of JNVWY cannot take it: their
repetition step's soundness hypothesis is an *entanglement* bound, and `Ent(G, 1-ε) = ∞`
needs `val*(G) < 1-ε` **strictly**, so a non-strict `≤` leaves the requirement finite.
They therefore run the chain in `Ent`, and a value-form route would force them to apply
repetition at `ε₂/2`, costing `2^17` in the repetition exponent. Direct repetition takes a
value hypothesis, so it needs no strictness and pays no such factor. That is the second
place — after `rem:direct-vs-anchored` — where the value form is *cheaper* than the
entanglement form rather than merely equivalent, and it is why no entanglement lower bound
has to be tracked in chapter 6 at all.

Two of the nine new statements, `lem:compress-margin` (`1.5.3`) and `lem:lambda-bound`
(`1.6.4`), are pure arithmetic with no quantum content and are claim-tested upstream.
They are the cheapest genuine chapter-6 Lean targets in the whole pipeline and are the
natural next Lean work after P1.

## Keeping the correspondence: `scripts/ledger-sync.py`

The ledger is a live artifact in another repository, so the correspondence rots silently
unless something checks it. A blueprint statement declares what it accounts for with
`\ledgernode{1.5.3}`, a macro that expands to nothing, and the script has two modes:

* no arguments — check the annotations against the committed snapshot
  `planning/ledger-index.json`, reporting annotations naming an unknown node, cited nodes
  the ledger records as *admitted* rather than validated, and per-stage coverage. Exit
  status 1 on a problem, so it is usable in CI.
* `--ledger PATH` — replay a clone of `vidick/mipre-proof`, rewrite the snapshot, and say
  which nodes changed, flagging separately those the blueprint cites. A cited node whose
  statement hash changed is exactly the case a human must look at.

Neither mode needs Lean, LaTeX or the network. The snapshot records the ledger head
(`11a03e8`), its event count, and for each node its state, challenge and amendment counts
and the sha256 of its statement.

## Stage 1.4 is 3/8 on purpose, from 2026-09-13

`scripts/ledger-sync.py` now reports stage 1.4 at 3 of 8 nodes, and the drop is not an
annotation lost in an edit. The anchored parallel repetition material left the blueprint
that day: `def:anchoring` (1.4.1), `lem:anchoring-value` (1.4.1.1--1.4.1.3) and `thm:bvy`
(1.4.2) carried the five missing annotations, and they were deleted along with the
toolkit their proof needs --- fidelity and Uhlmann, the relative entropy lemmas, quantum
Raz, Holenstein conditioning.

This is the consequence of what the section above already records: anchored repetition is
*not used at all* on this route. Anchoring is what the entanglement form forces, because
`lem:recursive-compression` needs a measure preserved by every transformation; Lin's
criterion has no measure, so value decay suffices and repetition applies to the game as it
is. The five nodes stay in the ledger --- they are what the source's proof needs --- and
this blueprint no longer accounts for them, which is the honest state: not "unaccounted
for yet", but "not on this route". The three that remain (1.4.3--1.4.5, the direct
theorems and `thm:parallel-repetition`) are what the pipeline uses.

If the anchored route is ever wanted back --- for the entanglement-requirement corollaries
of `rem:entanglement-form`, say --- it comes back from `\cite{BVY17}` and from git history
(`de3e22c`), not from a gap in the blueprint.

## Correspondence to maintain

As P1 proceeds, each Lean declaration should name the ledger node it discharges, and
this file should keep the node → blueprint label → Lean declaration table, so the
two projects can be diffed. The ledger is authoritative on *what the proof needs*;
this repository is authoritative on *what has been checked by machine*.
