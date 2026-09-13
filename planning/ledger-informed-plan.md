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

**P3 — expand blueprint chapter 6 along the ledger.** Turn six monoliths into the
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
| `1.1.7.2.1` (norm constraint half) | — | `MIPRE.ValueApprox.posSemidef_realSmul_one_add_and_sub_iff` | proved 2026-09-13 |
| `1.1.7.2.1` (exact arithmetic, psd decidability) | — | — | open |
| `1.1.7.2.2` candidate set finiteness | — | — | open |
| `1.1.7.2.3` stability | — | — | open |
| `1.1.7.2.4` density | — | — | open |
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

## Correspondence to maintain

As P1 proceeds, each Lean declaration should name the ledger node it discharges, and
this file should keep the node → blueprint label → Lean declaration table, so the
two projects can be diffed. The ledger is authoritative on *what the proof needs*;
this repository is authoritative on *what has been checked by machine*.
