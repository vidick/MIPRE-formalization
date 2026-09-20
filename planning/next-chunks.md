# What to formalize next, in four chunks

Written 2026-09-18 at the maintainer's request, after a session that produced nine merged
pull requests (#93–#101) and, fairly, the observation that several were too small: the
`chi`-fibre count and the value-one characterization were each a single idea that belonged
inside a larger piece. This file replaces that cadence with four chunks, one pull request
each, opened only when the chunk's blueprint marks and axiom guards are all in place.

It supersedes nothing in `planning/formalization-plan.md`, which remains the account of *why*
the pipeline is the shape it is; this is the shorter question of what to do next and in what
order.

## Status, measured 2026-09-18 at `73a3d5f`

| chapter | statements `\leanok` | proofs `\leanok` |
|---|---|---|
| 2 foundations | 33/33 | 6/7 |
| 3 background results | 18/50 | 12/28 |
| 4 computability | 14/14 | 8/10 |
| 5 parallel repetition | 9/10 | 6/7 |
| 6 proof structure | 26/48 | 18/25 |
| 7 main theorem | 5/5 | 4/4 |
| 8 downstream | 0/20 | 0/0 |

223 proof-level `\leanok` marks, all axiom-guarded. One axiom outside the vendored trees
(Shoup's irreducible polynomials, `MIPRE.LowDegree.exists_shoup_irreducible`). Four `sorry`s
outside them: the main theorem (`MIPRE/HaltingGameValue.lean`), the two universal-machine
specifications (issues #17 and #18), and one LCS bridge lemma.

Ledger coverage by stage puts the mathematical gap where the table does: stage 1.2, the
low-degree and Pauli subtree, is at 65 of 149 nodes. Stage 1.4 reads 3 of 63, but that is an
annotation-granularity artifact rather than a gap — repetition is formalized and proved, and
one umbrella site carries a finely decomposed source subtree.

Within chapter 6, the subsections divide sharply:

| subsection | envs | statements | proofs |
|---|---|---|---|
| CL functions and samplers | 7 | 7 | 5/5 |
| introspection | 15 | 1 | 0/5 |
| oracularization | 3 | 2 | 0/0 |
| answer reduction | 10 | 4 | 1/3 |
| parallel repetition | 1 | 1 | 1/1 |
| compression | 7 | 6 | 6/6 |
| halting reduction | 5 | 5 | 5/5 |

Introspection is the largest unformalized block in the project. Compression, the halting
reduction and the main theorem are *finished conditionally*: they consume the transformation
structures as hypotheses, so every remaining exterior stage is an obligation to inhabit one.

## Chunk 1 — Oracularization, proved at the level of games

`thm:oracularization` is at zero, and the blueprint calls it "probably the easiest
transformation in the paper". The construction landed in #100 as
`MIPRE.SeededGame.oracular`, a `SynchronousGame` on questions `Role × V`; this chunk proves
its two clauses.

* the value-from-consistency step carrying the **single square root**
  (`fact:approx-implies-close-value` of `oracularization.tex`, from [NW19, Fact 4.31]).
  `MIPRE/Foundations/Distances.lean` has `inconsistency`, `povmDistance` and `IsPOVMClose`;
  the lemma itself is missing. Repair 1 of `rem:oracularization-repairs` records that an
  earlier blueprint revision wrote `poly(ε)` here, "not merely imprecise but false as
  stated";
* **completeness**: a value-`1` PCC strategy for the input gives one for `oracular`. The
  honest oracle measures the input strategy's two measurements jointly — projective because
  `IsPCC` supplies the commutation — and wins because #101 says a perfect strategy's rejected
  outcomes have probability zero. That the two players use identical operators, repair 2, is
  free: a `SyncStrategy` is one family played by both;
* **soundness**: `val*(oracular) > 1 - ε` gives `val*(input) ≥ 1 - c√ε`.

Done when both clauses carry a game-level `\leanok` with guards, and a remark separates the
verifier-level obligations that remain — repairs 3 and 4 are about a decider's bounded parse
and its timeout bound, and have no content at a finite game-level alphabet.

Deliberately *not* in scope: inhabiting `MIPRE.Oracularization`. `rem:oracularization-contract`
records that the source typed theorem does not, that generic detyping adds two levels, and
that `GapCompression.ofPipeline` does not consume the structure. That obligation stays
recorded and untouched.

## Chunk 2 — The self-dual basis algorithm, end to end

Independent of everything quantum, and the only chunk that can run beside Chunk 1 without
touching the same mathematics. On Mathlib's `IsGalois.normalBasis` and the Shoup axiom of
#96, following the sixteen-node route the ledger already lays out under `1.1.6.1`:

* the `𝔽₂[T]/(f)` model with addition, multiplication, inversion and the Frobenius matrix,
  in the ambient cost model (node `1.1.6.1.2`);
* the trace form, `F^k = I`, and `tr(1) = 1` for odd `k` (`1.1.6.1.3`), on top of the
  identities already proved in #96;
* binary squarefree factorization (`1.1.6.1.4`), the minimal polynomial `X^k - 1` of Frobenius
  and its squarefreeness for odd `k` (`1.1.6.1.5`), and the normal element (`1.1.6.1.6`);
* circulant Gram self-dualization (`1.1.6.1.7`, `1.1.6.1.8`) and table transport
  (`1.1.6.1.9`).

Done when `lem:self-dual-basis` carries statement and proof `\leanok` modulo the one axiom,
**and** `MIPRE.SAT.BinField` is inhabited for every admissible `q`. That second half is what
makes the chunk worth its length: `thm:pcp-decider` currently *takes* a field representation
as a parameter, and would then have one.

## Chunk 3 — `thm:lidt-cl-soundness` and the CL adapter — **done for `ldc = 1`**

The gate to the whole of chapter 3's quantum half. It was scoped as: state the seeded CL
soundness theorem as an interface with its `δ_CL`, then prove it from the vendored
canonical-line theorem through `lem:lidt-reduction-setup`, `lem:lidt-test-transfer`,
`lem:lidt-sync-transfer` and `lem:lidt-derandomize`. `def:lidt-cl` and `card_chi_fiber` landed
in #98 and #99.

**It was done by a different route, and that is worth knowing before reading the blueprint.**
Those four lemmas are steps of the *paper's* tensor-code reduction, which is conditional on
`thm:tensor-codes` — no Lean proof, and none coming soon. The canonical-line theorem this
repository has proved is about `lidtGame`, and `rem:lidt-cl-adapter` already identified reducing
to *it* as a separate, unconditional route. That route was taken (maintainer decision,
2026-09-18), and the result is **`MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL`**, the
`ldc = 1` case of `thm:lidt-cl-soundness` with the blueprint's own `δ_CL`, resting on
`propext`, `Classical.choice` and `Quot.sound` and nothing else.

`planning/lidt-cl-adapter.md` is the full record: the route change and its reason, two
corrections found while proving it, and the design of the adapter. Blueprint:
`lem:lidt-cl-adapter-maps`, `lem:lidt-cl-adapter-weights`, `lem:lidt-cl-adapter-params` and
`thm:lidt-cl-soundness-one`, all with proof-level `\leanok` and guards in
`MIPRE/Background/LIDT/Axioms.lean`.

What is still open here, and is not small:

* **`ldc > 1`**, which is `lem:lidt-ldc` and the paper's Steps 1–5. QLD uses only `ldc = 1`, so this is not on its critical path.
  Answer reduction requires `(q,m′,d,m′+6)`, so its supply path does require
  this extension. In particular,
  `thm:lidt-cl-soundness` as stated is not proved without it.
* **The four lemmas of the paper's route**, which this route certifies and does not touch. They
  remain formalization targets for anyone who wants the tensor-code route, and
  `rem:lidt-cl-adapter` says the implication fails in both directions. In particular
  `lem:lidt-sync-transfer` has no counterpart on the canonical-line route at all: `lidtGame`'s
  only same-type subtest is point self-consistency, so there is no line synchronicity to
  transfer. That is why this route needs no Schwartz–Zippel and picks up no `d/q` term of its
  own.

## Chunk 4 — `thm:qld` — **planned, in progress**

A campaign, not a chunk. Seventeen statements over roughly three thousand lines of source, and
Chunk 3 landing is what opened it: `thm:qld`'s stage 4 consumes the seeded CL theorem at
`(q, 4m, d, 1)`, which is the `ldc = 1` case now proved unconditionally.

**The plan is `planning/qld-campaign.md`**, and it fixes four pull requests for the whole
campaign. Read it before starting anything here; two things it records are not visible from this
file and change what the work is:

* the `≈_δ` of the qld appendix is the **state-dependent** distance on a bipartite state, and
  the repository has only the tracial one (`povmDistance`, `Closeness.lean`). It needs building,
  and its own blueprint definition beside `def:distance`;
* **the game `game^pauli` is not in the blueprint at all.** `thm:qld` and `lem:qld-win` are
  statements about it. Defining it — twenty-five question types, a type graph, a decider — is
  the campaign's largest definitional job, and `clGame`'s missing format check is the warning
  for how it can go wrong.

The four pull requests, in order: **A** the state-dependent distance, stage 1
(`lem:qld-averaging`, `lem:qld-povm-to-obs`, `cor:ortho-from-consistency`) and
`lem:ms-direct-anticomm`, all of which need no game; **B** `def:qld-game`, `lem:qld-win` and the
expansion; **C** `thm:linearity` and the combining stage; **D** separation, the swap isometry and
`thm:qld`.

## Not in the four

Chapter 8's twenty statements are corollaries of a theorem that is still conditional, so they
would land as conditional corollaries; worth doing as a chunk of its own once someone decides
that is wanted. The universal-machine specifications are tracked by issues #17 and #18. The
LCS bridge `sorry` is small and orphaned and should be folded into whichever chunk next
touches `MIPRE/LCS/`.

## How these chunks are worked

One pull request per chunk, opened when the chunk is done — its Lean, its blueprint marks,
its guards, and the two checkers green. Progress is reported in the session without opening
anything.

The failure mode this cadence has to survive is the one that produced #101: a chunk blocked
half way on infrastructure nobody had written. The answer inside a chunk is to write the
infrastructure and say so in the chunk's pull request, not to ship it separately.
