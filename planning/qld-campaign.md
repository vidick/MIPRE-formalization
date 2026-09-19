# Chunk 4: `thm:qld`, the Pauli basis test — campaign plan

Written 2026-09-18, after Chunk 3 landed (`thm:lidt-cl-soundness-one`, PR #111). Scoped by
reading the blueprint's five-stage appendix section, the paper's `qld-appendix.tex`,
`qld-prelim.tex` and `ldt.tex` §"The Pauli basis test", and the Lean the repository already has.

`next-chunks.md` calls this "a campaign, not a chunk", and that is right: seventeen statements
over roughly three thousand lines of paper source. The maintainer's constraint is **four pull
requests for the whole campaign**, so this file fixes the four and says what goes in each.

## What Chunk 3 bought, precisely

`thm:qld`'s stage 4 consumes the seeded CL theorem at `(q, 4m, d, 1)`. That is `ldc = 1`, which
is exactly what `MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` now proves unconditionally. So
`lem:qld-simultaneous` can cite a Lean theorem rather than a conditional one, and `lem:lidt-ldc`
(`ldc > 1`) is **not** on this campaign's path.

## Two gaps found while scoping, both structural

### 1. The `≈_δ` of this appendix is not the `≈_δ` the repository has

`def:distance` in the blueprint is the **normalized Hilbert--Schmidt** distance
`𝔼_x ∑_a ‖M^x_a − N^x_a‖²_hs`, and that is what `MIPRE.povmDistance` and `MIPRE.IsPOVMClose`
formalize. `MIPRE/Foundations/Closeness.lean` says so in its own docstring: "For a
*synchronous* strategy the state is the normalized trace itself, so that distance is the
normalized Hilbert--Schmidt distance."

The qld appendix's `≈_δ` is the **state-dependent** distance on a bipartite state. The paper
(`qld-prelim.tex`) defines it as

```
A^x ≈_δ B^x   ⟺   𝔼_{x ∼ μ} ⟨ψ| (A^x − B^x)† (A^x − B^x) |ψ⟩ ≤ O(δ)
```

with `|ψ⟩` fixed by context, for operators indexed by questions but *not* answers. Nothing in
`MIPRE/Foundations/` has this: `Distances.lean` and `Closeness.lean` are both tracial, and
`OracularSound.lean`'s `sqDist` is a synchronous construction. Every statement in stages 1, 3, 4
and 5 is in this distance, so it has to be built first, and it needs its own blueprint
definition beside `def:distance` rather than a reinterpretation of it.

Two deliberate departures from the paper when formalizing it:

* **no `O(·)` inside the definition.** The paper writes `≤ O(δ)`; in Lean the relation is
  `stateDist μ ψ A B ≤ δ`, and the constants then appear in the lemmas that produce them. This
  is stronger, not weaker: `lem:qld-averaging` preserves `δ` exactly and
  `lem:qld-povm-to-obs` gives exactly `|A| · δ`.
* **answer-indexed families too.** The paper's `≈_δ` is for question-indexed operators and it
  separately uses the answer-indexed form (`cor:ortho-from-consistency`'s conclusion is
  `P_a ⊗ Id ≈ Q_a ⊗ Id`, summed over `a`). Both are needed; the answer-indexed one is the
  general definition and the question-indexed one its `Unit`-answer case, so define the general
  one and derive.

### 2. The game `game^pauli` is not in the blueprint at all

`thm:qld` is a statement about "the game `game^pauli_{qldparams}`" and `lem:qld-win` about "a
strategy succeeding with probability `1 − ε` in the Pauli basis test", and **no definition of
that game appears anywhere in `blueprint/src/content/`**. It is in the paper, `ldt.tex`
§`sec:qld-game`, lines 2159--2340 for the question distribution and `fig:decider_pauli` at 2459
for the decision procedure.

So the campaign's first definitional job is `def:qld-game`, the analogue of `def:lidt-cl`, and it
is a bigger one. Its shape, from the paper:

* **types** `type^pauli = ({Point, ALine, DLine, Pauli, Pair} × {X, Z}) ∪ type^MS ∪ {Pair}`,
  where `type^MS` is the Magic Square game's 6 constraints and 9 variables — 25 types in all;
* **distribution**: an ordered pair of types from the type graph `fig:type-graph-pauli` (the
  graph distribution: each non-loop edge two ordered pairs, each self-loop one), then uniform
  `u_X, u_Z ∈ F_q^m`, `s ∈ F_q`, `v ∈ F_q^m`, `r_X, r_Z ∈ F_q`, with the question content read
  off the type exactly as in `def:lidt-cl` (`L^Ln` base points, `χ(s)` blocks, `π_{i−1}(v)`);
* **answers**: `F_q` for points, degree-`d`/`md` polynomials for lines, `F_q^M` (`M = 2^m`) for
  `(Pauli, W)`, `F_2` for the two-outcome probes, LCS assignments for the Magic Square types;
* **decider**: `fig:decider_pauli`.

`def:lidt-cl` is the precedent for how much care this needs, and its history is the warning:
`clGame`'s missing format check made the test vacuous and `thm:lidt-cl-soundness` false about it
(`reports/clgame-format-check-missing.md`). The same class of error is available here, with
twenty-five types instead of three. **Verify the decider rejects ill-formatted answers before
proving anything about the game**, and check by `rfl` that each subtest can fail.

## The four pull requests

### PR A — the state-dependent distance, stage 1, and the Magic Square lemma

Everything that needs no Pauli-test game. This is the piece the maintainer asked for first.

| piece | blueprint | where |
|---|---|---|
| `def:state-distance` and its calculus | **new** | `MIPRE/Foundations/StateDistance.lean` |
| averaging preserves closeness | `lem:qld-averaging` | same |
| POVM elements to generalized observables | `lem:qld-povm-to-obs` | same |
| orthonormalization from consistency | `cor:ortho-from-consistency` | `MIPRE/Background/QLD/Ortho.lean` |
| anticommuting question tuples | `fact:omega-anticomm-prob` | `MIPRE/Foundations/LowDegree/Anticomm.lean` |

`lem:ms-direct-anticomm` was planned for PR A and **moved to PR B** while it was being scoped;
"What the Magic Square lemma actually costs" below says why.

The first three are short once the distance exists: triangle inequality and Jensen, then
Cauchy--Schwarz over the outcome set, both already available for the tracial distance in
`Closeness.lean` and needing the state-dependent analogues.

`cor:ortho-from-consistency` is the one with analysis in it. It is *not*
`thm:orthonormalization` restated: that theorem needs strict near-projectivity in a normal
state, and what we have is bipartite consistency. The Cauchy--Schwarz bridge is written out in
the blueprint. The delicate step is the last one: the theorem gives `< 9ε` for every `ε > 2γ`,
and the blueprint takes a limit over a compact set of projective measurements to land at `2γ`.
**If that limit proves expensive, the slack form is what every downstream use consumes** —
`∀ η > 2γ, ∃ projective P, dist ≤ 9η` — and the blueprint should be repaired to it rather than
the Lean contorted to match. Decide inside PR A and record the decision either way.

#### What the orthonormalization bridge actually costs (reconnaissance, 2026-09-18)

Nothing in the repository consumes `povm_orthogonalization_finDim` yet, so
`cor:ortho-from-consistency` is its first caller and the bridge from `MIPRE.POVM` (matrices) to
the vendored statement (continuous linear maps on a Hilbert space) is new work. Three findings,
two of them good news:

* **No normality to prove.** `MIPRE/Background/Orthonormalization/Statement.lean`'s version wants
  a `NormalState` on a `VonNeumannAlgebra`, and there is no `⊤ : VonNeumannAlgebra H` instance in
  Mathlib. But `Orthogonalization/FinDim/Main.lean`'s `povm_orthogonalization_finDim` takes only a
  linear functional `φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ` with `0 ≤ φ (star x * x)` and `φ 1 = 1`, and a
  family `a` with `0 ≤ a i` and `∑ a i = 1`. Call *that* one: no algebra, no normal state, no
  weak-* continuity.
* **Use Alice's space, not the tensor product.** The blueprint says to apply the theorem to the
  algebra `L(H_A) ⊗ Id`; the equivalent move that needs no algebra is `H := EuclideanSpace ℂ dA`
  with the *reduced* functional `x ↦ ⟨ψ| x ⊗ Id |ψ⟩`. The projections then come out on Alice's
  space directly, which is what the conclusion `P_a ⊗ Id ≈ Q_a ⊗ Id` wants. `quadForm_eq` in
  `StateDistance.lean` is the identity that makes `0 ≤ φ (star x * x)` immediate, since it says
  the value *is* `stateSqNorm ψ M` as a complex number.
* **Positivity transfer is the one real gap.** `Matrix.toEuclideanCLM` is a `StarAlgEquiv`, so
  `map_add`, `map_smul`, `map_one` and `map_mul` are free and `map_star'` is a field; and
  `Mathlib/Analysis/CStarAlgebra/Matrix.lean` gives `ofLp (toEuclideanCLM A x) = A *ᵥ ofLp x` by
  `rfl`. What Mathlib does **not** have is `M.PosSemidef → (toEuclideanCLM M).IsPositive`, nor the
  complex `⟪x, toEuclideanCLM A y⟫ = star x ⬝ᵥ A *ᵥ y` (only the `ℝ` case, `inner_toEuclideanCLM`).
  Both have to be written, and they are what the POVM hypothesis `0 ≤ a i` needs.

So the cost estimate stands at a couple of hundred lines, and the shape is settled; what it is
*not* is a two-line application of a vendored theorem.

`lem:ms-direct-anticomm` is the campaign's best-specified target: the blueprint writes the whole
proof out with explicit constants (Naimark dilation of each constraint POVM, a telescoping
substitution bound `γ² ≤ 144ε`, one six-step word identity through the six constraints, final
`186624 ε`). It is `\effortMedium` and it is independent of everything else. Lean already has
the Magic Square as an LCS game (`MIPRE.LCS.MagicSquare.game`) and
`MIPRE.LCS.Game.toNonlocalGame` turns an LCS game into a `MIPRE.Game (Fin r) (Fin s) …`, which
is the right home for the statement.

One paper statement the blueprint is missing and PR A should add:
`fact:omega-anticomm-prob` (`qld-prelim.tex`), the probability that a uniform
`(u_X, u_Z, r_X, r_Z)` is anticommuting, at least `(1 − 3md/q)/2`. It is Schwartz--Zippel — which
this repository has — plus the trace-is-balanced fact. Its `\cnote` records that two false
auxiliary claims were removed from an earlier revision, so read the live text, not the original.

#### What the Magic Square lemma actually costs (reconnaissance, 2026-09-19)

`lem:ms-direct-anticomm` was scoped inside PR A and moved to PR B. It is still the
best-specified target in the campaign — the blueprint and `paper/ldt.tex` write the whole proof
out with explicit constants — but it is not a tail item, for three reasons, two of them
structural and one of them a finding about the repository rather than about the lemma.

**1. The Naimark dilation the proof needs already existed, behind a 71k-line import.**
*(Extracted 2026-09-19; see the end of this item.)*
The proof dilates each of Alice's six constraint POVMs to a projective measurement on *one
shared* initialized ancilla, which is what lets all six families act on a single state
`|ψ'⟩ = (J ⊗ Id)|ψ⟩`; that is why the paper needs the unitary extension `U_c J = V_c` rather
than the one-line isometry `V_c`. `exists_projective_dilation`, then in
`MIPRE/Background/Repetition/Entangled.lean`, is exactly that theorem, with exactly that
question-independent embedding (`ancillaEmbed d a₀`), together with
`exists_isometry_of_povm`, `exists_unitary_extending`, `ancillaProj` and the Born-rule
transport lemmas. None of it touches the vendored trees.

But `Entangled.lean` is one of the nine bridge modules: it imports
`MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition`, the 71k-line vendored
module that costs 25 CPU-minutes on its own. `MIPRE/LCS/` may not import `MIPRE/Background/`
at all (the one-way import graph in `CLAUDE.md`), so the dilation had to be **extracted first**
into `MIPRE/Foundations/Dilation.lean`, with `Entangled.lean` importing it and its namespace
changing from `MIPRE.Repetition` to `MIPRE`. **Done**: a pure refactor of 220 lines, with the
imports narrowed from a wholesale `import Mathlib` to four Mathlib modules on the way (8706
build jobs down to 2708). `planning/next-steps.md` had predicted this move and said to make it
when a second consumer appeared; this is that consumer.

**2. `Game.toNonlocalGame` was one-directional, and the lemma's Alice half was not statable on
it.** *(Settled 2026-09-19: the game is now symmetrized. What follows is the finding as it
stood, kept because it is why the definition changed and where the constant comes from.)*

The old `MIPRE.LCS.Game.toNonlocalGame` sampled an equation `i` for **Alice** and a variable
`j ∈ V i` for **Bob**, always in that direction: 18 equiprobable incidences, and Alice never
receives a variable question. The paper's `game^MS` samples one of **36 oriented** incidences,
so both players answer both kinds of question, and `lem:ms-direct-anticomm` asserts a bound for
each player — `A^{Variable_j}` on Alice's side did not exist in that game. Nothing in
`MIPRE/LCS/` or `MIPRE/Foundations/` symmetrized an LCS nonlocal game (the `Bool` role of
`def:lidt` and `def:lidt-cl` is the precedent for how it would be done).

So PR B had to either symmetrize `Game.toNonlocalGame` — the honest fix, and the one that makes
the Lean game the paper's game — or state the lemma for a separately defined symmetrized Magic
Square game. **The maintainer chose to symmetrize it**, and that is the first commit of PR B:
both players now draw questions from `Fin G.r ⊕ Fin G.s` and answer in
`(Fin G.s → ZMod 2) ⊕ ZMod 2`, the referee samples an incidence and a uniform orientation, and
the decider rejects a mismatched answer shape and an off-support pair. Nothing in the repository
depended on the old direction, so this is a replacement rather than an addition;
`MIPRE/LCS/MagicSquare/Game.lean` pins each accept/reject outcome with `decide`-checked
witnesses, which is the `clGame` lesson applied.

**3. The constant follows the game, and with the symmetrization it is the paper's.** The paper's `186624`
is `36² · 144` where `γ² ≤ 144 ε` comes from `δ²_{c,j} ≤ 4 ℓ_{c,j}` and `∑ ℓ_{c,j} ≤ 36 ε`, the
last factor being the 36 oriented incidences. On the *one-directional* game there are 18
equiprobable incidences, so `∑ ℓ_{c,j} ≤ 18 ε`, `γ² ≤ 72 ε`, and the bound is `36² · 72 =
93312 ε`. On the symmetrized game the paper's counting applies verbatim and the constant is
the paper's, which is the one the blueprint now carries. Either is fine downstream —
`lem:qld-win` only needs `O(ε)` — but the two must not be mixed up.

What remains after those three is the work the blueprint describes and it is substantial on its
own: the reflections `C_{c,j} = ∑_β (-1)^{β_j} P_c(β)` and their within-constraint product
relations, `⟨ψ'|C_{c,j} B_j|ψ'⟩ ≥ 1 - 2 ℓ_{c,j}` from the winning condition with rejected
answers valued zero, the suffix-insertion bound `‖R W ψ'‖ ≤ ‖R ψ'‖ + ‖R‖ t γ`, the
non-projectivity bound `‖(Id - B_j²) W ψ'‖ ≤ (2 + t) γ`, the six-step word path with its
`24 γ`, and the two end-removals. Roughly twenty operator-norm steps over a 9-variable,
6-constraint structure.

#### How it was proved (2026-09-19): the operator calculus, and why it is matrix-level

**Done**, sorry-free, in `MIPRE/Background/QLD/Anticomm.lean` (namespace `MIPRE.QLD.MS`):
`ms_direct_anticomm` (Bob's half), `ms_direct_anticomm'` (Alice's), and
`ms_direct_anticomm_avg` (the averaged form the expansion stage will actually call), each
bounding `‖anti‖²` by `186624 ε`. The lemma lives under `MIPRE/Background/` because
`MIPRE/Background/` may import `MIPRE/LCS/` but not conversely, and because it exists to feed
the Pauli basis test; its guards are in `MIPRE/Background/QLD/Axioms.lean`, and all four names
print `[propext, Classical.choice, Quot.sound]`.

**The one design decision worth recording: the proof does not use the operator norm.** The
natural route — push each matrix through `Matrix.toEuclideanCLM` and reason with `‖T‖` — dies at
the first step. `T * T ≤ 1 → ‖T‖ ≤ 1` on
`EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n` exhausted 200000 heartbeats in `whnf`: the
Loewner order on continuous linear maps unfolds through the CLM structure and the elaborator
cannot see through it. What replaced it is three definitions in
`MIPRE/Foundations/OpBound.lean`, all stated on matrices acting on vectors and none of them a
norm:

* `Bnd M K` := `∀ v, ‖M v‖ ≤ K ‖v‖` — the operator bound as a *relation*, closed under
  `add`, `sub`, `mul`, `smul` and `mono`, with `bnd_one_of_isometry` and
  `bnd_one_of_conjTranspose_mul_self_le` as the two ways to get `K = 1`;
* `snorm v M` := `‖M v‖` — the state-dependent seminorm, with the triangle inequalities and
  the suffix-insertion bound `snorm_mul_swap`, which is the `‖R W ψ'‖ ≤ ‖R ψ'‖ + ‖R‖ t γ` of the
  blueprint's proof;
* `qform v M` := `re ⟨v|M|v⟩`, additive and real-linear, with `snorm_sq_eq_qform` tying the two
  together.

`aOp X = X ⊗ₖ 1` and `bOp Y = 1 ⊗ₖ Y` are ring homomorphisms into the product space, so the
commutation of the two players' operators is `aOp_mul_bOp` and needs no per-case work. The
reflections come from `MIPRE/Foundations/PVM.lean`: `pvmObs P ε = ∑ a, ε a • P a` is
*multiplicative in* `ε` (`pvmObs_mul`) because a PVM's elements are mutually orthogonal, which
delivers self-adjointness, squaring to one, within-constraint commutation and — the step the
word argument runs on — the exact product equal to the constraint's sign, all from one fact
instead of six cases. `MIPRE/Foundations/POVMValue.lean` carries the value side:
`condFail_le_div` turns `1 - ω ≤ ε` into a per-incidence bound, and with `μ = 1/36` at each of
the 36 oriented incidences that is `condFail ≤ 36 ε` — which is where the paper's constant
comes from, as item 3 above says.

The six-step path is `d a e b → g e b → g h → i → −f c → −d e c → −d e a b`, costing
`7+3+3+3+5+3 = 24γ`; the two end-removals take it to `34γ` and then `36γ`, and `γ = 12√ε`
gives `(36 · 12)² = 186624`. The path's Lean text was emitted by a generator rather than typed:
18 cell conversions, 6 `game.b` values, 6 relations, 6 steps and 5 triangle inequalities is
past the length where transcription is reliable.

Alice's half is not a re-proof. `MIPRE/LCS/NonlocalGame.lean` gained `questionDist_symm` and
`accepts_symm` (both `cases <;> rfl`), and `StateDistance.lean`'s swap section gives
`povmValue_swapVec`, so `ms_direct_anticomm'` is `ms_direct_anticomm` applied to the swapped
state — which is the dividend of symmetrizing the game rather than stating a second lemma.

**One blueprint repair.** `lem:ms-direct-anticomm` also asserted that the bound transfers to the
point observables of `game^pauli`. That is a statement about `game^pauli`, not about the Magic
Square, and it cannot be stated where this lemma lives; it moved into a Comments paragraph
belonging to `lem:qld-win`, which is where the transfer is actually performed.

### PR B — the game, what winning implies, the Magic Square lemma, and the expansion

`def:qld-game` (see above), then `lem:ms-direct-anticomm`, `lem:qld-win`,
`lem:qld-expanded-points`, `lem:qld-expanded-lines`. `lem:qld-win` is bookkeeping *given* the game — each item is the value
of a subtest divided by its selection probability — plus one real step, transferring
`lem:ms-direct-anticomm` to the point observables. The expansion stage is where the ancillas
come in and where the sign `(−1)^γ` cancels exactly; the blueprint flags that cancellation as
the pivotal step, so it is the thing to get right first.

#### PR B as it stands (2026-09-19), and the one thing it is blocked on

**Done, sorry-free**: `def:qld-game` (`MIPRE/Background/QLD/Game.lean`), `lem:qld-win` in all
seven items (`Win.lean`, `WinMS.lean`), `lem:ms-direct-anticomm`, and
`lem:qld-obs-consistency`. The supporting calculus is
`MIPRE/Foundations/CrossConsistency.lean`, which is the appendix's *cross-party* `≃_δ` --- one
player's operator against the other's --- and had to be written because
`MIPRE.stateDist` of `def:state-distance` compares two families on the *same* side. That is the
distance the orthonormalization step wants; every consistency statement of `lem:qld-win` wants
the other one.

**Two things the paper leaves implicit, both of which the formalization needed.** First, a
subtest's decider does not *equal* an agreement predicate: it checks the answer formats and
rejects an ill-formatted pair even when the post-processings agree. What holds is **accept
implies agree**, and that is all `xSqNorm_sum_le_condFail` asks --- which in turn lets the
readings send an ill-formatted answer to `0`. Second, "divided by the probability that the
subtest is selected" needs no injectivity: the subtests are indexed by the verifier's content
and several contents give the same question pair, a `(Pauli, W)` question reading none of it, so
the hypothesis is a condition on the *push-forward*.

**One hypothesis of the paper's `lem:qld-win-implications` is not needed.** `6md ≤ q` is there to
turn the four `γ`-gated items into averages *conditioned* on `γ`; via
`fact:omega-anticomm-prob` each gate then has probability at least `1/4`. The Lean states those
items unconditionally with the gate's indicator inside the average, which is what the machinery
produces and needs no lower bound at all. Whoever wants the conditional form divides and pays
`6md ≤ q` there. The blueprint records this.

**The constants are named, and one of them is loose.** `172 = 2 · 86` for the consistency items
(the factor `2` of the agreement inequality, the selection probability `1/86`), and
`16049664 = 186624 · 86` for the anticommutator. The `86` in the second is a factor `36` looser
than it needs to be: it bounds each of the thirty-six Magic Square incidences against the whole
`ε` budget, where the paper instead budgets them jointly and gets `86/36`. Sharpening means a
multi-edge form of `subtest_le` --- `sum_condFail_le_of_pushforward` with the index set ranging
over edges as well as contents --- and nothing downstream needs it, `thm:qld` asking only for
`O(ε)`.

**What PR B is blocked on: the generalized Pauli operators over `F_q`.** Stage 3
(`lem:qld-expanded-points`, `lem:qld-expanded-lines`) is not a matter of more bookkeeping. Its
expanded observable is

```
  Ŵ^r(u) = W^r(u) ⊗ τ^W(r · ind_m(u))
```

where `τ^W` is the generalized Pauli observable on `(C^q)^{⊗ M}`, `M = 2^m` (the paper's
`sec:generalized-pauli`), and the projections are Fourier transforms
`M̂^{(Point,W),u}_a = E_r (-1)^{tr(ar)} Ŵ^r(u)`. **None of that exists in this repository.**
`MIPRE/LCS/Pauli.lean` is the `2 × 2` Pauli matrices for the Magic Square, not the `F_q` Weyl
system: what is needed is `X`- and `Z`-type Weyl operators on `C^q`, their commutation relation
`X^a Z^b = χ(ab) Z^b X^a`, the `M`-fold tensor families `τ^W_h` for `h ∈ F_q^M`, the projections
`τ^{W,u}_a` of `eq:qld-point-obs-def`, the Fourier identities over `F_q` that turn the average
over `r` into a sum of projectors, and `|EPR_q⟩^{⊗ M}` with its stabilizer relations. That is a
development on the scale of one of this campaign's chunks, and it is also what stage 5's swap
isometry runs on --- so it is not stage-3 overhead, it is the missing half of the campaign's
infrastructure.

Two smaller prerequisites, both named in the comments on `lem:qld-obs-commutation`: the paper's
commutation-analysis lemma (whose projectivity hypothesis a general POVM strategy meets only
after `cor:ortho-from-consistency`), and the order-reversal rule `AB ⊗ Id ≈ Id ⊗ B'A'` for
transferring a product across the tensor factors --- elementary, absent here, and the thing the
paper's own correction note on that proof got backwards in two displays.

**So the campaign's shape has changed.** The plan had four pull requests with stage 3 inside
PR B. Stage 3 should instead be preceded by a **generalized-Pauli chunk**, and PR B ends where
it now does: the game, the win implications, and the observable consistency. That is the honest
boundary --- everything up to it is checked, and the next thing is a new development rather than
a continuation.

### PR C — combining the two bases

`thm:linearity`, then `lem:qld-combined-points`, `lem:qld-pairs-of-lines`,
`lem:qld-padded-points`, `lem:qld-sublines`, `lem:qld-padded-lines`, `lem:qld-simultaneous`.

**A correction to the blueprint's proof text of `thm:linearity` to make before relying on it.**
It says "the source is vendored and was audited line by line". That is true of the *paper* —
`paper/external/nv17/` — and false of this repository: `MIPRE/Background/` holds only
GowersHatami, LIDT, Orthonormalization and Repetition. So `thm:linearity` must be **proved**
here, from Parseval and Naimark with `thm:gowers-hatami` (which is proved) available, not
imported. A reader of the current text would plan the wrong work.

`lem:qld-sublines` is purely combinatorial and the blueprint says it is "a reasonable place to
start formalizing"; it is the natural first commit of PR C. `lem:qld-simultaneous` is the one
that cites Chunk 3.

### PR D — separation, the swap isometry, and the theorem

`lem:qld-helper`, `lem:qld-exact-paulis`, `lem:qld-swap`, `thm:qld`. Two things to hold on to:
`thm:linearity` is **not** used in `lem:qld-exact-paulis` (exactness comes from projectivity of
the simultaneous measurement plus the Pauli group law), and Schwartz--Zippel is applied there in
the *agreement* direction — distinct degree-`md` polynomials agree on at most an `md/q` fraction
— which `rem:qld-admitted` records as a place an earlier revision had backwards.

## Risks, in the order they will bite

1. **The game definition.** Twenty-five types, a type graph, and a decider whose format check is
   exactly the thing that went wrong in `clGame`. Largest single definitional job in the
   campaign, and PR B cannot start without it.
2. **`cor:ortho-from-consistency`'s limit.** See above; the slack form is the escape hatch and
   it is a blueprint repair, not a weakening of the Lean.
3. **`thm:linearity` is not vendored here.** Parseval and Naimark in Lean, on top of
   Gowers--Hatami. Plan for real work, not a bridge.
4. **The expansion stage's exact sign cancellation** (`lem:qld-expanded-points`). The blueprint
   says without the ancillas the error does not improve, so this is not a place to approximate.
5. **Statement-level drift.** Seventeen statements, none of which currently carries even a
   statement-level `\leanok`. Every PR marks the statements it proves and guards them, and
   `scripts/lean-coverage.py` enforces the correspondence — so the drift risk is mechanical
   rather than a matter of discipline, which is the point of that check.

## Not in this campaign

`lem:lidt-ldc` (`ldc > 1` for the seeded CL theorem), `thm:almost-sync`, and the four lemmas of
the paper's tensor-code route (`lem:lidt-reduction-setup` through `lem:lidt-derandomize`). None
of them is on `thm:qld`'s path; see `planning/lidt-cl-adapter.md` for why the last four are not.
