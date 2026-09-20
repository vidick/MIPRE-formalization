# Chunk 4: `thm:qld`, the Pauli basis test — campaign plan

Current blueprint synchronization (2026-09-20): the expansion and linearity
proof marks remain intact. The additional axis-degree lemma and the ten
`lem:qld-global-*` nodes are explicit unformalized combining obligations.
They use the proved `thm:lidt-cl-soundness-one`; the general multi-codeword
extension is needed by answer reduction, not this QLD application. The
source pin and remaining adapters are in `paper-correspondence.md`.


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

### PR B' — the Weyl chunk, and the anticommuting half of the commutation lemma

Written 2026-09-19, on finishing it. This is the chunk the paragraph above said had to come
first, plus the one prerequisite of stage 3 that turned out to be cheap once the rule was stated.

**The `F_q` Weyl system** (`MIPRE/Foundations/Weyl.lean`, `WeylEPR.lean`, `WeylBinary.lean`;
blueprint `def:generalized-pauli`, `def:weyl-epr`, `lem:pauli-binary`). Three decisions did most
of the work:

* **characteristic two throughout.** The paper builds the system over `F_p` with phases
  `omega = e^{2 pi i / p}` and then specializes. Admissible field sizes are `q = 2^k`, so
  `omega = -1`, every phase is the real sign `MIPRE.sgn`, and the operators are self-adjoint
  *involutions* rather than order-`p` unitaries — genuine `±1`-observables. A second dividend
  showed up in `WeylEPR.lean`: `(M ⊗ Id)|EPR> = (Id ⊗ M^T)|EPR>` costs a transpose in general, and
  the Weyl matrices here are real symmetric, so for them the transpose is the identity and the two
  parties' operators act identically on the state. Over odd `p` that bookkeeping reappears.
* **one matrix, not an iterated Kronecker product.** `(C^q)^{⊗ n}` is `Matrix (n → F) (n → F) C`,
  indexed by the functions `n → F_q`, which *is* `F_q^n`. So the `n`-register statements are the
  one-register statements with no associativity bookkeeping, and `n` is an arbitrary finite type,
  which is what lets the test use it at `n = {0,1}^m`.
* **`IsWeylFamily` rather than two developments.** The spectral theory of
  `eq:pauli-obs-proj-bp` uses only three properties — the family represents the additive group,
  its operators are self-adjoint, `w 0 = 1` — so the projectors are built once and the statements
  hold for both families. The paper's Fourier transform conjugating `tau^Z` into `tau^X` is then
  not needed, which is worth avoiding: it carries a `q^{-1/2}`, and a square root in matrix
  entries costs far more in Lean than on paper. Two of the identities need even less: the
  expansion of an operator in its own projectors and the line average
  `eq:pauli-line-bp` use *no* group law at all.

`lem:pauli-binary` is a relabelling, not an isometry: both systems are matrices indexed by a
finite set, `phi` is a bijection of those index sets, and conjugating by it is
`Matrix.submatrix`. Only the form's transport uses self-duality (it *is*
`trace_mul_eq_dot`); `tau^X` transports because `phi` is additive, the projectors because the
Fourier average reindexes, the state because a relabelling preserves the diagonal. That the
target really is qubits is checked rather than read off the encoding — `trDot_two`,
`sgn_trDot_two`, `wZ_two_diag`, `wX_two_apply` are the paper's tensor-product form, entry by
entry.

One generalization went back into an existing file: the cancellation count
`card_filter_ker_mul` existed only for a functional on a field *extension*, and the proof uses
nothing but the module structure, so it is now `card_filter_ker_mul'` for any finite `F`-vector
space, with the field-extension form as the instance.

**The order-reversal rule** (`MIPRE/Foundations/CrossConsistency.lean`, blueprint
`eq:order-reversal-bp` and `eq:anticomm-transfer-bp`). `AB ⊗ Id ~ Id ⊗ B'A'` at the sum of the two
deviations, from the split
`AB ⊗ Id - Id ⊗ B'A' = (A ⊗ Id)(B ⊗ Id - Id ⊗ B') + (Id ⊗ B')(A ⊗ Id - Id ⊗ A')`. The reversal
*is* the step that commutes `A ⊗ Id` past `Id ⊗ B'`. Applying it in both orders and cancelling
Bob's two products transfers an anticommutation from one side to the other, which is the shape
the commutation lemma wants. Stating it needed one small thing: the `±1`-observable of a
two-outcome POVM has to be written as a *difference* of POVM elements for
`POVM.sub_mul_self_le_one` to apply, not as the weighted sum `obsOf` produces — hence `obs2` and
`obsOf_sgn_eq_obs2`.

**The anticommuting half of `lem:qld-obs-commutation`**
(`MIPRE/Background/QLD/Commutation.lean`, blueprint `lem:qld-obs-commutation-acomm`). Item 7 to
observables (two outcomes, so `344 eps` each), item 6's anticommutator, and the transfer rule.
Two bookkeeping points were the only real work: the items carry a *sub-probability* weight
— uniform on all contents, supported on the anticommuting ones — so `sum_acommWeight_mul`
converts between that and the `∑ over acommSet` form; and item 6 is stated for the conditional
Magic Square strategy's observables, which are the same operators as the `Variable` observables
here because relabelling along `Sum.inr` leaves a coarse-grained POVM element alone
(`bobs_msPOVM`).

**This half costs `eps`, not `sqrt(eps)`, and that should not be rounded away.** Every input is a
squared-norm bound linear in `eps` and the only inequalities used are the triangle inequality and
`(a+b+c)^2 <= 3(a^2+b^2+c^2)`; the constant is `12*344 + 12*344 + 3*16049664 = 48157248`. The
`O(sqrt(eps))` of `lem:qld-obs-commutation` belongs to the *commuting* case alone, where the
`Pair` measurement's projectivity comes from `cor:ortho-from-consistency` at the cost of a square
root. So the two halves will not combine by adding constants, and when the commuting case lands
the square root will be attributable to exactly one of them.

**What stage 3 still needs**, with this chunk in place: the commuting case (the projectivity
bookkeeping through `cor:ortho-from-consistency`), the expanded six-fold state with its ancilla
registers, and the hatted measurements `M-hat^{(Point,W),u}` as Fourier averages of
`W-hat^r(u) = W^r(u) ⊗ tau^W(r · ind_m(u))`. The Weyl half of that is now all present, including
the stabilizer relation the sign cancellation runs on.

### PR B'' — the commutation lemma, both halves

Written 2026-09-19. `lem:qld-obs-commutation` is now proved in full, at an explicit `57676416 eps`.

**The commutation analysis** (`MIPRE/Foundations/Commutation.lean`, blueprint
`lem:commutation-analysis`). Two POVMs on one side, each cross-party close to a marginal of one
**projective** measurement on the other, commute on the state at `16 delta`. Both products are
moved to the same operator `Id (x) P_{b,c}` on the other side, and that is the only use of
projectivity in the whole appendix (`IsPVM.marg_mul_marg`). The step that makes it work is the
paper's `fact:add-a-proj`: a family with `sum_i F_i^dag F_i <= Id` in front of a deviation costs
nothing and *adds* its index to the sum.

Stated for abstract families in **one** matrix algebra, with the two parties entering only through
four hypotheses. That is not tidiness: the first version, stated with `aOp`/`bOp` in the
hypotheses, timed out at 200000 heartbeats in three places; in one algebra it elaborates in
seconds and the bipartite version is a one-line instance.

**The commuting half** (`MIPRE/Background/QLD/Commutation.lean`, blueprint
`lem:qld-obs-commutation-comm`), at `9519168 eps`. Three things had to be arranged:

* **the analysis runs on Bob's observables.** `cor:ortho-from-consistency` produces a projective
  measurement on *Alice's* factor, and the analysis needs the joint projective measurement on the
  side *opposite* the commuting pair. So it is applied to Bob's point measurements against Alice's
  projectivized `Pair` measurement, and the conclusion is carried back by the order-reversal rule
  with `pts_obs_consistency`. The bridge is a swap lemma for *mixed* operators,
  `snorm_swapVec_aOp_sub_bOp`; `norm_stateVecB` only covers an operator on one factor. The
  alternative --- a Bob-side orthonormalization corollary --- would duplicate `Ortho.lean`.
* **the chain runs mirrored.** Items 5 and 1 with the players exchanged (every rule of
  `fig:decider_pauli` is stated in both orientations) and item 4 as it stands: three links at
  `172 eps`, so `1548 eps` after one three-term triangle inequality.
* **the corollary's strict slack is discharged by a limit.** It needs `0 < delta`; it is applied at
  `delta = inconsistency + eta` for arbitrary `eta > 0`, which survives averaging as an additive
  constant and is sent to zero with `le_of_forall_pos_le_add`. No compactness.

**A correction to what the last PR said about the square root.** PR B' recorded that the
anticommuting half costs `eps` and attributed the `O(sqrt(eps))` of the blueprint's statement to
the commuting half. That was wrong: the commuting half is `O(eps)` as well --- the analysis is
linear in its hypothesis and `cor:ortho-from-consistency` is linear in the inconsistency. The
paper's `sqrt(eps)` is a uniform *weakening*, and the paper's own text says so where the
anticommuting case is proved ("in particular it implies the following weaker bound, retained in the
form used below"). Nothing downstream needs the sharper form, so this is a note about where a
square root is not spent rather than a repair. The blueprint carries the correction at
`lem:qld-obs-commutation-acomm`.

**One finding worth keeping.** Data processing is a **consistency**-level fact: NW19's Fact 4.26 is
stated for `simeq_delta` and the remark following it gives a counterexample for `approx_delta`. The
paper's `fact:data-processing` is the `simeq` form, correctly. So every coarse-graining in the chain
is taken at the Born level and only then converted, and a formalization that reached for the
`approx` form would be proving something false.

### Stage 3, the commutation half (2026-09-19)

`lem:qld-expanded-points` has two items. The **commutation** half is done
(`MIPRE/Background/QLD/Expanded.lean`, blueprint `lem:qld-expanded-commutation`); the
**self-consistency** half is not.

**What the expansion buys, precisely.** The sign is *gone*, not smaller. The hatted observable is
`W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u))`, and

```
  [X-hat, Z-hat] = (X Z - (-1)^gamma Z X) (x) (tau^X(a) tau^Z(b)) ,
```

because the two ancilla operators commute up to *exactly* the sign the strategy's carry -- the
twisted commutation relation, whose sign is the form `tr((r_X ind(u_X)) . (r_Z ind(u_Z)))`, and that
form **is** `gamma(omega)` (`gam_eq_trDot`, a four-line computation that is the linchpin of the
whole stage). Then the surviving ancilla operator is unitary, so invisible to the state-norm, and
what is left has an inert ancilla, so its norm on the expanded state is its norm on the original
one. The expansion therefore costs *nothing*: the constant is `lem:qld-obs-commutation`'s, with the
sign removed. Without the ancillas the error carries `(-1)^gamma`, which no amount of soundness
improves, `gamma` being a property of the question and not of the strategy.

The bookkeeping is isolated in `MIPRE/Foundations/Expanded.lean` (blueprint
`def:expanded-state`): the re-bipartitioned product state, an operator of product form acting factor
by factor, the norm of a product state, an inert ancilla, and a unitary ancilla. None of it mentions
the Pauli test.

**The self-consistency half (2026-09-19, done).** The hatted measurement is the *convolution*
`M-hat^{(Point,W),u}_a = sum_{a'+a''=a} M_{a'} (x) tau^{W,u}_{a''}` -- in Lean, the product
measurement `POVM.kron` coarse-grained by addition. Its consistency is three facts and no loss:

* the agreement probability of a product measurement on the expanded state **factorizes**
  (`bornProb_expVec_kron`; only the ancilla's operators need to be positive, which is what makes
  their quadratic form real so the real part of the product splits);
* the ancilla factor is **exactly one** -- the syndrome projectors are perfectly self-consistent
  across the two halves of the EPR ancilla. That is `stateVec_epr_syn` (the stabilizer relation
  summed over a level set) turned into a Born probability, and the sum is `1` rather than
  `1 - O(eps)`;
* the convolution is a coarse-graining, so it can only **increase** agreement
  (`sum_bornProb_le_map`).

What is left is the strategy's own disagreement, which item 1 bounds by the subtest's conditional
failure; one conversion to the distance gives `172 eps`. So the expansion contributes nothing to
either item's constant.

**And the one thing to keep in mind about all of it**: the whole estimate runs on Born
probabilities and converts to the state-dependent distance exactly once, at the end. That is
forced -- `approx_delta` has no data-processing inequality (NW19's own counterexample), so a
coarse-graining can only be taken at the Born level. `sum_bornProb_le_map` is stated there for that
reason, and the blueprint says so under `def:expanded-state`.

### Stage 3, the line measurements (2026-09-19, done)

`lem:qld-expanded-lines`, the paper's `lem:qld-comm-line-cons`. Same convolution one level up: the
strategy's line measurement against an ancilla measurement that reports the **restriction to the
line** of the low-degree encoding of its outcome. Four things are worth recording, because three of
them made the proof shorter than the paper's and the fourth is a correction to this file's own
earlier note above.

**The missing infrastructure was the restriction itself.** `MIPRE/Foundations/LowDegree/`
had `lineParam` and `LinePoly.eval` but no way to restrict a multivariate polynomial to a line.
`LineRestrict.lean` is that: `lineRestrict u0 w p = p(u0 + t w)` by substitution
(`MvPolynomial.aeval` into `Polynomial F` -- which needs
`import Mathlib.Algebra.Polynomial.AlgebraMap` for the `Algebra F (Polynomial F)` instance, whose
absence was the first hour), with `eval_lineRestrict`, a degree bound `natDegree <= totalDegree`
monomial by monomial, and `sum_coeff_lineRestrict` reading the coefficients as a `LinePoly F n` for
any `n` the degree does not exceed. Plus `totalDegree_ldEnc_le : totalDegree (ldEnc a) <= m`.

**The ancilla's line and point measurements are literally the same family, relabelled.** This is
what replaces the paper's step "by the exact consistency between the `tau^{W,line}` and `tau^{W,u}`
measurements". Generalize the syndrome projector to a coarse-graining of the eigenbasis measurement
along an *arbitrary* label -- `synOf w phi o = sum_{e : phi e = o} proj w e`, with `syn w v` the
case `phi e = <e, v>` -- and the three facts it needs (`IsPVM`, EPR transport, and that
coarse-graining again gives the composite label's family) generalize verbatim. Then
`synLinePOVM_map_eval` is a **POVM equality**: relabelling the line measurement by evaluation at
the point *is* the point measurement, because `eval_lineCoeffs` says the labels agree. So the
ancilla's contribution to the line-against-point estimate is the same exact `1` as in the point
case, and no new estimate is needed.

**Projectivity is two closure properties, not an orthogonality computation.** A coarse-graining of a
projective measurement is projective (`IsPVM.coarse`, from `IsPVM.orthogonal`), and so is a product
(`isPVM_kron`). The convolution is a coarse-graining of a product, so `isPVM_hatLinePOVM` is three
lemma applications -- *given* that the strategy's own line measurement is projective, which the
paper takes for granted and which is WLOG by Naimark. The Lean statement carries it as a hypothesis
instead of hiding it. The note above, that projectivity "comes from an orthogonality property of the
convolution", was the paper's framing of the same fact; the closure route is shorter and says
where the hypothesis is.

**The constant is linear in `eps`, and the blueprint's `O(sqrt eps)` was wrong.** Both items come
out at `172 eps` -- item 1 of `lem:qld-win` with no further loss. The paper says `poly(eps)`; the
square root was this blueprint's own and had no source, like the one in `lem:qld-obs-commutation`
before it. Nothing in the proof takes a square root because nothing in it converts an operator
inequality into a norm. The blueprint statement is repaired in the same pull request.

**One thing deliberately not proved.** For an axis-parallel line the honest restriction is affine,
hence of degree at most `d` rather than `md`; `lem:qld-pairs-of-lines` will need that to keep padded
answers in the degree-`d` format, and it needs the *individual*-degree bound along the line's own
direction, which `natDegree_lineRestrict_le` (a total-degree bound) does not give. The convolution
is stated at degree `md` for both line types with the axis-parallel answers padded, which is what
the paper's printed definition does too; the refinement is the paper's `cnote` in
`qld-combining.tex` and is PR C's problem.

### PR C — combining the two bases

`thm:linearity`, then `lem:qld-combined-points`, `lem:qld-pairs-of-lines`,
`lem:qld-padded-points`, `lem:qld-sublines`, `lem:qld-padded-lines`, `lem:qld-simultaneous`.

### `thm:linearity`, proved here (2026-09-19, done)

The correction this file flagged -- the blueprint said "the source is vendored and was audited line
by line", which is true of the *paper*'s `paper/external/nv17/` and false of `MIPRE/Background/` --
is now moot, because the theorem is **proved**: `MIPRE/Foundations/Linearity.lean`, 440 lines.

Three things are worth keeping.

**`thm:gowers-hatami` is not the tool.** It is about the Hilbert--Schmidt distance and approximate
*representations*; the hypothesis here is in the state-dependent distance. The blueprint's
`\uses{thm:gowers-hatami}` was a guess and is gone. What replaces it is one *exact* step: the
Fourier transform `A_e = |V|^{-1} sum_a sgn(<a,e>) O^a` of a family of **involutions** has
`sum_e A_e^2 = |V|^{-1} sum_a (O^a)^2 = Id`, so `{A_e^2}` is a POVM with no approximation anywhere.
Then `exists_projective_dilation` -- now a blueprint node, `lem:naimark-dilation`, having been
silent infrastructure before -- and Fourier inversion give the exactly linear family, and the
character-sum identity `sum_e sgn(<u,e>) A_e^2 = |V|^{-1} sum_a O^a O^{a+u}` connects it back.

**The conclusion is an equality.** `E_u ||(L^u - O^u)psi'||^2 = E_{a,b} ||(O^a O^b - O^{a+b})psi||^2`
-- the linearity defect is *transported*, not estimated. The paper's own audit note concludes "the
closeness exponent is 1, with the identical delta", and the ledger's child node 1.2.2.7.3 records
the same; the equality says where it comes from. Nothing in the proof is an inequality, so there is
no constant to lose.

**The ancilla is one-sided.** `extVecA psi a0 = (ancillaEmbed (x) 1) *v psi` adjoins `|0>` to the
*first* party only -- the source's `|psi> (x) |0>_{A'}`, not `def:expanded-state`'s two-sided EPR
ancilla. The only fact needed about it is `qform_extVecA`: a quadratic form on the extended state is
the quadratic form of the compressed operator on the original one, which is
`dotProduct_mulVec_conj` plus one Kronecker identity. `Dilation.lean`'s universe variables had to be
relaxed from `Type` to `Type*` for the index group `n -> F` to serve as the ancilla.

**Still to do in PR C**: `lem:qld-pairs-of-lines`, `lem:qld-sublines`,
`lem:qld-padded-lines`, `lem:qld-simultaneous`.

`lem:qld-sublines` is purely combinatorial and the blueprint says it is "a reasonable place to
start formalizing"; it is the natural next commit of PR C. `lem:qld-simultaneous` is the one
that cites Chunk 3.

### `lem:qld-combined-points`, by the sandwich rather than the linearity test (2026-09-20, done)

`MIPRE/Foundations/Sandwich.lean` (generic), `MIPRE/Foundations/Parseval.lean`,
`MIPRE/Foundations/Swap.lean`, `MIPRE/Background/QLD/Swap.lean`,
`MIPRE/Background/QLD/Combined.lean` (the instantiation). Statement and proof marked, sixty-seven
declarations guarded.

**`thm:linearity` is not used, and neither is `cor:ortho-from-consistency`.** The paper's route is
three steps -- sandwich, orthonormalize, linearity test. Two of them drop out once the strategy is
taken projective, which the paper also assumes and which `lem:naimark-dilation` supplies:

* `R-hat^{x,z}_{a,b} = M-hat^Z_b M-hat^X_a M-hat^Z_b` is **already a POVM**, exactly --
  `sum_{a,b} R-hat = sum_b M-hat^Z_b (sum_a M-hat^X_a) M-hat^Z_b = sum_b M-hat^Z_b = Id` uses only
  projectivity of the `Z` side, and each term is a Gram operator, hence positive. So no
  orthonormalization.
* its **Naimark dilation** is the projective joint measurement the lemma wants, on one extra
  `F_q x F_q` register per party, and the dilation's compression identity carries every Born-rule
  estimate unchanged. So no linearity test, and no Fourier inversion of an exactly linear family.

This leaves exactly the analytic content, and it is one chain. Written with `P_b = M-hat^Z_b (x)
M-hat^Z_b` and `Delta = sum_a (Id - M-hat^X_a) (x) M-hat^X_a`, the five links are: two players'
commutators (each a `M-hat^Z_b` times a commutator, front factor a contraction, one
Cauchy--Schwarz over *all* outcome pairs), the `X`-consistency as the single product
`(sum_b P_b) Delta` of two projections, the exact collapse `sum_a M-hat^X_a = Id`, and the
`Z`-consistency.

**The third link is the one that must not be broken up.** Bounding the `q^2` outcome pairs one at a
time costs a factor `q` and the conclusion has to be `q`-independent -- which is precisely the
defect the paper's round-11 `\cnote` on node 1.2.2.8 repairs, and the reason it introduces its own
Parseval identity there. Here the whole double sum is one operator product, both factors are
projections because their summands are mutually orthogonal projections, and Cauchy--Schwarz gives
`sqrt(<Delta>) = sqrt(half the X-consistency defect)` once.

**Parseval is the dictionary, and the probe average is free.** `lem:qld-expanded-points` bounds the
commutator of the *observables*, one pair per probe `(r,s)`; the sandwich needs the commutator of
the *elements*, one pair per outcome `(a,b)`. The elements are the two-variable Fourier transform of
the observables (`hatComm_eq_fourierOf`), so `sum_norm_fourierVec_sq` exchanges the two at no cost
-- and the verifier's content already averages over `(r_X, r_Z)` uniformly and independently of
everything else it carries, so `sum_content_avg_probe` turns the average the transform introduces
into the one the hypothesis already has.

**Both players' commutation bounds are needed, and the game's symmetry supplies the second.**
Every rule of `fig:decider_pauli` is written in both orientations and the sampler draws an ordered
edge of a symmetric type graph, so `accepts_symm` (a `cases`-and-`simp` bash over the question and
answer constructors, 27 s) and `qldGame_mu_symm` (the edge-swap bijection) give
`povmValue_qldGame_swapVec`, and `hatObs_commutation` applied to `(MB, MA)` on `swapVec psi` is
Bob's half. `hatVec_swapVec` is what makes that readable back: it needs the maximally entangled
ancilla to be symmetric, `MIPRE.Weyl.swapVec_epr`.

**Constants.** `delta_Q(eps) = 2 sqrt(57676416 eps) + sqrt(86 eps) + 86 eps`; self-consistency at
`2 delta_Q`, consistency with `M-hat^Z_b M-hat^X_a` at `4 delta_Q + 115352832 eps` and with the
other order at `4 delta_Q + 461411328 eps`. The square roots are the three Cauchy--Schwarz links;
nothing depends on `q`.

**The generic half is in `Foundations/`** and says nothing about the Pauli basis test: two
approximately commuting projective measurements per party, four error hypotheses, and
`exists_projective_joint` returns the dilated pair with its three estimates. That is what
`Combined.lean` instantiates at `A := F_q`, `iota := Content F m`, uniform weights.

### `lem:qld-padded-points`, and why its two items are free for opposite reasons (2026-09-20, done)

The combined measurement coarse-grained along `(a,b) |-> alpha a + beta b`, so that it returns
the single field element `alpha g_X(x) + beta g_Z(z)`. Indexed by `(x, z, alpha, beta)`, which is
what the paper's "independent of the dummy coordinates `w`" means; the padded space `F_q^{4m}`
itself is not needed until the line--point distribution over it is, in `lem:qld-padded-lines`.

**Item 1 (self-consistency) is free because both families are projective.** The state-dependent
distance has no data-processing inequality -- `Expanded.lean`'s docstring records NW19's own
counterexample -- so a coarse-graining is not free in general. What makes it free here is that
for *projective* families the summed deviation and the agreement probability determine each other
exactly (`one_sub_sum_bornProb_eq`, proved for the sandwich chain and reused verbatim), and
agreement can only increase under a coarse-graining applied to both sides
(`sum_bornProb_le_map`). Three lines: `sum_xSqNorm_map_le`. And it holds for *every*
`(alpha,beta)`, not just on average.

**Item 2 (consistency with the ordered products) is not free, and Parseval pays for it.** The
right-hand families are products of two measurements, not POVMs, so item 1's route is
unavailable, and a per-fibre triangle inequality costs the fibre size `q`. The paper's round-12
`\cnote` on node 1.2.2.10 records that an earlier orthogonality-and-Cauchy--Schwarz route claimed
`O(delta_Q^{1/2})` and was retracted for exactly this reason. The argument that works, and is
what is formalized (`sum_avg_norm_fibre_sq`):

* Parseval over `F_q` turns the sum over fibres into an average over one probe `r`;
* the `r = 0` term vanishes **identically**, because the deviation family sums to zero --
  `sum_{a,b} Q-hat_{a,b} = Id` and `sum_{a,b} M-hat^Z_b M-hat^X_a = Id`. This is the only place
  the zero-sum hypothesis is used, and without it the identity is false;
* for `r != 0` the pair `(r alpha, r beta)` is uniform on `F_q^2` when `(alpha,beta)` is, so
  averaging and applying Parseval over `F_q^2` returns the outcome-pair sum exactly.

So the error comes out at `(q-1)/q` times the input -- **better** than preserved, and with no
`md/q` term. The Lean keeps the factor visible.

New Foundations pieces: `sum_norm_trVecRaw_sq` (Parseval over one copy of the field, a copy of
the `n -> F` proof with `sum_sgn_trMul` in place of `sum_sgn_trDot`), `sum_norm_char_two_sq`
(over two copies, transported from `n := Fin 2` through `pairVec`), `sum_avg_norm_fibre_sq`,
`sum_xSqNorm_map_le`, and the vector bridge `xSqNorm_eq_norm_evec_sq` / `sum_fibre_dev` that lets
a fibre sum of deviation *vectors* be read back as the deviation of the coarse-grained operators.

### The pasting lemma, cheaper than the paper's (2026-09-20, done)

`lem:qld-pairs-of-lines` rests on NW19's Fact 4.35 (the paper's `lem:pasting-updated`), which the
blueprint did not have. It is now in `MIPRE/Foundations/Pasting.lean`, at `k = 2` — the paper's
reduction of general `k` to `k = 2` is an induction that adds nothing and the consumer needs
`k = 2` only — together with `lem:cool-closeness-fact` in `MIPRE/Foundations/Commutation.lean`.

**Two hypotheses of the paper's statement are not needed, and the reason is the same both times:
what the consumer has is stronger than what the paper's proof assumes.**

* The paper allows the inner family `G_1` to be a POVM. Then the two diagonal terms of the
  commutator expansion are only approximately one, and repairing that is exactly what its appeal
  to NW19's Fact 4.31 does. Our `G_1` is a line measurement, hence **projective**, and then the
  two diagonal sums are *exactly* one: `sum_snorm_sq_comm_eq` computes the commutator sum as
  `2 - 2 Sigma` with no error term at all. Fact 4.31 is not needed anywhere, and task Q-C5a's
  original scope — "NW19 Fact 4.31 and `lem:cool-closeness-fact`" — shrank by half.
* The paper derives the cross-party self-consistency of `G_2` from the backwards consistency and
  Alice's self-consistency, and pays a further `eps` for the passage from the fibres of the
  outcome map to the fine family. Item 1 of `lem:qld-expanded-lines` gives the fine-level relation
  directly, at `172 eps`. So it is a hypothesis of the abstract lemma rather than a derivation.

Neither change touches the conclusion; both are recorded in the blueprint's Comments.

**What the chain actually is.** With `R` the coarse-grained inner family and `G` the outer one:

* step (i), `sum_bornProb_ord_ge`: the *ordered* product `G_g R_b` carries all but
  `delta/2 + sqrt(delta/2)`. The outer factor sums away against Alice's second marginal, and what
  is left is Alice's first marginal against `Id - R_b` — whose square is `Id - R_b` again, `R`
  being projective, so no `M^2 <= M` estimate is needed;
* step (ii), `abs_sand_sub_ord_le`: from the ordered product to the sandwich, one Cauchy--Schwarz
  against Bob's commutator, the front factor `A_{b, e(g)} (x) G_g` being a mutually orthogonal
  family of projections and so a contraction (`sum_snorm_sq_prod_le_one`);
* the fine-grained commutator against the coarse-grained one, `sum_snorm_sq_comm_fine_le`: the
  coarse one is `16(delta_1 + delta_2)` by `commutation_analysis_abstract` read **in the mirror**
  — both families on Bob, Alice's joint measurement supplying the operator both products reach —
  and the two overlaps differ by the cloud, the strife and the collision term.

**The one estimate that had to be got right.** In the cloud step (`abs_sigma_sub_cloud_le`) the
deviation `G'_g (x) Id - Id (x) G_g` is summed over `g` only, while the term being bounded is
summed over `(b, g)`. Splitting the Cauchy--Schwarz as
`[R_b G_g R_b] . [R_b . deviation]` — legal because `R_b G_g R_b . R_b = R_b G_g R_b` — keeps one
`R_b` in front of the deviation, and `sum_snorm_sq_mul_le` then absorbs the `b`-sum instead of
repeating it. Dropping that factor multiplies the bound by `|R1| = q`.

**The collision term is a hypothesis of the core and a lemma of its own.** `collisionTerm` names
the off-diagonal cloud mass — pairs `g != g'` the outcome map cannot tell apart — and
`strife_sub_cloud_eq` says the strife minus the cloud *is* that term, exactly.
`sum_collisionTerm_le` is the bridge for a product question distribution: with the probe uniform
and independent, the Born probabilities do not depend on it, so the probe average acts on the
collision indicator alone and what multiplies it is a POVM's total mass. The collision probability
there is a *function of the question*, and the conclusion is its average — because the seeded
test's diagonal branch samples a zero direction with probability at most `1/q`, and on such a
degenerate line the outcome map separates nothing; what makes the average small is the rarity, not
a bound holding everywhere. That split keeps the
analytic core free of the question distribution, which matters because the consumer's distribution
is the line--point distribution rather than a product on the nose — the product structure there
comes from shifting the point along its line, which is the next piece of work.

Constants: `delta/2 + sqrt(delta/2) + sqrt(32 delta + 4 sqrt(eta) + 2 eps)`. The `32` rather than
`16` is because the commutation analysis takes a single `delta` for both marginal hypotheses, here
instantiated at their sum. Nothing in the chain is a per-outcome estimate, so no constant depends
on `q`.

### `lem:qld-pairs-of-lines`, and the shift that makes the point uniform (2026-09-20, done)

With the pasting lemma in hand the remaining work was its four hypotheses at the QLD line
measurements. Three pieces of bookkeeping, and one of them is the interesting one.

**The marginal step.** `lem:qld-combined-points` gives the joint measurement against the *ordered
product* `M-hat^Z_b M-hat^X_a`; the pasting lemma wants each marginal against a *single* line
measurement. `lem:cool-closeness-fact` (partition form) plus the orthogonality of the other
family's fibres takes the first step at a factor 10 and no factor `q`; a triangle inequality
through *Bob's own* point measurement --- its two legs being item 1 of `lem:qld-expanded-points`
and item 2 of `lem:qld-expanded-lines` --- takes the second.

**The extended space.** The joint measurement is the Naimark dilation and lives on each party's
space enlarged by one `F_q x F_q` register; the line measurements do not. `xSqNorm_extVec2_aOp`
says an operator with an inert ancilla has the same cross-party deviation on the extended state as
the operator itself, which transports both inputs.

**The probe, which is where the paper's `lem:alnf`/`lem:dlnf` would be used.** The pasting lemma's
collision term needs the point to be uniform on its line once the line is fixed. The content
determines both, and rather than form the conditional distribution the formalization *shifts*: for
each fixed `t` the map `u_W |-> u_W + t . w_W` is a bijection of contents (`bijective_shift_gen`),
so the content average and the (content, shift) average agree (`sum_content_shift_gen`); the line's
question, base point and direction are invariant under it (`rep_add_smul` is why); and the point's
parameter moves by exactly `t` (`lineParam_add_smul`). That is the whole content of "conditioned on
the line the point is uniform on it", with no quotient formed and no measure-theoretic detour.

The same device, applied to the raw direction `v` instead of the point, bounds the probability that
the *diagonal* direction `zeroBelow(chi(s), v)` vanishes --- and it has to be bounded, because on
such a content the "line" is a single point and the outcome map separates nothing. The paper's
`eps = md/q` does not account for that; see `reports/pasting-degenerate-diagonal-line.md`. The
collision average is `md/q` on an axis-parallel line and at most `md/q + 1/q` on a diagonal one,
and `delta_P` is still `poly(eps, md/q)`.

**Stated per pair of line types, which is stronger than the paper's mixture.** The line type is a
parameter (`LinePres`, with the six invariances the shift argument needs, and its four instances
`aPres`/`dPres` on each side), so the lemma is proved for each of the four pairs; the paper's
average over the line--point distribution is a convex combination of them.

**One methodological note, learned the hard way.** `lake env lean FILE` does **not** pick up the
lakefile's `leanOptions`, and this project sets `autoImplicit false`. A `W` that had fallen out of
scope was silently auto-bound under `lake env lean` --- the file "compiled" --- and `lake build`
then reported six errors and two `sorry`s. Use `lake build MIPRE.<Module>` to confirm a module, as
`CLAUDE.md` says; `lake env lean` is for fast iteration only.

#### 2026-09-20, part 3: the padded space and the sublines (`lem:qld-sublines`, partly)

`MIPRE/Background/QLD/Padded.lean`. The padding geometry and the paper's sampling procedure, with
the containment proved and the distributional half of Property 2 left open. The blueprint carries
the `\lean{}` list and no `\leanok` at either level, and the Comments there say exactly which half
is which; there are no new axiom guards, which is the correct state for a statement whose proof is
not claimed.

**What the seed block equivalence buys.** `seedEquiv : F ~ Fin m x Fin (q/m)` names the bijection
whose first component is `chi`, and `seedIn hm i s` is "the seed in block `i` with `s`'s offset".
Three facts follow, and the construction needs all three: `chi_seedIn` (the retargeted seed has the
prescribed index), `seedIn_self` (retargeting to the seed's own block is the identity, which is how
a branch that keeps the padded seed is written), and `sum_seedIn` (a uniform seed retargeted to a
fixed block is uniform on that block, which is the paper's "choose `s_X` uniformly at random
subject to `chi(s_X) = i`"). That last one is the only piece of the distributional half that is
proved.

**The construction is forced, and the forcing is not symmetric.** Moving along the padded line moves
the `X` block along the `X` block of the padded direction, so when that block is nonzero the
subline's direction *must* be it and the only freedom is which seed presents it. `padCase`
classifies a coordinate position into the `X` block, the `Z` block, `alpha`/`beta`, and the dummy
block, and the four cases say which blocks vanish --- differently for the two line types. An
axis-parallel padded line has a single-coordinate direction, so at most one of the two blocks is
nonzero. A diagonal one has `v` truncated below the axis index, so an index in the `X` block leaves
the whole `Z` block intact: both blocks are then nonzero and the `Z` subline is forced too, at axis
index `0` since nothing of its direction is truncated. That is the only place `subZ` looks at the
line type, and it is what the paper's round-12 note on this lemma repairs (the missing primes on
`w_X, w_Z` and the unspecified law of `s_X, s_Z`).

**Property 3 is definitional here.** The paper must check that an axis-parallel padded line has
axis-parallel sublines because its procedure chooses the types; here the type is a parameter handed
to both sides. What the paper actually uses its Property 3 for --- that the directions match --- is
`xBlk_dir_sub` and `zBlk_dir_sub`.

**The mixture-of-products law, done in the same session.** The general lemma turned out to be
cheaper in the `Equiv`-free form: an assignment to a sum index type *is* a pair of assignments to the
summands (`MIPRE/Foundations/Blocks.lean`, `sum_arrow_pair` and `sum_arrow_inl`), so no `Set.range`
subtype and no fibre-cardinality computation is needed. `padEquiv : (Fin m + Fin m) + Fin (2m) ~ Fin
(4m)` names the block decomposition -- `finSumFinEquiv` twice puts the `X` block on positions
`0..m-1` and the `Z` block on `m..2m-1`, which is exactly `xIdx` and `zIdx`, so the two computation
lemmas are `Fin.ext` plus `simp` -- and `sum_point_pad` is the product identity for a uniform padded
point.

The law is then four identities, one per case, and they are identities of *averages*: `avgSub_free`,
`avgSub_zc`, `avgSub_xc` and `avgSub_xc_dline` each say the average over the sampling space **equals**
the average over a product of two line-point laws. Stating them normalized is what makes them usable
and is also what hides an awkwardness: the multiplicities differ from case to case (`q^{6m}` when
neither side is forced, `m q^{6m}` when one is, `m^2 q^{6m}` when both are), because a forced side
reads a block of the padded raw direction and pays a `seedIn` factor while a free side reads its own
fresh randomness instead. Normalization divides all of that out. `field_simp` plus `ring` closes each
one once `((q/m : N) : R)` is rewritten as `q/m` over the reals, which is where `m | q` is used.

**The bookkeeping is worth naming.** A block decomposition turns one sum into two *where the old one
was*, so every step afterwards is: rewrite a sum sitting under others, move one sum past its
neighbours, pull a constant out. `sum_congr1..4`, `sum_nsmul1..4`, `sum_comm_four_in`,
`sum_comm_four_mid`, `sum_comm_six`, `sum_comm_six_swap` and `sum_prod_fst` are those three moves at
the arities this needs. With them each branch proof is one `rw` chain whose steps name what they do;
without them it is a tower of `Finset.sum_congr` whose shape has to be rebuilt every time. The reason
descent lemmas are needed at all is that `rw` cannot instantiate a pattern like `?g (zBlk u)` whose
metavariable would have to mention variables bound outside the rewrite -- so the rewrite has to
happen at the depth where the function is closed, and the `sum_congr` family is what gets it there.

**And one thing the consumer will need that is not in this lemma.** `pairs_of_lines_of_items` is
proved on the *single content* of the Pauli basis test, whose seed and raw direction are shared by
the two sides; `lem:qld-padded-lines` wants it on the product of two independent line--point laws.
That transfer is available and is not hard, because each of the pasting lemma's four hypotheses
involves only one of the two lines, and the relevant marginal of the product law coincides with the
relevant marginal of the content --- the other side's point is uniform and independent in both. It
is a re-instantiation of `one_sub_sum_bornProb_pasteJ_le` at pairs of contents with product weights,
not a new argument.

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
