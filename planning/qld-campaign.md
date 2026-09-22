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

#### 2026-09-20, part 5: the product-law transfer (`MIPRE/Background/QLD/Product.lean`)

`pairs_of_lines_of_items` is proved on the *single content* of the Pauli basis test, whose seed and
raw direction are shared by the two sides; `lem:qld-padded-lines` wants it on a product of two
independent line-point laws, which is what `lem:qld-sublines` delivers. The two distributions are
genuinely different, and the reason the transfer exists is worth stating before any machinery: **no
hypothesis of the pasting lemma involves both lines.** Each marginal consistency involves one line and
the two points; the fine self-consistency and the collision term involve one line only. So the only
laws that have to agree are

* one side's line-point data on its own,
* one side's data together with the *other side's point*,
* the two points,

and each has the same law under a content as under a product, because a content's two points and its
seed and raw direction are independent and uniform. `avg_content_eq_pair_X`,
`avg_content_eq_pair_Z` and `avg_content_eq_pair_pts` are those three identities, and each is **one
line** on top of a single general lemma (`MIPRE.avg_comp_equiv_fst`: a uniform average of a function
of one factor of a product is the uniform average over that factor). All the content is in choosing
the splitting of each sample space that isolates the part the quantity depends on --- `contentSplitX`
against `pairSplitX`, and so on --- after which the marginals match by construction.

**The change of variables generalizes for free.** `sum_content_shift_gen` is stated about contents but
uses nothing about them: a finite nonempty sample space, a shift action, and a direction the shift
does not move. `bijective_shift` and `sum_shift_gen` are the general statements and `sum_pair_shift`
is the instance at a pair with the shift acting on the `X` side only, which is what the product form
of the collision term needs.

### `lem:qld-pairs-of-lines` with the question distribution as a parameter (2026-09-20, done)

The transfer above says the two distributions agree on everything the pasting lemma looks at. Using it
needed the lemma itself to stop naming a distribution, and that is `pairs_of_lines_gen`: an arbitrary
finite nonempty `iota`, a content per side (`kX` presenting the `X` line, `kZ` the `Z` line), and a
shift `sh` with `kX (sh w a) = Content.shiftPt .X w (kX a)` and the same for `kZ`. `pairs_of_lines` is
the instance `kX = kZ = id`, `sh = Content.shiftPt .X`; `pairs_of_lines_prod`, in `Product.lean`, is
the instance `kX = pairCX`, `kZ = pairCZ`, `sh = pairShift`, and its two hypotheses are `rfl`.

Three things are worth recording, because none of them was visible from the plan.

**It is not a re-instantiation, it is a generalization, and `pasteLine` had to move first.**
`pasteLine` and `pasteJ_eq_pasteLine` read both lines off one content; they now take two. That is
three call sites and no mathematics, but it has to be done before the statement of the lemma can
mention two contents at all.

**The generalization belongs in `Lines.lean`, not `Product.lean`.** `Lines.lean` cannot import
`Product.lean`, so proving the general form on the product side would have meant duplicating a
170-line proof. `bijective_shift` and `sum_shift_gen` moved the same way, out of `Product.lean` and
into `Lines.lean`, with `bijective_shift_gen` and `sum_content_shift_gen` left as thin instances.

**Higher-order unification does not find `dir`.** `sum_shift_gen` takes `{dir : alpha -> V}` implicit
and infers it from `hdir : forall a w, dir (sh w a) = dir a`. At `dir = fun a => PX.dir (kX a)` the
pattern `?dir (sh w a)` against `PX.dir (kX (sh w a))` is not a Miller pattern and the elaborator
reports an application type mismatch with `?m` still in the expected type; naming `(dir := ...)` at
the three call sites is the whole fix. Two further failures were the same class of thing in reverse:
`Bas.Z.other` is not syntactically `Bas.X`, so `lineEvalMats_shiftPt_other` has to be applied through
a `show ... from` that lets unification do the reduction (which is what the content proof already
did), and the collision bound's shift sits under the binder of a filtered set, where `rw` cannot
reach and `simp only` can.

### The combining map and the padded line measurement (2026-09-20, done)

`lem:qld-padded-lines` asserts two things: that there *is* a POVM on the padded line with outcomes of
degree at most `md+1`, and that it is consistent with the padded point measurement at
`delta_combine`. The first is now formalized, in `MIPRE/Background/QLD/Combine.lean`; the second is
not.

**The combining map is a product of degrees, once the substitutions are seen to be affine.**
`combine` is `alpha(t) f_X(x(t)) + beta(t) f_Z(z(t))` built through Mathlib's `Polynomial` and
truncated back to a coefficient vector by `ofPoly`. All four substitutions are affine in the padded
parameter, so `md+1` is `1 + md` and nothing subtler. `eval_padCombine` is the paper's
parametrization-free defining property, and it is what a consumer should cite.

**The geometry is one disjunction, proved once.** `xBlk_dir_sub` (from the sublines work) says the `X`
block of the padded direction is *either* the `X` subline's direction *or* zero. In the first case
the subline parameter moves by exactly the padded shift; in the second it does not move. So it is
`p0 + c t` with `c` one or zero, and `subAff` is that pair. The paper instead walks the six branches
of its subline construction; here the branches were already absorbed into `xBlk_dir_sub`, so the
affine substitution costs two lines (`on_line_affEval`, `lineParam_affEval`) and the branch analysis
never reappears. Two small facts make the chain close: `rep_xBlk_padShift` (the subline's base point
does not move, by the same disjunction) and `subX_padShift` (the subline data is unchanged but in its
point, because the seed and the raw direction it reads are).

**The axis bound is `padCase`'s own case distinction.** A padded direction in the `X` or `Z` block
leaves `alpha` and `beta` constant along the line, so the combined polynomial inherits the degree of
the inputs --- which is `d` exactly when `lem:qld-axis-degree` supplies it, so
`degLE_padCombine_aline` takes that as a hypothesis rather than pretending to it. A direction at
`alpha`, `beta` or a dummy coordinate leaves *both* blocks constant, and then the polynomial is
affine and only `d >= 1` is used. `DegLE` is a predicate on coefficient vectors rather than a
change of type, because the answer alphabet is `LinePoly F (m*d)` throughout.

**Conditioning on the padded line is averaging over the fresh randomness.** `padLineMats` is
`Q-hat^l`: the uniform average over `SubRand` --- a seed and a raw direction per side --- of
`pasteLine` coarse-grained by `padCombine`. The paper writes a conditional expectation
`E_{(l_X,l_Z) ~ D|l}`; since `D` is *defined* by the sampling procedure, conditioning on `l` leaves
exactly that randomness, so no conditional distribution has to be formed. `sum_padLineMats` and
`posSemidef_padLineMats` are the POVM property, and `sum_filter_padLineMats` is the data-processing
step the paper's proof ends with, stated in the form `pairs_of_lines_prod` applies to.

**What remains, and why it is a separate piece of work.** The consistency bound chains three
Cauchy--Schwarz claims, and each consumes an input averaged over a *different* distribution: the
combined point measurement's self-consistency, `lem:qld-pairs-of-lines` on the product, and item 3 of
the expanded-line lemma on the `i`-th *restricted* line-point distributions `D_{Ty,i}`. That last
transfer --- an approximation at error `delta` over `D_Line` holds over each `D_{Ty,i}` at `2m delta`
--- is what produces the factors of `m` in `delta_combine = m poly(eps, md/q)`, and it is not
formalized at all. It is the natural next task.

### The distributional inputs of `delta_combine` (2026-09-20, done)

Three things the consistency chain of `lem:qld-padded-lines` needs, none of which is the chain itself.

**The restricted laws cost a factor of `m`, and that is all the `m` in `delta_combine` is.**
`avgRestr hm i` was already the paper's `D_{ty,i}` --- the law restricted to axis index `i`. What was
missing is one line: the `m` restricted laws are nonnegative and average to the unrestricted one
(`sum_avgRestr`), so each is at most `m` times it (`avgRestr_le_mul_avgAll`), and a product of two at
most `m^2` times the product (`avgRestr_prod_le_mul_avgAll`). The paper's factor is `2m` because it
mixes over the two line types; here the type is a parameter, so it is `m`.

**The combined point measurement must be indexed by the pair of points, not by the content.** This
was the real obstacle to using `pairs_of_lines_prod`, and it is worth recording why. Its hypotheses
are averages over pairs of line-point data of quantities involving `QA`; the content-level `QA` of
`lem:qld-combined-points` is an arbitrary function of the content, and `pairCX p` always has zeroed
probe registers, so *no* identity transfers a content average of it to a pair average. The fix is not
a transfer but a re-indexing: all four inputs of the joint-measurement construction
(`exists_projective_joint`) see the content only through its two points, so the construction runs at
`Point x Point` directly (`combined_points_pts`), and the resulting measurement is usable at any
sample space carrying two points. `avg_content_eq_pts` carries the four inputs there, and carries the
two ordered-product conclusions back to contents when the content-level derivations need them.

**A line presentation reads only its own side's line-point data.** `FactorsX` / `FactorsZ` say so;
both presentations satisfy them by `rfl`, because `dirOf` and `ddirOf` read the seed and the raw
direction, the base point is the canonical representative of the side's own point, and
`Content.question` at a line type reads nothing else. From it, `lineMats`, `param`, `lineEvalMats` and
`collProb` all factor through `Content.lpX`, which is the shape `avg_content_eq_pair_X` needs --- so
each content-level bound becomes a bound on the product (`avg_pair_eq_content_X` and its three
companions).

**The result.** `pairs_of_lines_prod_of_items`: `lem:qld-pairs-of-lines` on a product of two
independent line-point laws, from game-level hypotheses only, at the same `deltaPairs eps eps_c` as
the content version. That is the input the paper's Claim 17-3 consumes.

**What remains of `lem:qld-padded-lines`.** The chain itself: Claims 17-1, 17-2 and 17-3 of
`qld-combining.tex`. Three Cauchy--Schwarz steps --- replace `Q-hat^{x,z}` by the ordered product,
drop the `X` factor, bound the rest by `1` --- each of them a bound of the size of
`sum_content_marg_line_le`. The last additionally needs the padded line-point law written as a mixture
of products of subline laws, i.e. `avgSub_free` and its three companions carried from reals to
operators. That is the next task, and it is one piece of work rather than four.

### The three claims are avoidable: the padded law is a mixture of products (2026-09-20)

Sent to do the paper's Claims 17-1, 17-2 and 17-3. They are not needed for this construction, and the
reason is worth recording carefully, because it looks at first like the paper rules it out.

The paper's concluding `\cnote` on `lem:qld-4-13` says the three claims exist because "under the
distribution `D` the pair is correlated (for diagonal lines both coordinates share the line
parameter), so that decomposition is not available". That is true *given the padded line*: a uniform
point of it moves both blocks with one parameter. But the quantity to be bounded conditions on the two
**sublines**, not on the padded line. `(l_X, l_Z)` knows each block's coset in its own space; it does
not know the relative offset of the two blocks, which is exactly what `l` adds. Marginalize that out
and independence is restored --- and `avgSub_free` and its three companions (the Q-C5e work) already
prove the joint law to be *exactly* a product of the two marginals at a fixed padded seed.

So the chain collapses. Two new lemmas finish the distributional side:

* `avgSub_le_mul_avgAll`: the padded line-point law is at most `m^2` times the product of the two
  unrestricted subline laws, uniformly in the padded seed and the line type. Four cases by `padCase`,
  each an `avgSub_*` rewrite followed by the restricted-law transfer.
* `avgSubAB_le_of_forall`: `alpha` and `beta` at the sampled padded point are uniform and independent
  of both sublines. The proof is a change of variables, not a refinement of the block decomposition:
  translating the padded point in the `alpha` and `beta` coordinates alone is a bijection that leaves
  both sublines fixed (`shiftAB`, `subX_shiftAB`, `subZ_shiftAB`), so a bound holding for every fixed
  `(alpha, beta)` holds for the joint law. This is the trick that avoided splitting `padEquiv` into
  four blocks and reproving the four factorization theorems.

Plus the bridge `avgAll_eq_uniform` / `avgAll_prod_eq_uniform`, which identifies `avgAll` with the
uniform average over `LPData` that `pairs_of_lines_prod` is stated in.

**What remains is one data-processing step.** Coarse-grain the outcome pair `(f_X(x), f_Z(z))` along
`(r_1,r_2) |-> alpha r_1 + beta r_2`; coarse-graining only increases agreement, so the bound survives.
`sum_bornProb_le_map` is that inequality, but it is stated for `POVM` structures and the two families
here are bare matrix families, so the step needs them presented as `POVM`s first. Then
`avgSub_le_mul_avgAll` and `avgSubAB_le_of_forall` finish.

**The error.** This route gives `m^2 * delta_P`-shaped rather than the paper's
`m * (eps^{1/4} + delta_P^{1/4} + delta_Q^{1/4} + delta_Line^{1/2})`. That is not literally
`m * poly(eps, md/q)`, but `lem:qld-4-7` absorbs any polynomial factor in `m` into its `a(md)^a`
prefactor, and for small `delta_P` the new bound is the stronger one. Recorded, with the suggested
upstream action, in `reports/padded-lines-product-law.md`.

### The coarse-graining step, and `delta_combine` (2026-09-20, done)

`padded_lines_consistency` in `MIPRE/Background/QLD/PaddedLines.lean`: on the padded line-point law,
at every padded seed and line type, the combined point measurement read along `(alpha, beta)` at the
sampled point agrees with the pasted line measurement coarse-grained by the combining map, up to
`m^2 * delta_P`. That is the analytic half of `lem:qld-padded-lines`.

The proof is short because the distributional work was done: coarse-graining only increases agreement
(`sum_bornProb_le_fibre`, stated for bare matrix families rather than `POVM` structures --- the
pasted measurement is one), then `avgSub_le_mul_avgAll` and `avgSubAB_le_of_forall`.
`lineComb_eq_sum_pasteFib` is the one identification that makes the two sides comparable: the line
side's coarse-graining by the combining map *is* the coarse-graining, along the same linear form, of
its own outcome-pair fibres.

**Two hours went to a universe.** The Born-probability helpers were written in a section with
`variable {dA dB : Type}`, copying the convention of the strategy dimensions. But the index type here
is `(dA x Anc F m) x (F x F)`, which lives in `F`'s universe, not `Type 0`. Lean did not report a
universe error: it reported a `whnf` heartbeat timeout in the middle of the proof, and bisecting the
proof showed every individual piece fast and the assembly slow. The fix is `Type*` in that section.
Worth remembering: a `whnf` timeout in an application whose pieces all elaborate quickly is a
universe mismatch until proved otherwise.

**What still stands between this and a proof-level mark on `lem:qld-padded-lines`.** Three things,
all recorded in the blueprint Comments and in `reports/padded-lines-product-law.md`:

1. the error is `m^2 * delta_P`, of the form `poly(m) * poly(eps, md/q)` rather than the
   `m * poly(eps, md/q)` the statement advertises --- `lem:qld-4-7` absorbs it, and in the regime it
   is applied in the new bound is stronger by a fourth power in `eps`, but the *statement* should be
   corrected before it is claimed;
2. only one register version is proved; the symmetric one goes by the game's player symmetry, as
   `sum_content_hatComm_le_B` does it, but is not written;
3. the axis-parallel degree bound `d` is conditional on `lem:qld-axis-degree`, an additional target.

**And how big is `delta_P`?** Unfolded, `delta_P = deltaPairs eps eps_c ~ 7*10^3 * eps^{1/4}
+ 1.5 sqrt(md/q)`. It exceeds `1` --- says nothing --- unless `eps <= 4*10^{-16}`. The `eps^{1/4}` is
the two nested Cauchy-Schwarz chains, the constant is `lem:qld-obs-commutation`'s `57676416` and
`lem:qld-combined-points`' `461411328`. That is a property of the whole appendix, not of this step,
but it is worth writing down once.

### `lem:qld-padded-lines` closed (2026-09-20)

The three items that stood between the consistency bound and a proof-level mark, in order of size.

**The error's functional form.** The statement said `delta_combine = m * poly(eps, md/q)`; the route
taken gives `m^2 * delta_P`. Repaired in the blueprint to `poly(m) * poly(eps, md/q)`, which is what
is proved and what `lem:qld-4-7` consumes (its `a(md)^a` prefactor absorbs any polynomial factor in
`m`). This is a blueprint repair rather than a weakening of the Lean: the paper's own bound is
`m * (eps^{1/4} + delta_P^{1/4} + ...)`, and neither dominates the other everywhere.

**The other register version.** `padded_lines_consistency_swap`: the first version applied to the
swapped strategy on the swapped state, read back through `extHat_swapVec` and `bornProb_swapVec` --
the route `Swap.lean` already takes for the expansion stage's point items. Two new Foundations-level
facts were needed: `extVec2_swapVec` (swapping the state swaps the twice-extended state, exchanging
the two ancilla labels with it) and `xSqNorm_swapVec`. They sit in `PaddedLines.lean` because
`Foundations/Sandwich.lean` (`extVec2`) and `Foundations/StateDistance.lean` (`swapVec`) do not import
each other. A pleasant surprise: the first of the three mirrored inputs is the *original* `hX1`,
because `xSqNorm_swapVec` exchanges its two arguments and `hX1` is already in that orientation.

**The axis-parallel degree bound.** Half of `lem:qld-axis-degree` is now formalized and half is not,
and the split is worth stating precisely because it is not where one would guess.

* Formalized: `natDegree_lineRestrict_single_le` --- the restriction of a polynomial to `u_0 + t e_j`
  has degree at most its individual degree in `X_j`, since every other substitution is a constant. So
  a multilinear encoding restricts to an affine function of the line parameter, and
  `degLE_hatLine_outcome` adds that to a legal axis answer (degree `d` by the answer *type* here) for
  degree `d` when `d >= 1`.
* Not formalized: the phrase "can be supported". The strategy's line measurement is indexed by *all*
  answers, and a `dpoly` answer to an axis-parallel question --- rejected by the decider, but still an
  element of the measurement --- gives an outcome of degree up to `md`. Making the measurement
  supported on degree `d` means coarse-graining those into a default outcome and re-deriving
  `lem:qld-expanded-lines`' two items for the modified measurement at the cost of the format-failure
  probability. That is a piece of work in its own right.

So `lem:qld-padded-lines` states its degree-`d` clause *conditionally* on `lem:qld-axis-degree`, which
is how `degLE_padCombine_aline` has taken it all along, and is now marked formalized --- statement and
proof --- with its 178 axiom guards. `lem:qld-axis-degree` remains an additional target, with the
remaining half characterized in its Comments.

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

### PR D, stage 5: the exact half of `lem:qld-exact-paulis` and `lem:qld-swap` (2026-09-21)

Three new modules, all in the seconds-per-check regime (none reaches `MIPRE/Background/LIDT/`):
`MIPRE/Background/QLD/ExactPauli.lean`, `SwapUnitary.lean`, `NonMultilinear.lean`.

**The dividing line of this PR is the register count, and it is sharp.** Every statement of stage 5
splits into an *exact* part that is an identity between matrices and an *approximate* part that needs
the appendix's estimates on the expanded state. The exact parts are all formalizable now, and all of
them turn out to rest on one identity; the approximate parts need a six-register state with two
maximally entangled pairs and transport between two cuts, which the repository does not have and
which is a PR of its own. So this PR proves the exact parts unconditionally, in `S`, and neither
statement gets a `leanok` mark.

**The identity.** `wTilde_eq`: the appendix's binary observable factorizes,

```
W~^e(u)  =  pvmObs S (p ↦ (-1)^{tr(e (cd (π p) · u))})  ⊗  w (e · u),
```

a signed sum of the *pair* measurement tensor a bare generalized Pauli. Everything else is two lines
of the `pvmObs` calculus of `MIPRE/Foundations/PVM.lean` (which already had exactly the right
lemmas: `pvmObs_mul`, `pvmObs_isSelfAdjoint`, `pvmObs_mul_self`, `pvmObs_comm`) plus
`MIPRE.Weyl.wX_mul_wZ`. Self-adjointness, involutivity, the twisted commutation relation, unitarity
of the swap map, and the conjugation identity are each three lines once it is in place. The
`F_q`-valued syndrome label is what makes the factorization work: summing the syndrome projectors
against the character of `a` reassembles the Weyl operator on the line `r ↦ r·u`
(`MIPRE.Weyl.eq_sum_proj`), which needs no group law at all.

`sTensor` is the abstraction the swap side wants: operators of the shape `∑_p S_p ⊗ T_p` compose
factorwise when `S` is projective (`sTensor_mul`), and that is the *only* place projectivity is used
on that side.

**The twirl identity is cheaper here than in the paper.** `twirl_mul_twirl` says the product of the
two Weyl twirls is the maximally entangled projector. The paper proves it by an induction over the
`M` qudits, having presented the ancilla as an iterated tensor product. This repository presents
`(C^q)^{⊗ M}` as *one* matrix algebra indexed by `F_q^M`, so the whole thing is a single entry
computation: the `v`-average kills every off-diagonal pair of column indices by
`MIPRE.Weyl.sum_sgn_trDot`, and the `u`-average then leaves exactly the diagonal pairs of row
indices. This is the second dividend of that presentation choice, after the one `WeylEPR.lean`
records.

**The repaired arithmetic, and one addition to it.** `re_inner_ge_of_two_close` concludes exactly the
paper's `1 - 2√δ_S - 2δ_S`, and it needed a case split the paper does not have: a statement with no
hidden "for small enough `δ_S`" must handle `δ_S > 1`, where squaring `1 - √δ_S` reverses the
inequality. There the trivial bound `Re⟨x,y⟩ ≥ -2δ_S`, from the triangle inequality and the
nonnegativity of the two squared norms alone, is already stronger. `norm_sub_normalize_sq_le` is the
extraction of the auxiliary state, and it is where the fourth root of `δ_qld` comes from: the overlap
is the square root of the weight.

**The critical finding at node 1.2.2.15 is discharged as far as it goes.**
`prob_agree_ldEnc_le_of_not_multilinear` is Schwartz--Zippel in the agreement direction, and the
useful part of the statement is that it is *uniform in the interpolated data*: non-multilinearity
makes `g` distinct from every multilinear polynomial at once, so one application covers every `k`,
which is what the consumer's sum over `F_q^M` needs. `nonMultilinear_mass_le` is the aggregation.
One ingredient is still a hypothesis rather than a theorem: that a multilinear polynomial is the
interpolant of its own values on the cube. That is uniqueness of multilinear interpolation, an
independent `MvPolynomial` fact, and it is a follow-up.

**Five blueprint repairs and four upstream notes** came out of the reading; the two that are
mechanically verifiable are ledger dependency omissions at nodes `1.2.2.14` and `1.2.2.16`, both
confirmed by replaying the ledger with `scripts/ledger-sync.py`'s own event handling rather than by
reading node files. `reports/qld-stage5-blueprint-repairs.md` is the record. The sharpest of the
others: `lem:qld-swap` as it stood was provable by a three-line exact computation and left
`thm:qld`'s second item unreachable.

**What stage 4 costs, from this scoping.** `lem:qld-simultaneous` and its ten sub-lemmas are three
more PRs, not one, and there are two prerequisites the blueprint does not count against them: the
unproved half of `lem:qld-axis-degree` (a hard blocker --- without it the padded strategy's answer to
an axis-line question fails `clGame`'s format check) and a `povmValue → TensorProductStrategy.value`
adapter with dimension reindexing to `Fin n`, which nothing in the repository does and which is the
unique choke point for applying the vendored LIDT soundness from a `Foundations`-style strategy. That
adapter is the cheapest next piece: `Foundations`-level, no QLD content, and it unblocks everything
else in stage 4.

## Finishing the campaign: stages 4 and 5 (plan, 2026-09-21)

Where it stands after PR D, counted mechanically over the blueprint (tags and `\uses` wrap, so
the scan is whole-file): twenty QLD statements carry both `\leanok` marks and are guarded; three
have Lean without a proof-level mark --- `lem:qld-axis-degree` (the degree computation, not the
support half), `lem:qld-exact-paulis` (the exact half), `lem:qld-swap` (item 1's exact parts);
thirteen have no Lean at all --- `lem:qld-simultaneous` with its ten `lem:qld-global-*`
sub-lemmas, `lem:qld-helper`, and `thm:qld`. The ledger's stage 1.2 is 86 of 150 nodes annotated.
The Lean is 19 files and 11.5k lines under `MIPRE/Background/QLD/`, sorry-free, on about 2.3k
lines of Foundations support.

**The organising decision.** Stage 5 consumes stage 4 through one interface: the paper's
`lem:qld-4-7`, a projective measurement `S-hat_{g_X, g_Z}` on the padded local space whose
evaluated marginals are consistent with the opposite party's expanded point measurements, in both
register versions. That interface is fixed *first*, as a Lean `structure` (data plus hypotheses),
in the first stage-4 PR. Stage 5 is then proved against the structure while stage 4 fills it in,
and no `sorry` enters the tree at any point --- the pattern `NonMultilinear.lean` already follows
by taking multilinear uniqueness as a hypothesis.

What the interface has to carry, learned from the code rather than the paper: the Lean padded
strategy does not live on the paper's registers `A A' | B A''`. `lem:qld-padded-points` makes the
sandwich `M^X_a M^Z_b M^X_a` projective by dilating with an `F × F` ancilla per party (the
combining coefficients' register), so the padded state is `extHat ψ` on
`((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F))`, and the LIDT theorem returns `S-hat`
on the *extended* Alice register. Stage 5 must therefore be stated for an arbitrary Alice
register carrying a product ancilla, or the output compressed through `ancillaEmbed` first ---
and compression loses projectivity, which the Pauli construction `∑_g (-1)^{...} S-hat_g` needs.
So: carry the extended register, and state stage 5 over an abstract register type.

**The seven pull requests.**

| PR | closes | Lean-specific content |
|---|---|---|
| E | nothing; the prerequisite | `MIPRE/Foundations/RegisterReindex.lean`: `reindexStarAlgEquiv`, `POVM.reindex`, `reindexVec`, invariance of the Born rule, of `povmValue` and of `inconsistency`; `TensorProductStrategy.ofProjective` and `ofPVM` with `value_ofProjective`. `MIPRE/Background/LIDT/Adapter/Registers.lean`: `clSoundness_ldc_one_deltaCL_of_pvm`, the `ldc = 1` soundness for a strategy on arbitrary registers with a `povmValue` hypothesis. |
| F | `lem:qld-axis-degree` | the support half: coarse-grain axis-line answers off the degree-`≤ d` format to a default outcome, keep projectivity, bound the default outcome's mass by the expanded-lines consistency, re-derive the padded-lines items it feeds. Read the paper's treatment before designing anything. |
| G | `lem:qld-global-setup`, `-success`, `-pvm`, `-dummy` | the interface structure; the padded strategy as PVM families on `clGame (q, 4m, d, 1)` --- the seeded test's questions, answers in its format; the value bound, including the identical-line subtest by polynomial separation (`(md+1)/q`); `clSoundness_ldc_one_deltaCL_of_pvm`; `m ∣ 2^k → m = 2^j` (report note D); the LIDT import confined to this one module. |
| H | `-products`, `-linear`, `-separate` | the good/bad triple counting of `qld-combining.tex` lines 1050--1180, with `-linear` repaired to carry `md/q` (note B). |
| I | `-complete`, `-sandwich`, `-robustness`, `lem:qld-simultaneous` | the sandwich chain `Q_2 ≤ Q_3^{1/2}`; robustness is a repackaging, the LIDT theorem already returning both register versions (note C); the structure instance. |
| J | `lem:qld-helper`, `lem:qld-exact-paulis` | the six-register state `A A' B'' \| B A'' B'` with two EPR pairs and transport of `stateDist` between the cuts; multilinear interpolation uniqueness (Mathlib's vanishing lemma, or induction on the variables); the approximate half; the stale dependencies fixed (note A). Proved against G's structure, so independent of H and I. |
| K | `lem:qld-swap`, `thm:qld` | the ancilla embedding and item 2; the assembly: `16md > q` trivial with `a ≥ 64`, conjugation by the projector `P` against conjugation by `V`, Naimark descent in the consistency form, the square root halving `b`; marks and guards; `thm:qld`'s `\uses` corrected to `thm:lidt-cl-soundness-one`; #115 closed. |

Order: E, F, G, H, I, J, K. E and F are independent; G needs both; J needs only G. Each is the
size of PR C or PR D. (G is split: G-a is the Foundations half --- dilating a POVM strategy to a
projective one, and the seeded soundness for POVM strategies that follows --- and G-b the padded
strategy itself, its value bound, and the interface structure.) G's module is the one place QLD reaches the vendored MIPStarRE tree, so it
enters the slow build regime; nothing else in QLD should import it except the assembly.

**Two things to settle in G, not later.** The Lean shape of `thm:qld` must match its consumer ---
the introspection chapter, through `thm:pauli` of `ldt.tex` --- and not only the appendix that
proves it. And the paper's stage 4 is written for `ψ-hat` on four registers where the Lean's has
six from the start (the two `F × F` ancillas): the value claim `lem:qld-global-success` is to be
made for the strategy as built, `ptComb` and `lineComb` on `extHat ψ`, not for a paraphrase of it.
### PR F: `lem:qld-axis-degree`, closed by legalizing the strategy (2026-09-21)

The plan above priced this as the hard blocker: coarse-grain the ill-formatted axis answers into a
default outcome and re-derive both items of `lem:qld-expanded-lines` for the modified measurement,
paying the format-failure probability and moving the constants. Reading the paper's own
justification first (`qld-combining.tex`, the sentence proving `f_W ∈ deg_d(l_W)` for axis-parallel
`l_W`) showed why that is one legalization too late: the paper's strategies are *valid* --- they
answer each question in its prescribed format --- so a term of the convolution contributes only if
the strategy's factor sits on a legal `apoly` answer. The Lean strategies are not valid in that
sense, one `Answer F m d` serving every question; but they can be made so once, at the top, and it
costs nothing.

**`MIPRE/Background/QLD/Legalize.lean`.** `legalize q a` keeps a well-formatted answer and replaces
any other by `Question.defaultAns q`, a legal answer reading as `0`; `legalizeStrat M` relabels
every measurement along it. Four facts, each a few lines: projectivity is kept
(`isPVM_legalizeStrat`, coarse-graining); no element sits on an ill-formatted answer
(`LegalSupport`, `legalizeStrat_mats_eq_zero`); the value in `qldGame` does not decrease
(`povmValue_le_legalizeStrat`), because the decider rejects an ill-formatted answer before any rule
runs, so every accepted pair is untouched --- `sum_weight_bornProb_map` is the data processing that
makes this a one-screen proof; and every reading of `Win.lean` is unchanged, since all of them send
ill-formatted answers to `0` and the defaults read as `0` (`rdVal_legalize_point` and siblings,
lifted by `legalizeStrat_map` to `ptPOVM_legalizeStrat`, `ptObs_legalizeStrat`,
`hatPtPOVM_legalizeStrat`, `hatMats_legalizeStrat`). So every hypothesis of the appendix's chain
transfers to `legalizeStrat MA`, `legalizeStrat MB`, and every conclusion about point or Pauli
measurements transfers back, exactly.

**The support half, in `PaddedLines.lean` next to the degree computation.** For a `LegalSupport`
strategy and `d ≥ 1`: the strategy's axis reading has no element off `DegLE _ d`
(`lineAnsPOVM_aline_eq_zero_of_not_degLE`, every surviving answer is an `apoly`); the ancilla's
factor has none off `DegLE _ 1` (its elements sit on restrictions of `ldEnc h` to an axis line,
`degLE_lineCoeffs_aline`); so the convolution has none off `DegLE _ d`
(`hatLinePOVM_aline_eq_zero_of_not_degLE`), the presentation's `lineMats` at `aPres` likewise, and
the padded line measurement inherits it by contraposing `degLE_padCombine_aline`
(`padLineMats_aline_eq_zero_of_not_degLE`): `padLineMats` is an average of sandwiches of the two
sides' axis elements, and an outcome of degree above `d` only arises from a pair with a factor of
degree above `d`, which is zero. Zero mass, not `O(eps)`; no constant moves; `lem:qld-axis-degree`
carries both marks with 35 guards.

**What stage 4 gets from this.** The padded strategy is built from `legalizeStrat MA`,
`legalizeStrat MB`; its `aline` answer map may send an outcome to `apolys` of its truncation when
`DegLE f d` and to anything otherwise, and the "otherwise" branch has no mass. The blueprint
statement was rewritten to say what is proved (the without-loss-of-generality clause and the exact
support), its Comments to correct the earlier costing, and one stale sentence in
`lem:qld-padded-lines`' Comments ("not yet proved") was repaired in passing.

### PR G-b: the padded strategy and `lem:qld-global-success` (2026-09-21)

**What was proved.** `MIPRE/Background/QLD/PaddedStrategy.lean` defines the padded strategy for
the seeded test at `(q, 4m, d, 1)` as a family of POVMs on the registers of `extHat ψ`
(`padStrat`): the point measurement is the sandwich of the hatted point measurements coarse-grained
along `(a, b) ↦ αa + βb` and extended by the identity to the coefficients' register (`padPt`); the
line measurement at a question is the padded line POVM at the line's canonical base point, averaged
over the raw directions that produce the question (`lineMeas`, `rawSet`), read into the seeded
test's answer format (`lineAns`). `MIPRE/Background/QLD/PaddedValue.lean` proves
`padStrat_value`: a legal projective strategy of value `1 - ε` gives a padded strategy of value at
least `1 - 5 m² δ_P(ε, md/q + 1/q) - 4 δ_Q(ε) - (md + 1)/q`. Both `lem:qld-global-setup` and
`lem:qld-global-success` carry both marks, with 172 guards.

**The two facts the plan had not priced.** First, the strategy has to be a function of the
*question*, while `lem:qld-padded-lines` is stated at the *data* a sample generates the question
from, with the sample's point. The decider reads the answer polynomial at the parameter of the
sampled point relative to the canonical base point; moving the padded point along the padded line
does not change the pasted line measurement (`pasteLine_subPair_padShift`, from `xBlk_dir_sub`:
each block either moves along its own subline or does not move), so the strategy's line measurement
read at the sample's point is `padLineMats` at the sample's own data, coarse-grained by the
combining map there (`lineMeas_map_eval_mats`), which is the quantity of `sum_filter_padLineMats`.
Second, averaging the strategy's raw-fibre average against the sample's uniform raw direction gives
the plain average (`sum_rawSet_fiber`), and the sample's normalization `q^{-(8m+1)}` composed with
the fresh randomness is `avgSubAB`'s `q^{-(10m+2)}` (`inv_card_amb_eq`), so the line-point
agreement is *equal* to the seed-average of the padded consistency quantity
(`agreeSum_lineEvalFam_ptFam`), not merely bounded by it.

**The identical-line subtest.** The paper compares `f_A(u)` and `f_B(u)` at a uniformly random
point of the line. The formalization reads the sample's own point and makes its parameter uniform by
a change of variables: translating the point along the line is a bijection of the sample space that
fixes the line and shifts the parameter (`sum_shift_param`, with `lineParam_rep_add_smul`). This
needs the direction to be nonzero; a degenerate diagonal direction has probability at most `1/q`
(`sum_indicator_zeroBelow_eq_zero_le`) and is paid for in full. The evaluated disagreement is then
bounded through the agreement triangle for POVMs (`agreeSum_triangle`, `11δ` in place of the
paper's `9δ`), and polynomial separation costs `(md + 1)/q` (`one_sub_sum_bornProb_le_avg_eval`).

**Foundations added.** `MIPRE/Foundations/POVMMix.lean`: mixtures and uniform averages of POVMs
(`POVM.mix`, `POVM.avgOn`, extension by the identity `POVM.aOp`), the Born rule's linearity in them,
the agreement triangle, and the support-aware conditional-failure bounds
(`condFail_le_one_sub_sum_bornProb_map`, `_diag`) --- the decider's acceptance is implied by, not
equal to, agreement of the relabelled answers, since an ill-formatted agreeing pair is rejected,
and the implication is asked only of answers the strategy can produce.
`MIPRE/Background/LIDT/Adapter/Value.lean`: the seeded test's failure probability sample by sample
(`one_sub_povmValue_clGame`), the split into the nine type pairs (`sum_sample_eq`), and every point
lies on its own seeded line at the parameter `lineParam` computes (`rep_add_lineParam_smul`).

**Scope.** The plan gave G the four lemmas `-setup`, `-success`, `-pvm`, `-dummy`. G-a (dilation
and the seeded soundness for POVM strategies) and G-b (this) close the first two. `-pvm` --- applying
`clSoundness_ldc_one_deltaCL_of_povm` to `padStrat`, the one module of QLD that reaches the
vendored MIPStarRE tree --- and `-dummy` --- the Schwartz--Zippel argument that the recovered
polynomial does not read the dummy coordinates --- are a follow-up, G-c, together with the interface
structure stage 5 is proved against. `lem:qld-global-pvm`'s `\uses` now names
`lem:naimark-dilation`, which `-setup` no longer needs.

### PR G-c: the interface structure and `lem:qld-global-pvm` (2026-09-21)

**What closed.** `lem:qld-global-pvm`, with both marks. `MIPRE/Background/QLD/PaddedLIDT.lean`
feeds `padStrat_value` to `clSoundness_ldc_one_deltaCL_of_povm` at `(q, 4m, d, 1)`
(`exists_global_pvm`) and reads the conclusion back without the dilation (`exists_global_pvm_hat`):
projective low-degree measurements `GA`, `GB` on the dilated registers
`PadReg = ((dA × Anc) × (F × F)) × Ans`, consistent on the twice-padded state
`padState ψ = extVec2 (extHat ψ) ansZero ansZero`, on average over a uniform point of `F^{4m}`,
with the *original* strategy's padded point measurements `padPt` extended by the identity, and with
each other, all with error `deltaLD q m d ε = deltaCL q (4m) d (deltaGS q m d ε)`. This is the one
module of the QLD analysis that imports the vendored MIPStarRE tree (through
`LIDT/Adapter/Registers`); everything else in `MIPRE/Background/QLD/` stays in the fast regime.

**Why no further dilation is needed.** The dilation's point measurement compresses to `padPt`
(`POVM.map_compress` with `padStrat_point_map_toValue`), and on a product state the Born
probability of an operator on one party's dilated register depends on it only through its
compression (`inconsistency_extVec2`); the identity extension of `padPt` has the same compression
(`POVM.compress_aOp`), so each inconsistency against the dilation's point measurement *equals* the
one against `padPt.aOp` (`inconsistency_padState_aOp_left/right`). Doubly extended operators have
on `padState ψ` their `hatVec ψ` expectations (`bornProb_padState_aOp_aOp`, from the generic
`bornProb_extVec2_aOp_aOp`), which is how stages 2 and 3 will transfer. The paper's second Naimark
application to the recovered measurement is not needed, as the ledger's challenge history of node
1.2.2.13 already records.

**The interface.** `MIPRE/Background/QLD/Simul.lean` states `lem:qld-simultaneous`'s conclusion as
the structure `SimulPair ψ MA MB δ`: ancilla types `EA`, `EB`, a unit state `Φ` on
`((dA × Anc) × EA) × ((dB × Anc) × EB)` reducing to `hatVec ψ` on the hat registers
(`Φ_reduced`), projective pair measurements `SA`, `SB` with outcomes `PolyPair` (pairs of
individual-degree-`d` polynomials in `m` variables), and the two evaluated-marginal consistencies
(`consA`, `consB`, through `evalMarg`). Stage 5 is proved against it; stage 4c supplies
`Nonempty (SimulPair ψ MA MB δ_S)`. `lem:qld-simultaneous` carries `\lean{}` for the structure but
no `\leanok`: there is no existence theorem yet. The padded state of `-pvm` has the register shape
`((dA × Anc) × (F × F)) × Ans`, one associativity reindexing away from the structure's
`(dA × Anc) × EA` with `EA = (F × F) × Ans`; `RegisterReindex.lean` has `reindexVec`,
`POVM.reindex` and `inconsistency_reindex` for the transport, which is stage 4c's last step.

**A Lean point.** `DecidableEq (PadReg F m d dA)` is not found by instance synthesis at the default
`synthInstance.maxSize`: the five-fold product with the derived instance of the seeded answer type
is too large a term. `instDecidableEqPadReg` assembles the two halves by hand.

**Scope.** `lem:qld-global-dummy` moves to PR H (stage 4b), whose first step it is: it needs the
bridge from `LowIndDegPoly F (4m) d` (a coefficient vector) to `MvPolynomial (Fin (4m)) F` for
`prob_agree_le_individualDegree`, applied to `g(v, w) - g(v, w')` in `6m - 2` variables, and the
mass argument that a `w`-dependent outcome cannot be consistent with a `w`-independent point
measurement at two independent `w`, `w'`. The paper's `8md/q` and the standing `16md ≤ q` make
the `w`-dependent mass at most `4 δ_ld`.

### PR H-a: `lem:qld-global-dummy` (2026-09-21)

**What closed.** `lem:qld-global-dummy`, with both marks. `MIPRE/Background/QLD/Dummy.lean` (fast
regime) proves that an outcome of the global measurement which reads a dummy coordinate carries
little weight: `sum_bad_mass_le` gives `(1 - 8md/q) · W ≤ 2δ` for any projective `G` with outcomes
in `LowIndDegPoly F (4m) d` whose evaluation is `δ`-consistent with a point measurement that does
not read the dummy coordinates, and `sum_bad_mass_le_of_le` gives `W ≤ 4δ` under `16md ≤ q`.
`exists_global_pvm_wIndep` (in `PaddedLIDT.lean`) is the statement for the measurements of `-pvm`,
on both sides, at `4 δ_ld`.

**The route.** The paper's: resample the dummy coordinates (`mix u u'`), use the consistency at
both points (the pair swap `mixSwap` is an involution, so the resampled point is uniform too), and
bound the collision probability by Schwartz--Zippel. Two things are done differently. The paper's
orthogonality step needs projective point measurements; the formalization works with the padded
point measurements of the *original* strategy, which are POVMs, and uses `P_b + P_b' ≤ 1` for
`b ≠ b'` instead (`POVM.add_le_one`), so no dilation enters. And Schwartz--Zippel is applied to
`rename inl g − rename dumSub g` on the variable type `Fin (4m) ⊕ Fin (4m)`, with individual
degrees, giving `8md/q`; the lemma in `Foundations` is for `Fin n`, so
`prob_agreeOn_le_individualDegree` restates it for any finite variable type by transport along
`Fintype.equivFin`. The coefficient at any monomial of `g` involving a dummy coordinate survives
in the difference (`rename_toMv_ne`, by `coeff_rename_mapDomain` and `coeff_rename_eq_zero`).

**The bridge.** `LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with
entries at most `d`; `LowIndDegPoly.toMv` is the `MvPolynomial` it denotes, with `eval_toMv`,
`coeff_toMv` and `degreeOf_toMv_le`, and `degreeOf_rename_le` carries a degree bound along an
injective renaming to every target variable. Stage 4b's linearity and separation analyses will
use the same bridge.

**Two Lean points.** `swapVec_unit` in `QLD/Swap.lean` has `dA dB : Type`, while the dilated
registers live in `Type u`; applying it to `padState ψ` sends the unifier into a `whnf` timeout
rather than a universe error. `swapVec_dotProduct` (Foundations, universe-polymorphic) is the
lemma to use. And in a theorem named `LowIndDegPoly.eval_toMv`, the bare `eval` resolves to
`LowIndDegPoly.eval`, not `MvPolynomial.eval`.

### PR H-b: `lem:qld-global-products` (2026-09-21)

**What closed.** `lem:qld-global-products`, with both marks, for every outcome, both product
orders and both parties. `MIPRE/Background/QLD/Products.lean` (fast regime) proves the abstract
statement `sum_snorm_sq_ordComb_le`: for a projective `G` with outcomes in `LowIndDegPoly F (4m) d`
that is `δ`-consistent, on average over a uniform padded point, with the sandwich combination
`sandComb X Z u c = ∑_{αa+βb=c} Z_b X_a Z_b` of two projective families on Bob's register whose
average commutator weight is `κ`, and for an ordered product `ord` with `∑ ord = 1` deviating
from the sandwich by a contraction of the commutator,
`∑_u μ_u ∑_g ‖(G_g ⊗ (1 − ∑_{αa+βb=g(u)} ord(a,b))) Φ‖² ≤ 2δ + 2κ`. `ordZX` and `ordXZ` instantiate
it. `PaddedLIDT.lean` specializes it to a `GlobalPair` (`GlobalPair.products_ZX_A`, `_XZ_A`, and
the Bob versions `_ZX_B`, `_XZ_B` on the swapped state) with `κ = 57676416 ε` from
`sum_content_hatComm_le(_B)`.

**The route.** Split `1 − B = (1 − P) + (P − B)`. The first part is the consistency: `0 ≤ P ≤ 1`
gives `(1 − P)² ≤ 1 − P` (`mul_self_le_self_of_le_one`, from `Commute.mul_nonneg`), so
`∑_g E ‖(G_g ⊗ (1 − P))Φ‖² ≤ ∑_g E ⟨G_g ⊗ (1 − P)⟩ ≤ δ`. The second part: group by the value
`c = g(u)` and drop Alice's projector `∑_{g(u)=c} G_g ≤ 1` (`sum_snorm_sq_aOp_mul_bOp_le`), leaving
`E_u ∑_c ‖(1 ⊗ (P_u(c) − B_u(c)))Φ‖²`, the fibre sums of `D = sand − ord`, which sum to zero over
`(a, b)`; Parseval over `F_q` (`sum_avg_norm_fibre_sq`, transferred to `stateVecB` by
`sum_avg_normSq_stateVecB_fibre_eq`) gives `(1 − 1/q) ∑_{ab} ‖(1 ⊗ D(a,b))Φ‖²` with no factor `q`,
and `D = Z[X, Z]` (order `Z X`) or `−(1 − Z)[X, Z]` (order `X Z`) is a contraction of the
commutator. The uniform padded point is read as independent uniform `(x, z, α, β)` by the
involution `abSwap` (`sum_uniform_pad4`), and the verifier's content as independent uniform `(x, z)`
(`sum_content_blocks`).

**The structure.** `GlobalPair ψ hprojA hprojB δ` (in `PaddedLIDT.lean`) bundles `-pvm`'s output:
`GA`, `GB` and the three consistencies. `exists_globalPair` is `-pvm`; `-dummy`
(`GlobalPair.sum_bad_mass_A_le`, `_B_le`) and `-products` are theorems on it, and so will be
`-linear`, `-separate` and stage 4c. The earlier bundled existential `exists_global_pvm_wIndep` is
gone.

**Two remarks.** The paper's `-products` is for `w`-independent outcomes and goes through the
dilated projective joint measurement of `lem:qld-4-12`; the sandwich POVM suffices and the
estimate holds for all outcomes, so `-dummy` is not used here (its `\uses` no longer names it).
The `X Z` order needs `‖(Z X Z − X Z) w‖ ≤ ‖[X, Z] w‖`, which is not obvious termwise but is the
identity `Z X Z − X Z = −(1 − Z)(X Z − Z X)`, valid for a projector `Z`.

### PR H-c: `lem:qld-global-linear` (2026-09-21)

**What closed.** `lem:qld-global-linear`, with both marks, for all outcomes and both parties.
`MIPRE/Background/QLD/Linear.lean` (fast regime) proves the abstract statement
`sum_bad_linear_mass_le`: if a projective `G` with outcomes in `LowIndDegPoly F (4m) d` satisfies
the `X_a Z_b` products estimate `∑_g E_u ‖(G_g ⊗ (1 − B_u(g(u))))Φ‖² ≤ Δ`, then
`(1 − 2η) · ∑_{g not linear in (α,β)} ⟨G_g ⊗ 1⟩ ≤ 2Δ` with `η = (1 + 2d + 4md)/q`. "Linear in
`(α, β)`" is `IsLinAB g`: every monomial of `g` has exponents `(1, 0)` or `(0, 1)` on the two
combining coordinates. `PaddedLIDT.lean` specializes it to a `GlobalPair`
(`GlobalPair.sum_bad_linear_mass_A_le`, `_B_le`) with `Δ = 2δ + 2 · 57676416 ε` from
`products_XZ_A`, `_B`.

**The route.** Per bad outcome, `⟨G_g⟩ ≤ 2‖(G_g ⊗ B_u)Φ‖² + 2‖(G_g ⊗ (1 − B_u))Φ‖²` for every
`u`; the second terms are the products estimate, so everything rests on
`E_u ‖(G_g ⊗ B_u(g(u)))Φ‖² ≤ η ⟨G_g⟩` (`sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB`). The
uniform padded point is read as a uniform base point `u₀` with a fresh uniform pair `(α, β)`
written into the combining coordinates (`sum_uniform_setAB`, the map `setAB` being `q²`-to-one by
the involution `abSwap`); `g(setAB u₀ α β)` is the bivariate polynomial `pAB g u₀` (`eval_pAB`),
whose coefficients are the `coef`s of `g` — `LowIndDegPoly.coef g T t`, the coefficient vector of
the monomial pattern `t` on the coordinates `T` as a polynomial in the others
(`eval_eq_sum_coef`). A bad `g` has a nonzero non-linear coefficient (`exists_bad_coef`);
Schwartz--Zippel in `4m` variables (`card_eval_eq_zero_le`) bounds the base points where it
vanishes by `4md/q`, and there each `B` is a contraction (`snorm_sq_ordComb_ordXZ_le`). At the
other base points `pAB g u₀` differs from every linear form (`pAB_ne_linAB`): the `β = 0` pairs
cost `1/q`, and for `β ≠ 0` the fibre has one `b` per `a`, so Pythagoras over the orthogonal
`X_a` (`snorm_sq_ordComb_ordXZ_of_ne`, from `snorm_sq_sum_proj_mul`) writes
`‖(S ⊗ B)Φ‖² = ∑_{fibre} W(a, b)` with weights summing to `⟨S⟩` (`sum_snorm_sq_ordXZ_eq`);
exchanging the sums, each weight is counted with the agreement probability of two distinct
bivariate polynomials, `≤ 2d/q` (`sum_agree_two_le`).

**Two remarks.** The paper displays `O((δ_ld + δ_Q)^{1/2} + md/q)` for the `w`-independent
outcomes and notes in a `cnote` that the quadratic expansion gives the linear bound; the
formalization proves the linear bound for all outcomes, so `-dummy` is not a dependency here
either, and the constant is explicit. Lean points: `Fintype.card_ne_zero` needs `Nonempty F`,
which `omit [Field F]` removes; `not_imp` is ambiguous between `_root_` and `Classical`
(the former deprecated); and the `ᴴ` notation is scoped to `Matrix`, so a `namespace MIPRE` block
needs `open Matrix`.

### PR H-d: `lem:qld-global-separate` (2026-09-21)

**What closed.** `lem:qld-global-separate`, with both marks, for all outcomes and both parties.
`MIPRE/Background/QLD/Separate.lean` (fast regime) defines the good outcomes `IsGood g`
(`g = α g_X(x) + β g_Z(z)`, every monomial with exponents `(1, 0)` on `(α, β)` and nothing else
outside the `x` block, or `(0, 1)` and nothing else outside the `z` block) and proves
`sum_not_isGood_mass_le`: from the two ordered-product estimates with bounds `Δ₁` (order `X_a Z_b`)
and `Δ₂` (order `Z_b X_a`), `(1 − 2η) · ∑_{¬IsGood g} ⟨G_g⟩ ≤ 2Δ₁ + 2Δ₂` with
`η = (2 + 2d + 8md)/q`. `PaddedLIDT.lean` specializes it to a `GlobalPair`
(`GlobalPair.sum_not_isGood_mass_A_le`, `_B_le`, right-hand side `4(2δ + 2 · 57676416 ε)`).

**The route.** `not_isGood_cases`: a non-good outcome is non-linear, or linear with the `β`
coefficient `gB` reading a coordinate outside the `z` block (`LowIndDegPoly.DepOutside`), or linear
with the `α` coefficient `gA` reading a coordinate outside the `x` block; `isGood_of` is the
converse, through `coef_maskOff`. The assembly of `-linear` is restated abstractly
(`sum_bad_mass_le_of_avg`: any bad predicate, any Bob-side family `B`), applied once per order
with the common `η`, and the two weights are added by a union bound. Per bad linear outcome and
base point `u₀`, `g(setAB u₀ α β) = α gA(u₀) + β gB(u₀)` (`eval_setAB_of_isLinAB`, from
`pAB_eq_linAB_of_isLinAB`), the fibre contains the diagonal pair always and any other pair for at
most `q` values of `(α, β)` (`card_filter_linear_le`, a nontrivial linear form on `F²`), so the
`(α, β)`-average is at most `2/q ⟨S⟩ + W(gA(u₀), gB(u₀))` (`sum_ab_snorm_sq_ordComb_le_of_lin`),
and the diagonal weight is `⟨S ⊗ Z X Z⟩ ≤ ⟨S ⊗ Z_{gB(u₀)}(zBlk u₀)⟩` (`snorm_sq_ordXZ_le_bornProb`).
Then `sum_uniform_bornProb_readOn_le`: for an operator family reading only the coordinates in `T`
and a polynomial `H` reading a coordinate outside `T`, `E_u ⟨S ⊗ Op_u(H(u))⟩ ≤ 8md/q ⟨S⟩`. The
uniform point is read as a uniform `T` block with the rest uniform and independent
(`sum_uniform_mixOn`, the involution `mixOnSwap`); `LowIndDegPoly.restrictOff H T z` is `H` with
the `T` coordinates fixed to `z`, as a coefficient vector in the others (`eval_restrictOff`,
through `eval_eq_sum_coef` on `Tᶜ`); it is non-constant unless a nonzero coefficient vector
`H.coef Tᶜ t₀`, `t₀ ≠ 0` (`exists_coef_ne_zero_of_depOutside`), vanishes at `z`, and a
non-constant vector takes each value with probability at most `4md/q`
(`sum_uniform_eval_eq_zero_le` on `restrictOff − const b`). The `Z X` order is the `X Z` order with
`(X, a, α)` and `(Z, b, β)` exchanged (`ptComb_ordZX_eq`, reindexing the fibre by `Prod.swap`), so
the mirror half reuses every lemma with the two families swapped and the base point read as a
uniform `x` block.

**Remarks.** The paper's bound is `O((δ_ld + δ_Q)^{1/2} + md/q)` and its Schwartz--Zippel counts
are `(2m+2)d/q` and `2md/q`; the formalization's are `4md/q` each, from `card_eval_eq_zero_le`
over all `4m` coordinates, and the bound is linear. Since the good outcomes read no dummy
coordinate, `-dummy` is subsumed for stage 4c. Two Lean points: `gcongr` on
`c * ↑(#s) ≤ c * ↑(#t)` descends to the Finset inequality `s ≤ t`, so `mul_le_mul_of_nonneg_left`
with `exact_mod_cast` is the predictable route; and a multi-line `nlinarith [...]` hint list
inside a term-mode `by` breaks on the continuation line's column, so the facts go in `have`s.

### PR I: stage 4c — `-complete`, `-sandwich`, `-robustness`, `lem:qld-simultaneous` (2026-09-22)

**What closed.** The four remaining statements of stage 4, and with them the interface stage 5 is
proved against. `MIPRE/Background/QLD/Complete.lean` (fast regime) relabels each good outcome
`g = α g_X(x) + β g_Z(z)` by the pair `(g_X, g_Z)` (`pairOf`, through
`LowIndDegPoly.blockPoly`, a coefficient vector read on a block of the variables, with
`eval_blockPoly` for a vector supported there), and `pairMeas` is the coarse-graining of the
global measurement by it: projective (`isPVM_pairMeas`), complete, with the non-good outcomes
absorbed into the fixed pair — the paper's complement `R`, whose weight `lem:qld-global-separate`
bounds. `inconsistency_map_eq` reads the inconsistency of any such coarse-graining outcome by
outcome. The marginals: `one_sub_two_sqrt_le_sum_snorm_sq` turns the products estimate into
`∑_g E_u ‖(G_g ⊗ B_u(g(u)))Φ‖² ≥ 1 − 2√Δ` (triangle inequality, then one Cauchy--Schwarz over the
pairs `(u, g)`), and `marg_Z_ge`, `marg_X_ge` bound the rest by the fibre analysis of `-separate`
plus the non-good weight, giving `E_z ∑_g ⟨G_g ⊗ Z_{g_Z(z)}(z)⟩ ≥ 1 − 2√Δ − 2/q − δ_G` and the
`X` mirror; `inconsistency_evalMarg_Z_le`, `_X_le` are the same statements as inconsistencies.

**The errors.** `PaddedLIDT.lean` names them as functions of the `GlobalPair` error `δ` and the
strategy's failure `ε`: `deltaProd δ ε = 2δ + 2·57676416 ε` (the products bound `Δ`),
`deltaSep δ ε = 8 Δ` (the non-separated weight `δ_G`) and
`deltaS q δ ε = 2√Δ + 2/q + δ_G`. `deltaSep` needs `48 m d ≤ q`: `2 + 2d + 8md ≤ 12md` for
`m, d ≥ 1`, so `η = (2+2d+8md)/q ≤ 1/4` and the factor `1 − 2η` of `-separate` is at least `1/2`
(`one_sub_two_eta_ge`). The standing assumption of the subsection is `16md ≤ q`; the regime
`16md < q < 48md` is absorbed in the assembly the same way `16md > q` is, by enlarging the
universal constant, and the blueprint says so.

**The instance.** `GlobalPair.toSimulPair` builds a `SimulPair` with
`EA = EB = (F × F) × CL.Answer F (4m) d 1`, the state `padState ψ` reindexed by
`Equiv.prodAssoc`, and the completed pair measurements reindexed likewise. The transport is
four lemmas: `isPVM_reindex` (a reindexing is a `*`-isomorphism, so projectivity survives),
`reindex_aOp_aOp` (extending twice by the identity and reassociating is extending once by the
product ancilla), `POVM.aOp_aOp_reindex` (its POVM form), and Foundations'
`inconsistency_reindex`, `bornProb_reindex`, `reindexVec_unit`. `exists_simulPair` composes it
with `exists_globalPair`.

**Two remarks.** The paper's `lem:qld-4-7` also announces the sandwiched joint estimate; stage 5
consumes only the two evaluated marginals, so the structure carries those and the sandwich stays
where it is used, inside `-sandwich`. And the bound here is linear in `δ_ld` and `ε` up to the one
square root the Cauchy--Schwarz costs, where the paper writes `O((δ_ld + δ_Q)^{1/2} + md/q)`
throughout; `δ_S` is closed under that square root by halving `b`, which is the assembly's job.

### PR J-a: `lem:qld-helper` (2026-09-22)

**What closed.** Both items of `lem:qld-helper`, on an abstract `SimulPair`.
`MIPRE/Background/QLD/Helper.lean` (fast regime). Item 1 is the consistency read as an agreement:
`sum_bornProb_diag_eq` says the inconsistency of two POVM families on a unit state is one minus
the probability that they agree (from `sum_diag_eq_one_sub`, which was already there for the pair
form). Item 2 is the same-party statement the Pauli construction needs, and rests on one matrix
identity (`aOp_mul_one_sub_eq`): with `T`, `A` on Alice and `B` on Bob a projector,
`(T ⊗ 1)(1 − A ⊗ 1) = (1 − 1 ⊗ B)(T ⊗ 1 − 1 ⊗ B) − (T ⊗ 1)(A ⊗ 1 − 1 ⊗ B)`, because the cross
terms `(T ⊗ 1)(1 ⊗ B)` cancel and `(1 − 1 ⊗ B)(1 ⊗ B) = 0`. Both front factors are contractions
(`snorm_mul_le` with `bnd_aOp`, `bnd_bOp`), so the same-party deviation is at most the two
cross-party ones: `2δ_S` from item 1 (`xSqNorm_sum_le_two_mul`) and `172 ε` from the
self-consistency of the expanded point measurements. Squaring costs a factor two on each, giving
`4δ_S + 344ε`.

**Two transfers.** The self-consistency (`hatPOVM_consistency`) is stated at the verifier's
content; `sum_content_pt` says the content's `W` block is uniform, so it reads at a uniform point.
And it lives on the expanded state, while the helper is on the padded state `Φ`: `SimulPair`'s
`Φ_reduced` gives the Born probabilities, and `Simul.lean` now derives the two squared state norms
from it (`stateSqNorm_aOp`, `normSq_stateVecB_aOp`, through the generic
`stateSqNorm_eq_bornProb_one` and `normSq_stateVecB_eq_one_bornProb`), hence the whole cross-party
deviation (`xSqNorm_aOp`, by the three-term expansion `xSqNorm_eq_expand`).

**A Lean point.** A `have h : ∀ {R S : Type*} ...` inside a declaration whose own universe is
fixed produces `AddConstAsyncResult.commitConst: constant has level params [u, u_2, u_3] but
expected [u]`; the two norm bridges had to become top-level universe-polymorphic theorems.

### What PR J-b needs, read off the paper (2026-09-22)

The approximate half of `lem:qld-exact-paulis` is the paper's
`lem:qld-construct-the-paulis`, item 1: `M̃^{W,ind_m(u)}_a` (the `ExactPauli.lean` construction,
`mTilde`) is consistent with the strategy's `(Point, W)` point measurement on the opposite party,
on average over a uniform `u ∈ F_q^m`. Its proof is a four-line chain, and the fourth line is the
one that was repaired twice in the paper:

1. expand `mTilde` by `eq:tilde_M`, which is `mTilde_eq_sum`, already formalized;
2. recognize `M^{(Point,W),u}_{a} ⊗ τ^W_{cd(g)·ind_m(u) − a}` summed over `a` as the hatted point
   measurement `M̂^{(Point,W),u}_{cd(g)·ind_m(u)}` --- the definition of `hatPtPOVM`;
3. **the substitution** `cd(g)·ind_m(u) ↦ g(u)`, which is false for non-multilinear `g`: the
   error is at most twice the mass `Ŝ^W` puts on non-multilinear outcomes;
4. apply `lem:qld-helper` item 1.

Step 3 is the one with Lean already in place from PR D:
`prob_agree_ldEnc_le_of_not_multilinear` (two distinct polynomials of total degree `md` agree at a
uniform point with probability at most `md/q` --- the *agreement* direction, which is the repair),
`nonMultilinear_mass_le` (the abstract aggregation: `S` a probability vector, `T ≤ S` with
`T ≤ c·S` off a set and `∑T ≥ 1 − η`, then the mass off the set is at most `η + c`), and
`sum_sub_le_of_eq_on` (the substitution error of two families agreeing on that set). What is
missing is the chain that produces the hypotheses of `nonMultilinear_mass_le` for the actual
measurements: the Pauli-basis consistency check in its *same-side* form
`(M^{(Point,W),u}_{a'})_A ≈ (M^{(Pauli,W)}_{[g_h(u) = a']})_A`, obtained from
`lem:qld-win-implications` in both orientations plus the self-consistency of the point
measurements, and the projective family `N_k = ∑_{h + h'' = k} M^{(Pauli,W)}_h ⊗ τ^W_{h''}` it
produces. That same-side step is `lem:qld-helper` item 2's pattern (`aOp_mul_one_sub_eq`) applied
to the Pauli-basis measurement rather than the marginal.

The six-register state `A A' B'' | B A'' B'` enters only here: `mTilde` acts on
`B B' B''` while the point measurement acts on `A`, so the two cuts of the paper's
`ψ̂` are needed at once, with `stateDist` transported between them. `SwapUnitary.lean` already has
the two twirls and the maximally entangled state; the transport is the piece to write.

### PR J-b, first piece: the point and Pauli-basis measurements on one party (2026-09-22)

`MIPRE/Background/QLD/PauliBasis.lean` (fast regime). The repaired proof of
`lem:qld-exact-paulis` needs the `(Point, W)` measurement to be close to the low-degree reading of
the `(Pauli, W)` answer *on the same party*, because the Pauli basis answer does not depend on the
sampled point and that is what lets Schwartz--Zippel see a uniform point independent of the
operators. Both inputs are cross-party items of `lem:qld-win-implications` --- `item_consistency`
at the type `(Point, W)` and `item_pauli_consistency` --- and they share Alice's point
measurement, so Foundations' `normSq_stateVecB_sub_le` (the triangle
`‖(1 ⊗ (N₁ − N₂))ψ‖ ≤ ‖(A ⊗ 1 − 1 ⊗ N₂)ψ‖ + ‖(A ⊗ 1 − 1 ⊗ N₁)ψ‖`, squared at the usual factor two,
written for the pasting lemma and reused verbatim here) removes it: `sum_normSq_point_sub_pauli_le`, at `688 ε` on average over the verifier's content.
This is on the bare strategy; carrying it to the expanded state, and from there to the mass
argument, is the next step.

**The ancilla transfer.** A second piece of the same module: `sum_normSq_stateVecB_conv_eq`. Every
hatted measurement is a convolution `X̂_c = ∑_{a+b=c} X_a ⊗ T_b` of the party's own family with the
ancilla's Weyl measurement, and for a *projective* `T` the cross terms of `X̂ᴴ X̂` vanish --- the
ancilla outcome determines the other one (`conjTranspose_conv_mul_conv`) --- so the same-party
deviation on the expanded state equals the one on the strategy's own state, with no loss at all.
Summing a convolution over its outcome frees the ancilla factor (`sum_conv`), and
`bornProb_expVec_kron` then peels the maximally entangled pair off, whose own weight is one. With
this and the previous piece, what is left of the approximate half is the aggregation itself: the
projective family indexed by cube data, and `nonMultilinear_mass_le` applied to it.

**On the expanded state.** `sum_normSq_hat_point_sub_pauli_le` puts the two together: a hatted
point measurement is `conv X T` for `X` the party's own reading and `T` the syndrome measurement
(`hatPtPOVM_mats_eq_conv`, which is `POVM.map_mats` and nothing more), the Pauli basis reading at
the point has the same shape against the same `T`, their difference is the convolution of the
differences, and the transfer removes `T`. So the constant on the expanded state is the bare one,
`688 ε`.

### PR J, the rest: the mass at bad outcomes, and item 1's agreement (2026-09-22)

`MIPRE/Background/QLD/Multilinear.lean` (fast regime). With the closeness of the previous piece in
hand, the aggregation goes through, and then so does item 1.

**The point-independent family.** `hatPauli MB W` is the strategy's `(Pauli, W)` measurement
convolved with the ancilla's Weyl measurement --- projective (`isPVM_hatPauli`), indexed by cube
data, and crucially not a function of any sampled point. `hatPauli_map` says that reading it at
`u` gives the hatted Pauli measurement there, because the pairing is additive and coarse-graining
therefore commutes with the convolution. `POVM.map_kron_map` is the small general fact that makes
that one rewrite.

**The substitution.** `abs_sum_weighted_bornProb_le` is Cauchy--Schwarz against a projective
family at each question followed by Jensen for the average; against Alice's evaluated marginal it
replaces Bob's point measurement by the hatted Pauli family at cost the root of their average
squared distance, `√(688 ε)` (`SimulPair.sum_bornProb_hatPauli_ge`).

**The aggregation.** `sum_mass_off_le` is `nonMultilinear_mass_le` in operator form: a projective
`S` on one party, a projective `N` on the other, two labellings, an agreement lower bound and a
uniform bound on how often a bad outcome matches any one label. `SimulPair.sum_bornProb_off_le`
instantiates it, and the marginal it uses is `polyMarg` --- indexed by *polynomials*, not by their
value at the point, which is the whole point: the outcome operator must not depend on the point
Schwartz--Zippel then samples. The result is `δ_S + √(688 ε) + md/q`.

**Item 1.** Expanding `mTilde` and contracting the generalized Pauli on the opposite party's
ancilla against the strategy's point measurement turns item 1's left-hand side into the outcome
sum with the label `coded(g) · ind_m(u)`, which differs from the helper's `g(u)` only off the good
set. `sum_sub_le_of_eq_on` pays twice the mass, and `SimulPair.sum_bornProb_cubeData_ge` is

    E_u ∑_g ⟨Ŝ^W_g ⊗ M̂^(Point,W),u_{coded(g)·ind_m(u)}⟩ ≥ 1 − δ_S − 2(δ_S + √(688 ε) + md/q).

**Two things this found**, both in `reports/qld-stage5-blueprint-repairs.md`. Uniqueness of
multilinear interpolation, listed here as the chain's one outstanding ingredient, is not needed:
take the good set to be `IsInterp`, "g is the encoding of its own cube data", and agreement on it
is definitional while Schwartz--Zippel off it is immediate and uniform in the datum. And the
six-register state is not needed for item 1: each orientation of `lem:qld-4-7` reads one of the
paper's two pairs, `hatVec` is one such cut, and in it the paper's `A''` is the opposite party's
ancilla half --- so the pairing is bipartite. The second pair is still needed to read the display
*as* `mTilde`, one operator on one party, which is what stands between this and a statement-level
`\leanok`.

### PR K, first piece: `mTilde` as one operator on one party (2026-09-22)

`MIPRE/Background/QLD/MTilde.lean` (fast regime). The merged stage 5a left item 1 of
`lem:qld-exact-paulis` as a sum over the simultaneous measurement's outcomes; the paper states it
as a closeness of two measurements, and this reads it that way. It is a reindexing, not an
estimate, and the reason is worth recording because the campaign carried the opposite belief for
three PRs.

**The obstacle was not real.** The note said `mTilde` needs `S-hat^W` and the generalized Pauli on
disjoint registers of one party, `A A'` and `A''`, while `SimulPair.SA` acts on all of
`A A' A''` --- so the paper's second entangled pair had to be adjoined and the operators
transported between two cuts. The first half is true; the conclusion is not. In `hatVec`'s cut the
register `A''` is the *opposite party's* ancilla half: it is already present, on the far side. So
writing `M~` as one matrix regroups the same six registers along a third cut,
`A A' A'' | B`, and that is `bornProb_regroupVec` --- one entry computation
(`reindex_regroupEquiv`) plus one invariance of the quadratic form (`qform_comp_equiv`). What made
it look impossible was that Foundations only had `quadForm_reindex`, which reindexes the two
parties *separately* and therefore cannot move a factor between them; the unary companion is three
lines and was simply missing.

**What it took.** `isPVM_mTilde` (through `sTensor_mul`, so through projectivity of the pair
measurement and nothing else); `sum_kron_syn_eq_hatMats`, the characteristic-two shift that turns
`mTilde`'s defining sum into the hatted point measurement --- `c + a` is the partner of `a` in the
fibre of the sum, so summing along `a` is summing over the fibre; and then
`SimulPair.sum_bornProb_mTilde_ge` and `SimulPair.inconsistency_mTilde_le`, the latter in the
paper's own `simeq_delta` form at `delta = delta_S + 2(delta_S + sqrt(688 eps) + md/q)`.

**And the exact half moved onto the same objects.** `wTilde`'s three relations were proved for an
abstract projective pair measurement; `SimulPair.wTildeAt` instantiates them at the simultaneous
one, and `wTilde_mul_add` adds the fourth relation the lemma asserts and the file did not have,
linearity in the argument (both tensor factors are additive, so it is exact). With that,
`lem:qld-exact-paulis` carries `\leanok` at both levels, 94 guarded declarations.

One small infrastructure note: the index of `mTilde`'s matrices is a four-fold product whose
`DecidableEq` runs past the default `synthInstance.maxSize` --- each half alone is found, the
product is not. Raised in that file and nowhere else.

### PR K, second piece: the swap isometry's state estimate (2026-09-22)

`MIPRE/Background/QLD/SwapState.lean` (fast regime). `SwapUnitary.lean` had item 1 of
`lem:qld-swap` in three separate pieces --- the exact conjugation, `twirl_mul_twirl`, and the
repaired arithmetic chain --- and not the assembly, because `twirl_mul_twirl` lives on the two
ancilla halves alone while the state lives on all four registers. The assembly is
`exists_auxVec_close`, and it was smaller than the note here predicted.

Two reasons. First, **the twirl is a projection**, not merely a contraction: the Weyl family is a
homomorphism, so `(sum_u w_u (x) w_u)^2` collapses --- for each `s` there are exactly `q^n` pairs
`(u,v)` with `u + v = s`. That is `twirl_mul_self`, and it lets `snorm_le_one_of_proj` supply the
`||x|| <= 1` hypothesis of `norm_sub_sq_le_of_re_inner_ge` with no operator-norm estimate anywhere
(the alternative, lifting a `Bnd` through `bOp`, would have needed a fibrewise decomposition that
Foundations does not have). Second, **the range of `1 (x) |EPR><EPR|` consists of product
vectors** by inspection (`bOp_eprProj_mulVec`), so the auxiliary state of item 1 is read off
directly --- no partial trace, no Schmidt decomposition.

**And the graph was wrong.** Assembling item 1 made it visible that its real input --- the
self-consistency of `W~^e(u-tilde)` at a *uniform* `u-tilde` --- is nowhere in the blueprint. It is
the paper's second item of `lem:qld-construct-the-paulis`, and the blueprint's paraphrase of
`lem:qld-exact-paulis` kept only the first. Added as `lem:qld-pauli-selfcons` and recorded in
`reports/qld-stage5-blueprint-repairs.md`. It is the substantial piece of stage 5 that remains, and
it is what `thm:qld` is now waiting on: item 2 of `lem:qld-swap` and the assembly both run through
it.

### PR L, first piece: the exact steps of `lem:qld-pauli-selfcons` (2026-09-22)

`MIPRE/Background/QLD/AncTransport.lean` (fast regime). The node added in the previous PR is the
blocker for everything left in stage 5, so this starts on it. Its chain splits cleanly: the
`approx_0` displays are identities and the `approx_delta` ones are estimates. All the identities
are now in (`syn_mul_syn` landed with the previous PR; `stateVec_ancSyn` and `sum_ancSyn_mulVec`
here).

**The one that looked blocked.** `eq:qld-pulling-3a` moves a generalized Pauli between the two
ancilla halves, exactly. Foundations has that for the bare entangled state, but the chain runs on
a `SimulPair`'s padded state `Phi`, and `SimulPair` does not say `Phi` *is* an expanded state ---
only `Phi_reduced`, that it reproduces expectations. A vector identity looked out of reach, which
would have meant strengthening the merged stage-4 interface. It is not out of reach: the identity
is the vanishing of `xSqNorm Phi A B`, and a squared norm is an expectation, so the existing
`SimulPair.xSqNorm_aOp` carries it. Worth remembering for the rest of the chain: an exact statement
about `Phi` expressible as a vanishing squared norm is reachable through `Phi_reduced`; one that is
not, is not. Every `approx_0` step here is of the first kind, so no interface change is needed.

**Sizing what is left.** The estimates are `eq:qld-pulling-1`, `-3`, `-7` and `-10` through `-12`,
then the passage through `fact:agreement`, `fact:data-processing` and `lem:qld-povm-to-obs`. Their
tools are in place (`fact:add-a-proj` in `MIPRE/Foundations/Commutation.lean`, item 2 of
`lem:qld-helper`). On stage 4's evidence that is about three pull requests, after which
`lem:qld-swap` item 2 and the `thm:qld` assembly follow.

### PR L, second piece: what the estimates of `lem:qld-pauli-selfcons` consume (2026-09-22)

`MIPRE/Background/QLD/Pulling.lean` (fast regime). With the identities closed, this takes the two
inputs the `approx_delta` displays need and puts them in the form the chain asks for.

**The helper, re-indexed.** Displays `eq:qld-pulling-7` and `eq:qld-pulling-11` are item 2 of
`lem:qld-helper`, but the helper is stated at an outcome `a` in `F_q` --- what the expansion stage
produces --- and the chain sums over the *polynomial* outcomes `g`, because the label
`coded(g) . u-tilde` it carries depends on `g` and not on `g(u)`. The two sums are **equal**, not
merely comparable: within a fibre of the evaluation the pair measurement's outcomes are orthogonal
projectors, so every cross term of the squared norm vanishes (`snorm_sq_sum_orthogonal`), and the
fibres partition the outcomes. So `SimulPair.sum_snorm_sq_polyMarg_one_sub_le` holds at the
helper's own constant, with nothing lost.

**Schwartz--Zippel again.** `eq:qld-pulling-12` is `sum_uniform_agree_mass_le`: restricting a
weighted sum to the tuples where two distinct outcome polynomials agree at the sampled point costs
`md/q`. A small thing worth noting --- the linter caught it --- is that no `1 <= d` hypothesis is
needed here, unlike at `prob_agree_ldEnc_le_of_not_multilinear`, because both polynomials carry the
same individual-degree bound and so the Schwartz--Zippel hypothesis is already met. The version in
`NonMultilinear.lean` needs it only because one side there is an interpolant, of individual degree
at most one, which has to be brought under the bound `d`.

**A tactic note, since it cost a cycle.** `Finset.sum_fiberwise` will not close
`sum_a sum_{g in fibre} f(g, a) = sum_g f(g, ev g)` directly: the summand on the left mentions `a`
and only agrees with the right *inside* the fibre. Rewriting the right-hand side with
`<- sum_fiberwise` first and then matching pointwise with the membership hypothesis is the pattern
that works, and it is the same one `Multilinear.lean` uses. Applied the wrong way round it does not
fail fast --- it spends the whole heartbeat budget on unification and reports a `whnf` timeout,
which reads like a performance problem and is not one.

What is left of the node: `eq:qld-pulling-1` and `-3` (inserting and moving a near-identity),
`eq:qld-pulling-10`, the assembly, and the final passage through `fact:agreement`,
`fact:data-processing` and `lem:qld-povm-to-obs`. The remaining tool is `fact:add-a-proj`, in
`MIPRE/Foundations/Commutation.lean`.

### PR L, third piece: the near-identity of `eq:qld-pulling-1` (2026-09-22)

`MIPRE/Background/QLD/Pulling.lean`, continued (fast regime). The display right-multiplies by
`sum_g (S-hat^W_g)_{A A'} (x) (M-hat^{(Point,W),u}_{g(u)})_{B A''}`, which item 1 of
`lem:qld-helper` says is near the identity. The step is cheap for a reason worth naming: that
operator is a **projection** (`agreeOp_mul_self`). The pair measurement's outcomes are orthogonal,
so the cross terms of the square vanish, and the opposite party's factors are projectors. So its
deficit from the identity is *linear* in it --- `snorm_sq_one_sub_agreeOp` gives exactly
`1 - agreement`, with no Cauchy--Schwarz --- and a contraction on the left cannot amplify it
(`snorm_sub_mul_agreeOp_le`).

The package is stated for any family of projectors on the second party, not just a measurement:
the cross-term cancellation needs only the *first* party's family to be projective. That is what
lets it apply here, where the second-party factors are indexed by `g` through `g(u)` and so are
not a measurement in `g`.

Left on the node after this: `eq:qld-pulling-3`, `eq:qld-pulling-10`, the assembly, and the final
passage through `fact:agreement`, `fact:data-processing` and `lem:qld-povm-to-obs`.

### PR L, fourth piece: the two ends of `eq:qld-pulling-10` (2026-09-22)

`MIPRE/Background/QLD/Pulling.lean`, continued. That display is argued by bounding the magnitude of
a difference, and its justification runs from `fact:add-a-proj` at the top to the helper at the
bottom. Both ends are now in.

The top is `sum_kron_le_one`: a family of projectors on one factor tensored with a projective
measurement on another sums to at most the identity, the complement `sum_x (1 - B_x) (x) T_x` being
a sum of positive semidefinite terms. Against a positive operator on the other party that discards
the index the sandwich runs over (`sum_bornProb_kron_le`), which is one line given
`bornProb_sum_right` and `bornProb_mono_right`.

The bottom is `eq:qld-pulling-14`, `SimulPair.sum_bornProb_polyMarg_one_sub_le`: the complement of
the helper's agreement, read by polynomial outcome, is at most `delta_S`. It is the agreement
itself subtracted from one, the marginal's outcomes summing to the identity.

Left on the node: `eq:qld-pulling-3`; the middle of `-10` (the expansion of the squared norm and
the `O(sqrt eps)` substitution at `eq:qld-pulling-13`); the assembly; and the final passage through
`fact:agreement`, `fact:data-processing` and `lem:qld-povm-to-obs`.

### PR L, fifth piece: the middle of `eq:qld-pulling-10`, `eq:qld-pulling-3`, and the final passage (2026-09-22)

`MIPRE/Background/QLD/Pulling.lean`, continued. Three sections, and after them the only thing the
node is missing is the assembly of the chain itself.

**The middle of `eq:qld-pulling-10` (`section Substitute`).** Between the two ends already in
place, the estimate expands a squared norm over the orthogonal outcomes of a projective family
into a sum of sandwiches (`snorm_sq_sum_proj_sandwich`), drops the constraint on the outcomes
(`sum_qform_sandwich_le_of_subset`, from the nonnegativity `qform_sandwich_nonneg`), and then
*moves* the sandwiched measurement from one party to the other. That last step is
`abs_sum_qform_swap_le`, and it is the only Cauchy--Schwarz in the whole chain: the difference of
the two sandwiches is written as two terms each carrying the deviation `X - Y` on one side, and
each is bounded by `sqrt(eps)` against a mass at most one. `snorm_sq_proj_mul_eq_qform` is how
that mass is read off a sandwich.

The `X` side needs no second half: `X S X = X S` there, because `X` is a projection commuting with
what it sandwiches. The summed Cauchy--Schwarz is `Introspection.abs_sum_qform_mul_le`, already in
Foundations for the introspection induction and the reason this file now imports
`MIPRE/Foundations/Introspection/ValueStability.lean`. It wants the self-adjoint factor written
first, which the deviation is and the half-sandwich is not; `qform_conjTranspose` turns the first
term around so that both fit.

**`eq:qld-pulling-3` (`section Insert`).** The expansion leaves one party's projector beside the
*other* party's point measurement, and the chain inserts a copy of that measurement on the first
party's side. Two things make the step cost the self-consistency of `lem:qld-win` and no more. The
deficit of the insertion is the cross-party deviation itself (`snorm_one_sub_aOp_mul_bOp_le`):
`(1 - A) B = B (B - A)` because `B` is a projection and the parties commute, and a projection in
front costs nothing. And the projective family in front is indexed *through a map* to the
measurement's own outcomes, so only the fibres of that map are summed over
(`sum_snorm_sq_proj_comp_le`). Without the fibres this would be false --- the index of the family
is far larger than the outcome set, and summing one deviation once per index would multiply the
bound by the size of a fibre. `sum_snorm_sq_insert_le` is the display.

**The final passage (`section Coarse`).** This turned out to be already available. Foundations has
`sum_xSqNorm_map_le` --- coarse-graining two projective measurements the same way costs nothing,
which is exactly `fact:agreement`, `fact:data-processing` and `fact:agreement` again --- stated on
bundled POVMs, because that is what the expansion stage of the introspection tree speaks. The
chain speaks `IsPVM`. `povmOfIsPVM` and `sum_xSqNorm_fibre_le` bridge the two, and the passage is
then one `simpa`. Worth recording as a small lesson: before writing an estimate of this shape,
look for it in `Foundations/Sandwich.lean` and `Foundations/Expanded.lean` first.

Left on the node: the assembly of the chain itself, which is the index bookkeeping of the eleven
displays plus `lem:qld-povm-to-obs` at the end. Every step it assembles is now formalized.

### PR M: the exact steps of `lem:qld-swap` item 2 (2026-09-22)

`MIPRE/Background/QLD/SwapMeasure.lean`, new. Item 2 of `lem:qld-swap` is the longer half of the
swap lemma and none of it was formalized. Three of its displays are now, and they are the ones
that are identities or that reuse a packaging already in the library.

**`eq:qld-unitary-6`: conjugating the measurement, not the observable.** `SwapUnitary.lean`
carries the observable version, `V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. The measurement
version needs one thing the observable version did not, and it is worth having on its own. The
twisted commutation relation says conjugation by the ancilla factor multiplies each Weyl operator
by a character; on the *spectral projectors* that is a **shift**, because a projector is the
Fourier average of the family against a character and two characters compose by adding their
labels (`conj_proj_of_sign`). A syndrome projector is a sum of spectral projectors over a level
set of the pairing with the probe, so its outcome moves by the shift's own pairing
(`conj_syn_of_sign`), the level sets being carried onto each other by adding the shift --- an
involution of the index group in characteristic two.

Then the cancellation is arithmetic. In `M~^{W,u}_a` the outcome carried at the pair outcome `p`
is `cd(pi p) . u + a` and the shift conjugation applies is `cd(pi p)`, whose pairing with `u` is
that same `cd(pi p) . u`; so every factor of the conjugated sum is the same syndrome projector,
the pair outcome is gone, and the measurement in front sums to the identity
(`swapU_conj_mTilde`, and `swapU_conj_mTilde_X` / `_Z` at the two bases). This is the paper's
relabelling `h' = h + coded(g_W)`, the passage its `\cnote` records as repaired: the repair kept
`coded(g_W) . ind_m(u)` rather than the false `g_W(u)`, and what makes the relabelling exact here
is that the shift and the outcome are written with the same `cd(pi p) . u` by construction, so
nothing has to be identified at all.

At the interface this is `SimulPair.swapU_conj_mTildeAt`, with `SimulPair.swapA` Alice's swap
unitary. `PolyPair.proj .X` is the first projection and `weylOf .X` is `wX`, and likewise for `Z`,
so the two bases are the two cases of `Bas` and nothing else is needed.

**`eq:qld-unitary-7`: the expansion.** `sum_snorm_sq_sub_eq_two_sub`. The two families compared in
the endgame act on the *same* party, so `one_sub_sum_bornProb_eq` --- the bipartite version, which
the rest of the appendix uses --- does not apply. The same three-term expansion does, with both
diagonal sums exactly one because both families are projective, and with no real part left in the
statement: `qform` is already the real part, and the flipped cross term has the same one.

**`eq:qld-unitary-8`: the same Schwartz--Zippel.** The endgame's one estimate turned out to be
`eq:qld-pulling-12` again, in the packaging already written for it. The only mismatch was
bookkeeping: there the index set excludes the coinciding polynomials, here the index is a *pair*
of Pauli outcomes and the diagonal is excluded by the weight. So `sum_uniform_agree_mass_le` now
asks for the two polynomials to be distinct only where the weight is nonzero --- a weakening, so
nothing that used it changes --- and `sum_uniform_agree_bornProb_le` is the display.

Left on item 2: `eq:qld-unitary-5`, the triangle chain through `lem:qld-win` and
`lem:qld-exact-paulis`; the transport of the estimate from the product state back to the padded
state across item 1; and the assembly. Left on `lem:qld-pauli-selfcons`: its assembly, unchanged.

**A note on what `eq:qld-unitary-5` still needs.** Looking for the triangle chain's engine turned
up `agreeSum_triangle` in `MIPRE/Foundations/POVMMix.lean`: the POVM form of the paper's
`fact:triangle-for-simeq` item 1, formalized earlier in the campaign for
`lem:qld-global-success`, with `11 delta` in place of the paper's `9 delta` (the padding into a
four-dimensional auxiliary space that buys the `9` is what the Lean proof does without, and the
blueprint records the difference). So `eq:qld-unitary-5` is not a new estimate: what is left of it
is stating the three consistencies --- `eq:qld-unitary-2`, `-3`, `-4` --- as `agreeSum` statements
at this interface. That is the second time in two pull requests that an appendix estimate turned
out to be already in Foundations under another name; the habit is now worth the two minutes it
costs.

### PR N: the triangle chain's adapter, and a duplicate of my own making (2026-09-22)

Two things.

**`inconsistency_triangle`.** `eq:qld-unitary-5`'s estimate is `agreeSum_triangle`, which speaks of
the *agreement* of two POVM families; every consistency in the QLD interface --- `consA`, `consB`,
`inconsistency_mTilde_le` --- is stated as an *inconsistency* instead. The two are the same number
(`sum_bornProb_diag_eq`), so the adapter is five lines, and with it the display is the estimate
applied to `eq:qld-unitary-2`, `-3` and `-4`. One Lean detail worth remembering: passing the
constant as `(delta := delta)` was necessary, because `rw` closes its goal by `rfl` and would
otherwise unify the triangle's implicit constant with the first hypothesis's left-hand side.

**A duplicate, removed.** `povmOfIsPVM`, which PR #158 added to `Pulling.lean` to bridge `IsPVM` to
`POVM`, already existed as `IsPVM.toPOVM` in `MIPRE/Foundations/Commutation.lean` --- and the QLD
tree was already using it, in `inconsistency_mTilde_le` two files away. Removed, and
`sum_xSqNorm_fibre_le` now goes through the existing one. This is the third time in three pull
requests that something in this appendix was already in the library; the first two were finds, this
one was a miss. The lesson is the same and it is now cheap to apply: `grep` the declaration name's
shape before writing it.

Left after this: putting `eq:qld-unitary-5`'s three consistencies on one cut (`consA` and `consB`
are read along the padded state's cut, `inconsistency_mTilde_le` along the regrouped one, and
`bornProb_regroupVec` carries a Born probability between them); the transport from the product
state back to the padded state; item 2's assembly; and the pulling chain's assembly.

### PR N, continued: `eq:qld-unitary-5` at the interface, and the endgame's transport (2026-09-22)

Three more pieces, all in `SwapMeasure.lean`.

**The cut.** The one real obstacle to `eq:qld-unitary-5` was that its three legs are not read along
the same cut. `M~^{W,u}` wants the ancilla half with the first party, which is the regrouped cut
`mVec`; the strategy's own point and Pauli measurements are local to the unpadded registers and
are stated along the padded state's cut. `inconsistency_regroupVec` settles it: for operators that
ignore the register the regrouping moves --- which the strategy's measurements do, being extended
by the identity there --- the two readings are the *same number*, the regrouping being a
reindexing of the whole space and `bornProb_regroupVec` the one entry computation. The proof is
four lines and the statement is the general one, not an instance.

**The display.** `SimulPair.inconsistency_mTilde_pauli_le` is `eq:qld-unitary-5`: the exact Pauli
measurement agrees with the strategy's `(Pauli, W)` measurement read at the sampled point
(`pauliAtPOVM`, which is `rdPauli` --- the paper's `g_h(u)` --- coarse-graining the Pauli answer),
to within eleven times whatever bounds the three legs. Its own leg is item 1 of
`lem:qld-exact-paulis`; the two middle legs are the game's point--point and point--Pauli
consistencies and are hypotheses, in the same way `exists_auxVec_close` takes item 1's
near-invariances. That is the honest shape: those two are `lem:qld-win`'s to supply, and supplying
them is a separate piece of work.

**The transport.** `abs_qform_sub_qform_le`: moving an expectation from the product state to the
padded one costs twice the operator's bound times the distance between them, by splitting the
difference into two terms with the deviation on one side each. Item 1 bounds the *squared*
distance, so this is exactly where the fourth root in `delta_qld` comes from.

What item 2 still needs: the two game consistencies that `inconsistency_mTilde_pauli_le` assumes,
and the assembly --- threading `eq:qld-unitary-7` through `-9` and this transport into the
statement about `V M^{(Pauli,W)}_h V^dagger`. What `lem:qld-pauli-selfcons` still needs is
unchanged: the assembly of its chain.

**And the padding transport.** `SimulPair.bornProb_padded` and `inconsistency_padded`: a
consistency between the strategy's *own* measurements reads the same on the padded state as on the
strategy's own state, both operators being extended by the identity on the expansion's ancillas and
on the padding. The padded state's reduction carries them to the expanded state and
`bornProb_expVec_kron` carries them down to `psi`, the entangled pair contributing its norm and
nothing else. That is what lets `inconsistency_mTilde_pauli_le'` ask for its two middle legs in the
form `agree_subtest_le` leaves them --- on `psi`, with nothing about the expansion or the padding in
sight. What remains of those two legs is instantiating `agree_subtest_le` at the edges `adj_self'`
and `adj_point_pauli` with the readings `rdVal` and `rdPauli`, averaging over contents into points
with `sum_content_pt`, and halving the cross-deviation into an inconsistency (exact for projective
families).

### PR N, third piece: the two middle legs, discharged (2026-09-22)

`eq:qld-unitary-5`'s two middle legs are no longer hypotheses. They are items 1 and 3 of
`lem:qld-win` --- `item_consistency` at the point type and `item_pauli_consistency` --- both of
which were already in `Win.lean`, and three steps carry each into the form the triangle wants.

* The point question a content asks is the point the content carries (`Content.question` at
  `.point W` is `.point W (c.pt W)`, by `rfl`), so the average over contents of a function of that
  point is the uniform average over points: `sum_content_pt`, also already in.
* For *projective* families a cross-party deviation is exactly twice the inconsistency
  (`inconsistency_eq_half_xPovmDist`). Only `≤` holds for general POVMs
  (`xSqNorm_sum_le_two_mul`); what makes it an equality is that both families' masses are exactly
  one, which `one_sub_sum_bornProb_eq` already knew.

`inconsistency_pt_pt_le` and `inconsistency_pt_pauli_le` are the two legs at `86 ε`, which is
`agree_subtest_le`'s `172 ε` halved, and `inconsistency_mTilde_pauli_le_of_win` is
`eq:qld-unitary-5` from the game's soundness and item 1 of `lem:qld-exact-paulis` alone.

Two Lean notes. `linarith` compares atoms syntactically, so a hypothesis whose Born probability is
written unfolded and a goal whose is not will not close: `simp only [bornProb]` on the hypothesis
was the fix, twice. And a `rw` with the measurement arguments left as `_` unified them against the
*proof terms* supplied for projectivity, producing `POVM.map _ (MA _)` where the goal had
`ptAtPOVM MA W u`; naming the two families in `have`s first fixed it.

That is item 1 of the four in `planning/formalization-plan.md`'s QLD list, done. Left: the assembly
of item 2, the assembly of `lem:qld-pauli-selfcons`'s chain, and `thm:qld`.

### PR O: the endgame of item 2, in bricks (2026-09-22)

`MIPRE/Background/QLD/SwapEndgame.lean`, new. Item 1 leaves a product state
`|aux> (x) |EPR_q>^M`, and what the endgame does to it turns out to be elementary once said
plainly.

* An operator on the entangled pair acts on the second factor and leaves the first
  (`bOp_mulVec_auxVec`, one entry computation), so two operators that agree on the pair agree on
  the whole product (`mulVec_auxVec_congr`). That is `eq:qld-unitary-7`'s last line, where a
  generalized Pauli's spectral projector moves from one half of the pair to the other: the
  projectors are symmetric, being real Fourier averages of a symmetric family, so the existing
  `stateVec_epr_proj` moves them across the pair and `mulVec_auxVec_proj` carries that to the
  product state. `mulVec_auxVec_syn` is the same for the syndrome projectors.
* `sum_snorm_sq_sub_le_of_agree` is the display's first two lines read as a bound: everything after
  them is a lower bound on one number, the agreement, and the deviation the lemma asks about is
  twice its deficit.
* `sum_uniform_bornProb_fibre_le` is `eq:qld-unitary-8` in the form the chain consumes. Reading the
  two families at the *value* of the encoding at the sampled point rather than at the full outcome
  can only add agreeing pairs, and the ones it adds are the distinct pairs whose encodings collide
  there, which `sum_uniform_agree_bornProb_le` already bounds. The work is the regrouping: the
  agreeing pairs at `u`, fibred by the common value, are exactly the products of the fibres, and
  the diagonal of that is the fine agreement.

With this, every step of item 2's endgame is formalized. What is left of item 2 is the threading:
matching the registers of the conjugated Pauli measurement with item 1's, which is where
`exists_auxVec_close`'s cut (the two parties' non-ancilla registers as one index, their two ancilla
halves adjacent) has to be reconciled with the measurement's. That is bookkeeping, and it is the
only thing between here and the lemma.

**And a four-factor regrouping --- which is _not_ item 1's cut, and finding that out is the point.**
`endEquiv` moves both ancilla factors of a two-party product out of the party grouping and puts
them together; `qform_endVec` carries an expectation between the readings, by the same route
`regroupEquiv` and `bornProb_regroupVec` take. It was written to be item 1's cut. It is not, and
checking the claim before building on it turned up the real obstacle to item 2's threading.

`exists_auxVec_close` concludes about `|EPR>_{A'' B''}` --- one half of *each* party's local pair;
the paper's expanded state is `|psi>_{AB} (x) |EPR>_{A'A''} (x) |EPR>_{B'B''}`, and `V_A` acts on
`A A' A''`, `V_B` on `B B' B''`. The padded state of this formalization carries only the pair
`A' A''`, read along the cut `A A' | B A''`, with no `B' B''` in it at all. That was deliberate:
`lem:qld-simultaneous` and `lem:qld-helper` each use one orientation at a time, and
`reports/qld-stage5-blueprint-repairs.md` already records that the second pair was not needed for
`lem:qld-exact-paulis`'s item 1. Item 2's threading is the first consumer that does need it.

So the standing claim that "what remains is index bookkeeping with no missing mathematics" was
right for `lem:qld-pauli-selfcons`'s chain and **wrong for item 2's threading**: before the
endgame's steps can be pointed at one vector, the interface has to carry both entangled pairs, or
there has to be an argument that one suffices here as it did there. That is an interface change,
and it is the next real decision of the campaign. `endEquiv` and `qform_endVec` keep their place ---
whatever the representation, the regrouping they do is the shape the threading needs --- but they do
not by themselves reach item 1's conclusion.

**And the chain's probe.** `lem:qld-pauli-selfcons` runs at a *uniform* `u-tilde` in `F_q^M`, which
is not a point's low-degree encoding --- the encodings are a tiny subset of `F_q^M`, and confusing
the two is the omission that created the node. `MIPRE/Background/QLD/ChainProbe.lean` keeps them
apart by name: `SimulPair.mTildeAnc` is the exact Pauli measurement at an arbitrary probe (the
generic `mTilde` already took the probe as an argument, so this is a naming, not a construction),
`isPVM_mTildeAnc` says it is projective at every probe, `mTildeAt_eq_mTildeAnc` is the one place it
meets `lem:qld-exact-paulis`'s, and `swapU_conj_mTildeAnc` is `eq:qld-unitary-6` there --- the
conjugation's cancellation never used the probe's shape, only that the outcome's shift and the
conjugation's are written with the same pairing.

That is the first brick of the chain assembly: every display of the chain has to be available at
this probe, and until now none of them were stateable there.

**And the missing edge, made explicit.** Item 1 of `lem:qld-swap` asks for a near-invariance of the
state under the Weyl twirl on its two ancilla halves; what `lem:qld-pauli-selfcons` supplies is an
agreement of the two parties' exact Pauli observables averaged over a *uniform* probe. The twirl is
by definition that average (`twirl w = E_u w(u) (x) w(u)`), so the two are one rewriting apart:
`qform_bOp_twirl`. Worth recording that the edge is this short. The node was separated out from
`lem:qld-exact-paulis` because the latter's `leanok` marks had to stay honest, and the worry was
that the separation would cost a translation layer between them. It costs one line.

### The correction to the correction (2026-09-22)

The note above said item 2's threading was blocked on the second entangled pair while
`lem:qld-pauli-selfcons`'s chain was unblocked bookkeeping. The second half is wrong, and checking
it before starting the chain assembly is what turned it up.

The chain's conclusion is a cross-party closeness of the two parties' *exact Pauli observables*:
`(W~^e(u-tilde))_{A A' A''} approx (W~^e(u-tilde))_{B B' B''}`. Each side needs its party's whole
triple, so six registers at once; `Phi` has four. And the two readings pull opposite ways ---
`mTildeAt` lives on the regrouping that gives Alice both ancilla factors, a Bob-side `mTilde` would
need the one that gives Bob both, and no bipartite cut of a four-factor state supports both. The
conclusion cannot be stated in the present representation. That there is no Bob-side `mTilde` in
the tree is the same fact from the other side.

What kept the one-pair economy honest until now: every earlier consumer compares an exact Pauli
object on one party with a *point measurement* on the other, and a point measurement carries no
ancilla. `inconsistency_mTilde_le` is `mTildeAt` against `(ptAtPOVM MB W u).aOp` on `dB x EB`. Two
exact Pauli objects is the first comparison the economy cannot serve.

**So there is one blocker with two consumers**, and it is now the next piece of work: `SimulPair`
carrying both pairs. `Phi`'s type changes and every statement reading `Phi` or `mVec` is re-derived
--- `Helper`, `Multilinear`, `MTilde`, `AncTransport`, `Pulling`, `SwapMeasure`, `ChainProbe`. The
estimates are untouched, being about operators and states in the abstract; this is a retyping and a
re-derivation of the transports. Neither assembly should be started before it.

### PR P: the two-pairs change is additive (2026-09-22)

The scope written an hour ago said `SimulPair.Phi` had to be retyped to carry the paper's second
entangled pair, at about 94 mentions of `Phi` and 19 of `mVec` across 135 declarations. That was
wrong, and `MIPRE/Background/QLD/TwoPairs.lean` is the demonstration: it builds against the tree as
it stands.

`SimulPair`'s `EA` and `EB` are **arbitrary types**, constrained only by `Fintype` and
`DecidableEq`. The second pair lives inside them --- `EA = Anc x EA'`, `EB = Anc x EB'` --- so
`Phi` already is a state on the paper's six registers plus padding, and `Phi_reduced` is satisfiable
unchanged, speaking as it does of `aOp X` and `aOp Y`, which put the identity on all of `EA` and
`EB` whatever those are.

With each pair split across the party cut the way `hatVec` already splits the first, Alice's side
is `A A'` and `B'' EA'`, Bob's is `B A''` and `B' EB'`. Alice's `M~` wants `A A' A''` and Bob's
wants `B B' B''`; each needs one register from the far side, and they are *different* registers.
So one permutation serves both: `pairSwapEquiv` sends each party's far half home, after which
Alice holds `A A' A''`, Bob holds `B B' B''`, and both exact Pauli objects are expressible on one
bipartite cut. `pairSwapVec`, `pairSwapVec_unit`, `reindex_pairSwapEquiv` and `qform_pairSwapVec`
come with it, in the pattern `regroupEquiv` and `bornProb_regroupVec` set.

The lesson is worth keeping, because it is about reading an interface rather than about this proof:
**when a structure carries an opaque type parameter, check what can be put into it before changing
the fields around it.** The first estimate read `EA` and `EB` as fixed padding. They are free.

Left: a structure beside `SimulPair` recording the shape and the mirror `Phi_reduced`; Bob's
`mTilde` from `SB`; then the two assemblies.

### PR Q: the mirror is a second `SimulPair` (2026-09-22)

The scope written an hour before this one was wrong too, in the other direction, and the reason is
worth recording because it is the same mistake twice: **both wrong turns came from reasoning about
the Lean types instead of reading the paper's register assignments.**

Putting the second pair inside `EA` and `EB` typechecks and needs nothing retyped. It also lets
`SA : POVM (PolyPair) ((dA x Anc) x EA)` act on `B''`, which is Bob's. The paper's `S-hat` does
not: `lem:qld-4-7` gives it on `H (x) (C^q)^{(x) n}` for each player's own space, and
`qld-separating.tex` says in as many words that `M-tilde` then acts on `A A' A''` (resp.
`B B' B''`). A measurement free to touch `B''` makes `M-tilde` and the swap unitary non-local, and
then `lem:qld-pauli-selfcons` cannot be **stated**, its two sides not lying on opposite sides of
any cut.

The design that works appends the pair instead. A `SimulPair` stays exactly as stages 4a--4c
produce it, carrying only the pair its own cut splits; the other pair is tensored on with
`expVec _ epr`, one half to each party. Party registers then read `((X x Anc) x E) x Anc`, with the
appended half outermost --- which is where `mTilde` writes its Pauli register, so `mTildeAnc` lands
on Alice's physical register `A A' Ea A''` with nothing to reindex.

And the second cut is not a new kind of data. `sec:expanding` partitions the six registers two ways
and says every bipartite relation holds for both; `lem:qld-4-7` gives `S-hat` on `A A'` *and* on
`B B'`. So **the mirror of a `SimulPair` is a `SimulPair`**, at the swapped strategy with the
players exchanged. `MirrorSimul` in `MIPRE/Background/QLD/Mirror.lean` carries the two readings and
`hmirror`, which says the two appendings give one state; `toFirst` and `toSecond` are the views.
Bob's `mTildeAnc`, `swapA`, projectivity and `eq:qld-unitary-6` are then instantiations, with no
mirror lemma proved.

A claim that went out and had to be withdrawn: PR #163's description said Bob's `mTilde` could come
from `SimulPair.SB`. It cannot --- `SB` is typed on `(dB x Anc) x EB` with that `Anc` being `A''`,
so it sits on `B A''`, the second party of the *first* cut, not on `B B'`. The description was
corrected before merge. Checking the premise before building on it has now caught four wrong claims
in this campaign; the cost of the check has been minutes each time.

Left: the two assemblies, now that both are expressible, and then `thm:qld` --- where the paper's
"symmetric equivalents" remark has to be made good by running stage 4 on the second cut as well.

### PR R: the pulling chain's two ends (2026-09-22)

`MIPRE/Background/QLD/Chain.lean` is the chain's arithmetic frame, and it contains no estimate: it
is the index algebra that the eleven displays are bookkeeping for.

**The near end.** `mTildeAnc_eq_sum_chainIdx` is `eq:qld-pulling-2` and `eq:qld-pulling-2b`. The
definition `eq:tilde_M` sums over pair outcomes `g` with a syndrome projector attached; the chain
sums over pairs `(g, h)` cut out by `(cd(g) - h) . u-tilde = a`. Same sum: the syndrome projector
is the fibre of the spectral family over that pairing, and in characteristic two the shift the
definition carries is the sum the chain's label is written with.

**The far end, and why the lemma holds at all.** `endOp` is display `eq:qld-pulling-12`. Both
parties' derivations end there, and the two exact Pauli measurements are close to *each other* ---
rather than each close to something --- only because that display is symmetric in the two pairs.
That is not apparent: its index set is cut out by a coupling `g - g_h = g' - g_h'`, symmetric on
its face, together with a pairing condition read off the *first* pair alone.

`chainLabel_eq_of_coupled` is the reason, and the proof is one line: evaluate the coupling at a
cube point, where the encoding of a cube datum is that datum. So coupled pairs carry the same
label, the condition may be read off either pair, and the index set is invariant under exchanging
them (`swap_mem_coupledIdx`). `endOpMirror_apply` is then the symmetry of the display itself.

**And closing.** `sum_xSqNorm_le_of_endOp`: given the two chains, `sum_snorm_sq_triangle'` (already
in Foundations) gives `eq:qld-pulling-cons` at twice the cost, the factor the paper absorbs into
`delta_S`.

What is left of `lem:qld-pauli-selfcons` is the eight `approx` steps between those two ends. Every
estimate they consume is in the tree --- the blueprint's comment on the lemma lists them one by one
--- and what is missing is the four-index bookkeeping that threads them. That is now the only thing
missing, and it is bounded work with no mathematics left in it.

### PR S: the chain's first estimate (2026-09-22)

`eq:qld-pulling-1` right-multiplies the exact Pauli measurement by the helper's near-identity.
`SimulPair.sum_uniform_snorm_sq_nearId_le` is that display, at item 1 of `lem:qld-helper`'s own
constant, and two things make it cost that and no more.

The insertion's deficit is *exactly* the near-identity's. A naive termwise bound would give
`sum_a snorm(1 - N)^2 = q * snorm(1 - N)^2` and lose a factor of the field size; what saves it is
that the measurement's outcomes are orthogonal, so `snorm_sq_sum_orthogonal` at the complete family
collapses the sum. That is `sum_snorm_sq_sub_mul`, and it is worth having separately: the same
shape recurs at `eq:qld-pulling-7` and `eq:qld-pulling-11`.

The near-identity lives on `Phi`'s own cut, where `snorm_sq_one_sub_agreeOp` turns its deficit into
the helper's Born probability; `mTilde` lives on the cut that has `A''` with Alice.
`snorm_comp_equiv` moves between them --- a state-norm is carried by *any* reindexing of the whole
space, `qform_comp_equiv` being the statement for the quadratic form. That generalises the
`prodComm` case written for the endpoint's symmetry, and it is the lemma that lets each step of the
chain be read along whichever of the paper's three groupings it is local in, instead of forcing one
grouping on all of them. Having it settles a question that looked like an obstacle: the chain runs
across three different cuts, and no one of them makes every step local.

Seven `approx` steps left.

### PR T: the chain's expansion, `eq:qld-pulling-2b` (2026-09-22)

`SimulPair.aOp_mTildeAnc_mul_nearId` is the product the second and third displays carry out. It is
an identity, not an estimate, and it runs in three moves.

The near-identity expands because the hatted point measurement *is* the convolution
`sum_{a'} M^{(Point,W),u}_{a'} (x) tau^{W,u}_{c-a'}` by construction --- that is
`sum_kron_syn_eq_hatMats`, already in the tree --- and `reindex_regroupEquiv` sends each of its
terms to the cut `mTilde` lives on, which puts `tau^{W,u}` beside Alice and the point measurement
alone on Bob. That is `nearId_eq_sum`.

Multiplying then kills all but one pair outcome (the family is projective) and fuses the two
syndrome projectors into the Weyl outcomes meeting both conditions. That is `syn_mul_syn`, and it
is where the chain's index set first appears: `mTildeAnc_mul_kron`.

Finally the sum over Bob's point outcome collapses. For each Weyl outcome `h` exactly one `a'`
survives --- in characteristic two `h . ind_m(u) = g(u) + a'` determines it --- and that one is
`(g - g_h)(u)`, the paper's. What is left is a sum over `chainIdx` with `chainOp` as its summand,
which is what those two definitions were introduced for in PR R.

Three small general lemmas came out of it and are worth keeping: `kron_sum'` and `sum_kron'` (the
Kronecker product distributes over a sum on either side, at arbitrary registers --- the existing
`kron_sum` is typed to `ExactPauli.lean`'s own registers) and `reindex_sum`.

Six `approx` steps left.

### PR U: the chain's insertion, `eq:qld-pulling-3` (2026-09-22)

The expansion of PR T leaves Bob's point measurement beside each term; this display inserts Alice's
copy of it, spending the point measurements' self-consistency.
`SimulPair.sum_snorm_sq_insert_chain` is that display. The packaging `sum_snorm_sq_insert_le`, in
the tree since PR J, does the work once its hypotheses are supplied, and supplying them is the
whole content.

Both hypotheses are about the chain's terms being a **projective family in the pair `(g, h)`** ---
`isPVM_chainOp`, a marginal of the pair measurement tensored with a Weyl spectral projector.
Projectivity is what makes the outcomes not interfere, so that the squared norm of a sum over one
outcome's fibre is the sum of the squared norms; and it is what makes the fibres of the outcome map
`(g,h) |-> (g - g_h)(u)` be seen once rather than once per index. Without the second, the bound
would be multiplied by the size of a fibre.

Two small gaps in the toolkit turned up and are filled. `isPVM_proj` bundles three facts Foundations
had only separately (`proj_conjTranspose`, `proj_mul_proj`, `sum_proj`) into the form `isPVM_kron`
consumes. And `snorm_sq_sum_orthogonal'` is the varying-tail version of `snorm_sq_sum_orthogonal`:
the existing one fixes a single `R` for all the blocks, while the chain's tail carries each term's
own point measurement. Orthogonality kills the cross terms either way.

Summing the display over the measurement outcome `a` recovers the whole index set --- the
`chainIdx v a` are the fibres of the label map --- which is `Finset.sum_fiberwise`.

Five `approx` steps left.

### PR V: the chain's two transports, `eq:qld-pulling-3a` and `-4` (2026-09-22)

Both are `approx_0` steps: identities on the state, not estimates.

`SimulPair.stateVec_ancProj` moves a single Weyl projector from `A'` to `A''` at no cost --- the
two halves of the pair are maximally entangled and the projectors are symmetric. `sum_ancProj_mulVec`
is the consequence the chain uses: summing the matched pairs of them, one on each party, leaves the
state alone, since by the transport each matched pair acts as the projector on one side and those
sum to the identity.

`AncTransport.lean` had both for the *syndrome* projector, which is a fibre of the spectral family.
The chain moves one projector of that family, not a fibre, so it needs the single-projector version.
`stateVec_epr_proj` --- already in Foundations and already used by the endgame --- is the ingredient,
so this is four short lemmas mirroring four that were already there.

The shape of the argument is worth restating, because it is what makes these steps available at all:
`lem:qld-simultaneous` does not say the padded state *is* an expanded state, only that it reproduces
its expectations, so a **vector** identity about it looks out of reach. It is not: the identity to be
proved is the vanishing of a squared norm, and a squared norm is an expectation, so `xSqNorm_aOp`
carries it across with no loss.

Three `approx` steps left: `-3b`, `-5`/`-7`, `-10`/`-11`.

### PR W: `eq:qld-pulling-3b`, a definition unfolded the other way (2026-09-22)

`hatMats_mul_proj` says the chain's factor `(M^{Point,u}_r)_A (x) (tau_h)_{A'}` *is* the hatted
point measurement cut down by the Weyl outcome: `M-hat^u_c` times the projector at `h` keeps exactly
the point outcome `c - g_h(u)`. The reason is that the syndrome factor of the convolution selects
the one term whose shift matches `h`, and `syn_mul_proj` is that fact on its own --- a syndrome
projector meets a single spectral projector in that projector or in nothing, the syndrome being the
fibre of the family over the pairing.

Nine of the chain's eleven displays are now in. Two `approx` steps left: `-5`/`-7` (the helper's
item 2 at polynomial indexing) and `-10`/`-11` (the Cauchy-Schwarz swap and Schwartz-Zippel).

### PR X: the last two displays' common machinery (2026-09-22)

`eq:qld-pulling-5` to `-7` and `-10` to `-12` are the chain's remaining estimates, and they are the
first of its steps to live on all six registers: both compare operators on the **physical cut**,
`A A' A''` against `B B' B''`, which is what `MirrorSimul` was built to make expressible. Displays
`-1` through `-4` all lived on `Phi` or `mVec`, four registers and two indices; these carry a
four-index sum. That is the size difference, and it is why they are last.

They share two things, and both are now in.

`sum_snorm_sq_fiber_sandwich_le` is the outer shape. Each display bounds the summed squared norm of
the chain's terms grouped by the measurement outcome; projectivity turns each group into a sum of
sandwiches (`snorm_sq_sum_proj_sandwich`, in the tree since PR J), the groups are the fibres of the
outcome map, so the double sum is the single sum over the whole index, and what is left to bound
carries no outcome in it at all.

`sum_bornProb_sandwich_drop_le` is the discharge. Each sandwich carries, on the far party, a
projector times a Weyl outcome; summed over that outcome these are at most the identity
(`sum_kron_le_one`), so the whole sum is bounded by the near party's sandwiches alone. That is
`fact:add-a-proj` in the form both displays consume it.

`MirrorSimul.chainP` is the projective family they sum over --- Alice's pair and Weyl outcomes
together, against Bob's Weyl outcome --- with `isPVM_chainP`, which is what both lemmas need of it.

What is left of the two displays is the identification of their terms with that shape, and then the
reduction of what remains to the helper's item 2 and to Schwartz-Zippel.

### PR Y: `eq:qld-pulling-5` to `-9`, the first of the two remaining estimates (2026-09-22)

The first step of the chain to compare operators on all six registers, and the first to run over a
*triple* index: Alice's pair outcome `g`, her Weyl outcome `h`, and Bob's Weyl outcome `h'`.
`sum_snorm_sq_chainP_le` is displays `-5` through `-8`, `sum_uniform_snorm_sq_chainP_le` is `-9`.
The step costs item 2 of `lem:qld-helper` and nothing more.

Three things had to be arranged, and each recurs at `-10`.

*The tail.* `chainW` is Alice's gap `Id - M-hat^u_{g(u)}` against Bob's point measurement at
`(g - g_h + g_h')(u)` --- shifted by **both** Weyl outcomes, which is why the index is a triple.
`chainW_sandwich` is where it meets `sum_snorm_sq_fiber_sandwich_le`: conjugating the chain's
projector by the tail splits across the cut, each party's factor local, so one rewrite turns the
shape's quadratic form into a Born probability.

*Bob discharges.* `bobHat_conj_bobWeyl` says his factor is a projector on `B B'` tensored with a
Weyl outcome on `B''`; `sum_bornProb_chainW_drop_le` sums it away by `sum_bornProb_kron_le`. The
projector **varies with** the Weyl outcome, so the discharge has to be stated with the two indices
coupled --- `sum_bornProb_sandwich_drop_le` from PR X, which fixes the projector across the
dropped index, does not cover it. That was worth finding before writing the proof rather than
after.

*Alice collapses and travels.* `sum_aliceChainOp` sums the Weyl outcome out of her summand, the
spectral projectors being complete, and `sum_aliceChainOp_sandwich` carries that through the
sandwich, her gap operator not depending on the Weyl index. What is left is on `A A'` alone, and
`bornProb_physVec_aOp` carries it back to `Phi`, where
`SimulPair.sum_snorm_sq_polyMarg_one_sub_le` bounds it.

The transport is stated twice. `bornProb_physVec_aOp_kron` keeps the identity written as a
fourfold tensor product and only `bornProb_physVec_aOp` collapses it, because the intermediate
`mVec` carries Bob's padding under `toFirst`'s name for it and `rw` cannot abstract inside that
application --- the motive is not type-correct at `implicit` transparency. The same spelling
problem is why Alice's objects here (`aliceChainOp`, `aliceHat`) are named in her own spelling
rather than reached through `toFirst`. This is the third time `toFirst.EA` versus `M.Ea` has cost
a detour; the rule that has worked every time is to give a physical-cut object its own name and
never to rewrite under a `toFirst` projection.

Ten of the chain's eleven displays are in. One estimate left: `-10` to `-12`, the Cauchy--Schwarz
swap (`abs_sum_qform_swap_le`) and Schwartz--Zippel (`sum_uniform_agree_mass_le`), both of which
are already in the tree. Then the chain's assembly and `lem:qld-povm-to-obs` at its end.

### PR Z: the mirror of a `MirrorSimul`, and the four-index family (2026-09-22)

**The mirror of a `MirrorSimul` is a `MirrorSimul`** --- at the swapped strategy, with the two
players' measurements exchanged and the two cuts exchanged. This is the same economy `toSecond`
buys one level down, and it should have been noticed when `MirrorSimul` was introduced in PR Q.

`toFirst` and `toSecond` give Bob's objects as a `SimulPair`, which is enough for anything stated
on one cut's state --- `bobMTilde`, `bobSwap`, `bobSwap_conj_bobMTilde` all came that way. But the
chain's last displays compare operators on the **physical** state, and nothing about that state was
available for Bob: `physVec`, `bornProb_physVec`, `chainP`, `chainW` are all `MirrorSimul` methods.
`mirror` supplies them. `mirror_sum_snorm_sq_chainP_le` is `-5` to `-8` for Bob, and its proof is
`rw [← M.mirror_physVec]; exact M.mirror.sum_snorm_sq_chainP_le hprojA W v u`.

What makes it go through is that `hmirror` survives the exchange, and that is `mirrorVec_mirrorVec`:
`mirrorEquiv` composed with itself is the identity, **by `rfl`**. Exchanging the two parties and,
within each, the party's own pair half with the other pair's, puts every register back where it
started. The `Prod.swap`-twice and `Prod.mk.eta` definitional equalities carry the rest --- the
whole `mirror` definition typechecks with `hmirror := by rw [M.hmirror, mirrorVec_mirrorVec]` and
every other field a projection.

This halves what is left of the chain. `sum_xSqNorm_le_of_endOp` takes both parties' chains as
hypotheses; only one has to be built.

*The four-index family.* From `-9a` on the chain runs over both parties' pairs. `chainQ` is that
family; `endOp_eq_sum_chainQ` says the endpoint already in the tree is exactly its restriction to
`coupledIdx`, so the displays leading there and the endpoint speak about one projective
measurement. `sum_poly_chainQ` is `-9a`: left-multiplying by Bob's own pair measurement, which is
the identity, refines the three-index family into the four-index one.

*The spelling rule, for the third and fourth time.* `chainP` was defined through
`M.toFirst.chainOp`; the moment a statement mentioned both it and `aliceChainOp`, the product's
`HMul` instance failed to synthesize, because `toFirst.EA` and `M.Ea`, equal by definition, are not
the same spelling. Retyping `chainP` through `aliceChainOp` fixed it, and `bobChainOp` was
introduced for the same reason rather than using `mirror.aliceChainOp`. The rule, now applied
consistently: **give every physical-cut object its own name in its own party's spelling, and never
reach through `toFirst`, `toSecond` or `mirror` inside a statement.**

What is left of the chain: `-10` to `-12`, then the assembly through `sum_xSqNorm_le_of_endOp`,
then `lem:qld-povm-to-obs`.

### PR AA: `eq:qld-pulling-10` down to its Cauchy--Schwarz step (2026-09-22)

The chain's second remaining estimate runs over the four-index family and over the pairs whose
outcomes **disagree** at the sampled point. Everything before the swap is now in.

`sum_snorm_sq_fiber_sandwich_subset_le` is the outer shape on a subset of the index. The version
PR X added fixes the index to `univ`, which the first display needs and this one does not; the
general form is now the lemma and the old one is a one-line case of it.

`bobTail_sandwich` splits the sandwich across the cut --- Alice's factor untouched, since this
display's tail is Bob's alone --- and `bobHat_conj_bobChainOp` identifies Bob's factor as his
sandwiched pair-measurement marginal `bobSand` tensored with his Weyl outcome.

`sum_snorm_sq_chainQ_disagree_le` is the relaxation, which is where the paper's `<=` sits. Each
disagreeing pair contributes one term of a sum over **all** outcomes the pair's own value excludes;
the rest of that sum is nonnegative; and the constraint tying the outcome to the index may then be
dropped. Worth recording what this step does *not* use: no Cauchy--Schwarz, and no measurement
property beyond projectivity --- only `qform_sandwich_nonneg`, that a sandwich is nonnegative.
`Finset.single_le_sum` and `Finset.sum_le_sum_of_subset_of_nonneg` are the whole argument.

`sum_qform_bobTail_eq` closes the reduction at `eq:qld-pulling-13a`: Alice's whole family and Bob's
Weyl outcome both sum to the identity, so what is left carries neither, and the bound is a
statement about Bob's registers alone.

What is left of `-10` is `eq:qld-pulling-13`, the swap --- `abs_sum_qform_swap_le`, already in the
tree, applied on the *second* cut, so every transport it needs goes through `mirror`. Then `-11`
(the helper's item 2 on Bob's side, with a constraint on the index set) and `-12`
(Schwartz--Zippel, `sum_uniform_agree_mass_le`, also in the tree).
