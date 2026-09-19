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

### PR B — the game, what winning implies, the Magic Square lemma, and the expansion

`def:qld-game` (see above), then `lem:ms-direct-anticomm`, `lem:qld-win`,
`lem:qld-expanded-points`, `lem:qld-expanded-lines`. `lem:qld-win` is bookkeeping *given* the game — each item is the value
of a subtest divided by its selection probability — plus one real step, transferring
`lem:ms-direct-anticomm` to the point observables. The expansion stage is where the ancillas
come in and where the sign `(−1)^γ` cancels exactly; the blueprint flags that cancellation as
the pivotal step, so it is the thing to get right first.

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
