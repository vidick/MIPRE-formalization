# The seeded-CL adapter: target, route, and the lemmas it needs

Written 2026-09-18, scoping Chunk 3 of `planning/next-chunks.md` after reading the paper's own
proof (`ldt.tex`, `lem:ld-soundness`) and both games as formalized. It records a **route change
from what `next-chunks.md` says**, the reason for it, and the bridging lemmas the route needs.

## What `next-chunks.md` says, and why it cannot be followed as written

Chunk 3 reads: prove `thm:lidt-cl-soundness` "from the vendored canonical-line theorem through
`lem:lidt-reduction-setup`, `lem:lidt-test-transfer`, `lem:lidt-sync-transfer` and
`lem:lidt-derandomize`". Those two halves belong to different routes.

The four lemmas, as the blueprint states them, are steps of the **paper's** route: they name the
two-prover tensor code test (`lem:lidt-reduction-setup`: "The seeded CL test with `ldc = 1` is
*not* the two-prover tensor code test"), its axis-parallel-line distribution
(`lem:lidt-test-transfer`), and `lem:tensor-codes-bipartite` (`lem:lidt-derandomize`). The paper
proves the `ldc = 1` case from `[ji2021quantum, Theorem 4.7]`, the tensor code test, and never
mentions the canonical-line test. `thm:tensor-codes` has no Lean proof and is not going to
acquire one soon, so that route yields a **conditional** theorem.

The **canonical-line theorem is the one this repository has proved**:
`MIPRE.LIDT.lowIndividualDegree_soundness` (`MIPRE/Background/LIDT/Soundness.lean`), for
`MIPRE.LIDT.lidtGame`, with the explicit error `lidtError m d q k ε`, through the vendored
MIPStarRE bridge. `rem:lidt-cl-adapter` already identifies reducing to *it* as a separate,
unwritten route ("Reusing Theorem `thm:lidt-soundness` to prove the single-codeword case of
Theorem `thm:lidt-cl-soundness` requires an explicit strategy adapter"), and says plainly that
"a proof by either route would not certify the intermediate claims of the other".

**Decision (maintainer, 2026-09-18): take the canonical-line route.** It gives an unconditional
theorem and needs no new game. The cost is that the argument is ours rather than the paper's, so
the campaign's adversarial review does not underwrite it, and the four blueprint lemmas must be
*restated* for the new target rather than reused under their current labels.

## Prerequisite, now merged

`clGame`'s decision predicate was missing `fig:ld-decider`'s format check, which made the test
vacuous; see `reports/clgame-format-check-missing.md`. Nothing about the adapter is meaningful
before that repair, since the value being transferred was a value no strategy could fail to
achieve.

## The two games, side by side

| | `clGame` (`def:lidt-cl`) | `lidtGame` (`def:lidt`) |
|---|---|---|
| line questions | `(u₀, s)` / `(u₀, s, v')`, seed retained | canonical `Line.through u w`, no seed |
| direction scale | raw `v'`, any scale | normalized: first nonzero coordinate is `1` |
| diagonal support | `zeroBelow i v`: first `i` coordinates zero | `extend v`: coordinates past `j` zero |
| answers | `ldc`-tuples | single |
| distribution | uniform over 9 ordered type pairs × `(u, s, v)` | `1/3` per subtest × uniform swap |
| line-vs-line | equality checked on `(ALine, ALine)`, `(DLine, DLine)` | no such subtest |

The last row is the piece of luck. `lidtGame`'s only same-type subtest is point self-consistency,
so **the adapter needs no line-synchronicity transfer**: no `lem:lidt-sync-transfer`, no
Schwartz–Zippel, and no `d/q` term from that source. The paper needs them because the tensor
code test has a line synchronicity condition.

## The reduction

Same `dA`, `dB`, `ψ`; the measurements are reindexed on questions and coarse-grained on answers.
Let `ρ : F^m → F^m` be coordinate reversal, `ρ(x)_j = x_{m+1-j}`, which exchanges the third row
of the table.

* **Points.** `PA' (point u) := PA (point (ρ u))`, answer `values a ↦ value (a 0)`.
* **Axis lines.** A question of `lidtGame` is `Line.through u (Pi.single i 1)`. Its reversal has
  direction `Pi.single (m-1-i) 1`; the `clGame` questions describing it are `(u₀, s)` for the
  `q/m` seeds `s` with `χ(s) = m-1-i` (`card_chi_fiber`). Choose one, `σ ℓ`.
* **Diagonal lines.** A question of `lidtGame` is `Line.through u (extend v)`, direction
  normalized. The `clGame` questions describing the reversed line are `(u₀, s, c • w)` for
  `χ(s)` in the right range and `c ≠ 0`; choose one, `τ ℓ`. The answer polynomial is
  reparametrized: `clGame`'s `f` is in the parameter of `u₀ + t (c • w)`, `lidtGame` wants `g` in
  that of `u₀ + t w`, so `g(t) = f(t/c)`, i.e. `gᵢ = fᵢ / cⁱ` — degree-preserving and a
  bijection of `LinePoly F n`.
* **Second player.** The same with independent choice functions.

Then average over the choice functions and derandomize: `𝔼[value] ≥ 1 - ε'` gives some choice
achieving it.

## Infrastructure that already exists

`MIPRE/Foundations/GameTransport.lean` has most of the pieces:
`ProjectiveMeasurement.reindex` (questions along any map, answers along an equivalence),
`ProjectiveMeasurement.merge` (coarse-grain answers, needs `mul_eq_zero_of_ne`),
`TensorProductStrategy.relabel`, `mergeAnswers`, `value_le_mergeAnswers`.

What is missing is the combination the adapter wants: reindex questions along a **map** *and*
merge answers, with the value bounded below by the source game's per-subtest failures. The
existing `value_le_mergeAnswers` assumes the two games share their question alphabets and
distribution (`hμ : ∀ x y, G.μ x y = G'.μ x y`), which is exactly what fails here. That
combination lemma is the adapter's core and has to be written from the definition of `value`,
summing over `lidtGame`'s `Sample`.

## Correction (2026-09-18, found while proving the geometry): the rebasing is affine

The list below originally said the answer polynomial needs *rescaling*. That is right on
axis-parallel lines and wrong on diagonal ones, and the reason is that **the two tests pick
different canonical base points**.

`rep w x` zeroes the coordinate of `x` at the *first* nonzero coordinate of `w` (`rep_eq`,
from `pivots_span_singleton`). `Line.through u v` zeroes the coordinate at the first nonzero
coordinate of `v`. But the adapter applies `rep` to the *reversed* direction, and the first
nonzero coordinate of `ρ dir` is the reversal of the **last** nonzero coordinate of `dir`. On an
axis-parallel line the first and last nonzero coordinates coincide, the two base points agree
exactly (`rep_single_eq_through`) and there is nothing to do. On a diagonal line they differ by
a multiple of the direction, so the two parameters differ by a *shift*:

`x = base + t·dir` on the canonical-line side is `ρ x = u₀ + (t + base_J/dir_J)·ρ dir` on the
seeded side, `J` the last nonzero coordinate of `dir`.

There is no freedom to avoid this: the seeded question's base point is whatever `rep` returns,
and `rep` is constant along the line (`rep_add_smul`), so every seeded description of the line
carries the same base point. The reparametrization of the answer is therefore affine,
`g(t) = f(a t + b)`, which is exactly the "canonicalization and **rebasing**" that
`rem:lidt-cl-adapter` lists among the adapter's obligations --- the remark had it right and this
note did not.

Consequence for the work: `rescaleEquiv` is not enough. What is needed is an affine
reparametrization of `LinePoly F k` that preserves the degree bound and is a bijection. The
clean route is through `Polynomial F`: send a coefficient vector to `∑ C (f i) * X ^ i`, compose
with `C a * X + C b`, and read the coefficients back, using `natDegree_comp` to see that the
degree bound survives and `Polynomial.taylor`/`comp` algebra for the inverse. A Taylor shift
written directly on coefficient vectors would need the binomial theorem by hand; going through
`Polynomial` does not.

## Status (2026-09-18)

The adapter's **ingredients are proved**; the **assembly is not**.

| piece | where | state |
|---|---|---|
| general reduction: `succAt`/`failAt`, `adapt`, the cost in the distributions | `MIPRE/Foundations/GameAdapt.lean` | done |
| derandomization over a family of question maps | same (`exists_one_sub_value_adapt_le`) | done |
| axis-parallel lines: the two tests agree exactly | `Adapter/Geometry.lean` | done |
| coordinate reversal, the two diagonal conventions | same | done |
| the direction scale, and the two parameter conventions | same | done |
| `rep` in closed form, constant along the line | same | done |
| affine reparametrization of an answer | `Adapter/Reparam.lean` | done |
| choosing a seed in a `χ`-fibre | `Adapter/Seeds.lean` | done |
| the question maps and the answer coarse-graining | `Adapter/Strategy.lean` | done (`qmap`, `amap`) |
| `hD`: all five support cases, assembled | same (`hD_qmap`) | done |
| the weight domination, with the seed averaging | --- | **open** |
| the final theorem, and the `k = poly(m,d)` corollary | --- | **open** |

The one open Lean row is the reduction's arithmetic; its decision-predicate half is done. The hardest is the weight domination, and it
is worth saying why: both `clGame.μ` and `lidtGame.μ` are defined as sums over a `Sample` type
against an indicator, so dominating one push-forward by the other means *counting* the samples
that produce a given question pair. On the diagonal subtest that is a count of solutions of
`zeroBelow (χ s) V = w` together with `rep w u = u₀`, which comes to `q^{χ s}` samples, against
the canonical-line test's `q^{j+1}` for the direction supported on the first `j+1` coordinates.
Those match under the reversal `j + 1 = m - χ s` — that correspondence is the arithmetic content
of `lem:lidt-test-transfer` for this target — but both sides also range over the admissible
`χ s` and `j`, and the singleton line `v = 0` is a separate case. None of it is deep; all of it
is careful.

## The bridging lemmas, smallest first

1. `pivots (span {Pi.single i 1}) = {i}`, whence
   `rep (Pi.single i 1) u = u - u i • Pi.single i 1 = (Line.through u (Pi.single i 1)).1` and
   `(Line.through u (Pi.single i 1)).2 = Pi.single i 1`. This is the one place the canonical
   representative of `def:cl-canonical` has to be computed rather than used abstractly.
2. Coordinate reversal as an equivalence of `Point F m`, with `ρ (Pi.single i 1) = Pi.single (rev i) 1`
   and `ρ (zeroBelow i v) = extend (…)` — the third row of the table.
3. Rescaling of `LinePoly F n`: `rescale c f` with `(rescale c f).eval t = f.eval (c * t)`, an
   equivalence for `c ≠ 0` (`rescaleEquiv`), with
   `lineParam u₀ (c • w) x = c⁻¹ * lineParam u₀ w x` (`lineParam_smul`). **Done**, but see the
   correction above: the diagonal case additionally needs the affine shift.
4. `lineParam u₀ w x = Line.param (Line.through u w) x` when `x` is on the line and the
   direction is normalized — reconciling the two parameter conventions.
5. The weight bookkeeping: each of `clGame`'s nine ordered type pairs has mass `1/9`, and each
   of `lidtGame`'s three subtests mass `1/3` split over the swap, so a conditional failure of
   `clGame` at `9ε` bounds the corresponding `lidtGame` subtest failure. No `md/q` term is
   expected from this route; if one appears it will be from the derandomization and should be
   tracked down rather than absorbed.
6. The combination lemma of the previous section, then the derandomization, then
   `lowIndividualDegree_soundness`, then the pull-back of its three consistency conclusions
   through the point-answer relabelling (`Answer.toValue` on one side, `values a ↦ a 0` on the
   other).

## The assembly, worked out on paper

This section is the part that is designed but not yet in Lean. It is written out because the
choices in it are not forced by the types, and rediscovering them costs more than reading them.

### The question map

Index the averaging family by `σ : Fin m → Fin (q/m)`, a fibre position per direction index, and
write `s i = seedOf hm i (σ i)` (`Adapter/Seeds.lean`). Then

* `point u ↦ .point (ρ u)`;
* `axisLine ℓ ↦ .aline (ρ ℓ.1) (s (rev i))`, where `ℓ.2 = eᵢ`. The base point needs no `rep`:
  the two agree exactly on axis-parallel lines (`rep_single_eq_through`).
* `diagLine ℓ ↦ .dline (ρ ℓ.1 - sh(ℓ) • ρ ℓ.2) (s (p ℓ)) (ρ ℓ.2)`, where `p ℓ` is the first
  nonzero coordinate of `ρ ℓ.2` and `sh(ℓ) = (ρ ℓ.1)_{p} / (ρ ℓ.2)_{p}` is the shift of the
  correction above; the base point is `rep (ρ ℓ.2) (ρ ℓ.1)` written out through `rep_eq`.

The direction carried was **exactly** `ρ ℓ.2`, not a rescaling of it, making the scale factor `1`
and leaving only the shift, so that `reparam 1 (sh ℓ)` was the whole answer conversion. **See the
second correction below: that is wrong**, and the scale has to be averaged over too, so the
conversion is `reparam c (sh ℓ)`.

### The answer coarse-graining

Source answers are `clGame`'s, target answers `lidtGame`'s, question-dependent (hence
`mergeAt`):

* at `point _`: `values a ↦ value (a 0)`;
* at `axisLine _`: `apolys f ↦ axisPoly (f 0)`;
* at `diagLine ℓ`: `dpolys f ↦ diagPoly (reparam 1 (sh ℓ) (f 0))`;
* anything else to a fixed answer. Those cases are unreachable in `hD`: a source answer of the
  wrong format for its question is *rejected* by `clGame` (the repair of #108), so the
  implication is vacuous there. Before that repair this would have been a real gap.

### `hD`, case by case

`lidtGame.μ x' y' ≠ 0` gives a `Sample` with `s.questions = (x', y')`, so there are three cases
and their swaps. In each, `clGame`'s acceptance first gives both answer formats, then:

* **`selfConsistency u`.** Both questions are `point (ρ u)`; the source checks `α = β` and the
  target `u = u ∧ α 0 = β 0`. Immediate.
* **`axis false u i`.** The source accepts iff `ρ u = ρ ℓ.1 + t • e_{rev i}` for some `t` and
  `(f 0).eval (lineParam (ρ ℓ.1) e_{rev i} (ρ u)) = α 0`. Applying `ρ` to the first gives
  `u = ℓ.1 + t • ℓ.2`, which is `ℓ.Mem u`; `lineParam_eq_of_mem` and
  `param_through_eq_of_mem` then both evaluate to the *same* `t`, so the target's
  `(f 0).eval (ℓ.param u) = α 0` is the same equation.
* **`diag false u j v`.** The same, with the base point shifted: `ρ u = u₀ + (t + sh) • ρ ℓ.2`, so
  `lineParam` returns `t + sh`, and the target wants
  `(reparam 1 (sh ℓ) (f 0)).eval t = (f 0).eval (t + sh)` --- which is `eval_reparam`. This is
  the case the affine rebasing exists for.

The two swapped cases are the same with the roles exchanged.

### Correction (2026-09-18, second): carrying the direction unrescaled breaks the weight bound

The design above chooses the seeded question that carries the direction **exactly** `ρ ℓ.2`, so
that the answer conversion is a pure shift. That choice is wrong, and the weight arithmetic is
what shows it.

The seeded test's `DLine` questions carry the raw direction, so for one geometric line there are
`q - 1` questions differing only by the scale of the direction, and `μ` spreads over all of them.
The unrescaled adapter maps into exactly **one** of them: the one whose reversal is normalized.
So its push-forward is concentrated on a `1/(q-1)` fraction of the seeded questions it could
have used, and at those questions it exceeds `μ` by a factor that grows with `q` --- even though
the *aggregate* masses differ only by a constant (`1/3` against `1/9`). A per-pair bound
`push-forward ≤ C · μ` therefore forces `C` to grow with `q`, and `C` must be `poly(m, d)`: the
error it multiplies is the `ε` of `δ_CL`. Concretely the diagonal shape comes out needing
`C ≥ 3q/2` where the point-point shape needs only `C ≥ 3`.

**The fix is to average over the scale as well as the seed.** One *global* nonzero scale
parameter suffices: for a given seeded question exactly one value of it makes the fibre
nonempty, so the family grows by `q - 1` while the push-forward does not, and the ratio comes
back to a constant. The axis subtest is unaffected, its questions carrying no direction at all
(the direction is determined by `χ s`), so the extra parameter multiplies both sides equally
there.

Two consequences for the work. The averaging family becomes
`(σ : Fin m → Fin (q/m)) × {c : F // c ≠ 0}`. And `amap` needs `reparam c (sh ℓ)` rather than
`reparam 1 (sh ℓ)`, so the **general two-parameter** `reparam` is on the critical path after all,
together with `lineParam_smul` --- which the previous correction had written off. `Reparam.lean`
was built with general `a` and `b`, so nothing has to be rewritten, but `hD_diag` and `hD_diag'`
will each need the scale threaded through. `hD_selfCons`, `hD_axis` and `hD_axis'` are unaffected.

Status of this correction: the *structural* reason is certain --- the image misses `q - 2` of
every `q - 1` scalings while `μ` does not --- and it is enough to rule the design out. The exact
constants below are a hand derivation and have not been machine-checked.

### The weight domination, with the axis case computed

The push-forward hypothesis is

```
∀ x y, (∑ σ, ∑ x' ∈ fib(qmap σ, x), ∑ y' ∈ fib(qmap σ, y), μ' x' y') ≤ |Seed| * (C * μ x y)
```

with `Seed = Fin m → Fin (q/m)`, so `|Seed| = (q/m)^m`. The useful reformulation swaps the
orders: for fixed `(x, y)`,

```
LHS = ∑_{x'} ∑_{y'} μ'(x', y') * #{σ : qmap σ x' = x ∧ qmap σ y' = y}
```

and that count is easy, because on the support one of the two questions is a *point*, whose
image does not depend on `σ` at all, and the other is a line, whose image depends on `σ` at
exactly **one** index. So the count is `(q/m)^{m-1}` when the one constraint is satisfiable and
`0` otherwise.

The axis-parallel case, in full, as the pattern for the others. Take
`x = .aline u₀ s`, `y = .point xₚ`.

* **`μ x y`.** The seeded samples producing it have `tyA = aline`, `tyB = point`, `U = xₚ`,
  seed `s`, and `V` free; the base point matches iff `rep e_{χ s} xₚ = u₀`. So there are `q^m`
  of them out of `9 q^{2m+1}`, giving `μ = 1/(9 q^{m+1})` when consistent and `0` otherwise.
* **The push-forward.** `qmap σ y' = .point xₚ` forces `y' = point (ρ xₚ)`. For `x'`, matching the
  seed forces `χ s = rev (axisIdx ℓ)` by `chi_seedOf`, so the direction index is `rev (χ s)` and
  `ℓ.2 = e_{rev (χ s)}`; matching the base point forces `ℓ.1 = ρ u₀`. So `ℓ` is *determined*, and
  the surviving constraint on `σ` is at the single index `χ s`, where exactly one of the `q/m`
  fibre positions works (`seedOf_injective`). Count `(q/m)^{m-1}`.
* **`μ'`** at that one pair is `1/(6 m q^m)`, the weight of the single sample `axis false u i`.
* **The inequality.** `(q/m)^{m-1} / (6 m q^m) ≤ (q/m)^m * C / (9 q^{m+1})` reduces to
  `9 q ≤ 6 q C`, i.e. **`C ≥ 3/2`**, with no `q` or `m` left in it. That is the factor `q/m` a
  fixed choice would have cost, paid back exactly by the averaging.

### The weight domination

Still the hard row, and the reason a fixed seed choice is not merely lossy: the push-forward of
a fixed choice is concentrated on `m` of the `q` seeds, so it exceeds `μ` by `q/m` there.
Averaging over `σ` spreads it over each fibre, and `seedOf_injective` is what makes that count.
For the axis subtest the resulting constant is `3/2`: `lidtGame` puts `1/(6 m q^m)` on
`(axisLine ℓ, point u)`, each seed is chosen with probability `m/q`, and
`clGame` puts `1/(9 q^{m+1})` on the corresponding pair. The diagonal subtest is the same
computation with the `q^{χ s}` against `q^{j+1}` matching described above.

## What this route does *not* give

No ledger node. The paper's route and its reviewed intermediate statements
(`lem:lidt-reduction-setup` through `lem:lidt-derandomize`, nodes `1.2.1.1`–`1.2.1.8`) are
claims about the tensor-code reduction, and this route certifies none of them — `rem:lidt-cl-adapter`
says so explicitly. Node `1.2.1` itself is the seeded CL theorem, and a proof of it by this route
*would* discharge that node's statement, but only once the parameter corollary below is in place.

Nor does it give the `ldc > 1` case, which is `lem:lidt-ldc` and the paper's Steps 1–5, a
separate piece of work on top.

The quantitative obligation stays: `lowIndividualDegree_soundness` produces
`lidtError m d q k ε'` with `k` free subject to `k ≥ 400md`, and `thm:lidt-cl-soundness` asks for
`a (dm·ldc)^a (ε^b + q^{-b} + 2^{-bmd})`. Choosing `k = poly(m, d)` and bounding one by the other
is arithmetic that has to be done honestly against the explicit constants (`100000 k² m⁴`,
`ε^(1/40000)`, `exp(-k/(2560000 m²))`), not waved at. It is a corollary of its own and should be
stated separately from the reduction, so that a failure to make the constants work does not
silently weaken the reduction.
