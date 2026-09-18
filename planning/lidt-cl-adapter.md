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

## The bridging lemmas, smallest first

1. `pivots (span {Pi.single i 1}) = {i}`, whence
   `rep (Pi.single i 1) u = u - u i • Pi.single i 1 = (Line.through u (Pi.single i 1)).1` and
   `(Line.through u (Pi.single i 1)).2 = Pi.single i 1`. This is the one place the canonical
   representative of `def:cl-canonical` has to be computed rather than used abstractly.
2. Coordinate reversal as an equivalence of `Point F m`, with `ρ (Pi.single i 1) = Pi.single (rev i) 1`
   and `ρ (zeroBelow i v) = extend (…)` — the third row of the table.
3. Rescaling of `LinePoly F n`: `rescale c f` with `(rescale c f).eval t = f.eval (t / c)` for
   `c ≠ 0`, an equivalence, with `lineParam u₀ (c • w) x = c⁻¹ * lineParam u₀ w x`.
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
