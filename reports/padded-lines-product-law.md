# The padded line-point law is a mixture of products, so `lem:qld-4-13`'s three claims are avoidable

**Status.** Found while formalizing `lem:qld-padded-lines` (the paper's `lem:qld-4-13`). Not a
contradiction with the paper: the paper's proof is correct. The finding is that one of its steps is
more conservative than the construction requires, and that the stronger fact --- which this
repository has proved in Lean --- shortens the proof of the lemma from three Cauchy--Schwarz claims
to a data-processing step.

## What the paper says

The proof of `lem:qld-4-13` bounds

    E_{(l, l_X, l_Z) ~ D} E_{(x,z,a,b) in l} sum_{f_X,f_Z}
        <psi| T^{l_X,l_Z}_{f_X,f_Z} (x) (I - Q^{x,z}_{f_X(x),f_Z(z)}) |psi>

by chaining Claims 17-1, 17-2 and 17-3. The concluding `\cnote` explains why the chain is needed:

> The previous conclusion [...] derived the bound by treating the right-hand side of
> (eq:qld-combined-lines-consistency) as a mixture of terms with *independent* `(l_X,x)` and
> `(l_Z,z)`; under the distribution `D` of Lemma `lem:qld-sublines` the pair is correlated (for
> diagonal lines both coordinates share the line parameter), so that decomposition is not available.
> Claims 17-1 through 17-3 avoid the issue by using only the marginal distributions, which Property 2
> does provide.

And `lem:qld-xz-lines` is available on a product of restricted laws at `O(m^2 delta_P)`
(eq:qld-xz-lines-restricted), so if the decomposition *were* available the lemma would follow at
once.

## What is true

The correlation is real, but it is a correlation *given the padded line*, not given the two sublines.

* Conditioned on `l`, a uniform point of `l` has `u_X = v_X + t w_X` and `u_Z = v_Z + t w_Z` with one
  shared `t`. That is the paper's observation, and it is correct.
* The quantity to be bounded conditions on `(l_X, l_Z)`, not on `l`. The pair `(l_X, l_Z)` knows each
  block's coset in its own space; it does **not** know the relative offset of the two blocks, which
  is what `l` adds. Marginalizing that out restores independence.

Concretely, at a fixed padded seed the four-tuple `(l_X, u_X, l_Z, u_Z)` is a function of
`(dir_X, xBlk u)` and `(dir_Z, zBlk u)`, and those two groups depend on disjoint blocks of the two
independent uniform vectors `u` and `v` --- the padded point and the padded raw direction. So the
joint law *is* a product of the two marginals, each restricted or not according to which block the
padded axis index lies in.

## What is proved in Lean

`MIPRE/Background/QLD/Padded.lean`:

* `avgSub_free`, `avgSub_zc`, `avgSub_xc`, `avgSub_xc_dline` (earlier work): at a fixed padded seed
  the padded law is *exactly* the product of the two marginal laws.
* `sum_avgRestr`, `avgRestr_le_mul_avgAll`, `avgRestr_prod_le_mul_avgAll`: the `m` restricted laws
  average to the unrestricted one, so each is at most `m` times it and a product of two at most
  `m^2` times the product.
* `avgSub_le_mul_avgAll`: **the padded line-point law is at most `m^2` times the product of the two
  unrestricted subline laws**, uniformly in the padded seed and the line type.
* `shiftAB`, `sumSubAB_eq`, `avgSubAB_le_of_forall`: `alpha` and `beta` at the sampled padded point
  are uniform and independent of both sublines, because translating the point in those two
  coordinates alone is a bijection that leaves both sublines fixed. So a bound holding for every
  fixed `(alpha, beta)` holds for the joint law.

`MIPRE/Background/QLD/Product.lean`:

* `pairs_of_lines_prod_of_items`: `lem:qld-xz-lines` on a product of two independent line-point laws,
  from game-level hypotheses only.

## Consequence for the lemma

With those, `lem:qld-4-13` follows from `pairs_of_lines_prod_of_items` by

1. coarse-graining the outcome pair `(f_X(x), f_Z(z))` along `(r_1, r_2) |-> alpha r_1 + beta r_2`
   (data processing: coarse-graining only increases agreement),
2. `avgSub_le_mul_avgAll` to pass from the product law to the padded law, and
3. `avgSubAB_le_of_forall` to put `(alpha, beta)` back inside the average.

Claims 17-1, 17-2 and 17-3 are not used. Step 1 is the only part not yet formalized.

Claims 17-1, 17-2 and 17-3 are not used. **Update: all of this is now formalized**, in
`MIPRE/Background/QLD/PaddedLines.lean`; `padded_lines_consistency` is the bound.

## How big is `delta_P`, and how do the two errors compare?

`delta_P` is `deltaPairs eps eps_c`, the error of `lem:qld-pairs-of-lines`. Unfolded
(`Lines.lean`, `Combined.lean`):

    deltaQ eps       = 2 sqrt(57676416 eps) + sqrt(86 eps) + 86 eps
    kappaPairs eps   = 4 deltaQ eps + 461411328 eps
    deltaPairsD eps  = 20 kappaPairs eps + 1376 eps
    deltaPairs eps e = deltaPairsD eps / 2 + sqrt(deltaPairsD eps / 2)
                         + sqrt(32 deltaPairsD eps + 4 sqrt(172 eps) + 2 e)

so for small `eps` and `eps_c`

    delta_P  ~  7 * 10^3 * eps^{1/4}  +  1.5 * sqrt(eps_c),        eps_c = md/q (+ 1/q diagonal).

Two things follow, and neither is specific to this route --- they are properties of the chain as a
whole.

* **`delta_P` is not small in any absolute sense.** It exceeds `1` --- i.e. says nothing --- unless
  `eps <~ 4 * 10^{-16}` and `md/q <~ 0.2`. The `eps^{1/4}` comes from the two nested square roots
  (the sandwich's Cauchy--Schwarz chain inside `deltaQ`, then the pasting lemma's), and the constant
  from `lem:qld-obs-commutation`'s `57676416` and `lem:qld-combined-points`' `461411328`. Every
  stage of the appendix multiplies constants this way; `thm:qld` is an asymptotic statement and its
  consumers take `eps` polynomially small.
* **The comparison with the paper's bound is not uniform.** The paper gets
  `O(m(eps^{1/4} + delta_P^{1/4} + ...))`, which contains `delta_P^{1/4} ~ eps^{1/16}`; this route
  gets `m^2 delta_P ~ m^2 eps^{1/4}`. So `m^2 delta_P <= m delta_P^{1/4}` exactly when
  `delta_P <= m^{-4/3}`, i.e. when `eps <~ 4 * 10^{-16} m^{-16/3}`. In that regime --- the regime
  `lem:qld-4-7` is applied in --- this route is very much the better bound, by a fourth power in
  `eps`; outside it the paper's is better. Neither dominates everywhere.

The functional form is `poly(m) * poly(eps, md/q)` rather than the `m * poly(eps, md/q)` the
statement of `lem:qld-4-13` advertises. `lem:qld-4-7` --- the only consumer --- absorbs any
polynomial factor in `m` into its `a(md)^a` prefactor, so the difference is harmless there, but the
statement of `lem:qld-4-13` should be corrected to say `poly(m)` if this route is adopted.

## Suggested upstream action

Either replace Claims 17-1 to 17-3 by the product decomposition and the data-processing step, or keep
them and add a remark that the decomposition *is* available for the construction of
`lem:qld-sublines`, with the reason above. Either way the `\cnote` on the conclusion should be
corrected: it is conditioning on `l`, not on `(l_X, l_Z)`, that creates the correlation.
