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

The error obtained this way is `m^2 * delta_P`-shaped rather than the paper's
`O(m(eps^{1/4} + delta_P^{1/4} + delta_Q^{1/4} + delta_Line^{1/2}))`. That is **not** of the form
`m * poly(eps, md/q)` that the statement of `lem:qld-4-13` advertises, but it is of the form
`poly(m) * poly(eps, md/q)`, and `lem:qld-4-7` --- the only consumer --- absorbs any polynomial
factor in `m` into its `a(md)^a` prefactor. For small `delta_P` the new bound is also the stronger
one.

## Suggested upstream action

Either replace Claims 17-1 to 17-3 by the product decomposition and the data-processing step, or keep
them and add a remark that the decomposition *is* available for the construction of
`lem:qld-sublines`, with the reason above. Either way the `\cnote` on the conclusion should be
corrected: it is conditioning on `l`, not on `(l_X, l_Z)`, that creates the correlation.
