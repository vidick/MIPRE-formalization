# The pasting lemma's collision parameter is not `md/q` on a degenerate diagonal line

**Status: found 2026-09-20**, while formalizing `lem:qld-pairs-of-lines` (Chunk 4, PR C). The
formalization is complete and carries the corrected parameter; the paper's `md/q` is off by an
additive `1/q` on one of the two line types, which leaves `delta_P = poly(eps, md/q)` intact. Worth
one sentence upstream, not a repair.

## What the paper says

`lem:pasting-updated` (`paper/games.tex`) asks of the outcome maps a **distance property**:

> Then for any two nonequal `g_i, g_i' in G_i`, the probability that `g_i(y_i) = g_i'(y_i)`, over a
> random `y_i ~ D_z`, is at most `eps`.

and the application in `paper/qld-combining.tex` supplies it with

> the lemma's collision parameter (called `eps` there) set to `md/q` (this follows from the
> Schwartz-Zippel lemma applied to the polynomials `f_X, f_Z`, which are of total degree at most
> `md`).

`y_i` is the point sampled on the line, `g_i` is a degree-`md` polynomial on it, and
`g_i(y_i)` is its value at the point's parameter.

## Why that is not quite right

The seeded CL test's diagonal line has direction `zeroBelow(chi(s), v)`
(`MIPRE.LIDT.CL.zeroBelow`, used by `MIPRE.QLD.ddirOf`), which is `v` with its coordinates *below*
the seed's block zeroed. That vector **can be zero**: it is zero exactly when `v` vanishes from
`chi(s)` upwards, and since `chi(s) <= m - 1` this happens for at least a `1/q^m`- and at most a
`1/q`-fraction of the contents.

On such a content the "line" is a single point. Every polynomial on it is evaluated at the same
parameter, so two distinct degree-`md` polynomials agree there with probability `1`, not `md/q`.
The distance property therefore fails at those questions, and `eps = md/q` is not available as a
uniform bound.

Two things make this a small correction rather than a hole.

* The conclusion only needs the collision probability **on average over the question**, which is
  how the formalization states it: `MIPRE.sum_collisionTerm_le` takes a collision probability
  `eps(z)` per question and concludes with its average. (The paper's own proof also only uses the
  average --- "by our distance assumption it is at most `eps` in expectation" --- so the statement
  is stronger than the proof needs.)
* The degenerate contents are rare: `MIPRE.QLD.sum_content_degenerate_le` bounds their probability
  by `1/q`, by the same change of variables that gives the point's uniformity on its line, applied
  to the raw direction `v` instead of the point.

So the collision average is `md/q` for an axis-parallel line
(`MIPRE.QLD.sum_content_collProb_aPres`) and at most `md/q + 1/q` for a diagonal one
(`MIPRE.QLD.sum_content_collProb_dPres`), and `delta_P` stays `poly(eps, md/q)`.

## What the formalization does

`MIPRE.QLD.collProb` is the per-content collision probability of a line presentation, defined by a
case split on whether the direction vanishes: `md/q` when it does not, and `1` --- the trivial
bound --- when it does. `MIPRE.QLD.card_collide_le` proves the count in both cases, and the two
averages above are what `lem:qld-pairs-of-lines` reports in its error term. Nothing in the chain
assumes the paper's uniform `md/q`.

## Where this is recorded

* `blueprint/src/content/03_background_results.tex`, the Comments of `lem:qld-pairs-of-lines`;
* `blueprint/src/content/02_foundations.tex`, the statement of `lem:pasting-updated`, whose last
  clause takes the collision probability as a function of the question for exactly this reason;
* `planning/qld-campaign.md`.
