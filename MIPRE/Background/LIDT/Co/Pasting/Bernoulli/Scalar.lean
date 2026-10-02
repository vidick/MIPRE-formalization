/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
Scalar.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.TruncatedSums
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.Scalar

@[expose] public section

/-!
# Scalar Bernoulli polynomial helpers for pasting

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored file is classical throughout: the scalar Bernoulli tail polynomial
`F(p) = ∑_{r=d+1}^k C(k,r) p^r (1-p)^{k-r}`, its lower tail and affine lower envelope, Hoeffding's
lemma for a centered Bernoulli variable, the binomial moment-generating function and its
Hoeffding bound, and the pointwise estimate `bernoulliTailLowerAffine_le_scalarBernoulliTail`
on `[0, 1]` that the operator Chernoff comparison feeds through the functional calculus. None of
them mentions a state, an operator or a measurement, so none is ported: this file imports the
vendored file, and the ported files of `Pasting` name its declarations through explicit
`open MIPStarRE.LDT.Pasting (…)` lists.

The file mirrors the vendored module so that the ported tree keeps the vendored import graph:
it imports `Co/Pasting/Bernoulli/TruncatedSums.lean`, the counterpart of the vendored file's
import, and `Co/Pasting/Bernoulli/FromHToG/Core/BernoulliTail.lean` imports it as the vendored
`BernoulliTail` imports `Scalar`.

## Not ported

- `scalarBernoulliTail`: classical, imported.
- `scalarBernoulliLowerTail`: classical, imported.
- `bernoulliTailLowerAffine`: classical, imported.
- `bernoulli_centered_mgf_le`: classical, imported.
- `binomial_centered_mgf_eq`: classical, imported.
- `binomial_centered_mgf_le`: classical, imported.
- `binomial_lowerTail_eq`: classical, imported.
- `scalarBernoulliLowerTail_le_exp`: classical, imported.
- `scalarBernoulliLowerTail_add_scalarBernoulliTail`: classical, imported.
- `scalarBernoulliTail_hoeffding_lower_bound`: classical, imported.
- `degree_div_le_theta_half`: classical, imported.
- `bernoulliTailLowerAffine_le_scalarBernoulliTail`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

end
