/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LineInterpolation/BadLine.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LineInterpolation.Core
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.BadLine

@[expose] public section

/-!
# Line interpolation: bad-line event

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadLine.lean` in
the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored file mixes two classical declarations, the interpolated vertical line of a tuple of
slice answers and the extraction of a mismatching slice when that line differs from a given line
polynomial, with two commutation lemmas: evaluating at a point, or restricting to the vertical
line through a point, commutes with averaging an indexed submeasurement family over a
distribution. The classical pair is imported from the vendored file. The two commutation lemmas
read no state, so they are ported generic over an ordered `⋆`-ring `R`, as `evaluateAt`,
`hRestrictionToVerticalLine` and `averageIdxSubMeas` are; they serve the local algebra `𝔓` (the
vendored `Op ι`, where all their vendored callers apply them) and `K →L[ℂ] K` alike.

## Not ported

- `tupleInterpolatedVerticalLine`: classical, imported.
- `tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point Distribution)
open MIPRE.LIDT.Co (SubMeas IdxSubMeas postprocess averageIdxSubMeas
  averageOperatorOverDistribution evaluateAt)

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R] [Module ℝ R]
  [PosSMulMono ℝ R] [SMulPosMono ℝ R] [ZeroLEOneClass R]

/-- Evaluating at a point commutes with averaging an indexed polynomial-valued submeasurement
family over a sub-probability distribution. -/
theorem evaluateAt_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (MIPStarRE.LDT.Polynomial params) R)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    evaluateAt params u (averageIdxSubMeas 𝒟 A h𝒟) =
      averageIdxSubMeas 𝒟 (fun q => evaluateAt params u (A q)) h𝒟 := by
  refine SubMeas.ext (fun a => ?_) rfl
  simp only [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution,
    Finset.smul_sum]
  exact Finset.sum_comm

/-- Restricting to the vertical line through a point commutes with averaging an indexed
polynomial-valued submeasurement family over a sub-probability distribution. -/
theorem hRestrictionToVerticalLine_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (MIPStarRE.LDT.Polynomial params.next) R)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    hRestrictionToVerticalLine params (averageIdxSubMeas 𝒟 A h𝒟) u =
      averageIdxSubMeas 𝒟 (fun q => hRestrictionToVerticalLine params (A q) u) h𝒟 := by
  refine SubMeas.ext (fun f => ?_) rfl
  simp only [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
    averageOperatorOverDistribution, Finset.smul_sum]
  exact Finset.sum_comm

end MIPRE.LIDT.Co.Pasting

end
