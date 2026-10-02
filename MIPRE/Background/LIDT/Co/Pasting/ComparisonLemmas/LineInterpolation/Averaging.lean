/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LineInterpolation/Averaging.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.DistributionAvg
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.Common
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.Averaging

@[expose] public section

/-!
# Line interpolation: averaging and tensor helpers

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Averaging.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored file mixes five classical lemmas (the comparison of an average over distinct tuples
with the uniform average plus the total-variation distance, and three `max 0` estimates, the
last of which is Jensen's inequality for `max 0` under an average) with three bipartite lemmas:
averaging the left family of an indexed submeasurement over a distribution averages the matching
mass and the total overlap, and does not increase the consistency defect. The classical lemmas
are imported from the vendored file. The bipartite lemmas take the symmetric model
`S : SymModel 𝔓 K` as their first explicit argument, in place of the vendored
`ψ : QuantumState (ι × ι)`, and keep this file's namespace so that their vendored names pair;
the families are local, in `𝔓` (the vendored `Op ι`). No statement carries a swap or
normalization hypothesis, the vendored statements having none.

## Not ported

- `avgOver_distinct_bounded_le_avgOver_uniform_add_tv`: classical, imported.
- `avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k`: classical, imported.
- `max_zero_add_le`: classical, imported.
- `max_zero_mul_add_le`: classical, imported.
- `max_zero_avgOver_le_avgOver_max_zero`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Distribution avgOver avgOver_sum avgOver_sub)
open MIPStarRE.LDT.Pasting (max_zero_avgOver_le_avgOver_max_zero)
open MIPRE.LIDT.Co (SymModel SubMeas IdxSubMeas averageIdxSubMeas)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The bipartite matching mass of an averaged left family against `B` is the average of the
matching masses. -/
theorem qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : SubMeas Outcome 𝔓)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    S.qBipartiteMatchMass (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => S.qBipartiteMatchMass (A q) B) :=
  (Finset.sum_congr rfl fun a _ => S.ev_opTensor_averageOperatorOverDistribution_left 𝒟
    (fun q => (A q).outcome a) (B.outcome a)).trans
    (avgOver_sum 𝒟 fun q a => S.ev (S.opTensor ((A q).outcome a) (B.outcome a))).symm

/-- The total overlap of an averaged left family with `B` is the average of the total
overlaps. -/
theorem ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : SubMeas Outcome 𝔓)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    S.ev (S.opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => S.ev (S.opTensor (A q).total B.total)) :=
  S.ev_opTensor_averageOperatorOverDistribution_left 𝒟 (fun q => (A q).total) B.total

/-- Averaging the left family does not increase the bipartite consistency defect: the defect
of the average is at most the average of the defects (Jensen for `max 0`). -/
theorem qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓)
    (B : SubMeas Outcome 𝔓)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    S.qBipartiteConsDefect (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => S.qBipartiteConsDefect (A q) B) := by
  have h : S.qBipartiteConsDefect (averageIdxSubMeas 𝒟 A h𝒟) B =
      max 0 (avgOver 𝒟 fun q =>
        S.ev (S.opTensor (A q).total B.total) - S.qBipartiteMatchMass (A q) B) := by
    rw [avgOver_sub, ← ev_opTensor_total_averageIdxSubMeas_left S 𝒟 A B h𝒟,
      ← qBipartiteMatchMass_averageIdxSubMeas_left S 𝒟 A B h𝒟]
    rfl
  exact h.trans_le (max_zero_avgOver_le_avgOver_max_zero 𝒟 _)

end MIPRE.LIDT.Co.Pasting

end
