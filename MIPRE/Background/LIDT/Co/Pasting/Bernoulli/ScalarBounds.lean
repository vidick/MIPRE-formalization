/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
ScalarBounds.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.ScalarBounds

@[expose] public section

/-!
# Section 12 pasting: scalar bounds for complementary Bernoulli branches

The elementary scalar estimates used by the complementary branches of `thm:ld-pasting`, the
large-error reduction of `references/ldt-paper/ld-pasting.tex`, lines 52--55: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/ScalarBounds.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

Four declarations read a strategy or a family and are ported: `kappa_nonneg_of_complete`, and
the three large-parameter bounds on `ν`, whose strategy is a `SymStrat params.next 𝔓 K` and whose
slice family an `IdxPolyFamily params 𝔓`. `kappa_nonneg_of_complete` bounds the mass of the
left-placed averaged submeasurement by `1` through the keystone's `S.leftTensor_le_one`,
`S.ev_mono` and `S.ev_one_of_isNormalized`, the last without the vendored normalization field
(section "Swap symmetry is a theorem"). No lemma of the file has a swap, density or normalization
hypothesis.

The other six are arithmetic on the classical error functions `ldPastingInInductionNu` and
`ldPastingInInductionError`: this file imports the vendored file and names them through an
explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

- `ldPasting_kappa_coefficient_nonneg`: classical, imported.
- `ldPasting_degreeRatio_nonneg`: classical, imported.
- `one_le_ldPastingNu_coefficient`: classical, imported.
- `one_le_ldPastingNu_of_one_le_sum`: classical, imported.
- `one_le_ldPastingError_of_one_le_nu`: classical, imported.
- `one_le_ldPastingError_of_k_eq_zero`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel)
open MIPStarRE.LDT.MainInductionStep (ldPastingInInductionNu)
open MIPStarRE.LDT.Pasting (ldPasting_degreeRatio_nonneg one_le_ldPastingNu_of_one_le_sum)
open MIPRE.LIDT.Co (SymStrat IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The scalar `κ` in a complete family is nonnegative. -/
theorem kappa_nonneg_of_complete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {kappa : ℝ}
    (hcomplete : family.Complete strategy.state kappa) :
    0 ≤ kappa := by
  have hmass_le_one :
      strategy.state.subMeasMass (family.averagedSubMeas.liftLeft strategy.state) ≤ 1 :=
    (strategy.state.ev_mono _ _
      (strategy.state.leftTensor_le_one family.averagedSubMeas.total_le_one)).trans_eq
      strategy.state.ev_one_of_isNormalized
  linarith [hcomplete.averageCompleteness.lowerBound]

/-- The `ν` term is at least one when `γ > 1` and `k ≥ 1`. -/
theorem one_le_ldPastingNu_of_large_gamma
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hgamma : 1 < gamma) :
    1 ≤ ldPastingInInductionNu params k eps delta gamma zeta := by
  have hepsTerm_nonneg : 0 ≤ Real.rpow eps (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (eps_nonneg_of_isGood params.next strategy hgood) _
  have hdeltaTerm_nonneg : 0 ≤ Real.rpow delta (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (delta_nonneg_of_isGood params.next strategy hgood) _
  have hgammaTerm_one : 1 ≤ Real.rpow gamma (1 / (32 : ℝ)) :=
    le_of_lt (Real.one_lt_rpow hgamma (by norm_num))
  have hzetaTerm_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons) _
  have hdqTerm_nonneg :
      0 ≤ Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  exact one_le_ldPastingNu_of_one_le_sum params k eps delta gamma zeta hk_pos (by linarith)

/-- The `ν` term is at least one when `ζ > 1` and `k ≥ 1`. -/
theorem one_le_ldPastingNu_of_large_zeta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hzeta : 1 < zeta) :
    1 ≤ ldPastingInInductionNu params k eps delta gamma zeta := by
  have hepsTerm_nonneg : 0 ≤ Real.rpow eps (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (eps_nonneg_of_isGood params.next strategy hgood) _
  have hdeltaTerm_nonneg : 0 ≤ Real.rpow delta (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (delta_nonneg_of_isGood params.next strategy hgood) _
  have hgammaTerm_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (gamma_nonneg_of_isGood params.next strategy hgood) _
  have hzetaTerm_one : 1 ≤ Real.rpow zeta (1 / (32 : ℝ)) :=
    le_of_lt (Real.one_lt_rpow hzeta (by norm_num))
  have hdqTerm_nonneg :
      0 ≤ Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  exact one_le_ldPastingNu_of_one_le_sum params k eps delta gamma zeta hk_pos (by linarith)

/-- The `ν` term is at least one when `d / q > 1` and `k ≥ 1`. -/
theorem one_le_ldPastingNu_of_large_degreeRatio
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hdq : params.q < params.d) :
    1 ≤ ldPastingInInductionNu params k eps delta gamma zeta := by
  have hratio_gt_one : 1 < ((params.d : ℝ) / (params.q : ℝ)) :=
    (one_lt_div params.q_cast_pos).2 (by exact_mod_cast hdq)
  have hepsTerm_nonneg : 0 ≤ Real.rpow eps (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (eps_nonneg_of_isGood params.next strategy hgood) _
  have hdeltaTerm_nonneg : 0 ≤ Real.rpow delta (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (delta_nonneg_of_isGood params.next strategy hgood) _
  have hgammaTerm_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (gamma_nonneg_of_isGood params.next strategy hgood) _
  have hzetaTerm_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : ℝ)) :=
    Real.rpow_nonneg (IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons) _
  have hdqTerm_one :
      1 ≤ Real.rpow (((params.d : ℝ) / (params.q : ℝ))) (1 / (32 : ℝ)) :=
    le_of_lt (Real.one_lt_rpow hratio_gt_one (by norm_num))
  exact one_le_ldPastingNu_of_one_le_sum params k eps delta gamma zeta hk_pos (by linarith)

end MIPRE.LIDT.Co.Pasting

end
