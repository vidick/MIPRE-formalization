/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Theorems/Averaging.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.GlobalVariance.Defs.Families
public import MIPStarRE.LDT.GlobalVariance.Theorems.Averaging

@[expose] public section

/-!
# Section 8 global variance: uniform averaging

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean`
in the port of `planning/c6b-plan.md` (milestone M6, section "Port conventions"): the squared
norm of a uniform operator average is at most the average of the squared norms
(`ev_uniformAverage_sq_le_avg`), and its consequences for one-outcome averaged families
(`qSDD_unit_family_of_average_le_avg`, `sddRel_unit_family_of_pointwise`).

Each statement uses a single state and joint operators, so it takes a vector state
`V : VecState K` (a symmetric model is accepted through its coercion) as its explicit first
argument, in the `GlobalVariance` namespace, as M1's and M3's helpers do. `ev ψ` is `V.ev`,
`qSDD ψ` is `V.qSDD`, `SDDRel ψ` is `V.SDDRel`, `ᴴ` is `star`.

The vendored proof of `ev_uniformAverage_sq_le_avg` expands the square into a double sum and
bounds each cross term by Cauchy–Schwarz; here it is the Jensen inequality of the vector state,
`VecState.ev_sum_conjTranspose_mul_sum_le`, applied to the family `a ↦ |α|⁻¹ • D a`. Two
private theorems unfold the uniform operator and scalar averages to these sums.

## Not ported

- `avgOver_polynomialDistribution_le_of_pointwise`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.GlobalVariance

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_comm uniformDistribution)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Uniform averaging infrastructure -/

/-- The uniform operator average is the sum of the family scaled by `|α|⁻¹`. -/
private theorem averageOperatorOverDistribution_uniform_eq_sum
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {R : Type*} [AddCommMonoid R] [Module ℝ R] (D : α → R) :
    averageOperatorOverDistribution (uniformDistribution α) D =
      ∑ a, (1 / (Fintype.card α : ℝ)) • D a := by
  simp [averageOperatorOverDistribution, uniformDistribution]

/-- The uniform average of a real function is its sum scaled by `|α|⁻¹`. -/
private theorem avgOver_uniform_eq_sum
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (x : α → ℝ) :
    avgOver (uniformDistribution α) x = ∑ a, (1 / (Fintype.card α : ℝ)) * x a := by
  simp [avgOver, uniformDistribution]

/-- Jensen for a uniform operator average: `ev (Sᴴ S) ≤ avg_a ev (D_aᴴ D_a)` for
`S = avg_a D_a`. -/
theorem ev_uniformAverage_sq_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (V : VecState K) (D : α → K →L[ℂ] K) :
    V.ev
      (star (averageOperatorOverDistribution (uniformDistribution α) D) *
        averageOperatorOverDistribution (uniformDistribution α) D)
      ≤ avgOver (uniformDistribution α) (fun a => V.ev (star (D a) * D a)) := by
  set c : ℝ := 1 / (Fintype.card α : ℝ) with hc
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  rw [averageOperatorOverDistribution_uniform_eq_sum, avgOver_uniform_eq_sum, ← hc]
  refine (V.ev_sum_conjTranspose_mul_sum_le (fun a => c • D a)).trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.coe_smul, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm,
    ← Complex.ofReal_mul, V.ev_scale, hc]
  field_simp

/-- The squared distance of two one-outcome submeasurements whose outcomes are uniform averages
is at most the average of the pointwise squared distances. -/
theorem qSDD_unit_family_of_average_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (V : VecState K)
    (MA MB : SubMeas Unit (K →L[ℂ] K))
    (A B : α → K →L[ℂ] K)
    (hMA :
      MA.outcome () = averageOperatorOverDistribution (uniformDistribution α) A)
    (hMB :
      MB.outcome () = averageOperatorOverDistribution (uniformDistribution α) B) :
    V.qSDD MA MB
      ≤ avgOver (uniformDistribution α)
          (fun a => V.ev (star (A a - B a) * (A a - B a))) := by
  have havg_sub :
      MA.outcome () - MB.outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => A a - B a) := by
    rw [hMA, hMB]
    exact (map_sub ((uniformDistribution α).weightedSumLinearMap (K →L[ℂ] K)) A B).symm
  have h : V.qSDD MA MB = V.ev (star (MA.outcome () - MB.outcome ()) *
      (MA.outcome () - MB.outcome ())) :=
    Fintype.sum_unique fun a : Unit =>
      V.ev (star (MA.outcome a - MB.outcome a) * (MA.outcome a - MB.outcome a))
  rw [h, havg_sub]
  exact ev_uniformAverage_sq_le_avg V (fun a => A a - B a)

/-- Lift pointwise operator deviation bounds to an `SDDRel` bound for
unit-valued averaged families. -/
theorem sddRel_unit_family_of_pointwise
    {Question α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (V : VecState K) (𝒟 : Distribution Question)
    (MA MB : Question → SubMeas Unit (K →L[ℂ] K))
    (A B : Question → α → K →L[ℂ] K)
    (hMA :
      ∀ q, (MA q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => A q a))
    (hMB :
      ∀ q, (MB q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => B q a))
    (δ : ℝ)
    (hpoint :
      ∀ a, avgOver 𝒟 (fun q => V.ev (star (A q a - B q a) * (A q a - B q a))) ≤ δ) :
    V.SDDRel 𝒟 MA MB δ := by
  refine ⟨?_⟩
  calc
    V.sddError 𝒟 MA MB
      ≤ avgOver 𝒟
          (fun q =>
            avgOver (uniformDistribution α)
              (fun a => V.ev (star (A q a - B q a) * (A q a - B q a)))) :=
        avgOver_mono _ _ _ fun q =>
          qSDD_unit_family_of_average_le_avg V (MA q) (MB q) (fun a => A q a) (fun a => B q a)
            (hMA q) (hMB q)
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver 𝒟 (fun q => V.ev (star (A q a - B q a) * (A q a - B q a)))) :=
        avgOver_comm 𝒟 (uniformDistribution α)
          (fun q a => V.ev (star (A q a - B q a) * (A q a - B q a)))
    _ ≤ avgOver (uniformDistribution α) (fun _ => δ) :=
        avgOver_mono _ _ _ hpoint
    _ = δ := by
        rw [avgOver_uniform_eq_sum]
        simp

end MIPRE.LIDT.Co.GlobalVariance

end
