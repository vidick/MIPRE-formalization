/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/ApproxDelta.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.InnerProduct

@[expose] public section

/-!
# Switch-sandwich preparation: `approx_δ` overlap gaps

Pointwise overlap-gap estimates used to bound the switch-sandwich approximation
error under `approx_δ` families: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/ApproxDelta.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The statements use a single state and joint operators, so they take a vector state
`V : VecState K` (a symmetric model is accepted through its coercion) and submeasurements in
`K →L[ℂ] K`, and they drop the vendored normalization hypothesis `hψ : ψ.IsNormalized`, a
theorem of the vector state. `SDDRel ψ` is `V.SDDRel`.

Both gaps are one estimate: for submeasurements `A`, `B` and a third one `E` (`E = A` on the
left, `E = B` on the right), `∑_a ev ((A_a - B_a) E_a)` is at most `√(qSDD A B)` in absolute
value, by Cauchy–Schwarz and `∑_a ev (E_a²) ≤ 1` (`subMeas_diagMass_le_one`).

## New here

- `question_overlap_gap_aux`: the common estimate above, from which both gaps follow.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_sub)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The common estimate behind `question_overlap_gap_left` and `question_overlap_gap_right`:
`|∑_a ev ((A_a - B_a) E_a)| ≤ √(qSDD A B)` for submeasurements `A`, `B`, `E`. -/
theorem question_overlap_gap_aux
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B E : SubMeas Outcome (K →L[ℂ] K)) :
    |∑ a : Outcome, V.ev ((A.outcome a - B.outcome a) * E.outcome a)| ≤
      Real.sqrt (V.qSDD A B) := by
  have hdiag : Real.sqrt (∑ a : Outcome, V.ev (E.outcome a * E.outcome a)) ≤ 1 :=
    Real.sqrt_le_one.mpr (subMeas_diagMass_le_one V E)
  have hherm : ∀ a, star (A.outcome a - B.outcome a) = A.outcome a - B.outcome a := fun a => by
    rw [star_sub, A.outcome_hermitian, B.outcome_hermitian]
  calc
    |∑ a : Outcome, V.ev ((A.outcome a - B.outcome a) * E.outcome a)|
      ≤ ∑ a : Outcome, |V.ev ((A.outcome a - B.outcome a) * E.outcome a)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (V.ev (star (A.outcome a - B.outcome a) * (A.outcome a - B.outcome a))) *
            Real.sqrt (V.ev (E.outcome a * E.outcome a)) :=
          Finset.sum_le_sum fun a _ => by
            simpa only [hherm, E.outcome_hermitian] using
              V.ev_abs_mul_le_sqrt (A.outcome a - B.outcome a) (E.outcome a)
    _ ≤ Real.sqrt (V.qSDD A B) * Real.sqrt (∑ a : Outcome, V.ev (E.outcome a * E.outcome a)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun a => V.ev_adjoint_self_nonneg _)
            (fun a => by
              simpa only [E.outcome_hermitian] using V.ev_adjoint_self_nonneg (E.outcome a))
    _ ≤ Real.sqrt (V.qSDD A B) * 1 := mul_le_mul_of_nonneg_left hdiag (Real.sqrt_nonneg _)
    _ = Real.sqrt (V.qSDD A B) := mul_one _

/-- Left overlap gap: `|∑_a ev (A_a A_a) - ∑_a ev (A_a B_a)| ≤ √(qSDD A B)`. -/
theorem question_overlap_gap_left
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B : SubMeas Outcome (K →L[ℂ] K)) :
    |(∑ a : Outcome, V.ev (A.outcome a * A.outcome a)) -
        ∑ a : Outcome, V.ev (A.outcome a * B.outcome a)| ≤
      Real.sqrt (V.qSDD A B) := by
  convert question_overlap_gap_aux V A B A using 2
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [V.ev_mul_comm_of_psd _ _ (A.outcome_pos a) (B.outcome_pos a), ← V.ev_sub, sub_mul]

/-- Right overlap gap: `|∑_a ev (A_a B_a) - ∑_a ev (B_a B_a)| ≤ √(qSDD A B)`. -/
theorem question_overlap_gap_right
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A B : SubMeas Outcome (K →L[ℂ] K)) :
    |(∑ a : Outcome, V.ev (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, V.ev (B.outcome a * B.outcome a)| ≤
      Real.sqrt (V.qSDD A B) := by
  convert question_overlap_gap_aux V A B B using 2
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [← V.ev_sub, sub_mul]

/-- `prop:easy-approx-from-approx-delta`. -/
theorem easyApproxFromApproxDelta_twoFamily {Question Outcome : Type*}
    [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome (K →L[ℂ] K)) (δ : ℝ) :
    V.SDDRel 𝒟 A B δ →
      |avgOver 𝒟 (fun q => ∑ a : Outcome, V.ev ((A q).outcome a * (A q).outcome a)) -
          avgOver 𝒟 (fun q => ∑ a : Outcome, V.ev ((A q).outcome a * (B q).outcome a))|
          ≤ Real.sqrt δ ∧
      |avgOver 𝒟 (fun q => ∑ a : Outcome, V.ev ((A q).outcome a * (B q).outcome a)) -
          avgOver 𝒟 (fun q => ∑ a : Outcome, V.ev ((B q).outcome a * (B q).outcome a))|
          ≤ Real.sqrt δ := by
  intro ⟨hδ⟩
  have hsdd : ∀ q, 0 ≤ V.qSDD (A q) (B q) := fun q => V.qSDD_nonneg (A q) (B q)
  constructor
  · rw [← avgOver_sub]
    exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun q => question_overlap_gap_left V (A q) (B q)) hsdd h𝒟).trans (Real.sqrt_le_sqrt hδ)
  · rw [← avgOver_sub]
    exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun q => question_overlap_gap_right V (A q) (B q)) hsdd h𝒟).trans (Real.sqrt_le_sqrt hδ)

end MIPRE.LIDT.Co.Preliminaries

end
